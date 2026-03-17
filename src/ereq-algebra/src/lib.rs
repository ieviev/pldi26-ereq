// there is no universally right answer for when and what to simplify.
// these constants control the tradeoffs between node blowup and simplification cost.
// different formulas benefit from different settings  -- tune via bench-all in the docker container.
const HIGH_LIMIT: u32 = if cfg!(feature = "low_high_limit") {
    200_000
} else {
    500_000
};
const HIGH_SIZE_LIMIT: usize = 240;
const MED_LIMIT: u32 = 300_000;
const MED_SIZE_LIMIT: usize = 80;
const HEAVY_LIMIT: u32 = if cfg!(feature = "heavy_equiv") {
    8000
} else {
    200
};
const LIGHT_LIMIT: u32 = 200_000;

const DNF: bool = cfg!(feature = "dnf");
const NO_REWRITES: bool = cfg!(feature = "no_rewrites");
const NO_REWRITE_PRED: bool = cfg!(feature = "no_rewrite_pred");
const BOUNDED_SUBSUMES: bool = cfg!(feature = "bounded_subsumes");
const LOW_COST_SIMPLIFY: bool = cfg!(feature = "low_cost_simplify");
const NO_INIT_SIMPLIFY: bool = cfg!(feature = "no_init_simplify");
const THEN_FIRST: bool = cfg!(feature = "then_first");
const NO_COMPL_CONTAINS: bool = cfg!(feature = "no_compl_contains");
const EXTRACT_EXISTS: bool = cfg!(feature = "extract_exists");

use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;
use solver::{Solver, TSetId};
use std::cmp::{max, min};
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::fmt::Write;
use std::hash::Hash;
use std::ops::{BitAnd, BitOr, Not};

use crate::bdd::BddId;
use crate::bdd::BddIndex;
use crate::bdd::BddOrdinal;
pub mod bdd;
pub mod solver;

macro_rules! prof {
    ($self:ident, $($tt:tt)*) => {
        #[cfg(feature = "profile")]
        { $self.$($tt)* }
    };
}

// certain nodes are hardcoded to numbers for optimization
mod id {
    pub const MISSING: u32 = 0;
    pub const BOT: u32 = 1;
    pub const EPS: u32 = 2;
    pub const TOP: u32 = 3;
    pub const TOPSTAR: u32 = 4;
    pub const TOPPLUS: u32 = 5;
    pub const TOPPLUS2: u32 = 6;
    pub const OPTTOP: u32 = 7;
    pub const NOTTOP: u32 = 8;
}

#[derive(Clone, Copy, PartialEq, Hash, Eq, Debug, PartialOrd, Ord)]
pub struct MetadataId(u32);
impl MetadataId {
    pub const MISSING: MetadataId = MetadataId(id::MISSING);
}

#[derive(Clone, Copy, PartialEq, Hash, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct NodeId(pub u32);
impl NodeId {
    pub const MISSING: NodeId = NodeId(id::MISSING);
    /// bot: ⊥
    pub const BOT: NodeId = NodeId(id::BOT);
    /// epsilon: ε
    pub const EPS: NodeId = NodeId(id::EPS);
    /// top: _
    pub const TOP: NodeId = NodeId(id::TOP);
    /// top star: _*
    pub const TS: NodeId = NodeId(id::TOPSTAR);
    /// top plus: _+
    pub const TP: NodeId = NodeId(id::TOPPLUS);
    /// top plus 2: _{2,}
    pub const TP2: NodeId = NodeId(id::TOPPLUS2);
    pub const NOTTOP: NodeId = NodeId(id::NOTTOP);
    pub const OPTTOP: NodeId = NodeId(id::OPTTOP);
}
impl Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let num = &self.0;
        f.write_str(format!("{num}").as_str())
    }
}
impl NodeId {
    /// ∃(bit). (body) -> bit
    #[inline]
    pub fn exists_bit(self, b: &RegexBuilder) -> TSetId {
        debug_assert!(self.is_kind(b, Kind::Exists));
        BddId(b.get_left(self).0 as BddIndex)
    }
    #[inline]
    pub fn exists_body(self, b: &RegexBuilder) -> NodeId {
        debug_assert!(self.is_kind(b, Kind::Exists));
        b.get_right(self)
    }
    #[inline]
    pub fn kind(self, b: &RegexBuilder) -> Kind {
        b.kind(self)
    }
    #[inline]
    pub fn left(self, b: &RegexBuilder) -> NodeId {
        b.get_left(self)
    }
    #[inline]
    pub fn right(self, b: &RegexBuilder) -> NodeId {
        b.get_right(self)
    }
    #[inline]
    pub fn extra(self, b: &RegexBuilder) -> u32 {
        b.get_extra(self)
    }

    #[inline]
    pub fn is_nullable(self, b: &RegexBuilder) -> bool {
        b.is_nullable(self)
    }

    fn is_contains(self, b: &RegexBuilder) -> Option<NodeId> {
        if b.kind(self) == Kind::Concat && self.left(b) == NodeId::TS {
            let middle = self.right(b);
            if middle.kind(b) == Kind::Concat && middle.right(b) == NodeId::TS {
                return Some(middle.left(b));
            }
        }
        None
    }

    fn is_pred2plus(self, b: &RegexBuilder) -> Option<NodeId> {
        if self.is_concat(b) {
            let l = self.left(b);
            let r = self.right(b);
            if r.is_concat(b) {
                if let Some(p) = r.right(b).is_pred_star(b) {
                    if p == l && p == r.left(b) {
                        return Some(p);
                    }
                }
            }
        }
        None
    }

    fn is_contains2(self, b: &RegexBuilder) -> Option<NodeId> {
        // _*a_*a_*
        if b.kind(self) == Kind::Concat && self.left(b).is_ts() {
            // a_*a_*
            let c1 = self.right(b);
            if c1.kind(b) == Kind::Concat {
                // _*a_*
                let c2 = c1.right(b);
                if c2.kind(b) == Kind::Concat && c2.left(b).is_ts() {
                    // a_*
                    let c3 = c2.right(b);
                    if c3.kind(b) == Kind::Concat && c3.right(b).is_ts() {
                        if c1.left(b) == c3.left(b) {
                            return Some(c1.left(b));
                        }
                    }
                }
            }
        }
        None
    }
    #[inline]
    pub fn is_bot(self) -> bool {
        self == NodeId::BOT
    }
    #[inline]
    pub fn is_eps(self) -> bool {
        self == NodeId::EPS
    }
    #[inline]
    pub fn is_ts(self) -> bool {
        self == NodeId::TS
    }
    #[inline]
    pub fn is_tp(self) -> bool {
        self == NodeId::TP
    }

    pub fn is_tp2(self) -> bool {
        self == NodeId::TP2
    }

    #[inline]
    fn is_kind(self, b: &RegexBuilder, k: Kind) -> bool {
        b.kind(self) == k
    }

    /// pred 1 unsat with pred2, [a] unsat with [^a]
    #[inline(always)]
    pub fn is_unsat_pred(&self, pred2: NodeId, b: &mut RegexBuilder) -> bool {
        debug_assert!(self.is_pred(b));
        debug_assert!(pred2.is_pred(b), "{}", b.pp(pred2));
        let lset = self.tset(b);
        let rset = pred2.tset(b);
        b.solver().unsat_id(lset, rset)
    }

    /// pred 1 fully contains pred2, [ab] contains [a]
    #[inline(always)]
    pub fn is_contains_pred(&self, pred2: NodeId, b: &mut RegexBuilder) -> bool {
        debug_assert!(self.is_pred(b), "{}", b.pp(*self));
        debug_assert!(pred2.is_pred(b));
        let lset = self.tset(b);
        let rset = pred2.tset(b);
        b.solver().contains_id(lset, rset)
    }

    #[inline]
    pub fn is_pred(self, b: &RegexBuilder) -> bool {
        b.kind(self) == Kind::Pred
    }
    #[inline]
    pub fn is_concat(self, b: &RegexBuilder) -> bool {
        b.kind(self) == Kind::Concat
    }
    #[inline]
    pub fn is_compl(self, b: &RegexBuilder) -> bool {
        b.kind(self) == Kind::Compl
    }
    #[inline]
    pub fn contains_compl(self, b: &RegexBuilder) -> bool {
        b.flags(self).contains_compl()
    }
    #[inline]
    pub fn is_exists(self, b: &RegexBuilder) -> bool {
        b.kind(self) == Kind::Exists
    }
    #[inline]
    pub fn is_union(self, b: &RegexBuilder) -> bool {
        b.kind(self) == Kind::Union
    }

    fn is_singleton_constraint(self, b: &RegexBuilder) -> Option<(NodeId, NodeId)> {
        // 𝑃⁻⁴*𝑃⁴𝑃⁻⁴*
        if self.is_concat(b) {
            let not_contains = self.left(b);
            if let Some(not_pred) = not_contains.is_pred_star(b) {
                let middle = self.right(b);
                if middle.is_concat(b) && middle.right(b) == not_contains {
                    return Some((not_pred, middle.left(b)));
                }
            }
        }
        None
    }

    #[inline]
    pub fn is_inter(self, b: &RegexBuilder) -> bool {
        b.kind(self) == Kind::Inter
    }

    #[inline]
    pub fn is_star(self, b: &RegexBuilder) -> bool {
        if self == NodeId::EPS {
            return false;
        }
        b.kind(self) == Kind::Star
    }
    #[inline]
    pub fn is_plus(self, b: &RegexBuilder) -> bool {
        if self.is_concat(b) {
            let r = self.right(b);
            return r.is_star(b) && r.left(b) == self.left(b);
        }
        false
    }

    #[inline]
    pub fn is_opt(self, b: &RegexBuilder) -> Option<NodeId> {
        if self.is_union(b) && self.left(b) == NodeId::EPS {
            return Some(self.right(b));
        }
        None
    }

    #[inline]
    pub fn is_pred_star(self, b: &RegexBuilder) -> Option<NodeId> {
        if self == NodeId::EPS {
            return None;
        }
        if self.is_star(b) && self.left(b).is_pred(b) {
            Some(self.left(b))
        } else {
            None
        }
    }
    #[inline]
    pub fn is_pred_plus(self, b: &RegexBuilder) -> Option<NodeId> {
        if self.is_concat(b) {
            if let Some(p) = self.right(b).is_pred_star(b) {
                if p == self.left(b) {
                    return Some(p);
                }
            }
        }
        None
    }
    #[inline]
    pub fn is_begins_with_pred(self, b: &RegexBuilder) -> Option<NodeId> {
        if self.is_concat(b) && self.right(b).is_top_star() && self.left(b).is_pred(b) {
            Some(self.left(b))
        } else {
            None
        }
    }
    #[inline]
    pub fn has_concat_tail(self, b: &RegexBuilder, tail: NodeId) -> bool {
        if self == tail {
            true
        } else if self.is_concat(b) {
            self.right(b).has_concat_tail(b, tail)
        } else {
            false
        }
    }
    #[inline]
    pub fn is_top_star(self) -> bool {
        self == NodeId::TS
    }
    #[inline]
    pub fn is_top(self) -> bool {
        self == NodeId::TOP
    }
    #[inline]
    pub fn tset(self, b: &RegexBuilder) -> TSetId {
        debug_assert!(self.is_pred(b));
        BddId(b.get_extra(self) as BddIndex)
    }

    pub fn iter_inter(self, b: &mut RegexBuilder, mut f: impl FnMut(&mut RegexBuilder, NodeId)) {
        let mut curr: NodeId = self;
        while curr.kind(b) == Kind::Inter {
            f(b, curr.left(b));
            curr = curr.right(b);
        }
        f(b, curr);
    }

    #[inline]
    pub fn iter_inter_while(
        self,
        b: &mut RegexBuilder,
        mut f: impl FnMut(&mut RegexBuilder, NodeId) -> bool,
    ) {
        let mut curr: NodeId = self;
        let mut continue_loop = true;
        while continue_loop && curr.kind(b) == Kind::Inter {
            let left = curr.left(b);
            let right = curr.right(b);
            continue_loop = f(b, left);
            curr = right;
        }
        if continue_loop {
            f(b, curr);
        }
    }

    #[inline]
    pub fn iter_union(self, b: &mut RegexBuilder, mut f: impl FnMut(&mut RegexBuilder, NodeId)) {
        let mut curr: NodeId = self;
        while curr.kind(b) == Kind::Union {
            let left = curr.left(b);
            let right = curr.right(b);
            f(b, left);
            curr = right;
        }
        f(b, curr);
    }

    #[inline]
    pub fn iter_union_while(
        self,
        b: &mut RegexBuilder,
        f: &mut impl FnMut(&mut RegexBuilder, NodeId) -> bool,
    ) {
        let mut curr: NodeId = self;
        let mut continue_loop = true;
        while continue_loop && curr.kind(b) == Kind::Union {
            let left = curr.left(b);
            let right = curr.right(b);
            continue_loop = f(b, left);
            curr = right;
        }
        if continue_loop {
            f(b, curr);
        }
    }
}

#[derive(Clone, Copy, PartialEq, Hash, Eq, Debug, PartialOrd, Ord)]
#[repr(transparent)]
pub struct TRegexId(u32);
impl TRegexId {
    pub const MISSING: TRegexId = TRegexId(id::MISSING);
    pub const BOT: TRegexId = TRegexId(id::BOT);
    pub const EPS: TRegexId = TRegexId(id::EPS);
    pub const TOP: TRegexId = TRegexId(id::TOP);
    pub const TOPSTAR: TRegexId = TRegexId(id::TOPSTAR);
}

#[derive(Clone, Copy, PartialEq, Hash, Eq, Debug)]
pub struct Nullability(u8);

impl Not for Nullability {
    type Output = Self;

    #[inline]
    fn not(self) -> Self::Output {
        Nullability(!self.0)
    }
}
impl Nullability {
    pub const NEVER: Nullability = Nullability(0b0);
    pub const ALWAYS: Nullability = Nullability(0b1);
}

#[derive(Eq, Hash, PartialEq, Clone, Copy, Debug, PartialOrd, Ord)]
pub struct MetaFlags(u8);

impl BitAnd for MetaFlags {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        MetaFlags(rhs.0 & self.0)
    }
}
impl BitOr for MetaFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        MetaFlags(rhs.0 | self.0)
    }
}
impl Not for MetaFlags {
    type Output = Self;

    fn not(self) -> Self::Output {
        MetaFlags(!self.0)
    }
}

impl MetaFlags {
    pub const ZERO: MetaFlags = MetaFlags(0);
    pub const IS_NULLABLE: MetaFlags = MetaFlags(1);
    pub const CONTAINS_COMPL: MetaFlags = MetaFlags(1 << 4);
    pub const CONTAINS_INTER: MetaFlags = MetaFlags(1 << 5);
    pub const CONTAINS_EXISTS: MetaFlags = MetaFlags(1 << 6);
    pub const ALL_CONTAINS: MetaFlags = MetaFlags(0b1111000);

    #[inline(always)]
    pub fn has_flag(self, other: MetaFlags) -> bool {
        self & other != MetaFlags::ZERO
    }

    #[inline(always)]
    pub fn nullability_flags(self) -> MetaFlags {
        self & MetaFlags(0b1)
    }
    #[inline(always)]
    pub fn contains_inter(self) -> bool {
        self & MetaFlags::CONTAINS_INTER != MetaFlags::ZERO
    }
    #[inline(always)]
    pub fn contains_compl(self) -> bool {
        self & MetaFlags::CONTAINS_COMPL != MetaFlags::ZERO
    }
    #[inline(always)]
    pub fn contains_exists(self) -> bool {
        self & MetaFlags::CONTAINS_EXISTS != MetaFlags::ZERO
    }

    #[inline(always)]
    pub fn new(nullability: MetaFlags, contains_flags: MetaFlags) -> MetaFlags {
        nullability | contains_flags
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Kind {
    // var 0..n, propositions n+1 ...
    Pred = 0,
    Concat,
    Union,
    Star,
    Compl,
    Exists,
    Inter,
}

#[derive(Eq, Hash, PartialEq, Clone, PartialOrd, Ord)]
struct Metadata {
    flags: MetaFlags,
    bits: TSetId,
    cost: usize,
}

struct MetadataBuilder {
    num_created: u32,
    solver: Solver,
    index: FxHashMap<Metadata, MetadataId>,
    pub array: Vec<Metadata>,
}

impl MetadataBuilder {
    fn new() -> MetadataBuilder {
        let mut arr = Vec::new();
        arr.push(Metadata {
            flags: MetaFlags::ZERO,
            bits: TSetId::EMPTY,
            cost: 1,
        });
        let inst = Self {
            num_created: 0,
            solver: Solver::new(),
            index: FxHashMap::default(),
            array: arr,
        };
        inst
    }

    fn init(&mut self, inst: Metadata) -> MetadataId {
        self.num_created += 1;
        let new_id = MetadataId(self.num_created);
        self.index.insert(inst.clone(), new_id);
        self.array.push(inst);
        new_id
    }

    fn get_meta_id(&mut self, inst: Metadata) -> MetadataId {
        match self.index.get(&inst) {
            Some(&id) => id,
            None => self.init(inst),
        }
    }

    fn cost(&self, inst: MetadataId) -> usize {
        self.array[inst.0 as usize].cost
    }

    #[inline(always)]
    fn all_contains(&self, setflags: MetaFlags) -> MetaFlags {
        setflags & (MetaFlags::ALL_CONTAINS)
    }

    fn flags_compl(&self, left_id: MetadataId) -> MetaFlags {
        let left = &self.array[left_id.0 as usize].flags;
        let nullabilities = !left.nullability_flags() & MetaFlags::IS_NULLABLE;
        let contains = self.all_contains(*left);
        let newflags = nullabilities | contains | MetaFlags::CONTAINS_COMPL;
        newflags
    }

    fn flags_concat(&self, left_id: MetadataId, right_id: MetadataId) -> MetaFlags {
        let left = &self.array[left_id.0 as usize].flags;
        let right = &self.array[right_id.0 as usize].flags;
        let nullabilities = left.nullability_flags() & right.nullability_flags();
        let contains = self.all_contains(*left | *right);
        let newflags = MetaFlags::new(nullabilities, contains);
        newflags
    }

    fn flags_inter(&self, left_id: MetadataId, right_id: MetadataId) -> MetaFlags {
        let left = &self.array[left_id.0 as usize].flags;
        let right = &self.array[right_id.0 as usize].flags;
        let nullabilities = left.nullability_flags() & right.nullability_flags();
        let contains = self.all_contains(*left | *right) | MetaFlags::CONTAINS_INTER;
        let newflags = MetaFlags::new(nullabilities, contains);
        newflags
    }

    fn flags_union(&self, left_id: MetadataId, right_id: MetadataId) -> MetaFlags {
        let left = &self.array[left_id.0 as usize].flags;
        let right = &self.array[right_id.0 as usize].flags;
        let nullabilities = left.nullability_flags() | right.nullability_flags();
        let contains = self.all_contains(*left | *right);
        let newflags = MetaFlags::new(nullabilities, contains);
        newflags
    }
}

#[derive(Eq, Hash, PartialEq, Clone)]
pub struct NodeKey {
    pub kind: Kind,
    pub left: NodeId,
    pub right: NodeId,
    pub extra: u32,
}

#[derive(Eq, Hash, PartialEq, Clone, Debug, Copy)]
pub enum TRegex<TSetId> {
    Leaf(NodeId),
    ITE(TSetId, TRegexId, TRegexId),
}

#[derive(Eq, Hash, PartialEq, Clone, Copy)]
pub struct NodeFlags(u8);
impl NodeFlags {
    pub const NONE: NodeFlags = NodeFlags(0);
    pub const CHECKED_EMPTY: NodeFlags = NodeFlags(1);
    pub const IS_NONEMPTY: NodeFlags = NodeFlags(1 << 1);
    pub const CHECKED_FULL: NodeFlags = NodeFlags(1 << 2);
    pub const IS_NONFULL: NodeFlags = NodeFlags(1 << 3);
    fn is_checked_empty(self) -> bool {
        self.0 & NodeFlags::CHECKED_EMPTY.0 != NodeFlags::NONE.0
    }
    fn is_checked_full(self) -> bool {
        self.0 & NodeFlags::CHECKED_FULL.0 != NodeFlags::NONE.0
    }
    fn is_empty(self) -> bool {
        self.0 & NodeFlags::IS_NONEMPTY.0 == NodeFlags::NONE.0
    }
    fn is_nonfull(self) -> bool {
        self.0 & NodeFlags::IS_NONFULL.0 == NodeFlags::IS_NONFULL.0
    }
    fn is_full(self) -> bool {
        self.0 & NodeFlags::IS_NONFULL.0 == NodeFlags::NONE.0
    }
    fn is_nonempty(self) -> bool {
        self.0 & NodeFlags::IS_NONEMPTY.0 == NodeFlags::IS_NONEMPTY.0
    }
}

impl Debug for NodeFlags {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_checked_empty() {
            if self.is_empty() {
                f.write_str("[non_empty]")?;
            } else {
                f.write_str("[empty]")?;
            }
        }
        if self.is_checked_full() {
            if self.is_nonfull() {
                f.write_str("[non_full]")?;
            } else {
                f.write_str("[full]")?;
            }
        }
        Ok(())
    }
}

pub struct RegexBuilder {
    mb: MetadataBuilder,
    // reused internally for sorting
    temp_vec: Vec<NodeId>,
    // regex nodes
    index: FxHashMap<NodeKey, NodeId>,
    reverse_cache: FxHashMap<NodeId, NodeId>,
    array: Vec<NodeKey>,
    metadata: Vec<MetadataId>,
    cache_flags: FxHashMap<NodeId, NodeFlags>,
    cycle_empty_count: FxHashMap<NodeId, u32>,
    simplified: Vec<NodeId>,
    // symbolic regexes
    tr_cache: FxHashMap<TRegex<TSetId>, TRegexId>,
    tr_array: Vec<TRegex<TSetId>>,
    tr_der_center: Vec<TRegexId>,
    bdd_to_ite: Vec<TRegexId>,
    rev_der_cache_null: Vec<NodeId>,
    rev_der_cache_nonnull: Vec<NodeId>,
    // number of keys created
    num_created: u32,
    pub num_var2: BddOrdinal,
    pub factor: bool,
    subsumes_budget: u32, // 0 = unlimited
    #[cfg_attr(not(feature = "profile"), allow(dead_code))]
    prof_simplify_calls: u64,
    #[cfg_attr(not(feature = "profile"), allow(dead_code))]
    prof_init_calls: u64,
    #[cfg_attr(not(feature = "profile"), allow(dead_code))]
    prof_is_empty_calls: u64,
    #[cfg_attr(not(feature = "profile"), allow(dead_code))]
    prof_is_empty_nodes: u64,
    #[cfg_attr(not(feature = "profile"), allow(dead_code))]
    prof_is_full_calls: u64,
    #[cfg_attr(not(feature = "profile"), allow(dead_code))]
    prof_subsumes_calls: u64,
    #[cfg_attr(not(feature = "profile"), allow(dead_code))]
    prof_subsumes_hits: u64,
    #[cfg_attr(not(feature = "profile"), allow(dead_code))]
    prof_heavy_calls: u64,
    #[cfg_attr(not(feature = "profile"), allow(dead_code))]
    prof_heavy_nodes: u64,
    #[cfg_attr(not(feature = "profile"), allow(dead_code))]
    prof_simplify_hit: u64,
}

impl RegexBuilder {
    pub fn node_count(&self) -> u32 {
        self.num_created
    }

    pub fn config_string() -> String {
        format!(
            "HIGH_LIMIT={}, HIGH_SIZE_LIMIT={}, MED_LIMIT={}, MED_SIZE_LIMIT={}, \
             HEAVY_LIMIT={}, LIGHT_LIMIT={}, DNF={}, NO_REWRITES={}, NO_REWRITE_PRED={}, \
             BOUNDED_SUBSUMES={}, LOW_COST_SIMPLIFY={}, NO_INIT_SIMPLIFY={}, THEN_FIRST={}, NO_COMPL_CONTAINS={}, EXTRACT_EXISTS={}, cache_cycle_empty=true",
            HIGH_LIMIT, HIGH_SIZE_LIMIT, MED_LIMIT, MED_SIZE_LIMIT,
            HEAVY_LIMIT, LIGHT_LIMIT, DNF, NO_REWRITES, NO_REWRITE_PRED, BOUNDED_SUBSUMES, LOW_COST_SIMPLIFY, NO_INIT_SIMPLIFY, THEN_FIRST, NO_COMPL_CONTAINS, EXTRACT_EXISTS,
        )
    }

    pub fn print_profile(&self) {
        #[cfg(feature = "profile")]
        {
            eprintln!(
                "  init: {} total calls (final nodes: {})",
                self.prof_init_calls, self.num_created
            );
            eprintln!(
                "  simplify_from_init: {} calls, {} hits",
                self.prof_simplify_calls, self.prof_simplify_hit
            );
            eprintln!(
                "  subsumes: {}/{} hit/calls",
                self.prof_subsumes_hits, self.prof_subsumes_calls
            );
            eprintln!(
                "  is_empty: {} calls; is_full: {} calls; heavy: {} calls",
                self.prof_is_empty_calls, self.prof_is_full_calls, self.prof_heavy_calls
            );
            // node kind distribution
            let mut counts = [0u32; 7];
            let mut cost_sum = [0u64; 7];
            for i in 1..=self.num_created {
                let kind = self.array[i as usize].kind as usize;
                counts[kind] += 1;
                let meta_id = self.metadata[i as usize];
                if meta_id != MetadataId::MISSING {
                    cost_sum[kind] += self.mb.cost(meta_id) as u64;
                }
            }
            let kinds = [
                "Pred", "Concat", "Union", "Inter", "Star", "Compl", "Exists",
            ];
            for (i, name) in kinds.iter().enumerate() {
                if counts[i] > 0 {
                    eprintln!(
                        "  {}: {} nodes (avg cost {:.1})",
                        name,
                        counts[i],
                        cost_sum[i] as f64 / counts[i] as f64
                    );
                }
            }
        }
    }

    pub fn new() -> RegexBuilder {
        let mut inst = Self {
            mb: MetadataBuilder::new(),
            array: Vec::new(),
            index: FxHashMap::default(),
            cache_flags: FxHashMap::default(),
            cycle_empty_count: FxHashMap::default(),
            tr_array: Vec::new(),
            tr_cache: FxHashMap::default(),
            tr_der_center: Vec::new(),
            num_created: 0,
            temp_vec: Vec::new(),
            reverse_cache: FxHashMap::default(),
            metadata: Vec::new(),
            simplified: Vec::new(),
            num_var2: 0,
            factor: !DNF,
            subsumes_budget: 0,
            prof_simplify_calls: 0,
            prof_init_calls: 0,
            prof_is_empty_calls: 0,
            prof_is_empty_nodes: 0,
            prof_is_full_calls: 0,
            prof_subsumes_calls: 0,
            prof_subsumes_hits: 0,
            prof_heavy_calls: 0,
            prof_heavy_nodes: 0,
            prof_simplify_hit: 0,
            rev_der_cache_nonnull: Vec::new(),
            rev_der_cache_null: Vec::new(),
            bdd_to_ite: Vec::new(),
        };
        // hardcoded node ids
        // array[0] is for undefined nodes
        inst.array.push(NodeKey {
            kind: Kind::Inter,
            left: NodeId::MISSING,
            right: NodeId::MISSING,
            extra: 0,
        });

        inst.mk_pred(TSetId::EMPTY); // 1 - bot
        inst.mk_star(NodeId::BOT); // 2 - eps
        let top = inst.mk_pred(TSetId::FULL); // 3 - top
        inst.mk_star(top); // 4 - topstar
        let top_plus = inst.mk_concat(top, NodeId::TS); // 5 - tp
                                                        // hardcoded tregexes
        inst.tr_array.push(TRegex::Leaf(NodeId::MISSING)); // 0: missing
        inst.mk_leaf(NodeId::BOT); // 1 - bot
        inst.mk_leaf(NodeId::EPS); // 2 - eps
        inst.mk_leaf(NodeId::TOP); // 3 - top
        inst.mk_leaf(NodeId::TS); // 4 - topstar

        debug_assert_eq!(top_plus, NodeId::TP);

        let tp2 = inst.mk_concat(top, top_plus); // 6 - tp2
        debug_assert_eq!(tp2, NodeId::TP2);
        let opttop = inst.mk_union(NodeId::EPS, NodeId::TOP);
        debug_assert_eq!(opttop, NodeId::OPTTOP);
        let nottop = inst.mk_union(NodeId::EPS, NodeId::TP2);
        debug_assert_eq!(nottop, NodeId::NOTTOP);

        inst
    }

    #[inline]
    pub fn solver(&mut self) -> &mut Solver {
        &mut self.mb.solver
    }

    #[inline]
    pub fn ordinal(&mut self, set: TSetId) -> BddOrdinal {
        self.solver().bdd_builder.get_ref(set).ordinal
    }

    fn tr_init(&mut self, inst: TRegex<TSetId>) -> TRegexId {
        let new_id = TRegexId(self.tr_cache.len() as u32 + 1);
        self.tr_cache.insert(inst.clone(), new_id);
        self.tr_array.push(inst);
        new_id
    }

    fn get_term_id(&mut self, inst: TRegex<TSetId>) -> TRegexId {
        match self.tr_cache.get(&inst) {
            Some(&id) => id,
            None => self.tr_init(inst),
        }
    }

    #[inline]
    fn get_cached_term_id(&mut self, inst: TRegex<TSetId>) -> Option<&TRegexId> {
        self.tr_cache.get(&inst)
    }

    #[inline]
    pub fn get_tregex(&self, inst: TRegexId) -> &TRegex<TSetId> {
        &self.tr_array[inst.0 as usize]
    }

    fn unsat_lengths(&self, minmax1: (u32, u32), minmax2: (u32, u32)) -> bool {
        let absmin = max(minmax1.0, minmax2.0);
        let absmax = min(minmax1.1, minmax2.1);
        absmin > absmax
    }

    fn unsat(&mut self, cond1: TSetId, cond2: TSetId) -> bool {
        let cd = self.mb.solver.and_id(cond1, cond2);
        self.mb.solver.is_empty_id(cd)
    }

    pub fn mk_leaf(&mut self, node_id: NodeId) -> TRegexId {
        let term = TRegex::<TSetId>::Leaf(node_id);
        self.get_term_id(term)
    }

    pub fn mk_ite(&mut self, cond: TSetId, _then: TRegexId, _else: TRegexId) -> TRegexId {
        // outside in exists indexing
        if _then == _else {
            return _then;
        }

        let bdd_one = self.solver().bdd_builder.get_ref(cond).one;
        if bdd_one == BddId::FALSE {
            {
                let notcond = self.solver().not_id(cond);
                return self.mk_ite(notcond, _else, _then);
            }
        }

        let key = TRegex::ITE(cond, _then, _else);
        if let Some(cached) = self.get_cached_term_id(key) {
            return *cached;
        }
        if cond == TSetId::FULL {
            return _then;
        }
        if cond == TSetId::EMPTY {
            return _else;
        }
        let _clean_then = self.clean(cond, _then);
        let notcond = self.solver().not_id(cond);
        let _clean_else = self.clean(notcond, _else);

        if _clean_then == _clean_else {
            return _clean_then;
        }

        self.get_term_id(TRegex::ITE(cond, _clean_then, _clean_else))
    }

    fn clean(&mut self, beta: TSetId, tterm: TRegexId) -> TRegexId {
        match self.get_tregex(tterm) {
            TRegex::Leaf(_) => return tterm,
            TRegex::ITE(alpha, _then_id, _else_id) => {
                let alpha = *alpha;
                let _then_id = *_then_id;
                let _else_id = *_else_id;
                let notalpha = self.mb.solver.not_id(alpha);
                if self.mb.solver.unsat_id(beta, alpha) {
                    let ec = self.mb.solver.and_id(beta, notalpha);
                    let new_else = self.clean(ec, _else_id);
                    return new_else;
                }
                if self.unsat(beta, notalpha) {
                    let tc = self.mb.solver.and_id(beta, alpha);
                    let new_then = self.clean(tc, _then_id);
                    return new_then;
                }
                let tc = self.mb.solver.and_id(beta, alpha);
                let ec = self.mb.solver.and_id(beta, notalpha);
                let new_then = self.clean(tc, _then_id);
                let new_else = self.clean(ec, _else_id);

                return self.mk_ite(alpha, new_then, new_else);
            }
        }
    }

    #[inline]
    fn mk_unary(
        &mut self,
        term: TRegexId,
        apply: &mut impl FnMut(&mut RegexBuilder, NodeId) -> NodeId,
    ) -> TRegexId {
        match self.tr_array[term.0 as usize] {
            TRegex::Leaf(node_id) => {
                let applied = apply(self, node_id);
                self.mk_leaf(applied)
            }
            TRegex::ITE(c1, _then, _else) => {
                let _then1 = self.mk_unary(_then, apply);
                let _else1 = self.mk_unary(_else, apply);
                self.mk_ite(c1, _then1, _else1)
            }
        }
    }

    #[inline]
    fn mk_binary(
        &mut self,
        left: TRegexId,
        right: TRegexId,
        apply: &mut impl FnMut(&mut RegexBuilder, NodeId, NodeId) -> NodeId,
    ) -> TRegexId {
        match *self.get_tregex(left) {
            TRegex::Leaf(left_node_id) => match self.tr_array[right.0 as usize] {
                TRegex::Leaf(right_node_id) => {
                    let applied = apply(self, left_node_id, right_node_id);
                    self.mk_leaf(applied)
                }
                TRegex::ITE(c2, _then, _else) => {
                    let then2 = self.mk_binary(left, _then, apply);
                    let else2 = self.mk_binary(left, _else, apply);
                    self.mk_ite(c2, then2, else2)
                }
            },
            TRegex::ITE(c1, _then1, _else1) => match self.tr_array[right.0 as usize] {
                TRegex::Leaf(_) => {
                    let then2 = self.mk_binary(_then1, right, apply);
                    let else2 = self.mk_binary(_else1, right, apply);
                    self.mk_ite(c1, then2, else2)
                }
                TRegex::ITE(c2, _then2, _else2) => {
                    if c1 == c2 {
                        let _then = self.mk_binary(_then1, _then2, apply);
                        let _else = self.mk_binary(_else1, _else2, apply);
                        return self.mk_ite(c1, _then, _else);
                    }
                    // normally this ordering is is an arbitrary choice,
                    // but here this ordering is essential for correctness
                    // largest indices first, then smaller
                    if self.ordinal(c1) > self.ordinal(c2) {
                        let _then = self.mk_binary(_then1, right, apply);
                        let _else = self.mk_binary(_else1, right, apply);
                        return self.mk_ite(c1, _then, _else);
                    } else {
                        let _then = self.mk_binary(left, _then2, apply);
                        let _else = self.mk_binary(left, _else2, apply);
                        return self.mk_ite(c2, _then, _else);
                    }
                }
            },
        }
    }

    pub fn meta_contains_inter(&self, node_id: NodeId) -> bool {
        self.flags(node_id).0 & MetaFlags::CONTAINS_INTER.0 != 0
    }

    fn get_min_max_len(&self, node_id: NodeId) -> (u32, u32) {
        if node_id == NodeId::EPS {
            return (0, 0);
        }
        match self.kind(node_id) {
            Kind::Pred => (1, 1),
            Kind::Concat => {
                let left = self.get_min_max_len(node_id.left(self));
                let right = self.get_min_max_len(node_id.right(self));
                let max_r = match (left.1, right.1) {
                    (u32::MAX, _) => u32::MAX,
                    (_, u32::MAX) => u32::MAX,
                    _ => left.1 + right.1, // will panic on overflow
                };
                let new_bounds = (left.0 + right.0, max_r);
                new_bounds
            }
            Kind::Union => {
                let left = self.get_min_max_len(self.get_left(node_id));
                let right = self.get_min_max_len(self.get_right(node_id));
                let new_bounds = (left.0.min(right.0), left.1.max(right.1));
                new_bounds
            }
            Kind::Inter => {
                let left = self.get_min_max_len(self.get_left(node_id));
                let right = self.get_min_max_len(self.get_right(node_id));
                let new_bounds = (left.0.max(right.0), left.1.min(right.1));
                new_bounds
            }
            Kind::Star => (0, u32::MAX),
            Kind::Compl => {
                if self.is_nullable(node_id) {
                    (0, u32::MAX)
                } else {
                    (1, u32::MAX) // overapproximation
                }
            }
            Kind::Exists => self.get_min_max_len(self.get_right(node_id)),
        }
    }

    pub fn is_star(&mut self, node_id: NodeId) -> bool {
        self.kind(node_id) == Kind::Star
    }

    #[inline(always)]
    pub fn is_nullable(&self, node_id: NodeId) -> bool {
        debug_assert!(node_id != NodeId::MISSING);
        (self.flags(node_id) & MetaFlags::IS_NULLABLE).0 != 0
    }

    #[inline(always)]
    pub fn cache_der(&mut self, node_id: NodeId, result: TRegexId) -> TRegexId {
        self.tr_der_center[node_id.0 as usize] = result;
        result
    }

    pub fn bdd_to_pred(&mut self, bdd_id: BddId) -> NodeId {
        self.mk_pred(bdd_id)
    }

    pub fn bdd_to_bits(&mut self, bdd_id: BddId) -> BddId {
        if bdd_id.0 <= BddId::TRUE.0 {
            return BddId::FALSE;
        }
        let bdd = *self.solver().bdd_builder.get_ref(bdd_id);
        let nth = self.solver().create_nth_bit_1(bdd.ordinal);
        let one = self.bdd_to_bits(bdd.one);
        let zero = self.bdd_to_bits(bdd.zero);
        let or_1 = self.solver().or_id(nth, one);
        self.solver().or_id(or_1, zero)
    }

    #[inline]
    pub fn bdd_to_ite(&mut self, bdd_id: BddId) -> TRegexId {
        if let Some(ite) = self.bdd_to_ite.get(bdd_id.0 as usize) {
            if *ite != TRegexId::MISSING {
                return *ite;
            }
        }

        if bdd_id == BddId::TRUE {
            return TRegexId::EPS;
        }
        if bdd_id == BddId::FALSE {
            return TRegexId::BOT;
        }
        let bdd = *self.solver().bdd_builder.get_ref(bdd_id);
        let ord = self.solver().create_nth_bit_1(bdd.ordinal);
        let one = self.bdd_to_ite(bdd.one);
        let zero = self.bdd_to_ite(bdd.zero);
        let result = self.mk_ite(ord, one, zero);
        self.init_bdd_ite(bdd_id, result);
        result
    }

    pub fn der(&mut self, node_id: NodeId) -> TRegexId {
        match self.tr_der_center.get(node_id.0 as usize) {
            Some(&result) => {
                if result != TRegexId::MISSING {
                    return result;
                }
            }
            None => {
                self.tr_der_center
                    .resize(self.array.len() as usize * 2, TRegexId::MISSING);
            }
        }

        let result = match self.kind(node_id) {
            Kind::Pred => {
                let cond = self.get_tset(node_id);
                if cond == TSetId::FULL || cond == TSetId::EMPTY {
                    return self.mk_ite(cond, TRegexId::EPS, TRegexId::BOT);
                }
                let result = self.bdd_to_ite(cond);
                result
            }
            Kind::Compl => {
                let leftd = self.der(self.get_left(node_id));
                self.mk_unary(leftd, &mut (|b, v| b.mk_compl(v)))
            }
            Kind::Inter => {
                let leftd = self.der(self.get_left(node_id));
                let rightd = self.der(self.get_right(node_id));
                let result = self.mk_binary(
                    leftd,
                    rightd,
                    &mut (|b, left, right| b.mk_inter(left, right)),
                );
                result
            }
            Kind::Union => {
                let leftd = self.der(self.get_left(node_id));
                let rightd = self.der(self.get_right(node_id));
                self.mk_binary(
                    leftd,
                    rightd,
                    &mut (|b, left, right| b.mk_union(left, right)),
                )
            }
            Kind::Concat => {
                let left = self.get_left(node_id);
                let leftd = self.der(left);
                let right = self.get_right(node_id);

                if self.is_nullable(left) {
                    let rightd = self.der(right);
                    let right_leaf = self.mk_leaf(right);
                    let ldr = self.mk_binary(
                        leftd,
                        right_leaf,
                        &mut (|b, left, right| b.mk_concat(left, right)),
                    );
                    self.mk_binary(ldr, rightd, &mut (|b, left, right| b.mk_union(left, right)))
                } else {
                    let right_leaf = self.mk_leaf(right);
                    let ldr = self.mk_binary(
                        leftd,
                        right_leaf,
                        &mut (|b, left, right| b.mk_concat(left, right)),
                    );
                    ldr
                }
            }
            Kind::Star => {
                if node_id == NodeId::EPS {
                    TRegexId::BOT
                } else {
                    let left = self.get_left(node_id);
                    let r_decr_leaf = self.mk_leaf(node_id);
                    let r_der = self.der(left);
                    let result = self.mk_binary(
                        r_der,
                        r_decr_leaf,
                        &mut (|b, left, right| b.mk_concat(left, right)),
                    );
                    result
                }
            }

            Kind::Exists => {
                let exists_bit = node_id.exists_bit(self);
                let exists_body = self.get_right(node_id);
                let body_der = self.der(exists_body);
                match self.get_tregex(body_der) {
                    TRegex::Leaf(_) => {
                        self.mk_unary(body_der, &mut (|b, v| b.mk_exists(exists_bit, v)))
                    }
                    TRegex::ITE(cond_f, f1, f0) => {
                        let cond_f = *cond_f;
                        let f1 = *f1;
                        let f0 = *f0;
                        if cond_f == exists_bit || cond_f == self.mb.solver.not_id(exists_bit) {
                            self.mk_binary(
                                f1,
                                f0,
                                &mut (|b, v1, v2| {
                                    let left = b.mk_exists(exists_bit, v1);
                                    let right = b.mk_exists(exists_bit, v2);
                                    b.mk_union(left, right)
                                }),
                            )
                        } else {
                            self.mk_unary(body_der, &mut (|b, v| b.mk_exists(exists_bit, v)))
                        }
                    }
                }
            }
        };

        if let Some(rw) = self.try_exists_der(node_id, result) {
            self.init_simplified(node_id, rw);
            return self.cache_der(node_id, result);
        }

        return self.cache_der(node_id, result);
    }

    #[inline]
    pub fn is_simplified(&mut self, node_id: NodeId) -> Option<NodeId> {
        if let Some(sim) = self.simplified.get(node_id.0 as usize) {
            if *sim != NodeId::MISSING {
                return Some(*sim);
            }
        }
        return None;
    }

    fn init(&mut self, inst: NodeKey) -> NodeId {
        self.num_created += 1;
        prof!(self, prof_init_calls += 1);
        let node_id = NodeId(self.num_created);
        self.index.insert(inst.clone(), node_id);
        self.array.push(inst.clone());

        match inst.kind {
            Kind::Pred => {
                let set_id = BddId(inst.extra as BddIndex);
                let bits = self.bdd_to_bits(set_id);
                let meta_id = self.mb.get_meta_id(Metadata {
                    flags: MetaFlags::ZERO,
                    bits: bits,
                    cost: 1,
                });
                self.init_metadata(node_id, meta_id);
            }
            Kind::Concat => {
                let left_bits = self.bits(inst.left);
                let right_bits = self.bits(inst.right);
                let bits = self.solver().or_id(left_bits, right_bits);

                let m1 = self.get_node_meta_id(inst.left);
                let m2 = self.get_node_meta_id(inst.right);
                let flags = self.mb.flags_concat(m1, m2);
                let new_id = self.mb.get_meta_id(Metadata {
                    flags,
                    bits: bits,
                    cost: self.mb.cost(m1) + self.mb.cost(m2),
                });
                self.init_metadata(node_id, new_id);
            }
            Kind::Union => {
                let left_bits = self.bits(inst.left);
                let right_bits = self.bits(inst.right);
                let bits = self.solver().or_id(left_bits, right_bits);

                let m1 = self.get_node_meta_id(inst.left);
                let m2 = self.get_node_meta_id(inst.right);
                let metadata = Metadata {
                    flags: self.mb.flags_union(m1, m2),
                    bits,
                    cost: self.mb.cost(m1) + self.mb.cost(m2),
                };
                let meta_id = self.mb.get_meta_id(metadata);
                self.init_metadata(node_id, meta_id);
            }
            Kind::Inter => {
                let left_bits = self.bits(inst.left);
                let right_bits = self.bits(inst.right);
                let bits = self.solver().or_id(left_bits, right_bits);

                let m1 = self.get_node_meta_id(inst.left);
                let m2 = self.get_node_meta_id(inst.right);
                let new_meta = Metadata {
                    flags: self.mb.flags_inter(m1, m2),
                    bits,
                    cost: self.mb.cost(m1) + self.mb.cost(m2),
                };
                let meta_id = self.mb.get_meta_id(new_meta);
                self.init_metadata(node_id, meta_id);
            }
            Kind::Star => {
                let flags = self.flags(inst.left) & MetaFlags::ALL_CONTAINS;
                let meta_id = self.mb.get_meta_id(Metadata {
                    flags: flags | MetaFlags::IS_NULLABLE,
                    bits: self.bits(inst.left),
                    cost: self.cost(inst.left) + 1,
                });
                self.init_metadata(node_id, meta_id);
            }
            Kind::Compl => {
                let bits = self.bits(inst.left);

                let meta_left = self.get_node_meta_id(inst.left);

                let meta_id = self.mb.get_meta_id(Metadata {
                    flags: self.mb.flags_compl(meta_left),
                    bits,
                    cost: self.mb.cost(meta_left) + 1,
                });
                self.init_metadata(node_id, meta_id);
            }

            Kind::Exists => {
                let bits = self.bits(inst.right);
                let bits = self.solver().or_id(bits, BddId(inst.left.0 as BddIndex));
                let meta = self.get_meta(inst.right);
                let meta_right = self.get_node_meta_id(inst.right);

                let meta_id = self.mb.get_meta_id(Metadata {
                    flags: meta.flags | MetaFlags::CONTAINS_EXISTS,
                    bits,
                    cost: self.mb.cost(meta_right) + 1,
                });

                self.init_metadata(node_id, meta_id);
            }
        }

        if LOW_COST_SIMPLIFY && (node_id.is_inter(self) || node_id.is_exists(self)) {
            if node_id.0 < HIGH_LIMIT && self.cost(node_id) < HIGH_SIZE_LIMIT {
                let result = self.simplify(node_id);

                return result;
            }
            if node_id.is_inter(self)
                && node_id.0 < MED_LIMIT
                && self.cost(node_id) < MED_SIZE_LIMIT
            {

                let result = self.simplify(node_id);

                return result;
            }

        }

        // heavyweight simplification for all nodes under a certain size.
        let _cost = self.cost(node_id);
        let cost_limit = if LOW_COST_SIMPLIFY { 30 } else { 50 };
        if !NO_INIT_SIMPLIFY && _cost < cost_limit {
            prof!(self, prof_simplify_calls += 1);
            let result = self.simplify(node_id);
            prof!(
                self,
                prof_simplify_hit += if result != node_id { 1 } else { 0 }
            );
            return result;
        }

        if BOUNDED_SUBSUMES && _cost < 100 && (node_id.is_inter(self) || node_id.is_union(self)) {
            if let Some(rw) = self.attempt_simplify_bounded(node_id, 1000) {
                return rw;
            }
        }

        node_id
    }

    fn init_as(&mut self, key: NodeKey, subsumed: NodeId) -> NodeId {
        self.index.insert(key, subsumed);
        subsumed
    }

    fn init_metadata(&mut self, node_id: NodeId, meta_id: MetadataId) {
        debug_assert!(meta_id != MetadataId::MISSING);
        match self.metadata.get_mut(node_id.0 as usize) {
            Some(v) => *v = meta_id,
            None => {
                self.metadata
                    .resize(node_id.0 as usize * 2, MetadataId::MISSING);
                self.metadata[node_id.0 as usize] = meta_id;
            }
        }
    }

    fn init_simplified(&mut self, node_id: NodeId, simplified_id: NodeId) {
        debug_assert!(simplified_id != NodeId::MISSING);
        match self.simplified.get_mut(node_id.0 as usize) {
            Some(v) => *v = simplified_id,
            None => {
                self.simplified
                    .resize(node_id.0 as usize * 2, NodeId::MISSING);
                self.simplified[node_id.0 as usize] = simplified_id;
            }
        }
    }

    fn init_rev_null(&mut self, der: TRegexId, node_id: NodeId) {
        debug_assert!(node_id != NodeId::MISSING);
        match self.rev_der_cache_null.get_mut(der.0 as usize) {
            Some(v) => *v = node_id,
            None => {
                self.rev_der_cache_null
                    .resize(der.0 as usize * 2, NodeId::MISSING);
                self.rev_der_cache_null[der.0 as usize] = node_id;
            }
        }
    }

    fn init_rev_nonnull(&mut self, der: TRegexId, node_id: NodeId) {
        debug_assert!(node_id != NodeId::MISSING);
        match self.rev_der_cache_nonnull.get_mut(der.0 as usize) {
            Some(v) => *v = node_id, // panic!("{}",1), // ;*v = node_id
            None => {
                self.rev_der_cache_nonnull
                    .resize(der.0 as usize * 2, NodeId::MISSING);
                self.rev_der_cache_nonnull[der.0 as usize] = node_id;
            }
        }
    }

    fn init_bdd_ite(&mut self, bdd: BddId, ite: TRegexId) {
        debug_assert!(ite != TRegexId::MISSING);
        match self.bdd_to_ite.get_mut(bdd.0 as usize) {
            Some(v) => *v = ite,
            None => {
                self.bdd_to_ite
                    .resize(bdd.0 as usize * 2, TRegexId::MISSING);
                self.bdd_to_ite[bdd.0 as usize] = ite;
            }
        }
    }

    fn get_node_id(&mut self, inst: NodeKey) -> NodeId {
        match self.index.get(&inst) {
            Some(&id) => id,
            None => self.init(inst),
        }
    }
    #[inline]
    fn key_is_created(&self, key: &NodeKey) -> Option<&NodeId> {
        self.index.get(key)
    }
    #[inline]
    fn reverse_is_created(&self, inst: &NodeId) -> Option<NodeId> {
        self.reverse_cache.get(inst).copied()
    }

    #[inline]
    pub fn get_left(&self, node_id: NodeId) -> NodeId {
        self.array[node_id.0 as usize].left
    }

    fn starts_with_ts(&self, node_id: NodeId) -> bool {
        if node_id == NodeId::TS {
            return true;
        }
        match self.kind(node_id) {
            Kind::Inter => {
                self.starts_with_ts(self.get_left(node_id))
                    && self.starts_with_ts(self.get_right(node_id))
            }
            Kind::Union => {
                self.starts_with_ts(self.get_left(node_id))
                    && self.starts_with_ts(self.get_right(node_id))
            }
            Kind::Concat => self.starts_with_ts(self.get_left(node_id)),
            Kind::Star => self.starts_with_ts(self.get_left(node_id)),
            _ => false,
        }
    }

    #[inline]
    pub fn get_loop_min_max(&self, node_id: NodeId) -> (u32, u32) {
        let loop_min = self.get_right(node_id).0;
        let loop_max = self.get_extra(node_id);
        (loop_min, loop_max)
    }

    #[inline]
    pub fn get_right(&self, node_id: NodeId) -> NodeId {
        self.array[node_id.0 as usize].right
    }

    #[inline]
    pub fn get_extra(&self, node_id: NodeId) -> u32 {
        self.array[node_id.0 as usize].extra
    }

    #[inline]
    pub fn get_tset(&self, node_id: NodeId) -> TSetId {
        debug_assert!(self.kind(node_id) == Kind::Pred);
        BddId(self.get_extra(node_id) as BddIndex)
    }

    #[inline]
    pub fn kind(&self, node_id: NodeId) -> Kind {
        self.array[node_id.0 as usize].kind
    }

    #[inline]
    pub fn get_node(&self, node_id: NodeId) -> &NodeKey {
        &self.array[node_id.0 as usize]
    }

    #[inline]
    fn get_node_meta_id(&self, node_id: NodeId) -> MetadataId {
        self.metadata[node_id.0 as usize]
    }

    #[inline]
    pub fn bits(&self, node_id: NodeId) -> TSetId {
        let metadata_id = self.metadata[node_id.0 as usize];
        self.mb.array[metadata_id.0 as usize].bits
    }

    #[inline]
    fn get_meta(&self, node_id: NodeId) -> &Metadata {
        debug_assert!(node_id.0 != u32::MAX);
        let meta_id = self.get_node_meta_id(node_id);
        debug_assert!(meta_id != MetadataId::MISSING);
        &self.mb.array[meta_id.0 as usize]
    }

    pub fn cost(&self, node_id: NodeId) -> usize {
        self.get_meta(node_id).cost
    }

    #[inline]
    pub fn flags(&self, node_id: NodeId) -> MetaFlags {
        let meta_id = self.get_node_meta_id(node_id);
        let meta = &self.mb.array[meta_id.0 as usize];
        meta.flags
    }

    #[inline]
    pub fn get_flags_nullability(&self, node_id: NodeId) -> MetaFlags {
        let nullability = self.get_meta(node_id).flags & MetaFlags::IS_NULLABLE;
        nullability
    }

    pub fn reverse(&mut self, node_id: NodeId) -> NodeId {
        if let Some(id) = self.reverse_is_created(&node_id) {
            return id;
        }
        let result = match self.kind(node_id) {
            Kind::Pred => node_id,
            Kind::Concat => {
                let left = node_id.left(self);
                let right = node_id.right(self);
                let left = self.reverse(left);
                let right = self.reverse(right);
                self.mk_concat(right, left)
            }
            Kind::Union => {
                let left = node_id.left(self);
                let right = node_id.right(self);
                let left = self.reverse(left);
                let right = self.reverse(right);
                self.mk_union(left, right)
            }
            Kind::Inter => {
                let left = node_id.left(self);
                let right = node_id.right(self);
                let left = self.reverse(left);
                let right = self.reverse(right);
                self.mk_inter(left, right)
            }
            Kind::Star => {
                let left = node_id.left(self);
                let body = self.reverse(left);
                self.mk_star(body)
            }
            Kind::Compl => {
                let left = node_id.left(self);
                let body = self.reverse(left);
                self.mk_compl(body)
            }
            Kind::Exists => {
                let exists_bit = BddId(node_id.left(self).0 as BddIndex);
                let right = node_id.right(self);
                let body = self.reverse(right);
                self.mk_exists(exists_bit, body)
            }
        };
        self.reverse_cache.insert(node_id, result);
        result
    }

    pub fn mk_pred(&mut self, pred: TSetId) -> NodeId {
        let key = NodeKey {
            kind: Kind::Pred,
            left: NodeId::MISSING,
            right: NodeId::MISSING,
            extra: pred.0,
        };
        self.get_node_id(key)
    }

    pub fn mk_exists(&mut self, exists_bit: TSetId, body_id: NodeId) -> NodeId {
        let key = NodeKey {
            kind: Kind::Exists,
            left: NodeId(exists_bit.0),
            right: body_id,
            extra: u32::MIN,
        };
        if let Some(id) = self.key_is_created(&key) {
            return *id;
        }

        // ∃(R) -> R
        if body_id == NodeId::BOT {
            return self.init_as(key, body_id);
        }
        if body_id == NodeId::TS {
            return self.init_as(key, body_id);
        }
        if body_id == NodeId::TOP {
            return self.init_as(key, body_id);
        }

        if body_id.is_pred(self) {
            let prop_bit = body_id.tset(self);
            let ordbit = self.solver().bdd_builder.get_ref(prop_bit).ordinal;
            let ord = self
                .solver()
                .create_nth_bit_1(ordbit.try_into().expect("overflow"));

            if ord == exists_bit {
                let bdd = *self.solver().bdd_builder.get_ref(prop_bit);
                let p1 = self.bdd_to_pred(bdd.one);
                let p2 = self.bdd_to_pred(bdd.zero);
                let result = self.mk_union(p1, p2);
                return self.init_as(key, result);
            }
        }
        // ∃(R*) => (∃R)*
        if body_id.is_star(self) {
            let star_body = body_id.left(self);
            let inner_exists = self.mk_exists(exists_bit, star_body);
            let result = self.mk_star(inner_exists);
            return self.init_as(key, result);
        }

        // ∃(𝑅·𝑆)≡ ∃(𝑅)·∃(𝑆)
        if body_id.is_concat(self) {
            let left = body_id.left(self);
            let right = body_id.right(self);
            let exists_left = self.mk_exists(exists_bit, left);
            let exists_right = self.mk_exists(exists_bit, right);
            let result = self.mk_concat(exists_left, exists_right);
            return self.init_as(key, result);
        }

        // ∃(𝑅|𝑆)≡ ∃(𝑅)|∃(𝑆)
        if body_id.is_union(self) {
            let left = body_id.left(self);
            let right = body_id.right(self);
            let exists_left = self.mk_exists(exists_bit, left);
            let exists_right = self.mk_exists(exists_bit, right);
            let result = self.mk_union(exists_left, exists_right);
            return self.init_as(key, result);
        }

        let bits = self.bits(body_id);
        if !self.solver().contains_id(bits, exists_bit) {
            return self.init_as(key, body_id);
        }
        if EXTRACT_EXISTS && body_id.is_inter(self) {
            let mut extracted = NodeId::TS;
            let mut kept = NodeId::TS;
            body_id.iter_inter(self, |b, v| {
                let bits = b.bits(v);
                if !b.solver().contains_id(bits, exists_bit) {
                    extracted = b.mk_inter(v, extracted);
                } else {
                    kept = b.mk_inter(v, kept);
                };
            });
            if extracted != NodeId::TS {
                let updated = self.mk_exists(exists_bit, kept);
                let result = self.mk_inter(extracted, updated);
                return self.init_as(key, result);
            }
        }

        self.get_node_id(key)
    }

    #[inline]
    pub fn mk_prop(&mut self, pred: TSetId) -> NodeId {
        self.mk_pred(pred)
    }

    pub fn mk_compl(&mut self, body: NodeId) -> NodeId {
        let key = NodeKey {
            kind: Kind::Compl,
            left: body,
            right: NodeId::MISSING,
            extra: u32::MAX,
        };
        if let Some(id) = self.key_is_created(&key) {
            return *id;
        }

        if let Some(rw) = self.attempt_rw_compl(body) {
            return self.init_as(key, rw);
        }

        self.get_node_id(key)
    }

    pub fn mk_concat(&mut self, head: NodeId, tail: NodeId) -> NodeId {
        match head {
            NodeId::EPS => return tail,
            NodeId::BOT => return NodeId::BOT,
            _ => {}
        }
        match tail {
            NodeId::EPS => return head,
            NodeId::BOT => return NodeId::BOT,
            _ => {}
        }

        let key = NodeKey {
            kind: Kind::Concat,
            left: head,
            right: tail,
            extra: u32::MAX,
        };
        if let Some(id) = self.key_is_created(&key) {
            return *id;
        }

        // R*RR* = R+
        if head.is_star(self) {
            let r = head.left(self);
            if tail.is_concat(self) {
                let tl = tail.left(self);
                let tr = tail.right(self);
                if head == tr && r == tl {
                    let result = self.mk_plus(r);
                    return self.init_as(key, result);
                }
            }
        }

        // normalize, concat always in tail
        if self.kind(head) == Kind::Concat {
            let left = self.get_left(head);
            let result = self.mk_concat(self.get_right(head), tail);
            let result = self.mk_concat(left, result);
            return self.init_as(key, result);
        }

        if self.kind(tail) == Kind::Concat {
            let rtail = self.get_right(tail);
            if let Some(rw) = self.attempt_rw_concat_2(head, self.get_left(tail)) {
                let upd = self.mk_concat(rw, rtail);
                return self.init_as(key, upd);
            }
        }

        match self.attempt_rw_concat_2(head, tail) {
            Some(new) => return self.init_as(key, new),
            None => {}
        }
        self.init(key)
    }

    fn attempt_rw_concat_2(&mut self, head: NodeId, tail: NodeId) -> Option<NodeId> {
        if NO_REWRITES {
            return None;
        }

        if head == NodeId::TS {
            if self.is_nullable(tail) {
                return Some(NodeId::TS);
            }
        }

        if tail == NodeId::TS {
            if self.is_nullable(head) {
                return Some(NodeId::TS);
            }
        }

        if head.is_star(self) {
            let hl = head.left(self);
            if tail == hl {
                let result = self.mk_plus(hl);
                return Some(result);
            }
            if let Some(tail) = tail.is_opt(self) {
                let result = self.mk_union(head, tail);
                return Some(result);
            }
        }

        if self.kind(tail) == Kind::Union {
            // gather topstar to head
            if head == NodeId::TS {
                let mut should_distribute_top = false;
                self.iter_unions(tail, |v| {
                    if self.starts_with_ts(v) {
                        should_distribute_top = true;
                    }
                });
                if should_distribute_top {
                    let mut new_union = NodeId::BOT;
                    let mut curr = tail;
                    while self.kind(curr) == Kind::Union {
                        let new_node = self.mk_concat(NodeId::TS, self.get_left(curr));
                        new_union = self.mk_union(new_node, new_union);
                        curr = self.get_right(curr);
                    }
                    let new_node = self.mk_concat(NodeId::TS, curr);
                    new_union = self.mk_union(new_union, new_node);
                    return Some(new_union);
                }
            }
        }

        if head.is_star(self) {
            if head == tail {
                return Some(head);
            }

            if let Some(head_pred) = head.is_pred_star(self) {
                if let Some(opt_tail) = tail.is_opt(self) {
                    if opt_tail.is_concat(self) {
                        let tl = opt_tail.left(self);
                        let tr = opt_tail.right(self);
                        if tl.is_pred(self) {
                            let h_tset = self.get_tset(head_pred);
                            let t_tset = self.get_tset(tl);
                            // ⁻f*(ε|[g˒⁻f]⁻f* => ⁻f*
                            if self.solver().contains_id(h_tset, t_tset) {
                                // consume 1 char of left
                                let opt_tr = self.mk_opt(tr);
                                let result = self.mk_concat(head, opt_tr);
                                return Some(result);
                            }
                        }
                    }
                }
            }
        }

        None
    }

    fn symmetric_union_rewrites(&mut self, lhs: NodeId, rhs: NodeId) -> Option<NodeId> {
        // ~(e) | ⁻e => ~(e)
        if lhs.is_compl(self) {
            if rhs.is_pred(self) {
                let notright = self.mk_not(rhs);
                if lhs.left(self) == notright {
                    return Some(lhs);
                }
            }
        }

        if let Some(lp) = lhs.is_pred_star(self) {
            if rhs.is_compl(self) {
                if rhs.left(self) == lp {
                    return Some(NodeId::TS);
                }
            }
            if rhs.is_pred(self) && lp.is_contains_pred(rhs, self) {
                return Some(lhs);
            }
            if let Some(rp) = rhs.is_pred_star(self) {
                let result = self.mk_union(rp, lp);
                let result = self.mk_star(result);
                return Some(result);
            }
        }

        if let Some(p_left) = lhs.is_contains(self) {
            // _*R_*|_*S_* => _*(R|S)_*
            if let Some(p_right) = rhs.is_contains(self) {
                let union = self.mk_union(p_left, p_right);
                let result = self.mk_contains(union);
                return Some(result);
            }

            if let Some((_, p_right)) = rhs.is_singleton_constraint(self) {
                // (_*ite(7,T,6)_*|⁻6*[7˒⁻6]⁻6*) => _*ite(7,T,6)_*
                if p_left.is_pred(self) && p_right.is_pred(self) {
                    if p_left.is_contains_pred(p_right, self) {
                        return Some(lhs);
                    }
                }
            }
        }

        if rhs.is_concat(self) {
            if lhs.is_concat(self) {
                let ll = lhs.left(self);
                let rl = rhs.left(self);
                let lr = lhs.right(self);
                let rr = rhs.right(self);

                if ll == rl {
                    let t1 = self.get_right(lhs);
                    let t2 = self.get_right(rhs);
                    // opportunistic rewrites
                    if ll == NodeId::TS {
                        if t2.has_concat_tail(self, t1) {
                            return Some(lhs);
                        }
                        if t1.has_concat_tail(self, t2) {
                            return Some(rhs);
                        }
                    }
                    let un = self.mk_union(t1, t2);
                    return Some(self.mk_concat(self.get_left(lhs), un));
                }

                if ll.is_pred(self) {
                    let not_ll = self.mk_not(ll);
                    // (⁻e_*|e_+) => (_{2,}|⁻e)
                    if not_ll == rl {
                        if lr == NodeId::TS && rr == NodeId::TP {
                            let un = self.mk_union(ll, NodeId::TP2);
                            return Some(un);
                        }
                    }
                }

                if lr == rr {
                    let un = self.mk_union(ll, rl);
                    let result = self.mk_concat(un, rr);
                    return Some(result);
                }
            }

            if lhs.is_pred(self) {
                // good rewrite
                if lhs == self.get_left(rhs) {
                    let rr = rhs.right(self);
                    let un = self.mk_opt(rr);
                    let conc = self.mk_concat(lhs, un);
                    return Some(conc);
                }

            }
        }

        None
    }

    fn symmetric_inter_rewrites(&mut self, lhs: NodeId, rhs: NodeId) -> Option<NodeId> {
        // R & (S1|S2) -> R&S1|R&S2
        if lhs.is_pred(self) || !self.factor {
            if rhs.is_union(self) {
                let mut result = NodeId::BOT;
                self.iter_unions_b(rhs, |b, v| {
                    let new_inter = b.mk_inter(lhs, v);
                    result = b.mk_union(result, new_inter);
                });
                return Some(result);
            }
        }

        if lhs == NodeId::NOTTOP {
            if rhs.is_compl(self) {
                // (~(a)&(ε|_{2,})) -> (ε|_{2,})
                if rhs.left(self).is_pred(self) {
                    return Some(lhs);
                }
            }
        }

        if lhs == NodeId::OPTTOP {
            if rhs.is_compl(self) {
                let rl = rhs.left(self);
                // (~(a)&(ε|_)) -> (ε|-a)
                if rl.is_pred(self) {
                    let notrl = self.mk_not(rl);
                    let result = self.mk_opt(notrl);
                    return Some(result);
                }
            }
        }

        if rhs.is_union(self) {
            let rl = rhs.left(self);
            let rr = rhs.right(self);

            // wrong
            if rl.is_eps() {
                let result = self.mk_inter(lhs, rr);
                let result = self.mk_union(NodeId::EPS, result);
                return Some(result);
            }
        }
        if lhs.is_eps() {
            if rhs.is_nullable(self) {
                return Some(rhs);
            } else {
                return Some(NodeId::BOT);
            }
        }

        if lhs.is_top() {
            if rhs.is_union(self) {
                let rl = rhs.left(self);
                let rr = rhs.right(self);
                // (_&(ε|_{2,}|a)) => a
                // todo?
                if rl.is_eps() {
                    let result = self.mk_inter(lhs, rr);
                    return Some(result);
                }
                if rl.is_tp2() {
                    let result = self.mk_inter(lhs, rr);
                    return Some(result);
                }
                let (minl, _) = self.get_min_max_len(rl);
                if minl >= 1 {
                    return Some(rr);
                }
                let (minr, _) = self.get_min_max_len(rr);
                if minr >= 1 {
                    return Some(rl);
                }
            }
        }

        if lhs.is_compl(self) {
            let (rmin, rmax) = self.get_min_max_len(rhs);
            let ll = lhs.left(self);
            if rhs == ll {
                return Some(NodeId::BOT);
            }
            let ll_lens = self.get_min_max_len(ll);

            if rhs.is_union(self) {
                let rl = rhs.left(self);
                let rr = rhs.right(self);
                if ll == rr {
                    let result = self.mk_inter(lhs, rl);
                    return Some(result);
                }
                if ll == rl {
                    let result = self.mk_inter(lhs, rr);
                    return Some(result);
                }
            }

            if self.unsat_lengths((rmin, rmax), ll_lens) {
                return Some(rhs);
            }

            // ~(_)
            if ll == NodeId::TOP {
                // ~(_) & a => ⊥
                // (~(_)&j_*) and j_+
                if let Some(p) = rhs.is_begins_with_pred(self) {
                    let result = self.mk_concat(p, NodeId::TP);
                    return Some(result);
                }
            }

            // ~(_+)
            if ll == NodeId::TP {
                if let Some(_) = rhs.is_pred_star(self) {
                    return Some(lhs);
                }
            }

            // (~(⁻H*H⁻H*)
            if let Some((lo, lp)) = ll.is_singleton_constraint(self) {
                if let Some((ro, rp)) = rhs.is_singleton_constraint(self) {
                    if lo == ro {
                        // (~(⁻H*H⁻H*)&⁻H*[H˒8]⁻H*) => ⊥
                        let diff = self.mk_diff(rp, lp);
                        if diff.is_bot() {
                            return Some(NodeId::BOT);
                        }
                    }
                }
            }

            // ~(H)
            if ll.is_pred(self) {
                if rhs.is_pred(self) {
                    if !NO_REWRITE_PRED {
                        // predicates
                        let lset = ll.tset(self);
                        let notlset = self.solver().not_id(lset);
                        let rset = rhs.tset(self);
                        let merged = self.solver().and_id(notlset, rset);
                        let result = self.mk_pred(merged);
                        return Some(result);
                    }
                }
            }

            if self.kind(ll) == Kind::Concat {
                let compl_head = self.get_left(ll);
                // not starts with
                if self.get_right(ll) == NodeId::TS {
                    if compl_head == rhs {
                        return Some(NodeId::BOT);
                    }
                }
            }

            // ~(R*)
            if ll.is_star(self) {
                if rhs.is_plus(self) {
                    // (~(R*)&R+) -> ⊥
                    if ll.left(self) == rhs.left(self) {
                        return Some(NodeId::BOT);
                    }
                }
            }

            // (_&~((_{2,}
            if ll.is_union(self) {
                let (rmin, rmax) = self.get_min_max_len(rhs);
                let lbl = ll.left(self);
                let lbr = ll.right(self);

                if rhs == lbl || rhs == lbr {
                    let result = NodeId::BOT;
                    return Some(result);
                }

                if rhs.is_top() {
                    if lbl.is_tp2() {
                        let new_compl = self.mk_compl(lbr);
                        let result = self.mk_inter(new_compl, rhs);
                        return Some(result);
                    }
                    if lbr.is_tp2() {
                        let new_compl = self.mk_compl(lbl);
                        let result = self.mk_inter(new_compl, rhs);
                        return Some(result);
                    }
                }

                // ll unsat
                if self.unsat_lengths((rmin, rmax), self.get_min_max_len(lbl)) {
                    let new_compl = self.mk_compl(lbr);
                    let result = self.mk_inter(new_compl, rhs);
                    return Some(result);
                };

                if self.unsat_lengths((rmin, rmax), self.get_min_max_len(lbr)) {
                    let new_compl = self.mk_compl(lbl);
                    let result = self.mk_inter(new_compl, rhs);
                    return Some(result);
                };
            }
            // ~(A&B) & C
            if ll.is_inter(self) {
                let lll = ll.left(self);
                let llr = ll.right(self);
                if lll == lhs {
                    let new_compl = self.mk_compl(llr);
                    let result = self.mk_inter(new_compl, lhs);
                    return Some(result);
                }
                if llr == rhs {
                    let new_compl = self.mk_compl(lll);
                    let new_inter = self.mk_inter(new_compl, rhs);
                    let result = new_inter;
                    return Some(result);
                }
            }
        }

        if let Some(p_l) = lhs.is_pred_star(self) {
            if let Some(p_r) = rhs.is_pred_star(self) {
                let lset = p_l.tset(self);
                let rset = p_r.tset(self);
                let andset = self.solver().and_id(lset, rset);
                let merged = self.mk_pred(andset);
                return Some(self.mk_star(merged));
            }

            // predicates
            if rhs.is_pred(self) {
                if !NO_REWRITE_PRED {
                    let lset = p_l.tset(self);
                    let rset = rhs.tset(self);
                    let and = self.solver().and_id(lset, rset);
                    let result = self.mk_pred(and);
                    return Some(result);
                }
            }

            // (⁻j*&_*j_*) => ⊥
            if let Some(p_r) = rhs.is_contains(self) {
                if rhs.is_pred(self) {
                    if p_l.is_unsat_pred(p_r, self) {
                        return Some(NodeId::BOT);
                    }
                }
            }

            // distribute pred star
            // this makes rewriting extremely difficult
            if rhs.is_concat(self) {
                let rl = rhs.left(self);
                let rr = rhs.right(self);
                let new_left = self.mk_inter(rl, lhs);
                let new_right = self.mk_inter(rr, lhs);
                let result = self.mk_concat(new_left, new_right);
                return Some(result);
            }

        }

        if let Some(r_pred) = rhs.is_contains(self) {
            if lhs.is_plus(self) {
                // (⁻2⁻2*&_*2_*) => ⊥
                let inter = self.mk_inter(r_pred, lhs.left(self));
                if inter == NodeId::BOT {
                    return Some(inter);
                }
            }
        }

        if let Some((lo, l_pred)) = lhs.is_singleton_constraint(self) {
            if let Some(r_pred) = rhs.is_contains(self) {
                // (_*4_*&⁻4*4⁻4*) => ⁻4*4⁻4*
                if l_pred == r_pred {
                    return Some(lhs);
                }

                if l_pred.is_pred(self) && r_pred.is_pred(self) {
                    // (_*a_*&[^a]*[^a][^a]*) => ⊥
                    if r_pred.is_unsat_pred(l_pred, self) {
                        return Some(NodeId::BOT);
                    }
                }

                if let Some((ro, r_pred)) = rhs.is_singleton_constraint(self) {
                    if r_pred.is_pred(self) && l_pred.is_pred(self) {
                        // -p*p-p* & R(a ⊓ p)S  ==> (R&-p*)(a ⊓ p)(S& -p*)
                        if r_pred.is_contains_pred(l_pred, self) {
                            let lo_star = self.mk_star(lo);
                            let ro_star = self.mk_star(ro);
                            let new_l = self.mk_inter(lo_star, ro_star);
                            let center = self.mk_inter(r_pred, l_pred);
                            let new_r = self.mk_inter(lo_star, ro_star);
                            let result = self.mk_concats([new_l, center, new_r].into_iter());

                            return Some(result);
                        }

                        if lo.is_unsat_pred(r_pred, self) || ro.is_unsat_pred(l_pred, self) {
                            let lo_star = self.mk_star(lo);
                            let ro_star = self.mk_star(ro);
                            let new_l = self.mk_inter(lo_star, ro_star);
                            let center = self.mk_inter(r_pred, l_pred);
                            let new_r = self.mk_inter(lo_star, ro_star);
                            let result = self.mk_concats([new_l, center, new_r].into_iter());

                            return Some(result);
                        }
                    }
                }
            }
        }

        None
    }

    fn attempt_rw_inter_2(&mut self, left: NodeId, right: NodeId) -> Option<NodeId> {
        if left == right {
            return Some(left);
        }

        // A & ~A → ⊥
        if right.is_compl(self) && right.left(self) == left {
            return Some(NodeId::BOT);
        }
        if left.is_compl(self) && left.left(self) == right {
            return Some(NodeId::BOT);
        }

        // cached emptiness: if either child was already proven empty
        if let Some(f) = self.cache_flags.get(&left) {
            if f.is_checked_empty() && f.is_empty() {
                return Some(NodeId::BOT);
            }
        }
        if let Some(f) = self.cache_flags.get(&right) {
            if f.is_checked_empty() && f.is_empty() {
                return Some(NodeId::BOT);
            }
        }

        if left.is_inter(self) {
            self.iter_inters_b(left, |b, v| {
                b.temp_vec.push(v);
            });
            self.iter_inters_b(right, |b, v| {
                b.temp_vec.push(v);
            });
            self.temp_vec.sort();
            let tvec = self.temp_vec.clone();
            self.temp_vec.clear();
            let newnode = tvec
                .into_iter()
                .rev()
                .fold(NodeId::TS, |acc, x| self.mk_inter(x, acc));
            return Some(newnode);
        }

        if right.is_inter(self) {
            let rleft = right.left(&self);
            if left > rleft {
                self.iter_inters_b(left, |b, v| {
                    b.temp_vec.push(v);
                });
                self.iter_inters_b(right, |b, v| {
                    b.temp_vec.push(v);
                });
                self.temp_vec.sort();
                let tvec = self.temp_vec.clone();
                self.temp_vec.clear();
                let newnode = tvec
                    .into_iter()
                    .rev()
                    .fold(NodeId::TS, |acc, x| self.mk_inter(x, acc));
                return Some(newnode);
            } else {
                if let Some(rw) = self.attempt_rw_inters(left, right) {
                    return Some(rw);
                }
            }
        }

        if left.is_compl(self) {
            if right.is_compl(self) {
                let result = self.mk_union(left.left(self), right.left(self));
                let result = self.mk_compl(result);
                return Some(result);
            }
            if right.is_inter(self) && right.left(self).is_compl(self) {
                let result = self.mk_union(left.left(self), right.left(self));
                let result = self.mk_compl(result);
                let result = self.mk_inter(result, right.right(self));
                return Some(result);
            }
            if right.is_inter(self) && right.right(self).is_compl(self) {
                let result = self.mk_union(left.left(self), right.right(self));
                let result = self.mk_compl(result);
                let result = self.mk_inter(result, right.left(self));
                return Some(result);
            }
        }

        let len_l = self.get_min_max_len(left);
        let len_r = self.get_min_max_len(right);

        if self.unsat_lengths(len_l, len_r) {
            return Some(NodeId::BOT);
        }

        if left == NodeId::EPS {
            if self.is_nullable(right) {
                return Some(left);
            } else {
                return Some(NodeId::BOT);
            }
        }

        if left == NodeId::TP {
            if len_r.1 == 0 {
                return Some(NodeId::BOT);
            }
            if len_r.0 >= 1 {
                return Some(right);
            }
            // _+ & a* ==> a+
            if let Some(p) = right.is_pred_star(self) {
                return Some(self.mk_plus(p));
            }

            // (_+&~(⁻i)) ==> (i|__+)
            if right.is_compl(self) {
                let rb = right.left(self);
                if rb.is_pred(self) {
                    let notpred = self.mk_not(rb);
                    let result = self.mk_union(notpred, NodeId::TP2);
                    return Some(result);
                }
                // (_+&~((_{2,}|R))) -> _ & ~(R)
                if rb.is_union(self) {
                    let rbl = rb.left(self);
                    let rbr = rb.left(self);
                    if rbl.is_tp2() {
                        let notrbr = self.mk_not(rbr);
                        let result = self.mk_inter(NodeId::TOP, notrbr);
                        return Some(result);
                    }
                }
                // (_+&~((_{2,}&
                if rb.is_inter(self) {
                    let rbl = rb.left(self);
                    let rbr = rb.left(self);
                    if rbl.is_tp2() {
                        let notrbr = self.mk_not(rbr);
                        let result = self.mk_inter(NodeId::TOP, notrbr);
                        return Some(result);
                    }
                }
            }
        }

        if left.is_tp2() {
            if right.is_compl(self) {
                let rbody = right.left(self);
                if rbody.is_union(self) {
                    if rbody.left(self).is_pred(self) {
                        let remaining_compl = rbody.right(self);
                        let compl = self.mk_compl(remaining_compl);
                        let result = self.mk_inter(left, compl);
                        return Some(result);
                    }
                }
                if let Some(p) = rbody.is_pred2plus(self) {
                    let notp = self.mk_not(p);
                    let contains_notp = self.mk_contains(notp);
                    let result = self.mk_inter(left, contains_notp);
                    return Some(result);
                }
            }
        }

        if left == NodeId::TOP {
            if right.is_concat(self) {
                let rl = right.left(self);
                let rr = right.right(self);
                if rl.is_pred(self) {
                    if rr.is_nullable(self) {
                        return Some(rl);
                    } else {
                        return Some(NodeId::BOT);
                    }
                }
            }
            if right.is_pred(self) {
                return Some(right);
            }
            if !self.factor && right.is_union(self) {
                let rl = self.mk_inter(left, right.left(self));
                let rr = self.mk_inter(left, right.right(self));
                let result = self.mk_union(rl, rr);
                return Some(result);
            }
            if let Some(p) = right.is_pred_star(self) {
                return Some(p);
            }
            if let Some(p) = right.is_contains(self) {
                let inter = self.mk_inter(left, p);
                return Some(inter);
            }
        }

        // bare minimum
        if NO_REWRITES {
            return None;
        }

        if right.is_compl(self) {
            // ~(R)
            let rl = right.left(self);
            if rl == left {
                return Some(NodeId::BOT);
            }
            if rl.is_inter(self) {
                let rll = rl.left(self);
                let rlr = rl.right(self);
                if rll == left {
                    let new_compl = self.mk_compl(rlr);
                    let new_inter = self.mk_inter(left, new_compl);
                    let result = new_inter;
                    return Some(result);
                }
                if rlr == left {
                    let new_compl = self.mk_compl(rll);
                    let new_inter = self.mk_inter(left, new_compl);
                    let result = new_inter;
                    return Some(result);
                }
                if left == NodeId::TOP {
                    if rll == NodeId::TP {
                        let new_compl = self.mk_compl(rlr);
                        let new_inter = self.mk_inter(left, new_compl);
                        let result = new_inter;
                        return Some(result);
                    }
                }
            }
        }

        if left.is_pred(self) {
            // predicates
            if right.is_pred(self) {
                if !NO_REWRITE_PRED {
                    let l = left.tset(&self);
                    let r = right.tset(&self);
                    let psi = self.solver().and_id(l, r);
                    let result = self.mk_pred(psi);
                    return Some(result);
                }
            }

            if right.is_concat(self) {
                let rl = right.left(self);
                let rr = right.right(self);
                if rl.is_pred(self) {
                    if rr.is_nullable(self) {
                        let inter = self.mk_inter(left, rl);
                        return Some(inter);
                    } else {
                        return Some(NodeId::BOT);
                    }
                }
            }

            if let Some((_, i)) = right.is_singleton_constraint(self) {
                if i.is_pred(self) {
                    if left.is_unsat_pred(i, self) {
                        return Some(NodeId::BOT);
                    }
                }
            }

            // (_&⁻w*w⁻w*) => w
            if let Some((_, inner)) = right.is_singleton_constraint(self) {
                if inner.is_pred(self) {
                    let inter = self.mk_inter(left, inner);
                    return Some(inter);
                }
            }
            if right.is_compl(self) {
                // (_&~(⁻w*w⁻w*)) => [^w]
                let rb = right.left(self);
                if let Some((_, inner)) = rb.is_singleton_constraint(self) {
                    if inner.is_pred(self) {
                        let result = self.mk_not(inner);
                        let result = self.mk_inter(left, result);
                        return Some(result);
                    }
                }
            }
        }

        if left.is_concat(self) {
            if right.is_concat(self) {
                let ll = left.left(self);
                let rl = right.left(self);
                let lr = left.right(self);
                let rr = right.right(self);
                if ll.is_pred(self) && rl.is_pred(self) {
                    let new_l = self.mk_inter(ll, rl);
                    let new_r = self.mk_inter(left.right(self), right.right(self));
                    let result = self.mk_concat(new_l, new_r);
                    return Some(result);
                }

                if lr == rr {
                    if let Some(lp) = ll.is_pred_star(self) {
                        if lp == rl {
                            return Some(left);
                        }
                    }
                }
            }
        }

        if right.is_union(self) {
            let rl = right.left(self);
            let rr = right.right(self);
            // (A|(A&B)
            if rl == left {
                return Some(left);
            }
            if rr == left {
                return Some(left);
            }
            // A&(~(A)|(R) -> A&R
            if rl.is_compl(self) && rl.left(self) == left {
                let result = self.mk_inter(left, rr);
                return Some(result);
            }
            if rr.is_compl(self) && rr.left(self) == left {
                let result = self.mk_inter(left, rl);
                return Some(result);
            }
            // important rule
            if !DNF && left.is_union(self) {
                let ll = left.left(self);
                let lr = left.right(self);
                if ll == rl {
                    let rights = self.mk_inter(lr, rr);
                    let result = self.mk_union(ll, rights);
                    return Some(result);
                }
                if ll == rr {
                    let rights = self.mk_inter(lr, rl);
                    let result = self.mk_union(ll, rights);
                    return Some(result);
                }
                if lr == rr {
                    let lefts = self.mk_inter(ll, rl);
                    let result = self.mk_union(lr, lefts);
                    return Some(result);
                }
                if lr == rl {
                    let lefts = self.mk_inter(ll, rr);
                    let result = self.mk_union(lr, lefts);
                    return Some(result);
                }
            }
        }

        if let Some(rw) = self.symmetric_inter_rewrites(left, right) {
            return Some(rw);
        }

        if let Some(rw) = self.symmetric_inter_rewrites(right, left) {
            return Some(rw);
        }

        // todo: first order variables only!!

        None
    }

    fn attempt_rw_union_2(&mut self, left: NodeId, right: NodeId) -> Option<NodeId> {
        if left == right {
            return Some(left);
        }

        if left == NodeId::TS || right == NodeId::TS {
            return Some(NodeId::TS);
        }

        // A | ~A → _*
        if right.is_compl(self) && right.left(self) == left {
            return Some(NodeId::TS);
        }
        if left.is_compl(self) && left.left(self) == right {
            return Some(NodeId::TS);
        }

        // cached fullness: if either child was already proven full
        if let Some(f) = self.cache_flags.get(&left) {
            if f.is_checked_full() && f.is_full() {
                return Some(NodeId::TS);
            }
        }
        if let Some(f) = self.cache_flags.get(&right) {
            if f.is_checked_full() && f.is_full() {
                return Some(NodeId::TS);
            }
        }

        if left.is_union(self) {
            self.iter_unions_b(left, |b, v| {
                b.temp_vec.push(v);
            });
            self.iter_unions_b(right, |b, v| {
                b.temp_vec.push(v);
            });
            self.temp_vec.sort();
            let tvec = self.temp_vec.clone();
            self.temp_vec.clear();
            let newnode = tvec
                .into_iter()
                .rev()
                .fold(NodeId::BOT, |acc, x| self.mk_union(x, acc));
            return Some(newnode);
        }

        if right.is_union(self) {
            let rleft = right.left(&self);
            if left > rleft {
                self.iter_unions_b(left, |b, v| {
                    b.temp_vec.push(v);
                });
                self.iter_unions_b(right, |b, v| {
                    b.temp_vec.push(v);
                });
                self.temp_vec.sort();
                let tvec = self.temp_vec.clone();
                self.temp_vec.clear();
                let newnode = tvec
                    .iter()
                    .rev()
                    .fold(NodeId::BOT, |acc, x| self.mk_union(*x, acc));
                return Some(newnode);
            } else {
                if let Some(rw) = self.attempt_rw_unions(left, right) {
                    return Some(rw);
                }
            }
        }
        // -- bare minimum
        if NO_REWRITES {
            return None;
        }

        if left.is_compl(self) {
            if right.is_compl(self) {
                let result = self.mk_inter(left.left(self), right.left(self));
                let result = self.mk_compl(result);
                return Some(result);
            }

            if right.is_union(self) && right.left(self).is_compl(self) {
                let result = self.mk_inter(left.left(self), right.left(self).left(self));
                let result = self.mk_compl(result);
                let result = self.mk_union(result, right.right(self));
                return Some(result);
            }
            if right.is_union(self) && right.right(self).is_compl(self) {
                let result = self.mk_inter(left.left(self), right.right(self).left(self));
                let result = self.mk_compl(result);
                let result = self.mk_union(result, right.left(self));
                return Some(result);
            }
        }

        if left == NodeId::EPS {
            if self.is_nullable(right) {
                return Some(right);
            }
            // ε|_+ -> _*
            if right == NodeId::TP {
                return Some(NodeId::TS);
            }
            if right.is_union(self) {
                let rl = right.left(self);
                let rr = right.right(self);
                if rl.is_pred(self) {
                    if let Some(p) = rr.is_pred2plus(self) {
                        // (ε|⁻g|[⁻g∧⁻f]{2,}) => (⁻g|[⁻g∧⁻f]*)
                        if rl.is_contains_pred(p, self) {
                            let pstar = self.mk_star(p);
                            let result = self.mk_union(rl, pstar);
                            return Some(result);
                        }
                    }
                }
                // this is a nice rewrite
                // (ε|_{2,}|k) => ~(⁻k)
                if rl == NodeId::TP2 && rr.is_pred(self) {
                    let notpred = self.mk_not(rr);
                    let result = self.mk_compl(notpred);
                    return Some(result);
                }
            }
        }

        if left.is_pred(self) && right.is_pred(self) {
            if !NO_REWRITE_PRED {
                let l = left.tset(&self);
                let r = right.tset(&self);
                let psi = self.solver().or_id(l, r);
                let result = self.mk_pred(psi);
                return Some(result);
            }
        }

        if left == NodeId::TOP {
            // _|_{2,} -> _*
            if right == NodeId::TP2 {
                return Some(NodeId::TP);
            }
            if right.is_inter(self) {
                let rl = right.left(self);
                if rl == NodeId::TP2 {
                    let new_l = NodeId::TP;
                    let result = self.mk_inter(new_l, right.right(self));
                    return Some(result);
                }
            }
            if let Some(p) = right.is_pred2plus(self) {
                let plus = self.mk_plus(p);
                let result = self.mk_union(left, plus);
                return Some(result);
            }
            if right.is_concat(self) {
                let rl = right.left(self);
                let rr = right.right(self);
                if rl.is_pred(self) {
                    if rr == NodeId::TP {
                        let new_t = self.mk_concat(rl, NodeId::TS);
                        let result = self.mk_union(new_t, left);
                        return Some(result);
                    }

                }
            }
        }

        if right.is_inter(self) {
            if right.right(self) == left || right.left(self) == left {
                return Some(left);
            }
        }

        if left == NodeId::TP {
            if right.is_nullable(self) {
                return Some(NodeId::TS);
            }
            if right.is_pred(self) {
                return Some(left);
            }
        }

        if left == NodeId::TP2 {
            if right.is_nullable(self) {
                return Some(NodeId::TS);
            }
            // (_{2,}|j_*) => (_{2,}|j)
            if let Some(p) = right.is_begins_with_pred(self) {
                let result = self.mk_union(left, p);
                return Some(result);
            }
        }

        if right.is_compl(self) {
            let rl = right.left(self);
            if rl == left {
                return Some(NodeId::TS);
            }

            if let Some(l_pred) = left.is_pred_star(self) {
                // (⁻f*|~(⁻f*(ε|[g˒⁻f]⁻f*))) => _*
                if let Some((_, rpred)) = rl.is_singleton_constraint(self) {
                    if rpred.is_pred(self) {
                        let lset = l_pred.tset(self);
                        let pset = rpred.tset(self);
                        if self.solver().contains_id(lset, pset) {
                            return Some(NodeId::TS);
                        }
                    }
                }
            }

            if rl.is_union(self) {
                let rll = rl.left(self);
                let rlr = rl.right(self);
                // A | ~(A|B) -> A | ~B
                if rll == left {
                    let new_compl = self.mk_compl(rlr);
                    let result = self.mk_union(left, new_compl);
                    return Some(result);
                }

                if rlr == left {
                    let new_compl = self.mk_compl(rll);
                    let result = self.mk_union(left, new_compl);
                    return Some(result);
                }
                if left == NodeId::TOP {
                    if rll == NodeId::TP {
                        let new_compl = self.mk_compl(rlr);
                        let new_inter = self.mk_union(left, new_compl);
                        let result = new_inter;
                        return Some(result);
                    }
                }
            }
        }

        if right.is_inter(self) {
            let rl = right.left(self);
            let rr = right.right(self);
            // (A|(A&B)
            if rl == left {
                return Some(left);
            }
            if rr == left {
                return Some(left);
            }
            // A|(~(A)&(R) -> A|(R)
            if rl.is_compl(self) && rl.left(self) == left {
                let result = self.mk_union(left, rr);
                return Some(result);
            }
            // (A&B)|(A&C) -> A & (B|C)
            if !DNF && left.is_inter(self) {
                let ll = left.left(self);
                let lr = left.right(self);
                if ll == rl {
                    let rights = self.mk_union(lr, rr);
                    let result = self.mk_inter(ll, rights);
                    return Some(result);
                }
                if ll == rr {
                    let rights = self.mk_union(lr, rl);
                    let result = self.mk_inter(ll, rights);
                    return Some(result);
                }
                if lr == rr {
                    let lefts = self.mk_union(ll, rl);
                    let result = self.mk_inter(lr, lefts);
                    return Some(result);
                }
                if lr == rl {
                    let lefts = self.mk_union(ll, rr);
                    let result = self.mk_inter(lr, lefts);
                    return Some(result);
                }
            }
        }

        if let Some(rw) = self.symmetric_union_rewrites(left, right) {
            return Some(rw);
        }

        if let Some(rw) = self.symmetric_union_rewrites(right, left) {
            return Some(rw);
        }

        if left == NodeId::EPS {
            if right.is_plus(self) {
                let result = self.mk_star(right.left(self));
                return Some(result);
            }
        }

        if left.is_star(self) {
            // (⁻a*|⁻a⁻a*) => ⁻a*
            if right.is_plus(self) && right.right(self) == left {
                return Some(left);
            }
        }

        // should not be wrong, investigate
        if self.kind(right) == Kind::Concat {
            let rleft = right.left(&self);
            if left == rleft {
                let opt = self.mk_opt(right.right(&self));
                return Some(self.mk_concat(left, opt));
            }
        }

        None
    }

    fn attempt_rw_inters(&mut self, left: NodeId, right_inter: NodeId) -> Option<NodeId> {
        debug_assert!(self.kind(right_inter) == Kind::Inter);
        let mut rewritten: Option<(NodeId, NodeId)> = None;
        right_inter.iter_inter_while(self, |b, v| {
            if let Some(rw) = b.attempt_rw_inter_2(left, v) {
                rewritten = Some((v, rw));
                false
            } else {
                true
            }
        });

        if let Some(rw) = rewritten {
            if rw.0 == rw.1 {
                return Some(right_inter);
            }
            let mut new_inter = NodeId::TS;
            right_inter.iter_inter(self, |b, v| {
                if v == rw.0 {
                    new_inter = b.mk_inter(rw.1, new_inter)
                } else {
                    new_inter = b.mk_inter(v, new_inter)
                }
            });
            return Some(new_inter);
        };
        None
    }

    fn attempt_rw_unions(&mut self, left: NodeId, right_union: NodeId) -> Option<NodeId> {
        debug_assert!(self.kind(right_union) == Kind::Union);
        let mut rewritten = None;
        right_union.iter_union_while(
            self,
            &mut (|b, v| {
                if let Some(rw) = b.attempt_rw_union_2(left, v) {
                    rewritten = Some((v, rw));
                    false
                } else {
                    true
                }
            }),
        );

        if let Some(rw) = rewritten {
            let mut new_union = NodeId::BOT;
            right_union.iter_union(self, |b, v| {
                if v == rw.0 {
                    new_union = b.mk_union(rw.1, new_union)
                } else {
                    new_union = b.mk_union(v, new_union)
                }
            });
            return Some(new_union);
        };

        return None;
    }

    pub fn concat_to_vec(&mut self, concat: NodeId) -> Vec<NodeId> {
        let mut result = Vec::new();
        let mut current = concat;
        while self.kind(current) == Kind::Concat {
            result.push(self.get_left(current));
            current = self.get_right(current);
        }
        result.push(current);
        result
    }

    fn attempt_rw_compl(&mut self, body: NodeId) -> Option<NodeId> {
        if body == NodeId::BOT {
            return Some(NodeId::TS);
        }
        if body.is_compl(self) {
            return Some(body.left(self));
        }
        if body == NodeId::TS {
            return Some(NodeId::BOT);
        }
        if body == NodeId::EPS {
            return Some(NodeId::TP);
        }
        if body == NodeId::TP {
            return Some(NodeId::EPS);
        }
        if body == NodeId::TP2 {
            let result = self.mk_union(NodeId::EPS, NodeId::TOP);
            return Some(result);
        }
        if body == NodeId::TOP {
            let result = self.mk_union(NodeId::EPS, NodeId::TP2);
            return Some(result);
        }

        // ~(ε|_) -> _{2,}
        if body.is_union(self) && body.left(self) == NodeId::EPS && body.right(self) == NodeId::TOP
        {
            let result = NodeId::TP2;
            return Some(result);
        }

        // ~((ε|_{2,})) -> _
        if body.is_union(self) && body.left(self) == NodeId::EPS && body.right(self) == NodeId::TP2
        {
            let result = NodeId::TOP;
            return Some(result);
        }
        // de Morgan: ~(A | B) → ~A & ~B when at least one side is already complemented,
        // which eliminates a complement layer: ~(~X | B) → X & ~B, ~(A | ~Y) → ~A & Y
        // only safe when body contains no exists (complement semantics change under projection)
        if body.is_union(self) && !self.flags(body).contains_exists() {
            let left = body.left(self);
            let right = body.right(self);
            let left_is_compl = left.is_compl(self);
            let right_is_compl = right.is_compl(self);
            if left_is_compl || right_is_compl {
                let nl = if left_is_compl {
                    left.left(self)
                } else {
                    self.mk_compl(left)
                };
                let nr = if right_is_compl {
                    right.left(self)
                } else {
                    self.mk_compl(right)
                };
                let result = self.mk_inter(nl, nr);
                return Some(result);
            }
        }

        if NO_REWRITES {
            return None;
        }

        if body.is_concat(self) {
            let head = body.left(self);
            let tail = body.right(self);
            // ~(a_*) -> [^a]_*|ε
            if tail.is_top_star() && head.is_pred(self) {
                let nothead = self.mk_not(head);
                let case1 = self.mk_concat(nothead, NodeId::TS);
                let case2 = NodeId::EPS;
                let result = self.mk_union(case1, case2);
                return Some(result);
            }
            // ~(⁻k+) -> _*k_*|ε
            if let Some(p) = tail.is_pred_star(self) {
                if p == head {
                    let notp = self.mk_not(p);
                    let contains_notp = self.mk_contains(notp);
                    let result = self.mk_union(contains_notp, NodeId::EPS);
                    return Some(result);
                }
            }
            // ~(a_+) ==> (ε|_|-a_*)
            if head.is_pred(self) && tail == NodeId::TP {
                let nothead = self.mk_not(head);
                let notheadplus = self.mk_concat(nothead, NodeId::TP);
                let result = self.mk_unions([NodeId::TOP, NodeId::EPS, notheadplus].into_iter());
                return Some(result);
            }
        }

        // ~(_*p_*) -> (¬p)* - need to verify that this is correct
        // should be safe since _*p_* contains no exists
        if !NO_COMPL_CONTAINS {
            if let Some(contains_body) = body.is_contains(&self) {
                if contains_body.is_pred(self) {
                    let notpred = self.mk_not(contains_body);
                    let result = self.mk_star(notpred);
                    return Some(result);
                }
            };
        }

        // ~(_*p_*p_*) -> (¬p)*p(¬p)* | ε
        if let Some(p) = body.is_contains2(&self) {
            if p.is_pred(&self) {
                let np = self.mk_not(p);
                let nps = self.mk_star(np);
                let singleton = self.mk_concats([nps, p, nps].into_iter());
                let result = self.mk_opt(singleton);
                return Some(result);
            }
        };

        if let Some((outer, inner)) = body.is_singleton_constraint(&self) {
            if inner.is_pred(self) {
                let notouter = self.mk_not(outer);
                if notouter == inner {
                    // ~(⁻j*j⁻j*) -> ⁻j*|_*j_*j_*
                    let contains2 = self
                        .mk_concats([NodeId::TS, inner, NodeId::TS, inner, NodeId::TS].into_iter());
                    let contains0 = outer;
                    let result = self.mk_union(contains0, contains2);
                    return Some(result);
                }
            }
        };

        if body.is_union(self) {
            let left = body.left(self);
            let right = body.right(self);

            if left.0 < 6 || (left.is_compl(self) && right.is_compl(self)) {
                let left2 = self.mk_compl(left);
                let right2 = self.mk_compl(right);
                let result = self.mk_inter(left2, right2);
                return Some(result);
            }
        }

        if !DNF && body.is_inter(self) {
            let left = body.left(self);
            let right = body.right(self);
            if left.0 < 6 || (left.is_compl(self) || right.is_compl(self)) {
                let left2 = self.mk_compl(left);
                let right2 = self.mk_compl(right);
                let result = self.mk_union(left2, right2);
                return Some(result);
            }
        }

        None
    }

    pub fn mk_union(&mut self, left_id: NodeId, right_id: NodeId) -> NodeId {
        debug_assert!(left_id != NodeId::MISSING);
        debug_assert!(right_id != NodeId::MISSING);
        if left_id > right_id {
            return self.mk_union(right_id, left_id);
        }

        // short-circuit if created
        let key = NodeKey {
            kind: Kind::Union,
            left: left_id,
            right: right_id,
            extra: u32::MAX,
        };
        if let Some(id) = self.key_is_created(&key) {
            return *id;
        }

        if left_id == right_id {
            return left_id;
        }
        if left_id == NodeId::BOT {
            return right_id;
        }
        if right_id == NodeId::BOT {
            return left_id;
        }
        if left_id == NodeId::TS || right_id == NodeId::TS {
            return NodeId::TS;
        }

        if let Some(rw) = self.attempt_rw_union_2(left_id, right_id) {
            return self.init_as(key, rw);
        }
        self.init(key)
    }

    pub fn mk_diff(&mut self, left_id: NodeId, not_right_id: NodeId) -> NodeId {
        let not_right = self.mk_compl(not_right_id);
        self.mk_inter(left_id, not_right)
    }

    pub fn mk_inter(&mut self, left_id: NodeId, right_id: NodeId) -> NodeId {
        debug_assert!(left_id != NodeId::MISSING);
        debug_assert!(right_id != NodeId::MISSING);
        if left_id > right_id {
            return self.mk_inter(right_id, left_id);
        }
        let key = NodeKey {
            kind: Kind::Inter,
            left: left_id,
            right: right_id,
            extra: u32::MAX,
        };
        if let Some(id) = self.key_is_created(&key) {
            return *id;
        }

        if left_id == right_id {
            return left_id;
        }
        if left_id == NodeId::BOT || right_id == NodeId::BOT {
            return NodeId::BOT;
        }
        if left_id == NodeId::TS {
            return right_id;
        }
        if right_id == NodeId::TS {
            return left_id;
        }

        if let Some(rw) = self.attempt_rw_inter_2(left_id, right_id) {
            return self.init_as(key, rw);
        }

        let node = self.init(key);
        node
    }

    pub fn mk_repeat(&mut self, body_id: NodeId, lower: u32, upper: u32) -> NodeId {
        let opt = self.mk_opt(body_id);
        let mut nodes1 = vec![];
        for _ in lower..upper {
            nodes1.push(opt);
        }
        for _ in 0..lower {
            nodes1.push(body_id);
        }
        self.mk_concats(nodes1.into_iter())
    }

    pub fn mk_plus(&mut self, body_id: NodeId) -> NodeId {
        let star = self.mk_star(body_id);
        self.mk_concat(body_id, star)
    }
    pub fn mk_plus2(&mut self, body_id: NodeId) -> NodeId {
        let star = self.mk_plus(body_id);
        self.mk_concat(body_id, star)
    }
    pub fn mk_opt(&mut self, body_id: NodeId) -> NodeId {
        debug_assert!(body_id != NodeId::MISSING);
        self.mk_union(NodeId::EPS, body_id)
    }
    #[inline]
    pub fn get_concat_end(&self, node_id: NodeId) -> NodeId {
        debug_assert!(self.kind(node_id) == Kind::Concat);
        let mut curr = node_id;
        while self.kind(curr) == Kind::Concat {
            curr = self.get_right(curr);
        }
        curr
    }

    pub fn mk_star(&mut self, body_id: NodeId) -> NodeId {
        let key = NodeKey {
            kind: Kind::Star,
            left: body_id,
            right: NodeId::MISSING,
            extra: 0,
        };
        if let Some(id) = self.key_is_created(&key) {
            return *id;
        }
        // _*{500} is still _*
        if body_id.is_kind(self, Kind::Star) {
            return body_id;
        }
        self.get_node_id(key)
    }

    /// pretty-print to string
    pub fn pp(&self, node_id: NodeId) -> String {
        let mut s = String::new();
        self.ppw(&mut s, node_id).unwrap();
        s
    }

    /// pretty-print transition regex
    pub fn ppt(&mut self, term_id: TRegexId) -> String {
        match *self.get_tregex(term_id) {
            TRegex::Leaf(node_id) => {
                let mut s = String::new();
                self.ppw(&mut s, node_id).unwrap();
                s
            }
            TRegex::ITE(cond, then_id, else_id) => {
                format!(
                    "ITE({},{},{})",
                    self.mb.solver.pp(cond),
                    self.ppt(then_id),
                    self.ppt(else_id)
                )
            }
        }
    }

    /// pretty-print to writer
    fn ppw(&self, s: &mut String, node_id: NodeId) -> Result<(), std::fmt::Error> {
        match node_id {
            NodeId::MISSING => return write!(s, "MISSING"),
            NodeId::BOT => return write!(s, "⊥"),
            NodeId::TS => return write!(s, "_*"),
            NodeId::TOP => return write!(s, "_"),
            NodeId::EPS => return write!(s, "ε"),
            _ => {}
        }

        match self.kind(node_id) {
            Kind::Pred => {
                let psi = self.get_tset(node_id);
                if self.mb.solver.is_empty_id(psi) {
                    return write!(s, r"⊥");
                } else if self.mb.solver.is_full_id(psi) {
                    return write!(s, r"_");
                } else {
                    let right = self.get_extra(node_id);
                    let pred = self.mb.solver.pp_bits(BddId(right as BddIndex));
                    write!(s, "{}", pred)
                }
            }
            Kind::Inter => {
                let left = self.get_left(node_id);
                let right = self.get_right(node_id);
                write!(s, "(")?;
                self.ppw(s, left)?;
                write!(s, "&")?;
                let mut curr = right;
                while self.kind(curr) == Kind::Inter {
                    let n = self.get_left(curr);
                    self.ppw(s, n)?;
                    write!(s, "&")?;
                    curr = self.get_right(curr);
                }
                self.ppw(s, curr)?;
                write!(s, ")")
            }
            Kind::Union => {
                let left = self.get_left(node_id);
                let right = self.get_right(node_id);
                write!(s, "(")?;
                self.ppw(s, left)?;
                write!(s, "|")?;
                let mut curr = right;
                while self.kind(curr) == Kind::Union {
                    let n = self.get_left(curr);
                    self.ppw(s, n)?;
                    write!(s, "|")?;
                    curr = self.get_right(curr);
                }
                self.ppw(s, curr)?;
                write!(s, ")")
            }
            Kind::Concat => {
                let left = self.get_left(node_id);
                let right = self.get_right(node_id);
                if right.is_star(self) && right.left(self) == left {
                    self.ppw(s, left)?;
                    write!(s, "+")?;
                    return Ok(());
                }
                if right.is_concat(self) && right.left(self) == left {
                    let mut num = 1;
                    let mut right = right;
                    while right.is_concat(self) && right.left(self) == left {
                        num = num + 1;
                        right = right.right(self);
                    }
                    self.ppw(s, left)?;
                    if right == left {
                        num = num + 1;
                        return write!(s, "{{{}}}", num);
                    }
                    if right.is_star(self) && right.left(self) == left {
                        return write!(s, "{{{},}}", num);
                    }
                    write!(s, "{{{}}}", num)?;
                    return self.ppw(s, right);
                }

                self.ppw(s, left)?;
                self.ppw(s, right)
            }
            Kind::Star => {
                let left = self.get_left(node_id);
                let leftkind = self.kind(left);
                match leftkind {
                    Kind::Concat | Kind::Star | Kind::Compl => {
                        write!(s, "(")?;
                        self.ppw(s, left)?;
                        write!(s, ")")?;
                    }
                    _ => {
                        self.ppw(s, left)?;
                    }
                };
                write!(s, "*")
            }
            Kind::Compl => {
                let left = self.get_left(node_id);
                write!(s, "~(")?;
                self.ppw(s, left)?;
                write!(s, ")")
            }
            Kind::Exists => {
                let right = self.get_right(node_id);
                let prop_bit = self
                    .mb
                    .solver
                    .pp_bits(BddId(self.get_left(node_id).0 as BddIndex));
                write!(s, "∃{}(", prop_bit)?;
                self.ppw(s, right)?;
                write!(s, ")")
            }
        }
    }

    pub fn mk_pred_not(&mut self, set: TSetId) -> NodeId {
        let not_pred = self.solver().not_id(set);
        self.mk_pred(not_pred)
    }

    /// not pred or not prop
    pub fn mk_not(&mut self, node_id: NodeId) -> NodeId {
        if self.kind(node_id) == Kind::Pred {
            let tset = BddId(self.get_extra(node_id) as BddIndex);
            let inverted = self.solver().not_id(tset);
            return self.mk_pred(inverted);
        } else {
            let compl = self.mk_compl(node_id);
            let inter = self.mk_inter(NodeId::TOP, compl);
            return inter;
        }
    }

    pub fn invert_pred(&mut self, node_id: NodeId) -> NodeId {
        debug_assert!(node_id.kind(self) == Kind::Pred);
        let tset = self.get_tset(node_id);
        self.mk_pred_not(tset)
    }

    pub fn mk_u8(&mut self, char: u8) -> NodeId {
        let pred = self.solver().u16_to_set_id(char.into());
        self.mk_pred(pred)
    }

    pub fn mk_range_u8(&mut self, start: u8, end_inclusive: u8) -> NodeId {
        let mut set = NodeId::BOT;
        for c in start..=end_inclusive {
            let c = self.mk_u8(c);
            set = self.mk_union(set, c)
        }
        set
    }

    pub fn mk_bytestring(&mut self, raw_str: &[u8]) -> NodeId {
        let mut result = NodeId::EPS;
        for byte in raw_str.into_iter().rev() {
            let node = self.mk_u8(*byte);
            result = self.mk_concat(node, result);
        }
        result
    }

    pub fn mk_string(&mut self, raw_str: &str) -> NodeId {
        let mut result = NodeId::EPS;
        // iterate string bytes
        for byte in raw_str.bytes().rev() {
            let node = self.mk_u8(byte);
            result = self.mk_concat(node, result);
        }
        result
    }

    pub fn mk_unions(&mut self, nodes: impl Iterator<Item = NodeId>) -> NodeId {
        let mut vec = nodes.collect::<Vec<NodeId>>();
        vec.sort();
        vec.iter()
            .rev()
            .fold(NodeId::BOT, |acc, x| self.mk_union(*x, acc))
    }

    pub fn mk_unions_set(&mut self, nodes: &BTreeSet<NodeId>) -> NodeId {
        nodes
            .iter()
            .rev()
            .fold(NodeId::BOT, |acc, x| self.mk_union(*x, acc))
    }

    pub fn mk_inters(&mut self, nodes: impl DoubleEndedIterator<Item = NodeId>) -> NodeId {
        nodes.rev().fold(NodeId::TS, |acc, v| self.mk_inter(acc, v))
    }

    pub fn mk_concats(&mut self, nodes: impl DoubleEndedIterator<Item = NodeId>) -> NodeId {
        nodes
            .rev()
            .fold(NodeId::EPS, |acc, x| self.mk_concat(x, acc))
    }

    pub fn mk_contains(&mut self, body: NodeId) -> NodeId {
        self.mk_concats([NodeId::TS, body, NodeId::TS].into_iter())
    }
    pub fn mk_begins(&mut self, body: NodeId) -> NodeId {
        self.mk_concats([body, NodeId::TS].into_iter())
    }
    pub fn mk_not_contains(&mut self, body: NodeId) -> NodeId {
        let contains = self.mk_contains(body);
        self.mk_compl(contains)
    }
    pub fn mk_not_contains_singleton(&mut self, body: NodeId) -> NodeId {
        let contains = self.mk_contains(body);
        let not_contains = self.mk_compl(contains);
        self.mk_inter(not_contains, NodeId::TOP)
    }
}

impl RegexBuilder {
    pub fn extract_sat(&self, tregex_id: TRegexId) -> Vec<NodeId> {
        match *self.get_tregex(tregex_id) {
            TRegex::Leaf(node_id) => {
                if NodeId::BOT == node_id {
                    vec![]
                } else {
                    vec![node_id]
                }
            }
            TRegex::ITE(cond, then_id, else_id) => {
                if self.mb.solver.is_empty_id(cond) {
                    return self.extract_sat(else_id);
                }
                let mut then_nodes = self.extract_sat(then_id);
                let mut else_nodes = self.extract_sat(else_id);
                then_nodes.append(&mut else_nodes);
                then_nodes
            }
        }
    }

    pub fn extract_sat_w_cond(
        &mut self,
        beta: TSetId,
        tregex_id: TRegexId,
    ) -> Vec<(NodeId, TSetId)> {
        match *self.get_tregex(tregex_id) {
            TRegex::Leaf(node_id) => {
                if NodeId::BOT == node_id {
                    vec![]
                } else {
                    vec![(node_id, beta)]
                }
            }
            TRegex::ITE(cond, then_id, else_id) => {
                if self.mb.solver.is_empty_id(cond) {
                    return self.extract_sat_w_cond(TSetId::FULL, else_id);
                }
                let c_and = self.mb.solver.and_id(beta, cond);
                let c_not_cond = self.mb.solver.not_id(cond);
                let c_and_not = self.mb.solver.and_id(beta, c_not_cond);
                let mut then_nodes = self.extract_sat_w_cond(c_and, then_id);
                let mut else_nodes = self.extract_sat_w_cond(c_and_not, else_id);
                then_nodes.append(&mut else_nodes);
                then_nodes
            }
        }
    }

    pub fn iter_unions_b(&mut self, curr: NodeId, mut f: impl FnMut(&mut RegexBuilder, NodeId)) {
        let mut curr = curr;
        while self.kind(curr) == Kind::Union {
            let left = curr.left(self);
            let right = curr.right(self);
            f(self, left);
            curr = right;
        }
        f(self, curr);
    }

    pub fn iter_inters_b(&mut self, curr: NodeId, mut f: impl FnMut(&mut RegexBuilder, NodeId)) {
        let mut curr = curr;
        while self.kind(curr) == Kind::Inter {
            let left = curr.left(self);
            curr = curr.right(self);
            f(self, left);
        }
        f(self, curr);
    }

    pub fn iter_sat(&self, start: TRegexId, mut f: impl FnMut(NodeId)) {
        let mut stack = vec![start];
        loop {
            match stack.pop() {
                None => break,
                Some(curr) => match self.get_tregex(curr) {
                    TRegex::Leaf(n) => f(*n),
                    TRegex::ITE(_, then_id, else_id) => {
                        stack.push(*then_id);
                        stack.push(*else_id);
                    }
                },
            }
        }
    }

    pub fn iter_unions(&self, start: NodeId, mut f: impl FnMut(NodeId)) {
        debug_assert!(self.kind(start) == Kind::Union);
        let mut curr = start;
        while self.kind(curr) == Kind::Union {
            f(self.get_left(curr));
            curr = self.get_right(curr);
        }
        f(curr);
    }

    pub fn iter_find_stack(
        &mut self,
        stack: &mut Vec<TRegexId>,
        mut f: impl FnMut(&mut RegexBuilder, NodeId) -> bool,
    ) -> bool {
        loop {
            match stack.pop() {
                None => return false,
                Some(curr) => match *self.get_tregex(curr) {
                    TRegex::Leaf(n) => {
                        let mut curr = n;
                        while curr != NodeId::BOT {
                            match self.kind(curr) {
                                Kind::Union => {
                                    if f(self, self.get_left(curr)) {
                                        return true;
                                    }
                                    curr = self.get_right(curr);
                                }
                                _ => {
                                    if f(self, n) {
                                        return true;
                                    }
                                    curr = NodeId::BOT;
                                }
                            }
                        }
                    }
                    TRegex::ITE(_, then_id, else_id) => {
                        if then_id != TRegexId::BOT {
                            stack.push(then_id);
                        }
                        if else_id != TRegexId::BOT {
                            stack.push(else_id);
                        }
                    }
                },
            }
        }
    }

    pub fn iter_find_stack_split(
        &mut self,
        stack: &mut Vec<TRegexId>,
        mut f: impl FnMut(&mut RegexBuilder, NodeId) -> bool,
    ) -> bool {
        loop {
            match stack.pop() {
                None => return false,
                Some(curr) => match self.get_tregex(curr) {
                    TRegex::Leaf(n) => {
                        let mut curr = *n;
                        while curr != NodeId::BOT {
                            match self.kind(curr) {
                                Kind::Union => {
                                    let leaf = self.mk_leaf(self.get_left(curr));
                                    stack.push(leaf);
                                    curr = self.get_right(curr);
                                }
                                _ => {
                                    if f(self, curr) {
                                        return true;
                                    }
                                    curr = NodeId::BOT;
                                }
                            }
                        }
                    }
                    TRegex::ITE(_, then_id, else_id) => {
                        if THEN_FIRST {
                            if *else_id != TRegexId::BOT {
                                stack.push(*else_id);
                            }
                            stack.push(*then_id);
                        } else {
                            stack.push(*then_id);
                            if *else_id != TRegexId::BOT {
                                stack.push(*else_id);
                            }
                        }
                    }
                },
            }
        }
    }

    pub fn iter_find_valid_split(
        &mut self,
        stack: &mut Vec<TRegexId>,
        mut f: impl FnMut(&mut RegexBuilder, NodeId) -> bool,
    ) -> bool {
        loop {
            match stack.pop() {
                None => return false,
                Some(curr) => match *self.get_tregex(curr) {
                    TRegex::Leaf(n) => {
                        let mut curr = n;
                        while curr != NodeId::TS {
                            match self.kind(curr) {
                                Kind::Inter => {
                                    let leaf = self.mk_leaf(self.get_left(curr));
                                    stack.push(leaf);
                                    curr = self.get_right(curr);
                                }
                                _ => {
                                    if f(self, n) {
                                        return true;
                                    }
                                    curr = NodeId::TS;
                                }
                            }
                        }
                    }
                    TRegex::ITE(_, then_id, else_id) => {
                        stack.push(then_id);
                        if else_id != TRegexId::TOPSTAR {
                            stack.push(else_id);
                        }
                    }
                },
            }
        }
    }

    pub fn iter_find_stack_non_null(
        &self,
        stack: &mut Vec<TRegexId>,
        mut f: impl FnMut(NodeId) -> bool,
    ) -> bool {
        loop {
            match stack.pop() {
                None => return false,
                Some(curr) => match *self.get_tregex(curr) {
                    TRegex::Leaf(n) => {
                        if f(n) {
                            return true;
                        }
                    }
                    TRegex::ITE(_, then_id, else_id) => {
                        stack.push(else_id);
                        stack.push(then_id);
                    }
                },
            }
        }
    }

    pub fn iter_find_stack_counterexample(
        &self,
        stack: &mut Vec<TRegexId>,
        mut f: impl FnMut(NodeId) -> Option<NodeId>,
    ) -> Option<NodeId> {
        loop {
            match stack.pop() {
                None => return None,
                Some(curr) => match *self.get_tregex(curr) {
                    TRegex::Leaf(n) => {
                        let mut curr = n;
                        while curr != NodeId::BOT {
                            match self.kind(curr) {
                                Kind::Union => {
                                    if let Some(v) = f(self.get_left(curr)) {
                                        return Some(v);
                                    }
                                    curr = self.get_right(curr);
                                }
                                _ => {
                                    if let Some(v) = f(n) {
                                        return Some(v);
                                    }
                                    curr = NodeId::BOT;
                                }
                            }
                        }
                    }
                    TRegex::ITE(_, then_id, else_id) => {
                        stack.push(then_id);
                        if else_id != TRegexId::BOT {
                            stack.push(else_id);
                        }
                    }
                },
            }
        }
    }

    pub fn expand_unions(&mut self, node: NodeId, f: &mut impl FnMut(&mut RegexBuilder, NodeId)) {
        use Kind::*;
        if node.is_kind(self, Union) {
            self.iter_unions_b(node, |b, union| {
                b.expand_unions(union, f);
            })
        } else if node.is_kind(self, Kind::Concat) {
            // f(self, node)

            // expensive
            let h1 = node.left(self);
            let t1 = node.right(self);
            if h1.is_kind(self, Kind::Union) {
                self.iter_unions_b(h1, |b, union_head| {
                    let cat = b.mk_concat(union_head, t1);
                    b.expand_unions(cat, f);
                })
            } else {
                f(self, node)
            }
        } else {
            f(self, node)
        }
    }

    pub fn initial_simplify(&mut self, node_id: NodeId) -> Option<NodeId> {
        self.attempt_simplify(node_id)
    }

    pub fn attempt_simplify_bounded(&mut self, node_id: NodeId, budget: u32) -> Option<NodeId> {
        match node_id.kind(self) {
            Kind::Pred | Kind::Exists | Kind::Compl | Kind::Concat | Kind::Star => None,
            Kind::Union => {
                let left = node_id.left(self);
                let right = node_id.right(self);
                if self.subsumes_bounded(left, right, budget) {
                    Some(left)
                } else if self.subsumes_bounded(right, left, budget) {
                    Some(right)
                } else {
                    None
                }
            }
            Kind::Inter => {
                let left = node_id.left(self);
                let right = node_id.right(self);
                if self.subsumes_bounded(left, right, budget) {
                    Some(right)
                } else if self.subsumes_bounded(right, left, budget) {
                    Some(left)
                } else {
                    None
                }
            }
        }
    }

    pub fn attempt_simplify(&mut self, node_id: NodeId) -> Option<NodeId> {
        {
            match node_id.kind(self) {
                Kind::Pred => None,
                Kind::Exists => None,
                Kind::Compl => None,
                Kind::Concat => None,
                Kind::Star => None,
                Kind::Union => {
                    let left = node_id.left(self);
                    let right = node_id.right(self);

                    if self.is_full_lang(node_id) {
                        Some(NodeId::TS)
                    } else if self.subsumes(left, right) {
                        Some(left)
                    } else if self.subsumes(right, left) {
                        Some(right)
                    } else {
                        None
                    }
                }
                Kind::Inter => {
                    let left = node_id.left(self);
                    let right = node_id.right(self);

                    if self.is_empty_lang(node_id) {
                        Some(NodeId::BOT)
                    } else if self.subsumes(left, right) {
                        Some(right)
                    } else if self.subsumes(right, left) {
                        Some(left)
                    } else {
                        None
                    }
                }
            }
        }
    }

    pub fn attempt_simplify_heavy(&mut self, node_id: NodeId) -> Option<NodeId> {
        if node_id.0 < HEAVY_LIMIT && node_id.0 > NodeId::NOTTOP.0 {
            prof!(self, prof_heavy_calls += 1);
            for i in 1..node_id.0 - 1 {
                let n = NodeId(i);
                if self.is_equiv(node_id, n) {

                    return Some(n);
                }
            }
        }

        None
    }

    #[inline]
    pub fn try_exists(&mut self, node_id: NodeId) -> Option<NodeId> {
        if node_id.0 < 6 {
            return None;
        }
        if node_id.0 > LIGHT_LIMIT {
            return None;
        }

        let is_nullable = self.is_nullable(node_id);
        let der = self.der(node_id);

        let entry = if is_nullable {
            self.rev_der_cache_null.get(der.0 as usize)
        } else {
            self.rev_der_cache_nonnull.get(der.0 as usize)
        };

        if let Some(sim) = entry {
            if *sim != NodeId::MISSING {
                let sim = *sim;

                return Some(sim);
            }
        }
        if is_nullable {
            self.init_rev_null(der, node_id);
        } else {
            self.init_rev_nonnull(der, node_id);
        }
        return None;
    }

    #[inline]
    pub fn try_exists_der(&mut self, node_id: NodeId, der: TRegexId) -> Option<NodeId> {
        if node_id.0 < 6 {
            return None;
        }
        if node_id.0 > LIGHT_LIMIT {
            return None;
        }

        let is_nullable = self.is_nullable(node_id);

        let entry = if is_nullable {
            self.rev_der_cache_null.get(der.0 as usize)
        } else {
            self.rev_der_cache_nonnull.get(der.0 as usize)
        };

        if let Some(sim) = entry {
            if *sim != NodeId::MISSING {

                return Some(*sim);
            }
        }
        if is_nullable {
            self.init_rev_null(der, node_id);
        } else {
            self.init_rev_nonnull(der, node_id);
        }
        return None;
    }

    pub fn simplify(&mut self, node_id: NodeId) -> NodeId {
        debug_assert_ne!(NodeId::MISSING, node_id);
        if let Some(sim) = self.simplified.get(node_id.0 as usize) {
            if *sim != NodeId::MISSING {
                return *sim;
            }
        }
        if let Some(rw) = self.attempt_simplify_heavy(node_id) {
            self.init_simplified(node_id, rw);
            return rw;
        } else {
            // node_id
        }
        // node_id

        if let Some(rw) = self.attempt_simplify(node_id) {
            self.init_simplified(node_id, rw);
            if LOW_COST_SIMPLIFY {
                if let Some(o) = self.try_exists(rw) {
                    return o;
                }
            }
            rw
        } else {
            node_id
        }
    }

    pub fn is_full_lang(&mut self, node: NodeId) -> bool {
        debug_assert!(node != NodeId::MISSING);
        if node == NodeId::TS {
            return true;
        }
        if !self.is_nullable(node) {
            return false;
        }
        if let Some(cached) = self.cache_flags.get(&node) {
            if cached.is_checked_full() {
                return cached.is_full();
            }
        }
        prof!(self, prof_is_full_calls += 1);
        // --

        let mut visited = FxHashSet::default();
        let mut visited_valid = FxHashSet::default();
        let compl = self.mk_compl(node);
        let (flags, _) = self.is_sat_recursive(&mut visited, &mut visited_valid, compl);
        flags.is_empty()
    }

    pub fn is_empty_lang(&mut self, node: NodeId) -> bool {
        debug_assert!(node != NodeId::MISSING);
        if node == NodeId::BOT {
            return true;
        }
        if self.is_nullable(node) {
            return false;
        }
        if let Some(cached) = self.cache_flags.get(&node) {
            if cached.is_checked_empty() {
                return cached.is_empty();
            }
        }
        prof!(self, prof_is_empty_calls += 1);
        #[cfg(feature = "profile")]
        let before = self.num_created;

        let mut visited = FxHashSet::default();
        let mut visited_valid = FxHashSet::default();
        let (isempty_flag, _) = self.is_sat_recursive(&mut visited, &mut visited_valid, node);
        prof!(self, prof_is_empty_nodes += (self.num_created - before) as u64);
        isempty_flag.is_empty()
    }

    /// debug: print the first N levels of derivative exploration
    pub fn debug_derivatives(&mut self, node: NodeId, max_depth: usize) {
        let mut stack: Vec<(NodeId, usize)> = vec![(node, 0)];
        let mut seen: FxHashSet<NodeId> = FxHashSet::default();
        seen.insert(NodeId::BOT);
        let mut total_leaves = 0usize;

        while let Some((n, depth)) = stack.pop() {
            if depth > max_depth || seen.contains(&n) {
                continue;
            }
            seen.insert(n);

            let before = self.num_created;
            let kind = self.kind(n);
            let cost = self.cost(n);
            let nullable = self.is_nullable(n);
            let pp_node = self.pp(n);
            let truncated = &pp_node[..pp_node.floor_char_boundary(200)];

            eprintln!(
                "\n--- depth={} node={} kind={:?} cost={} nullable={} ---",
                depth, n.0, kind, cost, nullable
            );
            eprintln!("  expr: {}", truncated);

            let der = self.der(n);
            let after = self.num_created;
            let der_pp = self.ppt(der);
            let der_truncated = &der_pp[..der_pp.floor_char_boundary(500)];
            eprintln!("  der nodes created: {}", after - before);
            eprintln!("  der: {}", der_truncated);

            // collect derivative leaves
            let mut leaves = Vec::new();
            self.iter_sat(der, |leaf| {
                leaves.push(leaf);
            });
            eprintln!("  derivative leaves: {} nodes", leaves.len());
            total_leaves += leaves.len();

            for leaf in &leaves {
                let leaf = *leaf;
                if !seen.contains(&leaf) && leaf != NodeId::BOT {
                    let leaf_kind = self.kind(leaf);
                    let leaf_cost = self.cost(leaf);
                    // show structure: walk into Compl/Inter/Union to see top-level shape
                    let structure = self.debug_structure(leaf, 6);
                    eprintln!(
                        "    leaf {}: kind={:?} cost={} => {}",
                        leaf.0, leaf_kind, leaf_cost, structure
                    );
                    if depth + 1 <= max_depth {
                        stack.push((leaf, depth + 1));
                    }
                }
            }
        }
        eprintln!(
            "\ntotal states seen: {}, total derivative leaves encountered: {}",
            seen.len(),
            total_leaves
        );
        eprintln!("total nodes created: {}", self.num_created);
    }

    /// show top-level structure of a node without full pretty-print
    pub fn debug_structure(&self, node: NodeId, depth: usize) -> String {
        if depth == 0 {
            return format!("[#{}:{:?}:c{}]", node.0, self.kind(node), self.cost(node));
        }
        if node == NodeId::BOT {
            return "⊥".into();
        }
        if node == NodeId::TOP {
            return "_".into();
        }
        if node == NodeId::EPS {
            return "ε".into();
        }
        if node == NodeId::TS {
            return "_*".into();
        }
        match self.kind(node) {
            Kind::Compl => {
                let inner = self.get_left(node);
                format!("~({})", self.debug_structure(inner, depth - 1))
            }
            Kind::Inter => {
                let l = self.get_left(node);
                let r = self.get_right(node);
                format!(
                    "({} & {})",
                    self.debug_structure(l, depth - 1),
                    self.debug_structure(r, depth - 1)
                )
            }
            Kind::Union => {
                let l = self.get_left(node);
                let r = self.get_right(node);
                format!(
                    "({} | {})",
                    self.debug_structure(l, depth - 1),
                    self.debug_structure(r, depth - 1)
                )
            }
            Kind::Concat => {
                let l = self.get_left(node);
                let r = self.get_right(node);
                format!(
                    "({} · {})",
                    self.debug_structure(l, depth - 1),
                    self.debug_structure(r, depth - 1)
                )
            }
            Kind::Exists => {
                let bit = node.exists_bit(self);
                let body = self.get_right(node);
                format!("∃{}({})", bit.0, self.debug_structure(body, depth - 1))
            }
            Kind::Star => {
                let inner = self.get_left(node);
                format!("({})*", self.debug_structure(inner, depth - 1))
            }
            Kind::Pred => {
                format!("[pred#{}]", node.0)
            }
        }
    }

    pub fn all_states(&mut self, node: NodeId) -> FxHashSet<NodeId> {
        let mut states = FxHashSet::default();
        let mut stack = vec![];
        stack.push(node);
        while let Some(n) = stack.pop() {
            let der = self.der(n);
            states.insert(n);
            self.iter_sat(der, |b| {
                if !states.contains(&b) {
                    stack.push(b);
                }
            })
        }
        states
    }

    /// DFS-based emptiness check with proper cycle handling.
    /// Uses an on-stack set for cycle detection (removed on backtrack)
    /// and only caches definitive results (not cycle-dependent ones).
    /// returns (flags, hit_cycle)
    ///
    /// suboptimal: should be refactored to an iterative worklist.
    fn is_sat_recursive(
        &mut self,
        on_stack: &mut FxHashSet<NodeId>,
        _visited_valid: &mut FxHashSet<NodeId>,
        node: NodeId,
    ) -> (NodeFlags, bool) {
        debug_assert!(node != NodeId::MISSING);
        let nonempty = NodeFlags(NodeFlags::IS_NONEMPTY.0 | NodeFlags::CHECKED_EMPTY.0);
        let empty = NodeFlags(NodeFlags::NONE.0 | NodeFlags::CHECKED_EMPTY.0);

        if self.is_nullable(node) {
            return (nonempty, false);
        }
        if let Some(cached) = self.cache_flags.get(&node) {
            if cached.is_checked_empty() {
                return (*cached, false);
            }
        }
        if node == NodeId::BOT {
            return (empty, false);
        }
        if node.is_pred(self) {
            return (nonempty, false);
        }
        // budget exceeded: conservatively return NONEMPTY (can't prove empty), signal cycle to prevent caching
        if self.subsumes_budget > 0 && self.num_created > self.subsumes_budget {
            return (nonempty, true);
        }
        // after multiple cycle-affected empty visits, assume truly empty
        if let Some(&count) = self.cycle_empty_count.get(&node) {
            if count >= 3 {
                return (empty, true);
            }
        }
        // cycle: conservatively return EMPTY, signal cycle
        if on_stack.contains(&node) {
            return (empty, true);
        }
        on_stack.insert(node);

        let (result, hit_cycle) = if node.is_union(self) {
            let left = node.left(self);
            let right = node.right(self);
            let (flags_r, cyc_r) = self.is_sat_recursive(on_stack, _visited_valid, right);
            if flags_r.is_nonempty() {
                (flags_r, cyc_r)
            } else {
                let (flags_l, cyc_l) = self.is_sat_recursive(on_stack, _visited_valid, left);
                if flags_l.is_nonempty() {
                    (flags_l, cyc_l)
                } else {
                    (empty, cyc_r || cyc_l)
                }
            }
        } else if node.is_concat(self) {
            let left = node.left(self);
            let right = node.right(self);
            let (flags_l, cyc_l) = self.is_sat_recursive(on_stack, _visited_valid, left);
            if flags_l.is_empty() {
                (flags_l, cyc_l)
            } else {
                let (flags_r, cyc_r) = self.is_sat_recursive(on_stack, _visited_valid, right);
                (NodeFlags(flags_l.0 & flags_r.0), cyc_l || cyc_r)
            }
        } else if node.is_inter(self) {
            // inter: if either child is empty, intersection is empty
            let left = node.left(self);
            let right = node.right(self);
            let (flags_l, cyc_l) = self.is_sat_recursive(on_stack, _visited_valid, left);
            if flags_l.is_empty() {
                (empty, cyc_l)
            } else {
                let (flags_r, cyc_r) = self.is_sat_recursive(on_stack, _visited_valid, right);
                if flags_r.is_empty() {
                    (empty, cyc_r)
                } else {
                    // both children nonempty - still need derivative check
                    let mut stack = Vec::new();
                    stack.push(self.der(node));
                    let mut any_cycle = cyc_l || cyc_r;
                    let nonempty_found = self.iter_find_stack_split(&mut stack, |b, inner| {
                        let (flags, cyc) = b.is_sat_recursive(on_stack, _visited_valid, inner);
                        if cyc {
                            any_cycle = true;
                        }
                        flags.is_nonempty()
                    });
                    if nonempty_found {
                        (nonempty, any_cycle)
                    } else {
                        (empty, any_cycle)
                    }
                }
            }
        } else {
            let mut stack = Vec::new();
            stack.push(self.der(node));

            let mut any_cycle = false;
            let nonempty_found = self.iter_find_stack_split(&mut stack, |b, inner| {
                let (flags, cyc) = b.is_sat_recursive(on_stack, _visited_valid, inner);
                if cyc {
                    any_cycle = true;
                }
                flags.is_nonempty()
            });
            if nonempty_found {
                (nonempty, any_cycle)
            } else {
                (empty, any_cycle)
            }
        };

        on_stack.remove(&node);

        if !hit_cycle || result.is_nonempty() {
            // cache definitive results: non-cycle or nonempty (always safe)
            let existing = self.cache_flags.get_mut(&node);
            match existing {
                Some(v) => *v = NodeFlags(v.0 | result.0),
                None => {
                    self.cache_flags.insert(node, result);
                }
            }
        } else {
            // cycle-affected empty: track visit count for re-exploration limit
            *self.cycle_empty_count.entry(node).or_insert(0) += 1;
        }
        (result, hit_cycle)
    }

    pub fn mk_equiv(&mut self, a: NodeId, b: NodeId) -> NodeId {
        let nota = self.mk_compl(a);
        let notb = self.mk_compl(b);
        let neither = self.mk_inter(nota, notb);
        let both = self.mk_inter(a, b);
        return self.mk_union(neither, both);
    }

    pub fn mk_equiv_pred(&mut self, a: NodeId, b: NodeId) -> NodeId {
        assert!(a.is_pred(self),);
        assert!(b.is_pred(self),);
        let nota = self.mk_not(a);
        let notb = self.mk_not(b);
        let neither = self.mk_inter(nota, notb);
        let both = self.mk_inter(a, b);
        return self.mk_union(neither, both);
    }

    pub fn is_equiv(&mut self, nodea: NodeId, nodeb: NodeId) -> bool {
        // equiv = A⊕B = (A\B)∪(B\A) = ⊥
        let nota = self.mk_compl(nodea);
        let notb = self.mk_compl(nodeb);
        let anotb = self.mk_inter(nodea, notb);
        let bnota = self.mk_inter(nodeb, nota);
        let diff = self.mk_union(anotb, bnota);
        let empt = self.is_empty_lang(diff);

        empt
    }

    /// subsumes with a node creation budget. returns false if budget exceeded (conservative).
    pub fn subsumes_bounded(
        &mut self,
        larger_lang: NodeId,
        smaller_lang: NodeId,
        budget: u32,
    ) -> bool {
        if larger_lang == smaller_lang {
            return true;
        }
        if !self.is_nullable(larger_lang) && self.is_nullable(smaller_lang) {
            return false;
        }
        let saved_budget = self.subsumes_budget;
        self.subsumes_budget = self.num_created.saturating_add(budget);
        let nota = self.mk_compl(larger_lang);
        let diff = self.mk_inter(smaller_lang, nota);
        let is_empty = self.is_empty_lang(diff);
        self.subsumes_budget = saved_budget;
        is_empty
    }

    pub fn subsumes(&mut self, larger_lang: NodeId, smaller_lang: NodeId) -> bool {
        prof!(self, prof_subsumes_calls += 1);
        debug_assert_ne!(NodeId::MISSING, larger_lang);
        debug_assert_ne!(NodeId::MISSING, smaller_lang);
        // short-circuit
        if larger_lang == smaller_lang {
            return true;
        }
        // assess initial nullability
        if !self.is_nullable(larger_lang) && self.is_nullable(smaller_lang) {
            return false;
        }
        #[cfg(feature = "profile")]
        let before = self.num_created;
        let nota = self.mk_compl(larger_lang);
        let diff = self.mk_inter(smaller_lang, nota);
        let is_empty = self.is_empty_lang(diff);
        prof!(self, prof_subsumes_hits += if is_empty { 1 } else { 0 });
        prof!(self, prof_heavy_nodes += (self.num_created - before) as u64);
        is_empty
    }

    pub fn dot_single_match(&mut self, initial: NodeId, len: i32) -> Result<String, String> {
        let mut id_cache = FxHashMap::default();
        let s0 = initial;
        id_cache.insert(s0, 0);

        let mut visited = FxHashSet::default();
        let mut queue = Vec::new();
        let mut dot = String::new();
        dot.push_str("digraph G {\n");

        queue.push(s0);

        loop {
            match queue.pop() {
                None => break,
                Some(curr) => {
                    if visited.contains(&curr) {
                        continue;
                    }
                    let der = self.der(curr);
                    let conds = self.extract_sat_w_cond(TSetId::FULL, der);

                    for (next, mt) in conds {
                        let prefix = String::new();
                        if next != NodeId::BOT {
                            let pred_str = self.solver().pp(mt);
                            queue.push(next);
                            dot.push_str(&format!(
                                "{} -> {} [label=\"{}{}\"];\n",
                                curr.0, next.0, prefix, pred_str
                            ));
                        }
                    }
                    visited.insert(curr);
                }
            }
        }

        let mut all_nodes = visited.iter().collect::<Vec<_>>();
        all_nodes.sort();

        for (n, i) in all_nodes.iter().enumerate() {
            let nodeid = **i;
            let is_initial = nodeid == initial;
            let is_nullable = self.is_nullable(nodeid);
            let txt = self.pp(nodeid);
            let label = if len < 0 {
                (n + 1).to_string()
            } else if len > 0 && txt.len() > len as usize {
                format!("Node({})", nodeid.0)
            } else {
                txt.to_string()
            };
            let label_w_tags = label;
            let extraattrs = if is_initial {
                let nullcolor = if is_nullable { "green" } else { "black" };
                &format!(",fillcolor=gray,style=filled,color={nullcolor}")
            } else if is_nullable {
                let nullcolor = "green";
                &format!(",style=filled,fillcolor={nullcolor}")
            } else {
                ""
            };
            dot.push_str(&format!(
                "{} [label=\"{}\"{extraattrs}];\n",
                nodeid.0, label_w_tags
            ));
        }
        dot.push_str("}\n");
        Ok(dot)
    }
}
