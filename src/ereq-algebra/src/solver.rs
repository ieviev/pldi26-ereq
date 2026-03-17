use crate::bdd::{Bdd, BddBuilder, BddId, BddOrdinal};

pub type TSetId = BddId;
impl TSetId {
    pub const EMPTY: TSetId = BddId::FALSE;
    pub const FULL: TSetId = BddId::TRUE;
}
type TSet = Bdd;

pub struct Solver {
    pub bdd_builder: BddBuilder,
}

impl Solver {
    pub fn new() -> Solver {
        let inst = Self {
            bdd_builder: BddBuilder::new(),
        };
        inst
    }

    #[inline(always)]
    pub fn get_set(&self, set_id: TSetId) -> &TSet {
        self.bdd_builder.get_ref(set_id)
    }
    #[inline(always)]
    pub fn deref(&self, set_id: TSetId) -> TSet {
        *self.bdd_builder.get_ref(set_id)
    }

    #[inline(always)]
    pub fn get_id(&mut self, inst: TSet) -> TSetId {
        self.bdd_builder.get_id(inst)
    }

    #[inline(always)]
    pub fn is_negated_condition(&self, condition_id: TSetId) -> bool {
        let bdd = self.bdd_builder.get_ref(condition_id);
        bdd.one == BddId::FALSE && bdd.zero == BddId::TRUE
    }

    pub fn create_nth_bit_1(&mut self, nth_index: BddOrdinal) -> TSetId {
        self.bdd_builder.create_nth_bit_1(nth_index)
    }

    pub fn pp_bits(&self, tset: TSetId) -> String {
        if tset == TSetId::EMPTY {
            return "⊥".to_owned();
        }
        if tset == TSetId::FULL {
            return "_".to_owned();
        }

        format!("{}", self.pp(tset))
    }

    pub fn pp(&self, tset: TSetId) -> String {
        if tset == TSetId::FULL {
            return "_".to_owned();
        }
        if tset == TSetId::EMPTY {
            return "⊥".to_owned();
        }
        let pretty = self.bdd_builder.pp(tset);
        if pretty.contains('∧') || pretty.contains('∨') {
            return format!("[{pretty}]");
        } else {
            return format!("{pretty}");
        }
    }
}

impl Solver {
    #[inline]
    pub fn or_id(&mut self, set1: TSetId, set2: TSetId) -> TSetId {
        self.bdd_builder.or(set1, set2)
    }

    #[inline]
    pub fn and_id(&mut self, set1: TSetId, set2: TSetId) -> TSetId {
        self.bdd_builder.and(set1, set2)
    }

    #[inline]
    pub fn not_id(&mut self, set_id: TSetId) -> TSetId {
        self.bdd_builder.not(set_id)
    }

    #[inline]
    pub fn is_sat_id(&mut self, set1: TSetId, set2: TSetId) -> bool {
        self.and_id(set1, set2) != TSetId::EMPTY
    }
    #[inline]
    pub fn unsat_id(&mut self, set1: TSetId, set2: TSetId) -> bool {
        self.and_id(set1, set2) == TSetId::EMPTY
    }

    #[inline]
    pub fn is_empty_id(&self, set1: TSetId) -> bool {
        set1 == TSetId::EMPTY
    }

    #[inline]
    pub fn is_full_id(&self, set1: TSetId) -> bool {
        set1 == TSetId::FULL
    }

    #[inline]
    pub fn contains_id(&mut self, large_id: TSetId, small_id: TSetId) -> bool {
        let not_large = self.not_id(large_id);
        self.and_id(small_id, not_large) == TSetId::EMPTY
    }

    pub fn u16_to_set_id(&mut self, byte: u16) -> TSetId {
        self.bdd_builder.from_ordinal_u16(byte as _)
    }
}
