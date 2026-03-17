use rustc_hash::FxHashMap;
use std::hash::Hash;

pub type BddOrdinal = i32;
pub type BddIndex = u32;

// 5 bits
pub const MAX_BIT: BddOrdinal = 60;

#[derive(Clone, Copy, PartialEq, Hash, Eq, Debug, PartialOrd, Ord)]
#[repr(transparent)]
pub struct BddId(pub BddIndex);
impl BddId {
    // every bdd has a node-id
    // these 3 can be hardcoded in
    pub const MISSING: BddId = BddId(0);
    pub const FALSE: BddId = BddId(1);
    pub const TRUE: BddId = BddId(2);
}

#[derive(Clone, PartialEq, PartialOrd, Eq, Hash, Debug, Copy, Ord)]
pub struct Bdd {
    pub ordinal: BddOrdinal, // nth bit
    pub one: BddId,          // if true
    pub zero: BddId,         // if false
}

impl Bdd {
    pub fn new(ordinal: BddOrdinal, one: BddId, zero: BddId) -> Bdd {
        Bdd { ordinal, one, zero }
    }

    pub fn is_leaf(&self) -> bool {
        debug_assert_eq!(self.one == BddId::MISSING, self.zero == BddId::MISSING);
        self.one == BddId::MISSING
    }
}

pub struct BddBuilder {
    index: FxHashMap<Bdd, BddId>,
    pub array: Vec<Bdd>,
    pub and_cache: FxHashMap<(BddId, BddId), BddId>,
    pub or_cache: FxHashMap<(BddId, BddId), BddId>,
    pub not_cache: FxHashMap<BddId, BddId>,
}

impl BddBuilder {
    pub fn new() -> BddBuilder {
        let mut inst = Self {
            index: FxHashMap::default(),
            array: Vec::new(),
            and_cache: FxHashMap::default(),
            or_cache: FxHashMap::default(),
            not_cache: FxHashMap::default(),
        };
        // 0 for missing
        let _ = inst.init(Bdd {
            ordinal: -3,
            one: BddId::MISSING,
            zero: BddId::MISSING,
        });
        let _ = inst.init(Bdd {
            ordinal: -1,
            one: BddId::MISSING,
            zero: BddId::MISSING,
        }); // 1 for false
        let _ = inst.init(Bdd {
            ordinal: -2,
            one: BddId::MISSING,
            zero: BddId::MISSING,
        }); // 2 for true
        inst
    }

    fn pp_ord(&self, ord: BddOrdinal) -> String {
        if ord < 26 {
            format!("{}", (97 as u8 + ord as u8) as char)
        } else {
            let ord = ord - 26;
            format!("{}", (65 as u8 + ord as u8) as char)
        }
    }

    fn init(&mut self, inst: Bdd) -> BddId {
        let new_id = BddId(self.index.len() as BddIndex);
        self.index.insert(inst, new_id);
        self.array.push(inst);

        if inst.ordinal > MAX_BIT {
            panic!("todo incr bit: {:?}", inst)
        }
        new_id
    }

    #[inline(always)]
    pub fn deref(&self, bdd_id: BddId) -> Bdd {
        self.array[bdd_id.0 as usize]
    }

    pub fn pp(&self, bdd_id: BddId) -> String {
        match self.deref(bdd_id) {
            Bdd {
                ordinal,
                one: BddId::MISSING,
                zero: BddId::MISSING,
            } => {
                if ordinal == -2 {
                    format!("⊤")
                } else {
                    format!("⊥")
                }
            }
            Bdd {
                ordinal,
                one: BddId::TRUE,
                zero: BddId::FALSE,
            } => {
                format!("{}", (self.pp_ord(ordinal)))
            }
            Bdd {
                ordinal,
                one: BddId::FALSE,
                zero: BddId::TRUE,
            } => {
                format!("⁻{}", (self.pp_ord(ordinal)))
            }
            Bdd {
                ordinal,
                one,
                zero: BddId::FALSE,
            } => {
                format!("({})∧({})", (self.pp_ord(ordinal)), self.pp(one))
            }
            Bdd {
                ordinal,
                one: BddId::FALSE,
                zero,
            } => {
                format!("⁻{}∧{}", (self.pp_ord(ordinal)), self.pp(zero))
            }
            Bdd {
                ordinal,
                one: BddId::TRUE,
                zero,
            } => {
                format!("{}∨{}", (self.pp_ord(ordinal)), self.pp(zero))
            }
            Bdd {
                ordinal,
                one,
                zero: BddId::TRUE,
            } => {
                format!("⁻{}∨{}", (self.pp_ord(ordinal)), self.pp(one))
            }
            bdd => {
                format!(
                    "ite({},{},{})",
                    (self.pp_ord(bdd.ordinal)),
                    self.pp(bdd.one),
                    self.pp(bdd.zero)
                )
            }
        }
    }

    #[inline(always)]
    pub fn get_ref(&self, bdd_id: BddId) -> &Bdd {
        &self.array[bdd_id.0 as usize]
    }

    #[inline(always)]
    pub fn get_id(&mut self, inst: Bdd) -> BddId {
        match self.index.get(&inst) {
            Some(&id) => id,
            None => self.init(inst),
        }
    }

    pub fn and(&mut self, left: BddId, right: BddId) -> BddId {
        if let Some(result) = self.and_cache.get(&(left, right)) {
            return *result;
        }
        if left == right {
            return left;
        }
        if left == BddId::FALSE || right == BddId::FALSE {
            return BddId::FALSE;
        }
        if left == BddId::TRUE {
            return right;
        }
        if right == BddId::TRUE {
            return left;
        }
        let set1 = self.deref(left);
        let set2 = self.deref(right);
        let result = if set2.ordinal > set1.ordinal {
            let one = self.and(set2.one, left);
            let two = self.and(set2.zero, left);
            self.new_bdd(set2.ordinal, one, two)
        } else if set1.ordinal > set2.ordinal {
            let one = self.and(set1.one, right);
            let two = self.and(set1.zero, right);
            self.new_bdd(set1.ordinal, one, two)
        } else {
            let one = self.and(set1.one, set2.one);
            let two = self.and(set1.zero, set2.zero);
            self.new_bdd(set1.ordinal, one, two)
        };
        self.and_cache.insert((left, right), result);
        result
    }
    pub fn or(&mut self, left: BddId, right: BddId) -> BddId {
        if let Some(result) = self.or_cache.get(&(left, right)) {
            return *result;
        }
        if left == right {
            return left;
        }
        if left == BddId::TRUE || right == BddId::TRUE {
            return BddId::TRUE;
        }
        if left == BddId::FALSE {
            return right;
        }
        if right == BddId::FALSE {
            return left;
        }

        let set1 = self.deref(left);
        let set2 = self.deref(right);
        let result = if set2.ordinal > set1.ordinal {
            let one = self.or(set2.one, left);
            let two = self.or(set2.zero, left);
            self.new_bdd(set2.ordinal, one, two)
        } else if set1.ordinal > set2.ordinal {
            let one = self.or(set1.one, right);
            let two = self.or(set1.zero, right);
            self.new_bdd(set1.ordinal, one, two)
        } else {
            let one = self.or(set1.one, set2.one);
            let two = self.or(set1.zero, set2.zero);
            self.new_bdd(set1.ordinal, one, two)
        };
        self.or_cache.insert((left, right), result);
        result
    }
    pub fn not(&mut self, left: BddId) -> BddId {
        if left == BddId::TRUE {
            return BddId::FALSE;
        }
        if left == BddId::FALSE {
            return BddId::TRUE;
        }
        if let Some(result) = self.not_cache.get(&(left)) {
            return *result;
        }
        let v = self.deref(left);
        let one = self.not(v.one);
        let zero = self.not(v.zero);
        let result = self.new_bdd(v.ordinal, one, zero);
        self.not_cache.insert(left, result);
        return result;
    }

    pub fn new_bdd(&mut self, ord: BddOrdinal, one: BddId, zero: BddId) -> BddId {
        if one == zero {
            return one;
        }
        let bdd = Bdd {
            ordinal: ord,
            one,
            zero,
        };
        self.get_id(bdd)
    }

    #[inline]
    pub fn create_nth_bit_1(&mut self, nth_index: BddOrdinal) -> BddId {
        self.new_bdd(nth_index, BddId::TRUE, BddId::FALSE)
    }
    #[inline]
    pub fn create_nth_bit_0(&mut self, nth_index: BddOrdinal) -> BddId {
        self.new_bdd(nth_index, BddId::FALSE, BddId::TRUE)
    }

    pub fn from_ordinal_u16(&mut self, ord: BddOrdinal) -> BddId {
        let mut bdd = BddId::TRUE;
        for k in 0..15 {
            if ord & 1 << k != 0 {
                bdd = self.new_bdd(k, bdd, BddId::FALSE)
            } else {
                bdd = self.new_bdd(k, BddId::FALSE, bdd)
            }
        }
        bdd
    }
}
