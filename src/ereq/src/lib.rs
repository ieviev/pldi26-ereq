pub mod lexer;
pub mod parser;
use std::{
    collections::{BTreeMap, HashMap},
    fmt::Write,
};

use ereq_algebra::bdd::BddOrdinal;
pub use ereq_algebra::{
    Kind, NodeId, Nullability, RegexBuilder, solver::Solver, solver::TSetId,
};

#[derive(Debug)]
pub enum EREQError {
    ParserError(String),
}

impl From<EREQError> for Box<dyn std::error::Error> {
    fn from(value: EREQError) -> Self {
        format!("{:?}", value).into()
    }
}

#[derive(Clone, Copy, PartialEq, Hash, Eq, PartialOrd, Ord, Debug)]
pub struct ExprId(pub u32);
impl ExprId {
    pub const FALSE: ExprId = ExprId(0);
    pub const TRUE: ExprId = ExprId(1);
}

#[derive(Debug, Clone)]
pub enum Declaration<'input> {
    Expr(ExprId),
    Pred(&'input str, Option<Vec<&'input str>>, ExprId),
    Macro(&'input str, Option<Vec<&'input str>>, ExprId),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Expr<'input> {
    False, // ⊥
    True,  // _*
    Int(i32),
    Var(&'input str),
    Var2(BddOrdinal),
    Add(ExprId, i32),
    Not(ExprId),
    Or(ExprId, ExprId),
    And(ExprId, ExprId),
    Implies(ExprId, ExprId),
    Equiv(ExprId, ExprId),
    Eq(ExprId, ExprId),
    Ne(ExprId, ExprId),
    Lt(ExprId, ExprId),
    Le(ExprId, ExprId),
    EqSet(ExprId, Vec<i32>),
    Subset(ExprId, ExprId),
    In(ExprId, ExprId),
    Ex1(Vec<&'input str>, ExprId),
    All1(Vec<&'input str>, ExprId),
    Ex2(Vec<&'input str>, ExprId),
    All2(Vec<&'input str>, ExprId),
}

pub struct ExprBuilder<'input> {
    cache: BTreeMap<Expr<'input>, ExprId>,
    pub b: RegexBuilder,
    pub array: Vec<Expr<'input>>,
    pub declared_var2: HashMap<String, BddOrdinal>,
    pub declared_var1: HashMap<String, BddOrdinal>,
    pub declarations: Vec<Declaration<'input>>,
}

impl<'input> ExprBuilder<'input> {
    pub fn new() -> ExprBuilder<'input> {
        let b = ereq_algebra::RegexBuilder::new();
        let mut inst = Self {
            cache: BTreeMap::new(),
            array: Vec::new(),
            declared_var2: HashMap::new(),
            declared_var1: HashMap::new(),
            declarations: Vec::new(),
            b,
        };
        inst.get_id(Expr::False); // mapped to 0
        inst.get_id(Expr::True); // mapped to 1
        inst
    }

    fn create(&mut self, inst: Expr<'input>) -> ExprId {
        let new_id = ExprId(self.cache.len() as u32);
        self.cache.insert(inst.clone(), new_id);
        self.array.push(inst);
        new_id
    }

    pub fn get_id(&mut self, inst: Expr<'input>) -> ExprId {
        match self.cache.get(&inst) {
            Some(v) => *v,
            None => self.create(inst),
        }
    }

    pub fn declare_var2(&mut self, varnames: Vec<&'input str>) {
        // if self.b.num_var2 != i32::MAX {
        //     panic!("all variables must be declared before othexpressions")
        // }

        // ALPHABET BITS: 0..A
        for name in varnames {
            self.declared_var2.insert(
                name.to_string(),
                self.declared_var2.len().try_into().unwrap(),
            );
        }
    }
    pub fn declare_var1(&mut self, varnames: &Vec<&'input str>) {
        for name in varnames {
            if self.declared_var1.get(*name).is_none() {
                let assigned_bit = self.declared_var1.len();
                self.declared_var1
                    .insert(name.to_string(), assigned_bit.try_into().unwrap());
            }
        }
    }

    pub fn comment(&mut self, _expr: &'input str) {}

    pub fn declare_expr(&mut self, expr: ExprId) {
        // fix the number of var2 bits
        self.b.num_var2 = BddOrdinal::try_from(self.declared_var2.len()).expect("overflow");
        self.declarations.push(Declaration::Expr(expr));
    }

    pub fn expr(&mut self, expr_id: ExprId) -> &Expr<'input> {
        &self.array[expr_id.0 as usize]
    }
    pub fn expr_ident(&mut self, name: &'input str) -> ExprId {
        let expr = match self.declared_var2.get(name) {
            Some(n) => self.get_id(Expr::Var2(*n)),
            None => {
                self.get_id(Expr::Var(name))
            }
        };
        expr
    }
    pub fn expr_in(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let expr = self.get_id(Expr::In(left, right));

        if cfg!(debug_assertions) {
            match self.expr(left) {
                Expr::Int(_) => {}
                Expr::Var(_) => {}
                Expr::Add(_, _) => {}

                _ => panic!("expected var1 or int left side: {:?}", self.pp(left)),
            }
        }

        if cfg!(debug_assertions) {
            match self.expr(right) {
                Expr::Var2(_) => {}
                _ => panic!("expected var2 right side: {:?}", self.expr(left)),
            }
        }

        expr
    }
    pub fn expr_notin(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        let expr_in = self.get_id(Expr::In(e0, e1));
        self.expr_not(expr_in)
    }
    pub fn expr_sub(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        self.get_id(Expr::Subset(e0, e1))
    }
    pub fn expr_or(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        self.get_id(Expr::Or(e0, e1))
    }
    pub fn expr_and(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        if e0 == ExprId::TRUE {
            return e1;
        }
        self.get_id(Expr::And(e0, e1))
    }
    pub fn expr_not(&mut self, e0: ExprId) -> ExprId {
        if e0 == ExprId::TRUE {
            return ExprId::FALSE;
        }
        if e0 == ExprId::FALSE {
            return ExprId::TRUE;
        }
        self.get_id(Expr::Not(e0))
    }
    pub fn expr_equiv(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        self.get_id(Expr::Equiv(e0, e1))
    }
    pub fn expr_implies(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        if e0 == ExprId::TRUE {
            return e1;
        }
        self.get_id(Expr::Implies(e0, e1))
    }
    pub fn expr_eq(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        self.get_id(Expr::Eq(e0, e1))
    }
    pub fn expr_ne(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        self.get_id(Expr::Ne(e0, e1))
    }
    pub fn expr_lt(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        self.get_id(Expr::Lt(e0, e1))
    }
    pub fn expr_gt(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        self.get_id(Expr::Lt(e1, e0))
    }
    pub fn expr_le(&mut self, left: ExprId, right: ExprId) -> ExprId {
        self.get_id(Expr::Le(left, right))
    }
    pub fn expr_ge(&mut self, e0: ExprId, e1: ExprId) -> ExprId {
        self.get_id(Expr::Le(e1, e0))
    }
    pub fn expr_eqset(&mut self, e0: ExprId, set: Vec<i32>) -> ExprId {
        self.get_id(Expr::EqSet(e0, set))
    }
    pub fn expr_add(&mut self, e0: ExprId, num: i32) -> ExprId {
        let expr = match self.expr(e0) {
            Expr::Int(0) => self.get_id(Expr::Int(num)),
            _ => self.get_id(Expr::Add(e0, num)),
        };
        expr
    }
    pub fn expr_int(&mut self, num: i32) -> ExprId {
        self.get_id(Expr::Int(num))
    }
    pub fn expr_ex1(&mut self, varnames: Vec<&'input str>, e0: ExprId) -> ExprId {
        self.get_id(Expr::Ex1(varnames, e0))
    }
    pub fn expr_all1(&mut self, varnames: Vec<&'input str>, e0: ExprId) -> ExprId {
        self.get_id(Expr::All1(varnames, e0))
    }

    // pretty printer
    pub fn pp(&mut self, e0: ExprId) -> String {
        let mut s = String::new();
        self.pp_writer(&mut s, e0).unwrap();
        s
    }

    pub fn pp_binary(
        &mut self,
        s: &mut String,
        e0: ExprId,
        operator: &str,
        e1: ExprId,
    ) -> Result<(), std::fmt::Error> {
        write!(s, "(")?;
        self.pp_writer(s, e0)?;
        write!(s, "{}", operator)?;
        self.pp_writer(s, e1)?;
        write!(s, ")")
    }

    pub fn pp_writer(&mut self, s: &mut String, e0: ExprId) -> Result<(), std::fmt::Error> {
        match &self.array[e0.0 as usize] {
            Expr::False => write!(s, "false"),
            Expr::True => write!(s, "true"),
            Expr::Int(i) => write!(s, "{}", i),
            Expr::Var(name) => write!(s, "{}", name),
            Expr::Var2(bit) => {
                let entry = self.declared_var2.iter().find(|v| v.1 == bit).unwrap();
                // write!(s, "({}:bit {})", entry.0, entry.1,)
                // write!(s, "({}: bit{})", entry.0, entry.1,)
                write!(s, "{}", entry.0)
            }
            Expr::Add(e, n) => {
                let n = n.clone();
                self.pp_writer(s, *e)?;
                write!(s, " + {}", n)
            }
            Expr::In(e0, e1) => {
                let e1 = *e1;
                self.pp_binary(s, *e0, " in ", e1)
            }
            Expr::And(e0, e1) => {
                let e1 = *e1;
                self.pp_binary(s, *e0, " & ", e1)
            }
            Expr::Or(e0, e1) => {
                let e1 = *e1;
                self.pp_binary(s, *e0, " | ", e1)
            }
            Expr::Eq(e0, e1) => {
                let e1 = *e1;
                self.pp_binary(s, *e0, " = ", e1)
            }
            Expr::Le(e0, e1) => {
                let e1 = *e1;
                self.pp_binary(s, *e0, " <= ", e1)
            }
            Expr::Lt(e0, e1) => {
                let e1 = *e1;
                self.pp_binary(s, *e0, " < ", e1)
            }
            Expr::Implies(e0, e1) => {
                let e1 = *e1;
                self.pp_binary(s, *e0, " => ", e1)
            }
            Expr::Equiv(e0, e1) => {
                let e1 = *e1;
                self.pp_binary(s, *e0, " <=> ", e1)
            }
            Expr::Ex1(vars, e1) => {
                write!(s, "(ex1")?;
                for v in vars {
                    write!(s, " {}", v)?;
                }
                write!(s, ":")?;
                self.pp_writer(s, *e1)?;
                write!(s, ")")
            }
            Expr::All1(vars, e1) => {
                write!(s, "(all1")?;
                for v in vars {
                    write!(s, " {}", v)?;
                }
                write!(s, ":")?;
                self.pp_writer(s, *e1)?;
                write!(s, ")")
            }
            Expr::Not(e1) => {
                write!(s, "~(")?;
                self.pp_writer(s, *e1)?;
                write!(s, ")")
            }
            e => {
                panic!("unsupported expression in pretty-printer: {:?}", e)
            }
        }
    }
}

pub struct MSO<'input> {
    pub expr_builder: ExprBuilder<'input>,
    pub simplify_initial: bool,
}

impl<'input> MSO<'input> {
    pub fn new() -> MSO<'input> {
        Self {
            expr_builder: ExprBuilder::new(),
            simplify_initial: true,
        }
    }

    pub fn parse_mona_m2l_str(&mut self, input: &'input str) -> Result<NodeId, EREQError> {
        self.expr_builder =
            crate::parser::parse_mona(input).map_err(|e| EREQError::ParserError(e))?;
        let declarations = self.expr_builder.declarations.clone();
        let mut constraints = NodeId::TS;
        for decl in &declarations {
            let decl = decl.clone();
            match decl {
                Declaration::Expr(expr_id) => {
                    let ereq = self.convert_to_ereq(expr_id);
                    constraints = self.b().mk_inter(ereq, constraints)
                }
                Declaration::Pred(..) => return Err(EREQError::ParserError("pred declarations not supported".into())),
                Declaration::Macro(..) => return Err(EREQError::ParserError("macro declarations not supported".into())),
            }
        }

        constraints = self.b().mk_inter(NodeId::TP, constraints);

        Ok(constraints)
    }

    pub fn parse_m2l_str_wo_mona(&mut self, input: &'input str) -> Result<NodeId, EREQError> {
        self.expr_builder =
            crate::parser::parse_mona(input).map_err(|e| EREQError::ParserError(e))?;
        let declarations = self.expr_builder.declarations.clone();
        let mut constraints = NodeId::TS;
        for decl in &declarations {
            let decl = decl.clone();
            match decl {
                Declaration::Expr(expr_id) => {
                    let ereq = self.convert_to_ereq(expr_id);
                    constraints = self.b().mk_inter(ereq, constraints)
                }
                Declaration::Pred(..) => return Err(EREQError::ParserError("pred declarations not supported".into())),
                Declaration::Macro(..) => return Err(EREQError::ParserError("macro declarations not supported".into())),
            }
        }

        Ok(constraints)
    }

    /// regex builder instance
    pub fn b(&mut self) -> &mut RegexBuilder {
        &mut self.expr_builder.b
    }
    /// EBA solver instance
    pub fn solver(&mut self) -> &mut Solver {
        self.expr_builder.b.solver()
    }
    pub fn pp_expr(&mut self, mona_expr: ExprId) -> String {
        self.expr_builder.pp(mona_expr)
    }
    pub fn pp_ereq(&mut self, ereq_node_id: NodeId) -> String {
        self.b().pp(ereq_node_id)
    }
    pub fn get_expr(&mut self, mona_expr: ExprId) -> &Expr<'_> {
        self.expr_builder.expr(mona_expr)
    }

    pub fn get_var1_index(&mut self, name: &str) -> BddOrdinal {
        let var_bit = *self.expr_builder.declared_var1.get(name).unwrap();
        // really we would need to do 2 passes
        // but there will never come a time where we need over 100 bits
        // var_bit + self.expr_builder.declared_var2.len() as BddOrdinal
        var_bit + self.expr_builder.declared_var2.len() as BddOrdinal
    }

    pub fn get_var1_eba(&mut self, name: &str) -> TSetId {
        let index = self.get_var1_index(name);
        self.solver().create_nth_bit_1(index)
    }

    pub fn create_singleton_first_order(&mut self, body: NodeId) -> NodeId {
        let notcontains = self.b().mk_not_contains(body);
        self.b()
            .mk_concats([notcontains, body, notcontains].into_iter())
    }

    pub fn create_expr_in_var2(&mut self, left: ExprId, var2: NodeId) -> NodeId {
        match *self.expr_builder.expr(left) {
            Expr::Int(n) => {
                let nu32 = n.abs() as _;
                let left = self.b().mk_repeat(NodeId::TOP, nu32, nu32);
                self.b().mk_concats([left, var2, NodeId::TS].into_iter())
            }
            Expr::Var(left) => {
                let var1_eba = self.get_var1_eba(left);
                let proposition = self.b().mk_prop(var1_eba);
                let notprop = self.b().mk_not_contains(proposition);
                let intersection = self.b().mk_inter(proposition, var2);
                // a(Xi) => _*(pred&prop)_*
                let elem_in = self
                    .b()
                    .mk_concats([notprop, intersection, notprop].into_iter());
                return elem_in;
            }
            // t+1 in c => _*tc_*
            Expr::Add(t, 1) => {
                let t_ereq = self.convert_to_ereq(t);
                let lhs = self.b().mk_concat(NodeId::TS, t_ereq);
                let rhs = self.b().mk_concat(var2, NodeId::TS);
                let full = self.b().mk_concat(lhs, rhs);
                return full;
            }
            ref e => panic!("unsupported expression in set membership: {:?}", e),
        }
    }

    /// x1 < x2
    pub fn mk_before_first_ord(&mut self, l_ereq: NodeId, r_ereq: NodeId) -> NodeId {
        let both = self.b().mk_union(l_ereq, r_ereq);
        let contains_neither = self.b().mk_not_contains(both);

        let notright = self.b().mk_not(r_ereq);
        let notleft = self.b().mk_not(l_ereq);

        let left_notright = self.b().mk_inter(l_ereq, notright);
        let right_notleft = self.b().mk_inter(r_ereq, notleft);

        self.b().mk_concats(
            [
                contains_neither,
                left_notright,
                contains_neither,
                right_notleft,
                contains_neither,
            ]
            .into_iter(),
        )

        // self.b().mk_concats(
        //     [
        //         NodeId::TS,
        //         l_ereq,
        //         NodeId::TS,
        //         r_ereq,
        //         NodeId::TS,
        //     ]
        //     .into_iter(),
        // )
    }
    /// x1 = x2 + 1
    /// => ereq :  (x1x2)
    ///
    /// t+1 in c
    /// _*tc_*
    pub fn mk_successor_first_ord(&mut self, l_ereq: NodeId, r_ereq: NodeId) -> NodeId {
        let both = self.b().mk_union(l_ereq, r_ereq);
        let contains_neither = self.b().mk_not_contains(both);

        let notright = self.b().mk_not(r_ereq);
        let notleft = self.b().mk_not(l_ereq);

        let left_notright = self.b().mk_inter(l_ereq, notright);
        let right_notleft = self.b().mk_inter(r_ereq, notleft);

        self.b().mk_concats(
            [
                contains_neither,
                left_notright,
                right_notleft,
                contains_neither,
            ]
            .into_iter(),
        )

        // self.b().mk_concats(
        //     [
        //         NodeId::TS,
        //         l_ereq,
        //         r_ereq,
        //         NodeId::TS,
        //     ]
        //     .into_iter(),
        // )
    }

    /// x1 <= x2
    pub fn mk_before_or_eq_first_ord(&mut self, l_ereq: NodeId, r_ereq: NodeId) -> NodeId {
        // let both = self.b().mk_union(l_ereq, r_ereq);
        // let contains_neither = self.b().mk_not_contains(both);

        // let notright = self.b().mk_not(r_ereq);
        // let notleft = self.b().mk_not(l_ereq);

        // let left_notright = self.b().mk_inter(l_ereq, notright);
        // let right_notleft = self.b().mk_inter(r_ereq, notleft);

        let is_same_pos = self.mk_same_pos_first_ord(l_ereq, r_ereq);
        let is_before = self.mk_before_first_ord(l_ereq, r_ereq);
        let result = self.b().mk_union(is_before, is_same_pos);

        // panic!("x");

        // self.b().mk_concats(
        //     [
        //         contains_neither,
        //         left_notright,
        //         contains_neither,
        //         right_notleft,
        //         contains_neither,
        //     ]
        //     .into_iter(),
        // )
        result

        // self.b().mk_concats(
        //     [
        //         NodeId::TS,
        //         l_ereq,
        //         NodeId::TS,
        //         r_ereq,
        //         NodeId::TS,
        //     ]
        //     .into_iter(),
        // )
    }

    pub fn mk_same_pos_first_ord(&mut self, l_ereq: NodeId, r_ereq: NodeId) -> NodeId {
        let both = self.b().mk_union(l_ereq, r_ereq);
        let contains_neither = self.b().mk_not_contains(both);
        let inter = self.b().mk_inter(l_ereq, r_ereq);
        self.b()
            .mk_concats([contains_neither, inter, contains_neither].into_iter())
    }

    pub fn convert_to_ereq(&mut self, expr_id: ExprId) -> NodeId {
        let result = match *self.expr_builder.expr(expr_id) {
            Expr::All1(ref varnames, expr_id) => {
                let names = varnames.clone();
                assert!(
                    names.len() == 1,
                    "declaring multiple variables in exists not implemented"
                );
                self.expr_builder.declare_var1(&names.clone());
                let var1_eba = self.get_var1_eba(names[0]);
                let body = self.convert_to_ereq(expr_id);
                let prop = self.b().mk_prop(var1_eba);
                let notpropstar = self.b().mk_not_contains(prop);
                let singleton = self
                    .b()
                    .mk_concats([notpropstar, prop, notpropstar].into_iter());

                let not_body = self.b().mk_compl(body);

                let ereq_body = self.b().mk_inter(not_body, singleton);

                let ereq = self.b().mk_exists(var1_eba, ereq_body);

                // ∀x0(R) -> ~∃ x0  ~([R])& (x0) = |1|

                self.b().mk_compl(ereq)
            }
            Expr::Ex1(ref varnames, expr_id) => {
                let names = varnames.clone();
                assert!(
                    names.len() == 1,
                    "declaring multiple variables in exists not implemented"
                );
                self.expr_builder.declare_var1(&names.clone());
                let var1_eba = self.get_var1_eba(names[0]);
                let body = self.convert_to_ereq(expr_id);

                // let bits = self.b().bits(body);
                // if !self.solver().contains_id(bits, var1_eba) {
                //     // panic!("x")
                //     return NodeId::BOT;
                // }

                let prop = self.b().mk_prop(var1_eba);
                let notpropstar = self.b().mk_not_contains(prop);

                let singleton = self
                    .b()
                    .mk_concats([notpropstar, prop, notpropstar].into_iter());

                let ereq_body = self.b().mk_inter(singleton, body);
                // let ereq_body = body;
                let exists_node = self.b().mk_exists(var1_eba, ereq_body);
                // ∃ x0 (R) -> ∃(R & |x0| = 1)
                exists_node
            }
            Expr::Var(name) => {
                let eba = self.get_var1_eba(name);
                self.b().mk_prop(eba)
            }
            Expr::Eq(l_expr, r_expr) => {
                match *self.get_expr(r_expr) {
                    // successor: x3 = x2 + 1
                    Expr::Add(r_expr, 1) => {
                        let l_ereq = self.convert_to_ereq(l_expr);
                        let r_ereq = self.convert_to_ereq(r_expr);
                        self.mk_successor_first_ord(r_ereq, l_ereq)
                    }
                    Expr::Add(r_expr, n) => {
                        let l_ereq = self.convert_to_ereq(l_expr);
                        let r_ereq = self.convert_to_ereq(r_expr);
                        let both = self.b().mk_union(l_ereq, r_ereq);
                        let contains_neither = self.b().mk_not_contains(both);
                        let pred_neither = self.b().mk_inter(NodeId::TOP, contains_neither);

                        let notright = self.b().mk_not(r_ereq);
                        let notleft = self.b().mk_not(l_ereq);

                        let left_notright = self.b().mk_inter(l_ereq, notright);
                        let right_notleft = self.b().mk_inter(r_ereq, notleft);
                        let n = n as u32;
                        let loop_ = self.b().mk_repeat(pred_neither, n - 1, n - 1);

                        let result = self.b().mk_concats(
                            [
                                contains_neither,
                                left_notright,
                                loop_,
                                right_notleft,
                                contains_neither,
                            ]
                            .into_iter(),
                        );
                        result
                    }
                    Expr::Int(n) => {
                        let l_ereq = self.convert_to_ereq(l_expr);
                        if n == 0 {
                            // x0 = 0
                            // x0~(_*x0_*)
                            let not_contains = self.b().mk_not_contains(l_ereq);
                            let result = self.b().mk_concats([l_ereq, not_contains].into_iter());
                            result
                        } else if n == 1 {
                            let not_pred = self.b().mk_not(l_ereq);
                            let not_contains = self.b().mk_not_contains(l_ereq);
                            // x1 = 1
                            let result = self
                                .b()
                                .mk_concats([not_pred, l_ereq, not_contains].into_iter());
                            result
                        } else {
                            panic!("equality with constant >= 2 not implemented")
                        }
                    }
                    _ => panic!("unsupported equality form: {}", self.pp_expr(expr_id)),
                }
            }
            Expr::Le(left, right) => {
                if let Expr::Int(0) = self.get_expr(left) {
                    let r_ereq = self.convert_to_ereq(right);
                    return self.b().mk_contains(r_ereq);
                }
                let l_ereq = self.convert_to_ereq(left);
                let r_ereq = self.convert_to_ereq(right);
                self.mk_before_or_eq_first_ord(l_ereq, r_ereq)
            }
            Expr::Lt(left, right) => {
                let l_ereq = self.convert_to_ereq(left);
                let r_ereq = self.convert_to_ereq(right);
                self.mk_before_first_ord(l_ereq, r_ereq)
            }
            Expr::And(left, right) => {
                let _left_ereq = self.convert_to_ereq(left);
                let _right_ereq = self.convert_to_ereq(right);
                self.b().mk_inter(_left_ereq, _right_ereq)
            }
            Expr::Or(left, right) => {
                let _left_ereq = self.convert_to_ereq(left);
                let _right_ereq = self.convert_to_ereq(right);
                self.b().mk_union(_left_ereq, _right_ereq)
            }

            Expr::Not(left) => {
                let body = self.convert_to_ereq(left);
                self.b().mk_compl(body)
            }
            Expr::In(left, right) => {
                let Expr::Var2(var2bit) = *self.expr_builder.expr(right) else {
                    panic!("expected var2 on right");
                };
                let right_set = self.solver().create_nth_bit_1(var2bit);
                let var2 = self.b().mk_pred(right_set);
                self.create_expr_in_var2(left, var2)
            }
            Expr::Implies(left, right) => {
                let _left_ereq = self.convert_to_ereq(left);
                let _right_ereq = self.convert_to_ereq(right);
                let not_l = self.b().mk_compl(_left_ereq);
                self.b().mk_union(not_l, _right_ereq)
            }
            Expr::Equiv(l, r) => {
                // (not(a)&not(b)) | (a&b)
                let notl = self.expr_builder.get_id(Expr::Not(l));
                let notr = self.expr_builder.get_id(Expr::Not(r));
                let l_and_r = self.expr_builder.get_id(Expr::And(l, r));
                let not_l_and_not_r = self.expr_builder.get_id(Expr::And(notl, notr));
                let both_expr = self.expr_builder.get_id(Expr::Or(l_and_r, not_l_and_not_r));
                let both = self.convert_to_ereq(both_expr);
                both
            }
            ref e => {
                panic!("unsupported MSO expression: {:?}", e)
            }
        };

        if self.simplify_initial {
            self.b().initial_simplify(result).unwrap_or(result)
        } else {
            result
        }
    }
}
