//! Translation classes (mt-137, [ADR-0029]): the groups of per-use IR copies
//! that the reference translated as **one shared Kodkod node**, so its
//! polarity-blind `FOL2BoolCache` reused the first visit's translation at every
//! later reach.
//!
//! [ADR-0029]: ../../../docs/adr/0029-polarity-blind-translation-cache.md
//!
//! ## Why classes rather than shared ids
//! The jar memoises a translated formula on `(node identity, the bindings of its
//! free variables)` and **never** on `Environment.negated`, so a node reached at
//! two polarities gets the *first* visit's overflow guard both times
//! (LEDGER-017). mettle's lowerer mints fresh IR per formula-`let` use and per
//! pred call — deliberately, since mt-056 measured that freezing a formula-`let`
//! at its binding site mints skolems the jar refuses — so no shared node ever
//! reaches the (already polarity-blind) encoder caches.
//!
//! A class is the reconciliation: lowering keeps making per-use decisions and
//! merely *records* which roots the jar would have shared, and the encoder and
//! evaluator then treat one class as one node. Where the per-use decisions
//! diverge — most importantly where the skolemizer rewrote one occurrence and
//! not another (probe j6) — the copies are no longer structurally identical and
//! [`validate`] dissolves the class, which is exactly the jar's post-skolem
//! severing.
//!
//! ## What ships
//! [`validate`] is the gate every minted class passes through. It drops
//! - classes with fewer than two distinct member roots (nothing to share), and
//! - classes whose members are not **structurally identical** up to spans and
//!   the renaming of variables bound *inside* the compared subtrees.
//!
//! Free relations (including skolems) compare **by id**: two copies that minted
//! distinct skolem relations are unequal, which is the whole point. Variables
//! bound inside compare up to correspondence, because re-lowering a `let` RHS
//! that contains a quantifier allocates a fresh [`VarId`] each time and the jar
//! still shares that node (probe j5).

use std::collections::{BTreeMap, BTreeSet};

use als_syntax::{define_id, ArenaId};

use crate::ir::{
    CompDecl, FormulaId, FormulaKind, IntExprId, IntExprKind, Ir, RelExprId, RelExprKind, VarId,
};

define_id! {
    /// One group of IR roots the reference would have translated as a single
    /// shared node. Allocation order follows the lowering walk, so it is
    /// deterministic (STYLE D1).
    pub struct TransClassId;
}

/// The empty class table — what every consumer that has no classes to honour
/// borrows: the temporal encode path (ADR-0029 decision 5), the encoder's own
/// unit-test fixtures, and an evaluator built without a goal.
pub(crate) static NO_CLASSES: BTreeMap<FormulaId, TransClassId> = BTreeMap::new();

/// Node-pair comparisons one class may spend before it is dropped unvalidated.
///
/// The IR is a DAG (a `let`-bound relation is lowered once and referenced from
/// every use), so a pairwise walk that cannot memoise — which is the case inside
/// a variable correspondence, see [`StructEq::memoisable`] — can in principle
/// branch exponentially. Rather than reason about when it cannot, the walk is
/// metered: a class that outruns the meter is dropped, costing at worst the jar
/// parity that class would have bought. Deterministic, since the meter counts
/// visits in a fixed traversal order.
const COMPARE_BUDGET: u64 = 1_000_000;

/// Validates the classes minted during one command lowering, returning the table
/// that ships on the goal: member root → its surviving class.
///
/// `members[i]` is the roots registered under `TransClassId::from_index(i)`, in
/// registration (lowering) order. A root registered under two classes — a
/// formula-`let` whose body is nothing but a use, inside a zero-parameter pred —
/// keeps the **lower** class id, which is the outer (pred-call) one, since a
/// pred's class is minted before its body is walked.
pub(crate) fn validate(ir: &Ir, members: &[Vec<FormulaId>]) -> BTreeMap<FormulaId, TransClassId> {
    let mut table: BTreeMap<FormulaId, TransClassId> = BTreeMap::new();
    for (i, roots) in members.iter().enumerate() {
        let distinct: BTreeSet<FormulaId> = roots.iter().copied().collect();
        if distinct.len() < 2 {
            continue;
        }
        let mut eq = StructEq::new(ir);
        let first = roots[0];
        if !roots[1..].iter().all(|&r| eq.formula_eq(first, r)) {
            continue;
        }
        let class = TransClassId::from_index(i);
        for root in distinct {
            table.entry(root).or_insert(class);
        }
    }
    table
}

/// Span-insensitive structural equality over the IR arena, up to a
/// correspondence between variables bound inside the compared subtrees.
struct StructEq<'a> {
    ir: &'a Ir,
    /// The active binder correspondence `(left var, right var)`, innermost last.
    scope: Vec<(VarId, VarId)>,
    /// How many pairs in [`Self::scope`] are non-identity. While this is zero the
    /// correspondence is a no-op, so a comparison's outcome depends only on the
    /// node pair and may be memoised.
    renamed: usize,
    memo_formula: BTreeMap<(FormulaId, FormulaId), bool>,
    memo_rel: BTreeMap<(RelExprId, RelExprId), bool>,
    memo_int: BTreeMap<(IntExprId, IntExprId), bool>,
    budget: u64,
}

impl<'a> StructEq<'a> {
    fn new(ir: &'a Ir) -> Self {
        StructEq {
            ir,
            scope: Vec::new(),
            renamed: 0,
            memo_formula: BTreeMap::new(),
            memo_rel: BTreeMap::new(),
            memo_int: BTreeMap::new(),
            budget: COMPARE_BUDGET,
        }
    }

    /// Whether the current correspondence is inert, so results are context-free.
    fn memoisable(&self) -> bool {
        self.renamed == 0
    }

    /// Charges one node-pair visit; `false` once the meter is spent, which the
    /// callers propagate as "not identical" (the class is then dropped).
    fn charge(&mut self) -> bool {
        if self.budget == 0 {
            return false;
        }
        self.budget -= 1;
        true
    }

    /// Pushes a binder correspondence, rejecting a pair whose declared arities
    /// disagree (the copies then denote different bindings, not one renamed).
    fn push_binder(&mut self, a: VarId, b: VarId) -> bool {
        if self.ir.vars[a].arity != self.ir.vars[b].arity {
            return false;
        }
        if a != b {
            self.renamed += 1;
        }
        self.scope.push((a, b));
        true
    }

    fn pop_binder(&mut self) {
        if let Some((a, b)) = self.scope.pop() {
            if a != b {
                self.renamed -= 1;
            }
        }
    }

    /// Two variable *uses* correspond when they are bound at the same binder
    /// depth on their own side, or are both free and literally the same variable
    /// (a free variable was bound outside both copies, so the copies share it).
    fn var_eq(&self, a: VarId, b: VarId) -> bool {
        let ia = self.scope.iter().rposition(|&(l, _)| l == a);
        let ib = self.scope.iter().rposition(|&(_, r)| r == b);
        match (ia, ib) {
            (None, None) => a == b,
            (Some(i), Some(j)) => i == j,
            _ => false,
        }
    }

    fn formula_eq(&mut self, a: FormulaId, b: FormulaId) -> bool {
        if a == b && self.memoisable() {
            return true;
        }
        if self.memoisable() {
            if let Some(&hit) = self.memo_formula.get(&(a, b)) {
                return hit;
            }
        }
        if !self.charge() {
            return false;
        }
        let out = self.formula_eq_uncached(a, b);
        if self.memoisable() {
            self.memo_formula.insert((a, b), out);
        }
        out
    }

    #[allow(
        clippy::match_same_arms,
        clippy::too_many_lines,
        reason = "one arm per node-kind pair keeps the exhaustiveness check honest \
                  (PORTING R1): a new kind must be handled here, not swallowed — and \
                  that is the whole length"
    )]
    fn formula_eq_uncached(&mut self, a: FormulaId, b: FormulaId) -> bool {
        match (&self.ir.formulas[a].kind, &self.ir.formulas[b].kind) {
            (FormulaKind::Const(x), FormulaKind::Const(y)) => x == y,
            (FormulaKind::Not(x), FormulaKind::Not(y)) => {
                let (x, y) = (*x, *y);
                self.formula_eq(x, y)
            }
            (FormulaKind::And(xs), FormulaKind::And(ys))
            | (FormulaKind::Or(xs), FormulaKind::Or(ys)) => {
                let (xs, ys) = (xs.clone(), ys.clone());
                xs.len() == ys.len()
                    && xs
                        .iter()
                        .zip(ys.iter())
                        .all(|(&x, &y)| self.formula_eq(x, y))
            }
            (
                FormulaKind::Implies {
                    antecedent: xa,
                    consequent: xc,
                },
                FormulaKind::Implies {
                    antecedent: ya,
                    consequent: yc,
                },
            ) => {
                let (xa, xc, ya, yc) = (*xa, *xc, *ya, *yc);
                self.formula_eq(xa, ya) && self.formula_eq(xc, yc)
            }
            (FormulaKind::Iff(xl, xr), FormulaKind::Iff(yl, yr)) => {
                let (xl, xr, yl, yr) = (*xl, *xr, *yl, *yr);
                self.formula_eq(xl, yl) && self.formula_eq(xr, yr)
            }
            (
                FormulaKind::RelCompare {
                    op: xo,
                    lhs: xl,
                    rhs: xr,
                },
                FormulaKind::RelCompare {
                    op: yo,
                    lhs: yl,
                    rhs: yr,
                },
            ) => {
                let (xo, xl, xr, yo, yl, yr) = (*xo, *xl, *xr, *yo, *yl, *yr);
                xo == yo && self.rel_eq(xl, yl) && self.rel_eq(xr, yr)
            }
            (
                FormulaKind::IntCompare {
                    op: xo,
                    lhs: xl,
                    rhs: xr,
                },
                FormulaKind::IntCompare {
                    op: yo,
                    lhs: yl,
                    rhs: yr,
                },
            ) => {
                let (xo, xl, xr, yo, yl, yr) = (*xo, *xl, *xr, *yo, *yl, *yr);
                xo == yo && self.int_eq(xl, yl) && self.int_eq(xr, yr)
            }
            (
                FormulaKind::MultTest { test: xt, expr: xe },
                FormulaKind::MultTest { test: yt, expr: ye },
            ) => {
                let (xt, xe, yt, ye) = (*xt, *xe, *yt, *ye);
                xt == yt && self.rel_eq(xe, ye)
            }
            (
                FormulaKind::Quant {
                    kind: xk,
                    var: xv,
                    bound: xb,
                    body: xbody,
                },
                FormulaKind::Quant {
                    kind: yk,
                    var: yv,
                    bound: yb,
                    body: ybody,
                },
            ) => {
                let (xk, xv, xb, xbody) = (*xk, *xv, *xb, *xbody);
                let (yk, yv, yb, ybody) = (*yk, *yv, *yb, *ybody);
                if xk != yk || !self.rel_eq(xb, yb) || !self.push_binder(xv, yv) {
                    return false;
                }
                let out = self.formula_eq(xbody, ybody);
                self.pop_binder();
                out
            }
            (
                FormulaKind::TemporalUnary { op: xo, body: xb },
                FormulaKind::TemporalUnary { op: yo, body: yb },
            ) => {
                let (xo, xb, yo, yb) = (*xo, *xb, *yo, *yb);
                xo == yo && self.formula_eq(xb, yb)
            }
            (
                FormulaKind::TemporalBinary {
                    op: xo,
                    lhs: xl,
                    rhs: xr,
                },
                FormulaKind::TemporalBinary {
                    op: yo,
                    lhs: yl,
                    rhs: yr,
                },
            ) => {
                let (xo, xl, xr, yo, yl, yr) = (*xo, *xl, *xr, *yo, *yl, *yr);
                xo == yo && self.formula_eq(xl, yl) && self.formula_eq(xr, yr)
            }
            (FormulaKind::LoopIs { state: x }, FormulaKind::LoopIs { state: y }) => x == y,
            // Different kinds — and every remaining same-kind pairing is covered
            // above, so this is the genuine mismatch arm.
            (
                FormulaKind::Const(_)
                | FormulaKind::Not(_)
                | FormulaKind::And(_)
                | FormulaKind::Or(_)
                | FormulaKind::Implies { .. }
                | FormulaKind::Iff(..)
                | FormulaKind::RelCompare { .. }
                | FormulaKind::IntCompare { .. }
                | FormulaKind::MultTest { .. }
                | FormulaKind::Quant { .. }
                | FormulaKind::TemporalUnary { .. }
                | FormulaKind::TemporalBinary { .. }
                | FormulaKind::LoopIs { .. },
                _,
            ) => false,
        }
    }

    fn rel_eq(&mut self, a: RelExprId, b: RelExprId) -> bool {
        if a == b && self.memoisable() {
            return true;
        }
        if self.memoisable() {
            if let Some(&hit) = self.memo_rel.get(&(a, b)) {
                return hit;
            }
        }
        if !self.charge() {
            return false;
        }
        let out = self.rel_eq_uncached(a, b);
        if self.memoisable() {
            self.memo_rel.insert((a, b), out);
        }
        out
    }

    #[allow(
        clippy::match_same_arms,
        reason = "see `formula_eq_uncached`: exhaustive kind pairing, no catch-all"
    )]
    fn rel_eq_uncached(&mut self, a: RelExprId, b: RelExprId) -> bool {
        match (&self.ir.rel_exprs[a].kind, &self.ir.rel_exprs[b].kind) {
            // Free relations compare BY ID, skolems included: a copy that minted
            // its own skolem relation is a different translation, which is the
            // jar's post-skolemization severing (probe j6).
            (RelExprKind::Relation(x), RelExprKind::Relation(y)) => x == y,
            (RelExprKind::Var(x), RelExprKind::Var(y)) => {
                let (x, y) = (*x, *y);
                self.var_eq(x, y)
            }
            (RelExprKind::Const(x), RelExprKind::Const(y)) => x == y,
            (
                RelExprKind::Binary {
                    op: xo,
                    lhs: xl,
                    rhs: xr,
                },
                RelExprKind::Binary {
                    op: yo,
                    lhs: yl,
                    rhs: yr,
                },
            ) => {
                let (xo, xl, xr, yo, yl, yr) = (*xo, *xl, *xr, *yo, *yl, *yr);
                xo == yo && self.rel_eq(xl, yl) && self.rel_eq(xr, yr)
            }
            (RelExprKind::Unary { op: xo, expr: xe }, RelExprKind::Unary { op: yo, expr: ye }) => {
                let (xo, xe, yo, ye) = (*xo, *xe, *yo, *ye);
                xo == yo && self.rel_eq(xe, ye)
            }
            (RelExprKind::Prime(x), RelExprKind::Prime(y)) => {
                let (x, y) = (*x, *y);
                self.rel_eq(x, y)
            }
            (
                RelExprKind::IfThenElse {
                    cond: xc,
                    then_branch: xt,
                    else_branch: xe,
                },
                RelExprKind::IfThenElse {
                    cond: yc,
                    then_branch: yt,
                    else_branch: ye,
                },
            ) => {
                let (xc, xt, xe, yc, yt, ye) = (*xc, *xt, *xe, *yc, *yt, *ye);
                self.formula_eq(xc, yc) && self.rel_eq(xt, yt) && self.rel_eq(xe, ye)
            }
            (
                RelExprKind::Comprehension {
                    decls: xd,
                    body: xb,
                },
                RelExprKind::Comprehension {
                    decls: yd,
                    body: yb,
                },
            ) => {
                let (xd, xb) = (xd.clone(), *xb);
                let (yd, yb) = (yd.clone(), *yb);
                self.comprehension_eq(&xd, xb, &yd, yb)
            }
            (RelExprKind::IntToAtom(x), RelExprKind::IntToAtom(y)) => {
                let (x, y) = (*x, *y);
                self.int_eq(x, y)
            }
            (
                RelExprKind::Relation(_)
                | RelExprKind::Var(_)
                | RelExprKind::Const(_)
                | RelExprKind::Binary { .. }
                | RelExprKind::Unary { .. }
                | RelExprKind::Prime(_)
                | RelExprKind::IfThenElse { .. }
                | RelExprKind::Comprehension { .. }
                | RelExprKind::IntToAtom(_),
                _,
            ) => false,
        }
    }

    /// A comprehension's decls bind left to right and a later bound may mention
    /// an earlier variable, so each bound is compared under the correspondence
    /// the decls before it established.
    fn comprehension_eq(
        &mut self,
        xd: &[CompDecl],
        xb: FormulaId,
        yd: &[CompDecl],
        yb: FormulaId,
    ) -> bool {
        if xd.len() != yd.len() {
            return false;
        }
        let mut pushed = 0usize;
        let mut ok = true;
        for (dx, dy) in xd.iter().zip(yd.iter()) {
            if !self.rel_eq(dx.bound, dy.bound) || !self.push_binder(dx.var, dy.var) {
                ok = false;
                break;
            }
            pushed += 1;
        }
        let out = ok && self.formula_eq(xb, yb);
        for _ in 0..pushed {
            self.pop_binder();
        }
        out
    }

    fn int_eq(&mut self, a: IntExprId, b: IntExprId) -> bool {
        if a == b && self.memoisable() {
            return true;
        }
        if self.memoisable() {
            if let Some(&hit) = self.memo_int.get(&(a, b)) {
                return hit;
            }
        }
        if !self.charge() {
            return false;
        }
        let out = self.int_eq_uncached(a, b);
        if self.memoisable() {
            self.memo_int.insert((a, b), out);
        }
        out
    }

    #[allow(
        clippy::match_same_arms,
        reason = "see `formula_eq_uncached`: exhaustive kind pairing, no catch-all"
    )]
    fn int_eq_uncached(&mut self, a: IntExprId, b: IntExprId) -> bool {
        match (&self.ir.int_exprs[a].kind, &self.ir.int_exprs[b].kind) {
            (IntExprKind::Const(x), IntExprKind::Const(y)) => x == y,
            (IntExprKind::Card(x), IntExprKind::Card(y))
            | (IntExprKind::AtomToInt(x), IntExprKind::AtomToInt(y)) => {
                let (x, y) = (*x, *y);
                self.rel_eq(x, y)
            }
            (IntExprKind::Neg(x), IntExprKind::Neg(y)) => {
                let (x, y) = (*x, *y);
                self.int_eq(x, y)
            }
            (
                IntExprKind::Binary {
                    op: xo,
                    lhs: xl,
                    rhs: xr,
                },
                IntExprKind::Binary {
                    op: yo,
                    lhs: yl,
                    rhs: yr,
                },
            ) => {
                let (xo, xl, xr, yo, yl, yr) = (*xo, *xl, *xr, *yo, *yl, *yr);
                xo == yo && self.int_eq(xl, yl) && self.int_eq(xr, yr)
            }
            (
                IntExprKind::Sum {
                    var: xv,
                    bound: xbnd,
                    body: xbody,
                },
                IntExprKind::Sum {
                    var: yv,
                    bound: ybnd,
                    body: ybody,
                },
            ) => {
                let (xv, xbnd, xbody) = (*xv, *xbnd, *xbody);
                let (yv, ybnd, ybody) = (*yv, *ybnd, *ybody);
                if !self.rel_eq(xbnd, ybnd) || !self.push_binder(xv, yv) {
                    return false;
                }
                let out = self.int_eq(xbody, ybody);
                self.pop_binder();
                out
            }
            (
                IntExprKind::IfThenElse {
                    cond: xc,
                    then_branch: xt,
                    else_branch: xe,
                },
                IntExprKind::IfThenElse {
                    cond: yc,
                    then_branch: yt,
                    else_branch: ye,
                },
            ) => {
                let (xc, xt, xe, yc, yt, ye) = (*xc, *xt, *xe, *yc, *yt, *ye);
                self.formula_eq(xc, yc) && self.int_eq(xt, yt) && self.int_eq(xe, ye)
            }
            (
                IntExprKind::Const(_)
                | IntExprKind::Card(_)
                | IntExprKind::AtomToInt(_)
                | IntExprKind::Neg(_)
                | IntExprKind::Binary { .. }
                | IntExprKind::Sum { .. }
                | IntExprKind::IfThenElse { .. },
                _,
            ) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use als_syntax::{ArenaId, FileId, Span};

    use crate::ir::{Formula, IntCmpOp, IntExpr, Mutability, QuantKind, RelExpr, Relation, Var};

    fn span(lo: u32) -> Span {
        Span::new(FileId::from_index(0), lo, lo + 1)
    }

    /// Builds `#<rel> < 0` at `span(s)`, returning its root.
    fn card_lt_zero(ir: &mut Ir, rel: crate::ir::RelId, s: u32) -> FormulaId {
        let r = ir.rel_exprs.alloc(RelExpr {
            kind: RelExprKind::Relation(rel),
            span: span(s),
        });
        let card = ir.int_exprs.alloc(IntExpr {
            kind: IntExprKind::Card(r),
            span: span(s),
        });
        let zero = ir.int_exprs.alloc(IntExpr {
            kind: IntExprKind::Const(0),
            span: span(s),
        });
        ir.formulas.alloc(Formula {
            kind: FormulaKind::IntCompare {
                op: IntCmpOp::Lt,
                lhs: card,
                rhs: zero,
            },
            span: span(s),
        })
    }

    fn node_rel(ir: &mut Ir) -> crate::ir::RelId {
        ir.relations.alloc(Relation {
            name: "this/Node".to_owned(),
            arity: 1,
            span: span(0),
            mutability: Mutability::Static,
            is_meta_field: false,
        })
    }

    #[test]
    fn identical_copies_at_different_spans_form_a_class() {
        let mut ir = Ir::default();
        let node = node_rel(&mut ir);
        let a = card_lt_zero(&mut ir, node, 10);
        let b = card_lt_zero(&mut ir, node, 40);
        let table = validate(&ir, &[vec![a, b]]);
        assert_eq!(table.get(&a), Some(&TransClassId::from_index(0)));
        assert_eq!(table.get(&b), Some(&TransClassId::from_index(0)));
    }

    #[test]
    fn a_single_member_class_is_dropped() {
        let mut ir = Ir::default();
        let node = node_rel(&mut ir);
        let a = card_lt_zero(&mut ir, node, 10);
        assert!(validate(&ir, &[vec![a]]).is_empty());
    }

    #[test]
    fn distinct_relations_dissolve_the_class() {
        // The skolem-severing shape in miniature: one copy names a relation the
        // other does not, so the two are not one shared node (probe j6).
        let mut ir = Ir::default();
        let node = node_rel(&mut ir);
        let other = ir.relations.alloc(Relation {
            name: "$skolem".to_owned(),
            arity: 1,
            span: span(0),
            mutability: Mutability::Static,
            is_meta_field: false,
        });
        let a = card_lt_zero(&mut ir, node, 10);
        let b = card_lt_zero(&mut ir, other, 40);
        assert!(validate(&ir, &[vec![a, b]]).is_empty());
    }

    #[test]
    fn quantifier_copies_match_up_to_bound_variable_renaming() {
        // `some n: Node | #Node < 0` lowered twice allocates a fresh `VarId` per
        // copy; the jar still shares the node (probe j5), so the copies must
        // compare equal.
        let mut ir = Ir::default();
        let node = node_rel(&mut ir);
        let mut build = |s: u32| {
            let v = ir.vars.alloc(Var {
                name: "n".to_owned(),
                arity: 1,
                span: span(s),
            });
            let bound = ir.rel_exprs.alloc(RelExpr {
                kind: RelExprKind::Relation(node),
                span: span(s),
            });
            let body = card_lt_zero(&mut ir, node, s);
            ir.formulas.alloc(Formula {
                kind: FormulaKind::Quant {
                    kind: QuantKind::Some,
                    var: v,
                    bound,
                    body,
                },
                span: span(s),
            })
        };
        let a = build(10);
        let b = build(40);
        assert_eq!(validate(&ir, &[vec![a, b]]).len(), 2);
    }

    #[test]
    fn a_free_variable_must_be_literally_the_same_variable() {
        // A variable bound OUTSIDE both copies is shared by them, so two copies
        // naming different outer variables are different formulas.
        let mut ir = Ir::default();
        let v1 = ir.vars.alloc(Var {
            name: "x".to_owned(),
            arity: 1,
            span: span(0),
        });
        let v2 = ir.vars.alloc(Var {
            name: "y".to_owned(),
            arity: 1,
            span: span(1),
        });
        let mut build = |v: VarId, s: u32| {
            let r = ir.rel_exprs.alloc(RelExpr {
                kind: RelExprKind::Var(v),
                span: span(s),
            });
            ir.formulas.alloc(Formula {
                kind: FormulaKind::MultTest {
                    test: crate::ir::MultTest::Some,
                    expr: r,
                },
                span: span(s),
            })
        };
        let a = build(v1, 10);
        let b = build(v2, 40);
        let same = build(v1, 70);
        assert!(validate(&ir, &[vec![a, b]]).is_empty());
        assert_eq!(validate(&ir, &[vec![a, same]]).len(), 2);
    }
}
