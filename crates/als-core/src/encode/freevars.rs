//! Static free-variable analysis over the IR (mt-049).
//!
//! For each [`crate::ir`] node this precomputes the set of quantifier /
//! comprehension / `sum` variables that occur **free** in it — i.e. are bound
//! somewhere *outside* the node rather than within it. The grounding memoisation
//! in [`super::Encoder`] keys a node's cache on `(node id, the values of exactly
//! its free variables)`: a sub-expression that does not mention the innermost
//! bound variable then shares one encoded result across every binding of that
//! variable, instead of being re-encoded per binding.
//!
//! The result is a pure function of the IR (no environment, no hashing — the
//! per-node sets are ordered [`BTreeSet`]s), so it is deterministic (STYLE D1)
//! and computed once at [`super::Encoder`] construction.

use std::collections::BTreeSet;

use als_syntax::ArenaId;

use crate::ir::{
    FormulaId, FormulaKind, IntExprId, IntExprKind, Ir, RelExprId, RelExprKind, VarId,
};

/// Precomputed free-variable sets, indexed by node arena position.
///
/// Sets are `BTreeSet<VarId>` (ordered — deterministic iteration). The analysis
/// is total over the IR, including nodes the encoder later defers (temporal /
/// arithmetic): computing their free vars is harmless and keeps the walk simple.
pub(crate) struct FreeVars {
    formulas: Vec<BTreeSet<VarId>>,
    rel_exprs: Vec<BTreeSet<VarId>>,
    int_exprs: Vec<BTreeSet<VarId>>,
}

impl FreeVars {
    /// Computes the free-variable set of every node in `ir`.
    pub(crate) fn build(ir: &Ir) -> Self {
        let mut b = Builder {
            ir,
            formulas: vec![None; ir.formulas.len()],
            rel_exprs: vec![None; ir.rel_exprs.len()],
            int_exprs: vec![None; ir.int_exprs.len()],
        };
        // Fill every slot (memoised recursion handles DAG sharing; visiting all
        // ids guarantees totality regardless of cross-arena reference order).
        for (id, _) in ir.formulas.iter() {
            b.formula(id);
        }
        for (id, _) in ir.rel_exprs.iter() {
            b.rel(id);
        }
        for (id, _) in ir.int_exprs.iter() {
            b.int(id);
        }
        FreeVars {
            formulas: b
                .formulas
                .into_iter()
                .map(Option::unwrap_or_default)
                .collect(),
            rel_exprs: b
                .rel_exprs
                .into_iter()
                .map(Option::unwrap_or_default)
                .collect(),
            int_exprs: b
                .int_exprs
                .into_iter()
                .map(Option::unwrap_or_default)
                .collect(),
        }
    }

    /// Free variables of a formula node.
    pub(crate) fn formula(&self, id: FormulaId) -> &BTreeSet<VarId> {
        &self.formulas[id.index()]
    }

    /// Free variables of a relation-expression node.
    pub(crate) fn rel(&self, id: RelExprId) -> &BTreeSet<VarId> {
        &self.rel_exprs[id.index()]
    }

    /// Free variables of an integer-expression node.
    pub(crate) fn int(&self, id: IntExprId) -> &BTreeSet<VarId> {
        &self.int_exprs[id.index()]
    }
}

/// Memoising builder: each `Option` slot is `Some` once its node is computed.
///
/// `ir` is a shared `&Ir`, so reading through it (`self.ir.…`) does not borrow
/// `self` — the recursive `&mut self` calls below are free of borrow conflict.
struct Builder<'a> {
    ir: &'a Ir,
    formulas: Vec<Option<BTreeSet<VarId>>>,
    rel_exprs: Vec<Option<BTreeSet<VarId>>>,
    int_exprs: Vec<Option<BTreeSet<VarId>>>,
}

impl Builder<'_> {
    fn formula(&mut self, id: FormulaId) -> BTreeSet<VarId> {
        if let Some(s) = &self.formulas[id.index()] {
            return s.clone();
        }
        let mut set = BTreeSet::new();
        match &self.ir.formulas[id].kind {
            FormulaKind::Const(_) => {}
            FormulaKind::Not(f) => set = self.formula(*f),
            FormulaKind::And(parts) | FormulaKind::Or(parts) => {
                for &p in parts {
                    set.extend(self.formula(p));
                }
            }
            FormulaKind::Implies {
                antecedent,
                consequent,
            } => {
                set.extend(self.formula(*antecedent));
                set.extend(self.formula(*consequent));
            }
            FormulaKind::Iff(l, r) => {
                set.extend(self.formula(*l));
                set.extend(self.formula(*r));
            }
            FormulaKind::RelCompare { lhs, rhs, .. } => {
                set.extend(self.rel(*lhs));
                set.extend(self.rel(*rhs));
            }
            FormulaKind::IntCompare { lhs, rhs, .. } => {
                set.extend(self.int(*lhs));
                set.extend(self.int(*rhs));
            }
            FormulaKind::MultTest { expr, .. } => set = self.rel(*expr),
            FormulaKind::Quant {
                var, bound, body, ..
            } => {
                let (var, bound, body) = (*var, *bound, *body);
                set.extend(self.rel(bound));
                let mut body = self.formula(body);
                body.remove(&var);
                set.extend(body);
            }
            FormulaKind::TemporalUnary { body, .. } => set = self.formula(*body),
            FormulaKind::TemporalBinary { lhs, rhs, .. } => {
                set.extend(self.formula(*lhs));
                set.extend(self.formula(*rhs));
            }
        }
        self.formulas[id.index()] = Some(set.clone());
        set
    }

    fn rel(&mut self, id: RelExprId) -> BTreeSet<VarId> {
        if let Some(s) = &self.rel_exprs[id.index()] {
            return s.clone();
        }
        let mut set = BTreeSet::new();
        match &self.ir.rel_exprs[id].kind {
            RelExprKind::Relation(_) | RelExprKind::Const(_) => {}
            RelExprKind::Var(v) => {
                set.insert(*v);
            }
            RelExprKind::Binary { lhs, rhs, .. } => {
                set.extend(self.rel(*lhs));
                set.extend(self.rel(*rhs));
            }
            RelExprKind::Unary { expr, .. } | RelExprKind::Prime(expr) => set = self.rel(*expr),
            RelExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                set.extend(self.formula(*cond));
                set.extend(self.rel(*then_branch));
                set.extend(self.rel(*else_branch));
            }
            RelExprKind::Comprehension { decls, body } => {
                // A later decl's bound may reference an earlier decl's variable,
                // so gather all bound + body free vars, then strip every bound
                // variable (all are bound inside the comprehension).
                let body = *body;
                let vars: Vec<VarId> = decls.iter().map(|d| d.var).collect();
                let bounds: Vec<RelExprId> = decls.iter().map(|d| d.bound).collect();
                for b in bounds {
                    set.extend(self.rel(b));
                }
                set.extend(self.formula(body));
                for v in vars {
                    set.remove(&v);
                }
            }
            RelExprKind::IntToAtom(ie) => set = self.int(*ie),
        }
        self.rel_exprs[id.index()] = Some(set.clone());
        set
    }

    fn int(&mut self, id: IntExprId) -> BTreeSet<VarId> {
        if let Some(s) = &self.int_exprs[id.index()] {
            return s.clone();
        }
        let mut set = BTreeSet::new();
        match &self.ir.int_exprs[id].kind {
            IntExprKind::Const(_) => {}
            IntExprKind::Card(rel) | IntExprKind::AtomToInt(rel) => set = self.rel(*rel),
            IntExprKind::Neg(ie) => set = self.int(*ie),
            IntExprKind::Binary { lhs, rhs, .. } => {
                set.extend(self.int(*lhs));
                set.extend(self.int(*rhs));
            }
            IntExprKind::Sum { var, bound, body } => {
                let (var, bound, body) = (*var, *bound, *body);
                set.extend(self.rel(bound));
                let mut body = self.int(body);
                body.remove(&var);
                set.extend(body);
            }
            IntExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                set.extend(self.formula(*cond));
                set.extend(self.int(*then_branch));
                set.extend(self.int(*else_branch));
            }
        }
        self.int_exprs[id.index()] = Some(set.clone());
        set
    }
}
