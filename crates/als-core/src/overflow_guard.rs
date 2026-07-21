//! The forbid-mode overflow-guard classifier (translation-ref §10.7c) — shared
//! by the encoder ([`crate::encode`]) and the evaluator ([`crate::eval`]) so the
//! two implementations apply an identical guard.
//!
//! The jar's `DefCond.isUnivQuant` walk recognizes a quantifier binder as
//! **universal** for the Milicevic/Jackson rescue only when its domain is
//! *literally* the bare `Int`/`seq/Int` builtin; a `sig` or comprehension domain
//! fails the same `isInt()` string check and defaults to **existential**
//! (over-excludes instead of rescues — the common `all p: Sig | <overflow over p>`
//! shape, §10.7c rule 0/GAP2a). This is a purely **per-variable** rule: a
//! variable classifies by ITS OWN binder domain only, with **no dependence on
//! nesting shape, depth, or type** ("Defect B" — a supposed nesting-position
//! defect — was **retracted** in §10.7c/§10.7d round 3: its decisive probes were
//! all confounded by `negate[8]` silently emptying conjunction-shaped domains).
//!
//! ## The one-sided `Int[·]`-cast shape at `=`/`in`/mult-tests (§10.7c ext, mt-051)
//! A relational comparison (`RelCompare`) or multiplicity test (`MultTest`) whose
//! set-operator structure contains an overflow-capable `Int[·]` cast is governed
//! by two jar-pinned effects (probe labels in `scratchpad/probe/mt051_report.md`):
//!
//! - **(A) cast value semantics** — the jar builds every `IntToExprCast` cell with
//!   `Int.eq(other, Environment.empty())` (`∧ ¬accumOverflow`), so in forbid mode
//!   an overflowed cast denotes the **empty** set, polarity-independent, in every
//!   context. This lives at the `IntToAtom` node in both back ends.
//! - **(B) comparison-level guard** — `BooleanMatrix.eq/subset/some` additionally
//!   thread `DefCond.ensureDef`, i.e. the same rules 0–3 classification below is
//!   applied to each capable cast reachable through the compared sides' set
//!   structure ([`collect_capable_casts`]), **unless** the cast's overflow flag is
//!   translation-constant ([`translation_constant`]) — a constant-empty matrix
//!   sheds its `DefCond` in the jar's matrix fast paths, so (B) is lost while (A)
//!   still fires (the R-cardun/T5/T6 constant-escape trio).
//!
//! ## Rule 4 (the int-ITE / `implies`-antecedent sliver) — now pinned (mt-051)
//! A non-bare-`Int` effective-∀ overflow-driver reached through an int-ITE branch
//! or an `implies` **antecedent** behaves as **correctly classified** (rescue at
//! positive polarity; the usual swap at negative) — probe Part C, boundary fixed
//! by V-not (a bare `!` is **not** an escape). Consequents and bare negation get
//! ordinary Defect-A treatment.

use std::collections::BTreeSet;

use crate::bounds::Bounds;
use crate::ir::{
    CompDecl, FormulaKind, IntExprId, IntExprKind, Ir, RelConst, RelExprId, RelExprKind, VarId,
};

/// The shift-amount mask width `⌈log2 w⌉` = `32 − leading_zeros(w−1)` (Kodkod
/// `TwosComplementInt`, translation-ref §10.7d): only the low `mask` bits of a
/// shift amount are consulted for the value. Shared by the encoder circuit and
/// the evaluator so both mask identically.
pub(crate) fn shift_mask_width(w: usize) -> usize {
    if w <= 1 {
        0
    } else {
        (usize::BITS - (w - 1).leading_zeros()) as usize
    }
}

/// One enclosing quantifier binder on the path to a comparison (innermost last).
#[derive(Clone, Copy, Debug)]
pub(crate) struct QuantFrame {
    /// The bound variable.
    pub var: VarId,
    /// Whether the quantifier's domain is literally the `Int`/`seq/Int` builtin
    /// (the only domain the jar's classifier recognizes as universal).
    pub bare_int: bool,
    /// The binder's **effective** kind after polarity normalization.
    pub effective_forall: bool,
}

/// Whether an integer expression can overflow — it syntactically contains
/// arithmetic, `sum`, or cardinality (not `Const`, not `int[·]`; translation-ref
/// §10.7c). Drives both the value semantics and the comparison-level guard.
pub(crate) fn overflow_capable(ir: &Ir, id: IntExprId) -> bool {
    match &ir.int_exprs[id].kind {
        IntExprKind::Const(_) | IntExprKind::AtomToInt(_) => false,
        IntExprKind::Card(_)
        | IntExprKind::Neg(_)
        | IntExprKind::Binary { .. }
        | IntExprKind::Sum { .. } => true,
        IntExprKind::IfThenElse {
            then_branch,
            else_branch,
            ..
        } => overflow_capable(ir, *then_branch) || overflow_capable(ir, *else_branch),
    }
}

/// Collects every **overflow-capable** `Int[·]` cast reachable through the
/// SET-OPERATOR structure of a relational expression (translation-ref §10.7c
/// ext (B), mt-051): recurse through relational `Binary` (union/intersect/diff/
/// join/product/override), `Unary`, and `IfThenElse` branches — but **not** into
/// `Formula` positions (an ITE condition, a comprehension body: those guard at
/// their own comparison sites) nor into the int expr beneath a cast (a
/// nested-inside-`Card` cast is a documented out-of-scope corner). Pushed in
/// traversal order so the caller's lhs-then-rhs walk is deterministic (STYLE D2).
pub(crate) fn collect_capable_casts(ir: &Ir, id: RelExprId, out: &mut Vec<IntExprId>) {
    match &ir.rel_exprs[id].kind {
        RelExprKind::IntToAtom(ie) => {
            if overflow_capable(ir, *ie) {
                out.push(*ie);
            }
        }
        RelExprKind::Binary { lhs, rhs, .. } => {
            collect_capable_casts(ir, *lhs, out);
            collect_capable_casts(ir, *rhs, out);
        }
        RelExprKind::Unary { expr, .. } => collect_capable_casts(ir, *expr, out),
        RelExprKind::IfThenElse {
            then_branch,
            else_branch,
            ..
        } => {
            collect_capable_casts(ir, *then_branch, out);
            collect_capable_casts(ir, *else_branch, out);
        }
        // Leaves and Formula-bearing nodes stop the set-structure walk.
        RelExprKind::Relation(_)
        | RelExprKind::Var(_)
        | RelExprKind::Const(_)
        | RelExprKind::Comprehension { .. }
        | RelExprKind::Prime(_) => {}
    }
}

/// Whether a cast operand's overflow flag is **translation-constant** (§10.7c ext
/// (C), mt-051): its int-expr subtree contains no `Var` reference and no `Sum`
/// node, and every relation it references (through `Card`/`int[·]`, etc.) is
/// **exactly** bound (`lower == upper`). Such a cast contributes NO
/// comparison-level (B) guard — the jar's constant-empty matrices shed their
/// `DefCond` — while its (A) value semantics still applies (R-cardun/T5/T6). The
/// SAME predicate runs in the encoder and the evaluator, so the two can never
/// drift (do NOT substitute `Bool::Const`-ness on the encoder side).
pub(crate) fn translation_constant(ir: &Ir, bounds: &Bounds, id: IntExprId) -> bool {
    match &ir.int_exprs[id].kind {
        IntExprKind::Const(_) => true,
        IntExprKind::Card(rel) | IntExprKind::AtomToInt(rel) => rel_const(ir, bounds, *rel),
        IntExprKind::Neg(ie) => translation_constant(ir, bounds, *ie),
        IntExprKind::Binary { lhs, rhs, .. } => {
            translation_constant(ir, bounds, *lhs) && translation_constant(ir, bounds, *rhs)
        }
        // A `Sum` binder makes the operand non-constant regardless of its body.
        IntExprKind::Sum { .. } => false,
        IntExprKind::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => {
            formula_const(ir, bounds, *cond)
                && translation_constant(ir, bounds, *then_branch)
                && translation_constant(ir, bounds, *else_branch)
        }
    }
}

/// [`translation_constant`] over a relation expression: no `Var`, and every
/// referenced free relation is exactly bound.
fn rel_const(ir: &Ir, bounds: &Bounds, id: RelExprId) -> bool {
    match &ir.rel_exprs[id].kind {
        RelExprKind::Relation(r) => bounds.get(*r).is_some_and(|b| b.lower() == b.upper()),
        // A quantifier/comprehension variable is never a translation constant.
        RelExprKind::Var(_) => false,
        // `none`/`univ`/`iden` are fixed functions of the universe.
        RelExprKind::Const(RelConst::None | RelConst::Univ | RelConst::Iden) => true,
        RelExprKind::Binary { lhs, rhs, .. } => {
            rel_const(ir, bounds, *lhs) && rel_const(ir, bounds, *rhs)
        }
        RelExprKind::Unary { expr, .. } | RelExprKind::Prime(expr) => rel_const(ir, bounds, *expr),
        RelExprKind::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => {
            formula_const(ir, bounds, *cond)
                && rel_const(ir, bounds, *then_branch)
                && rel_const(ir, bounds, *else_branch)
        }
        RelExprKind::Comprehension { decls, body } => {
            decls
                .iter()
                .all(|d: &CompDecl| rel_const(ir, bounds, d.bound))
                && formula_const(ir, bounds, *body)
        }
        RelExprKind::IntToAtom(ie) => translation_constant(ir, bounds, *ie),
    }
}

/// [`translation_constant`] over a formula (reached only through an ITE
/// condition or a comprehension body): no `Var`/`Sum`, exact relations only.
fn formula_const(ir: &Ir, bounds: &Bounds, id: crate::ir::FormulaId) -> bool {
    match &ir.formulas[id].kind {
        FormulaKind::Const(_) => true,
        FormulaKind::Not(f) => formula_const(ir, bounds, *f),
        FormulaKind::And(parts) | FormulaKind::Or(parts) => {
            parts.iter().all(|&p| formula_const(ir, bounds, p))
        }
        FormulaKind::Implies {
            antecedent,
            consequent,
        } => formula_const(ir, bounds, *antecedent) && formula_const(ir, bounds, *consequent),
        FormulaKind::Iff(l, r) => formula_const(ir, bounds, *l) && formula_const(ir, bounds, *r),
        FormulaKind::RelCompare { lhs, rhs, .. } => {
            rel_const(ir, bounds, *lhs) && rel_const(ir, bounds, *rhs)
        }
        FormulaKind::IntCompare { lhs, rhs, .. } => {
            translation_constant(ir, bounds, *lhs) && translation_constant(ir, bounds, *rhs)
        }
        FormulaKind::MultTest { expr, .. } => rel_const(ir, bounds, *expr),
        // A quantifier binds a variable — its body is not a translation constant.
        FormulaKind::Quant { .. } => false,
        FormulaKind::TemporalUnary { body, .. } => formula_const(ir, bounds, *body),
        FormulaKind::TemporalBinary { lhs, rhs, .. } => {
            formula_const(ir, bounds, *lhs) && formula_const(ir, bounds, *rhs)
        }
    }
}

/// Whether an integer expression's subtree contains an int-ITE node — the
/// syntactic half of the rule-4 "reachable through an int-ITE branch" escape.
pub(crate) fn contains_int_ite(ir: &Ir, id: IntExprId) -> bool {
    match &ir.int_exprs[id].kind {
        IntExprKind::Const(_) | IntExprKind::Card(_) | IntExprKind::AtomToInt(_) => false,
        IntExprKind::Neg(ie) => contains_int_ite(ir, *ie),
        IntExprKind::Binary { lhs, rhs, .. } => {
            contains_int_ite(ir, *lhs) || contains_int_ite(ir, *rhs)
        }
        IntExprKind::Sum { body, .. } => contains_int_ite(ir, *body),
        IntExprKind::IfThenElse { .. } => true,
    }
}

/// Classifies one overflowing operand at a comparison (translation-ref §10.7c's
/// operational rule list), returning `forall_dep` = whether it classifies as
/// depending on an effective-∀ (a **rescue**) rather than an existential (an
/// **exclude**). `frames` is the enclosing-quantifier stack (innermost last);
/// `free` is the operand's free-variable set; `capable` is [`overflow_capable`]
/// of the operand; `behind_conditional` is true when the comparison is reached
/// through an `implies` antecedent or the operand contains an int-ITE.
pub(crate) fn classify(
    frames: &[QuantFrame],
    free: &BTreeSet<VarId>,
    capable: bool,
    behind_conditional: bool,
) -> bool {
    let mentions = |v: VarId| free.contains(&v);
    // The single per-variable rule (§10.7c rules 0–3): classify by the innermost
    // enclosing binder whose domain is bare `Int`/`seq/Int` and whose variable the
    // operand depends on — a bare-`Int` ∀ rescues, a bare-`Int` ∃ excludes. No
    // bare-`Int` binder ⇒ Defect A defaults the classification to **existential**
    // (exclude), regardless of nesting shape/depth/type.
    let driver = frames.iter().rev().find(|f| f.bare_int && mentions(f.var));

    // Rule 4 (§10.7c, pinned mt-051): when the classifier would default to
    // existential *because* the operand's overflow-driving ∀ has a non-bare-`Int`
    // domain (Defect A's precondition), and the comparison is reached through an
    // int-ITE branch or an `implies` antecedent, the driver behaves as CORRECTLY
    // classified — i.e. universal ⇒ rescue. Only when no bare-`Int` binder
    // classifies the operand first (a bare `!` is NOT an escape — probe V-not).
    if capable
        && behind_conditional
        && driver.is_none()
        && frames
            .iter()
            .any(|f| !f.bare_int && f.effective_forall && mentions(f.var))
    {
        return true;
    }

    driver.is_some_and(|f| f.effective_forall)
}
