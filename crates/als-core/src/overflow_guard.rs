//! The forbid-mode overflow-guard classifier (translation-ref §10.7c) — shared
//! by the encoder ([`crate::encode`]) and the evaluator ([`crate::eval`]) so the
//! two implementations apply an identical guard and defer identically.
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
//! One jar corner remains genuinely unpinned and is typed-deferred:
//!
//! - **The ITE/`implies` sliver** (§10.7c rule 4): a non-bare-`Int` universal
//!   overflow-driver reached through an int-ITE branch or an `implies` antecedent,
//!   where the jar's behaviour is Open (P9/P12). Deferred, not guessed.

use std::collections::BTreeSet;

use crate::ir::{IntExprId, IntExprKind, Ir, RelExprId, RelExprKind, VarId};

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

/// The guard decision for one overflowing operand at a comparison.
pub(crate) enum GuardDecision {
    /// The jar-unpinned ITE/`implies` sliver (§10.7c rule 4): typed defer.
    Defer,
    /// Apply the polarity guard; `forall_dep` = the operand classifies as
    /// depending on an effective-∀ (rescue) rather than existential (exclude).
    Guard { forall_dep: bool },
}

/// Whether an integer expression can overflow — it syntactically contains
/// arithmetic, `sum`, or cardinality (not `Const`, not `int[·]`; translation-ref
/// §10.7c). Drives both the guard and the defer.
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

/// Whether a **relational** equality/subset must typed-defer in forbid mode
/// because of the unpinned integer-equality typing rule (translation-ref §10.7c
/// `GAP1a`). The jar compares two `Int`-typed operands as integers — firing the
/// overflow guard — but mettle only reliably detects an integer comparison when
/// *both* sides are `Int[·]` casts (the pinned `div[5,0]=div[5,0]` cell) or a
/// literal/cardinality; an arithmetic result compared to a plain `Int`-typed
/// var/field (`plus[m,7] = n`) currently lowers to *relational* equality, whose
/// wrapped-value semantics silently skip the guard. Rather than answer
/// allow-style on this jar-pinned shape (a wrong verdict), we defer.
///
/// Fires only in forbid mode, only when **exactly one** side is an `Int[·]` cast
/// of an [`overflow_capable`] int expression and the other side is a plain
/// relational expression (not a cast). Allow mode stays on the relational path
/// (wrapped-value equality is exact there); non-capable casts (`Int[3]`,
/// `Int[int[e]]`) stay relational in both modes (no guard could fire).
pub(crate) fn eq_typing_defer(
    ir: &Ir,
    lhs: RelExprId,
    rhs: RelExprId,
    allow_overflow: bool,
) -> bool {
    if allow_overflow {
        return false;
    }
    let cast_capable = |id: RelExprId| matches!(&ir.rel_exprs[id].kind, RelExprKind::IntToAtom(ie) if overflow_capable(ir, *ie));
    let is_cast = |id: RelExprId| matches!(ir.rel_exprs[id].kind, RelExprKind::IntToAtom(_));
    (cast_capable(lhs) && !is_cast(rhs)) || (cast_capable(rhs) && !is_cast(lhs))
}

/// Whether an integer expression's subtree contains an int-ITE node — the
/// syntactic half of the rule-6 "reachable through an int-ITE branch" defer.
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
/// operational rule list). `frames` is the enclosing-quantifier stack
/// (innermost last); `free` is the operand's free-variable set; `capable` is
/// [`overflow_capable`] of the operand; `behind_conditional` is true when the
/// comparison is reached through an `implies` antecedent or the operand contains
/// an int-ITE (the rule-6 precondition).
pub(crate) fn classify(
    frames: &[QuantFrame],
    free: &BTreeSet<VarId>,
    capable: bool,
    behind_conditional: bool,
) -> GuardDecision {
    let mentions = |v: VarId| free.contains(&v);
    // The single per-variable rule (§10.7c rules 0–3): classify by the innermost
    // enclosing binder whose domain is bare `Int`/`seq/Int` and whose variable the
    // operand depends on — a bare-`Int` ∀ rescues, a bare-`Int` ∃ excludes. No
    // bare-`Int` binder ⇒ Defect A defaults the classification to **existential**
    // (exclude), regardless of nesting shape/depth/type.
    let driver = frames.iter().rev().find(|f| f.bare_int && mentions(f.var));

    // Rule 4 (the sole open sub-corner): when the classifier would default to
    // existential *because* the operand's overflow-driving ∀ has a non-bare-`Int`
    // domain (Defect A's precondition), and the comparison is reached through an
    // int-ITE branch or an `implies` antecedent, the jar's behaviour is Open —
    // typed defer. Only when no bare-`Int` binder classifies the operand first.
    if capable
        && behind_conditional
        && driver.is_none()
        && frames
            .iter()
            .any(|f| !f.bare_int && f.effective_forall && mentions(f.var))
    {
        return GuardDecision::Defer;
    }

    let forall_dep = driver.is_some_and(|f| f.effective_forall);
    GuardDecision::Guard { forall_dep }
}
