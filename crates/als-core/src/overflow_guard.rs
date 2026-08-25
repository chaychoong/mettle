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
//!   applied to each capable cast that SURVIVES the jar's matrix folding on the
//!   way up to the reader ([`collect_capable_casts`]).
//!
//! ## Which casts survive: the overflow-guard shedding rule (§10.7e–§10.7k, mt-129/130)
//! mt-096 pinned this corner as "sparse-matrix folding, not an inspectable rule";
//! mt-129 **refuted** that from the Kodkod source at the pinned oracle build and
//! measured the resulting rule on 137 cells (`scratchpad/probe/mt129/NOTES.md`),
//! 137/137. The rule mettle now implements:
//!
//! - **(R-a) Constant emptiness.** An `Int[e]` cast whose overflow circuit folds
//!   to the *constant* `TRUE` — every integer leaf under `e` constant **after
//!   quantifier ground substitution**, and the arithmetic overflows or divides by
//!   zero — is a matrix with **zero cells** that still carries a live overflow
//!   circuit (`FOL2BoolTranslator.visit(IntToExprCast)` + `BooleanMatrix.set`
//!   dropping `FALSE` cells + `setDefCond`). [`Fold::emptiness`] decides this
//!   from the IR, the bounds and the active bindings — never from a runtime
//!   value, which is what keeps the encoder and the evaluator a matched pair
//!   (mt-129 cell k9: a relation with variable cells is translation-time
//!   NON-empty even in instances that empty it).
//! - **(R-b) Operators.** `BooleanMatrix.or` tests `this.cells.isEmpty()` **before**
//!   merging, so a binary, left-associative UNION drops the overflow circuit of a
//!   cells-empty operand, testing the LEFT one first; `override` runs the same
//!   test on its RIGHT operand only. Every other former — intersection,
//!   difference, join, product, transpose, closure, if-then-else — merges
//!   unconditionally.
//! - **(R-c) Readers.** `lone`/`one` over a cells-empty matrix and `some` over a
//!   matrix with a constant-TRUE cell answer before `ensureDef` and shed the
//!   guard ([`collect_mult_test_casts`]); `no`, `in`, `=` never shed. `#` merges
//!   the matrix circuit (`BooleanMatrix.cardinality`), while the `sum` reader
//!   never consults it at all — which is why `AtomToInt` carries no merge.
//!
//! There is deliberately **no** unconditional constant escape at the comparison
//! site any more. mt-129 measured that mettle's old one was wrong in the
//! **UNSAT→SAT** direction on a fully ground cast (`run { plus[7,7] in Int }` for
//! `3 but 4 int` is jar UNSAT); the jar sheds a constant-empty matrix's `DefCond`
//! only where a union/override fast path or a `lone`/`one`/`some` short-circuit
//! throws it away. The R-cardun/T5/T6 trio still passes because those sheds come
//! from the union fast path, which (R-b) reproduces exactly.
//!
//! ## Rule 4 (the int-ITE / `implies`-antecedent sliver) — RETRACTED (mt-090)
//! §10.7f. There is no escape. The jar's `Environment.negate()` fires only in
//! `FOL2BoolTranslator.visit(NotFormula)`, so an `implies` **antecedent** keeps
//! the implication's own polarity, and `DefCond.isUnivQuant` never consults the
//! surrounding operator at all. mt-051's supporting cells were confounded twice
//! over: the antecedent cells cancelled a wrong polarity against a wrong
//! classification, and the "int-ITE" cells were relational ITEs over `Int[·]`
//! casts (`plus[..]` is a `fun` returning the SET `Int`), i.e. FACT-2/FACT-4
//! machinery, not a classification escape. Probes f0/f3/f4 — genuine int-ITEs
//! over `#·` branches — refute the escape directly.

use std::collections::{BTreeMap, BTreeSet};

use crate::bounds::{AtomId, Bounds, Tuple};
use crate::ir::{
    FormulaId, FormulaKind, IntBinOp, IntCmpOp, IntExprId, IntExprKind, Ir, MultTest, RelBinOp,
    RelConst, RelExprId, RelExprKind, RelUnOp, VarId,
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

/// Whether an integer literal is outside the bitwidth's two's-complement range,
/// i.e. whether Kodkod's `IntConstant` for it carries a **constantly-TRUE**
/// overflow flag (translation-ref §10.7k, mt-101). `8` at bitwidth 4 wraps
/// silently to the Int atom `-8` on the value layer, but the flag it raises is
/// what `DefCond.ensureDef` then folds into the enclosing comparison.
pub(crate) fn const_overflows(value: i32, bitwidth: u32) -> bool {
    value < crate::lower::int_min(bitwidth) || value > crate::lower::int_max(bitwidth)
}

/// Whether an integer expression can overflow — it syntactically contains
/// arithmetic, `sum`, or cardinality, **or is a literal outside the bitwidth's
/// range** (not an in-range `Const`, not `int[·]`; translation-ref §10.7c,
/// §10.7k). Drives both the value semantics and the comparison-level guard.
pub(crate) fn overflow_capable(ir: &Ir, bitwidth: u32, id: IntExprId) -> bool {
    match &ir.int_exprs[id].kind {
        IntExprKind::Const(v) => const_overflows(*v, bitwidth),
        IntExprKind::AtomToInt(_) => false,
        IntExprKind::Card(_)
        | IntExprKind::Neg(_)
        | IntExprKind::Binary { .. }
        | IntExprKind::Sum { .. } => true,
        IntExprKind::IfThenElse {
            then_branch,
            else_branch,
            ..
        } => {
            overflow_capable(ir, bitwidth, *then_branch)
                || overflow_capable(ir, bitwidth, *else_branch)
        }
    }
}

// ---------------------------------------------------------------- arithmetic
//
// The concrete two's-complement arithmetic below is the SINGLE source of truth
// for mettle's non-circuit integer semantics: the evaluator delegates to it, and
// so does [`Fold`], the translation-time constant folder that decides (R-a). One
// copy means the evaluator, the encoder's constant folding and the shed decision
// cannot drift apart (translation-ref §11.2, jar-verified §10.7b/§10.7d).

/// Two's-complement wrap of `value` to `bitwidth`, interpreted signed.
pub(crate) fn wrap_signed(value: i64, bitwidth: u32) -> i64 {
    if bitwidth == 0 {
        return 0;
    }
    let modulus = 1i64 << bitwidth;
    let masked = value.rem_euclid(modulus);
    if masked >= (1i64 << (bitwidth - 1)) {
        masked - modulus
    } else {
        masked
    }
}

/// One binary integer op over concrete operands, returning `(value, overflow)`
/// with exactly the encoder circuits' semantics (`div`/`rem` reproduce the jar's
/// edge values, §10.7b; shifts mask their amount, §10.7d).
pub(crate) fn int_binop_value(op: IntBinOp, a: i64, b: i64, bitwidth: u32) -> (i64, bool) {
    let (min, max) = (
        i64::from(crate::lower::int_min(bitwidth)),
        i64::from(crate::lower::int_max(bitwidth)),
    );
    let out_of_range = |x: i64| x < min || x > max;
    match op {
        IntBinOp::Add => (wrap_signed(a + b, bitwidth), out_of_range(a + b)),
        IntBinOp::Sub => (wrap_signed(a - b, bitwidth), out_of_range(a - b)),
        IntBinOp::Mul => (wrap_signed(a * b, bitwidth), out_of_range(a * b)),
        IntBinOp::Div => {
            if b == 0 {
                let v = match a.cmp(&0) {
                    std::cmp::Ordering::Less => 1,
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Greater => -1,
                };
                (v, true)
            } else {
                (wrap_signed(a / b, bitwidth), a == min && b == -1)
            }
        }
        IntBinOp::Rem => {
            if b == 0 {
                (a, true)
            } else {
                (wrap_signed(a % b, bitwidth), false)
            }
        }
        IntBinOp::Shl => shl_value(a, b, bitwidth),
        IntBinOp::Sha => (shift_right_value(a, b, bitwidth, true), false),
        IntBinOp::Shr => (shift_right_value(a, b, bitwidth, false), false),
    }
}

/// Logical left shift with its **own** overflow flag, matching the encoder's
/// `shl` bit-for-bit (translation-ref §10.7d): only the low `⌈log2 w⌉` amount
/// bits shift the value, but the overflow loop runs over all `w` amount bits, so
/// a masked-away junk bit can spuriously flag overflow when the (frozen) shifted
/// value has a bit transition in the inspected region.
#[allow(
    clippy::many_single_char_names,
    clippy::cast_sign_loss,
    clippy::cast_possible_wrap,
    reason = "concrete replica of the shl bit circuit; every cast is a bounded w-bit \
              pattern (`rem_euclid` is non-negative and < 2^w)"
)]
fn shl_value(a: i64, b: i64, bitwidth: u32) -> (i64, bool) {
    let w = bitwidth as usize;
    let mask = shift_mask_width(w);
    let modw = 1i64 << bitwidth;
    let bpat = b.rem_euclid(modw) as u64; // amount's w-bit pattern
    let mut s = (a.rem_euclid(modw) as u64) & (modw as u64 - 1); // running value bits
    let bit = |v: u64, i: usize| (v >> i) & 1 == 1;
    let mut overflow = false;
    for i in 0..w {
        let k = if i < 63 { 1usize << i } else { w };
        let lo = (w - 1).saturating_sub(k);
        // Any adjacent bit transition in [lo, w-1] of the current state.
        let mut region_changes = false;
        for j in lo..(w - 1) {
            region_changes |= bit(s, j) != bit(s, j + 1);
        }
        overflow |= bit(bpat, i) && region_changes;
        if i < mask && bit(bpat, i) {
            s = (s << k) & (modw as u64 - 1);
        }
    }
    (wrap_signed(s as i64, bitwidth), overflow)
}

/// Right shift by the low `⌈log2 w⌉` amount bits (translation-ref §10.7d): a
/// masked amount ≥ w fills fully with `fill` (sign for `>>`, zero for `>>>`).
/// Own overflow is always false (operand overflow propagates separately).
#[allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_wrap,
    clippy::cast_possible_truncation,
    reason = "bounded w-bit pattern arithmetic; `rem_euclid` is non-negative and < 2^w, \
              and the mask width fits usize"
)]
fn shift_right_value(a: i64, b: i64, bitwidth: u32, arith: bool) -> i64 {
    let w = bitwidth as usize;
    let mask = shift_mask_width(w);
    let modw = 1i64 << bitwidth;
    let bpat = b.rem_euclid(modw) as u64;
    // Effective shift = the low `mask` bits of the amount.
    let amt = (bpat & ((1u64 << mask) - 1)) as usize;
    if amt >= w {
        return if arith && a < 0 { -1 } else { 0 };
    }
    if arith {
        // Arithmetic shift on the signed value is sign-extending.
        a >> amt
    } else {
        // Logical shift on the non-negative w-bit pattern.
        wrap_signed(((a.rem_euclid(modw) as u64) >> amt) as i64, bitwidth)
    }
}

/// The integer value of an `Int` atom, `None` for a non-`Int` atom. `int_start`
/// is the universe index of the first `Int` atom, `int_end` one past the last —
/// both back ends derive them identically from the scope.
pub(crate) fn atom_int_value(
    atom: AtomId,
    int_start: usize,
    int_end: usize,
    bitwidth: u32,
) -> Option<i64> {
    use als_syntax::ArenaId;
    let idx = atom.index();
    if idx < int_start || idx >= int_end || bitwidth == 0 {
        return None;
    }
    let low = -(1i64 << (bitwidth - 1));
    let offset = i64::try_from(idx - int_start).unwrap_or(i64::MAX);
    Some(low + offset)
}

// -------------------------------------------------- translation-time folding

/// Three-valued translation-time emptiness of a relational expression's cell
/// set — Kodkod's `cells.isEmpty()` (`Empty`) and "holds a constant-`TRUE` cell"
/// (`NonEmpty`), which is what the union/override fast paths and the
/// `lone`/`one`/`some` short-circuits test.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Emptiness {
    /// Provably zero cells at translation time.
    Empty,
    /// Provably at least one constant-`TRUE` cell at translation time.
    NonEmpty,
    /// Neither is provable — the matrix carries solver variables, or the shape
    /// is one the folder deliberately does not model. Never sheds a guard, so an
    /// `Unknown` can only ever over-guard (mettle's pre-mt-130 behavior).
    Unknown,
}

/// The translation-time constant folder behind (R-a): Kodkod's cell folding,
/// expressed over mettle's IR.
///
/// Every input is a translation-time input — the IR, the bounds, the bitwidth,
/// and the **active grounding bindings** — so the encoder and the evaluator get
/// bit-identical answers by construction. It must never consult a runtime value
/// (mt-129 cell k9 separates the two: `no Node` empties `Node` in the instance
/// but not in the translation).
pub(crate) struct Fold<'a> {
    ir: &'a Ir,
    bounds: &'a Bounds,
    bitwidth: u32,
    int_start: usize,
    int_end: usize,
    /// Quantifier/comprehension/`sum` variables currently bound to one atom
    /// tuple by ground expansion — Kodkod's `Environment` of `groundValue`
    /// matrices, each a single `BooleanConstant.TRUE` cell.
    env: &'a BTreeMap<VarId, Tuple>,
}

impl<'a> Fold<'a> {
    /// Builds a folder over the current translation state.
    pub(crate) fn new(
        ir: &'a Ir,
        bounds: &'a Bounds,
        bitwidth: u32,
        int_start: usize,
        int_end: usize,
        env: &'a BTreeMap<VarId, Tuple>,
    ) -> Self {
        Self {
            ir,
            bounds,
            bitwidth,
            int_start,
            int_end,
            env,
        }
    }

    fn atom_int(&self, atom: AtomId) -> Option<i64> {
        atom_int_value(atom, self.int_start, self.int_end, self.bitwidth)
    }

    /// Three-valued emptiness of a relational expression's translated matrix.
    pub(crate) fn emptiness(&self, id: RelExprId) -> Emptiness {
        use Emptiness::{Empty, NonEmpty, Unknown};
        match &self.ir.rel_exprs[id].kind {
            // `none` has no cells; `univ`/`iden` have constant-TRUE ones as long
            // as the universe is inhabited (it always is, but assert nothing).
            RelExprKind::Const(RelConst::None) => Empty,
            RelExprKind::Const(RelConst::Univ | RelConst::Iden) => {
                if self.bounds.universe.is_empty() {
                    Empty
                } else {
                    NonEmpty
                }
            }
            // A ground-expanded binder is a singleton constant-TRUE matrix; a
            // free variable is not folded at all.
            RelExprKind::Var(v) => {
                if self.env.contains_key(v) {
                    NonEmpty
                } else {
                    Unknown
                }
            }
            // Lower-bound tuples are constant-TRUE cells; an empty upper bound
            // leaves no cells at all. Anything between is solver-variable.
            RelExprKind::Relation(r) => match self.bounds.get(*r) {
                Some(b) if !b.lower().is_empty() => NonEmpty,
                Some(b) if b.upper().is_empty() => Empty,
                _ => Unknown,
            },
            // (R-a): a constant overflow circuit folds every cell to FALSE, and
            // `BooleanMatrix.set` drops a FALSE cell.
            RelExprKind::IntToAtom(ie) => match self.int(*ie) {
                Some((_, true)) => Empty,
                Some((_, false)) => NonEmpty,
                None => Unknown,
            },
            RelExprKind::Binary { op, lhs, rhs } => self.binary_emptiness(*op, *lhs, *rhs),
            RelExprKind::Unary { op, expr } => match op {
                // Transpose permutes the cells; iterative squaring `or`s the
                // operand's own cells into the closure. Both preserve emptiness
                // in each direction.
                RelUnOp::Transpose | RelUnOp::Closure => self.emptiness(*expr),
                // `*e` folds in `iden`, whose cells are constants — but only over
                // the binary universe square, which is not worth modelling.
                RelUnOp::ReflexiveClosure => Unknown,
            },
            // Kodkod's `choice`: a constant condition returns the taken branch's
            // clone, otherwise every cell is an `ite` of the two.
            RelExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => match self.formula(*cond) {
                Some(true) => self.emptiness(*then_branch),
                Some(false) => self.emptiness(*else_branch),
                None => {
                    if self.emptiness(*then_branch) == Empty
                        && self.emptiness(*else_branch) == Empty
                    {
                        Empty
                    } else {
                        Unknown
                    }
                }
            },
            // A comprehension's cells are formula circuits over its own decls;
            // §10.7e/M5 — it never propagates a circuit outward either.
            RelExprKind::Comprehension { .. } | RelExprKind::Prime(_) => Unknown,
        }
    }

    fn binary_emptiness(&self, op: RelBinOp, lhs: RelExprId, rhs: RelExprId) -> Emptiness {
        use Emptiness::{Empty, NonEmpty, Unknown};
        let (l, r) = (self.emptiness(lhs), self.emptiness(rhs));
        match op {
            // `or`: a cell is TRUE as soon as either side's is.
            RelBinOp::Union => {
                if l == Empty && r == Empty {
                    Empty
                } else if l == NonEmpty || r == NonEmpty {
                    NonEmpty
                } else {
                    Unknown
                }
            }
            // `override`: the right operand's cells win outright, but a left
            // cell only survives where the right has no row — so a constant-TRUE
            // cell on the LEFT proves nothing unless the right is empty.
            RelBinOp::Override => {
                if l == Empty && r == Empty {
                    Empty
                } else if r == NonEmpty || (r == Empty && l == NonEmpty) {
                    NonEmpty
                } else {
                    Unknown
                }
            }
            // `and`/`dot`/`cross`: an empty operand annihilates.
            RelBinOp::Intersect | RelBinOp::Join => {
                if l == Empty || r == Empty {
                    Empty
                } else {
                    Unknown
                }
            }
            RelBinOp::Product => {
                if l == Empty || r == Empty {
                    Empty
                } else if l == NonEmpty && r == NonEmpty {
                    NonEmpty
                } else {
                    Unknown
                }
            }
            // `difference`: cells are `and(l, not(r))`. `x ∧ ¬x` folds to FALSE
            // in the factory, so structurally identical operands cancel — which
            // is exactly what makes `Int - Int` a cells-empty union operand
            // (mt-129 cells a7/a8).
            RelBinOp::Diff => {
                if l == Empty || rel_expr_eq(self.ir, lhs, rhs) {
                    Empty
                } else if l == NonEmpty && r == Empty {
                    NonEmpty
                } else {
                    Unknown
                }
            }
        }
    }

    /// The constant `(value, overflow)` of an integer expression under the
    /// active bindings, or `None` when it is not a translation constant.
    pub(crate) fn int(&self, id: IntExprId) -> Option<(i64, bool)> {
        match &self.ir.int_exprs[id].kind {
            IntExprKind::Const(v) => Some((
                wrap_signed(i64::from(*v), self.bitwidth),
                const_overflows(*v, self.bitwidth),
            )),
            IntExprKind::Card(rel) => {
                let c = self.card(*rel)?;
                // `BooleanMatrix.cardinality` merges the matrix's own circuit
                // (§10.7g/M4), so `#e` overflows if any surviving cast under `e`
                // does — the same merge both back ends perform on the circuit.
                let mut of = c > i64::from(crate::lower::int_max(self.bitwidth));
                let mut casts = Vec::new();
                collect_capable_casts(self, *rel, &mut casts);
                for ie in casts {
                    of = of || self.int(ie)?.1;
                }
                Some((wrap_signed(c, self.bitwidth), of))
            }
            IntExprKind::AtomToInt(rel) => self.int_of_set(*rel),
            IntExprKind::Neg(ie) => {
                let (v, of) = self.int(*ie)?;
                let min = i64::from(crate::lower::int_min(self.bitwidth));
                Some((wrap_signed(-v, self.bitwidth), of || v == min))
            }
            IntExprKind::Binary { op, lhs, rhs } => {
                let (a, oa) = self.int(*lhs)?;
                let (b, ob) = self.int(*rhs)?;
                let (v, op_of) = int_binop_value(*op, a, b, self.bitwidth);
                Some((v, oa || ob || op_of))
            }
            // A `sum` binder ranges over a matrix, so its value is only constant
            // when that matrix is — not worth folding, and never needed by the
            // measured cells.
            IntExprKind::Sum { .. } => None,
            IntExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                if self.formula(*cond)? {
                    self.int(*then_branch)
                } else {
                    self.int(*else_branch)
                }
            }
        }
    }

    /// The exact translation-time cardinality of a relational expression.
    fn card(&self, id: RelExprId) -> Option<i64> {
        let e = self.emptiness(id);
        if e == Emptiness::Empty {
            return Some(0);
        }
        match &self.ir.rel_exprs[id].kind {
            RelExprKind::Var(v) => self.env.get(v).map(|_| 1),
            RelExprKind::Relation(r) => {
                let b = self.bounds.get(*r)?;
                (b.lower() == b.upper()).then(|| i64::try_from(b.lower().len()).unwrap_or(i64::MAX))
            }
            // A cast is one cell exactly when the fold PROVED it did not
            // overflow; an unfoldable one has an unknown count, not one.
            RelExprKind::IntToAtom(_) => (e == Emptiness::NonEmpty).then_some(1),
            _ => None,
        }
    }

    /// `int[e]`: the signed sum of the `Int` atoms of a constant-valued set,
    /// accumulated in tuple order exactly as both back ends chain their adds, so
    /// an intermediate step leaving the range trips overflow.
    fn int_of_set(&self, id: RelExprId) -> Option<(i64, bool)> {
        let values = self.const_atom_ints(id)?;
        let (min, max) = (
            i64::from(crate::lower::int_min(self.bitwidth)),
            i64::from(crate::lower::int_max(self.bitwidth)),
        );
        let (mut acc, mut of) = (0i64, false);
        for v in values {
            let exact = acc + v;
            of = of || exact < min || exact > max;
            acc = wrap_signed(exact, self.bitwidth);
        }
        Some((acc, of))
    }

    /// The `Int`-atom values a constant-valued set contributes, in tuple order.
    /// Non-`Int` atoms and non-unary tuples contribute nothing, matching both
    /// back ends' `int[·]`.
    fn const_atom_ints(&self, id: RelExprId) -> Option<Vec<i64>> {
        match &self.ir.rel_exprs[id].kind {
            RelExprKind::Const(RelConst::None) => Some(Vec::new()),
            RelExprKind::Var(v) => {
                let t = self.env.get(v)?;
                Some(match (t.arity(), self.atom_int(t.atoms()[0])) {
                    (1, Some(n)) => vec![n],
                    _ => Vec::new(),
                })
            }
            RelExprKind::Relation(r) => {
                let b = self.bounds.get(*r)?;
                (b.lower() == b.upper()).then(|| {
                    b.lower()
                        .iter()
                        .filter(|t| t.arity() == 1)
                        .filter_map(|t| self.atom_int(t.atoms()[0]))
                        .collect()
                })
            }
            // `Int[e]` denotes one atom, or none when it overflowed.
            RelExprKind::IntToAtom(ie) => match self.int(*ie)? {
                (_, true) => Some(Vec::new()),
                (v, false) => Some(vec![v]),
            },
            _ => None,
        }
    }

    /// The constant truth value of a formula, or `None`. Reached only through an
    /// if-then-else condition, where Kodkod's `choice` fast paths need it.
    pub(crate) fn formula(&self, id: FormulaId) -> Option<bool> {
        match &self.ir.formulas[id].kind {
            FormulaKind::Const(b) => Some(*b),
            FormulaKind::Not(f) => self.formula(*f).map(|b| !b),
            FormulaKind::And(parts) => self.junction(parts, false),
            FormulaKind::Or(parts) => self.junction(parts, true),
            FormulaKind::Implies {
                antecedent,
                consequent,
            } => {
                let a = self.formula(*antecedent);
                let c = self.formula(*consequent);
                match (a, c) {
                    (Some(false), _) | (_, Some(true)) => Some(true),
                    (Some(true), Some(v)) => Some(v),
                    _ => None,
                }
            }
            FormulaKind::Iff(l, r) => Some(self.formula(*l)? == self.formula(*r)?),
            // Only an overflow-free constant comparison folds: an overflowing one
            // would carry a guard of its own, whose polarity this folder cannot
            // see.
            FormulaKind::IntCompare { op, lhs, rhs } => match (self.int(*lhs), self.int(*rhs)) {
                (Some((a, false)), Some((b, false))) => Some(match op {
                    IntCmpOp::Eq => a == b,
                    IntCmpOp::Lt => a < b,
                    IntCmpOp::Gt => a > b,
                    IntCmpOp::Le => a <= b,
                    IntCmpOp::Ge => a >= b,
                }),
                _ => None,
            },
            FormulaKind::MultTest { test, expr } => {
                let e = self.emptiness(*expr);
                match (test, e) {
                    (MultTest::No | MultTest::Lone, Emptiness::Empty)
                    | (MultTest::Some, Emptiness::NonEmpty) => Some(true),
                    (MultTest::No, Emptiness::NonEmpty)
                    | (MultTest::One | MultTest::Some, Emptiness::Empty) => Some(false),
                    _ => None,
                }
            }
            FormulaKind::RelCompare { .. }
            | FormulaKind::Quant { .. }
            | FormulaKind::LoopIs { .. }
            | FormulaKind::TemporalUnary { .. }
            | FormulaKind::TemporalBinary { .. } => None,
        }
    }

    /// `And` (`absorbing = false`) / `Or` (`absorbing = true`) over a part list.
    fn junction(&self, parts: &[FormulaId], absorbing: bool) -> Option<bool> {
        let mut known = true;
        for &p in parts {
            match self.formula(p) {
                Some(v) if v == absorbing => return Some(absorbing),
                Some(_) => {}
                None => known = false,
            }
        }
        known.then_some(!absorbing)
    }
}

/// Structural equality of two relational expressions. The IR arena does not
/// intern, so two spellings of the same expression are distinct ids; Kodkod
/// translates both to the same circuit, which its factory then folds. Only
/// [`Fold::binary_emptiness`] needs this, for `e - e`.
fn rel_expr_eq(ir: &Ir, a: RelExprId, b: RelExprId) -> bool {
    if a == b {
        return true;
    }
    match (&ir.rel_exprs[a].kind, &ir.rel_exprs[b].kind) {
        (RelExprKind::Relation(x), RelExprKind::Relation(y)) => x == y,
        (RelExprKind::Var(x), RelExprKind::Var(y)) => x == y,
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
        ) => xo == yo && rel_expr_eq(ir, *xl, *yl) && rel_expr_eq(ir, *xr, *yr),
        (RelExprKind::Unary { op: xo, expr: xe }, RelExprKind::Unary { op: yo, expr: ye }) => {
            xo == yo && rel_expr_eq(ir, *xe, *ye)
        }
        (RelExprKind::Prime(x), RelExprKind::Prime(y)) => rel_expr_eq(ir, *x, *y),
        // A comprehension binds fresh `VarId`s per occurrence and an `Int[·]`
        // would need int-expr equality; neither is needed, so neither is claimed.
        _ => false,
    }
}

// ------------------------------------------------------- the surviving casts

/// Collects every **overflow-capable** `Int[·]` cast whose overflow circuit
/// survives the jar's matrix folding up to the reader — the (B) guard's operand
/// list (translation-ref §10.7c ext / §10.7e–§10.7k, mt-051/mt-129/mt-130).
///
/// The walk descends the set-operator structure, applying (R-b): a UNION drops
/// the circuit of a cells-empty operand, testing the LEFT one first, and an
/// OVERRIDE runs the same test on its RIGHT operand only. Intersection,
/// difference, join, product and unary formers merge unconditionally; an
/// if-then-else with a constant condition contributes only the taken branch, and
/// merges both otherwise.
///
/// It does **not** enter `Formula` positions (a comprehension body, an ITE
/// condition: those guard at their own comparison sites) nor the int expr
/// beneath a cast (`#·`/`sum` reading is handled at the `Card`/`AtomToInt` node
/// per §10.7g/M4). Pushed in traversal order so the caller's lhs-then-rhs walk is
/// deterministic (STYLE D2).
pub(crate) fn collect_capable_casts(fold: &Fold, id: RelExprId, out: &mut Vec<IntExprId>) {
    let ir = fold.ir;
    match &ir.rel_exprs[id].kind {
        RelExprKind::IntToAtom(ie) => {
            if overflow_capable(ir, fold.bitwidth, *ie) {
                out.push(*ie);
            }
        }
        RelExprKind::Binary { op, lhs, rhs } => match op {
            RelBinOp::Union => {
                if fold.emptiness(*lhs) == Emptiness::Empty {
                    collect_capable_casts(fold, *rhs, out);
                } else if fold.emptiness(*rhs) == Emptiness::Empty {
                    collect_capable_casts(fold, *lhs, out);
                } else {
                    collect_capable_casts(fold, *lhs, out);
                    collect_capable_casts(fold, *rhs, out);
                }
            }
            RelBinOp::Override => {
                collect_capable_casts(fold, *lhs, out);
                if fold.emptiness(*rhs) != Emptiness::Empty {
                    collect_capable_casts(fold, *rhs, out);
                }
            }
            RelBinOp::Intersect | RelBinOp::Diff | RelBinOp::Join | RelBinOp::Product => {
                collect_capable_casts(fold, *lhs, out);
                collect_capable_casts(fold, *rhs, out);
            }
        },
        RelExprKind::Unary { expr, .. } => collect_capable_casts(fold, *expr, out),
        RelExprKind::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => match fold.formula(*cond) {
            Some(true) => collect_capable_casts(fold, *then_branch, out),
            Some(false) => collect_capable_casts(fold, *else_branch, out),
            None => {
                collect_capable_casts(fold, *then_branch, out);
                collect_capable_casts(fold, *else_branch, out);
            }
        },
        // Leaves and Formula-bearing nodes stop the set-structure walk.
        RelExprKind::Relation(_)
        | RelExprKind::Var(_)
        | RelExprKind::Const(_)
        | RelExprKind::Comprehension { .. }
        | RelExprKind::Prime(_) => {}
    }
}

/// [`collect_capable_casts`] behind a multiplicity test, applying (R-c): `lone`
/// and `one` return before `DefCond.ensureDef` on a cells-empty matrix, and
/// `some` returns as soon as it sees a constant-`TRUE` cell — all three shed
/// every guard the operand structure would otherwise have delivered. `no` reaches
/// `ensureDef` on an empty matrix and never sheds (`BooleanMatrix` :967/:987/:951
/// vs :1010).
pub(crate) fn collect_mult_test_casts(
    fold: &Fold,
    test: MultTest,
    expr: RelExprId,
    out: &mut Vec<IntExprId>,
) {
    let sheds = match test {
        MultTest::Lone | MultTest::One => fold.emptiness(expr) == Emptiness::Empty,
        MultTest::Some => fold.emptiness(expr) == Emptiness::NonEmpty,
        MultTest::No => false,
    };
    if !sheds {
        collect_capable_casts(fold, expr, out);
    }
}

/// Classifies one overflowing operand at a comparison (translation-ref §10.7c's
/// operational rule list), returning `forall_dep` = whether it classifies as
/// depending on an effective-∀ (a **rescue**) rather than an existential (an
/// **exclude**). `frames` is the enclosing-quantifier stack (innermost last);
/// `free` is the operand's free-variable set.
///
/// This is `DefCond.isUnivQuant` verbatim in behavior, and it has **no other
/// inputs**: neither an `implies` antecedent nor an int-ITE is an escape
/// (§10.7f, mt-090 — the old rule 4 is retracted).
pub(crate) fn classify(frames: &[QuantFrame], free: &BTreeSet<VarId>) -> bool {
    // The single per-variable rule (§10.7c rules 0–3): classify by the innermost
    // enclosing binder whose domain is bare `Int`/`seq/Int` and whose variable the
    // operand depends on — a bare-`Int` ∀ rescues, a bare-`Int` ∃ excludes. No
    // bare-`Int` binder ⇒ Defect A defaults the classification to **existential**
    // (exclude), regardless of nesting shape/depth/type.
    frames
        .iter()
        .rev()
        .find(|f| f.bare_int && free.contains(&f.var))
        .is_some_and(|f| f.effective_forall)
}
