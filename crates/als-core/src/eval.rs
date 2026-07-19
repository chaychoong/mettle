//! The direct three-sorted evaluator + the self-check net (mt-034,
//! translation-ref §6, ADR-0011 decision 5).
//!
//! This is an **independent second implementation** of the same relational
//! semantics the [`crate::encode`]r implements as SAT gates — but here over a
//! *concrete* [`Instance`], returning concrete values: a [`Formula`] evaluates
//! to a `bool`, a [`RelExpr`](crate::ir::RelExpr) to a [`TupleSet`], an
//! [`IntExpr`](crate::ir::IntExpr) to an `i64`. Two independent implementations
//! agreeing on exact instance counts (the encoder↔evaluator differential in
//! `tests/eval_differential.rs`) is the real correctness gauge; the self-check
//! ([`self_check`]) is how Rung 3 earns its "self-verified" promise without ever
//! diffing the jar's tuples.
//!
//! **Semantics faithful, structure idiomatic** (PORTING prime directive): a
//! bottom-up walk that grounds quantifiers/comprehensions over their bound's
//! concrete tuples, computes closure by fixpoint, and reads the integer slice
//! (`#`, `int[·]`, `Int[·]`) off the universe's Int-atom range. Every node kind
//! is matched with **no catch-all** (PORTING R1); constructs outside the Rung-3
//! slice (temporal, integer arithmetic / `sum` / integer-`ITE`) return the same
//! typed [`TranslateError`] the encoder defers with, so the evaluator and encoder
//! stay a **matched pair** — never one accepting what the other cannot solve.
//!
//! ## Overflow (translation-ref §2.4, LEDGER-001)
//! The encoder makes an instance *accepted* iff `goal ∧ ⋀ᵢ ¬overflowᵢ` holds:
//! with overflow **forbidden** (the default), any evaluated `#e` whose count
//! exceeds the signed range, or any intermediate `int[·]` sum that steps outside
//! it, **excludes the instance**. For the self-check to be consistent with the
//! solver's accept-set (so the differential counts match), the evaluator mirrors
//! this exactly: it evaluates the goal to a `bool` *and* tracks whether any Int
//! term overflowed; [`Evaluator::accepts`] returns `goal_holds && (allow ||
//! !overflowed)`. With overflow **allowed** the value simply wraps two's
//! complement at the bitwidth (matching the encoder's silent wrap). A
//! solver-produced instance never overflows (the solver conjoined every
//! `¬overflowᵢ`), so the self-check never rejects one on overflow grounds; the
//! path exists only to make the brute-force differential agree.

use std::collections::{BTreeMap, BTreeSet};

use als_syntax::ArenaId;

use crate::bounds::{AtomId, Tuple, TupleSet};
use crate::error::TranslateError;
use crate::ir::{
    FormulaId, FormulaKind, IntCmpOp, IntExprId, IntExprKind, Ir, MultTest, QuantKind, RelBinOp,
    RelCmpOp, RelConst, RelExprId, RelExprKind, RelId, RelUnOp, VarId,
};
use crate::lower::{LoweredGoal, Provenance};
use crate::scope::ScopedUniverse;
use crate::solve::{Instance, SolveOptions};

use crate::overflow_guard::shift_mask_width;

/// A concrete three-sorted evaluator over one solved [`Instance`].
///
/// The mutable state is exactly the encoder's: the grounding environment (`env`:
/// quantifier/comprehension variable → its bound atom tuple) and an `overflow`
/// flag gathered from the Int slice. Held by `&mut self` methods rather than an
/// immutable `EvalCtx` + interior mutability, to match the surrounding code's
/// explicit-state style (PORTING R7) — the three public methods
/// [`Evaluator::eval_formula`] / [`Evaluator::eval_rel`] / [`Evaluator::eval_int`]
/// are the documented three-sorted API and the future REPL substrate (Rung 5).
#[derive(Debug)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "the four flags are distinct evaluation state (overflow mode, observed \
              overflow, polarity, conditional context) — not a config bundle"
)]
pub struct Evaluator<'a> {
    ir: &'a Ir,
    instance: &'a Instance,
    /// Int atoms span `-2^(bw-1) … 2^(bw-1)-1`; `int_start` is the universe index
    /// of the first Int atom (sig atoms precede them).
    bitwidth: u32,
    int_start: usize,
    /// Universe index just past the last integer atom (`int_start + 2^bw`).
    /// String atoms (mt-045) trail the integer atoms, so an atom in
    /// `[int_end, universe_len)` is a string atom, never an integer.
    int_end: usize,
    universe_len: usize,
    allow_overflow: bool,
    env: BTreeMap<VarId, Tuple>,
    /// Set when a forbidden overflow fired at a comparison during the current
    /// evaluation — diagnostic only (the accept value bakes the guard in).
    overflow: bool,
    /// Current formula polarity (translation-ref §11.3): `true` = positive.
    /// Flipped by `Not` / `Implies` antecedent; drives the overflow-guard.
    pol_positive: bool,
    /// The enclosing-quantifier stack (innermost last), driving the §10.7c
    /// overflow classification — the same the encoder threads, so the two apply
    /// an identical guard and defer identically.
    quant_frames: Vec<crate::overflow_guard::QuantFrame>,
    /// Whether under an `Implies` antecedent (the rule-6 defer precondition).
    behind_implies: bool,
    /// The `Int`/`seq/Int` builtin relation ids, for recognizing a bare-`Int`
    /// quantifier domain (translation-ref §10.7c rule 0).
    int_sig: Option<RelId>,
    seq_int_sig: Option<RelId>,
}

impl<'a> Evaluator<'a> {
    /// Builds an evaluator for `instance` under the command's integer parameters.
    #[must_use]
    pub fn new(
        ir: &'a Ir,
        instance: &'a Instance,
        scoped: &ScopedUniverse,
        opts: &SolveOptions,
        int_sig: Option<RelId>,
        seq_int_sig: Option<RelId>,
    ) -> Self {
        Self {
            ir,
            instance,
            bitwidth: scoped.bitwidth,
            int_start: scoped.sig_atom_count,
            int_end: scoped.sig_atom_count + scoped.int_atom_count,
            universe_len: instance.universe.len(),
            allow_overflow: opts.allow_overflow,
            env: BTreeMap::new(),
            overflow: false,
            pol_positive: true,
            quant_frames: Vec::new(),
            behind_implies: false,
            int_sig,
            seq_int_sig,
        }
    }

    /// Evaluates `f` as the **top-level accept predicate** for one instance:
    /// its truth value *and* the forbid-overflow exclusion (translation-ref
    /// §2.4). Resets the overflow flag first, so it reflects only this call.
    ///
    /// # Errors
    /// A [`TranslateError`] if `f` reaches a construct outside the Rung-3
    /// evaluable slice (temporal / integer arithmetic) — which, for a
    /// solver-produced goal, is an internal inconsistency, since the encoder
    /// would have deferred it before solving.
    pub fn accepts(&mut self, f: FormulaId) -> Result<bool, TranslateError> {
        self.overflow = false;
        self.pol_positive = true;
        self.quant_frames.clear();
        self.behind_implies = false;
        // The forbid-mode overflow guard is applied locally at each comparison
        // (translation-ref §11.3), so the goal's truth value already embeds it —
        // no top-level `∧ ¬overflow` conjunction (that would flip the
        // universal-rescue case I11).
        self.eval_formula(f)
    }

    // ------------------------------------------------------------- formulas

    /// Evaluates a formula to a `bool` over the instance.
    ///
    /// Boolean connectives evaluate **all** operands (no short-circuit) so every
    /// Int subterm's overflow is observed — matching the encoder, which builds a
    /// gate for every subterm regardless of context (translation-ref §2.4).
    ///
    /// # Errors
    /// A [`TranslateError`] for a temporal connective (never reaches a Rung-3
    /// goal) or an unsupported integer op nested in a comparison.
    pub fn eval_formula(&mut self, id: FormulaId) -> Result<bool, TranslateError> {
        let node = &self.ir.formulas[id];
        match &node.kind {
            FormulaKind::Const(b) => Ok(*b),
            FormulaKind::Not(f) => {
                let f = *f;
                self.pol_positive = !self.pol_positive;
                let v = self.eval_formula(f);
                self.pol_positive = !self.pol_positive;
                Ok(!v?)
            }
            FormulaKind::And(parts) => {
                let parts = parts.clone();
                let mut all = true;
                for p in parts {
                    all &= self.eval_formula(p)?;
                }
                Ok(all)
            }
            FormulaKind::Or(parts) => {
                let parts = parts.clone();
                let mut any = false;
                for p in parts {
                    any |= self.eval_formula(p)?;
                }
                Ok(any)
            }
            FormulaKind::Implies {
                antecedent,
                consequent,
            } => {
                let (antecedent, consequent) = (*antecedent, *consequent);
                // `a ⟹ c` = `¬a ∨ c`: the antecedent is at flipped polarity and a
                // rule-6 conditional context (translation-ref §10.7c).
                self.pol_positive = !self.pol_positive;
                let saved_bi = self.behind_implies;
                self.behind_implies = true;
                let a = self.eval_formula(antecedent);
                self.behind_implies = saved_bi;
                self.pol_positive = !self.pol_positive;
                let a = a?;
                let c = self.eval_formula(consequent)?;
                Ok(!a || c)
            }
            FormulaKind::Iff(l, r) => {
                let a = self.eval_formula(*l)?;
                let b = self.eval_formula(*r)?;
                Ok(a == b)
            }
            FormulaKind::RelCompare { op, lhs, rhs } => {
                let (op, lhs, rhs) = (*op, *lhs, *rhs);
                // Matched-pair defer for the unpinned integer-equality typing rule
                // (translation-ref §10.7c GAP1a) — identical predicate to the
                // encoder's, so the two defer on exactly the same commands.
                if crate::overflow_guard::eq_typing_defer(self.ir, lhs, rhs, self.allow_overflow) {
                    return Err(TranslateError::LoweringUnsupported {
                        what: "forbid-mode overflow guard for a relational (=/in) comparison \
                               between an arithmetic result and a plain Int-typed operand is \
                               not pinned (translation-ref §10.7c GAP1a)"
                            .to_owned(),
                        span: self.ir.rel_exprs[lhs].span,
                    });
                }
                let a = self.eval_rel(lhs)?;
                let b = self.eval_rel(rhs)?;
                Ok(match op {
                    RelCmpOp::Subset => a.is_subset_of(&b),
                    RelCmpOp::Equal => a == b,
                })
            }
            FormulaKind::IntCompare { op, lhs, rhs } => {
                let (op, lhs, rhs) = (*op, *lhs, *rhs);
                let (a, oa) = self.eval_int(lhs)?;
                let (b, ob) = self.eval_int(rhs)?;
                let atom = match op {
                    IntCmpOp::Eq => a == b,
                    IntCmpOp::Lt => a < b,
                    IntCmpOp::Le => a <= b,
                    IntCmpOp::Gt => a > b,
                    IntCmpOp::Ge => a >= b,
                };
                self.int_compare_guard(atom, oa, ob, lhs, rhs)
            }
            FormulaKind::MultTest { test, expr } => {
                let m = self.eval_rel(*expr)?;
                Ok(match test {
                    MultTest::No => m.is_empty(),
                    MultTest::Some => !m.is_empty(),
                    MultTest::Lone => m.len() <= 1,
                    MultTest::One => m.len() == 1,
                })
            }
            FormulaKind::Quant {
                kind,
                var,
                bound,
                body,
            } => self.eval_quant(*kind, *var, *bound, *body),
            FormulaKind::TemporalUnary { .. } | FormulaKind::TemporalBinary { .. } => {
                Err(TranslateError::TemporalUnsupported {
                    op: "temporal operator reached the evaluator — a lowering invariant \
                         failure; temporal solving is Rung 6",
                    span: node.span,
                })
            }
        }
    }

    /// Grounds a single-variable quantifier over its bound's concrete tuples
    /// (translation-ref §2.3). `all` = every binding's body holds; `some` = some
    /// binding's does. Evaluates every binding (no short-circuit) so nested Int
    /// overflow is observed, matching the encoder's full grounding.
    fn eval_quant(
        &mut self,
        kind: QuantKind,
        var: VarId,
        bound: RelExprId,
        body: FormulaId,
    ) -> Result<bool, TranslateError> {
        let bm = self.eval_rel(bound)?;
        let tuples: Vec<Tuple> = bm.iter().cloned().collect();
        // Effective quantifier kind + bare-`Int` domain for the overflow rule
        // (translation-ref §10.7c), identical to the encoder's.
        let effective_forall = matches!(kind, QuantKind::All) == self.pol_positive;
        let bare_int = self.is_bare_int_bound(bound);
        self.quant_frames.push(crate::overflow_guard::QuantFrame {
            var,
            bare_int,
            effective_forall,
        });
        let mut acc = matches!(kind, QuantKind::All);
        let mut result = Ok(());
        for t in tuples {
            let prev = self.env.insert(var, t);
            let body_v = self.eval_formula(body);
            match prev {
                Some(p) => {
                    self.env.insert(var, p);
                }
                None => {
                    self.env.remove(&var);
                }
            }
            match body_v {
                Ok(body_v) => match kind {
                    QuantKind::All => acc &= body_v,
                    QuantKind::Some => acc |= body_v,
                },
                Err(e) => {
                    result = Err(e);
                    break;
                }
            }
        }
        self.quant_frames.pop();
        result?;
        Ok(acc)
    }

    /// Whether a quantifier bound is literally the bare `Int`/`seq/Int` builtin
    /// relation (translation-ref §10.7c) — matched to the encoder's check.
    fn is_bare_int_bound(&self, bound: RelExprId) -> bool {
        match &self.ir.rel_exprs[bound].kind {
            RelExprKind::Relation(r) => Some(*r) == self.int_sig || Some(*r) == self.seq_int_sig,
            _ => false,
        }
    }

    // ------------------------------------------------------------ relations

    /// Evaluates a relation expression to a concrete [`TupleSet`].
    ///
    /// # Errors
    /// A [`TranslateError`] for a temporal `Prime` (never reaches a Rung-3 goal)
    /// or an unsupported integer op inside `Int[·]`.
    pub fn eval_rel(&mut self, id: RelExprId) -> Result<TupleSet, TranslateError> {
        let node = &self.ir.rel_exprs[id];
        match &node.kind {
            RelExprKind::Relation(rel) => Ok(self.relation_value(*rel)),
            RelExprKind::Var(v) => Ok(self.var_value(*v)),
            RelExprKind::Const(c) => Ok(self.const_value(*c)),
            RelExprKind::Binary { op, lhs, rhs } => {
                let a = self.eval_rel(*lhs)?;
                let b = self.eval_rel(*rhs)?;
                Ok(rel_binary(*op, &a, &b))
            }
            RelExprKind::Unary { op, expr } => {
                let a = self.eval_rel(*expr)?;
                Ok(self.rel_unary(*op, &a))
            }
            RelExprKind::Prime(_) => Err(TranslateError::TemporalUnsupported {
                op: "temporal prime (`'`) reached the evaluator — a lowering invariant \
                     failure; temporal solving is Rung 6",
                span: node.span,
            }),
            RelExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                if self.eval_formula(*cond)? {
                    self.eval_rel(*then_branch)
                } else {
                    self.eval_rel(*else_branch)
                }
            }
            RelExprKind::Comprehension { decls, body } => {
                let decls = decls.clone();
                let body = *body;
                self.eval_comprehension(&decls, body)
            }
            RelExprKind::IntToAtom(ie) => {
                // `Int[·]` drops the operand's overflow (guarded only at
                // comparisons — translation-ref §11.3), matching the encoder.
                let (v, _of) = self.eval_int(*ie)?;
                Ok(self.int_to_atom(v))
            }
        }
    }

    /// A free relation's value: its decoded tuple set (every bounded relation is
    /// decoded, STYLE I1).
    fn relation_value(&self, rel: RelId) -> TupleSet {
        if let Some(ts) = self.instance.get(rel) {
            ts.clone()
        } else {
            debug_assert!(false, "unbounded relation {rel:?} in the evaluated goal");
            TupleSet::empty(self.ir.relations[rel].arity)
        }
    }

    /// A bound variable's value: the single atom tuple it is currently bound to.
    fn var_value(&self, v: VarId) -> TupleSet {
        let arity = self.ir.vars[v].arity;
        let mut m = TupleSet::empty(arity);
        if let Some(t) = self.env.get(&v) {
            m.insert(t.clone());
        } else {
            debug_assert!(false, "unbound IR variable {v:?} in the evaluated goal");
        }
        m
    }

    /// A relational constant over the universe (`none` / `univ` / `iden`).
    fn const_value(&self, c: RelConst) -> TupleSet {
        match c {
            RelConst::None => TupleSet::empty(1),
            RelConst::Univ => {
                let mut m = TupleSet::empty(1);
                for i in 0..self.universe_len {
                    m.insert(Tuple::new(vec![AtomId::from_index(i)]));
                }
                m
            }
            RelConst::Iden => {
                let mut m = TupleSet::empty(2);
                for i in 0..self.universe_len {
                    let a = AtomId::from_index(i);
                    m.insert(Tuple::new(vec![a, a]));
                }
                m
            }
        }
    }

    fn rel_unary(&self, op: RelUnOp, a: &TupleSet) -> TupleSet {
        match op {
            RelUnOp::Transpose => transpose(a),
            RelUnOp::Closure => closure(a),
            RelUnOp::ReflexiveClosure => {
                let c = closure(a);
                let iden = self.const_value(RelConst::Iden);
                union(&c, &iden)
            }
        }
    }

    /// Grounds a set comprehension (translation-ref §2.1): the concatenation of
    /// each binding's atoms, kept iff the body holds under that binding. Nested so
    /// a later decl's bound may reference an earlier decl's variable.
    fn eval_comprehension(
        &mut self,
        decls: &[crate::ir::CompDecl],
        body: FormulaId,
    ) -> Result<TupleSet, TranslateError> {
        let arity: usize = decls.iter().map(|d| self.ir.vars[d.var].arity).sum();
        let mut out = TupleSet::empty(arity.max(1));
        self.comprehension_rec(decls, 0, body, &mut Vec::new(), &mut out)?;
        Ok(out)
    }

    fn comprehension_rec(
        &mut self,
        decls: &[crate::ir::CompDecl],
        i: usize,
        body: FormulaId,
        prefix: &mut Vec<AtomId>,
        out: &mut TupleSet,
    ) -> Result<(), TranslateError> {
        if i == decls.len() {
            if self.eval_formula(body)? {
                out.insert(Tuple::new(prefix.clone()));
            }
            return Ok(());
        }
        let bm = self.eval_rel(decls[i].bound)?;
        let tuples: Vec<Tuple> = bm.iter().cloned().collect();
        for t in tuples {
            let atoms = t.atoms().to_vec();
            let prev = self.env.insert(decls[i].var, t);
            let plen = prefix.len();
            prefix.extend_from_slice(&atoms);
            let r = self.comprehension_rec(decls, i + 1, body, prefix, out);
            prefix.truncate(plen);
            match prev {
                Some(p) => {
                    self.env.insert(decls[i].var, p);
                }
                None => {
                    self.env.remove(&decls[i].var);
                }
            }
            r?;
        }
        Ok(())
    }

    // ------------------------------------------------------------- integers

    /// Evaluates an integer expression to a signed `i64` in the bitwidth range,
    /// **plus its accumulated overflow flag** (translation-ref §11.1–§11.3) — the
    /// matched pair of the encoder's [`crate::encode`] `int`. Every op wraps
    /// two's-complement identically to the encoder circuits; `div`/`rem` reproduce
    /// the jar's edge values (§10.7b). The overflow flag is consumed by the guard
    /// at comparisons and dropped at `Int[·]`.
    ///
    /// # Errors
    /// A [`TranslateError`] only for constructs outside the evaluable slice
    /// (temporal) reached through an int position — never for arithmetic itself.
    pub fn eval_int(&mut self, id: IntExprId) -> Result<(i64, bool), TranslateError> {
        let node = self.ir.int_exprs[id].clone();
        match node.kind {
            IntExprKind::Const(v) => Ok((self.wrap_signed(i64::from(v)), false)),
            IntExprKind::Card(rel) => {
                let m = self.eval_rel(rel)?;
                let c = i64::try_from(m.len()).unwrap_or(i64::MAX);
                let of = c > self.signed_max();
                Ok((self.wrap_signed(c), of))
            }
            IntExprKind::AtomToInt(rel) => {
                let m = self.eval_rel(rel)?;
                Ok(self.atom_to_int_value(&m))
            }
            IntExprKind::Neg(ie) => {
                let (v, of) = self.eval_int(ie)?;
                let neg_of = v == self.signed_min();
                Ok((self.wrap_signed(-v), of || neg_of))
            }
            IntExprKind::Binary { op, lhs, rhs } => {
                let (a, oa) = self.eval_int(lhs)?;
                let (b, ob) = self.eval_int(rhs)?;
                let (v, op_of) = self.int_binop_value(op, a, b);
                Ok((v, oa || ob || op_of))
            }
            IntExprKind::Sum { var, bound, body } => self.eval_sum(var, bound, body),
            IntExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                // Value and overflow both come from the taken branch (the encoder
                // muxes both, which is the taken one for a concrete instance).
                if self.eval_formula(cond)? {
                    self.eval_int(then_branch)
                } else {
                    self.eval_int(else_branch)
                }
            }
        }
    }

    /// One binary integer op over concrete operands, returning `(value, overflow)`
    /// with exactly the encoder circuits' two's-complement semantics
    /// (translation-ref §11.2, jar-verified §10.7b).
    fn int_binop_value(&self, op: crate::ir::IntBinOp, a: i64, b: i64) -> (i64, bool) {
        use crate::ir::IntBinOp;
        let (min, max) = (self.signed_min(), self.signed_max());
        let out_of_range = |x: i64| x < min || x > max;
        match op {
            IntBinOp::Add => (self.wrap_signed(a + b), out_of_range(a + b)),
            IntBinOp::Sub => (self.wrap_signed(a - b), out_of_range(a - b)),
            IntBinOp::Mul => (self.wrap_signed(a * b), out_of_range(a * b)),
            IntBinOp::Div => {
                if b == 0 {
                    let v = match a.cmp(&0) {
                        std::cmp::Ordering::Less => 1,
                        std::cmp::Ordering::Equal => 0,
                        std::cmp::Ordering::Greater => -1,
                    };
                    (v, true)
                } else {
                    (self.wrap_signed(a / b), a == min && b == -1)
                }
            }
            IntBinOp::Rem => {
                if b == 0 {
                    (a, true)
                } else {
                    (self.wrap_signed(a % b), false)
                }
            }
            IntBinOp::Shl => self.shl_value(a, b),
            IntBinOp::Sha => (self.shift_right_value(a, b, true), false),
            IntBinOp::Shr => (self.shift_right_value(a, b, false), false),
        }
    }

    /// Logical left shift with its **own** overflow flag, matching the encoder's
    /// `shl` bit-for-bit (translation-ref §10.7d): only the low `⌈log2 w⌉` amount
    /// bits shift the value, but the overflow loop runs over all `w` amount bits,
    /// so a masked-away junk bit can spuriously flag overflow when the (frozen)
    /// shifted value has a bit transition in the inspected region.
    #[allow(
        clippy::many_single_char_names,
        clippy::cast_sign_loss,
        clippy::cast_possible_wrap,
        reason = "concrete replica of the shl bit circuit; every cast is a bounded w-bit \
                  pattern (`rem_euclid` is non-negative and < 2^w)"
    )]
    fn shl_value(&self, a: i64, b: i64) -> (i64, bool) {
        let w = self.bitwidth as usize;
        let mask = shift_mask_width(w);
        let modw = 1i64 << self.bitwidth;
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
        (self.wrap_signed(s as i64), overflow)
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
    fn shift_right_value(&self, a: i64, b: i64, arith: bool) -> i64 {
        let w = self.bitwidth as usize;
        let mask = shift_mask_width(w);
        let modw = 1i64 << self.bitwidth;
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
            self.wrap_signed(((a.rem_euclid(modw) as u64) >> amt) as i64)
        }
    }

    /// `sum x: B | ie` (translation-ref §11.1): the plus-tree over the bound's
    /// present tuples, accumulated in two's complement; overflow accumulates each
    /// add's flag and each present body's overflow — matching the encoder.
    fn eval_sum(
        &mut self,
        var: VarId,
        bound: RelExprId,
        body: IntExprId,
    ) -> Result<(i64, bool), TranslateError> {
        let bm = self.eval_rel(bound)?;
        let tuples: Vec<Tuple> = bm.iter().cloned().collect();
        let (mut acc, mut of) = (0i64, false);
        for t in tuples {
            let prev = self.env.insert(var, t);
            let body_v = self.eval_int(body);
            match prev {
                Some(p) => {
                    self.env.insert(var, p);
                }
                None => {
                    self.env.remove(&var);
                }
            }
            let (bv, bof) = body_v?;
            let exact = acc + bv; // both in range ⇒ no i64 overflow
            of = of || bof || exact < self.signed_min() || exact > self.signed_max();
            acc = self.wrap_signed(exact);
        }
        Ok((acc, of))
    }

    /// `int[e]`: the signed sum of the integer values of the `Int` atoms in `e`,
    /// accumulated in tuple order in two's complement, exactly as the encoder's
    /// `int_atom_to_int` chains `add_signed` — so an intermediate step leaving the
    /// signed range trips overflow even when the final value is in range.
    fn atom_to_int_value(&mut self, m: &TupleSet) -> (i64, bool) {
        let mut acc: i64 = 0;
        let mut of = false;
        for t in m.iter() {
            if t.arity() != 1 {
                continue;
            }
            if let Some(v) = self.atom_int_value(t.atoms()[0]) {
                let exact = acc + v; // acc, v both in range ⇒ no i64 overflow
                if exact < self.signed_min() || exact > self.signed_max() {
                    of = true;
                }
                acc = self.wrap_signed(exact);
            }
        }
        (acc, of)
    }

    // ------------------------------------------ forbid-mode overflow guard

    /// Applies the forbid-mode overflow guard to a comparison via the shared
    /// [`crate::overflow_guard`] classifier (translation-ref §10.7c), matching the
    /// encoder's `int_compare` so the two accept-sets coincide. Allow mode passes
    /// the raw comparison; a jar-unpinned corner (Defect B / the ITE-`implies`
    /// sliver) is the same typed defer the encoder raises.
    fn int_compare_guard(
        &mut self,
        atom: bool,
        oa: bool,
        ob: bool,
        lhs: IntExprId,
        rhs: IntExprId,
    ) -> Result<bool, TranslateError> {
        if self.allow_overflow {
            return Ok(atom);
        }
        let g = self.apply_int_guard(atom, oa, lhs)?;
        self.apply_int_guard(g, ob, rhs)
    }

    /// One operand's concrete overflow guard, decided by the shared classifier
    /// (translation-ref §10.7c). A rescue (`forall_dep`) forces the atom true at
    /// positive polarity (`∨ of`), an exclusion false (`∧ ¬of`); negative polarity
    /// swaps them; a jar-unpinned corner defers. Inert when the overflow did not
    /// fire.
    fn apply_int_guard(
        &mut self,
        atom: bool,
        of: bool,
        operand: IntExprId,
    ) -> Result<bool, TranslateError> {
        use crate::overflow_guard::{classify, contains_int_ite, overflow_capable, GuardDecision};
        let capable = overflow_capable(self.ir, operand);
        let behind_conditional = self.behind_implies || contains_int_ite(self.ir, operand);
        let mut free = BTreeSet::new();
        self.collect_int_vars(operand, &mut free);
        match classify(&self.quant_frames, &free, capable, behind_conditional) {
            GuardDecision::Defer => Err(TranslateError::LoweringUnsupported {
                what: "forbid-mode overflow guard for this arithmetic comparison is not \
                       yet pinned in the jar (translation-ref §10.7c: Defect B nesting \
                       or the int-ITE/`implies` sliver)"
                    .to_owned(),
                span: self.ir.int_exprs[operand].span,
            }),
            GuardDecision::Guard { forall_dep } => {
                if !of {
                    return Ok(atom);
                }
                self.overflow = true; // diagnostic (self-check localization)
                Ok(if self.pol_positive == forall_dep {
                    atom || of
                } else {
                    atom && !of
                })
            }
        }
    }

    /// Collects the free variables of an integer expression (translation-ref
    /// §10.7c classification input). IR `VarId`s are unique per binding, so
    /// simply gathering every referenced `Var` equals the free set — an inner
    /// `sum`/comprehension binder is a distinct id, never in an enclosing frame.
    fn collect_int_vars(&self, id: IntExprId, out: &mut BTreeSet<VarId>) {
        match &self.ir.int_exprs[id].kind {
            IntExprKind::Const(_) => {}
            IntExprKind::Card(rel) | IntExprKind::AtomToInt(rel) => {
                self.collect_rel_vars(*rel, out);
            }
            IntExprKind::Neg(ie) => self.collect_int_vars(*ie, out),
            IntExprKind::Binary { lhs, rhs, .. } => {
                self.collect_int_vars(*lhs, out);
                self.collect_int_vars(*rhs, out);
            }
            IntExprKind::Sum { bound, body, .. } => {
                self.collect_rel_vars(*bound, out);
                self.collect_int_vars(*body, out);
            }
            IntExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.collect_formula_vars(*cond, out);
                self.collect_int_vars(*then_branch, out);
                self.collect_int_vars(*else_branch, out);
            }
        }
    }

    fn collect_rel_vars(&self, id: RelExprId, out: &mut BTreeSet<VarId>) {
        match &self.ir.rel_exprs[id].kind {
            RelExprKind::Relation(_) | RelExprKind::Const(_) => {}
            RelExprKind::Var(v) => {
                out.insert(*v);
            }
            RelExprKind::Binary { lhs, rhs, .. } => {
                self.collect_rel_vars(*lhs, out);
                self.collect_rel_vars(*rhs, out);
            }
            RelExprKind::Unary { expr, .. } | RelExprKind::Prime(expr) => {
                self.collect_rel_vars(*expr, out);
            }
            RelExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.collect_formula_vars(*cond, out);
                self.collect_rel_vars(*then_branch, out);
                self.collect_rel_vars(*else_branch, out);
            }
            RelExprKind::Comprehension { decls, body } => {
                for d in decls {
                    self.collect_rel_vars(d.bound, out);
                }
                self.collect_formula_vars(*body, out);
            }
            RelExprKind::IntToAtom(ie) => self.collect_int_vars(*ie, out),
        }
    }

    fn collect_formula_vars(&self, id: FormulaId, out: &mut BTreeSet<VarId>) {
        match &self.ir.formulas[id].kind {
            FormulaKind::Const(_) => {}
            FormulaKind::Not(f) => self.collect_formula_vars(*f, out),
            FormulaKind::And(parts) | FormulaKind::Or(parts) => {
                for &p in parts {
                    self.collect_formula_vars(p, out);
                }
            }
            FormulaKind::Implies {
                antecedent,
                consequent,
            } => {
                self.collect_formula_vars(*antecedent, out);
                self.collect_formula_vars(*consequent, out);
            }
            FormulaKind::Iff(l, r) => {
                self.collect_formula_vars(*l, out);
                self.collect_formula_vars(*r, out);
            }
            FormulaKind::RelCompare { lhs, rhs, .. } => {
                self.collect_rel_vars(*lhs, out);
                self.collect_rel_vars(*rhs, out);
            }
            FormulaKind::IntCompare { lhs, rhs, .. } => {
                self.collect_int_vars(*lhs, out);
                self.collect_int_vars(*rhs, out);
            }
            FormulaKind::MultTest { expr, .. } => self.collect_rel_vars(*expr, out),
            FormulaKind::Quant { bound, body, .. } => {
                self.collect_rel_vars(*bound, out);
                self.collect_formula_vars(*body, out);
            }
            FormulaKind::TemporalUnary { body, .. } => self.collect_formula_vars(*body, out),
            FormulaKind::TemporalBinary { lhs, rhs, .. } => {
                self.collect_formula_vars(*lhs, out);
                self.collect_formula_vars(*rhs, out);
            }
        }
    }

    /// `Int[ie]`: the unary set of `Int` atoms whose value equals `ie` — at most
    /// one, since Int-atom values are distinct (translation-ref §2.1).
    fn int_to_atom(&self, value: i64) -> TupleSet {
        let mut m = TupleSet::empty(1);
        for i in self.int_start..self.int_end {
            let atom = AtomId::from_index(i);
            if self.atom_int_value(atom) == Some(value) {
                m.insert(Tuple::new(vec![atom]));
            }
        }
        m
    }

    /// The integer value of an atom, if it is an `Int` atom (translation-ref
    /// §1.3: Int atoms are `-2^(bw-1) … 2^(bw-1)-1`, ascending, after sig atoms).
    fn atom_int_value(&self, atom: AtomId) -> Option<i64> {
        let idx = atom.index();
        if idx < self.int_start || idx >= self.int_end || self.bitwidth == 0 {
            return None;
        }
        let low = self.signed_min();
        let offset = i64::try_from(idx - self.int_start).unwrap_or(i64::MAX);
        Some(low + offset)
    }

    fn signed_min(&self) -> i64 {
        -(1i64 << (self.bitwidth - 1))
    }

    fn signed_max(&self) -> i64 {
        (1i64 << (self.bitwidth - 1)) - 1
    }

    /// Two's-complement wrap of `value` to the bitwidth, interpreted signed —
    /// the encoder's silent wrap when overflow is allowed (and the in-range
    /// identity otherwise).
    fn wrap_signed(&self, value: i64) -> i64 {
        let w = self.bitwidth;
        if w == 0 {
            return 0;
        }
        let modulus = 1i64 << w;
        let masked = value.rem_euclid(modulus);
        if masked >= (1i64 << (w - 1)) {
            masked - modulus
        } else {
            masked
        }
    }
}

// ============================ concrete set algebra ============================
// Free functions (no evaluator state): pure `TupleSet → TupleSet` operations,
// each matching one encoder gate family (translation-ref §2.1). Determinism is
// inherent — `TupleSet` iterates in lexicographic order (STYLE C2).

fn rel_binary(op: RelBinOp, a: &TupleSet, b: &TupleSet) -> TupleSet {
    match op {
        RelBinOp::Union => union(a, b),
        RelBinOp::Intersect => intersect(a, b),
        RelBinOp::Diff => diff(a, b),
        RelBinOp::Join => join(a, b),
        RelBinOp::Product => product(a, b),
        RelBinOp::Override => override_(a, b),
    }
}

fn union(a: &TupleSet, b: &TupleSet) -> TupleSet {
    debug_assert_eq!(a.arity(), b.arity(), "union arity mismatch");
    let mut out = TupleSet::empty(a.arity());
    for t in a.iter().chain(b.iter()) {
        out.insert(t.clone());
    }
    out
}

fn intersect(a: &TupleSet, b: &TupleSet) -> TupleSet {
    debug_assert_eq!(a.arity(), b.arity(), "intersect arity mismatch");
    let mut out = TupleSet::empty(a.arity());
    for t in a.iter() {
        if b.contains(t) {
            out.insert(t.clone());
        }
    }
    out
}

fn diff(a: &TupleSet, b: &TupleSet) -> TupleSet {
    debug_assert_eq!(a.arity(), b.arity(), "diff arity mismatch");
    let mut out = TupleSet::empty(a.arity());
    for t in a.iter() {
        if !b.contains(t) {
            out.insert(t.clone());
        }
    }
    out
}

fn product(a: &TupleSet, b: &TupleSet) -> TupleSet {
    let mut out = TupleSet::empty(a.arity() + b.arity());
    for ta in a.iter() {
        for tb in b.iter() {
            let mut atoms = ta.atoms().to_vec();
            atoms.extend_from_slice(tb.atoms());
            out.insert(Tuple::new(atoms));
        }
    }
    out
}

/// Relational join `a . b` over the shared middle atom (translation-ref §2.1).
fn join(a: &TupleSet, b: &TupleSet) -> TupleSet {
    let arity = a.arity() + b.arity() - 2;
    debug_assert!(arity >= 1, "join produces arity 0");
    let mut out = TupleSet::empty(arity);
    for ta in a.iter() {
        let mid = ta.atoms()[ta.arity() - 1];
        for tb in b.iter() {
            if tb.atoms()[0] != mid {
                continue;
            }
            let mut atoms = ta.atoms()[..ta.arity() - 1].to_vec();
            atoms.extend_from_slice(&tb.atoms()[1..]);
            out.insert(Tuple::new(atoms));
        }
    }
    out
}

/// Override `a ++ b` = `b ∪ { t ∈ a | t.first ∉ dom(b) }` (translation-ref §2.1).
fn override_(a: &TupleSet, b: &TupleSet) -> TupleSet {
    debug_assert_eq!(a.arity(), b.arity(), "override arity mismatch");
    let dom: BTreeSet<AtomId> = b.iter().map(|t| t.atoms()[0]).collect();
    let mut out = TupleSet::empty(a.arity());
    for t in a.iter() {
        if !dom.contains(&t.atoms()[0]) {
            out.insert(t.clone());
        }
    }
    for t in b.iter() {
        out.insert(t.clone());
    }
    out
}

/// Transpose of a binary set (translation-ref §2.1): reverse each tuple.
fn transpose(a: &TupleSet) -> TupleSet {
    debug_assert_eq!(a.arity(), 2, "transpose operand must be binary");
    let mut out = TupleSet::empty(2);
    for t in a.iter() {
        let atoms = t.atoms();
        out.insert(Tuple::new(vec![atoms[1], atoms[0]]));
    }
    out
}

/// Transitive closure `^r` by fixpoint (translation-ref §2.1): `s ← s ∪ (s . s)`
/// until it stops growing. Over a finite universe this terminates in `≤ log₂ n`
/// rounds and yields the full closure (the encoder's iterated squaring computes
/// the same set).
fn closure(r: &TupleSet) -> TupleSet {
    debug_assert_eq!(r.arity(), 2, "closure operand must be binary");
    let mut s = r.clone();
    loop {
        let sq = join(&s, &s);
        let grown = union(&s, &sq);
        if grown.len() == s.len() {
            return grown;
        }
        s = grown;
    }
}

// =============================== self-check net ===============================

/// A structured self-check failure: a solver-produced [`Instance`] does **not**
/// satisfy the command's own goal, localized to the first failing top-level
/// conjunct (translation-ref §2.5 provenance). This is always a mettle
/// solver/encoder bug — never a user error (ADR-0011 decision 5).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SelfCheckFailure {
    /// Index of the failing conjunct in [`LoweredGoal::conjuncts`].
    pub conjunct_index: usize,
    /// Where that conjunct came from (fact / field fact / command / …).
    pub provenance: Provenance,
    /// Why it failed.
    pub detail: SelfCheckDetail,
}

/// Why a conjunct failed its self-check.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SelfCheckDetail {
    /// The conjunct evaluated to `false` over the instance.
    ConjunctFalse,
    /// A forbidden integer overflow made the enclosing instance excluded
    /// (translation-ref §2.4) — yet the solver returned it: an inconsistency.
    Overflow,
    /// Evaluation hit a construct outside the evaluable slice — an internal
    /// inconsistency, since the encoder would have deferred the same construct
    /// before solving.
    EvalError(TranslateError),
}

impl std::fmt::Display for SelfCheckFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "instance fails its own goal at conjunct #{} ({:?}): ",
            self.conjunct_index, self.provenance
        )?;
        match &self.detail {
            SelfCheckDetail::ConjunctFalse => write!(f, "conjunct evaluated to false"),
            SelfCheckDetail::Overflow => {
                write!(f, "a forbidden integer overflow should have excluded it")
            }
            SelfCheckDetail::EvalError(e) => write!(f, "evaluation could not proceed: {e}"),
        }
    }
}

/// Re-evaluates a solved SAT `instance` against the command's **full goal**
/// (translation-ref §6). Returns `Ok(())` when the instance satisfies its own
/// formula, or a [`SelfCheckFailure`] localizing the first failing top-level
/// conjunct. This is the checked-mode entry the differential and corpus tests
/// call; [`crate::solve`] wires the same check as a `debug_assert!` on every SAT
/// verdict.
///
/// A failure is a mettle bug (encoder under-constraint or decode error), never a
/// user error — it is the tool built to localize exactly that class.
///
/// # Errors
/// A [`SelfCheckFailure`] when `instance` does not satisfy `goal` (the first
/// failing top-level conjunct, by [`Provenance`]) — or, defensively, when
/// evaluation hits a construct the encoder should have deferred before solving.
pub fn self_check(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    instance: &Instance,
    opts: &SolveOptions,
) -> Result<(), SelfCheckFailure> {
    let mut ev = Evaluator::new(ir, instance, scoped, opts, goal.int_sig, goal.seq_int_sig);
    match ev.accepts(goal.goal) {
        Ok(true) => Ok(()),
        // The goal is the conjunction of `goal.conjuncts`; a false/excluded goal
        // means some conjunct is false or overflows. Re-evaluate each in order to
        // name the first offender (its provenance is the localization).
        Ok(false) | Err(_) => Err(localize(&mut ev, goal)),
    }
}

/// Walks the conjuncts, returning the first that fails on its own.
fn localize(ev: &mut Evaluator<'_>, goal: &LoweredGoal) -> SelfCheckFailure {
    for (i, c) in goal.conjuncts.iter().enumerate() {
        match ev.accepts(c.formula) {
            Ok(true) => {}
            Ok(false) => {
                let detail = if ev.overflow {
                    SelfCheckDetail::Overflow
                } else {
                    SelfCheckDetail::ConjunctFalse
                };
                return SelfCheckFailure {
                    conjunct_index: i,
                    provenance: c.provenance.clone(),
                    detail,
                };
            }
            Err(e) => {
                return SelfCheckFailure {
                    conjunct_index: i,
                    provenance: c.provenance.clone(),
                    detail: SelfCheckDetail::EvalError(e),
                };
            }
        }
    }
    // The whole goal failed but every conjunct passed in isolation — impossible
    // for a plain conjunction (STYLE I3), but reported rather than silently lost.
    SelfCheckFailure {
        conjunct_index: goal.conjuncts.len(),
        provenance: Provenance::Command,
        detail: SelfCheckDetail::ConjunctFalse,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use als_syntax::ArenaId;

    fn atom(i: usize) -> AtomId {
        AtomId::from_index(i)
    }

    /// Builds a binary tuple set from `(a, b)` index pairs.
    fn bin(pairs: &[(usize, usize)]) -> TupleSet {
        let mut ts = TupleSet::empty(2);
        for &(a, b) in pairs {
            ts.insert(Tuple::new(vec![atom(a), atom(b)]));
        }
        ts
    }

    /// Unary tuple set from atom indices.
    fn un(atoms: &[usize]) -> TupleSet {
        let mut ts = TupleSet::empty(1);
        for &a in atoms {
            ts.insert(Tuple::new(vec![atom(a)]));
        }
        ts
    }

    #[test]
    fn set_ops_match_definitions() {
        let a = un(&[0, 1, 2]);
        let b = un(&[1, 2, 3]);
        assert_eq!(union(&a, &b), un(&[0, 1, 2, 3]));
        assert_eq!(intersect(&a, &b), un(&[1, 2]));
        assert_eq!(diff(&a, &b), un(&[0]));
    }

    #[test]
    fn join_over_middle_atom() {
        // {(0,1),(1,2)} . {(1,9),(2,8)} = {(0,9),(1,8)}.
        let r = bin(&[(0, 1), (1, 2)]);
        let s = bin(&[(1, 9), (2, 8)]);
        assert_eq!(join(&r, &s), bin(&[(0, 9), (1, 8)]));
    }

    #[test]
    fn transpose_reverses_pairs() {
        assert_eq!(transpose(&bin(&[(0, 1), (2, 3)])), bin(&[(1, 0), (3, 2)]));
    }

    #[test]
    fn product_concatenates() {
        let p = product(&un(&[0, 1]), &un(&[5]));
        assert_eq!(p, bin(&[(0, 5), (1, 5)]));
    }

    #[test]
    fn transitive_closure_reaches_all_paths() {
        // A chain 0->1->2->3: closure adds every longer reach.
        let chain = bin(&[(0, 1), (1, 2), (2, 3)]);
        let want = bin(&[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]);
        assert_eq!(closure(&chain), want);
    }

    #[test]
    fn closure_of_a_cycle_is_complete() {
        // 0->1->0 : closure = {(0,0),(0,1),(1,0),(1,1)}.
        let cyc = bin(&[(0, 1), (1, 0)]);
        assert_eq!(closure(&cyc), bin(&[(0, 0), (0, 1), (1, 0), (1, 1)]));
    }

    #[test]
    fn override_replaces_domain_rows() {
        // a = {(0,1),(2,3)}, b = {(0,9)} → keep (2,3), replace (0,*) with (0,9).
        let a = bin(&[(0, 1), (2, 3)]);
        let b = bin(&[(0, 9)]);
        assert_eq!(override_(&a, &b), bin(&[(0, 9), (2, 3)]));
    }
}
