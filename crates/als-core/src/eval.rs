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
pub struct Evaluator<'a> {
    ir: &'a Ir,
    instance: &'a Instance,
    /// Int atoms span `-2^(bw-1) … 2^(bw-1)-1`; `int_start` is the universe index
    /// of the first Int atom (sig atoms precede them).
    bitwidth: u32,
    int_start: usize,
    universe_len: usize,
    allow_overflow: bool,
    env: BTreeMap<VarId, Tuple>,
    /// Set when a forbidden overflow was observed during the current evaluation.
    overflow: bool,
}

impl<'a> Evaluator<'a> {
    /// Builds an evaluator for `instance` under the command's integer parameters.
    #[must_use]
    pub fn new(
        ir: &'a Ir,
        instance: &'a Instance,
        scoped: &ScopedUniverse,
        opts: &SolveOptions,
    ) -> Self {
        Self {
            ir,
            instance,
            bitwidth: scoped.bitwidth,
            int_start: scoped.sig_atom_count,
            universe_len: instance.universe.len(),
            allow_overflow: opts.allow_overflow,
            env: BTreeMap::new(),
            overflow: false,
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
        let v = self.eval_formula(f)?;
        Ok(v && (self.allow_overflow || !self.overflow))
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
            FormulaKind::Not(f) => Ok(!self.eval_formula(*f)?),
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
                let a = self.eval_formula(*antecedent)?;
                let c = self.eval_formula(*consequent)?;
                Ok(!a || c)
            }
            FormulaKind::Iff(l, r) => {
                let a = self.eval_formula(*l)?;
                let b = self.eval_formula(*r)?;
                Ok(a == b)
            }
            FormulaKind::RelCompare { op, lhs, rhs } => {
                let a = self.eval_rel(*lhs)?;
                let b = self.eval_rel(*rhs)?;
                Ok(match op {
                    RelCmpOp::Subset => a.is_subset_of(&b),
                    RelCmpOp::Equal => a == b,
                })
            }
            FormulaKind::IntCompare { op, lhs, rhs } => {
                let a = self.eval_int(*lhs)?;
                let b = self.eval_int(*rhs)?;
                Ok(match op {
                    IntCmpOp::Eq => a == b,
                    IntCmpOp::Lt => a < b,
                    IntCmpOp::Le => a <= b,
                    IntCmpOp::Gt => a > b,
                    IntCmpOp::Ge => a >= b,
                })
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
        let mut acc = matches!(kind, QuantKind::All);
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
            let body_v = body_v?;
            match kind {
                QuantKind::All => acc &= body_v,
                QuantKind::Some => acc |= body_v,
            }
        }
        Ok(acc)
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
                let v = self.eval_int(*ie)?;
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

    /// Evaluates an integer expression to a signed `i64` in the bitwidth range
    /// (the Rung-3 slice: `Const`, `#` cardinality, `int[·]`). Arithmetic /
    /// `sum` / integer-`ITE` are the same typed defer the encoder raises
    /// (translation-ref §2.4) — the evaluator and encoder handle exactly the same
    /// slice, so the differential compares like for like.
    ///
    /// # Errors
    /// [`TranslateError::LoweringUnsupported`] for integer arithmetic / `sum` /
    /// integer if-then-else (Rung 4).
    pub fn eval_int(&mut self, id: IntExprId) -> Result<i64, TranslateError> {
        let node = &self.ir.int_exprs[id];
        match &node.kind {
            IntExprKind::Const(v) => Ok(self.wrap_signed(i64::from(*v))),
            IntExprKind::Card(rel) => {
                let m = self.eval_rel(*rel)?;
                Ok(self.card_value(m.len()))
            }
            IntExprKind::AtomToInt(rel) => {
                let m = self.eval_rel(*rel)?;
                Ok(self.atom_to_int_value(&m))
            }
            IntExprKind::Neg(_)
            | IntExprKind::Binary { .. }
            | IntExprKind::Sum { .. }
            | IntExprKind::IfThenElse { .. } => Err(TranslateError::LoweringUnsupported {
                what: "integer arithmetic / `sum` / integer if-then-else (Rung 4; the \
                       Rung-3 slice — like the encoder — evaluates only cardinality, \
                       constants, and `int[·]`)"
                    .to_owned(),
                span: node.span,
            }),
        }
    }

    /// `#e`: the cell count normalised to a signed value at the bitwidth. Overflow
    /// (count above the signed max) matches the encoder's `unsigned_to_signed`
    /// flag; under forbid it excludes the instance.
    fn card_value(&mut self, count: usize) -> i64 {
        let c = i64::try_from(count).unwrap_or(i64::MAX);
        if c > self.signed_max() {
            self.overflow = true;
        }
        self.wrap_signed(c)
    }

    /// `int[e]`: the signed sum of the integer values of the `Int` atoms in `e`,
    /// accumulated in tuple order in two's complement, exactly as the encoder's
    /// `int_atom_to_int` chains `add_signed` — so an intermediate step leaving the
    /// signed range trips overflow even when the final value is in range.
    fn atom_to_int_value(&mut self, m: &TupleSet) -> i64 {
        let mut acc: i64 = 0;
        for t in m.iter() {
            if t.arity() != 1 {
                continue;
            }
            if let Some(v) = self.atom_int_value(t.atoms()[0]) {
                let exact = acc + v; // acc, v both in range ⇒ no i64 overflow
                if exact < self.signed_min() || exact > self.signed_max() {
                    self.overflow = true;
                }
                acc = self.wrap_signed(exact);
            }
        }
        acc
    }

    /// `Int[ie]`: the unary set of `Int` atoms whose value equals `ie` — at most
    /// one, since Int-atom values are distinct (translation-ref §2.1).
    fn int_to_atom(&self, value: i64) -> TupleSet {
        let mut m = TupleSet::empty(1);
        for i in self.int_start..self.universe_len {
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
        if idx < self.int_start || idx >= self.universe_len || self.bitwidth == 0 {
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
    let mut ev = Evaluator::new(ir, instance, scoped, opts);
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
