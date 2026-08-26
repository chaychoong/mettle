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

use crate::bounds::{AtomId, Bounds, Tuple, TupleSet};
use crate::error::TranslateError;
use crate::freevars::FreeVars;
use crate::ir::{
    FormulaId, FormulaKind, IntCmpOp, IntExprId, IntExprKind, Ir, MultTest, QuantKind, RelBinOp,
    RelCmpOp, RelConst, RelExprId, RelExprKind, RelId, RelUnOp, VarId,
};
use crate::lower::{LoweredGoal, Provenance};
use crate::scope::ScopedUniverse;
use crate::solve::{Instance, SolveOptions};
use crate::trans_class::TransClassId;

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
    /// Relation bounds — read only by [`crate::overflow_guard::Fold`], the shared
    /// translation-time constant folder that decides which overflow guards the
    /// jar's matrix folding sheds, so the evaluator and the encoder shed from the
    /// SAME predicate (translation-ref §10.7e, mt-051/mt-130).
    bounds: &'a Bounds,
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
    /// Flipped by `Not` only — an `Implies` antecedent does NOT flip it
    /// (§10.7f, mt-090); drives the overflow-guard.
    pol_positive: bool,
    /// The enclosing-quantifier stack (innermost last), driving the §10.7c
    /// overflow classification — the same the encoder threads, so the two apply
    /// an identical guard and defer identically.
    quant_frames: Vec<crate::overflow_guard::QuantFrame>,
    /// The `Int`/`seq/Int` builtin relation ids, for recognizing a bare-`Int`
    /// quantifier domain (translation-ref §10.7c rule 0).
    int_sig: Option<RelId>,
    seq_int_sig: Option<RelId>,
    /// The solved lasso back-loop target, when re-evaluating a **temporal**
    /// goal (mt-067): [`FormulaKind::LoopIs`] holds exactly at this state. The
    /// encoder resolves that atom through the
    /// [`LassoSelector`](crate::temporal::LassoSelector) it minted; the loop
    /// index is a solver variable, not a relation, so a decoded
    /// [`Instance`] cannot carry it and the driver threads it here instead.
    /// `None` on every static path, where the atom cannot occur.
    loop_state: Option<usize>,
    /// The goal's **translation classes** (mt-137, ADR-0029), when this
    /// evaluator was pointed at a goal that has any. Empty otherwise, which is
    /// what keeps the memo below inert on every other path.
    trans_classes: BTreeMap<FormulaId, TransClassId>,
    /// Per-node free-variable sets. `Some` exactly when the memos below are
    /// armed ([`Self::with_trans_classes`]); they key on precisely the free
    /// variables the encoder's own key uses, so the two agree on which visits
    /// share an entry.
    freevars: Option<FreeVars>,
    /// First-visit-wins memo over `(class, free-var bindings)` — the evaluator's
    /// twin of the encoder's class cache, and the reason a jar-matching
    /// polarity-blind SAT instance still passes its own self-check.
    ///
    /// Cleared at the top of [`Self::accepts`]: the values are truths *about one
    /// instance*, so they must never outlive the instance being checked (the
    /// brute-force differential reuses one evaluator across instances).
    class_memo: BTreeMap<(TransClassId, EnvKey), bool>,
    /// First-visit-wins memo over `(node id, free-var bindings)` — the twin of
    /// the encoder's [`crate::encode`] `formula_cache`, which has keyed on the
    /// node and its free variables and NEVER on polarity since mt-049.
    ///
    /// Wherever lowering genuinely produces one formula node reached twice —
    /// the formula-`if`/`then`/`else` desugaring `(c ∧ t) ∨ (¬c ∧ e)` is the
    /// standing producer, since it lowers `c` once and negates that id — the
    /// encoder therefore hands the second reach the first visit's guard, and an
    /// unmemoised evaluator would judge the same node afresh at its own
    /// polarity and reject the instance the solver just produced. This is what
    /// makes the two agree; probe cell `g5_let_shared_ite` is the witness.
    id_memo: BTreeMap<(FormulaId, EnvKey), bool>,
}

/// A memo key's environment part: the bindings of exactly the memoised node's
/// **free variables**, in `VarId` order — the same shape (and the same meaning)
/// as the encoder's own key.
type EnvKey = Vec<(VarId, Tuple)>;

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
        bounds: &'a Bounds,
    ) -> Self {
        Self {
            ir,
            instance,
            bounds,
            bitwidth: scoped.bitwidth,
            int_start: scoped.sig_atom_count,
            int_end: scoped.sig_atom_count + scoped.int_atom_count,
            universe_len: instance.universe.len(),
            allow_overflow: opts.allow_overflow,
            env: BTreeMap::new(),
            overflow: false,
            pol_positive: true,
            quant_frames: Vec::new(),
            int_sig,
            seq_int_sig,
            loop_state: None,
            trans_classes: BTreeMap::new(),
            freevars: None,
            class_memo: BTreeMap::new(),
            id_memo: BTreeMap::new(),
        }
    }

    /// Arms this evaluator with the **encoder's sharing** for `goal`: its
    /// translation classes (mt-137, ADR-0029) and, underneath them, the same
    /// first-visit-wins memo on node identity the encoder has had since mt-049.
    ///
    /// Both matter for the same reason. The encoder reuses a shared translation
    /// *whatever polarity* the later reach is at, because the reference's
    /// `FOL2BoolCache` does (LEDGER-017); an evaluator that re-derives the node
    /// at its own polarity would then reject exactly the instances the solver
    /// produces, turning every jar-matching verdict into a self-check failure.
    /// Armed, both walk the same IR in the same order under the same `Not`-only
    /// polarity flip, so their first visits coincide by construction.
    ///
    /// Builder-style, like [`Self::with_loop_state`]: the free-variable analysis
    /// the keys need costs a pass over the arena, so a goal that can share
    /// nothing — no classes and no formula node reachable from two places — pays
    /// for none of it. Callers that evaluate *fragments* rather than a goal (the
    /// REPL, the instance writer) do not arm it: they have no goal, and the
    /// reference gives each evaluated expression a fresh translator anyway.
    #[must_use]
    pub fn with_trans_classes(mut self, goal: &LoweredGoal) -> Self {
        if !goal.trans_classes.is_empty() || has_shared_formula(self.ir) {
            self.freevars = Some(FreeVars::build(self.ir));
        }
        self.trans_classes = goal.trans_classes.clone();
        self
    }

    /// Points this evaluator at a solved **lasso trace**: `LoopIs(l)` then holds
    /// exactly when `l == loop_state` (mt-067).
    ///
    /// Builder-style rather than an extra [`Self::new`] argument: every static
    /// caller — the REPL, the differential, the corpus nets — would otherwise
    /// have to pass `None` for something that cannot occur on their path.
    #[must_use]
    pub fn with_loop_state(mut self, loop_state: usize) -> Self {
        self.loop_state = Some(loop_state);
        self
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
        // The memos hold truths about ONE instance, so they never outlive it:
        // the brute-force differential drives thousands of instances through a
        // single evaluator.
        self.class_memo.clear();
        self.id_memo.clear();
        self.accepts_sharing_classes(f)
    }

    /// [`Self::accepts`] **keeping** the memos already populated (mt-137).
    ///
    /// Only [`localize`] uses it, and only after the whole goal has been
    /// evaluated: re-checking the conjuncts one at a time must reuse the shared
    /// values the goal walk settled on, or the localization could disagree with
    /// the verdict it is explaining.
    fn accepts_sharing_classes(&mut self, f: FormulaId) -> Result<bool, TranslateError> {
        self.overflow = false;
        self.pol_positive = true;
        self.quant_frames.clear();
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
        if self.freevars.is_none() {
            return self.eval_formula_uncached(id);
        }
        let env = self.env_key(id);
        // A classed node is served from the CLASS memo only — the encoder skips
        // its per-id cache for exactly these nodes, so mirroring that keeps the
        // two walks reaching for the same entry at the same moment.
        if let Some(&class) = self.trans_classes.get(&id) {
            let key = (class, env);
            if let Some(&hit) = self.class_memo.get(&key) {
                return Ok(hit);
            }
            let v = self.eval_formula_uncached(id)?;
            self.class_memo.insert(key, v);
            return Ok(v);
        }
        let key = (id, env);
        if let Some(&hit) = self.id_memo.get(&key) {
            return Ok(hit);
        }
        let v = self.eval_formula_uncached(id)?;
        self.id_memo.insert(key, v);
        Ok(v)
    }

    /// A memo key's environment part: the bindings of exactly this node's free
    /// variables, in `VarId` order — the same key the encoder builds, so a visit
    /// the encoder shared is a visit this shares (mt-137).
    fn env_key(&self, id: FormulaId) -> EnvKey {
        let Some(fv) = &self.freevars else {
            return Vec::new();
        };
        fv.formula(id)
            .iter()
            .map(|v| {
                let t = self.env.get(v).cloned().unwrap_or_else(|| {
                    debug_assert!(false, "free var {v:?} unbound during evaluation");
                    Tuple::new(Vec::new())
                });
                (*v, t)
            })
            .collect()
    }

    fn eval_formula_uncached(&mut self, id: FormulaId) -> Result<bool, TranslateError> {
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
                // The antecedent keeps the implication's OWN polarity — the jar
                // never rewrites `a ⟹ c` to `¬a ∨ c` for guard purposes
                // (translation-ref §10.7f, mt-090). Mirrors the encoder exactly.
                let a = self.eval_formula(antecedent)?;
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
                let a = self.eval_rel(lhs)?;
                let b = self.eval_rel(rhs)?;
                let atom = match op {
                    RelCmpOp::Subset => a.is_subset_of(&b),
                    RelCmpOp::Equal => a == b,
                };
                // (B) comparison-level overflow guard over the compared sides' set
                // structure (translation-ref §10.7c ext, mt-051) — the matched
                // pair of the encoder's, so the two accept-sets coincide.
                self.guard_rel_compare(atom, lhs, rhs)
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
                Ok(self.int_compare_guard(atom, oa, ob, lhs, rhs))
            }
            FormulaKind::MultTest { test, expr } => {
                let (test, expr) = (*test, *expr);
                let m = self.eval_rel(expr)?;
                let atom = match test {
                    MultTest::No => m.is_empty(),
                    MultTest::Some => !m.is_empty(),
                    MultTest::Lone => m.len() <= 1,
                    MultTest::One => m.len() == 1,
                };
                // (B) guard also threads through a multiplicity test (probe T7),
                // subject to the reader's own short-circuit (R-c, mt-130).
                self.guard_mult_test(atom, test, expr)
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
            FormulaKind::LoopIs { state } => self.loop_is(*state, node.span),
        }
    }

    /// The lasso back-loop atom (mt-067): true exactly at the solved loop
    /// target.
    ///
    /// The loop index is a solver variable, not a relation, so a decoded
    /// [`Instance`] carries no value for it — the temporal driver threads the
    /// solved target in through [`Evaluator::with_loop_state`]. Without one the
    /// atom is unevaluable, which is a caller bug, reported rather than guessed
    /// at (STYLE E5).
    fn loop_is(&self, state: usize, span: als_syntax::Span) -> Result<bool, TranslateError> {
        match self.loop_state {
            Some(l) => Ok(state == l),
            None => Err(TranslateError::TemporalUnsupported {
                op: "the lasso loop atom has no instance-level value — evaluating a \
                     temporal goal needs `Evaluator::with_loop_state`",
                span,
            }),
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
                let ie = *ie;
                let (v, of) = self.eval_int(ie)?;
                // (A) Cast value semantics (translation-ref §10.7c ext, mt-051):
                // in forbid mode an overflowed overflow-capable cast denotes the
                // EMPTY set (jar's per-cell `∧ ¬of`), polarity-independent —
                // matching the encoder's `empty_on_overflow`.
                if !self.allow_overflow
                    && of
                    && crate::overflow_guard::overflow_capable(self.ir, self.bitwidth, ie)
                {
                    Ok(TupleSet::empty(1))
                } else {
                    Ok(self.int_to_atom(v))
                }
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
            IntExprKind::Const(v) => Ok((
                self.wrap_signed(i64::from(v)),
                // §10.7k: an out-of-range literal wraps on the value layer but
                // raises a constantly-TRUE overflow flag, exactly as the
                // encoder's twin arm does.
                crate::overflow_guard::const_overflows(v, self.bitwidth),
            )),
            IntExprKind::Card(rel) => {
                let m = self.eval_rel(rel)?;
                let c = i64::try_from(m.len()).unwrap_or(i64::MAX);
                let of = c > self.signed_max();
                let merged = self.merge_card_overflow(of, rel)?;
                Ok((self.wrap_signed(c), merged))
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
    /// (translation-ref §11.2, jar-verified §10.7b). The arithmetic itself lives
    /// in [`crate::overflow_guard`], shared with the translation-time constant
    /// folder so the two can never disagree about what overflows.
    fn int_binop_value(&self, op: crate::ir::IntBinOp, a: i64, b: i64) -> (i64, bool) {
        crate::overflow_guard::int_binop_value(op, a, b, self.bitwidth)
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

    /// Applies the forbid-mode overflow guard to an integer comparison via the
    /// shared [`crate::overflow_guard`] classifier (translation-ref §10.7c),
    /// matching the encoder's `int_compare` so the two accept-sets coincide. Allow
    /// mode passes the raw comparison; no comparison defers (§10.7c rules 0–3 are
    /// the whole classifier — rule 4 is retracted, §10.7f/mt-090).
    fn int_compare_guard(
        &mut self,
        atom: bool,
        oa: bool,
        ob: bool,
        lhs: IntExprId,
        rhs: IntExprId,
    ) -> bool {
        if self.allow_overflow {
            return atom;
        }
        let g = self.apply_int_guard(atom, oa, lhs);
        self.apply_int_guard(g, ob, rhs)
    }

    /// The translation-time constant folder over the CURRENT grounding bindings
    /// — built from the same inputs as the encoder's, so the two back ends shed
    /// the same guards by construction (translation-ref §10.7e, mt-130).
    fn fold(&self) -> crate::overflow_guard::Fold<'_> {
        crate::overflow_guard::Fold::new(
            self.ir,
            self.bounds,
            self.bitwidth,
            self.int_start,
            self.int_end,
            &self.env,
        )
    }

    /// Collects the surviving overflow-capable casts of a relational comparison's
    /// sides (lhs-then-rhs order) and applies the (B) guard; allow mode passes the
    /// atom through unchanged (translation-ref §10.7c ext, mt-051/mt-130).
    fn guard_rel_compare(
        &mut self,
        atom: bool,
        lhs: RelExprId,
        rhs: RelExprId,
    ) -> Result<bool, TranslateError> {
        if self.allow_overflow {
            return Ok(atom);
        }
        let mut casts = Vec::new();
        {
            let fold = self.fold();
            crate::overflow_guard::collect_capable_casts(&fold, lhs, &mut casts);
            crate::overflow_guard::collect_capable_casts(&fold, rhs, &mut casts);
        }
        self.guard_rel_casts(atom, &casts)
    }

    /// The same for a multiplicity test, applying the reader short-circuit (R-c).
    fn guard_mult_test(
        &mut self,
        atom: bool,
        test: crate::ir::MultTest,
        expr: RelExprId,
    ) -> Result<bool, TranslateError> {
        if self.allow_overflow {
            return Ok(atom);
        }
        let mut casts = Vec::new();
        {
            let fold = self.fold();
            crate::overflow_guard::collect_mult_test_casts(&fold, test, expr, &mut casts);
        }
        self.guard_rel_casts(atom, &casts)
    }

    /// Applies the (B) comparison-level guard for each surviving overflow-capable
    /// cast operand (translation-ref §10.7c ext, mt-051), in the given order,
    /// matching the encoder's `guard_rel_casts`. Forbid mode only.
    fn guard_rel_casts(&mut self, atom: bool, casts: &[IntExprId]) -> Result<bool, TranslateError> {
        let mut guarded = atom;
        for &ie in casts {
            let (_v, of) = self.eval_int(ie)?;
            guarded = self.apply_int_guard(guarded, of, ie);
        }
        Ok(guarded)
    }

    /// `#e` merges the operand matrix's overflow circuit (§10.7g/M4), the twin of
    /// the encoder's `merge_card_overflow`. Forbid mode only.
    fn merge_card_overflow(&mut self, of: bool, rel: RelExprId) -> Result<bool, TranslateError> {
        if self.allow_overflow {
            return Ok(of);
        }
        let mut casts = Vec::new();
        {
            let fold = self.fold();
            crate::overflow_guard::collect_capable_casts(&fold, rel, &mut casts);
        }
        let mut merged = of;
        for ie in casts {
            let (_v, cast_of) = self.eval_int(ie)?;
            merged = merged || cast_of;
        }
        Ok(merged)
    }

    /// One operand's concrete overflow guard, decided by the shared classifier
    /// (translation-ref §10.7c). A rescue (`forall_dep`) forces the atom true at
    /// positive polarity (`∨ of`), an exclusion false (`∧ ¬of`); negative polarity
    /// swaps them. Inert when the overflow did not fire.
    fn apply_int_guard(&mut self, atom: bool, of: bool, operand: IntExprId) -> bool {
        let mut free = BTreeSet::new();
        self.collect_int_vars(operand, &mut free);
        let forall_dep = crate::overflow_guard::classify(&self.quant_frames, &free);
        if !of {
            return atom;
        }
        self.overflow = true; // diagnostic (self-check localization)
        if self.pol_positive == forall_dep {
            atom || of
        } else {
            atom && !of
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
            // A constant and the lasso loop atom are both closed (mt-066).
            FormulaKind::Const(_) | FormulaKind::LoopIs { .. } => {}
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
        crate::overflow_guard::atom_int_value(atom, self.int_start, self.int_end, self.bitwidth)
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
        crate::overflow_guard::wrap_signed(value, self.bitwidth)
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

/// Whether any formula node in `ir` is referenced from more than one place — the
/// precondition for the encoder's per-id memo to hand one reach the translation
/// another reach minted, at the other polarity.
///
/// mettle's lowerer re-walks pred/fun bodies and formula-`let` right-hand sides
/// into fresh nodes, so most goals share no formula node at all and can skip the
/// free-variable analysis entirely. The formula-`if`/`then`/`else` desugaring is
/// the standing exception: it lowers the condition once and puts that same id
/// under a `Not`.
///
/// A flat scan of the three arenas, not a reachability walk from the goal: it is
/// linear, allocation-free past one counter vector, and being conservative
/// (counting references from nodes this goal never reaches) can only arm a memo
/// that would have been correct anyway.
fn has_shared_formula(ir: &Ir) -> bool {
    let mut refs = vec![0u8; ir.formulas.len()];
    let mut shared = false;
    let mut bump = |id: FormulaId, shared: &mut bool| {
        let slot = &mut refs[id.index()];
        if *slot == 0 {
            *slot = 1;
        } else {
            *shared = true;
        }
    };
    for (_, f) in ir.formulas.iter() {
        match &f.kind {
            FormulaKind::Const(_)
            | FormulaKind::LoopIs { .. }
            | FormulaKind::RelCompare { .. }
            | FormulaKind::IntCompare { .. }
            | FormulaKind::MultTest { .. } => {}
            FormulaKind::Not(x)
            | FormulaKind::TemporalUnary { body: x, .. }
            | FormulaKind::Quant { body: x, .. } => bump(*x, &mut shared),
            FormulaKind::And(xs) | FormulaKind::Or(xs) => {
                for &x in xs {
                    bump(x, &mut shared);
                }
            }
            FormulaKind::Implies {
                antecedent,
                consequent,
            } => {
                bump(*antecedent, &mut shared);
                bump(*consequent, &mut shared);
            }
            FormulaKind::Iff(l, r) | FormulaKind::TemporalBinary { lhs: l, rhs: r, .. } => {
                bump(*l, &mut shared);
                bump(*r, &mut shared);
            }
        }
        if shared {
            return true;
        }
    }
    for (_, e) in ir.rel_exprs.iter() {
        match &e.kind {
            RelExprKind::IfThenElse { cond, .. } => bump(*cond, &mut shared),
            RelExprKind::Comprehension { body, .. } => bump(*body, &mut shared),
            RelExprKind::Relation(_)
            | RelExprKind::Var(_)
            | RelExprKind::Const(_)
            | RelExprKind::Binary { .. }
            | RelExprKind::Unary { .. }
            | RelExprKind::Prime(_)
            | RelExprKind::IntToAtom(_) => {}
        }
        if shared {
            return true;
        }
    }
    for (_, e) in ir.int_exprs.iter() {
        if let IntExprKind::IfThenElse { cond, .. } = &e.kind {
            bump(*cond, &mut shared);
        }
        if shared {
            return true;
        }
    }
    false
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
    bounds: &Bounds,
) -> Result<(), SelfCheckFailure> {
    self_check_inner(ir, scoped, goal, instance, opts, bounds, None)
}

/// The **temporal** self-check (mt-067): the same re-evaluation, over the
/// unrolled goal (whose relations are the per-state copies) with the solved
/// lasso back-loop target supplied, so [`crate::ir::FormulaKind::LoopIs`] has a
/// value. `instance` is the *flat* decoded instance — the per-state copies as
/// ordinary relations, exactly what the encoder saw — not the per-state trace
/// view the driver renders.
///
/// # Errors
/// As [`self_check`].
pub fn self_check_temporal(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    instance: &Instance,
    opts: &SolveOptions,
    bounds: &Bounds,
    loop_state: usize,
) -> Result<(), SelfCheckFailure> {
    self_check_inner(ir, scoped, goal, instance, opts, bounds, Some(loop_state))
}

#[allow(
    clippy::too_many_arguments,
    reason = "the two public entries' shared body: the evaluator's whole context \
              plus the optional lasso loop target"
)]
fn self_check_inner(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    instance: &Instance,
    opts: &SolveOptions,
    bounds: &Bounds,
    loop_state: Option<usize>,
) -> Result<(), SelfCheckFailure> {
    let mut ev = Evaluator::new(
        ir,
        instance,
        scoped,
        opts,
        goal.int_sig,
        goal.seq_int_sig,
        bounds,
    )
    .with_trans_classes(goal);
    if let Some(l) = loop_state {
        ev = ev.with_loop_state(l);
    }
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
        match ev.accepts_sharing_classes(c.formula) {
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
