//! Bounds-driven relational-to-SAT translation (mt-033, translation-ref §4).
//!
//! The [`Encoder`] is a bottom-up walk over the three-sorted IR
//! ([`crate::ir`]): each [`RelExpr`](crate::ir::RelExpr) becomes a boolean
//! [`Matrix`], each [`Formula`](crate::ir::Formula) a [`Bool`], each
//! [`IntExpr`](crate::ir::IntExpr) an [`IntVal`] — the classic Kodkod-style
//! encoding (behaviour, not structure — PORTING prime directive). Relational
//! operators become boolean gates over cells; quantifiers **ground** over their
//! bound's candidate tuples; multiplicity/comparison predicates fold the cells.
//!
//! The variable layout is pinned by ADR-0011 decision 3: the driver
//! ([`crate::solve`]) mints every **primary** variable first, in `RelId` × tuple
//! lexicographic order, so all Tseitin auxiliaries this module mints sort after
//! them. Everything here is a fixed function of the input (STYLE D1/D2): matrices
//! iterate in `BTreeMap` key order, integer networks build in a fixed order.
//!
//! # What is encoded vs deferred (Rung-3 slice)
//! Full relational algebra, quantifiers, multiplicity tests, comprehensions,
//! `if`/`then`/`else`, and the measured integer slice (`Const`, `#` cardinality,
//! `int[·]`, `Int[·]`, integer comparison) are encoded. Integer **arithmetic**
//! (`plus`/`minus`/…), `sum`, and integer `if`/`then`/`else` are a **typed
//! defer** ([`TranslateError::LoweringUnsupported`]) — the corpus needs none of
//! them at Rung 3 (mt-033 measurement), and a defer is never a wrong verdict
//! (STYLE E5). A [`crate::ir::RelExprKind::Prime`] (temporal) must never reach
//! here — lowering defers temporal — so it is a typed internal error, not a
//! panic.

mod circuit;
mod int;
mod matrix;
pub(crate) mod symmetry;

use std::collections::BTreeMap;

use als_solve::{Cnf, Var};

use crate::bounds::{AtomId, Bounds, Tuple};
use crate::error::TranslateError;
use crate::ir::{
    FormulaId, FormulaKind, IntCmpOp, IntExprId, IntExprKind, Ir, MultTest, QuantKind, RelBinOp,
    RelCmpOp, RelConst, RelExprId, RelExprKind, RelId, RelUnOp, VarId,
};

use crate::freevars::FreeVars;
use circuit::Circuit;
use int::{IntBuilder, IntVal};
use matrix::Matrix;

pub(crate) use circuit::Bool;

use als_syntax::ArenaId;

/// The grounding-memo cache key's environment part (mt-049): the bindings of
/// exactly the memoised node's **free variables**, in `VarId` order. Two
/// different full environments that agree on a node's free variables share its
/// cache entry — the node's encoded value depends on nothing else. Ordered
/// (`Vec` in `VarId` order) so it is a deterministic `BTreeMap` key (STYLE D2).
type EnvKey = Vec<(VarId, Tuple)>;

/// The primary-variable map: `(relation, floating tuple) → SAT variable`.
///
/// Only tuples in `upper ∖ lower` get a variable; lower tuples are constant-true
/// and non-upper tuples constant-false (ADR-0011 decision 3). Keyed and iterated
/// in `RelId` × tuple order (deterministic, STYLE D2).
pub(crate) type PrimaryMap = BTreeMap<(RelId, Tuple), Var>;

/// The relational-to-SAT encoder for one command.
///
/// Borrows the lowered [`Ir`], the [`Bounds`], and the primary-variable map; owns
/// the growing [`Cnf`] and the grounding environment.
///
/// Produced matrices/bools/int-values are memoised by `(node id, the bindings of
/// exactly that node's free variables)` (mt-049 env-cached grounding): a
/// sub-expression that does not mention the innermost bound variable is encoded
/// once and shared across every binding of it, instead of being re-grounded per
/// binding — the shared gates are identical, so the SB-0 model set over primary
/// variables is unchanged. A node whose free variables are the *whole* active
/// environment is not cached (its key would be distinct per binding — no reuse,
/// only overhead); [`FreeVars`] drives the decision.
pub(crate) struct Encoder<'a> {
    ir: &'a Ir,
    bounds: &'a Bounds,
    prim: &'a PrimaryMap,
    /// Precomputed per-node free-variable sets (mt-049), driving the memo keys.
    freevars: FreeVars,
    cnf: Cnf,
    /// Bitwidth for the integer slice (Int atoms `-2^(bw-1) … 2^(bw-1)-1`).
    bitwidth: u32,
    /// Universe index of the first integer atom (sig atoms precede them).
    int_start: usize,
    /// Universe index just past the last integer atom (`int_start + 2^bw`).
    /// String atoms (mt-045) trail the integer atoms, so the int-atom span ends
    /// here, **not** at `universe_len` — an atom in `[int_end, universe_len)` is
    /// a string atom, never an integer.
    int_end: usize,
    /// Total universe size (to bound closure iteration and index atoms).
    universe_len: usize,
    /// LEDGER-001 overflow switch: `false` (default) forbids, `true` wraps.
    allow_overflow: bool,
    /// Resource guard ([`crate::SolveOptions::encode_budget`]): encoding fails
    /// with [`TranslateError::CapacityExceeded`] once the spent effort — gate
    /// requests (folded or not, via [`Circuit`]), join pair-scans, and CNF
    /// clauses — outgrows this budget, instead of grounding until the machine
    /// runs out of memory (or time: constant-heavy matrices fold every gate
    /// away, so a clause count alone never trips while the walk still burns
    /// hours). `None` = unlimited. Checked in the memoising node wrappers,
    /// which every grounding re-visit passes through, so spend between checks
    /// is bounded by one node's own work.
    encode_budget: Option<u64>,
    /// Effort spent so far (see [`Encoder::encode_budget`]); grows only.
    ops: u64,
    /// Active grounding bindings: quantifier/comprehension var → its atom tuple.
    env: BTreeMap<VarId, Tuple>,
    /// Current formula polarity (translation-ref §11.3): `true` = positive (an
    /// even number of enclosing negations). Flipped by `Not` and an `Implies`
    /// antecedent; drives the forbid-mode overflow-guard direction.
    pol_positive: bool,
    /// The enclosing-quantifier stack (innermost last), driving the §10.7c
    /// overflow classification. Each frame records the binder's effective kind
    /// and whether its domain is bare `Int`/`seq/Int`.
    quant_frames: Vec<crate::overflow_guard::QuantFrame>,
    /// Whether the current node is under an `Implies` antecedent — the rule-6
    /// defer precondition (translation-ref §10.7c).
    behind_implies: bool,
    /// The `Int`/`seq/Int` builtin relation ids (from the bounds builder), for
    /// recognizing a bare-`Int` quantifier domain.
    int_sig: Option<RelId>,
    seq_int_sig: Option<RelId>,
    // Env-cached grounding memo (mt-049): keyed by `(node id, free-var bindings)`.
    // `BTreeMap` (STYLE D2): keys are ordered, iteration never escapes.
    matrix_cache: BTreeMap<(RelExprId, EnvKey), Matrix>,
    formula_cache: BTreeMap<(FormulaId, EnvKey), Bool>,
    /// Integer values carry their accumulated overflow flag (translation-ref
    /// §11.3): consumed at comparisons by the polarity guard, dropped at `Int[·]`.
    int_cache: BTreeMap<(IntExprId, EnvKey), (IntVal, Bool)>,
}

impl<'a> Encoder<'a> {
    /// Creates an encoder over a freshly-minted (primary-variables-installed)
    /// CNF pool. `opts` carries the LEDGER-001 overflow switch and the encode
    /// budget; the solver-side knobs it also holds are not read here.
    #[allow(
        clippy::too_many_arguments,
        reason = "the encoder threads the whole translation context (bounds, primaries, \
                  bitwidth, universe seam, overflow builtins) — a bundle struct would only \
                  move the arguments, not reduce them"
    )]
    pub(crate) fn new(
        ir: &'a Ir,
        bounds: &'a Bounds,
        prim: &'a PrimaryMap,
        cnf: Cnf,
        bitwidth: u32,
        int_start: usize,
        opts: crate::solve::SolveOptions,
        int_sig: Option<RelId>,
        seq_int_sig: Option<RelId>,
    ) -> Self {
        let universe_len = bounds.universe.len();
        let int_end = int_start + if bitwidth >= 1 { 1usize << bitwidth } else { 0 };
        let freevars = FreeVars::build(ir);
        Self {
            ir,
            bounds,
            prim,
            freevars,
            cnf,
            bitwidth,
            int_start,
            int_end,
            universe_len,
            allow_overflow: opts.allow_overflow,
            encode_budget: opts.encode_budget,
            ops: 0,
            env: BTreeMap::new(),
            pol_positive: true,
            quant_frames: Vec::new(),
            behind_implies: false,
            int_sig,
            seq_int_sig,
            matrix_cache: BTreeMap::new(),
            formula_cache: BTreeMap::new(),
            int_cache: BTreeMap::new(),
        }
    }

    /// Encodes the goal formula and returns the top-level [`Bool`] plus the
    /// finished CNF. The driver asserts the `Bool` true.
    ///
    /// Forbid-mode overflow is **not** a flat top-level `∧ ¬overflow`: each `Int`
    /// carries its accumulated overflow, guarded at the comparison where it
    /// becomes a formula by the Milicevic/Jackson polarity rule (translation-ref
    /// §11.3, [`Encoder::int_compare`]). So the goal formula already embeds every
    /// guard; nothing is conjoined here.
    ///
    /// **Symmetry breaking (translation-ref §16.1).** When `sbp` is `Some` (a
    /// non-zero [`crate::SolveOptions::symmetry`]) and the goal circuit did **not**
    /// fold to a constant, the lex-leader predicate is generated and conjoined with
    /// the goal (§16.1.5: the jar skips the SBP entirely on a trivial circuit,
    /// returning the constant before conjoining). The SBP adds only Tseitin
    /// auxiliaries, so the primary-variable set is unchanged.
    pub(crate) fn finish_goal(
        mut self,
        goal: FormulaId,
        sbp: Option<&symmetry::SbpPlan>,
        symmetry: u32,
    ) -> Result<(Bool, Cnf), TranslateError> {
        let span = self.ir.formulas[goal].span;
        let g = self.formula(goal)?;
        // §16.1.5: a goal that folded to a constant TRUE/FALSE gets no SBP.
        let g = match (g, sbp) {
            (Bool::Lit(_), Some(plan)) if !plan.is_trivial() && symmetry > 0 => {
                let s = self.generate_sbp(plan, symmetry, span)?;
                self.circ().and(g, s)
            }
            _ => g,
        };
        Ok((g, self.cnf))
    }

    /// Generates the lex-leader symmetry-breaking predicate for `plan`
    /// (translation-ref §16.3, a bit-exact port of `SymmetryBreaker.generateSBP`).
    ///
    /// For each class and each adjacent ascending atom pair `(prev, cur)`, two
    /// parallel `original`/`permuted` boolean lists are built by walking the
    /// `relparts` relations (in `(arity, name)` order) and, per relation, its upper
    /// tuples in ascending lexicographic order: the `original` entry is the tuple's
    /// matrix cell, the `permuted` entry the cell of the tuple with `prev`/`cur`
    /// swapped. Identity tuples (`t' == t`) and mirror duplicates (an earlier
    /// `(original[i], permuted[i]) == (permValue, entryValue)`) are skipped; the
    /// list is capped at `cap` entries — checked at each relation boundary, exactly
    /// as the jar's `original.size() < predLength` loop guard. Each pair's list is
    /// closed with a `lex-leq` circuit, and all are conjoined.
    fn generate_sbp(
        &mut self,
        plan: &symmetry::SbpPlan,
        cap: u32,
        span: als_syntax::Span,
    ) -> Result<Bool, TranslateError> {
        let cap = cap as usize;
        let mut clauses: Vec<Bool> = Vec::new();
        for class in plan.classes() {
            if class.len() < 2 {
                continue;
            }
            for pair in class.windows(2) {
                let (prev, cur) = (pair[0], pair[1]);
                let mut original: Vec<Bool> = Vec::new();
                let mut permuted: Vec<Bool> = Vec::new();
                for &rel in plan.relparts() {
                    if original.len() >= cap {
                        break;
                    }
                    if !self.rel_touches_class(rel, class) {
                        continue;
                    }
                    self.sbp_relation(rel, prev, cur, &mut original, &mut permuted);
                }
                // Charge the pair's circuit against the encode budget, then close
                // it with the lex-leq comparator.
                self.check_capacity(span)?;
                let leq = self.lex_leq(&original, &permuted);
                clauses.push(leq);
            }
        }
        Ok(self.circ().and_many(clauses))
    }

    /// Whether relation `rel`'s upper bound touches `class` — some atom of some
    /// upper tuple lands in the class (the jar's `representatives.contains(
    /// sym.min())`, translation-ref §16.3).
    fn rel_touches_class(&self, rel: RelId, class: &[AtomId]) -> bool {
        let Some(bound) = self.bounds.get(rel) else {
            return false;
        };
        let class_set: std::collections::BTreeSet<AtomId> = class.iter().copied().collect();
        bound
            .upper()
            .iter()
            .any(|t| t.atoms().iter().any(|a| class_set.contains(a)))
    }

    /// Appends one relation's SBP entries for the `(prev, cur)` swap
    /// (translation-ref §16.3). Iterates the relation's upper tuples in ascending
    /// lexicographic order; for each, the `original` value is the tuple's cell and
    /// the `permuted` value the swapped tuple's cell (`FALSE` when outside upper),
    /// with the identity and mirror-duplicate skips applied.
    fn sbp_relation(
        &self,
        rel: RelId,
        prev: AtomId,
        cur: AtomId,
        original: &mut Vec<Bool>,
        permuted: &mut Vec<Bool>,
    ) {
        let Some(bound) = self.bounds.get(rel) else {
            return;
        };
        for t in bound.upper().iter() {
            let e = self.sbp_cell(rel, bound, t);
            let swapped = swap_tuple(t, prev, cur);
            if swapped == *t {
                continue;
            }
            let p = self.sbp_cell(rel, bound, &swapped);
            // Mirror filter (jar `atSameIndex`): skip when some earlier accepted
            // pair equals `(permValue, entryValue)` = `(p, e)`.
            if original
                .iter()
                .zip(permuted.iter())
                .any(|(&o, &pm)| o == p && pm == e)
            {
                continue;
            }
            original.push(e);
            permuted.push(p);
        }
    }

    /// The boolean matrix cell of `tuple` for `rel` (translation-ref §16.3): `TRUE`
    /// for a lower-bound tuple, its primary variable for a floating upper tuple, and
    /// `FALSE` for a tuple outside the upper bound.
    fn sbp_cell(&self, rel: RelId, bound: &crate::bounds::RelBound, tuple: &Tuple) -> Bool {
        if bound.lower().contains(tuple) {
            Bool::TRUE
        } else if let Some(&var) = self.prim.get(&(rel, tuple.clone())) {
            Bool::var(var)
        } else {
            Bool::FALSE
        }
    }

    /// The `lex-leq` circuit (translation-ref §16.3, SymmetryBreaker.java:350):
    /// `⋀_i (prevEq_{i−1} → (orig_i → perm_i))` with `prevEq_i = prevEq_{i−1} ∧
    /// (orig_i ↔ perm_i)`, `prevEq_{−1} = TRUE`.
    fn lex_leq(&mut self, original: &[Bool], permuted: &[Bool]) -> Bool {
        let mut cmp: Vec<Bool> = Vec::with_capacity(original.len());
        let mut prev_eq = Bool::TRUE;
        for (&o, &p) in original.iter().zip(permuted.iter()) {
            let imp = self.circ().implies(o, p);
            let clause = self.circ().implies(prev_eq, imp);
            cmp.push(clause);
            let eq = self.circ().iff(o, p);
            prev_eq = self.circ().and(prev_eq, eq);
        }
        self.circ().and_many(cmp)
    }

    // ------------------------------------------------------------------ gates

    /// A transient gate builder over the CNF (constructed per call; effort is
    /// metered into [`Encoder::ops`]).
    fn circ(&mut self) -> Circuit<'_> {
        Circuit::new(&mut self.cnf, &mut self.ops)
    }

    /// The encode-budget resource guard (see the [`Encoder::encode_budget`]
    /// field): fails the encode once the spent effort outgrows the budget.
    /// `span` locates the node being encoded when the budget ran out (for the
    /// caret render).
    fn check_capacity(&self, span: als_syntax::Span) -> Result<(), TranslateError> {
        match self.encode_budget {
            Some(cap) if self.ops + self.cnf.clauses().len() as u64 > cap => {
                Err(TranslateError::CapacityExceeded { cap, span })
            }
            _ => Ok(()),
        }
    }

    // ------------------------------------------------------------- relations

    /// The memo key for a node given its free-variable set, or `None` when the
    /// node should not be cached (mt-049).
    ///
    /// A node is cacheable when its free variables are a **strict subset** of the
    /// active environment (so the same encoded value is reused across the bindings
    /// it does not depend on), or when the environment is empty (top level). When
    /// its free variables *are* the whole environment, every binding yields a
    /// distinct key — caching would only cost memory — so we skip it. `free` is
    /// always a subset of the active bindings (all free vars are in scope at
    /// encode time), so the strict-subset test reduces to a length comparison.
    fn env_key(&self, free: &std::collections::BTreeSet<VarId>) -> Option<EnvKey> {
        if self.env.is_empty() {
            return Some(Vec::new());
        }
        if free.len() >= self.env.len() {
            return None;
        }
        Some(
            free.iter()
                .map(|v| {
                    let t = self.env.get(v).cloned().unwrap_or_else(|| {
                        debug_assert!(false, "free var {v:?} unbound during encode");
                        Tuple::new(Vec::new())
                    });
                    (*v, t)
                })
                .collect(),
        )
    }

    /// Encodes a relation expression to its boolean matrix.
    fn rel(&mut self, id: RelExprId) -> Result<Matrix, TranslateError> {
        let key = self.env_key(self.freevars.rel(id)).map(|e| (id, e));
        if let Some(k) = &key {
            if let Some(m) = self.matrix_cache.get(k) {
                return Ok(m.clone());
            }
        }
        self.check_capacity(self.ir.rel_exprs[id].span)?;
        let m = self.rel_uncached(id)?;
        if let Some(k) = key {
            self.matrix_cache.insert(k, m.clone());
        }
        Ok(m)
    }

    fn rel_uncached(&mut self, id: RelExprId) -> Result<Matrix, TranslateError> {
        let node = &self.ir.rel_exprs[id];
        match &node.kind {
            RelExprKind::Relation(rel) => Ok(self.relation_matrix(*rel)),
            RelExprKind::Var(v) => Ok(self.var_matrix(*v)),
            RelExprKind::Const(c) => Ok(self.const_matrix(*c)),
            RelExprKind::Binary { op, lhs, rhs } => {
                let a = self.rel(*lhs)?;
                let b = self.rel(*rhs)?;
                Ok(self.rel_binary(*op, &a, &b))
            }
            RelExprKind::Unary { op, expr } => {
                let a = self.rel(*expr)?;
                Ok(self.rel_unary(*op, &a))
            }
            RelExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                let c = self.formula(*cond)?;
                let t = self.rel(*then_branch)?;
                let e = self.rel(*else_branch)?;
                Ok(self.rel_ite(c, &t, &e))
            }
            RelExprKind::Comprehension { decls, body } => {
                let decls = decls.clone();
                let body = *body;
                self.comprehension(&decls, body)
            }
            RelExprKind::IntToAtom(ie) => {
                let ie = *ie;
                let (v, of) = self.int(ie)?;
                let m = self.int_to_atom(&v);
                // (A) Cast value semantics (translation-ref §10.7c ext, mt-051):
                // the jar builds every `IntToExprCast` cell with `Int.eq(other,
                // empty)` (`∧ ¬accumOverflow`), so in forbid mode an overflowed
                // overflow-capable cast denotes the EMPTY set — polarity-
                // independent, in every context. Allow mode keeps the wrapped
                // atom; a non-capable cast (`Int[3]`) carries a constant-false
                // flag, so the gate folds away.
                if !self.allow_overflow && crate::overflow_guard::overflow_capable(self.ir, ie) {
                    Ok(self.empty_on_overflow(&m, of))
                } else {
                    Ok(m)
                }
            }
            RelExprKind::Prime(_) => Err(TranslateError::LoweringUnsupported {
                what: "temporal prime (`'`) reached the encoder — a lowering invariant \
                       failure; temporal solving is Rung 6"
                    .to_owned(),
                span: node.span,
            }),
        }
    }

    /// The base matrix of a free relation: lower tuples constant-true, other
    /// upper tuples their primary literal (ADR-0011 decision 3).
    fn relation_matrix(&self, rel: RelId) -> Matrix {
        let Some(bound) = self.bounds.get(rel) else {
            // Every allocated relation is bound by the bounds builder.
            debug_assert!(false, "unbounded relation {rel:?} in the goal");
            return Matrix::empty(1);
        };
        let mut m = Matrix::empty(bound.upper().arity());
        for t in bound.upper().iter() {
            let cell = if bound.lower().contains(t) {
                Bool::TRUE
            } else if let Some(&var) = self.prim.get(&(rel, t.clone())) {
                Bool::var(var)
            } else {
                // A floating tuple always has a primary variable (STYLE I1).
                unreachable!("floating tuple {t:?} of {rel:?} has no primary variable");
            };
            m.set(t.clone(), cell);
        }
        m
    }

    /// A bound variable's matrix: the single atom-tuple it is currently bound to.
    fn var_matrix(&self, v: VarId) -> Matrix {
        let arity = self.ir.vars[v].arity;
        let mut m = Matrix::empty(arity);
        if let Some(t) = self.env.get(&v) {
            m.set(t.clone(), Bool::TRUE);
        } else {
            debug_assert!(false, "unbound IR variable {v:?} in the goal");
        }
        m
    }

    /// A relational constant (`none`/`univ`/`iden`) over the universe.
    fn const_matrix(&self, c: RelConst) -> Matrix {
        match c {
            RelConst::None => Matrix::empty(1),
            RelConst::Univ => {
                let mut m = Matrix::empty(1);
                for i in 0..self.universe_len {
                    m.set(Tuple::new(vec![AtomId::from_index(i)]), Bool::TRUE);
                }
                m
            }
            RelConst::Iden => {
                let mut m = Matrix::empty(2);
                for i in 0..self.universe_len {
                    let a = AtomId::from_index(i);
                    m.set(Tuple::new(vec![a, a]), Bool::TRUE);
                }
                m
            }
        }
    }

    fn rel_binary(&mut self, op: RelBinOp, a: &Matrix, b: &Matrix) -> Matrix {
        match op {
            RelBinOp::Union => self.union(a, b),
            RelBinOp::Intersect => self.intersect(a, b),
            RelBinOp::Diff => self.diff(a, b),
            RelBinOp::Join => self.join(a, b),
            RelBinOp::Product => self.product(a, b),
            RelBinOp::Override => self.override_(a, b),
        }
    }

    fn rel_unary(&mut self, op: RelUnOp, a: &Matrix) -> Matrix {
        match op {
            RelUnOp::Transpose => transpose(a),
            RelUnOp::Closure => self.closure(a),
            RelUnOp::ReflexiveClosure => {
                let c = self.closure(a);
                let iden = self.const_matrix(RelConst::Iden);
                self.union(&c, &iden)
            }
        }
    }

    fn union(&mut self, a: &Matrix, b: &Matrix) -> Matrix {
        debug_assert_eq!(a.arity(), b.arity(), "union arity mismatch");
        let mut out = Matrix::empty(a.arity());
        for (t, av) in a.iter() {
            let bv = b.get(t);
            let v = self.circ().or(av, bv);
            out.set(t.clone(), v);
        }
        for (t, bv) in b.iter() {
            if !a.contains_key(t) {
                out.set(t.clone(), bv);
            }
        }
        out
    }

    fn intersect(&mut self, a: &Matrix, b: &Matrix) -> Matrix {
        debug_assert_eq!(a.arity(), b.arity(), "intersect arity mismatch");
        let mut out = Matrix::empty(a.arity());
        for (t, av) in a.iter() {
            if b.contains_key(t) {
                let v = self.circ().and(av, b.get(t));
                out.set(t.clone(), v);
            }
        }
        out
    }

    fn diff(&mut self, a: &Matrix, b: &Matrix) -> Matrix {
        debug_assert_eq!(a.arity(), b.arity(), "diff arity mismatch");
        let mut out = Matrix::empty(a.arity());
        for (t, av) in a.iter() {
            let bv = b.get(t);
            let nbv = self.circ().not(bv);
            let v = self.circ().and(av, nbv);
            out.set(t.clone(), v);
        }
        out
    }

    fn product(&mut self, a: &Matrix, b: &Matrix) -> Matrix {
        let mut out = Matrix::empty(a.arity() + b.arity());
        for (ta, av) in a.iter() {
            for (tb, bv) in b.iter() {
                let mut atoms = ta.atoms().to_vec();
                atoms.extend_from_slice(tb.atoms());
                let v = self.circ().and(av, bv);
                out.set(Tuple::new(atoms), v);
            }
        }
        out
    }

    /// Relational join `a . b` over the shared middle atom (translation-ref
    /// §2.1). Several `(ta, tb)` pairs can reach one result tuple; their
    /// contributions are or-accumulated in tuple order (deterministic).
    fn join(&mut self, a: &Matrix, b: &Matrix) -> Matrix {
        let arity = a.arity() + b.arity() - 2;
        debug_assert!(arity >= 1, "join produces arity 0");
        // Group contributions per result tuple, then or-reduce.
        let mut groups: BTreeMap<Tuple, Vec<(Bool, Bool)>> = BTreeMap::new();
        // The pair scan is the encoder's one quadratic that creates no gates on
        // a mismatch — meter it so the encode budget sees the work.
        self.ops += (a.len() as u64).saturating_mul(b.len() as u64);
        for (ta, av) in a.iter() {
            let mid = ta.atoms()[ta.arity() - 1];
            for (tb, bv) in b.iter() {
                if tb.atoms()[0] != mid {
                    continue;
                }
                let mut atoms = ta.atoms()[..ta.arity() - 1].to_vec();
                atoms.extend_from_slice(&tb.atoms()[1..]);
                groups.entry(Tuple::new(atoms)).or_default().push((av, bv));
            }
        }
        let mut out = Matrix::empty(arity);
        for (t, pairs) in groups {
            let mut terms = Vec::with_capacity(pairs.len());
            for (av, bv) in pairs {
                let term = self.circ().and(av, bv);
                terms.push(term);
            }
            let v = self.circ().or_many(terms);
            out.set(t, v);
        }
        out
    }

    /// Override `a ++ b` = `b ∪ { t ∈ a | t.first ∉ dom(b) }` (translation-ref
    /// §2.1). `dom(b)` membership per first-atom is or-reduced once.
    fn override_(&mut self, a: &Matrix, b: &Matrix) -> Matrix {
        debug_assert_eq!(a.arity(), b.arity(), "override arity mismatch");
        // dom(b): first-atom → "some tuple of b starts here".
        let mut dom: BTreeMap<AtomId, Vec<Bool>> = BTreeMap::new();
        for (tb, bv) in b.iter() {
            dom.entry(tb.atoms()[0]).or_default().push(bv);
        }
        let mut dom_bool: BTreeMap<AtomId, Bool> = BTreeMap::new();
        for (atom, terms) in dom {
            let v = self.circ().or_many(terms);
            dom_bool.insert(atom, v);
        }
        let mut out = Matrix::empty(a.arity());
        // a's surviving tuples.
        for (ta, av) in a.iter() {
            let in_dom = dom_bool.get(&ta.atoms()[0]).copied().unwrap_or(Bool::FALSE);
            let nd = self.circ().not(in_dom);
            let v = self.circ().and(av, nd);
            out.set(ta.clone(), v);
        }
        // b's tuples (or-merge onto any overlap).
        for (tb, bv) in b.iter() {
            let slot = out.entry_or_false(tb.clone());
            let merged = self.circ_or(*slot, bv);
            *out.entry_or_false(tb.clone()) = merged;
        }
        out
    }

    /// `or` helper usable while a `&mut` matrix borrow is live (avoids a second
    /// simultaneous `self` borrow in [`Encoder::override_`]).
    fn circ_or(&mut self, a: Bool, b: Bool) -> Bool {
        self.circ().or(a, b)
    }

    fn rel_ite(&mut self, c: Bool, t: &Matrix, e: &Matrix) -> Matrix {
        debug_assert_eq!(t.arity(), e.arity(), "ite arity mismatch");
        let mut out = Matrix::empty(t.arity());
        for (tt, tv) in t.iter() {
            let ev = e.get(tt);
            let v = self.circ().ite(c, tv, ev);
            out.set(tt.clone(), v);
        }
        for (te, ev) in e.iter() {
            if !t.contains_key(te) {
                let v = self.circ().ite(c, Bool::FALSE, ev);
                out.set(te.clone(), v);
            }
        }
        out
    }

    /// Transitive closure `^r` by iterated squaring (translation-ref §2.1):
    /// `s₀ = r`, `s_{k+1} = s_k ∪ (s_k . s_k)`. After `⌈log₂ n⌉` rounds `s`
    /// contains every path of length `1 … 2^k ≥ n-1`, i.e. the full closure over
    /// an `n`-atom universe. Deterministic and finite.
    fn closure(&mut self, r: &Matrix) -> Matrix {
        debug_assert_eq!(r.arity(), 2, "closure operand must be binary");
        let rounds = log2_ceil(self.universe_len);
        let mut s = r.clone();
        for _ in 0..rounds {
            let sq = self.join(&s, &s);
            s = self.union(&s, &sq);
        }
        s
    }

    // ------------------------------------------------------------- formulas

    /// Encodes a formula to a single boolean value.
    fn formula(&mut self, id: FormulaId) -> Result<Bool, TranslateError> {
        let key = self.env_key(self.freevars.formula(id)).map(|e| (id, e));
        if let Some(k) = &key {
            if let Some(&b) = self.formula_cache.get(k) {
                return Ok(b);
            }
        }
        self.check_capacity(self.ir.formulas[id].span)?;
        let b = self.formula_uncached(id)?;
        if let Some(k) = key {
            self.formula_cache.insert(k, b);
        }
        Ok(b)
    }

    fn formula_uncached(&mut self, id: FormulaId) -> Result<Bool, TranslateError> {
        let node = &self.ir.formulas[id];
        match &node.kind {
            FormulaKind::Const(b) => Ok(Bool::Const(*b)),
            FormulaKind::Not(f) => {
                let f = *f;
                self.pol_positive = !self.pol_positive;
                let a = self.formula(f);
                self.pol_positive = !self.pol_positive;
                Ok(self.circ().not(a?))
            }
            FormulaKind::And(parts) => {
                let parts = parts.clone();
                let mut bs = Vec::with_capacity(parts.len());
                for p in parts {
                    bs.push(self.formula(p)?);
                }
                Ok(self.circ().and_many(bs))
            }
            FormulaKind::Or(parts) => {
                let parts = parts.clone();
                let mut bs = Vec::with_capacity(parts.len());
                for p in parts {
                    bs.push(self.formula(p)?);
                }
                Ok(self.circ().or_many(bs))
            }
            FormulaKind::Implies {
                antecedent,
                consequent,
            } => {
                let (antecedent, consequent) = (*antecedent, *consequent);
                // `a ⟹ c` = `¬a ∨ c`: the antecedent sits at flipped polarity and
                // is a rule-6 conditional context (translation-ref §10.7c).
                self.pol_positive = !self.pol_positive;
                let saved_bi = self.behind_implies;
                self.behind_implies = true;
                let a = self.formula(antecedent);
                self.behind_implies = saved_bi;
                self.pol_positive = !self.pol_positive;
                let a = a?;
                let c = self.formula(consequent)?;
                Ok(self.circ().implies(a, c))
            }
            FormulaKind::Iff(l, r) => {
                let a = self.formula(*l)?;
                let b = self.formula(*r)?;
                Ok(self.circ().iff(a, b))
            }
            FormulaKind::RelCompare { op, lhs, rhs } => {
                let (op, lhs, rhs) = (*op, *lhs, *rhs);
                let a = self.rel(lhs)?;
                let b = self.rel(rhs)?;
                let atom = self.rel_compare(op, &a, &b);
                // (B) Comparison-level overflow guard (translation-ref §10.7c ext,
                // mt-051): each overflow-capable `Int[·]` cast reachable through
                // the compared sides' set structure threads the rules 0–3 polarity
                // guard, lhs-then-rhs; the constant-escape (C) skips it. Allow mode
                // never guards.
                self.guard_sides(atom, &[lhs, rhs])
            }
            FormulaKind::IntCompare { op, lhs, rhs } => {
                let (op, lhs, rhs) = (*op, *lhs, *rhs);
                let (a, oa) = self.int(lhs)?;
                let (b, ob) = self.int(rhs)?;
                Ok(self.int_compare(op, &a, &b, oa, ob, lhs, rhs))
            }
            FormulaKind::MultTest { test, expr } => {
                let expr = *expr;
                let m = self.rel(expr)?;
                let atom = self.mult_test(*test, &m);
                // (B) guard also threads through a multiplicity test's set
                // structure (probe T7, mt-051).
                self.guard_sides(atom, &[expr])
            }
            FormulaKind::Quant {
                kind,
                var,
                bound,
                body,
            } => self.quant(*kind, *var, *bound, *body),
            FormulaKind::TemporalUnary { .. } | FormulaKind::TemporalBinary { .. } => {
                Err(TranslateError::LoweringUnsupported {
                    what: "temporal operator reached the encoder — a lowering invariant \
                           failure; temporal solving is Rung 6"
                        .to_owned(),
                    span: node.span,
                })
            }
        }
    }

    /// Relational `in`/`=` (translation-ref §2.2): subset is a per-tuple
    /// implication over the left candidates; equality is subset both ways, i.e.
    /// a per-tuple `iff` over the union of candidate tuples.
    fn rel_compare(&mut self, op: RelCmpOp, a: &Matrix, b: &Matrix) -> Bool {
        match op {
            RelCmpOp::Subset => {
                let mut parts = Vec::with_capacity(a.len());
                for (t, av) in a.iter() {
                    let bv = b.get(t);
                    let imp = self.circ().implies(av, bv);
                    parts.push(imp);
                }
                self.circ().and_many(parts)
            }
            RelCmpOp::Equal => {
                let mut keys: std::collections::BTreeSet<Tuple> = std::collections::BTreeSet::new();
                for t in a.tuples() {
                    keys.insert(t.clone());
                }
                for t in b.tuples() {
                    keys.insert(t.clone());
                }
                let mut parts = Vec::with_capacity(keys.len());
                for t in &keys {
                    let e = self.circ().iff(a.get(t), b.get(t));
                    parts.push(e);
                }
                self.circ().and_many(parts)
            }
        }
    }

    /// A multiplicity test on a matrix's cells (translation-ref §2.2). `lone`
    /// uses a pairwise "no two together" encoding (deterministic; the cell counts
    /// are small at Rung-3 scope).
    fn mult_test(&mut self, test: MultTest, m: &Matrix) -> Bool {
        let cells: Vec<Bool> = m.iter().map(|(_, b)| b).collect();
        match test {
            MultTest::No => {
                let some = self.circ().or_many(cells);
                self.circ().not(some)
            }
            MultTest::Some => self.circ().or_many(cells),
            MultTest::Lone => self.at_most_one(&cells),
            MultTest::One => {
                let some = self.circ().or_many(cells.clone());
                let lone = self.at_most_one(&cells);
                self.circ().and(some, lone)
            }
        }
    }

    /// Pairwise at-most-one: `⋀_{i<j} ¬(cᵢ ∧ cⱼ)`.
    fn at_most_one(&mut self, cells: &[Bool]) -> Bool {
        let mut parts = Vec::new();
        for i in 0..cells.len() {
            for j in (i + 1)..cells.len() {
                let both = self.circ().and(cells[i], cells[j]);
                let nb = self.circ().not(both);
                parts.push(nb);
            }
        }
        self.circ().and_many(parts)
    }

    /// Grounds a single-variable quantifier over its bound's candidate tuples
    /// (translation-ref §2.3): `all` = `⋀ (member → body)`, `some` = `⋁ (member ∧
    /// body)`, where `member` is the cell asserting the atom is in the bound.
    fn quant(
        &mut self,
        kind: QuantKind,
        var: VarId,
        bound: RelExprId,
        body: FormulaId,
    ) -> Result<Bool, TranslateError> {
        let bm = self.rel(bound)?;
        let candidates: Vec<(Tuple, Bool)> = bm.iter().map(|(t, b)| (t.clone(), b)).collect();
        // The var's **effective** quantifier kind for the overflow rule
        // (translation-ref §11.3): an IR `All` at positive polarity (or `Some` at
        // negative) is effective-∀. Its domain is "bare `Int`" only when the bound
        // is literally the `Int`/`seq/Int` builtin relation (§10.7c rule 0).
        let effective_forall = matches!(kind, QuantKind::All) == self.pol_positive;
        let bare_int = self.is_bare_int_bound(bound);
        self.quant_frames.push(crate::overflow_guard::QuantFrame {
            var,
            bare_int,
            effective_forall,
        });
        let mut parts = Vec::with_capacity(candidates.len());
        let mut result = Ok(());
        for (t, member) in candidates {
            self.env.insert(var, t);
            let body_b = self.formula(body);
            self.env.remove(&var);
            match body_b {
                Ok(body_b) => {
                    let part = match kind {
                        QuantKind::All => self.circ().implies(member, body_b),
                        QuantKind::Some => self.circ().and(member, body_b),
                    };
                    parts.push(part);
                }
                Err(e) => {
                    result = Err(e);
                    break;
                }
            }
        }
        self.quant_frames.pop();
        result?;
        Ok(match kind {
            QuantKind::All => self.circ().and_many(parts),
            QuantKind::Some => self.circ().or_many(parts),
        })
    }

    /// Whether a quantifier bound is literally the bare `Int`/`seq/Int` builtin
    /// relation (translation-ref §10.7c) — the only domain the jar's overflow
    /// classifier recognizes as universal.
    fn is_bare_int_bound(&self, bound: RelExprId) -> bool {
        match &self.ir.rel_exprs[bound].kind {
            RelExprKind::Relation(r) => Some(*r) == self.int_sig || Some(*r) == self.seq_int_sig,
            _ => false,
        }
    }

    /// Grounds a set comprehension (translation-ref §2.1): a result tuple is the
    /// concatenation of the decl atoms, present iff every decl's membership cell
    /// and the body hold. Nested so a later decl's bound may reference an earlier
    /// decl's variable.
    fn comprehension(
        &mut self,
        decls: &[crate::ir::CompDecl],
        body: FormulaId,
    ) -> Result<Matrix, TranslateError> {
        let arity: usize = decls.iter().map(|d| self.ir.vars[d.var].arity).sum();
        let mut out = Matrix::empty(arity.max(1));
        self.comprehension_rec(decls, 0, body, &mut Vec::new(), &mut Vec::new(), &mut out)?;
        Ok(out)
    }

    fn comprehension_rec(
        &mut self,
        decls: &[crate::ir::CompDecl],
        i: usize,
        body: FormulaId,
        prefix: &mut Vec<AtomId>,
        guards: &mut Vec<Bool>,
        out: &mut Matrix,
    ) -> Result<(), TranslateError> {
        if i == decls.len() {
            let body_b = self.formula(body)?;
            let mut all = guards.clone();
            all.push(body_b);
            let cell = self.circ().and_many(all);
            out.set(Tuple::new(prefix.clone()), cell);
            return Ok(());
        }
        let bm = self.rel(decls[i].bound)?;
        let candidates: Vec<(Tuple, Bool)> = bm.iter().map(|(t, b)| (t.clone(), b)).collect();
        for (t, member) in candidates {
            let atoms = t.atoms().to_vec();
            self.env.insert(decls[i].var, t);
            let plen = prefix.len();
            prefix.extend_from_slice(&atoms);
            guards.push(member);
            self.comprehension_rec(decls, i + 1, body, prefix, guards, out)?;
            guards.pop();
            prefix.truncate(plen);
            self.env.remove(&decls[i].var);
        }
        Ok(())
    }

    // ------------------------------------------------------------- integers

    /// Encodes an integer expression to a two's-complement value **plus its
    /// accumulated overflow flag** (translation-ref §11.1–§11.3). The overflow is
    /// consumed by the polarity guard at the comparison where the `Int` becomes a
    /// formula ([`Encoder::int_compare`]) and dropped where it becomes an atom
    /// (`Int[·]`) — matching Kodkod's `DefCond.ensureDef` firing only at
    /// comparisons.
    fn int(&mut self, id: IntExprId) -> Result<(IntVal, Bool), TranslateError> {
        let key = self.env_key(self.freevars.int(id)).map(|e| (id, e));
        if let Some(k) = &key {
            if let Some(v) = self.int_cache.get(k) {
                return Ok(v.clone());
            }
        }
        self.check_capacity(self.ir.int_exprs[id].span)?;
        let v = self.int_uncached(id)?;
        if let Some(k) = key {
            self.int_cache.insert(k, v.clone());
        }
        Ok(v)
    }

    fn int_uncached(&mut self, id: IntExprId) -> Result<(IntVal, Bool), TranslateError> {
        let node = self.ir.int_exprs[id].clone();
        let width = self.bitwidth as usize;
        match node.kind {
            IntExprKind::Const(v) => Ok((IntVal::constant(i64::from(v), width), Bool::FALSE)),
            IntExprKind::Card(rel) => {
                let m = self.rel(rel)?;
                Ok(self.int_card(&m))
            }
            IntExprKind::AtomToInt(rel) => {
                let m = self.rel(rel)?;
                Ok(self.int_atom_to_int(&m))
            }
            IntExprKind::Neg(ie) => {
                let (v, of) = self.int(ie)?;
                let (nv, neg_of) = {
                    let mut circ = self.circ();
                    let mut ib = IntBuilder::new(&mut circ, width);
                    ib.negate(&v)
                };
                let overflow = self.circ().or(of, neg_of);
                Ok((nv, overflow))
            }
            IntExprKind::Binary { op, lhs, rhs } => self.int_binary(op, lhs, rhs),
            IntExprKind::Sum { var, bound, body } => self.int_sum(var, bound, body),
            IntExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => self.int_ite(cond, then_branch, else_branch),
        }
    }

    /// Binary integer arithmetic (translation-ref §11.1/§11.2): each op wraps at
    /// the bitwidth; overflow is the `or` of the operands' inherited overflow and
    /// the op's own flag (`div`/`rem` per the pinned edge rule, shifts flagless).
    fn int_binary(
        &mut self,
        op: crate::ir::IntBinOp,
        lhs: IntExprId,
        rhs: IntExprId,
    ) -> Result<(IntVal, Bool), TranslateError> {
        use crate::ir::IntBinOp;
        let width = self.bitwidth as usize;
        let (a, oa) = self.int(lhs)?;
        let (b, ob) = self.int(rhs)?;
        let (val, op_of) = {
            let mut circ = self.circ();
            let mut ib = IntBuilder::new(&mut circ, width);
            match op {
                IntBinOp::Add => ib.add_signed(&a, &b),
                IntBinOp::Sub => ib.sub_signed(&a, &b),
                IntBinOp::Mul => ib.multiply(&a, &b),
                IntBinOp::Div => {
                    let dr = ib.div_rem(&a, &b);
                    (dr.quotient, dr.div_overflow)
                }
                IntBinOp::Rem => {
                    let dr = ib.div_rem(&a, &b);
                    (dr.remainder, dr.rem_overflow)
                }
                IntBinOp::Shl => ib.shl(&a, &b),
                IntBinOp::Sha => (ib.sha(&a, &b), Bool::FALSE),
                IntBinOp::Shr => (ib.shr(&a, &b), Bool::FALSE),
            }
        };
        let inherited = self.circ().or(oa, ob);
        let overflow = self.circ().or(inherited, op_of);
        Ok((val, overflow))
    }

    /// `sum x: B | ie` (translation-ref §11.1): a plus-tree over the bound's
    /// grounded tuples, each summand gated by its membership cell. Overflow
    /// accumulates the per-binding body overflow (gated) and every add's flag.
    fn int_sum(
        &mut self,
        var: VarId,
        bound: RelExprId,
        body: IntExprId,
    ) -> Result<(IntVal, Bool), TranslateError> {
        let width = self.bitwidth as usize;
        let bm = self.rel(bound)?;
        let candidates: Vec<(Tuple, Bool)> = bm.iter().map(|(t, b)| (t.clone(), b)).collect();
        let mut acc = IntVal::constant(0, width);
        let mut overflow = Bool::FALSE;
        for (t, member) in candidates {
            self.env.insert(var, t);
            let body_v = self.int(body);
            self.env.remove(&var);
            let (bv, bof) = body_v?;
            // Contribute the body value iff the tuple is present; its overflow
            // likewise only counts when present.
            let (next, add_of, present_of) = {
                let mut circ = self.circ();
                let mut ib = IntBuilder::new(&mut circ, width);
                let zero = IntVal::constant(0, width);
                let gated = ib.mux(member, &bv, &zero);
                let (s, add_of) = ib.add_signed(&acc, &gated);
                let present_of = circ.and(member, bof);
                (s, add_of, present_of)
            };
            acc = next;
            let step = self.circ().or(add_of, present_of);
            overflow = self.circ().or(overflow, step);
        }
        Ok((acc, overflow))
    }

    /// Integer `cond ? then : else` (translation-ref §11.1): a bitwise mux;
    /// overflow flows from the **taken** branch (`cond ? then_of : else_of`).
    fn int_ite(
        &mut self,
        cond: FormulaId,
        then_branch: IntExprId,
        else_branch: IntExprId,
    ) -> Result<(IntVal, Bool), TranslateError> {
        let width = self.bitwidth as usize;
        let c = self.formula(cond)?;
        let (t, t_of) = self.int(then_branch)?;
        let (e, e_of) = self.int(else_branch)?;
        let val = {
            let mut circ = self.circ();
            let mut ib = IntBuilder::new(&mut circ, width);
            ib.mux(c, &t, &e)
        };
        let overflow = self.circ().ite(c, t_of, e_of);
        Ok((val, overflow))
    }

    /// Cardinality `#e`: a sequential ripple-carry count of the matrix cells,
    /// normalised to a signed value at the bitwidth with an overflow flag
    /// (translation-ref §2.4).
    fn int_card(&mut self, m: &Matrix) -> (IntVal, Bool) {
        let width = self.bitwidth as usize;
        let cells: Vec<Bool> = m.iter().map(|(_, b)| b).collect();
        let mut acc: Vec<Bool> = vec![Bool::FALSE];
        {
            let mut circ = self.circ();
            let mut ib = IntBuilder::new(&mut circ, width);
            for c in cells {
                acc = ib.add_bit(&acc, c);
            }
        }
        let mut circ = self.circ();
        let mut ib = IntBuilder::new(&mut circ, width);
        ib.unsigned_to_signed(&acc)
    }

    /// `int[e]`: the signed sum of the integer values of the `Int` atoms in `e`
    /// (translation-ref §2.4), each value gated by its cell and added in
    /// two's-complement with overflow tracking (the `or` of every add's flag).
    fn int_atom_to_int(&mut self, m: &Matrix) -> (IntVal, Bool) {
        let width = self.bitwidth as usize;
        let mut acc = IntVal::constant(0, width);
        let mut overflow = Bool::FALSE;
        // Gather (cell, value) for the int atoms present, in tuple order.
        let mut terms: Vec<(Bool, i64)> = Vec::new();
        for (t, cell) in m.iter() {
            if t.arity() != 1 {
                continue;
            }
            if let Some(v) = self.atom_int_value(t.atoms()[0]) {
                terms.push((cell, v));
            }
        }
        for (cell, value) in terms {
            let (next, add_of) = {
                let mut circ = self.circ();
                let mut ib = IntBuilder::new(&mut circ, width);
                // Gate the constant's bits by the cell (value contributes iff present).
                let konst = IntVal::constant(value, width);
                let gated = gate_intval(cell, &konst);
                ib.add_signed(&acc, &gated)
            };
            acc = next;
            overflow = self.circ().or(overflow, add_of);
        }
        (acc, overflow)
    }

    /// `Int[ie]`: the unary matrix `{ atom | value(atom) = ie }` over the Int
    /// atoms (translation-ref §2.1). For a constant `ie` this is a single
    /// constant-true cell.
    fn int_to_atom(&mut self, v: &IntVal) -> Matrix {
        let width = self.bitwidth as usize;
        let mut m = Matrix::empty(1);
        for i in self.int_start..self.int_end {
            let atom = AtomId::from_index(i);
            let value = self.atom_int_value(atom).unwrap_or(0);
            let cell = {
                let mut circ = self.circ();
                let mut ib = IntBuilder::new(&mut circ, width);
                let konst = IntVal::constant(value, width);
                ib.eq(v, &konst)
            };
            m.set(Tuple::new(vec![atom]), cell);
        }
        m
    }

    /// The integer value of an atom, if it is an Int atom (translation-ref §1.3:
    /// int atoms are `-2^(bw-1) … 2^(bw-1)-1`, ascending, after the sig atoms).
    fn atom_int_value(&self, atom: AtomId) -> Option<i64> {
        let idx = atom.index();
        if idx < self.int_start || idx >= self.int_end {
            return None;
        }
        let bw = self.bitwidth;
        if bw == 0 {
            return None;
        }
        let low = -(1i64 << (bw - 1));
        let offset = i64::try_from(idx - self.int_start).unwrap_or(i64::MAX);
        Some(low + offset)
    }

    /// An integer comparison, applying the forbid-mode overflow polarity guard
    /// (translation-ref §11.3). In allow mode the raw wrapped comparison is
    /// returned. In forbid mode each operand's accumulated overflow guards the
    /// atom per its polarity/quantifier-dependence (the §10.7c rules 0–3
    /// classification, rule 4 pinned mt-051 — no comparison defers).
    #[allow(
        clippy::too_many_arguments,
        reason = "one comparison needs both operands, both overflow flags, and both \
                  operand ids (for the polarity classification) — a struct would only obscure it"
    )]
    fn int_compare(
        &mut self,
        op: IntCmpOp,
        a: &IntVal,
        b: &IntVal,
        oa: Bool,
        ob: Bool,
        lhs: IntExprId,
        rhs: IntExprId,
    ) -> Bool {
        let width = self.bitwidth as usize;
        let atom = {
            let mut circ = self.circ();
            let mut ib = IntBuilder::new(&mut circ, width);
            match op {
                IntCmpOp::Eq => ib.eq(a, b),
                IntCmpOp::Lt => ib.signed_lt(a, b),
                IntCmpOp::Gt => ib.signed_gt(a, b),
                IntCmpOp::Le => ib.signed_le(a, b),
                IntCmpOp::Ge => ib.signed_ge(a, b),
            }
        };
        if self.allow_overflow {
            return atom;
        }
        let guarded = self.apply_overflow_guard(atom, oa, lhs);
        self.apply_overflow_guard(guarded, ob, rhs)
    }

    /// Collects the overflow-capable casts of the given comparison sides
    /// (lhs-then-rhs order) and applies the (B) guard; allow mode passes the atom
    /// through unchanged (translation-ref §10.7c ext, mt-051).
    fn guard_sides(&mut self, atom: Bool, sides: &[RelExprId]) -> Result<Bool, TranslateError> {
        if self.allow_overflow {
            return Ok(atom);
        }
        let mut casts = Vec::new();
        for &s in sides {
            crate::overflow_guard::collect_capable_casts(self.ir, s, &mut casts);
        }
        self.guard_rel_casts(atom, &casts)
    }

    /// Applies the (B) comparison-level guard for each collected overflow-capable
    /// cast operand (translation-ref §10.7c ext, mt-051), in the given order. A
    /// [`translation_constant`](crate::overflow_guard::translation_constant) cast
    /// contributes no guard (the (C) constant escape); its value semantics are
    /// already baked into the operand matrix. Forbid mode only (callers gate).
    fn guard_rel_casts(&mut self, atom: Bool, casts: &[IntExprId]) -> Result<Bool, TranslateError> {
        let mut guarded = atom;
        for &ie in casts {
            if crate::overflow_guard::translation_constant(self.ir, self.bounds, ie) {
                continue;
            }
            // `int(ie)` is memoised (already visited when the cast matrix was
            // built), so this returns the same `(value, overflow)` cell.
            let (_v, of) = self.int(ie)?;
            guarded = self.apply_overflow_guard(guarded, of, ie);
        }
        Ok(guarded)
    }

    /// Empties a cast matrix when its operand overflowed (`∧ ¬of` on every cell)
    /// — the (A) value semantics (translation-ref §10.7c ext, mt-051). A
    /// constant-false `of` folds each gate back to the original cell.
    fn empty_on_overflow(&mut self, m: &Matrix, of: Bool) -> Matrix {
        let nof = self.circ().not(of);
        let cells: Vec<(Tuple, Bool)> = m.iter().map(|(t, b)| (t.clone(), b)).collect();
        let mut out = Matrix::empty(m.arity());
        for (t, cell) in cells {
            let gated = self.circ().and(cell, nof);
            out.set(t, gated);
        }
        out
    }

    /// Applies one operand's overflow guard to a comparison atom (translation-ref
    /// §10.7c). The shared classifier decides the direction from the enclosing
    /// quantifier stack and the operand's dependence. A rescue (`forall_dep`)
    /// forces the atom true at positive polarity (`∨ of`), an exclusion false
    /// (`∧ ¬of`); negative polarity swaps them. A constant-false overflow makes
    /// the guard inert.
    fn apply_overflow_guard(&mut self, atom: Bool, of: Bool, operand: IntExprId) -> Bool {
        use crate::overflow_guard::{classify, contains_int_ite, overflow_capable};
        let capable = overflow_capable(self.ir, operand);
        let behind_conditional = self.behind_implies || contains_int_ite(self.ir, operand);
        let forall_dep = classify(
            &self.quant_frames,
            self.freevars.int(operand),
            capable,
            behind_conditional,
        );
        if matches!(of, Bool::Const(false)) {
            return atom;
        }
        // `∨ of` iff polarity and dependence agree; else `∧ ¬of`.
        if self.pol_positive == forall_dep {
            self.circ().or(atom, of)
        } else {
            let nof = self.circ().not(of);
            self.circ().and(atom, nof)
        }
    }
}

/// The tuple with `prev`/`cur` swapped in every position (translation-ref §16.3,
/// the jar's `permutation`): each occurrence of `prev` becomes `cur` and vice
/// versa; all other atoms unchanged.
fn swap_tuple(t: &Tuple, prev: AtomId, cur: AtomId) -> Tuple {
    let atoms = t
        .atoms()
        .iter()
        .map(|&a| {
            if a == prev {
                cur
            } else if a == cur {
                prev
            } else {
                a
            }
        })
        .collect();
    Tuple::new(atoms)
}

/// Transpose of a binary matrix (translation-ref §2.1): reverse each tuple, cell
/// unchanged.
fn transpose(a: &Matrix) -> Matrix {
    debug_assert_eq!(a.arity(), 2, "transpose operand must be binary");
    let mut out = Matrix::empty(2);
    for (t, v) in a.iter() {
        let atoms = t.atoms();
        out.set(Tuple::new(vec![atoms[1], atoms[0]]), v);
    }
    out
}

/// `⌈log₂ n⌉` for `n ≥ 1` (0 for `n ≤ 1`) — the closure iteration count.
fn log2_ceil(n: usize) -> u32 {
    if n <= 1 {
        return 0;
    }
    // Smallest k with 2^k >= n.
    (usize::BITS) - (n - 1).leading_zeros()
}

/// Gates every bit of a constant value by `cell` (the value contributes iff the
/// cell is true) — used by `int[·]`. Since the value's bits are constants, each
/// gated bit is just `cell` (bit set) or `false` — no auxiliary variable needed.
fn gate_intval(cell: Bool, konst: &IntVal) -> IntVal {
    let bits: Vec<Bool> = konst
        .bits()
        .iter()
        .map(|&b| match b {
            Bool::Const(true) => cell,
            _ => Bool::FALSE,
        })
        .collect();
    IntVal::from_bits(bits)
}
