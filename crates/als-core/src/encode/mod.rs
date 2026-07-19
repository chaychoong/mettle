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
mod freevars;
mod int;
mod matrix;

use std::collections::BTreeMap;

use als_solve::{Cnf, Var};

use crate::bounds::{AtomId, Bounds, Tuple};
use crate::error::TranslateError;
use crate::ir::{
    FormulaId, FormulaKind, IntCmpOp, IntExprId, IntExprKind, Ir, MultTest, QuantKind, RelBinOp,
    RelCmpOp, RelConst, RelExprId, RelExprKind, RelId, RelUnOp, VarId,
};

use circuit::Circuit;
use freevars::FreeVars;
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
    /// Total universe size (to bound closure iteration and map int atoms).
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
    /// Overflow flags gathered from integer ops; `¬flag` is conjoined into the
    /// goal when overflow is forbidden (translation-ref §2.4).
    overflow_flags: Vec<Bool>,
    // Env-cached grounding memo (mt-049): keyed by `(node id, free-var bindings)`.
    // `BTreeMap` (STYLE D2): keys are ordered, iteration never escapes.
    matrix_cache: BTreeMap<(RelExprId, EnvKey), Matrix>,
    formula_cache: BTreeMap<(FormulaId, EnvKey), Bool>,
    int_cache: BTreeMap<(IntExprId, EnvKey), IntVal>,
}

impl<'a> Encoder<'a> {
    /// Creates an encoder over a freshly-minted (primary-variables-installed)
    /// CNF pool. `opts` carries the LEDGER-001 overflow switch and the encode
    /// budget; the solver-side knobs it also holds are not read here.
    pub(crate) fn new(
        ir: &'a Ir,
        bounds: &'a Bounds,
        prim: &'a PrimaryMap,
        cnf: Cnf,
        bitwidth: u32,
        int_start: usize,
        opts: crate::solve::SolveOptions,
    ) -> Self {
        let universe_len = bounds.universe.len();
        let freevars = FreeVars::build(ir);
        Self {
            ir,
            bounds,
            prim,
            freevars,
            cnf,
            bitwidth,
            int_start,
            universe_len,
            allow_overflow: opts.allow_overflow,
            encode_budget: opts.encode_budget,
            ops: 0,
            env: BTreeMap::new(),
            overflow_flags: Vec::new(),
            matrix_cache: BTreeMap::new(),
            formula_cache: BTreeMap::new(),
            int_cache: BTreeMap::new(),
        }
    }

    /// Encodes the goal formula, conjoins the overflow-forbid constraints (when
    /// overflow is forbidden), and returns the resulting top-level [`Bool`] plus
    /// the finished CNF. The driver asserts the `Bool` true.
    pub(crate) fn finish_goal(mut self, goal: FormulaId) -> Result<(Bool, Cnf), TranslateError> {
        let g = self.formula(goal)?;
        let final_bool = if self.allow_overflow || self.overflow_flags.is_empty() {
            g
        } else {
            let flags = std::mem::take(&mut self.overflow_flags);
            let mut parts = Vec::with_capacity(flags.len() + 1);
            parts.push(g);
            for f in flags {
                let nf = self.circ().not(f);
                parts.push(nf);
            }
            self.circ().and_many(parts)
        };
        Ok((final_bool, self.cnf))
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
                let v = self.int(*ie)?;
                Ok(self.int_to_atom(&v))
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
                let a = self.formula(*f)?;
                Ok(self.circ().not(a))
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
                let a = self.formula(*antecedent)?;
                let c = self.formula(*consequent)?;
                Ok(self.circ().implies(a, c))
            }
            FormulaKind::Iff(l, r) => {
                let a = self.formula(*l)?;
                let b = self.formula(*r)?;
                Ok(self.circ().iff(a, b))
            }
            FormulaKind::RelCompare { op, lhs, rhs } => {
                let a = self.rel(*lhs)?;
                let b = self.rel(*rhs)?;
                Ok(self.rel_compare(*op, &a, &b))
            }
            FormulaKind::IntCompare { op, lhs, rhs } => {
                let a = self.int(*lhs)?;
                let b = self.int(*rhs)?;
                Ok(self.int_compare(*op, &a, &b))
            }
            FormulaKind::MultTest { test, expr } => {
                let m = self.rel(*expr)?;
                Ok(self.mult_test(*test, &m))
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
        let mut parts = Vec::with_capacity(candidates.len());
        for (t, member) in candidates {
            self.env.insert(var, t);
            let body_b = self.formula(body);
            self.env.remove(&var);
            let body_b = body_b?;
            let part = match kind {
                QuantKind::All => self.circ().implies(member, body_b),
                QuantKind::Some => self.circ().and(member, body_b),
            };
            parts.push(part);
        }
        Ok(match kind {
            QuantKind::All => self.circ().and_many(parts),
            QuantKind::Some => self.circ().or_many(parts),
        })
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

    /// Encodes an integer expression to a two's-complement value (the Rung-3
    /// slice: `Const`, `#` cardinality, `int[·]`). Arithmetic/`sum`/int-`ITE`
    /// are typed defers (translation-ref §2.4; mt-033 measurement).
    fn int(&mut self, id: IntExprId) -> Result<IntVal, TranslateError> {
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

    fn int_uncached(&mut self, id: IntExprId) -> Result<IntVal, TranslateError> {
        let node = &self.ir.int_exprs[id];
        let width = self.bitwidth as usize;
        match &node.kind {
            IntExprKind::Const(v) => Ok(IntVal::constant(i64::from(*v), width)),
            IntExprKind::Card(rel) => {
                let m = self.rel(*rel)?;
                Ok(self.int_card(&m))
            }
            IntExprKind::AtomToInt(rel) => {
                let m = self.rel(*rel)?;
                Ok(self.int_atom_to_int(&m))
            }
            IntExprKind::Neg(_)
            | IntExprKind::Binary { .. }
            | IntExprKind::Sum { .. }
            | IntExprKind::IfThenElse { .. } => Err(TranslateError::LoweringUnsupported {
                what: "integer arithmetic / `sum` / integer if-then-else (Rung 4; the \
                       Rung-3 corpus needs only cardinality, constants, and `int[·]`)"
                    .to_owned(),
                span: node.span,
            }),
        }
    }

    /// Cardinality `#e`: a sequential ripple-carry count of the matrix cells,
    /// normalised to a signed value at the bitwidth with an overflow flag
    /// (translation-ref §2.4).
    fn int_card(&mut self, m: &Matrix) -> IntVal {
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
        let (val, overflow) = {
            let mut circ = self.circ();
            let mut ib = IntBuilder::new(&mut circ, width);
            ib.unsigned_to_signed(&acc)
        };
        self.push_overflow(overflow);
        val
    }

    /// `int[e]`: the signed sum of the integer values of the `Int` atoms in `e`
    /// (translation-ref §2.4), each value gated by its cell and added in
    /// two's-complement with overflow tracking.
    fn int_atom_to_int(&mut self, m: &Matrix) -> IntVal {
        let width = self.bitwidth as usize;
        let mut acc = IntVal::constant(0, width);
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
            let (next, overflow) = {
                let mut circ = self.circ();
                let mut ib = IntBuilder::new(&mut circ, width);
                // Gate the constant's bits by the cell (value contributes iff present).
                let konst = IntVal::constant(value, width);
                let gated = gate_intval(cell, &konst);
                ib.add_signed(&acc, &gated)
            };
            acc = next;
            self.push_overflow(overflow);
        }
        acc
    }

    /// `Int[ie]`: the unary matrix `{ atom | value(atom) = ie }` over the Int
    /// atoms (translation-ref §2.1). For a constant `ie` this is a single
    /// constant-true cell.
    fn int_to_atom(&mut self, v: &IntVal) -> Matrix {
        let width = self.bitwidth as usize;
        let mut m = Matrix::empty(1);
        for i in self.int_start..self.universe_len {
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
        if idx < self.int_start || idx >= self.universe_len {
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

    fn int_compare(&mut self, op: IntCmpOp, a: &IntVal, b: &IntVal) -> Bool {
        let width = self.bitwidth as usize;
        let mut circ = self.circ();
        let mut ib = IntBuilder::new(&mut circ, width);
        match op {
            IntCmpOp::Eq => ib.eq(a, b),
            IntCmpOp::Lt => ib.signed_lt(a, b),
            IntCmpOp::Gt => ib.signed_gt(a, b),
            IntCmpOp::Le => ib.signed_le(a, b),
            IntCmpOp::Ge => ib.signed_ge(a, b),
        }
    }

    fn push_overflow(&mut self, flag: Bool) {
        if !matches!(flag, Bool::Const(false)) {
            self.overflow_flags.push(flag);
        }
    }
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
