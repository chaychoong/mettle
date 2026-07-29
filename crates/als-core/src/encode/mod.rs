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
use circuit::{Circuit, GateCache};
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

/// A dense identity for a **matrix value** (mt-081 structural sharing).
///
/// Two matrices receive the same `MatrixId` **iff** they are structurally
/// equal — same arity, same candidate tuples, same cell value in each. The
/// identity is established by full structural comparison in a `BTreeMap`, never
/// by a hash: a hash collision would silently fuse two different relational
/// values and emit a wrong formula, so the lossy shortcut is not available here.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct MatrixId(u32);

/// The canonical content of a matrix: `(arity, cells in tuple order)`, where
/// each cell is [`cell_key`]'d into a total order `Bool` itself does not have.
type MatrixKey = (usize, Vec<(Tuple, u64)>);

/// A total, injective encoding of a [`Bool`] (`Bool` is not `Ord`, and a cell
/// key must order deterministically for the intern `BTreeMap`).
fn cell_key(b: Bool) -> u64 {
    match b {
        Bool::Const(false) => 0,
        Bool::Const(true) => 1,
        // `Lit::code()` is `var << 1 | negated`, dense and injective, so no
        // literal can alias a constant or another literal.
        Bool::Lit(l) => 2 + l.code() as u64,
    }
}

/// The operations whose results are shared through the structural value cache
/// (mt-081) — those a pair of operand [`MatrixId`]s fully determines, tagged
/// into one key space. The rest are [`ExtKey`]'s.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum ShareOp {
    Union,
    Intersect,
    Diff,
    Join,
    Product,
    Override,
    Closure,
    ReflexiveClosure,
}

/// The structural key of a relational operation whose result is **not**
/// determined by a pair of operand [`MatrixId`]s, so [`ShareOp`]'s key shape
/// does not fit it (mt-087).
///
/// Each variant lists exactly what its builder reads, so a hit means the
/// builder would recompute the identical matrix. Everything else the builders
/// touch (bitwidth, the int-atom span, `allow_overflow`, the universe) is fixed
/// for the whole encode. Ids only, like [`ShareOp`] — the `u64`s are
/// [`cell_key`]s, which are injective over [`Bool`].
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum ExtKey {
    /// `~r`: [`transpose`] permutes the operand's cells and reads nothing else.
    Transpose(MatrixId),
    /// `c implies t else e`: [`Encoder::rel_ite`] reads the condition literal
    /// and the two branch matrices, nothing more.
    Ite(u64, MatrixId, MatrixId),
    /// `Int[ie]`: [`Encoder::int_to_atom`] reads only the value's bits. The
    /// `Option` is the forbid-mode empty-on-overflow guard — `Some(overflow
    /// flag)` when the node is overflow-capable and the guard therefore
    /// applies, `None` when it does not, so a guarded and an unguarded cast of
    /// the same value never share.
    IntToAtom(Vec<u64>, Option<u64>),
}

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
/// Work is shared at **three** levels, all of which reuse gates rather than
/// minting a second identical set — so the SB-0 model set over the primary
/// variables is unchanged whichever fires.
///
/// 1. **By node** (mt-049 env-cached grounding): produced matrices/bools/
///    int-values are memoised by `(node id, the bindings of exactly that node's
///    free variables)`, [`FreeVars`] supplying the free-variable set. A
///    sub-expression that does not mention the innermost bound variable is
///    encoded once and shared across every binding of it, instead of being
///    re-grounded per binding.
/// 2. **By value** (mt-081 structural sharing): every matrix is interned to a
///    [`MatrixId`] by exact content, and relational operations are keyed on
///    `(operator, operand ids)`. This shares across arena nodes that are
///    *structurally unrelated* — which is what `pred`/`fun` inlining produces,
///    since `lower` re-walks each callee body into fresh nodes per call site.
///    [`ExtKey`] extends this to the kinds a pair of operand ids does not
///    determine (`~`, relational `if`/`then`/`else`, `Int[·]`).
/// 3. **By gate** (mt-087 structural gate sharing, [`circuit::GateCache`]):
///    the boolean layer under both of the above. Levels 1 and 2 share
///    *matrices*; two matrices that are already shared still drove two
///    identical runs of `rel_compare`/`mult_test`/the integer network, each
///    minting a parallel auxiliary. A conjunction is now keyed by its
///    canonical operand literals, so the second request returns the first
///    gate's auxiliary.
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
    /// even number of enclosing negations). Flipped by `Not` **only** — an
    /// `Implies` antecedent does NOT flip it (§10.7f, mt-090); drives the
    /// forbid-mode overflow-guard direction.
    pol_positive: bool,
    /// The enclosing-quantifier stack (innermost last), driving the §10.7c
    /// overflow classification. Each frame records the binder's effective kind
    /// and whether its domain is bare `Int`/`seq/Int`.
    quant_frames: Vec<crate::overflow_guard::QuantFrame>,
    /// The `Int`/`seq/Int` builtin relation ids (from the bounds builder), for
    /// recognizing a bare-`Int` quantifier domain.
    int_sig: Option<RelId>,
    seq_int_sig: Option<RelId>,
    /// The lasso back-loop selector (mt-066), when encoding a temporal goal:
    /// [`crate::ir::FormulaKind::LoopIs`] resolves through it. `None` for every
    /// static goal, which is what keeps the temporal path inert here.
    lasso: Option<&'a crate::temporal::LassoSelector>,
    // Env-cached grounding memo (mt-049): keyed by `(node id, free-var bindings)`.
    // `BTreeMap` (STYLE D2): keys are ordered, iteration never escapes.
    matrix_cache: BTreeMap<(RelExprId, EnvKey), MatrixId>,
    formula_cache: BTreeMap<(FormulaId, EnvKey), Bool>,
    // Structural value sharing (mt-081): the node-keyed memo above can only
    // share a sub-expression with *itself*; these two share a computed **value**
    // across structurally-unrelated nodes. `lower` inlines every `pred`/`fun`
    // call by re-walking the callee body into fresh arena nodes, so one model
    // routinely holds hundreds of arena-distinct copies of the same expression
    // (mt-080: 181 copies of `*co_pa`, 2,532 copies of `ident[·]`'s `e->e`),
    // each of which the node-keyed memo must re-encode from scratch.
    /// Content-interning table: canonical matrix content → its dense id.
    matrix_intern: BTreeMap<MatrixKey, MatrixId>,
    /// The interned values themselves, indexed by [`MatrixId`] — the single
    /// place a matrix is stored. Every cache above and below holds an **id**,
    /// not a matrix, so `n` arena nodes that denote one value cost `n` ids and
    /// one matrix rather than `n` matrices (without this the widened memo held
    /// a full matrix per `(node, binding)` and peaked at ~3 GB on
    /// `c11_perturbed.als[7]`, whose arena carries 601,582 relation nodes).
    matrix_by_id: Vec<Matrix>,
    /// The shared results: `(op, operand ids) → the value first computed for
    /// them`. Reusing that value reuses its Tseitin auxiliaries instead of
    /// minting a second, identical set — the same soundness argument as the
    /// mt-049 memo (identical gates over identical inputs denote the identical
    /// function, so the model set over the primary variables is unchanged).
    value_cache: BTreeMap<(ShareOp, MatrixId, MatrixId), MatrixId>,
    /// The same sharing for the kinds whose result a pair of operand ids does
    /// not determine (mt-087): see [`ExtKey`]. `Comprehension` is deliberately
    /// absent — a comprehension's matrix is a function of its body *formula*
    /// and the bindings of its free variables, and the only key that captures
    /// that without interning the IR is `(node id, env)`, which is exactly the
    /// [`Encoder::matrix_cache`] memo already in place.
    ext_cache: BTreeMap<ExtKey, MatrixId>,
    /// Structural gate sharing (mt-087): a second request for a conjunction
    /// this encode already built reuses its auxiliary instead of minting a
    /// parallel one. This is the formula/int-side counterpart of
    /// [`Encoder::value_cache`] — the matrix caches share *values*, but two
    /// structurally identical matrices still drove two identical runs of
    /// `rel_compare`/`mult_test`/the integer network before this existed.
    gates: GateCache,
    /// A free relation's / a relational constant's matrix, built and interned
    /// once instead of once per referencing arena node.
    base_rel_cache: BTreeMap<RelId, MatrixId>,
    /// Keyed by a local tag rather than [`RelConst`] itself: the IR enum needs
    /// no `Ord` for its own sake, and adding one for a cache would be the
    /// encoder leaking into the IR's derives.
    base_const_cache: BTreeMap<u8, MatrixId>,
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
        lasso: Option<&'a crate::temporal::LassoSelector>,
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
            int_sig,
            seq_int_sig,
            lasso,
            matrix_cache: BTreeMap::new(),
            formula_cache: BTreeMap::new(),
            int_cache: BTreeMap::new(),
            matrix_intern: BTreeMap::new(),
            matrix_by_id: Vec::new(),
            value_cache: BTreeMap::new(),
            ext_cache: BTreeMap::new(),
            gates: GateCache::new(),
            base_rel_cache: BTreeMap::new(),
            base_const_cache: BTreeMap::new(),
        }
    }

    // ------------------------------------------------- structural sharing

    /// Interns `m`, returning the id every structurally-equal matrix shares
    /// (mt-081). The matrix itself is stored once, in [`Encoder::matrix_by_id`].
    ///
    /// The canonicalising walk is metered into [`Encoder::ops`] like any other
    /// traversal: it is `O(cells)` work the encode budget must see, or a goal
    /// could burn time interning matrices for operations that mint no gates.
    fn intern_matrix(&mut self, m: Matrix) -> MatrixId {
        self.ops += m.len() as u64 + 1;
        let key: MatrixKey = (
            m.arity(),
            m.iter().map(|(t, b)| (t.clone(), cell_key(b))).collect(),
        );
        if let Some(&id) = self.matrix_intern.get(&key) {
            return id;
        }
        // Ids are minted in first-encounter order, which is fixed by the
        // traversal, so the whole table is a pure function of the input.
        let id = MatrixId(u32::try_from(self.matrix_by_id.len()).unwrap_or(u32::MAX));
        self.matrix_intern.insert(key, id);
        self.matrix_by_id.push(m);
        id
    }

    /// The matrix an id denotes.
    fn matrix(&self, id: MatrixId) -> Matrix {
        self.matrix_by_id[id.0 as usize].clone()
    }

    /// Runs `build` for `(op, ka, kb)`, or returns the value an earlier
    /// structurally-identical call already produced (mt-081).
    ///
    /// A cache hit costs one `BTreeMap` lookup and nothing else — in particular
    /// the operand matrices are materialised only on a **miss**, so a shared
    /// operation never pays to reconstruct inputs it will not read. `kb == ka`
    /// marks a unary operation; `op` separates the key spaces, so a unary entry
    /// can never alias a binary one.
    fn shared(
        &mut self,
        op: ShareOp,
        ka: MatrixId,
        kb: MatrixId,
        build: impl FnOnce(&mut Self, &Matrix, &Matrix) -> Matrix,
    ) -> MatrixId {
        let key = (op, ka, kb);
        if let Some(&hit) = self.value_cache.get(&key) {
            return hit;
        }
        let a = self.matrix(ka);
        let b = if kb == ka { a.clone() } else { self.matrix(kb) };
        let m = build(self, &a, &b);
        let out = self.intern_matrix(m);
        self.value_cache.insert(key, out);
        out
    }

    /// [`Encoder::shared`] for the kinds [`ExtKey`] covers (mt-087).
    ///
    /// Same contract: a hit is one `BTreeMap` lookup and costs no `ops`, a miss
    /// costs exactly what the unshared build cost before. The key is built by
    /// the caller because each variant reads a different set of already-derived
    /// ids; `build` must read nothing the key does not name.
    fn ext_shared(&mut self, key: ExtKey, build: impl FnOnce(&mut Self) -> Matrix) -> MatrixId {
        if let Some(&hit) = self.ext_cache.get(&key) {
            return hit;
        }
        let m = build(self);
        let out = self.intern_matrix(m);
        self.ext_cache.insert(key, out);
        out
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
        Circuit::new(&mut self.cnf, &mut self.ops, &mut self.gates)
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

    /// The memo key for a node given its free-variable set (mt-049, widened by
    /// mt-081).
    ///
    /// The key is the bindings of exactly the node's free variables, in `VarId`
    /// order — everything the node's encoded value can depend on, and nothing
    /// else. Two different full environments that agree on those variables
    /// therefore share the entry.
    ///
    /// mt-049 originally declined to cache a node whose free variables were the
    /// *whole* active environment, reasoning that every binding then yields a
    /// distinct key so the entry could never be reused. The mt-080 probe
    /// measured that reasoning false: a `pred`/`fun` argument is lowered once
    /// and referenced from every occurrence of the parameter in the inlined
    /// body, so the *same* `(node, binding)` pair is revisited thousands of
    /// times under one binding (`RE->e` in `c11_perturbed.als` re-encoded 7,182
    /// times across 3 bindings of `e`, never cached). Admitting those nodes cut
    /// 7.1% of the encode effort on that model. The price is memory: the memo
    /// now holds an entry per `(node, binding)` actually visited rather than
    /// only per `(node, partial binding)`.
    fn env_key(&self, free: &std::collections::BTreeSet<VarId>) -> EnvKey {
        if self.env.is_empty() {
            return Vec::new();
        }
        free.iter()
            .map(|v| {
                let t = self.env.get(v).cloned().unwrap_or_else(|| {
                    debug_assert!(false, "free var {v:?} unbound during encode");
                    Tuple::new(Vec::new())
                });
                (*v, t)
            })
            .collect()
    }

    /// Encodes a relation expression to its boolean matrix.
    fn rel(&mut self, id: RelExprId) -> Result<Matrix, TranslateError> {
        let v = self.rel_shared(id)?;
        Ok(self.matrix(v))
    }

    /// [`Encoder::rel`], yielding the value's [`MatrixId`] instead of a copy.
    ///
    /// Every matrix is interned **once**, where it is produced, and only its id
    /// travels afterwards (mt-081). Re-deriving the id at each use site would
    /// cost `O(cells)` per operand per operation — on an inlining-heavy model
    /// that walk alone outgrows the encode budget it is meant to save.
    fn rel_shared(&mut self, id: RelExprId) -> Result<MatrixId, TranslateError> {
        let key = (id, self.env_key(self.freevars.rel(id)));
        if let Some(&hit) = self.matrix_cache.get(&key) {
            return Ok(hit);
        }
        self.check_capacity(self.ir.rel_exprs[id].span)?;
        let hit = self.rel_uncached(id)?;
        self.matrix_cache.insert(key, hit);
        Ok(hit)
    }

    fn rel_uncached(&mut self, id: RelExprId) -> Result<MatrixId, TranslateError> {
        let node = &self.ir.rel_exprs[id];
        match &node.kind {
            // A relation's and a constant's matrices depend on nothing but their
            // own identity, so both the build and the interning are done once
            // per relation/constant rather than once per referencing node.
            RelExprKind::Relation(rel) => {
                let rel = *rel;
                if let Some(&hit) = self.base_rel_cache.get(&rel) {
                    return Ok(hit);
                }
                let m = self.relation_matrix(rel);
                let hit = self.intern_matrix(m);
                self.base_rel_cache.insert(rel, hit);
                Ok(hit)
            }
            RelExprKind::Var(v) => {
                let m = self.var_matrix(*v);
                Ok(self.intern_matrix(m))
            }
            RelExprKind::Const(c) => {
                let c = *c;
                let tag = match c {
                    RelConst::None => 0u8,
                    RelConst::Univ => 1,
                    RelConst::Iden => 2,
                };
                if let Some(&hit) = self.base_const_cache.get(&tag) {
                    return Ok(hit);
                }
                let m = self.const_matrix(c);
                let hit = self.intern_matrix(m);
                self.base_const_cache.insert(tag, hit);
                Ok(hit)
            }
            RelExprKind::Binary { op, lhs, rhs } => {
                let (op, lhs, rhs) = (*op, *lhs, *rhs);
                let ka = self.rel_shared(lhs)?;
                let kb = self.rel_shared(rhs)?;
                Ok(self.rel_binary(op, ka, kb))
            }
            RelExprKind::Unary { op, expr } => {
                let (op, expr) = (*op, *expr);
                let ka = self.rel_shared(expr)?;
                Ok(self.rel_unary(op, ka))
            }
            RelExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                let (cond, then_branch, else_branch) = (*cond, *then_branch, *else_branch);
                let c = self.formula(cond)?;
                let kt = self.rel_shared(then_branch)?;
                let ke = self.rel_shared(else_branch)?;
                Ok(self.ext_shared(ExtKey::Ite(cell_key(c), kt, ke), |enc| {
                    let (t, e) = (enc.matrix(kt), enc.matrix(ke));
                    enc.rel_ite(c, &t, &e)
                }))
            }
            RelExprKind::Comprehension { decls, body } => {
                let decls = decls.clone();
                let body = *body;
                let m = self.comprehension(&decls, body)?;
                Ok(self.intern_matrix(m))
            }
            RelExprKind::IntToAtom(ie) => {
                let ie = *ie;
                let (v, of) = self.int(ie)?;
                // (A) Cast value semantics (translation-ref §10.7c ext, mt-051):
                // the jar builds every `IntToExprCast` cell with `Int.eq(other,
                // empty)` (`∧ ¬accumOverflow`), so in forbid mode an overflowed
                // overflow-capable cast denotes the EMPTY set — polarity-
                // independent, in every context. Allow mode keeps the wrapped
                // atom; a non-capable cast (`Int[3]`) carries a constant-false
                // flag, so the gate folds away.
                let guarded =
                    !self.allow_overflow && crate::overflow_guard::overflow_capable(self.ir, ie);
                let key = ExtKey::IntToAtom(
                    v.bits().iter().map(|&b| cell_key(b)).collect(),
                    guarded.then(|| cell_key(of)),
                );
                Ok(self.ext_shared(key, |enc| {
                    let m = enc.int_to_atom(&v);
                    if guarded {
                        enc.empty_on_overflow(&m, of)
                    } else {
                        m
                    }
                }))
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

    /// A binary relational operation, shared structurally (mt-081): a second
    /// call with operands equal to an earlier call's reuses that result.
    fn rel_binary(&mut self, op: RelBinOp, ka: MatrixId, kb: MatrixId) -> MatrixId {
        let share = match op {
            RelBinOp::Union => ShareOp::Union,
            RelBinOp::Intersect => ShareOp::Intersect,
            RelBinOp::Diff => ShareOp::Diff,
            RelBinOp::Join => ShareOp::Join,
            RelBinOp::Product => ShareOp::Product,
            RelBinOp::Override => ShareOp::Override,
        };
        self.shared(share, ka, kb, |enc, a, b| match op {
            RelBinOp::Union => enc.union(a, b),
            RelBinOp::Intersect => enc.intersect(a, b),
            RelBinOp::Diff => enc.diff(a, b),
            RelBinOp::Join => enc.join(a, b),
            RelBinOp::Product => enc.product(a, b),
            RelBinOp::Override => enc.override_(a, b),
        })
    }

    fn rel_unary(&mut self, op: RelUnOp, ka: MatrixId) -> MatrixId {
        match op {
            // Transposition mints no gates, so sharing it saves no clauses —
            // but it still saves the `O(cells)` permute-and-intern walk, which
            // the encode budget charges like any other traversal (mt-087).
            RelUnOp::Transpose => {
                self.ext_shared(ExtKey::Transpose(ka), |enc| transpose(&enc.matrix(ka)))
            }
            RelUnOp::Closure => self.shared(ShareOp::Closure, ka, ka, |enc, a, _| enc.closure(a)),
            RelUnOp::ReflexiveClosure => {
                self.shared(ShareOp::ReflexiveClosure, ka, ka, |enc, a, _| {
                    let c = enc.closure(a);
                    let iden = enc.const_matrix(RelConst::Iden);
                    enc.union(&c, &iden)
                })
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
    /// `s₀ = r`, `s_{k+1} = s_k ∪ (s_k . s_k)`, so after `k` rounds `s` holds
    /// every path of length `1 … 2^k`. Deterministic and finite.
    ///
    /// **Round count (mt-081).** The bound is `⌈log₂ m⌉` where `m` is the
    /// operand's **support** — the number of distinct atoms occurring in its
    /// candidate cells — not the universe size. Every path `^r` can contain
    /// runs entirely through support atoms, and a *simple* path visits each at
    /// most once, so no path longer than `m − 1` edges contributes a tuple the
    /// shorter paths do not already give. `2^⌈log₂ m⌉ ≥ m > m − 1` rounds
    /// therefore reach the fixpoint; every further squaring computes
    /// `s ∪ s.s = s`, adding gates that denote nothing new. This mirrors
    /// Kodkod's matrix-dimension bound; mettle previously used the whole
    /// universe, which on `tso_transistency_perturbed*` meant 7 rounds over a
    /// relation supported on 9 atoms (mt-080: 3 of 7 rounds pure waste, 28% of
    /// that command's encode effort).
    ///
    /// A support of 0 or 1 atoms needs no rounds at all: `r` is empty, or its
    /// only possible tuple is a self-loop, which squaring reproduces.
    fn closure(&mut self, r: &Matrix) -> Matrix {
        debug_assert_eq!(r.arity(), 2, "closure operand must be binary");
        let rounds = log2_ceil(support_size(r));
        debug_assert!(
            rounds <= log2_ceil(self.universe_len),
            "closure support {} exceeds the universe {}",
            support_size(r),
            self.universe_len
        );
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
        let key = (id, self.env_key(self.freevars.formula(id)));
        if let Some(&b) = self.formula_cache.get(&key) {
            return Ok(b);
        }
        self.check_capacity(self.ir.formulas[id].span)?;
        let b = self.formula_uncached(id)?;
        self.formula_cache.insert(key, b);
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
                // The antecedent keeps the implication's OWN polarity: the jar
                // builds a Kodkod `IMPLIES` node and only `visit(NotFormula)`
                // toggles the environment's negated flag, so `a ⟹ c` is NOT
                // rewritten to `¬a ∨ c` for guard purposes (translation-ref
                // §10.7f, mt-090).
                let a = self.formula(antecedent)?;
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
                           failure; the temporal lowering (mt-066) eliminates them"
                        .to_owned(),
                    span: node.span,
                })
            }
            // The lasso back-loop atom (mt-066): the driver minted an exactly-one
            // selector over the `k` candidate loop states, so the atom *is* that
            // variable. Trivially inert when no such atom occurs — a static goal
            // never contains one, so `lasso` stays `None` and this arm is dead.
            FormulaKind::LoopIs { state } => {
                let state = *state;
                let span = node.span;
                let Some(lasso) = self.lasso else {
                    return Err(TranslateError::LoweringUnsupported {
                        what: "a lasso loop atom reached the encoder without a loop \
                               selector — the temporal driver must mint one"
                            .to_owned(),
                        span,
                    });
                };
                Ok(Bool::Lit(als_solve::Lit::positive(lasso.loop_var(state))))
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
        let key = (id, self.env_key(self.freevars.int(id)));
        if let Some(v) = self.int_cache.get(&key) {
            return Ok(v.clone());
        }
        self.check_capacity(self.ir.int_exprs[id].span)?;
        let v = self.int_uncached(id)?;
        self.int_cache.insert(key, v.clone());
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
    /// classification — the whole classifier now that rule 4 is retracted,
    /// §10.7f/mt-090; no comparison defers).
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
        let forall_dep =
            crate::overflow_guard::classify(&self.quant_frames, self.freevars.int(operand));
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

/// The number of distinct atoms occurring in a matrix's candidate cells — the
/// closure's iteration bound (see [`Encoder::closure`]). Read off the sparse
/// cell map's `BTreeMap` keys, so it is a pure function of the matrix (STYLE D1).
fn support_size(m: &Matrix) -> usize {
    let atoms: std::collections::BTreeSet<AtomId> =
        m.tuples().flat_map(|t| t.atoms().iter().copied()).collect();
    atoms.len()
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

#[cfg(test)]
mod tests {
    // A test fixture that fails to build has nothing to assert; `expect` is the
    // right failure mode here, so the crate-level ban is lifted for the module.
    #![allow(clippy::expect_used)]

    use std::collections::BTreeSet;
    use std::fmt::Write as _;

    use super::*;
    use crate::bounds::Universe;
    use crate::solve::SolveOptions;

    /// A bare encoder over an `n`-atom universe with no relations bound — enough
    /// to exercise the matrix-level operators directly.
    fn bare_encoder(n: usize) -> (Ir, Bounds, PrimaryMap) {
        let names: Vec<String> = (0..n).map(|i| format!("A${i}")).collect();
        (
            Ir::default(),
            Bounds::new(Universe::new(names)),
            BTreeMap::new(),
        )
    }

    fn encoder<'a>(ir: &'a Ir, bounds: &'a Bounds, prim: &'a PrimaryMap) -> Encoder<'a> {
        Encoder::new(
            ir,
            bounds,
            prim,
            Cnf::new(),
            0,
            bounds.universe.len(),
            SolveOptions::default(),
            None,
            None,
            None,
        )
    }

    /// A binary matrix of constant-true cells for each edge in `edges`.
    fn edge_matrix(edges: &[(usize, usize)]) -> Matrix {
        let mut m = Matrix::empty(2);
        for &(a, b) in edges {
            m.set(
                Tuple::new(vec![AtomId::from_index(a), AtomId::from_index(b)]),
                Bool::TRUE,
            );
        }
        m
    }

    /// Brute-force transitive closure by repeated relaxation — the oracle for
    /// [`Encoder::closure`]'s squaring (deliberately a different algorithm).
    fn brute_closure(edges: &[(usize, usize)]) -> BTreeSet<(usize, usize)> {
        let mut set: BTreeSet<(usize, usize)> = edges.iter().copied().collect();
        loop {
            let mut grown = set.clone();
            for &(a, b) in &set {
                for &(c, d) in &set {
                    if b == c {
                        grown.insert((a, d));
                    }
                }
            }
            if grown.len() == set.len() {
                return set;
            }
            set = grown;
        }
    }

    fn closure_tuples(n: usize, edges: &[(usize, usize)]) -> BTreeSet<(usize, usize)> {
        let (ir, bounds, prim) = bare_encoder(n);
        let mut enc = encoder(&ir, &bounds, &prim);
        let out = enc.closure(&edge_matrix(edges));
        out.iter()
            .filter(|(_, b)| matches!(b, Bool::Const(true)))
            .map(|(t, _)| (t.atoms()[0].index(), t.atoms()[1].index()))
            .collect()
    }

    /// `SplitMix64` — a seeded, portable generator, so the randomized cases are
    /// the same on every machine and every run (STYLE D4/U5).
    struct SplitMix64(u64);

    impl SplitMix64 {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }
    }

    // ------------------------------------------------------- closure bound

    #[test]
    fn log2_ceil_is_the_smallest_covering_power_of_two() {
        assert_eq!(log2_ceil(0), 0);
        assert_eq!(log2_ceil(1), 0);
        assert_eq!(log2_ceil(2), 1);
        assert_eq!(log2_ceil(3), 2);
        assert_eq!(log2_ceil(4), 2);
        assert_eq!(log2_ceil(5), 3);
        assert_eq!(log2_ceil(9), 4);
    }

    #[test]
    fn support_size_counts_atoms_not_cells() {
        // Two tuples over three distinct atoms.
        assert_eq!(support_size(&edge_matrix(&[(0, 1), (1, 2)])), 3);
        // A self-loop is one atom, however many cells precede it.
        assert_eq!(support_size(&edge_matrix(&[(4, 4)])), 1);
        // Negative space: the empty matrix has no support at all.
        assert_eq!(support_size(&Matrix::empty(2)), 0);
    }

    /// Exhaustive: every binary relation over 1..=4 atoms. The squaring closure
    /// must agree with the relaxation oracle tuple for tuple.
    #[test]
    fn closure_matches_brute_force_exhaustively() {
        for n in 1..=4usize {
            let cells = n * n;
            for mask in 0u32..(1u32 << cells) {
                let edges: Vec<(usize, usize)> = (0..cells)
                    .filter(|i| mask & (1 << i) != 0)
                    .map(|i| (i / n, i % n))
                    .collect();
                assert_eq!(
                    closure_tuples(n, &edges),
                    brute_closure(&edges),
                    "closure mismatch at n={n} mask={mask:#x}"
                );
            }
        }
    }

    /// Randomized, at sizes the exhaustive sweep cannot reach — including the
    /// scope-9 shape the mt-080 probe measured on `tso_transistency_perturbed*`.
    #[test]
    fn closure_matches_brute_force_on_random_matrices() {
        let mut rng = SplitMix64(0x5EED_0080_0081);
        for n in [5usize, 7, 9, 12] {
            for _ in 0..60 {
                let density = rng.next() % 100;
                let mut edges = Vec::new();
                for a in 0..n {
                    for b in 0..n {
                        if rng.next() % 100 < density {
                            edges.push((a, b));
                        }
                    }
                }
                assert_eq!(
                    closure_tuples(n, &edges),
                    brute_closure(&edges),
                    "closure mismatch at n={n} edges={edges:?}"
                );
            }
        }
    }

    /// The support bound is never *looser* than the old universe bound, so it can
    /// only remove rounds — and it never removes a needed one (checked above).
    #[test]
    fn support_bound_never_exceeds_the_universe_bound() {
        let m = edge_matrix(&[(0, 1), (1, 2), (2, 0)]);
        assert!(log2_ceil(support_size(&m)) <= log2_ceil(64));
        // A relation supported on 9 atoms needs 4 rounds, not the 7 a 71-atom
        // universe would have demanded (mt-080, `tso_transistency_perturbed`).
        let dense: Vec<(usize, usize)> = (0..9).flat_map(|a| (0..9).map(move |b| (a, b))).collect();
        assert_eq!(log2_ceil(support_size(&edge_matrix(&dense))), 4);
        assert_eq!(log2_ceil(71), 7);
    }

    // ---------------------------------------------------- content interning

    #[test]
    fn interning_identifies_exactly_the_structurally_equal() {
        let (ir, bounds, prim) = bare_encoder(4);
        let mut enc = encoder(&ir, &bounds, &prim);
        let a = edge_matrix(&[(0, 1), (1, 2)]);
        // Built independently, in a different insertion order.
        let b = edge_matrix(&[(1, 2), (0, 1)]);
        let ka = enc.intern_matrix(a.clone());
        assert_eq!(ka, enc.intern_matrix(b));
        // Negative space: one differing cell must not share an id.
        let c = edge_matrix(&[(0, 1), (1, 3)]);
        assert_ne!(ka, enc.intern_matrix(c));
        // Negative space: a differing *cell value* at the same tuples.
        let scratch = enc.cnf.fresh_var();
        let mut d = Matrix::empty(2);
        d.set(
            Tuple::new(vec![AtomId::from_index(0), AtomId::from_index(1)]),
            Bool::TRUE,
        );
        d.set(
            Tuple::new(vec![AtomId::from_index(1), AtomId::from_index(2)]),
            Bool::var(scratch),
        );
        assert_ne!(ka, enc.intern_matrix(d));
        // Negative space: the same cells at a different arity.
        let mut unary = Matrix::empty(1);
        unary.set(Tuple::new(vec![AtomId::from_index(0)]), Bool::TRUE);
        let ku = enc.intern_matrix(unary.clone());
        assert_eq!(ku, enc.intern_matrix(unary));
        assert_ne!(ku, ka);
        // The id round-trips back to the value it was minted for.
        let round: Vec<(Tuple, Bool)> =
            enc.matrix(ka).iter().map(|(t, v)| (t.clone(), v)).collect();
        let want: Vec<(Tuple, Bool)> = a.iter().map(|(t, v)| (t.clone(), v)).collect();
        assert_eq!(round, want, "an id must denote the matrix it interned");
    }

    #[test]
    fn a_cell_key_never_aliases_across_bool_shapes() {
        assert_ne!(cell_key(Bool::TRUE), cell_key(Bool::FALSE));
        let mut cnf = Cnf::new();
        let v0 = cnf.fresh_var();
        assert_ne!(cell_key(Bool::var(v0)), cell_key(Bool::TRUE));
        assert_ne!(cell_key(Bool::var(v0)), cell_key(Bool::FALSE));
        assert_ne!(
            cell_key(Bool::Lit(als_solve::Lit::positive(v0))),
            cell_key(Bool::Lit(als_solve::Lit::negative(v0)))
        );
    }

    // --------------------------------------------------- value-cache sharing

    /// Two structurally-identical joins share one result — the same cells, and
    /// crucially the same Tseitin auxiliaries (no second, parallel gate set).
    #[test]
    fn identical_operations_share_one_result() {
        let (ir, bounds, prim) = bare_encoder(4);
        let mut enc = encoder(&ir, &bounds, &prim);
        // Variable cells, so the join actually mints gates.
        let mut a = Matrix::empty(2);
        let mut b = Matrix::empty(2);
        for i in 0..4u32 {
            let v = enc.cnf.fresh_var();
            a.set(
                Tuple::new(vec![AtomId::from_index(0), AtomId::from_index(i as usize)]),
                Bool::var(v),
            );
            let w = enc.cnf.fresh_var();
            b.set(
                Tuple::new(vec![AtomId::from_index(i as usize), AtomId::from_index(1)]),
                Bool::var(w),
            );
        }
        let ka = enc.intern_matrix(a);
        let kb = enc.intern_matrix(b);
        let first = enc.rel_binary(RelBinOp::Join, ka, kb);
        let vars_after_first = enc.cnf.num_vars();
        let clauses_after_first = enc.cnf.clauses().len();
        let second = enc.rel_binary(RelBinOp::Join, ka, kb);
        // The identical value, cell for cell and literal for literal.
        assert_eq!(
            first, second,
            "a shared join must return the identical value"
        );
        let f: Vec<(Tuple, Bool)> = enc
            .matrix(first)
            .iter()
            .map(|(t, v)| (t.clone(), v))
            .collect();
        let s: Vec<(Tuple, Bool)> = enc
            .matrix(second)
            .iter()
            .map(|(t, v)| (t.clone(), v))
            .collect();
        assert_eq!(f, s, "a shared join must return the identical literals");
        assert_eq!(
            enc.cnf.num_vars(),
            vars_after_first,
            "sharing minted a variable"
        );
        assert_eq!(
            enc.cnf.clauses().len(),
            clauses_after_first,
            "sharing emitted a clause"
        );
    }

    /// Negative space: different operands, or the same operands under a
    /// different operator, must never collide in the value cache.
    #[test]
    fn distinct_operations_never_share() {
        let (ir, bounds, prim) = bare_encoder(4);
        let mut enc = encoder(&ir, &bounds, &prim);
        let ka = enc.intern_matrix(edge_matrix(&[(0, 1), (1, 2)]));
        let kb = enc.intern_matrix(edge_matrix(&[(1, 2), (2, 3)]));
        let union = enc.rel_binary(RelBinOp::Union, ka, kb);
        let inter = enc.rel_binary(RelBinOp::Intersect, ka, kb);
        assert_ne!(union, inter, "union and intersect collided");
        assert_ne!(
            enc.matrix(union).len(),
            enc.matrix(inter).len(),
            "union and intersect produced the same value"
        );
        // A unary entry must not alias the binary entry with the same operand.
        let clo = enc.rel_unary(RelUnOp::Closure, ka);
        let refl = enc.rel_unary(RelUnOp::ReflexiveClosure, ka);
        assert_ne!(clo, refl, "^r and *r collided");
        assert!(
            enc.matrix(refl).len() > enc.matrix(clo).len(),
            "*r lost iden"
        );
        // Order matters for a non-commutative operator.
        let ab = enc.rel_binary(RelBinOp::Join, ka, kb);
        let ba = enc.rel_binary(RelBinOp::Join, kb, ka);
        assert_ne!(ab, ba, "a.b and b.a collided");
    }

    // ------------------------------------------------------ whole-pipeline

    /// The mt-080 shape in miniature: one `pred` with a relation-valued
    /// parameter, whose body closes over that parameter, called from many sites.
    /// `lower` inlines each call into fresh arena nodes, so without structural
    /// sharing the encoder computes the identical `^x` once per call site.
    fn inlining_model(call_sites: usize, scope: usize) -> String {
        let mut src = String::from("sig E { r: set E, q: set E }\n");
        src.push_str("pred acyclic[x: E->E] { no iden & ^x }\n");
        src.push_str("fun ident[e: univ] : univ->univ { iden & e->e }\n");
        for i in 0..call_sites {
            let _ = writeln!(
                src,
                "pred p{i} {{ acyclic[r] and acyclic[q] and (r & ident[E]) in q }}"
            );
        }
        let calls: Vec<String> = (0..call_sites).map(|i| format!("p{i}")).collect();
        let _ = writeln!(src, "run {{ {} }} for {scope}", calls.join(" and "));
        src
    }

    /// Translates command 0 of `src` under `budget`, returning the CNF shape.
    fn translate_at(
        src: &str,
        budget: Option<u64>,
    ) -> Result<(u32, Vec<Vec<als_solve::Lit>>), TranslateError> {
        let loader = als_types::MapLoader::new().with("root.als", src);
        let graph = als_types::ModuleGraph::load("root.als", &loader).expect("load");
        let world = als_types::resolve(&graph).expect("resolve").world;
        let scoped = crate::compute_universe(&world, &graph, &world.commands[0]).expect("universe");
        let mut ir = Ir::default();
        let bounds = crate::compute_bounds(&world, &scoped, &mut ir);
        let goal =
            crate::lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
        let opts = SolveOptions {
            encode_budget: budget,
            ..SolveOptions::default()
        };
        let t = crate::solve::translate(&ir, &scoped, &goal, &bounds, None, opts)?;
        Ok((t.cnf.num_vars(), t.cnf.clauses().to_vec()))
    }

    /// Structural sharing keeps a heavily-inlined model inside a budget that the
    /// per-call-site re-encoding blows through.
    ///
    /// The bound is calibrated against the mt-080 probe, which measured 242
    /// arena-distinct copies of the same handful of closures on
    /// `tso_transistency_perturbed_minimality_check.als[6]` — 16.6M of 25.5M
    /// encode ops spent recomputing values already in hand. Here the same shape
    /// is reproduced with 24 call sites; with sharing the encode lands far under
    /// the budget, without it the repeated `^x` alone runs past it.
    #[test]
    fn structural_sharing_keeps_an_inlining_heavy_model_in_budget() {
        let src = inlining_model(24, 8);
        assert!(
            translate_at(&src, Some(400_000)).is_ok(),
            "the inlining-heavy model must encode inside the mt-081 budget"
        );
        // Negative space: the budget is genuinely binding, not vacuous — the
        // same model fails at a budget below what even the shared encode costs.
        assert!(matches!(
            translate_at(&src, Some(2_000)),
            Err(TranslateError::CapacityExceeded { .. })
        ));
    }

    /// Two independent translations of one model produce byte-identical CNF —
    /// variable count, clause count, and every literal in order (STYLE D1/U4).
    /// Sharing mints *fewer* auxiliaries than before, but always the same ones.
    #[test]
    fn translation_is_byte_identical_across_runs() {
        for src in [
            &inlining_model(6, 5)[..],
            "sig A { f: set A }\nrun { some f and no iden & ^f } for 4\n",
            "sig N { nxt: lone N }\nfact { all n: N | n in N.^nxt implies some n.nxt }\nrun { some nxt } for 5\n",
        ] {
            let first = translate_at(src, None).expect("translate");
            let second = translate_at(src, None).expect("translate");
            assert_eq!(first.0, second.0, "variable count drifted between runs");
            assert_eq!(first.1, second.1, "CNF clauses drifted between runs");
        }
    }

    // ---------------------------------------------------- gate-cache sharing

    /// The structural gate cache (mt-087): a repeated conjunction reuses its
    /// auxiliary, operand order does not matter, and the De Morgan dual shares
    /// the same gate — while a *different* conjunction still mints its own.
    #[test]
    fn identical_gates_share_one_auxiliary() {
        let (ir, bounds, prim) = bare_encoder(2);
        let mut enc = encoder(&ir, &bounds, &prim);
        let (x, y, z) = (
            enc.cnf.fresh_var(),
            enc.cnf.fresh_var(),
            enc.cnf.fresh_var(),
        );
        let (bx, by, bz) = (Bool::var(x), Bool::var(y), Bool::var(z));

        let first = enc.circ().and(bx, by);
        let vars = enc.cnf.num_vars();
        let clauses = enc.cnf.clauses().len();

        assert_eq!(enc.circ().and(bx, by), first, "a repeat request re-gated");
        assert_eq!(
            enc.circ().and(by, bx),
            first,
            "operand order was not sorted"
        );
        // `¬(¬x ∨ ¬y)` is the same gate read through De Morgan.
        let dual = {
            let nx = enc.circ().not(bx);
            let ny = enc.circ().not(by);
            let or = enc.circ().or(nx, ny);
            enc.circ().not(or)
        };
        assert_eq!(dual, first, "the De Morgan dual minted a parallel gate");
        assert_eq!(enc.cnf.num_vars(), vars, "gate sharing minted a variable");
        assert_eq!(
            enc.cnf.clauses().len(),
            clauses,
            "gate sharing emitted a clause"
        );
        // Negative space: a different conjunction is a different gate.
        let other = enc.circ().and(bx, bz);
        assert_ne!(other, first, "distinct conjunctions collided");
        assert!(enc.cnf.num_vars() > vars, "a fresh gate minted nothing");
    }

    /// Canonicalising the operand list also folds the two degenerate cases it
    /// exposes: `x ∧ x = x` and `x ∧ ¬x = false`, neither of which needs a gate.
    #[test]
    fn duplicate_and_complementary_operands_fold() {
        let (ir, bounds, prim) = bare_encoder(2);
        let mut enc = encoder(&ir, &bounds, &prim);
        let x = enc.cnf.fresh_var();
        let bx = Bool::var(x);
        let nx = enc.circ().not(bx);
        let before = enc.cnf.num_vars();
        assert_eq!(enc.circ().and(bx, bx), bx);
        assert_eq!(enc.circ().and(bx, nx), Bool::FALSE);
        assert_eq!(enc.circ().or(bx, nx), Bool::TRUE);
        assert_eq!(
            enc.cnf.num_vars(),
            before,
            "a folded gate minted a variable"
        );
    }

    // ---------------------------------------------------- extended sharing

    /// The mt-087 [`ExtKey`] cache: `~r` and a relational `if`/`then`/`else`
    /// share on their operand values, and never across distinct ones.
    #[test]
    fn transpose_and_ite_share_on_their_operands() {
        let (ir, bounds, prim) = bare_encoder(4);
        let mut enc = encoder(&ir, &bounds, &prim);
        let ka = enc.intern_matrix(edge_matrix(&[(0, 1), (1, 2)]));
        let kb = enc.intern_matrix(edge_matrix(&[(2, 3)]));

        let t1 = enc.rel_unary(RelUnOp::Transpose, ka);
        let ops_after = enc.ops;
        assert_eq!(enc.rel_unary(RelUnOp::Transpose, ka), t1, "~r re-derived");
        assert_eq!(enc.ops, ops_after, "a shared ~r was charged effort");
        assert_ne!(
            enc.rel_unary(RelUnOp::Transpose, kb),
            t1,
            "~r collided across operands"
        );

        let c = Bool::var(enc.cnf.fresh_var());
        let ite = |enc: &mut Encoder, c: Bool, kt, ke| {
            enc.ext_shared(ExtKey::Ite(cell_key(c), kt, ke), |e| {
                let (t, f) = (e.matrix(kt), e.matrix(ke));
                e.rel_ite(c, &t, &f)
            })
        };
        let i1 = ite(&mut enc, c, ka, kb);
        let vars = enc.cnf.num_vars();
        assert_eq!(ite(&mut enc, c, ka, kb), i1, "the same ITE re-gated");
        assert_eq!(enc.cnf.num_vars(), vars, "a shared ITE minted a variable");
        // Negative space: swapping the branches is a different value, and so is
        // flipping the condition.
        assert_ne!(ite(&mut enc, c, kb, ka), i1, "the ITE branches collided");
        let nc = enc.circ().not(c);
        assert_ne!(ite(&mut enc, nc, ka, kb), i1, "the ITE condition collided");
    }

    /// A model whose `pred` inlining produces many arena copies of one
    /// `if`/`then`/`else` and one `~`: the whole-pipeline check that the two
    /// extended keys fire, and that the goal still solves to the same answer.
    #[test]
    fn extended_sharing_survives_the_whole_pipeline() {
        let src = "sig E { r: set E, q: set E }\n\
                   fun pick[a: E->E, b: E->E] : E->E { (some a implies a else b) }\n\
                   pred p[a: E->E, b: E->E] { ~(pick[a, b]) in ~a + ~b }\n\
                   run { p[r, q] and p[r, q] and p[q, r] } for 4\n";
        let first = translate_at(src, None).expect("translate");
        let second = translate_at(src, None).expect("translate");
        assert_eq!(first.0, second.0, "variable count drifted between runs");
        assert_eq!(first.1, second.1, "CNF clauses drifted between runs");
    }
}
