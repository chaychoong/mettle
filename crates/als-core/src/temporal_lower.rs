//! **LTL-on-lasso lowering** (ADR-0015 decision 2, mt-066): turns one temporal
//! command into a plain first-order [`LoweredGoal`] over the per-state relation
//! copies [`crate::temporal::unroll`] minted, at a fixed trace length `k`.
//!
//! [`lower_temporal_command`] is the entry point. It reuses the whole static
//! walk — [`crate::lower::lower_command_keeping_temporal`] produces the same IR
//! `lower_command` does, temporal nodes and all — and then *eliminates* the
//! temporal nodes by evaluating every formula / relational expression / integer
//! expression **at a logical time index**. The output contains no
//! [`FormulaKind::TemporalUnary`]/[`FormulaKind::TemporalBinary`]/
//! [`RelExprKind::Prime`] node and no reference to an un-unrolled variable
//! relation; both are asserted before returning (STYLE I1/I3).
//!
//! [`eliminate_fragment_at_state`] is that same machinery run **after** a solve,
//! for the REPL's per-state evaluator (mt-068): a solved trace fixes the loop
//! target, so it takes one concrete branch instead of the `k`-way split below.
//!
//! # The trace model, and why the loop index is split at the top
//!
//! Every SAT temporal instance is a **lasso**: `k` physical states plus a
//! back-loop target `l ∈ [0, k)` (alloy6-temporal.md §(c)). The infinite trace
//! is `0, 1, …, k−1, l, l+1, …, k−1, l, …`.
//!
//! Naively one lowers each formula at a *physical state* and case-splits on the
//! loop index locally, at each temporal operator ("the successor of state `k−1`
//! is state `j` **when** `LoopIs(j)`"). That is exactly right for the future
//! operators — but **wrong for the past ones**, because on the second and later
//! passes through the loop the history of a physical state is *not* its physical
//! prefix `0..i`: it also contains every state of the trace. Probe **P-D2** pins
//! this against the jar, decisively:
//!
//! ```text
//! var sig A {} var sig B {}
//! fact { no A; always (some A => after no A); always (no A => after some A) }
//! run { no B and always ((once some A) implies (some B)) } for 2 but exactly 2 steps
//! ```
//!
//! The alternation forces `traceLength = 2, loopState = 0`. Under an
//! honest-physical-prefix reading `once some A` is false at state 0 (A is empty
//! there), so the model is satisfiable with `B` empty at state 0. The jar
//! answers **UNSAT** — at logical time 2 the trace is back at state 0, `once
//! some A` is now true, and `some B` is required there too. ADR-0015's
//! shorthand ("past operators walk the honest prefix") is therefore *not* the
//! jar's semantics; the jar carries `UNROLL_MAP`/`LEVEL`/`L_PREFIX` and
//! `TemporalInstance.unrolls` for exactly this. mettle implements the jar.
//!
//! So mettle lowers over a **logical timeline**: a concrete finite sequence of
//! physical states, unrolled past the first pass far enough that every past
//! subformula has reached its fixpoint, with a concrete loop-back index. For
//! loop target `l` and past-nesting depth `d` ([`PastDepth`]):
//!
//! ```text
//! timeline(k, l, d) = [0, 1, …, k−1] ++ [l, …, k−1] × d
//! loop_at           = d == 0 ? l : (len − (k − l))     // start of the LAST copy
//! ```
//!
//! `d` extra copies suffice: a past operator whose operands are pass-`m`-stable
//! is itself pass-`(m+1)`-stable (one more traversal of the loop revisits the
//! same physical states with the same operand values, so neither the `∃u` nor
//! the `∀v` of any past operator can change), and a temporal-free operand is
//! pass-0-stable. Over-approximating `d` is harmless — extra copies of an
//! already-stable segment change nothing — so nested past operators simply get
//! `1 + max(children)`, never a cleverer bound.
//!
//! The timeline **length and content depend on `l`**, so the loop index cannot
//! be case-split locally at each operator: it is split once, above the whole
//! goal, as `⋁_l (LoopIs(l) ∧ Goal_l)`. [`FormulaKind::LoopIs`] is still the IR
//! atom the brief calls for and still resolves to a
//! [`crate::temporal::LassoSelector`] variable in the encoder — it just appears
//! once per branch instead of once per operator. Within a branch every index is
//! concrete, which is what makes the expansions below readable and checkable.
//!
//! Sharing keeps the `k`-fold split cheap: a subformula containing **no**
//! temporal operator ([`OperatorScan`]) has the same value at every logical time
//! mapping to the same physical state — reading a `var` relation is *not* enough
//! to make it time-dependent — so it is memoised on `(node, physical state)`
//! across every branch. Only the temporal skeleton is duplicated per branch.
//!
//! # The expansion equations
//!
//! Fix a branch: `T` = timeline length, `L` = `loop_at`, `σ[t]` = the physical
//! state at logical time `t`. Write `φ@t` for "φ lowered at time `t`".
//!
//! | | expansion | pinned by |
//! |---|---|---|
//! | `succ(t)` | `t+1 < T ? t+1 : L` | P-C1/C3 (`k=1`: the successor of the only state is itself) |
//! | `after φ @t` | `φ@succ(t)` | P-C3/C4 |
//! | `e' @t` | `e@succ(t)` | P-C1/C2, P-C5/C6 (prime chains step through the back-loop) |
//! | `before φ @t` | `t == 0 ? false : φ@(t−1)` | P-A1/A2 (**strong** previous: false at the initial state, for *any* body), P-J1–J3 (`always (after (before φ))` ≡ `always φ`) |
//! | `always φ @t` | `⋀_{u ∈ reach(t)} φ@u` | P-B8, P-C7 |
//! | `eventually φ @t` | `⋁_{u ∈ reach(t)} φ@u` | P-B8 |
//! | `once φ @t` | `⋁_{u ≤ t} φ@u` | P-A3/A4 (includes the present), P-D2 |
//! | `historically φ @t` | `⋀_{u ≤ t} φ@u` | P-A5, P-H1 |
//! | `φ until ψ @t` | `⋁_i (ψ@p_i ∧ ⋀_{j<i} φ@p_j)` | P-B1–B4 (operand order: ψ is the goal) |
//! | `φ releases ψ @t` | `⋀_i (ψ@p_i ∨ ⋁_{j<i} φ@p_j)` | P-B5–B7 |
//! | `φ since ψ @t` | `⋁_i (ψ@q_i ∧ ⋀_{j<i} φ@q_j)` | P-A6/A7 |
//! | `φ triggered ψ @t` | `⋀_i (ψ@q_i ∨ ⋁_{j<i} φ@q_j)` | P-A8/A9 |
//!
//! where `p = [t..T) ++ [L..T)` is the future path (two traversals: a third adds
//! no new `(witness, prefix)` pair, since the physical states and the required
//! prefix set both repeat), `reach(t)` is `p` as an ascending set, and
//! `q = [t, t−1, …, 0]` is the honest *logical* past — honest now, because the
//! timeline itself already carries the loop's real history.
//!
//! `releases`/`triggered` are the De Morgan duals of `until`/`since`
//! (`p R q ≡ ¬(¬p U ¬q)`), written out directly rather than as a negation so the
//! encoder sees a positive circuit.
//!
//! # Which conjuncts hold at every state
//!
//! The jar does **not** wrap the whole goal in `always`; it decides per conjunct
//! (`TranslateAlloyToKodkod.makeFacts`, `BoundsComputer`), and each rule is
//! probe-confirmed:
//!
//! - a top-level `fact` and the command body: **state 0 only**
//!   (`makeFacts` → `recursiveAddFormula`, no `always`; probe P-F3);
//! - a synthesized **field decl / domain** fact: `always` iff the formula is
//!   temporal (`:268-269`, `:281-282`; probe P-F5/F6);
//! - a **sig appended** fact: `always` iff temporal (`:307-308`; probe P-F4);
//! - a **field `disj` group** fact: `always` iff the decl is `var` (`:291-292`,
//!   `:297-298`) — mettle uses the same is-temporal test, which additionally
//!   wraps a *static* `disj` field group on a `var` sig (recorded as a divergence);
//! - a **bounds-builder** constraint: `always` for a `var` sig's
//!   `one`/`some`/`lone` (`BoundsComputer.java:473/477/479`; probe P-E4/E5) and
//!   for a subset sig's containment (`:245-246`). mettle re-lowers *every*
//!   bounds constraint at every state: a static sig's constraint mentions only
//!   rigid relations, so its `k` copies are identical and the blanket rule is
//!   exact there.
//!
//! "Holds at every state" is expressed by wrapping the conjunct in an
//! [`TemporalUnOp::Always`] node and lowering *that* at time 0 — one code path,
//! no second notion of per-state.
//!
//! # The two extra facts a `var` sig hierarchy induces
//!
//! `BoundsComputer` emits constraints for a `var` hierarchy that have no static
//! counterpart, so mettle's bounds builder (which is static-only by design)
//! cannot have emitted them. [`hierarchy_facts`] adds them here:
//!
//! 1. **Union rigidity** (`:206-207`, probe P-E1) — a **static** parent with at
//!    least one `var` child gets `always (sum' = sum)`, i.e. its whole
//!    population is rigid. Emitted as `⋀_{s>0} sum@s = sum@0`.
//! 2. **The subsig-migration ban** (`:164-173`, `:195-199`, probe P-E3) — once
//!    any child is `var`, plain per-state disjointness is replaced by
//!    `all v: univ | eventually (v in c) => always (v not in earlier siblings)`,
//!    i.e. an atom may never move between sibling subsigs (or between a subsig
//!    and the remainder). Emitted as the equivalent **cross-state** disjointness
//!    `no (c@s & earlier@t)` over every ordered state pair.

use std::collections::{BTreeMap, BTreeSet};

use als_syntax::Span;
use als_types::{ModuleGraph, ResolvedWorld, SigId, SigKind};

use crate::bounds_builder::BoundsResult;
use crate::error::TranslateError;
use crate::ir::{
    CompDecl, Formula, FormulaId, FormulaKind, IntExpr, IntExprId, IntExprKind, Ir, MultTest,
    RelBinOp, RelCmpOp, RelExpr, RelExprId, RelExprKind, TemporalBinOp, TemporalUnOp,
};
use crate::lower::{
    lower_command_keeping_temporal, GoalConjunct, LoweredFragment, LoweredGoal, Provenance,
};
use crate::scope::ScopedUniverse;
use crate::temporal::UnrolledBounds;

/// Lowers command `command_index` at trace length `k` into a plain first-order
/// goal over `unrolled`'s per-state relations (ADR-0015 decision 2).
///
/// `unrolled` must be [`crate::temporal::unroll`] of the same command's bounds
/// at the same `k`; the returned goal's [`FormulaKind::LoopIs`] atoms range over
/// `0..k`, so it must be encoded with a [`crate::temporal::LassoSelector`] of
/// that length — [`crate::solve::solve_temporal_goal`] is the matched driver.
///
/// Skolem relations minted by the walk are **static** (skolemization is off
/// under every temporal operator, `Skolemizer.java:494-526`, and a top-level
/// existential outside them still skolemizes into a rigid constant — probe
/// P-F1/F2), so they are *not* in `unrolled` and resolve to themselves at every
/// state; the caller binds [`LoweredGoal::skolem_bounds`] exactly as the static
/// driver does.
///
/// The returned [`LoweredGoal::conjuncts`] are **not** the §2.5 per-source list:
/// the loop split mixes every source conjunct into each branch, so the branch
/// disjunction is reported as one [`Provenance::Command`] conjunct followed by
/// the `var`-hierarchy facts. Provenance labelling of a temporal goal would have
/// to be per-branch, which nothing consumes.
///
/// # Errors
/// Every [`TranslateError`] [`crate::lower::lower_command`] can return except
/// [`TranslateError::TemporalUnsupported`].
///
/// # Panics
/// Panics if `unrolled.k != k`, or if the produced goal still contains a
/// temporal node or an un-unrolled variable relation — all internal invariant
/// violations (STYLE I1/I5).
#[allow(
    clippy::too_many_arguments,
    reason = "the same translation context `lower_command` threads (world, graph, scopes, \
              bounds, arena, command) plus the trace length and its unrolled view — a \
              bundle struct would only move the arguments, not reduce them"
)]
pub fn lower_temporal_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    bounds: &BoundsResult,
    ir: &mut Ir,
    command_index: usize,
    k: usize,
    unrolled: &UnrolledBounds,
) -> Result<LoweredGoal, TranslateError> {
    assert!(k >= 1, "trace length must be >= 1, got {k}");
    assert_eq!(
        unrolled.k, k,
        "unrolled view and requested trace length disagree"
    );

    let temporal = lower_command_keeping_temporal(world, graph, scoped, bounds, ir, command_index)?;
    let span = ir.formulas[temporal.goal].span;

    // 1. Decide, per conjunct, whether the jar asserts it at state 0 or at every
    //    state, and materialise the latter as an `always` wrapper.
    let wrapped: Vec<(FormulaId, Provenance)> = temporal
        .conjuncts
        .iter()
        .map(|c| {
            let f = if holds_at_every_state(ir, c) {
                let s = ir.formulas[c.formula].span;
                alloc_formula(
                    ir,
                    FormulaKind::TemporalUnary {
                        op: TemporalUnOp::Always,
                        body: c.formula,
                    },
                    s,
                )
            } else {
                c.formula
            };
            (f, c.provenance.clone())
        })
        .collect();

    // 2. How far past the first pass the timeline must run for every past
    //    subformula to reach its fixpoint.
    let mut depth = PastDepth::default();
    let unroll_depth = wrapped
        .iter()
        .map(|(f, _)| depth.formula(ir, *f))
        .max()
        .unwrap_or(0);

    // 3. One concrete branch per candidate loop target, guarded by its loop atom.
    let mut branches = Vec::with_capacity(k);
    let mut shared = SharedMemo::default();
    for l in 0..k {
        let line = Timeline::new(k, l, unroll_depth);
        let mut walker = Walker {
            ir,
            unrolled,
            line: &line,
            shared: &mut shared,
            timed: Memo::default(),
        };
        let parts: Vec<FormulaId> = wrapped.iter().map(|(f, _)| walker.formula(*f, 0)).collect();
        let body = conjoin(ir, parts, span);
        let atom = alloc_formula(ir, FormulaKind::LoopIs { state: l }, span);
        branches.push(alloc_formula(ir, FormulaKind::And(vec![atom, body]), span));
    }
    let mut conjuncts: Vec<GoalConjunct> = vec![GoalConjunct {
        formula: alloc_formula(ir, FormulaKind::Or(branches), span),
        provenance: Provenance::Command,
    }];

    // 4. The `var`-hierarchy facts the static bounds builder has no counterpart
    //    for. Loop-independent, so they stay outside the branch disjunction.
    conjuncts.extend(hierarchy_facts(world, bounds, ir, unrolled, k));

    let goal = conjoin(ir, conjuncts.iter().map(|c| c.formula).collect(), span);
    assert_first_order(ir, unrolled, goal);
    Ok(LoweredGoal {
        goal,
        conjuncts,
        // Translation classes are dropped explicitly, not left to go stale
        // (mt-137, ADR-0029 decision 5): the elimination above re-mints every
        // formula per state, so the input goal's class members name ids this
        // goal no longer contains. Temporal × overflow × cross-polarity sharing
        // is unprobed and out of scope; LIMITATIONS records it.
        trans_classes: BTreeMap::new(),
        ..temporal
    })
}

// ====================== post-solve fragment evaluation ======================

/// Eliminates one already-lowered evaluator **fragment**'s temporal nodes at
/// **logical time `state`** of an *already solved* lasso (mt-068;
/// alloy6-temporal.md §(h): all 11 temporal operators are legal evaluator input,
/// each evaluated relative to the given state — probes T-24 and P-068-1).
///
/// The post-solve twin of [`lower_temporal_command`], deliberately over the same
/// machinery rather than a second LTL semantics: the solve already fixed the
/// back-loop target, so there is no [`FormulaKind::LoopIs`] case split — one
/// concrete [`Timeline`], one branch, every index literal.
///
/// # What `state` means
///
/// It is a **time index on the infinite trace**, not an index into
/// `states[..]` — the reference's `eval(expr, state)` takes the same thing, and
/// `state` is never an error (§(h)):
///
/// - negatives clamp to 0;
/// - `state ∈ [0, k)` is that state on the trace's first pass;
/// - `state >= k` is a **later pass through the loop**. Its present-tense value
///   is the wrapped physical state ([`normalize_state`](crate::normalize_state)),
///   its future is the same from any pass — and its **past** is the real one,
///   containing the earlier passes. Probe **P-068-1** pins this decisively:
///   on a trace looping back to state 0, `once some A` is `false` at state 0 but
///   `true` at state 2, and `before some A` alternates with the *index's* parity
///   rather than with the physical state (`scratchpad/probe/mt068/NOTES.md`).
///
/// The timeline is unrolled far enough to reach `state`, with the pass **capped
/// at the fragment's past-nesting depth** — exact, not approximate, by the same
/// pass-stability argument the module docs make (`d`-deep past values agree from
/// pass `d` on), and what keeps an absurd `state` from building an absurd
/// timeline.
///
/// # Panics
/// Panics if `loop_state` is outside `unrolled.k`, or if a temporal node
/// survives the elimination — both internal invariants (STYLE I1/I5; `state`
/// itself is user input, and is therefore normalized rather than asserted).
pub fn eliminate_fragment_at_state(
    ir: &mut Ir,
    unrolled: &UnrolledBounds,
    loop_state: usize,
    state: i64,
    fragment: LoweredFragment,
) -> LoweredFragment {
    assert!(
        loop_state < unrolled.k,
        "loop target outside the trace: loop_state={loop_state} k={}",
        unrolled.k
    );

    let mut depth = PastDepth::default();
    let unroll_depth = match fragment {
        LoweredFragment::Formula(f) => depth.formula(ir, f),
        LoweredFragment::Int(i) => depth.int(ir, i),
        LoweredFragment::Rel(r) => depth.rel(ir, r),
    };
    // The clamp; the conversion cannot fail on a 64-bit target, and saturating
    // is harmless because `logical_time` caps the pass anyway.
    let state = usize::try_from(state.max(0)).unwrap_or(usize::MAX);
    let time = logical_time(state, unrolled.k, loop_state, unroll_depth);
    let line = Timeline::new(unrolled.k, loop_state, unroll_depth);
    debug_assert_eq!(
        line.states[time],
        crate::temporal_solve::normalize_state(
            i64::try_from(state).unwrap_or(i64::MAX),
            unrolled.k,
            loop_state
        ),
        "a logical time must sit at the state the pinned wrap rule names"
    );

    let mut shared = SharedMemo::default();
    let mut walker = Walker {
        ir,
        unrolled,
        line: &line,
        shared: &mut shared,
        timed: Memo::default(),
    };
    let eliminated = match fragment {
        LoweredFragment::Formula(f) => LoweredFragment::Formula(walker.formula(f, time)),
        LoweredFragment::Int(i) => LoweredFragment::Int(walker.int(i, time)),
        LoweredFragment::Rel(r) => LoweredFragment::Rel(walker.rel(r, time)),
    };

    let (formulas, rels, ints) = match eliminated {
        LoweredFragment::Formula(f) => (vec![f], Vec::new(), Vec::new()),
        LoweredFragment::Rel(r) => (Vec::new(), vec![r], Vec::new()),
        LoweredFragment::Int(i) => (Vec::new(), Vec::new(), vec![i]),
    };
    assert_first_order_from(ir, unrolled, formulas, rels, ints);
    eliminated
}

/// Where time index `state` sits on [`Timeline::new(k, loop_state, depth)`], with
/// the pass capped at `depth` (see [`eliminate_fragment_at_state`]).
///
/// `depth == 0` — nothing in the fragment can tell one pass from another — puts
/// every index on the first pass, i.e. exactly at
/// [`normalize_state`](crate::normalize_state)'s physical state.
fn logical_time(state: usize, k: usize, loop_state: usize, depth: usize) -> usize {
    if state < k {
        return state;
    }
    let span = k - loop_state;
    let within = (state - k) % span;
    if depth == 0 {
        return loop_state + within;
    }
    // `pass` counts complete traversals past the first one, 1-based; the
    // timeline holds `depth` of them, and pass `depth` onward all agree.
    let pass = (state - k) / span + 1;
    k + (pass.min(depth) - 1) * span + within
}

// ============================ the conjunct seam ============================

/// Whether the jar wraps this conjunct in `always` (see the module docs).
fn holds_at_every_state(ir: &Ir, conjunct: &GoalConjunct) -> bool {
    match conjunct.provenance {
        // A `fact` paragraph and the command body are one conjunction evaluated
        // at the initial state (`makeFacts` → `recursiveAddFormula`, probe P-F3).
        // A metamodel emptiness fact is added by `resolveMeta` with `addFact`,
        // so it is a fact paragraph too. The distinction is unobservable here:
        // no meta sig is ever `var` (mt-107 P0 §M5), so the alternative rule —
        // `is_temporal_formula`, which the other synthesized facts use — would
        // return `false` for these as well.
        Provenance::Fact | Provenance::MetaFact(_) | Provenance::Command => false,
        // `always` iff the constraint is temporal at all — for a static sig that
        // is false and the state-0 form is already the whole story, so lowering
        // it at every state is exact either way.
        Provenance::BoundsConstraint => true,
        Provenance::FieldFact(_) | Provenance::FieldDisjFact(_) | Provenance::AppendedFact(_) => {
            is_temporal_formula(ir, conjunct.formula)
        }
    }
}

/// `TemporalTranslator.isTemporal`: whether a lowered formula mentions a `var`
/// relation or a temporal operator — the jar's own test for wrapping a
/// synthesized fact in `always`.
fn is_temporal_formula(ir: &Ir, id: FormulaId) -> bool {
    let mut seen = Temporality::default();
    seen.formula(ir, id)
}

/// Memoised "does this subtree mention a temporal operator or a `var` relation".
#[derive(Default)]
struct Temporality {
    formulas: BTreeMap<FormulaId, bool>,
    rels: BTreeMap<RelExprId, bool>,
    ints: BTreeMap<IntExprId, bool>,
}

impl Temporality {
    fn formula(&mut self, ir: &Ir, id: FormulaId) -> bool {
        if let Some(v) = self.formulas.get(&id) {
            return *v;
        }
        let v = match &ir.formulas[id].kind {
            FormulaKind::Const(_) | FormulaKind::LoopIs { .. } => false,
            FormulaKind::Not(f) => self.formula(ir, *f),
            FormulaKind::And(parts) | FormulaKind::Or(parts) => {
                parts.clone().iter().any(|&p| self.formula(ir, p))
            }
            FormulaKind::Implies {
                antecedent,
                consequent,
            } => self.formula(ir, *antecedent) | self.formula(ir, *consequent),
            FormulaKind::Iff(l, r) => self.formula(ir, *l) | self.formula(ir, *r),
            FormulaKind::RelCompare { lhs, rhs, .. } => self.rel(ir, *lhs) | self.rel(ir, *rhs),
            FormulaKind::IntCompare { lhs, rhs, .. } => self.int(ir, *lhs) | self.int(ir, *rhs),
            FormulaKind::MultTest { expr, .. } => self.rel(ir, *expr),
            FormulaKind::Quant { bound, body, .. } => {
                self.rel(ir, *bound) | self.formula(ir, *body)
            }
            FormulaKind::TemporalUnary { .. } | FormulaKind::TemporalBinary { .. } => true,
        };
        self.formulas.insert(id, v);
        v
    }

    fn rel(&mut self, ir: &Ir, id: RelExprId) -> bool {
        if let Some(v) = self.rels.get(&id) {
            return *v;
        }
        let v = match &ir.rel_exprs[id].kind {
            RelExprKind::Var(_) | RelExprKind::Const(_) => false,
            RelExprKind::Relation(r) => ir.relations[*r].is_var(),
            RelExprKind::Binary { lhs, rhs, .. } => self.rel(ir, *lhs) | self.rel(ir, *rhs),
            RelExprKind::Unary { expr, .. } => self.rel(ir, *expr),
            RelExprKind::Prime(_) => true,
            RelExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => self.formula(ir, *cond) | self.rel(ir, *then_branch) | self.rel(ir, *else_branch),
            RelExprKind::Comprehension { decls, body } => {
                let (decls, body) = (decls.clone(), *body);
                decls.iter().any(|d| self.rel(ir, d.bound)) | self.formula(ir, body)
            }
            RelExprKind::IntToAtom(ie) => self.int(ir, *ie),
        };
        self.rels.insert(id, v);
        v
    }

    fn int(&mut self, ir: &Ir, id: IntExprId) -> bool {
        if let Some(v) = self.ints.get(&id) {
            return *v;
        }
        let v = match &ir.int_exprs[id].kind {
            IntExprKind::Const(_) => false,
            IntExprKind::Card(r) | IntExprKind::AtomToInt(r) => self.rel(ir, *r),
            IntExprKind::Neg(ie) => self.int(ir, *ie),
            IntExprKind::Binary { lhs, rhs, .. } => self.int(ir, *lhs) | self.int(ir, *rhs),
            IntExprKind::Sum { bound, body, .. } => self.rel(ir, *bound) | self.int(ir, *body),
            IntExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => self.formula(ir, *cond) | self.int(ir, *then_branch) | self.int(ir, *else_branch),
        };
        self.ints.insert(id, v);
        v
    }
}

/// Whether a subtree contains a temporal **operator** (including `'`) — a
/// strictly narrower question than [`Temporality`], which also counts a bare
/// `var` relation reference.
///
/// This is the one that decides the memo key: a subtree that merely *reads*
/// `var` relations still has a value determined entirely by the physical state,
/// so it can be shared across every loop branch and across every copy of the
/// same state. Only a subtree that inspects *time* needs a per-branch,
/// per-logical-time entry.
#[derive(Default)]
struct OperatorScan {
    formulas: BTreeMap<FormulaId, bool>,
    rels: BTreeMap<RelExprId, bool>,
    ints: BTreeMap<IntExprId, bool>,
}

impl OperatorScan {
    fn formula(&mut self, ir: &Ir, id: FormulaId) -> bool {
        if let Some(v) = self.formulas.get(&id) {
            return *v;
        }
        let v = match &ir.formulas[id].kind {
            FormulaKind::Const(_) | FormulaKind::LoopIs { .. } => false,
            FormulaKind::Not(f) => self.formula(ir, *f),
            FormulaKind::And(parts) | FormulaKind::Or(parts) => {
                parts.clone().iter().any(|&p| self.formula(ir, p))
            }
            FormulaKind::Implies {
                antecedent,
                consequent,
            } => self.formula(ir, *antecedent) | self.formula(ir, *consequent),
            FormulaKind::Iff(l, r) => self.formula(ir, *l) | self.formula(ir, *r),
            FormulaKind::RelCompare { lhs, rhs, .. } => self.rel(ir, *lhs) | self.rel(ir, *rhs),
            FormulaKind::IntCompare { lhs, rhs, .. } => self.int(ir, *lhs) | self.int(ir, *rhs),
            FormulaKind::MultTest { expr, .. } => self.rel(ir, *expr),
            FormulaKind::Quant { bound, body, .. } => {
                self.rel(ir, *bound) | self.formula(ir, *body)
            }
            FormulaKind::TemporalUnary { .. } | FormulaKind::TemporalBinary { .. } => true,
        };
        self.formulas.insert(id, v);
        v
    }

    fn rel(&mut self, ir: &Ir, id: RelExprId) -> bool {
        if let Some(v) = self.rels.get(&id) {
            return *v;
        }
        let v = match &ir.rel_exprs[id].kind {
            RelExprKind::Relation(_) | RelExprKind::Var(_) | RelExprKind::Const(_) => false,
            RelExprKind::Binary { lhs, rhs, .. } => self.rel(ir, *lhs) | self.rel(ir, *rhs),
            RelExprKind::Unary { expr, .. } => self.rel(ir, *expr),
            RelExprKind::Prime(_) => true,
            RelExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => self.formula(ir, *cond) | self.rel(ir, *then_branch) | self.rel(ir, *else_branch),
            RelExprKind::Comprehension { decls, body } => {
                let (decls, body) = (decls.clone(), *body);
                decls.iter().any(|d| self.rel(ir, d.bound)) | self.formula(ir, body)
            }
            RelExprKind::IntToAtom(ie) => self.int(ir, *ie),
        };
        self.rels.insert(id, v);
        v
    }

    fn int(&mut self, ir: &Ir, id: IntExprId) -> bool {
        if let Some(v) = self.ints.get(&id) {
            return *v;
        }
        let v = match &ir.int_exprs[id].kind {
            IntExprKind::Const(_) => false,
            IntExprKind::Card(r) | IntExprKind::AtomToInt(r) => self.rel(ir, *r),
            IntExprKind::Neg(ie) => self.int(ir, *ie),
            IntExprKind::Binary { lhs, rhs, .. } => self.int(ir, *lhs) | self.int(ir, *rhs),
            IntExprKind::Sum { bound, body, .. } => self.rel(ir, *bound) | self.int(ir, *body),
            IntExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => self.formula(ir, *cond) | self.int(ir, *then_branch) | self.int(ir, *else_branch),
        };
        self.ints.insert(id, v);
        v
    }
}

// ============================== the timeline ==============================

/// Past-operator nesting depth: how many extra copies of the loop the timeline
/// needs before every past subformula is at its fixpoint (module docs).
#[derive(Default)]
struct PastDepth {
    formulas: BTreeMap<FormulaId, usize>,
    rels: BTreeMap<RelExprId, usize>,
    ints: BTreeMap<IntExprId, usize>,
}

impl PastDepth {
    fn formula(&mut self, ir: &Ir, id: FormulaId) -> usize {
        if let Some(v) = self.formulas.get(&id) {
            return *v;
        }
        let v = match &ir.formulas[id].kind {
            FormulaKind::Const(_) | FormulaKind::LoopIs { .. } => 0,
            FormulaKind::Not(f) => self.formula(ir, *f),
            FormulaKind::And(parts) | FormulaKind::Or(parts) => parts
                .clone()
                .iter()
                .map(|&p| self.formula(ir, p))
                .max()
                .unwrap_or(0),
            FormulaKind::Implies {
                antecedent,
                consequent,
            } => self
                .formula(ir, *antecedent)
                .max(self.formula(ir, *consequent)),
            FormulaKind::Iff(l, r) => self.formula(ir, *l).max(self.formula(ir, *r)),
            FormulaKind::RelCompare { lhs, rhs, .. } => self.rel(ir, *lhs).max(self.rel(ir, *rhs)),
            FormulaKind::IntCompare { lhs, rhs, .. } => self.int(ir, *lhs).max(self.int(ir, *rhs)),
            FormulaKind::MultTest { expr, .. } => self.rel(ir, *expr),
            FormulaKind::Quant { bound, body, .. } => {
                self.rel(ir, *bound).max(self.formula(ir, *body))
            }
            FormulaKind::TemporalUnary { op, body } => {
                let (op, body) = (*op, *body);
                self.formula(ir, body) + usize::from(is_past_unary(op))
            }
            FormulaKind::TemporalBinary { op, lhs, rhs } => {
                let (op, lhs, rhs) = (*op, *lhs, *rhs);
                self.formula(ir, lhs).max(self.formula(ir, rhs)) + usize::from(is_past_binary(op))
            }
        };
        self.formulas.insert(id, v);
        v
    }

    fn rel(&mut self, ir: &Ir, id: RelExprId) -> usize {
        if let Some(v) = self.rels.get(&id) {
            return *v;
        }
        let v = match &ir.rel_exprs[id].kind {
            RelExprKind::Relation(_) | RelExprKind::Var(_) | RelExprKind::Const(_) => 0,
            RelExprKind::Binary { lhs, rhs, .. } => self.rel(ir, *lhs).max(self.rel(ir, *rhs)),
            RelExprKind::Unary { expr, .. } | RelExprKind::Prime(expr) => self.rel(ir, *expr),
            RelExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => self
                .formula(ir, *cond)
                .max(self.rel(ir, *then_branch))
                .max(self.rel(ir, *else_branch)),
            RelExprKind::Comprehension { decls, body } => {
                let (decls, body) = (decls.clone(), *body);
                decls
                    .iter()
                    .map(|d| self.rel(ir, d.bound))
                    .max()
                    .unwrap_or(0)
                    .max(self.formula(ir, body))
            }
            RelExprKind::IntToAtom(ie) => self.int(ir, *ie),
        };
        self.rels.insert(id, v);
        v
    }

    fn int(&mut self, ir: &Ir, id: IntExprId) -> usize {
        if let Some(v) = self.ints.get(&id) {
            return *v;
        }
        let v = match &ir.int_exprs[id].kind {
            IntExprKind::Const(_) => 0,
            IntExprKind::Card(r) | IntExprKind::AtomToInt(r) => self.rel(ir, *r),
            IntExprKind::Neg(ie) => self.int(ir, *ie),
            IntExprKind::Binary { lhs, rhs, .. } => self.int(ir, *lhs).max(self.int(ir, *rhs)),
            IntExprKind::Sum { bound, body, .. } => self.rel(ir, *bound).max(self.int(ir, *body)),
            IntExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => self
                .formula(ir, *cond)
                .max(self.int(ir, *then_branch))
                .max(self.int(ir, *else_branch)),
        };
        self.ints.insert(id, v);
        v
    }
}

fn is_past_unary(op: TemporalUnOp) -> bool {
    match op {
        TemporalUnOp::Before | TemporalUnOp::Historically | TemporalUnOp::Once => true,
        TemporalUnOp::Always | TemporalUnOp::Eventually | TemporalUnOp::After => false,
    }
}

fn is_past_binary(op: TemporalBinOp) -> bool {
    match op {
        TemporalBinOp::Since | TemporalBinOp::Triggered => true,
        TemporalBinOp::Until | TemporalBinOp::Releases => false,
    }
}

/// One branch's concrete logical timeline: the physical state at each logical
/// time, plus where the trace loops back to.
struct Timeline {
    /// `states[t]` is the physical state at logical time `t`.
    states: Vec<usize>,
    /// The logical time the last time step loops back to.
    loop_at: usize,
}

impl Timeline {
    fn new(k: usize, l: usize, unroll_depth: usize) -> Self {
        debug_assert!(l < k, "loop target {l} outside trace of length {k}");
        let mut states: Vec<usize> = (0..k).collect();
        for _ in 0..unroll_depth {
            states.extend(l..k);
        }
        // With extra copies the loop closes on the *last* one, which is the
        // fixpoint copy; with none it closes on the physical loop target.
        let loop_at = if unroll_depth == 0 {
            l
        } else {
            states.len() - (k - l)
        };
        debug_assert!(loop_at < states.len(), "loop target outside the timeline");
        Timeline { states, loop_at }
    }

    fn len(&self) -> usize {
        self.states.len()
    }

    /// The logical time one step after `t`, following the back-loop at the end.
    fn succ(&self, t: usize) -> usize {
        if t + 1 < self.len() {
            t + 1
        } else {
            self.loop_at
        }
    }

    /// The future path from `t`: the remaining suffix, then one full traversal
    /// of the loop. A third traversal adds no new witness/prefix pair, so two
    /// are enough for `until`/`releases` (module docs).
    fn future_path(&self, t: usize) -> Vec<usize> {
        (t..self.len()).chain(self.loop_at..self.len()).collect()
    }

    /// [`Self::future_path`] as an ascending set — the states `always` /
    /// `eventually` range over.
    fn reachable(&self, t: usize) -> Vec<usize> {
        let set: BTreeSet<usize> = self.future_path(t).into_iter().collect();
        set.into_iter().collect()
    }

    /// The logical past of `t`, most recent first: `[t, t−1, …, 0]`.
    fn past_path(t: usize) -> Vec<usize> {
        (0..=t).rev().collect()
    }
}

// ============================== the walk ==============================

/// Memo keyed on `(node, logical time)` — for subtrees whose value genuinely
/// depends on where in *this branch's* timeline they sit.
#[derive(Default)]
struct Memo {
    formulas: BTreeMap<(FormulaId, usize), FormulaId>,
    rels: BTreeMap<(RelExprId, usize), RelExprId>,
    ints: BTreeMap<(IntExprId, usize), IntExprId>,
}

/// Memo keyed on `(node, physical state)`, shared across every branch — for
/// temporal-free subtrees, whose value depends only on which physical state's
/// relations they read. This is what stops the `k`-way loop split from
/// duplicating the bulk of a real model.
#[derive(Default)]
struct SharedMemo {
    memo: Memo,
    operators: OperatorScan,
}

struct Walker<'a> {
    ir: &'a mut Ir,
    unrolled: &'a UnrolledBounds,
    line: &'a Timeline,
    shared: &'a mut SharedMemo,
    timed: Memo,
}

impl Walker<'_> {
    fn state_of(&self, t: usize) -> usize {
        self.line.states[t]
    }

    fn formula(&mut self, id: FormulaId, t: usize) -> FormulaId {
        let pure = !self.shared.operators.formula(self.ir, id);
        let key = if pure {
            (id, self.state_of(t))
        } else {
            (id, t)
        };
        let hit = if pure {
            self.shared.memo.formulas.get(&key).copied()
        } else {
            self.timed.formulas.get(&key).copied()
        };
        if let Some(hit) = hit {
            return hit;
        }
        let out = self.formula_uncached(id, t);
        if pure {
            self.shared.memo.formulas.insert(key, out);
        } else {
            self.timed.formulas.insert(key, out);
        }
        out
    }

    fn formula_uncached(&mut self, id: FormulaId, t: usize) -> FormulaId {
        let node = self.ir.formulas[id].clone();
        let span = node.span;
        let kind = match node.kind {
            FormulaKind::Const(b) => FormulaKind::Const(b),
            FormulaKind::LoopIs { state } => FormulaKind::LoopIs { state },
            FormulaKind::Not(f) => FormulaKind::Not(self.formula(f, t)),
            FormulaKind::And(parts) => {
                FormulaKind::And(parts.iter().map(|&p| self.formula(p, t)).collect())
            }
            FormulaKind::Or(parts) => {
                FormulaKind::Or(parts.iter().map(|&p| self.formula(p, t)).collect())
            }
            FormulaKind::Implies {
                antecedent,
                consequent,
            } => FormulaKind::Implies {
                antecedent: self.formula(antecedent, t),
                consequent: self.formula(consequent, t),
            },
            FormulaKind::Iff(l, r) => FormulaKind::Iff(self.formula(l, t), self.formula(r, t)),
            FormulaKind::RelCompare { op, lhs, rhs } => FormulaKind::RelCompare {
                op,
                lhs: self.rel(lhs, t),
                rhs: self.rel(rhs, t),
            },
            FormulaKind::IntCompare { op, lhs, rhs } => FormulaKind::IntCompare {
                op,
                lhs: self.int(lhs, t),
                rhs: self.int(rhs, t),
            },
            FormulaKind::MultTest { test, expr } => FormulaKind::MultTest {
                test,
                expr: self.rel(expr, t),
            },
            FormulaKind::Quant {
                kind,
                var,
                bound,
                body,
            } => FormulaKind::Quant {
                kind,
                // The universe is rigid, so a bound variable denotes the same
                // atom at every state; only its *domain* is state-indexed.
                var,
                bound: self.rel(bound, t),
                body: self.formula(body, t),
            },
            FormulaKind::TemporalUnary { op, body } => {
                return self.temporal_unary(op, body, t, span)
            }
            FormulaKind::TemporalBinary { op, lhs, rhs } => {
                return self.temporal_binary(op, lhs, rhs, t, span)
            }
        };
        alloc_formula(self.ir, kind, span)
    }

    /// The six unary connectives (module docs' expansion table).
    fn temporal_unary(
        &mut self,
        op: TemporalUnOp,
        body: FormulaId,
        t: usize,
        span: Span,
    ) -> FormulaId {
        match op {
            TemporalUnOp::After => {
                let u = self.line.succ(t);
                self.formula(body, u)
            }
            TemporalUnOp::Before => {
                if t == 0 {
                    // Strong previous: false at the start of time, for any body
                    // (probe P-A1/A2 — both `before (some A)` and `before (no A)`
                    // are UNSAT as an initial-state assertion).
                    alloc_formula(self.ir, FormulaKind::Const(false), span)
                } else {
                    self.formula(body, t - 1)
                }
            }
            TemporalUnOp::Always | TemporalUnOp::Eventually => {
                let times = self.line.reachable(t);
                let parts: Vec<FormulaId> = times.iter().map(|&u| self.formula(body, u)).collect();
                let kind = if matches!(op, TemporalUnOp::Always) {
                    FormulaKind::And(parts)
                } else {
                    FormulaKind::Or(parts)
                };
                alloc_formula(self.ir, kind, span)
            }
            TemporalUnOp::Historically | TemporalUnOp::Once => {
                let parts: Vec<FormulaId> = (0..=t).map(|u| self.formula(body, u)).collect();
                let kind = if matches!(op, TemporalUnOp::Historically) {
                    FormulaKind::And(parts)
                } else {
                    FormulaKind::Or(parts)
                };
                alloc_formula(self.ir, kind, span)
            }
        }
    }

    /// The four binary connectives: `until`/`since` are the "witness with a
    /// prefix" disjunction over the future/past path, `releases`/`triggered`
    /// their De Morgan duals (module docs).
    fn temporal_binary(
        &mut self,
        op: TemporalBinOp,
        lhs: FormulaId,
        rhs: FormulaId,
        t: usize,
        span: Span,
    ) -> FormulaId {
        let path = match op {
            TemporalBinOp::Until | TemporalBinOp::Releases => self.line.future_path(t),
            TemporalBinOp::Since | TemporalBinOp::Triggered => Timeline::past_path(t),
        };
        let strong = matches!(op, TemporalBinOp::Until | TemporalBinOp::Since);
        let mut steps = Vec::with_capacity(path.len());
        // `prefix` accumulates φ over the path already walked; each step pairs
        // ψ at the current position with it.
        let mut prefix: Vec<FormulaId> = Vec::with_capacity(path.len());
        for (i, &u) in path.iter().enumerate() {
            let goal = self.formula(rhs, u);
            let step = if i == 0 {
                goal
            } else if strong {
                let mut parts = Vec::with_capacity(prefix.len() + 1);
                parts.push(goal);
                parts.extend(prefix.iter().copied());
                alloc_formula(self.ir, FormulaKind::And(parts), span)
            } else {
                let mut parts = Vec::with_capacity(prefix.len() + 1);
                parts.push(goal);
                parts.extend(prefix.iter().copied());
                alloc_formula(self.ir, FormulaKind::Or(parts), span)
            };
            steps.push(step);
            let hold = self.formula(lhs, u);
            prefix.push(hold);
        }
        let kind = if strong {
            FormulaKind::Or(steps)
        } else {
            FormulaKind::And(steps)
        };
        alloc_formula(self.ir, kind, span)
    }

    fn rel(&mut self, id: RelExprId, t: usize) -> RelExprId {
        let pure = !self.shared.operators.rel(self.ir, id);
        let key = if pure {
            (id, self.state_of(t))
        } else {
            (id, t)
        };
        let hit = if pure {
            self.shared.memo.rels.get(&key).copied()
        } else {
            self.timed.rels.get(&key).copied()
        };
        if let Some(hit) = hit {
            return hit;
        }
        let out = self.rel_uncached(id, t);
        if pure {
            self.shared.memo.rels.insert(key, out);
        } else {
            self.timed.rels.insert(key, out);
        }
        out
    }

    fn rel_uncached(&mut self, id: RelExprId, t: usize) -> RelExprId {
        let node = self.ir.rel_exprs[id].clone();
        let span = node.span;
        let kind = match node.kind {
            // The bridge map is the only handle on a `var` relation's per-state
            // copies; a static relation (including every skolem) is itself at
            // every state.
            RelExprKind::Relation(r) => {
                RelExprKind::Relation(self.unrolled.at(r, self.state_of(t)).unwrap_or(r))
            }
            RelExprKind::Var(v) => RelExprKind::Var(v),
            RelExprKind::Const(c) => RelExprKind::Const(c),
            RelExprKind::Binary { op, lhs, rhs } => RelExprKind::Binary {
                op,
                lhs: self.rel(lhs, t),
                rhs: self.rel(rhs, t),
            },
            RelExprKind::Unary { op, expr } => RelExprKind::Unary {
                op,
                expr: self.rel(expr, t),
            },
            // `e'` is `e` one step later, following the back-loop at the last
            // time step (probes P-C1/C2, P-C5/C6).
            RelExprKind::Prime(e) => return self.rel(e, self.line.succ(t)),
            RelExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => RelExprKind::IfThenElse {
                cond: self.formula(cond, t),
                then_branch: self.rel(then_branch, t),
                else_branch: self.rel(else_branch, t),
            },
            RelExprKind::Comprehension { decls, body } => RelExprKind::Comprehension {
                decls: decls
                    .iter()
                    .map(|d| CompDecl {
                        var: d.var,
                        bound: self.rel(d.bound, t),
                    })
                    .collect(),
                body: self.formula(body, t),
            },
            RelExprKind::IntToAtom(ie) => RelExprKind::IntToAtom(self.int(ie, t)),
        };
        alloc_rel(self.ir, kind, span)
    }

    fn int(&mut self, id: IntExprId, t: usize) -> IntExprId {
        let pure = !self.shared.operators.int(self.ir, id);
        let key = if pure {
            (id, self.state_of(t))
        } else {
            (id, t)
        };
        let hit = if pure {
            self.shared.memo.ints.get(&key).copied()
        } else {
            self.timed.ints.get(&key).copied()
        };
        if let Some(hit) = hit {
            return hit;
        }
        let out = self.int_uncached(id, t);
        if pure {
            self.shared.memo.ints.insert(key, out);
        } else {
            self.timed.ints.insert(key, out);
        }
        out
    }

    fn int_uncached(&mut self, id: IntExprId, t: usize) -> IntExprId {
        let node = self.ir.int_exprs[id].clone();
        let span = node.span;
        let kind = match node.kind {
            IntExprKind::Const(v) => IntExprKind::Const(v),
            IntExprKind::Card(r) => IntExprKind::Card(self.rel(r, t)),
            IntExprKind::AtomToInt(r) => IntExprKind::AtomToInt(self.rel(r, t)),
            IntExprKind::Neg(ie) => IntExprKind::Neg(self.int(ie, t)),
            IntExprKind::Binary { op, lhs, rhs } => IntExprKind::Binary {
                op,
                lhs: self.int(lhs, t),
                rhs: self.int(rhs, t),
            },
            IntExprKind::Sum { var, bound, body } => IntExprKind::Sum {
                var,
                bound: self.rel(bound, t),
                body: self.int(body, t),
            },
            IntExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => IntExprKind::IfThenElse {
                cond: self.formula(cond, t),
                then_branch: self.int(then_branch, t),
                else_branch: self.int(else_branch, t),
            },
        };
        alloc_int(self.ir, kind, span)
    }
}

// ===================== the `var`-hierarchy extra facts =====================

/// The two `var`-hierarchy constraints `BoundsComputer` emits that have no
/// static counterpart (module docs): union rigidity and the migration ban.
///
/// Both are stated over *physical* states directly (they quantify over the whole
/// trace, not over a logical timeline), so they are loop-independent.
fn hierarchy_facts(
    world: &ResolvedWorld,
    bounds: &BoundsResult,
    ir: &mut Ir,
    unrolled: &UnrolledBounds,
    k: usize,
) -> Vec<GoalConjunct> {
    let mut out = Vec::new();
    let mut copies: BTreeMap<(RelExprId, usize), RelExprId> = BTreeMap::new();
    for (sig, s) in world.sigs.iter() {
        if s.is_builtin || !matches!(s.kind, SigKind::Prim { .. }) {
            continue;
        }
        // Scopable prim children, in `SigId` (declaration) order — the same
        // order the bounds builder and the jar accumulate `sum` in, which is
        // what makes "earlier siblings" well-defined.
        let kids: Vec<SigId> = world
            .sigs
            .iter()
            .filter(|(_, c)| {
                !c.is_builtin && matches!(&c.kind, SigKind::Prim { parent: Some(p) } if *p == sig)
            })
            .map(|(id, _)| id)
            .collect();
        let Some(first_var) = kids.iter().position(|c| world.sigs[*c].is_var) else {
            continue;
        };
        let span = s.span;

        // (1) A *static* parent of `var` children has a rigid population
        // (`BoundsComputer.java:206-207`, probe P-E1).
        if !s.is_var {
            if let Some(&denote) = bounds.sig_denote.get(&sig) {
                let at_zero = state_copy(ir, unrolled, &mut copies, denote, 0);
                for state in 1..k {
                    let here = state_copy(ir, unrolled, &mut copies, denote, state);
                    let f = alloc_formula(
                        ir,
                        FormulaKind::RelCompare {
                            op: RelCmpOp::Equal,
                            lhs: here,
                            rhs: at_zero,
                        },
                        span,
                    );
                    out.push(GoalConjunct {
                        formula: f,
                        provenance: Provenance::BoundsConstraint,
                    });
                }
            }
        }

        // (2) Once a child is `var`, an atom may never migrate between sibling
        // subsigs, nor between a subsig and the remainder
        // (`BoundsComputer.java:164-173`/`:195-199`, probe P-E3). Stated as
        // cross-state disjointness over every ordered state pair, which is
        // exactly "eventually in c ⇒ always not in the earlier siblings".
        let mut earlier: Vec<RelExprId> = Vec::new();
        for (i, &child) in kids.iter().enumerate() {
            let Some(&denote) = bounds.sig_denote.get(&child) else {
                continue;
            };
            if i >= first_var.max(1) {
                let prevs = earlier.clone();
                for (a, b) in cross_states(k) {
                    for &prev in &prevs {
                        let f = disjoint_across(
                            ir,
                            unrolled,
                            &mut copies,
                            (denote, a),
                            (prev, b),
                            span,
                        );
                        out.push(GoalConjunct {
                            formula: f,
                            provenance: Provenance::BoundsConstraint,
                        });
                    }
                }
            }
            earlier.push(denote);
        }
        if let Some(&rem) = bounds.remainder_rel.get(&sig) {
            let rem_expr = alloc_rel(ir, RelExprKind::Relation(rem), span);
            let prevs = earlier.clone();
            for (a, b) in cross_states(k) {
                for &prev in &prevs {
                    let f =
                        disjoint_across(ir, unrolled, &mut copies, (prev, a), (rem_expr, b), span);
                    out.push(GoalConjunct {
                        formula: f,
                        provenance: Provenance::BoundsConstraint,
                    });
                }
            }
        }
    }
    out
}

/// Every ordered state pair of a `k`-state trace, in ascending order.
fn cross_states(k: usize) -> Vec<(usize, usize)> {
    (0..k).flat_map(|a| (0..k).map(move |b| (a, b))).collect()
}

/// `no (lhs@a & rhs@b)`.
fn disjoint_across(
    ir: &mut Ir,
    unrolled: &UnrolledBounds,
    copies: &mut BTreeMap<(RelExprId, usize), RelExprId>,
    (lhs, a): (RelExprId, usize),
    (rhs, b): (RelExprId, usize),
    span: Span,
) -> FormulaId {
    let l = state_copy(ir, unrolled, copies, lhs, a);
    let r = state_copy(ir, unrolled, copies, rhs, b);
    let inter = alloc_rel(
        ir,
        RelExprKind::Binary {
            op: RelBinOp::Intersect,
            lhs: l,
            rhs: r,
        },
        span,
    );
    alloc_formula(
        ir,
        FormulaKind::MultTest {
            test: MultTest::No,
            expr: inter,
        },
        span,
    )
}

/// Rewrites a **temporal-free** relational expression to read `state`'s
/// relations. Used only for the hierarchy facts, whose operands are sig
/// denotations (unions of relations) and therefore never temporal.
fn state_copy(
    ir: &mut Ir,
    unrolled: &UnrolledBounds,
    copies: &mut BTreeMap<(RelExprId, usize), RelExprId>,
    id: RelExprId,
    state: usize,
) -> RelExprId {
    if let Some(hit) = copies.get(&(id, state)) {
        return *hit;
    }
    let node = ir.rel_exprs[id].clone();
    let span = node.span;
    let kind = match node.kind {
        RelExprKind::Relation(r) => RelExprKind::Relation(unrolled.at(r, state).unwrap_or(r)),
        RelExprKind::Binary { op, lhs, rhs } => RelExprKind::Binary {
            op,
            lhs: state_copy(ir, unrolled, copies, lhs, state),
            rhs: state_copy(ir, unrolled, copies, rhs, state),
        },
        RelExprKind::Unary { op, expr } => RelExprKind::Unary {
            op,
            expr: state_copy(ir, unrolled, copies, expr, state),
        },
        RelExprKind::Var(_) | RelExprKind::Const(_) => return id,
        RelExprKind::Prime(_)
        | RelExprKind::IfThenElse { .. }
        | RelExprKind::Comprehension { .. }
        | RelExprKind::IntToAtom(_) => {
            debug_assert!(
                false,
                "a sig denotation is a union of relations, never a derived form"
            );
            return id;
        }
    };
    let out = alloc_rel(ir, kind, span);
    copies.insert((id, state), out);
    out
}

// ============================== small helpers ==============================

fn alloc_formula(ir: &mut Ir, kind: FormulaKind, span: Span) -> FormulaId {
    ir.formulas.alloc(Formula { kind, span })
}

fn alloc_rel(ir: &mut Ir, kind: RelExprKind, span: Span) -> RelExprId {
    ir.rel_exprs.alloc(RelExpr { kind, span })
}

fn alloc_int(ir: &mut Ir, kind: IntExprKind, span: Span) -> IntExprId {
    ir.int_exprs.alloc(IntExpr { kind, span })
}

fn conjoin(ir: &mut Ir, parts: Vec<FormulaId>, span: Span) -> FormulaId {
    match parts.len() {
        0 => alloc_formula(ir, FormulaKind::Const(true), span),
        1 => parts[0],
        _ => alloc_formula(ir, FormulaKind::And(parts), span),
    }
}

// ============================== negative space ==============================

/// The bead's acceptance invariant (STYLE I1/I3): the produced goal is
/// **first-order** — no temporal node survives, and no relation reference names
/// an original `var` relation instead of one of its per-state copies.
///
/// Runs unconditionally (not only in debug builds): it is the one property that
/// distinguishes a correct temporal lowering from one that silently drops time,
/// and it is linear in the goal.
fn assert_first_order(ir: &Ir, unrolled: &UnrolledBounds, goal: FormulaId) {
    assert_first_order_from(ir, unrolled, vec![goal], Vec::new(), Vec::new());
}

/// [`assert_first_order`] from roots of any sort — an evaluator fragment's root
/// is a formula, a relational expression, or an integer expression
/// ([`eliminate_fragment_at_state`]), so the same walk is seeded three ways.
fn assert_first_order_from(
    ir: &Ir,
    unrolled: &UnrolledBounds,
    mut formulas: Vec<FormulaId>,
    mut rels: Vec<RelExprId>,
    mut ints: Vec<IntExprId>,
) {
    let mut seen_f: BTreeSet<FormulaId> = BTreeSet::new();
    let mut seen_r: BTreeSet<RelExprId> = BTreeSet::new();
    let mut seen_i: BTreeSet<IntExprId> = BTreeSet::new();
    // One worklist loop over the three sorts; each pops whatever is available,
    // so nested formulas (an ITE condition, a comprehension body) re-enter.
    while !formulas.is_empty() || !rels.is_empty() || !ints.is_empty() {
        if let Some(f) = formulas.pop() {
            if !seen_f.insert(f) {
                continue;
            }
            match &ir.formulas[f].kind {
                FormulaKind::Const(_) | FormulaKind::LoopIs { .. } => {}
                FormulaKind::Not(a) => formulas.push(*a),
                FormulaKind::And(parts) | FormulaKind::Or(parts) => formulas.extend(parts),
                FormulaKind::Implies {
                    antecedent,
                    consequent,
                } => formulas.extend([*antecedent, *consequent]),
                FormulaKind::Iff(a, b) => formulas.extend([*a, *b]),
                FormulaKind::RelCompare { lhs, rhs, .. } => rels.extend([*lhs, *rhs]),
                FormulaKind::IntCompare { lhs, rhs, .. } => ints.extend([*lhs, *rhs]),
                FormulaKind::MultTest { expr, .. } => rels.push(*expr),
                FormulaKind::Quant { bound, body, .. } => {
                    rels.push(*bound);
                    formulas.push(*body);
                }
                FormulaKind::TemporalUnary { .. } | FormulaKind::TemporalBinary { .. } => {
                    unreachable!("a temporal formula node survived the LTL-on-lasso lowering")
                }
            }
            continue;
        }
        if let Some(r) = rels.pop() {
            if !seen_r.insert(r) {
                continue;
            }
            match &ir.rel_exprs[r].kind {
                RelExprKind::Relation(rel) => assert!(
                    !unrolled.is_unrolled(*rel),
                    "an un-unrolled variable relation survived the temporal lowering: {}",
                    ir.relations[*rel].name
                ),
                RelExprKind::Var(_) | RelExprKind::Const(_) => {}
                RelExprKind::Binary { lhs, rhs, .. } => rels.extend([*lhs, *rhs]),
                RelExprKind::Unary { expr, .. } => rels.push(*expr),
                RelExprKind::Prime(_) => {
                    unreachable!("a prime node survived the LTL-on-lasso lowering")
                }
                RelExprKind::IfThenElse {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    formulas.push(*cond);
                    rels.extend([*then_branch, *else_branch]);
                }
                RelExprKind::Comprehension { decls, body } => {
                    rels.extend(decls.iter().map(|d| d.bound));
                    formulas.push(*body);
                }
                RelExprKind::IntToAtom(ie) => ints.push(*ie),
            }
            continue;
        }
        if let Some(i) = ints.pop() {
            if !seen_i.insert(i) {
                continue;
            }
            match &ir.int_exprs[i].kind {
                IntExprKind::Const(_) => {}
                IntExprKind::Card(r) | IntExprKind::AtomToInt(r) => rels.push(*r),
                IntExprKind::Neg(ie) => ints.push(*ie),
                IntExprKind::Binary { lhs, rhs, .. } => ints.extend([*lhs, *rhs]),
                IntExprKind::Sum { bound, body, .. } => {
                    rels.push(*bound);
                    ints.push(*body);
                }
                IntExprKind::IfThenElse {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    formulas.push(*cond);
                    ints.extend([*then_branch, *else_branch]);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn timeline_without_past_operators_is_the_bare_trace() {
        let line = Timeline::new(4, 2, 0);
        assert_eq!(line.states, vec![0, 1, 2, 3]);
        assert_eq!(line.loop_at, 2);
        assert_eq!(line.succ(3), 2);
        assert_eq!(line.succ(0), 1);
    }

    #[test]
    fn timeline_unrolls_the_loop_once_per_past_level() {
        let line = Timeline::new(3, 1, 1);
        assert_eq!(line.states, vec![0, 1, 2, 1, 2]);
        // The loop closes on the start of the last (fixpoint) copy.
        assert_eq!(line.loop_at, 3);
        assert_eq!(line.states[line.loop_at], 1);
        assert_eq!(line.succ(4), 3);

        let deeper = Timeline::new(3, 1, 2);
        assert_eq!(deeper.states, vec![0, 1, 2, 1, 2, 1, 2]);
        assert_eq!(deeper.loop_at, 5);
    }

    #[test]
    fn a_single_state_trace_loops_onto_itself() {
        let line = Timeline::new(1, 0, 0);
        assert_eq!(line.states, vec![0]);
        assert_eq!(line.succ(0), 0);
        assert_eq!(line.reachable(0), vec![0]);
        assert_eq!(line.future_path(0), vec![0, 0]);
    }

    #[test]
    fn reachable_is_the_ascending_future_set() {
        let line = Timeline::new(4, 1, 0);
        assert_eq!(line.reachable(2), vec![1, 2, 3]);
        assert_eq!(line.reachable(0), vec![0, 1, 2, 3]);
        // The future path keeps the traversal order (and its duplicates), which
        // is what `until` needs.
        assert_eq!(line.future_path(2), vec![2, 3, 1, 2, 3]);
    }

    #[test]
    fn past_path_is_most_recent_first() {
        assert_eq!(Timeline::past_path(0), vec![0]);
        assert_eq!(Timeline::past_path(3), vec![3, 2, 1, 0]);
    }

    /// A fragment with no past operator cannot tell one pass from another, so
    /// every time index collapses onto the first pass — which is exactly the
    /// physical state the pinned wrap rule names.
    #[test]
    fn without_past_operators_a_time_index_is_just_its_state() {
        for (k, l) in [(2, 0), (3, 1), (3, 2), (1, 0)] {
            for state in 0..12 {
                assert_eq!(
                    logical_time(state, k, l, 0),
                    crate::temporal_solve::normalize_state(
                        i64::try_from(state).unwrap_or(i64::MAX),
                        k,
                        l
                    ),
                    "k={k} l={l} state={state}"
                );
            }
        }
    }

    /// With past operators the index keeps its pass — up to the fragment's own
    /// past depth, past which every pass agrees (module docs' stability
    /// argument, and probe P-068-1's states 5..8).
    #[test]
    fn a_time_index_keeps_its_pass_up_to_the_past_depth() {
        // k=2, l=0: the timeline is [0,1] ++ [0,1], loop back at index 2.
        let line = Timeline::new(2, 0, 1);
        assert_eq!(line.states, vec![0, 1, 0, 1]);
        assert_eq!(logical_time(0, 2, 0, 1), 0);
        assert_eq!(logical_time(1, 2, 0, 1), 1);
        assert_eq!(logical_time(2, 2, 0, 1), 2);
        assert_eq!(logical_time(3, 2, 0, 1), 3);
        // Deeper passes fold onto the last copy, keeping the physical state.
        for state in [4, 6, 8, 100] {
            assert_eq!(logical_time(state, 2, 0, 1), 2, "state={state}");
        }
        for state in [5, 7, 9, 101] {
            assert_eq!(logical_time(state, 2, 0, 1), 3, "state={state}");
        }

        // Two extra copies keep two passes apart before folding.
        assert_eq!(logical_time(4, 2, 0, 2), 4);
        assert_eq!(logical_time(6, 2, 0, 2), 4);

        // A loop that is not at state 0: only `l..k` repeats.
        let line = Timeline::new(3, 2, 1);
        assert_eq!(line.states, vec![0, 1, 2, 2]);
        assert_eq!(logical_time(2, 3, 2, 1), 2);
        assert_eq!(logical_time(3, 3, 2, 1), 3);
        assert_eq!(logical_time(9, 3, 2, 1), 3);

        // Every result is a real index whose state is the pinned one.
        for k in 1..5usize {
            for l in 0..k {
                for depth in 0..3 {
                    let line = Timeline::new(k, l, depth);
                    for state in 0..20 {
                        let t = logical_time(state, k, l, depth);
                        assert!(t < line.len(), "k={k} l={l} d={depth} state={state}");
                        assert_eq!(
                            line.states[t],
                            crate::temporal_solve::normalize_state(
                                i64::try_from(state).unwrap_or(i64::MAX),
                                k,
                                l
                            ),
                            "k={k} l={l} d={depth} state={state}"
                        );
                    }
                }
            }
        }
    }
}
