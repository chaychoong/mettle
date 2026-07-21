//! The solve driver: bounded IR → CNF → verdict / instances (mt-033,
//! translation-ref §4).
//!
//! This is the phase-4 seam ADR-0011 names: it mints the primary variables in
//! the pinned order (decision 3), hands the goal to the [`crate::encode`]r, drives
//! the [`als_solve::CdclSolver`], and decodes an [`Assignment`](als_solve::Assignment)
//! back into an [`Instance`] over the command's [`Universe`]. It is the point
//! where mettle produces its first real **SAT/UNSAT verdicts** and instances.
//!
//! - [`solve_goal`] returns the first verdict ([`SolveVerdict`]).
//! - [`enumerate`] returns an [`InstanceEnumerator`] yielding **distinct
//!   instances** (distinct projections onto the primary variables) in a
//!   deterministic order — the SB-0 counting-net primitive (translation-ref
//!   §4.5): the enumerator blocks each found model over the **primary variables
//!   only**, never the Tseitin auxiliaries.
//!
//! Polarity (translation-ref §0/§4.3, for mt-036's CLI): the goal a `check`
//! command lowers to is the **negated** assertion, so `solve_goal` returning
//! [`SolveVerdict::Sat`] for a `check` means a **counterexample** was found, and
//! [`SolveVerdict::Unsat`] means the assertion holds within scope.

use std::collections::BTreeMap;

use als_solve::{block, Assignment, CdclSolver, Cnf, Outcome, Var};

use crate::bounds::{Bounds, Tuple, TupleSet, Universe};
use crate::bounds_builder::BoundsResult;
use crate::encode::{Bool, Encoder, PrimaryMap};
use crate::error::TranslateError;
#[cfg(debug_assertions)]
use crate::eval::self_check;
use crate::ir::{Ir, RelId};
use crate::lower::LoweredGoal;
use crate::scope::ScopedUniverse;

/// Solver knobs (translation-ref §2.4): the LEDGER-001 overflow switch plus the
/// **deterministic effort budgets**. Kept as a struct so mt-036/Rung-4 can
/// extend it without churning the driver signature.
///
/// `Default` is a **manual** impl (not derived) because [`Self::symmetry`]
/// defaults to **20** — the jar's `A4Options.symmetry` default (translation-ref
/// §16.4). Every other field is its type's own default (`false`/`None`), so the
/// only reason `Default` cannot be derived is that non-zero symmetry.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct SolveOptions {
    /// Whether integer overflow **wraps** (`true`) or **excludes the instance**.
    /// The default (`false`) is mettle's canonical **forbid** per LEDGER-001 —
    /// which is exactly `bool::default()`, so `Default` is derived.
    pub allow_overflow: bool,
    /// Maximum SAT conflicts [`solve_goal`] may analyze before giving up with
    /// [`SolveVerdict::Unknown`]; `None` (default) = unlimited. A **fixed
    /// function of the input** (STYLE D1), unlike a wall-clock timeout: the same
    /// goal with the same budget exhausts identically on every machine. When
    /// the budget stops a solve, all effort stops with it — nothing keeps
    /// allocating in the background (the mt-035 corpus-OOM lesson).
    pub conflict_budget: Option<u64>,
    /// Maximum **encode effort** — gate requests (folded or not), join
    /// pair-scans, and CNF clauses — before the encoder fails with
    /// [`TranslateError::CapacityExceeded`]; `None` (default) = unlimited. The
    /// grounding-side guard, bounding both memory *and time*: a goal whose
    /// primary-variable count looks small can still ground to a
    /// machine-exhausting CNF, and a constant-heavy goal can burn hours in a
    /// grounded walk that folds every gate away and would never trip a plain
    /// clause cap. Deterministic — a pure count of the traversal (STYLE D1).
    pub encode_budget: Option<u64>,
    /// Cumulative **effort** budget across an **entire enumeration** (every
    /// instance solve [`enumerate`] performs, summed), where effort = SAT
    /// **conflicts + branching decisions + propagation clause-visits**;
    /// `None` (default) = unbudgeted. Propagation visits are the term that
    /// makes the budget bind wall time: enumeration over a big-but-easy CNF is
    /// *propagation-bound* — thousands of near-conflict-free solves whose cost
    /// neither a conflict count nor a decision count sees, because each single
    /// step drags huge watch lists and accumulated blocking clauses (the two
    /// mt-047 counting-net grinds). Deterministic like
    /// [`Self::conflict_budget`] (effort-counted, never wall-clock), but a
    /// different knob: `conflict_budget` bounds one *verdict* solve, while this
    /// bounds the *total* effort of a whole enumeration. Enumeration is exact
    /// by contract (see
    /// [`InstanceEnumerator`] docs) — a budget-truncated count would be a
    /// silently wrong answer, so this never truncates the count. Instead, when
    /// the budget runs out mid-enumeration, the enumerator stops and reports
    /// itself [`InstanceEnumerator::exhausted`], so a caller (the SB-0 counting
    /// net) can skip the command typed rather than either hang or fabricate a
    /// count.
    pub enum_effort_budget: Option<u64>,
    /// Symmetry-breaking predicate length cap (translation-ref §3/§16, the jar's
    /// `A4Options.symmetry` / Kodkod `Options.symmetryBreaking`): the bound on the
    /// number of `(original, permuted)` boolean pairs generated **per symmetry
    /// class adjacent-atom pair**. Default **20** (the jar's own default — a
    /// drop-in). `0` disables symmetry breaking entirely (the ADR-0002 SB-0
    /// counting regime, mettle's original no-SB behavior). A lex-leader predicate
    /// only removes isomorphic copies of satisfying assignments, so this **never
    /// changes the SAT/UNSAT verdict** — it changes the enumerated (SB-quotiented)
    /// instance count and solve performance. The primary-variable set is untouched
    /// (the SBP adds only Tseitin auxiliaries), so instance decoding is unaffected.
    ///
    /// **`expect 1` forces this to 0** at every jar-comparing command boundary
    /// (translation-ref §3, §16.4): the jar's `A4Solution` does `int sym =
    /// (expected == 1 ? 0 : opt.symmetry)`, so a command annotated `expect 1`
    /// enumerates the raw (SB-0) count. Callers that compare against the jar apply
    /// that override before handing the options here.
    pub symmetry: u32,
}

impl Default for SolveOptions {
    /// The jar-matching defaults: forbid overflow (LEDGER-001), no effort budgets,
    /// and **symmetry 20** (translation-ref §16.4) — the one field that is not its
    /// type's own default.
    fn default() -> Self {
        Self {
            allow_overflow: false,
            conflict_budget: None,
            encode_budget: None,
            enum_effort_budget: None,
            symmetry: 20,
        }
    }
}

/// A solving verdict for one command.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SolveVerdict {
    /// Satisfiable, with a witnessing instance (a `run` instance or a `check`
    /// counterexample — see the module docs on polarity).
    Sat(Instance),
    /// Unsatisfiable (no `run` instance / no `check` counterexample).
    Unsat,
    /// No verdict: the [`SolveOptions::conflict_budget`] was exhausted first.
    /// Only reachable when a budget is set — an unbudgeted solve never returns
    /// this. Not a verdict about the model, and never conflated with one
    /// (STYLE E5); callers surface it as "gave up", the way the jar surfaces a
    /// solver timeout.
    Unknown,
}

/// A decoded instance: one concrete [`TupleSet`] per relation, over the command
/// universe.
///
/// Per ADR-0002 instance tuples are **never** diffed against the jar; this is for
/// display (mt-036), the evaluator self-check (mt-034), and the bounds-respect
/// property net. Relations iterate in `RelId` order (deterministic).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Instance {
    /// The atom universe the tuples range over.
    pub universe: Universe,
    rels: BTreeMap<RelId, TupleSet>,
}

impl Instance {
    /// The decoded value of `rel`, if present.
    #[must_use]
    pub fn get(&self, rel: RelId) -> Option<&TupleSet> {
        self.rels.get(&rel)
    }

    /// Iterates `(rel, tuples)` in `RelId` order.
    pub fn iter(&self) -> impl Iterator<Item = (RelId, &TupleSet)> {
        self.rels.iter().map(|(&r, ts)| (r, ts))
    }

    /// Builds an instance directly from a universe and per-relation values —
    /// for the evaluator differential (`tests/eval_differential.rs`) and future
    /// REPL construction. The solver's own instances come from [`decode`]; this
    /// is the constructor external callers need to hand the [`crate::eval`]uator
    /// a hand-built candidate. Relations are keyed in `RelId` order.
    #[must_use]
    pub fn from_relations(
        universe: Universe,
        rels: impl IntoIterator<Item = (RelId, TupleSet)>,
    ) -> Self {
        Instance {
            universe,
            rels: rels.into_iter().collect(),
        }
    }
}

/// Debug-only self-check (ADR-0011 decision 5, translation-ref §6): re-evaluate a
/// found instance against the **full goal** and fail loudly if it does not
/// satisfy its own formula — a mettle solver/encoder bug, never a user error.
/// Compiled out of release builds; [`crate::eval::self_check`] is the equivalent
/// checked-mode entry the differential and corpus tests call.
fn debug_self_check(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    inst: &Instance,
    opts: SolveOptions,
    bounds: &Bounds,
) {
    #[cfg(debug_assertions)]
    if let Err(failure) = self_check(ir, scoped, goal, inst, &opts, bounds) {
        debug_assert!(false, "self-check failed (a mettle bug): {failure}");
    }
    #[cfg(not(debug_assertions))]
    {
        let _ = (ir, scoped, goal, inst, opts, bounds);
    }
}

/// How to reconstruct one relation's [`TupleSet`] from an [`Assignment`]: its
/// fixed lower tuples plus each floating tuple gated by its primary variable.
#[derive(Debug)]
struct RelDecode {
    rel: RelId,
    arity: usize,
    lower: TupleSet,
    floating: Vec<(Tuple, Var)>,
}

/// The finished translation: CNF, primary variables (for blocking), the decode
/// layout, and the universe. `trivially_unsat` short-circuits an all-false goal.
#[derive(Debug)]
struct Translated {
    cnf: Cnf,
    primary_vars: Vec<Var>,
    layout: Vec<RelDecode>,
    universe: Universe,
    trivially_unsat: bool,
    /// The augmented bounds the encoder used (base bounds + skolem bounds), so the
    /// self-check evaluator shares the encoder's exact relation bounds for the
    /// (C) constant-escape predicate (translation-ref §10.7c ext, mt-051).
    bounds: Bounds,
}

/// Mints the primary variables (ADR-0011 decision 3) and builds the decode
/// layout for every bounded relation — referenced by the goal or not (the
/// equivalent of the reference's §2.5(4) reflexive `r = r` padding: every bounded
/// relation keeps its primary variables so unreferenced relations stay free, and
/// so enumeration counts match).
fn allocate_primaries(bounds: &Bounds, cnf: &mut Cnf) -> (PrimaryMap, Vec<Var>, Vec<RelDecode>) {
    let mut prim: PrimaryMap = BTreeMap::new();
    let mut primary_vars: Vec<Var> = Vec::new();
    let mut layout: Vec<RelDecode> = Vec::new();
    for (rel, bound) in bounds.iter() {
        let mut floating: Vec<(Tuple, Var)> = Vec::new();
        for t in bound.upper().iter() {
            if bound.lower().contains(t) {
                continue;
            }
            let var = cnf.fresh_var();
            prim.insert((rel, t.clone()), var);
            primary_vars.push(var);
            floating.push((t.clone(), var));
        }
        layout.push(RelDecode {
            rel,
            arity: bound.upper().arity(),
            lower: bound.lower().clone(),
            floating,
        });
    }
    (prim, primary_vars, layout)
}

/// Translates one lowered command goal to CNF (primary allocation + encoding).
fn translate(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    opts: SolveOptions,
) -> Result<Translated, TranslateError> {
    let mut cnf = Cnf::new();
    // Bind the goal's skolem relations (translation-ref §10.6): a higher-order
    // existential decl minted a free relation with lower `{}` and upper = the
    // sound abstract upper of its bound. Adding them to the bounds is the whole
    // seam — the primary allocator, encoder, decoder, and self-check treat a
    // skolem exactly like any other bounded relation (zero special-casing). Bound
    // by `RelId` (allocation, source-walk order), so numbering stays deterministic.
    let mut aug_bounds = bounds.bounds.clone();
    for (rel, bound) in &goal.skolem_bounds {
        aug_bounds.bind(*rel, bound.clone());
    }
    let (prim, primary_vars, layout) = allocate_primaries(&aug_bounds, &mut cnf);

    // Symmetry-breaking plan (translation-ref §16): the coarsest atom partition +
    // the post-skolem relation order for the lex-leader predicate. Built only when
    // symmetry breaking is on; the encoder conjoins it with the goal circuit
    // (unless the goal folded to a constant, §16.1.5). `expect 1`-forcing to
    // `symmetry = 0` happens at the command boundary (the CLI / gauge), so an
    // `opts.symmetry == 0` here means "no SBP" unconditionally.
    let sbp_plan = if opts.symmetry > 0 {
        // Every atom from the start of the int run to the end of the universe
        // (ints, then the string tail) is its own singleton class,
        // unconditionally (translation-ref §16.1.1, probes Y6/uf1-SB20/fmrun).
        let int_start = scoped.sig_atom_count;
        Some(crate::encode::symmetry::build_plan(
            ir,
            &aug_bounds,
            int_start,
        ))
    } else {
        None
    };

    let encoder = Encoder::new(
        ir,
        &aug_bounds,
        &prim,
        cnf,
        scoped.bitwidth,
        scoped.sig_atom_count,
        opts,
        bounds.int_sig,
        bounds.seq_int_sig,
    );
    let (goal_bool, mut cnf) = encoder.finish_goal(goal.goal, sbp_plan.as_ref(), opts.symmetry)?;

    let mut trivially_unsat = false;
    match goal_bool {
        Bool::Const(true) => {}
        Bool::Const(false) => trivially_unsat = true,
        Bool::Lit(l) => cnf.add_clause(vec![l]),
    }

    Ok(Translated {
        cnf,
        primary_vars,
        layout,
        universe: bounds.bounds.universe.clone(),
        trivially_unsat,
        bounds: aug_bounds,
    })
}

/// Decodes an assignment into an instance (STYLE I2 bounds-respect asserted).
fn decode(layout: &[RelDecode], universe: &Universe, assign: &Assignment) -> Instance {
    let mut rels: BTreeMap<RelId, TupleSet> = BTreeMap::new();
    for rd in layout {
        let mut ts = rd.lower.clone();
        debug_assert_eq!(ts.arity(), rd.arity, "lower/relation arity mismatch");
        for (tuple, var) in &rd.floating {
            if assign.value(*var) {
                ts.insert(tuple.clone());
            }
        }
        // Bounds-respect: lower ⊆ decoded ⊆ upper holds by construction (we start
        // from lower and only add floating tuples of the upper). Assert the lower
        // half, which the floating loop could not violate but a layout bug could.
        debug_assert!(
            rd.lower.is_subset_of(&ts),
            "decoded relation dropped a lower-bound tuple"
        );
        rels.insert(rd.rel, ts);
    }
    Instance {
        universe: universe.clone(),
        rels,
    }
}

/// Solves one lowered command, returning its first verdict (translation-ref §4).
///
/// # Errors
/// A [`TranslateError`] when the goal contains a construct outside the Rung-3
/// encoder slice (integer arithmetic / `sum` / int-`ITE`, or — as an internal
/// invariant failure — a temporal node), or [`TranslateError::CapacityExceeded`]
/// when a configured [`SolveOptions::clause_cap`] is outgrown; never a wrong
/// verdict (STYLE E5).
pub fn solve_goal(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    opts: &SolveOptions,
) -> Result<SolveVerdict, TranslateError> {
    let t = translate(ir, scoped, goal, bounds, *opts)?;
    if t.trivially_unsat {
        return Ok(SolveVerdict::Unsat);
    }
    let mut solver = CdclSolver::new(&t.cnf);
    Ok(
        match solver.solve_within(opts.conflict_budget.unwrap_or(u64::MAX)) {
            None => SolveVerdict::Unknown,
            Some(Outcome::Sat(model)) => {
                let inst = decode(&t.layout, &t.universe, &model);
                debug_self_check(ir, scoped, goal, &inst, *opts, &t.bounds);
                SolveVerdict::Sat(inst)
            }
            Some(Outcome::Unsat) => SolveVerdict::Unsat,
        },
    )
}

/// A deterministic enumerator over the **distinct instances** of one command
/// (translation-ref §4.5). Each [`InstanceEnumerator::next`] yields the next
/// instance and blocks its primary-variable projection; the sequence ends at the
/// first `Unsat`. Blocking over primary variables (never Tseitin auxiliaries)
/// makes the count the **raw / SB-0** model count (ADR-0002 counting net).
///
/// Enumeration is **exact by contract** and ignores
/// [`SolveOptions::conflict_budget`] (the per-solve verdict budget): a
/// budget-truncated enumeration would be a silently wrong count, the one thing
/// the counting net exists to prevent. The [`SolveOptions::encode_budget`]
/// guard *does* apply (it fails [`enumerate`] loudly at translate time,
/// corrupting nothing).
///
/// The separate [`SolveOptions::enum_effort_budget`] bounds the TOTAL effort
/// of the whole enumeration (summed across every instance solve), not any one
/// verdict. It never truncates the count silently: running out ends
/// enumeration in loud exhaustion ([`InstanceEnumerator::exhausted`]) instead
/// of a wrong number.
#[derive(Debug)]
pub struct InstanceEnumerator<'a> {
    solver: CdclSolver,
    primary_vars: Vec<Var>,
    layout: Vec<RelDecode>,
    universe: Universe,
    done: bool,
    // Self-check inputs (ADR-0011 decision 5): every enumerated SAT instance is
    // re-evaluated against the full goal (debug builds).
    ir: &'a Ir,
    scoped: &'a ScopedUniverse,
    goal: &'a LoweredGoal,
    opts: SolveOptions,
    /// The augmented bounds the encoder used, for the self-check evaluator's
    /// (C) constant-escape predicate (translation-ref §10.7c ext, mt-051).
    bounds: Bounds,
    /// Remaining cumulative effort (conflicts + decisions) before
    /// [`SolveOptions::enum_effort_budget`] is exhausted; `None` = unbudgeted
    /// (charge nothing, never exhaust).
    budget_remaining: Option<u64>,
    /// Set once `budget_remaining` hits zero mid-enumeration: the sequence
    /// stopped short of `Unsat`, so its count is a **lower bound**, not exact.
    exhausted: bool,
}

impl InstanceEnumerator<'_> {
    /// Whether the enumeration stopped because
    /// [`SolveOptions::enum_effort_budget`] ran out (rather than reaching a
    /// true `Unsat` and finishing exactly). Callers must check this before
    /// trusting a count from this enumerator.
    #[must_use]
    pub fn exhausted(&self) -> bool {
        self.exhausted
    }
}

impl Iterator for InstanceEnumerator<'_> {
    type Item = Instance;

    /// The next distinct instance, or `None` when the space is exhausted.
    fn next(&mut self) -> Option<Instance> {
        if self.done {
            return None;
        }
        let outcome = if let Some(remaining) = self.budget_remaining {
            // Effort = conflicts + decisions + propagation clause-visits. The
            // last is the term that actually tracks solver wall time: a
            // big-but-easy CNF enumerates through thousands of
            // near-conflict-free solves where each *step* is expensive (huge
            // watch lists, accumulated blocking clauses) — conflict and
            // decision counts both under-bill that mode (the two mt-047
            // counting-net grinds). A solve is only *interrupted* on the
            // conflict half (`solve_within`); the decision/propagation charge
            // lands between instance solves, which suffices — each individual
            // solve terminates in exactly the modes the other terms miss.
            if remaining == 0 {
                self.exhausted = true;
                self.done = true;
                return None;
            }
            let effort =
                |s: &CdclSolver| s.total_conflicts() + s.total_decisions() + s.total_props();
            let before = effort(&self.solver);
            let Some(outcome) = self.solver.solve_within(remaining) else {
                // Budget exhausted mid-enumeration: stop short, loudly.
                self.exhausted = true;
                self.done = true;
                return None;
            };
            let spent = effort(&self.solver).saturating_sub(before);
            self.budget_remaining = Some(remaining.saturating_sub(spent));
            outcome
        } else {
            self.solver.solve()
        };
        match outcome {
            Outcome::Unsat => {
                self.done = true;
                None
            }
            Outcome::Sat(model) => {
                let inst = decode(&self.layout, &self.universe, &model);
                debug_self_check(
                    self.ir,
                    self.scoped,
                    self.goal,
                    &inst,
                    self.opts,
                    &self.bounds,
                );
                let clause = block(&model, &self.primary_vars);
                if clause.is_empty() {
                    // No primary variables ⇒ a single distinguishable instance.
                    self.done = true;
                } else {
                    self.solver.add_clause(clause);
                }
                Some(inst)
            }
        }
    }
}

/// Builds an [`InstanceEnumerator`] for one lowered command.
///
/// # Errors
/// As [`solve_goal`] — a [`TranslateError`] for a construct outside the encoder
/// slice.
pub fn enumerate<'a>(
    ir: &'a Ir,
    scoped: &'a ScopedUniverse,
    goal: &'a LoweredGoal,
    bounds: &BoundsResult,
    opts: &SolveOptions,
) -> Result<InstanceEnumerator<'a>, TranslateError> {
    let t = translate(ir, scoped, goal, bounds, *opts)?;
    // A trivially-UNSAT goal (the encoded `Bool` folded to constant-false) gets an
    // empty clause, so the solver reports UNSAT on the first `next()` and the
    // enumerator terminates cleanly with no instances.
    let mut cnf = t.cnf;
    if t.trivially_unsat {
        cnf.add_clause(vec![]);
    }
    let solver = CdclSolver::new(&cnf);
    Ok(InstanceEnumerator {
        solver,
        primary_vars: t.primary_vars,
        layout: t.layout,
        universe: t.universe,
        done: false,
        ir,
        scoped,
        goal,
        opts: *opts,
        bounds: t.bounds,
        budget_remaining: opts.enum_effort_budget,
        exhausted: false,
    })
}
