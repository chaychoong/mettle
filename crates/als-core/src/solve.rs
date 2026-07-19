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
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
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
    /// Cumulative SAT-conflict budget across an **entire enumeration** (every
    /// instance solve [`enumerate`] performs, summed); `None` (default) =
    /// unbudgeted. Deterministic like [`Self::conflict_budget`] (conflict-counted,
    /// never wall-clock), but a different knob: `conflict_budget` bounds one
    /// *verdict* solve, while this bounds the *total* effort of a whole
    /// enumeration. Enumeration is exact by contract (see
    /// [`InstanceEnumerator`] docs) — a budget-truncated count would be a
    /// silently wrong answer, so this never truncates the count. Instead, when
    /// the budget runs out mid-enumeration, the enumerator stops and reports
    /// itself [`InstanceEnumerator::exhausted`], so a caller (the SB-0 counting
    /// net) can skip the command typed rather than either hang or fabricate a
    /// count.
    pub enum_conflict_budget: Option<u64>,
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
) {
    #[cfg(debug_assertions)]
    if let Err(failure) = self_check(ir, scoped, goal, inst, &opts) {
        debug_assert!(false, "self-check failed (a mettle bug): {failure}");
    }
    #[cfg(not(debug_assertions))]
    {
        let _ = (ir, scoped, goal, inst, opts);
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
    let (goal_bool, mut cnf) = encoder.finish_goal(goal.goal)?;

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
                debug_self_check(ir, scoped, goal, &inst, *opts);
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
/// The separate [`SolveOptions::enum_conflict_budget`] bounds the TOTAL effort
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
    /// Remaining cumulative conflicts before [`SolveOptions::enum_conflict_budget`]
    /// is exhausted; `None` = unbudgeted (charge nothing, never exhaust).
    budget_remaining: Option<u64>,
    /// Set once `budget_remaining` hits zero mid-enumeration: the sequence
    /// stopped short of `Unsat`, so its count is a **lower bound**, not exact.
    exhausted: bool,
}

impl InstanceEnumerator<'_> {
    /// Whether the enumeration stopped because
    /// [`SolveOptions::enum_conflict_budget`] ran out (rather than reaching a
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
            let before = self.solver.total_conflicts();
            let Some(outcome) = self.solver.solve_within(remaining) else {
                // Budget exhausted mid-enumeration: stop short, loudly.
                self.exhausted = true;
                self.done = true;
                return None;
            };
            let spent = self.solver.total_conflicts().saturating_sub(before);
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
                debug_self_check(self.ir, self.scoped, self.goal, &inst, self.opts);
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
        budget_remaining: opts.enum_conflict_budget,
        exhausted: false,
    })
}
