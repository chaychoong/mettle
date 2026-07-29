//! The **backend instrument** seam ([ADR-0019](../../../docs/adr/0019-optional-cadical-backend.md)
//! stage 1, mt-089) — one lowered command, one CNF, two solvers.
//!
//! Gated behind the `cadical-instrument` cargo feature and **off by default**:
//! nothing here is reachable from [`solve_goal`](crate::solve_goal) or any
//! other shipped path, so the default build's behavior is unchanged by
//! construction, not by discipline.
//!
//! The point of the seam is that both backends are handed the **same
//! [`Translated`](crate::solve::Translated) CNF** — same bounds, same primary
//! numbering, same symmetry-breaking predicate, same encode budget — so a
//! verdict difference between them can only be a solver bug or a wiring bug,
//! never an encoding difference. ADR-0019 §4 makes that the free
//! oracle-independent check; here it is the stop-the-line rule for the
//! measurement.

#![allow(
    clippy::doc_markdown,
    reason = "\"CaDiCaL\" is the solver's own spelling — a proper noun with internal \
              capitals, which doc_markdown mistakes for an unlinked item path"
)]

use std::time::Instant;

use als_solve::{CadicalSolver, CdclSolver, Outcome};

use crate::bounds_builder::BoundsResult;
use crate::error::TranslateError;
use crate::ir::Ir;
use crate::lower::LoweredGoal;
use crate::scope::ScopedUniverse;
use crate::solve::{translate, SolveOptions};

/// Which SAT backend decides the CNF.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum InstrumentBackend {
    /// mettle's own CDCL — the default and the conformance yardstick.
    Cdcl,
    /// CaDiCaL, via the `cadical` binding (ADR-0019).
    Cadical,
}

impl InstrumentBackend {
    /// The artifact spelling.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            InstrumentBackend::Cdcl => "cdcl",
            InstrumentBackend::Cadical => "cadical",
        }
    }
}

/// A backend's answer, with budget-exhaustion kept distinct from a verdict —
/// the same three-way shape [`SolveVerdict`](crate::SolveVerdict) has.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum InstrumentVerdict {
    /// An instance exists (for a `check`, a counterexample).
    Sat,
    /// No instance within scope.
    Unsat,
    /// The conflict budget (or, CaDiCaL-only, the wall deadline) ran out —
    /// not a verdict.
    Unknown,
}

impl InstrumentVerdict {
    /// The artifact spelling.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            InstrumentVerdict::Sat => "sat",
            InstrumentVerdict::Unsat => "unsat",
            InstrumentVerdict::Unknown => "unknown",
        }
    }
}

/// One instrumented solve: the verdict plus the measurements a per-row table
/// needs.
///
/// `conflicts_used` is `Some` only for the own CDCL: the `cadical` binding
/// exposes `limit("conflicts", n)` but no conflict *counter*, so CaDiCaL's
/// spend is genuinely unobservable through this seam (recorded as a gap, not
/// guessed).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct InstrumentOutcome {
    /// The backend's answer.
    pub verdict: InstrumentVerdict,
    /// CNF size — identical across backends for the same row, and the check
    /// that they really did see the same encoding.
    pub num_vars: u32,
    /// Clause count of the shared CNF.
    pub num_clauses: usize,
    /// Conflicts analyzed, when the backend exposes the counter.
    pub conflicts_used: Option<u64>,
    /// Wall milliseconds spent inside `translate` (encode).
    pub encode_ms: u128,
    /// Wall milliseconds spent inside the solver.
    pub solve_ms: u128,
    /// The [`self_check`](crate::self_check) failure for a SAT answer, if any
    /// — a nonempty value is a mettle bug regardless of which backend found
    /// the instance.
    pub self_check_fail: Option<String>,
}

/// Encodes one lowered command exactly as [`solve_goal`](crate::solve_goal)
/// would, then decides it with `backend`.
///
/// `wall_secs` is a per-solve deadline honored by the **CaDiCaL** backend only
/// (via its termination callback); the own CDCL has no wall hook, so a `Cdcl`
/// run must be bounded by its conflict budget and, if a hard cap is needed, by
/// the caller's own process timeout. Wall time never enters a verdict —
/// exceeding it reports [`InstrumentVerdict::Unknown`], the same
/// non-answer a spent conflict budget gives (STYLE D1).
///
/// # Errors
/// The same typed errors as [`solve_goal`](crate::solve_goal): a construct
/// outside the encoder slice, or [`TranslateError::CapacityExceeded`] when the
/// encode budget is outgrown.
pub fn solve_goal_with_backend(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    opts: &SolveOptions,
    backend: InstrumentBackend,
    wall_secs: Option<f32>,
) -> Result<InstrumentOutcome, TranslateError> {
    let encode_started = Instant::now();
    let t = translate(ir, scoped, goal, bounds, None, *opts)?;
    let encode_ms = encode_started.elapsed().as_millis();
    let budget = opts.conflict_budget.unwrap_or(u64::MAX);

    let mut out = InstrumentOutcome {
        verdict: InstrumentVerdict::Unsat,
        num_vars: t.cnf.num_vars(),
        num_clauses: t.cnf.clauses().len(),
        conflicts_used: None,
        encode_ms,
        solve_ms: 0,
        self_check_fail: None,
    };
    if t.trivially_unsat {
        return Ok(out);
    }

    let solve_started = Instant::now();
    let (answer, conflicts_used) = match backend {
        InstrumentBackend::Cdcl => {
            let mut solver = CdclSolver::new(&t.cnf);
            let answer = solver.solve_within(budget);
            (answer, Some(solver.total_conflicts()))
        }
        InstrumentBackend::Cadical => {
            let mut solver = CadicalSolver::new(&t.cnf);
            solver.set_wall_limit(wall_secs);
            (solver.solve_within(budget), None)
        }
    };
    out.solve_ms = solve_started.elapsed().as_millis();
    out.conflicts_used = conflicts_used;

    out.verdict = match answer {
        None => InstrumentVerdict::Unknown,
        Some(Outcome::Unsat) => InstrumentVerdict::Unsat,
        Some(Outcome::Sat(model)) => {
            // Every SAT answer is re-evaluated against the whole goal, in any
            // build: a cross-backend instrument is only as trustworthy as its
            // weakest model decode, and this is the one check that catches a
            // mis-decoded CaDiCaL model before it becomes a "verdict".
            let inst = crate::solve::decode(&t.layout, &t.universe, &model);
            out.self_check_fail = crate::eval::self_check(ir, scoped, goal, &inst, opts, &t.bounds)
                .err()
                .map(|f| f.to_string());
            InstrumentVerdict::Sat
        }
    };
    Ok(out)
}
