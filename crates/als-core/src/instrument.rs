//! The **backend instrument** seam ([ADR-0019](../../../docs/adr/0019-optional-cadical-backend.md)
//! stage 1, mt-089) — one lowered command, one CNF, measured on the way to a
//! verdict.
//!
//! A dev instrument, not a shipped path: nothing here is reachable from
//! [`solve_goal`](crate::solve_goal) or from the CLI, and its only caller is
//! `als-conform`'s `backend-instrument` bin. It was gated behind the
//! `cadical-instrument` cargo feature until mt-121, which retired the feature
//! along with the optional backend (ADR-0027); the isolation is now structural
//! (nothing calls it) rather than conditional compilation.
//!
//! Two entry points, both encoding the goal exactly as the shipped path would:
//!
//! - [`solve_goal_instrumented`] decides one command and reports what it cost —
//!   CNF size, conflicts, encode and solve milliseconds — which is what turns
//!   "how much of the defer tail is genuinely hard" into a measurement. It is
//!   also the only route to a **wall deadline** on a solve, which the shipped
//!   seam deliberately withholds (a clock must never reach a verdict, STYLE D1:
//!   exceeding it reports [`InstrumentVerdict::Unknown`], the same non-answer a
//!   spent conflict budget gives).
//! - [`certify_goal`] points the same seam at a stronger question
//!   ([ADR-0027](../../../docs/adr/0027-cadical-only-solver.md) decision 4,
//!   mt-123): CaDiCaL logs a **DRAT proof** of its UNSAT verdict, which an
//!   external checker verifies against the DIMACS form of the very CNF that was
//!   solved. It replaced the cross-backend arm this module opened with — two
//!   solvers agreeing was evidence, a checked proof is a proof — and it outlived
//!   it, since mt-124 deleted the second solver (ADR-0027 decision 3).

#![allow(
    clippy::doc_markdown,
    reason = "\"CaDiCaL\" is the solver's own spelling — a proper noun with internal \
              capitals, which doc_markdown mistakes for an unlinked item path"
)]

use std::io;
use std::path::{Path, PathBuf};
use std::time::Instant;

use als_solve::{write_dimacs_file, CadicalSolver, Outcome, ProofTraceError};
use thiserror::Error;

use crate::bounds_builder::BoundsResult;
use crate::error::TranslateError;
use crate::ir::Ir;
use crate::lower::LoweredGoal;
use crate::scope::ScopedUniverse;
use crate::solve::{translate, SolveOptions, Translated};

/// A backend's answer, with budget-exhaustion kept distinct from a verdict —
/// the same three-way shape [`SolveVerdict`](crate::SolveVerdict) has.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum InstrumentVerdict {
    /// An instance exists (for a `check`, a counterexample).
    Sat,
    /// No instance within scope.
    Unsat,
    /// The conflict budget, or the instrument's wall deadline, ran out — not a
    /// verdict.
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
/// `conflicts_used` is `Some` since mt-121: the vendored binding exposes
/// CaDiCaL's own conflict counter, so "where did the budget go" is a
/// measurement rather than the blank ADR-0019 had to record. It stays an
/// `Option` because a future backend without counters would land there
/// ([`Backend::reports_effort`](als_solve::Backend::reports_effort)), reported
/// as absent rather than as a fake zero.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct InstrumentOutcome {
    /// The solver's answer.
    pub verdict: InstrumentVerdict,
    /// CNF size — a property of the encoding, so it is also the check that a
    /// re-run of this row really did see the same problem.
    pub num_vars: u32,
    /// Clause count of the same CNF.
    pub num_clauses: usize,
    /// Conflicts analyzed, when the backend exposes the counter.
    pub conflicts_used: Option<u64>,
    /// Wall milliseconds spent inside `translate` (encode).
    pub encode_ms: u128,
    /// Wall milliseconds spent inside the solver.
    pub solve_ms: u128,
    /// The [`self_check`](crate::self_check) failure for a SAT answer, if any —
    /// a nonempty value is a mettle bug, always.
    pub self_check_fail: Option<String>,
}

/// Encodes one lowered command exactly as [`solve_goal`](crate::solve_goal)
/// would, then decides it and reports what that cost.
///
/// `wall_secs` is a per-solve deadline, delivered through CaDiCaL's termination
/// callback. It exists here and nowhere on the shipped path on purpose: wall
/// time never enters a verdict (STYLE D1/D4), so exceeding it reports
/// [`InstrumentVerdict::Unknown`] — the same non-answer a spent conflict budget
/// gives — and a run that needs a hard ceiling still wants the conflict budget
/// as well.
///
/// # Errors
/// The same typed errors as [`solve_goal`](crate::solve_goal): a construct
/// outside the encoder slice, or [`TranslateError::CapacityExceeded`] when the
/// encode budget is outgrown.
pub fn solve_goal_instrumented(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    opts: &SolveOptions,
    wall_secs: Option<f32>,
) -> Result<InstrumentOutcome, TranslateError> {
    let encode_started = Instant::now();
    let t = translate(ir, scoped, goal, bounds, None, *opts)?;
    let encode_ms = encode_started.elapsed().as_millis();
    Ok(decide(
        &t,
        Decide {
            ir,
            scoped,
            goal,
            opts,
            wall_secs,
            encode_ms,
        },
    ))
}

/// What one certified solve measured, whatever verdict it reached.
///
/// The same numbers [`InstrumentOutcome`] carries, minus the ones with no
/// meaning here: a certified solve is never budget-blind about its conflicts,
/// and it never self-checks a model because the answer it is about is UNSAT.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct CertifyMeasurements {
    /// CNF size — the pool the DIMACS header declares.
    pub num_vars: u32,
    /// Clause count of the CNF written out for the checker.
    pub num_clauses: usize,
    /// Conflicts CaDiCaL analyzed reaching this answer.
    pub conflicts_used: u64,
    /// Wall milliseconds spent inside `translate` (encode).
    pub encode_ms: u128,
    /// Wall milliseconds spent inside the solver.
    pub solve_ms: u128,
}

/// What [`certify_goal`] found, with the two non-answers kept apart from the
/// two verdicts.
///
/// [`Self::Sat`] is not a failure and not a certificate: a worklist aimed at
/// UNSAT rows that comes back SAT is either a mispiped bucket or real drift
/// since the sweep that produced it, and both are things a report has to show
/// rather than swallow.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum CertifyOutcome {
    /// The goal folded to `false` while encoding, so the formula is UNSAT by
    /// construction and no solver ever ran. Nothing is written — there is no
    /// CNF to check and no proof to check it with — and the caller reports it
    /// as its own bucket rather than as a certified proof it does not have.
    TriviallyUnsat,
    /// UNSAT, with a DRAT proof at the caller's `proof_path` and the matching
    /// DIMACS at its `cnf_path`.
    Unsat(CertifyMeasurements),
    /// Satisfiable — nothing to certify (a proof of unsatisfiability is the
    /// only thing DRAT expresses).
    Sat(CertifyMeasurements),
    /// The conflict budget ran out. Not a verdict, so not a certificate either;
    /// the partial proof on disk refutes nothing and the caller deletes it.
    Unknown(CertifyMeasurements),
}

impl CertifyOutcome {
    /// The artifact spelling.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            CertifyOutcome::TriviallyUnsat => "trivially_unsat",
            CertifyOutcome::Unsat(_) => "unsat",
            CertifyOutcome::Sat(_) => "sat",
            CertifyOutcome::Unknown(_) => "unknown",
        }
    }

    /// The measurements, when a solver actually ran.
    #[must_use]
    pub fn measurements(self) -> Option<CertifyMeasurements> {
        match self {
            CertifyOutcome::TriviallyUnsat => None,
            CertifyOutcome::Unsat(m) | CertifyOutcome::Sat(m) | CertifyOutcome::Unknown(m) => {
                Some(m)
            }
        }
    }
}

/// Why a row could not be certified at all — distinct from *what* certifying it
/// found ([`CertifyOutcome`]).
///
/// A separate enum from [`TranslateError`] because two of the three ways this
/// can fail are not translation failures and cannot be spelled as one: opening
/// a proof trace and writing a CNF file are I/O, and an I/O failure that got
/// flattened into "encode failed" would send a reader hunting through the
/// encoder for a missing directory (STYLE E1/E4).
#[derive(Debug, Error)]
pub enum CertifyError {
    /// The goal could not be encoded — including
    /// [`TranslateError::CapacityExceeded`], which the caller buckets as the
    /// same capacity defer the gauge uses.
    #[error(transparent)]
    Translate(#[from] TranslateError),
    /// CaDiCaL refused to open the proof trace, so no certificate could be
    /// produced. Never a solve that runs untraced (see
    /// [`CadicalSolver::with_proof_trace`]).
    #[error("cannot certify: {0}")]
    ProofTrace(#[from] ProofTraceError),
    /// The DIMACS form of the CNF could not be written, so the checker would
    /// have had nothing to check the proof against.
    #[error("writing the DIMACS CNF to `{path}`: {source}")]
    CnfWrite {
        /// The path that could not be written.
        path: PathBuf,
        /// The underlying I/O failure.
        source: io::Error,
    },
}

/// Encodes one lowered command exactly as [`solve_goal`](crate::solve_goal)
/// would, writes that CNF to `cnf_path` as DIMACS, and decides it with CaDiCaL
/// logging a DRAT proof to `proof_path` — the ADR-0027 decision-4 certificate.
///
/// The pair of files is the whole product: a DRAT proof is meaningless without
/// the formula it refutes, and it refutes *this* CNF in *this* numbering, which
/// is why the same `Translated` feeds both the file and the solver.
///
/// **Static goals only.** `unrolled` is `None`, so a temporal command — whose
/// pipeline is a per-length sweep rather than one translate — must be screened
/// out by the caller *before* it gets here. Certifying "some length" would
/// certify a formula no verdict was ever read from.
///
/// What a verified proof does and does not claim is worth stating plainly: it
/// establishes that **this CNF is unsatisfiable**, nothing more. That the CNF is
/// the right encoding of the Alloy command remains the job of the self-check
/// and of jar agreement — the proof cannot see the model it came from.
///
/// Wall times are measurements only; nothing here reads the clock to decide
/// anything (STYLE D1/D4).
///
/// # Errors
/// [`CertifyError`]: an unencodable goal (including capacity), a proof trace
/// CaDiCaL will not open, or a CNF file that cannot be written.
pub fn certify_goal(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    opts: &SolveOptions,
    cnf_path: &Path,
    proof_path: &Path,
) -> Result<CertifyOutcome, CertifyError> {
    let encode_started = Instant::now();
    let t = translate(ir, scoped, goal, bounds, None, *opts)?;
    let encode_ms = encode_started.elapsed().as_millis();
    debug_assert!(
        t.lasso.is_none(),
        "certify_goal translates the static path only: a lasso selector means a \
         temporal goal reached it unscreened"
    );

    // Ordered before the file write on purpose: a goal that folded to `false`
    // has no CNF worth checking, and writing an empty-clause DIMACS plus a
    // zero-length proof would dress an encode-time truth up as a checked one.
    if t.trivially_unsat {
        return Ok(CertifyOutcome::TriviallyUnsat);
    }

    write_dimacs_file(&t.cnf, cnf_path).map_err(|source| CertifyError::CnfWrite {
        path: cnf_path.to_path_buf(),
        source,
    })?;
    let mut solver = CadicalSolver::with_proof_trace(&t.cnf, proof_path)?;

    let solve_started = Instant::now();
    let answer = solver.solve_within(opts.conflict_budget.unwrap_or(u64::MAX));
    let solve_ms = solve_started.elapsed().as_millis();
    // Closed on every path, not just the UNSAT one: CaDiCaL buffers proof lines,
    // and a dropped-but-unclosed tracer leaves a truncated file behind that a
    // checker would reject as a broken proof rather than report as absent.
    solver.flush_proof_trace();
    solver.close_proof_trace();

    let measurements = CertifyMeasurements {
        num_vars: t.cnf.num_vars(),
        num_clauses: t.cnf.clauses().len(),
        conflicts_used: solver.total_conflicts(),
        encode_ms,
        solve_ms,
    };
    Ok(match answer {
        None => CertifyOutcome::Unknown(measurements),
        Some(Outcome::Sat(_)) => CertifyOutcome::Sat(measurements),
        Some(Outcome::Unsat) => CertifyOutcome::Unsat(measurements),
    })
}

/// Everything [`decide`] needs besides the encoded CNF — bundled so a caller
/// builds it once and cannot pass the pieces in inconsistently.
#[derive(Copy, Clone)]
struct Decide<'a> {
    ir: &'a Ir,
    scoped: &'a ScopedUniverse,
    goal: &'a LoweredGoal,
    opts: &'a SolveOptions,
    wall_secs: Option<f32>,
    encode_ms: u128,
}

/// Decides one already-encoded CNF, self-checking any SAT answer. The CNF is
/// borrowed rather than re-derived, so the measurement is about the encoding the
/// caller built and not a second one that merely ought to match it.
fn decide(t: &Translated, cx: Decide<'_>) -> InstrumentOutcome {
    let Decide {
        ir,
        scoped,
        goal,
        opts,
        wall_secs,
        encode_ms,
    } = cx;
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
        return out;
    }

    // Constructed here rather than through `LiveSolver` because this module
    // needs two things the shipped seam deliberately does not expose: a
    // *conflict* count on its own, rather than the three-term effort sum, and
    // CaDiCaL's wall-clock termination hook.
    let solve_started = Instant::now();
    let mut solver = CadicalSolver::new(&t.cnf);
    solver.set_wall_limit(wall_secs);
    let answer = solver.solve_within(budget);
    out.solve_ms = solve_started.elapsed().as_millis();
    out.conflicts_used = Some(solver.total_conflicts());

    out.verdict = match answer {
        None => InstrumentVerdict::Unknown,
        Some(Outcome::Unsat) => InstrumentVerdict::Unsat,
        Some(Outcome::Sat(model)) => {
            // Every SAT answer is re-evaluated against the whole goal, in any
            // build: an instrument is only as trustworthy as its model decode,
            // and this is the one check that catches a mis-decoded model before
            // it becomes a "verdict".
            let inst = crate::solve::decode(&t.layout, &t.universe, &model);
            out.self_check_fail = crate::eval::self_check(ir, scoped, goal, &inst, opts, &t.bounds)
                .err()
                .map(|f| f.to_string());
            InstrumentVerdict::Sat
        }
    };
    out
}
