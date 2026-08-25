//! The **CaDiCaL** backend ([ADR-0019](../../../docs/adr/0019-optional-cadical-backend.md),
//! mt-089) — the implementation of this crate's SAT boundary that mettle ships,
//! compiled into every build as of
//! [ADR-0027](../../../docs/adr/0027-cadical-only-solver.md) (mt-121) and the
//! only one left since mt-124.
//!
//! Its determinism is **by pinning** rather than by construction (ADR-0019 §1):
//! CaDiCaL's inprocessing and its own heuristics own the search, so nothing
//! about the *arithmetic* guarantees byte-identity. What ADR-0027's spike
//! measured instead is that a pinned build reproduces itself exactly, across
//! repeated runs, job counts and instruction sets.
//!
//! The mapping onto the trait boundary is one-to-one:
//!
//! | mettle | CaDiCaL (IPASIR) |
//! |---|---|
//! | [`Cnf`] variable `i` (0-based) | DIMACS literal `i + 1` |
//! | [`Lit`] negation | DIMACS sign |
//! | [`CadicalSolver::add_clause`] between solves (the enumeration seam) | `ipasir_add`, incrementally |
//! | [`CadicalSolver::solve_within`] conflict budget | `ccadical_limit("conflicts", n)` |
//! | [`Outcome::Sat`] / [`Outcome::Unsat`] / budget-out | `Some(true)` / `Some(false)` / `None` |
//! | [`CadicalSolver::total_conflicts`] and siblings | `Internal::stats`, via the vendored accessors |
//! | [`CadicalSolver::with_proof_trace`] | `Solver::trace_proof`, in the CONFIGURING state |
//!
//! The literal mapping itself lives in [`crate::dimacs`], shared with the DIMACS
//! writer: a proof trace is only checkable against the formula written out in
//! the *same* numbering the solver was loaded with (mt-123).
//!
//! ADR-0019 recorded one contract gap here: the published binding exposes no
//! conflict *counter*, so budgets bound but spend was unobservable. The fork in
//! `vendor/cadical` closes it — the three `total_*` methods read CaDiCaL's own
//! `Internal::stats` — and adds the proof tracer the same wall hid. Both are
//! documented in `vendor/README.md`.

#![allow(
    clippy::doc_markdown,
    reason = "\"CaDiCaL\" is the solver's own spelling — a proper noun with internal \
              capitals, which doc_markdown mistakes for an unlinked item path; \
              backticking a product name everywhere it appears would be worse prose"
)]

use std::fmt;
use std::path::{Path, PathBuf};

use crate::dimacs::dimacs_lit as dimacs;
use crate::{Assignment, Cnf, Lit, Outcome, Solver, Var};

/// CaDiCaL's own "no conflict limit" sentinel: `Internal::limit_conflicts`
/// treats any negative value as unlimited (`limit.cpp`).
const UNLIMITED_CONFLICTS: i32 = -1;

/// An incremental CaDiCaL instance holding one [`Cnf`], presenting exactly the
/// surface [`LiveSolver`](crate::LiveSolver) dispatches to — so a second
/// backend plugged in beside it is interchangeable at every call site.
pub struct CadicalSolver {
    inner: cadical::Solver<cadical::Timeout>,
    num_vars: u32,
    /// Per-solve wall limit in seconds, `None` = unbounded. Held here (rather
    /// than installed once) because `cadical::Timeout` restarts its clock on
    /// each `solve`, so the callback has to be re-armed per call to mean "this
    /// solve gets N seconds".
    wall_limit: Option<f32>,
    /// Whether a proof trace opened by [`CadicalSolver::with_proof_trace`] is
    /// still open. Tracked rather than asked of CaDiCaL because its flush/close
    /// contracts are enforced by **aborting the process**: flushing a solver
    /// that is not tracing, or closing one twice, is fatal, so the pass-throughs
    /// consult this flag instead of trusting the caller.
    proof_trace_open: bool,
}

impl fmt::Debug for CadicalSolver {
    /// Hand-written because `cadical::Solver` is an opaque FFI handle with no
    /// `Debug` — the useful shape is the problem size, not the pointer.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CadicalSolver")
            .field("num_vars", &self.num_vars)
            .field("num_clauses", &self.inner.num_clauses())
            .field("wall_limit", &self.wall_limit)
            .field("proof_trace_open", &self.proof_trace_open)
            .finish()
    }
}

impl CadicalSolver {
    /// Loads `cnf` into a fresh CaDiCaL instance, in clause order.
    #[must_use]
    pub fn new(cnf: &Cnf) -> Self {
        Self::load(cadical::Solver::new(), cnf, false)
    }

    /// Loads `cnf` into a fresh CaDiCaL instance that writes a DRAT proof of an
    /// UNSAT verdict to `path` — the certificate ADR-0027 decision 4 replaces
    /// the cross-solver audit with.
    ///
    /// A constructor rather than a setter because CaDiCaL only accepts a proof
    /// tracer in its CONFIGURING state — before the first clause **and before
    /// the variable reservation**, both of which leave that state. Asking later
    /// violates a solver contract and aborts the process, so the only way to
    /// trace is to say so while the solver is still empty.
    ///
    /// The trace is not finished until [`Self::close_proof_trace`] runs; a
    /// dropped solver leaves whatever CaDiCaL had buffered unwritten.
    ///
    /// # Errors
    /// [`ProofTraceError::Open`] when CaDiCaL cannot open `path` for writing,
    /// and [`ProofTraceError::UnusablePath`] when the path cannot cross the C
    /// boundary at all (non-UTF-8, or an interior NUL). Both are refusals: no
    /// solver is returned, so a caller can never end up with an untraced solve
    /// it believes is being certified.
    pub fn with_proof_trace(cnf: &Cnf, path: &Path) -> Result<Self, ProofTraceError> {
        let Some(text) = path.to_str() else {
            return Err(ProofTraceError::UnusablePath(path.to_path_buf()));
        };
        if text.contains('\0') {
            return Err(ProofTraceError::UnusablePath(path.to_path_buf()));
        }
        let mut inner = cadical::Solver::new();
        if !inner.trace_proof(text) {
            return Err(ProofTraceError::Open(path.to_path_buf()));
        }
        Ok(Self::load(inner, cnf, true))
    }

    /// The shared body of the two constructors: reserve, then add every clause
    /// in order. Split out so proof tracing can be armed on `inner` first —
    /// nothing here is legal in CaDiCaL's CONFIGURING state.
    fn load(mut inner: cadical::Solver<cadical::Timeout>, cnf: &Cnf, tracing: bool) -> Self {
        // Reserving up front keeps CaDiCaL from regrowing its arenas clause by
        // clause on the multi-million-variable encodings the gauge runs over.
        if cnf.num_vars() > 0 {
            let lit = dimacs(Lit::positive(Var::from_index(cnf.num_vars() as usize - 1)));
            inner.reserve(lit);
        }
        let mut solver = Self {
            inner,
            num_vars: cnf.num_vars(),
            wall_limit: None,
            proof_trace_open: tracing,
        };
        for clause in cnf.clauses() {
            solver.inner.add_clause(clause.iter().copied().map(dimacs));
        }
        solver
    }

    /// The linked CaDiCaL's own version string — recorded in instrument
    /// artifacts so a measurement names the solver that produced it.
    #[must_use]
    pub fn signature(&self) -> &str {
        self.inner.signature()
    }

    /// Conflicts generated over this solver's whole life — one of the three
    /// terms [`LiveSolver::effort`](crate::LiveSolver::effort) sums.
    ///
    /// Reads `Internal::stats.conflicts` through the accessors `vendor/cadical`
    /// adds; the published crate exposes none, which is the contract gap this
    /// module's header used to record. The counter is cumulative and survives
    /// the incremental seam, so an enumeration can charge what each solve
    /// actually spent.
    #[must_use]
    #[allow(
        clippy::cast_sign_loss,
        reason = "CaDiCaL's counters are monotonically non-negative int64 tallies"
    )]
    pub fn total_conflicts(&self) -> u64 {
        self.inner.conflicts() as u64
    }

    /// Decisions taken over this solver's whole life (see
    /// [`Self::total_conflicts`]).
    #[must_use]
    #[allow(clippy::cast_sign_loss, reason = "see total_conflicts")]
    pub fn total_decisions(&self) -> u64 {
        self.inner.decisions() as u64
    }

    /// Literals propagated during **search** over this solver's whole life (see
    /// [`Self::total_conflicts`]). CaDiCaL's inprocessing propagation
    /// sub-counters are deliberately excluded — the own solver's term counts
    /// search propagation, and an effort budget must mean the same thing on
    /// every backend.
    #[must_use]
    #[allow(clippy::cast_sign_loss, reason = "see total_conflicts")]
    pub fn total_props(&self) -> u64 {
        self.inner.propagations() as u64
    }

    /// Whether this solver is writing a proof trace that has not been closed.
    #[must_use]
    pub fn is_proof_tracing(&self) -> bool {
        self.proof_trace_open
    }

    /// Pushes buffered proof lines to the trace file, leaving it open. A no-op
    /// on a solver that is not tracing (CaDiCaL would abort).
    pub fn flush_proof_trace(&mut self) {
        if self.proof_trace_open {
            self.inner.flush_proof_trace();
        }
    }

    /// Finishes the trace file, flushing what is left. A no-op on a solver that
    /// is not tracing, and idempotent: a second close is the same no-op rather
    /// than the process abort CaDiCaL's own contract would deliver.
    pub fn close_proof_trace(&mut self) {
        if self.proof_trace_open {
            self.inner.close_proof_trace();
            self.proof_trace_open = false;
        }
    }

    /// Caps each subsequent [`Self::solve_within`] / [`Self::solve_now`] at
    /// `secs` of wall time, after which the solve reports budget-exhausted
    /// (`None`) exactly as a spent conflict budget does.
    ///
    /// Wall time is **not** deterministic — this is an instrument knob (a
    /// per-row deadline so one row cannot eat a whole run), never part of a
    /// verdict contract (STYLE D1).
    pub fn set_wall_limit(&mut self, secs: Option<f32>) {
        self.wall_limit = secs;
    }

    /// Adds a clause to the live instance — the enumeration seam
    /// ([`block`](crate::block) produces exactly these).
    ///
    /// # Panics
    /// Panics if a literal mentions a variable outside the loaded pool (the
    /// same negative-space invariant [`Cnf::add_clause`] asserts).
    pub fn add_clause(&mut self, lits: Vec<Lit>) {
        for lit in &lits {
            assert!(
                lit.var().index() < self.num_vars as usize,
                "clause mentions a variable outside the loaded pool: {:?} (pool size {})",
                lit.var(),
                self.num_vars
            );
        }
        self.inner.add_clause(lits.into_iter().map(dimacs));
    }

    /// Solves with no conflict budget.
    pub fn solve_now(&mut self) -> Option<Outcome> {
        self.solve_within(u64::MAX)
    }

    /// Solves, giving up after `conflict_limit` conflicts (or the configured
    /// wall limit, whichever binds first) and returning `None` — the three-way
    /// answer the backend contract requires (sat / unsat / budget spent, with
    /// the solver still usable).
    ///
    /// The limit is **per call**, as that contract specifies: CaDiCaL
    /// re-derives its internal ceiling as `stats.conflicts + inc.conflicts` at
    /// the start of every `solve` (`limit.cpp`/`internal.cpp`), so N here means
    /// "N more conflicts in this solve", not "N over the solver's life".
    /// [`u64::MAX`] means *unbudgeted* and is passed through as CaDiCaL's own
    /// unlimited sentinel (`-1`) rather than saturating to `i32::MAX`: a
    /// caller that asked for no budget must never be told "budget exhausted".
    ///
    /// # Panics
    /// Panics if CaDiCaL rejects the `"conflicts"` limit name, which would mean
    /// the binding's IPASIR limit interface changed under us (STYLE I3).
    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_possible_wrap,
        reason = "the budget is clamped to i32::MAX before the cast"
    )]
    pub fn solve_within(&mut self, conflict_limit: u64) -> Option<Outcome> {
        let limit = if conflict_limit == u64::MAX {
            UNLIMITED_CONFLICTS
        } else {
            conflict_limit.min(i32::MAX as u64) as i32
        };
        assert!(
            self.inner.set_limit("conflicts", limit).is_ok(),
            "CaDiCaL rejected the \"conflicts\" limit — binding interface changed"
        );
        self.inner
            .set_callbacks(self.wall_limit.map(cadical::Timeout::new));
        match self.inner.solve() {
            None => None,
            Some(false) => Some(Outcome::Unsat),
            Some(true) => Some(Outcome::Sat(self.model())),
        }
    }

    /// Reads the satisfying assignment back out, one value per minted variable.
    ///
    /// CaDiCaL reports "don't care" (`None`) for variables its preprocessing
    /// eliminated; either value extends to a model, so they are read as
    /// `false` — the same convention the own solver's unassigned-at-SAT
    /// variables get.
    fn model(&self) -> Assignment {
        let values = (0..self.num_vars as usize)
            .map(|i| {
                self.inner
                    .value(dimacs(Lit::positive(Var::from_index(i))))
                    .unwrap_or(false)
            })
            .collect();
        Assignment::new(values)
    }
}

/// Why a proof trace could not be started
/// ([`CadicalSolver::with_proof_trace`]).
///
/// Hand-rolled rather than `thiserror`-derived: this crate keeps its dependency
/// list to the one binding it cannot do without (crate docs), and the enum is
/// two variants and one `Display` — less code than the dependency would be.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ProofTraceError {
    /// CaDiCaL could not open the path for writing (a missing directory, no
    /// permission, a read-only filesystem).
    Open(PathBuf),
    /// The path cannot cross the C boundary: not UTF-8, or containing an
    /// interior NUL, either of which would truncate or corrupt the name the
    /// solver writes to.
    UnusablePath(PathBuf),
}

impl fmt::Display for ProofTraceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofTraceError::Open(path) => {
                write!(f, "cannot open proof trace file `{}`", path.display())
            }
            ProofTraceError::UnusablePath(path) => write!(
                f,
                "proof trace path `{}` is not usable (not UTF-8, or contains a NUL)",
                path.display()
            ),
        }
    }
}

impl std::error::Error for ProofTraceError {}

/// The [`Solver`] implementation for CaDiCaL: a stateless factory for a caller
/// that wants one verdict and nothing incremental.
#[derive(Copy, Clone, Debug, Default)]
pub struct Cadical;

impl Solver for Cadical {
    /// Decides `cnf` with no budget.
    ///
    /// # Panics
    /// Cannot panic in practice: an unbudgeted CaDiCaL solve is only `None`
    /// when terminated, and no callback is installed here (STYLE I3).
    fn solve(&mut self, cnf: &Cnf) -> Outcome {
        let Some(outcome) = CadicalSolver::new(cnf).solve_now() else {
            unreachable!("an unbudgeted, uninterrupted CaDiCaL solve always decides")
        };
        outcome
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Builds a CNF from 1-based DIMACS-ish literal codes for test brevity.
    fn cnf_of(num_vars: u32, clauses: &[&[i32]]) -> Cnf {
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..num_vars).map(|_| cnf.fresh_var()).collect();
        for clause in clauses {
            cnf.add_clause(
                clause
                    .iter()
                    .map(|&l| {
                        let v = vars[l.unsigned_abs() as usize - 1];
                        if l > 0 {
                            Lit::positive(v)
                        } else {
                            Lit::negative(v)
                        }
                    })
                    .collect(),
            );
        }
        cnf
    }

    #[test]
    fn trivial_sat_model_satisfies_every_clause() {
        let clauses: &[&[i32]] = &[&[1, 2], &[-1, 2], &[-2, 3]];
        let cnf = cnf_of(3, clauses);
        let Some(Outcome::Sat(model)) = CadicalSolver::new(&cnf).solve_now() else {
            panic!("expected SAT")
        };
        for clause in cnf.clauses() {
            assert!(
                clause
                    .iter()
                    .any(|l| model.value(l.var()) == l.is_positive()),
                "model falsifies a clause: {clause:?}"
            );
        }
    }

    #[test]
    fn trivial_unsat() {
        let cnf = cnf_of(1, &[&[1], &[-1]]);
        assert_eq!(CadicalSolver::new(&cnf).solve_now(), Some(Outcome::Unsat));
    }

    #[test]
    fn empty_clause_is_unsat() {
        let cnf = cnf_of(1, &[&[]]);
        assert_eq!(CadicalSolver::new(&cnf).solve_now(), Some(Outcome::Unsat));
    }

    #[test]
    fn empty_formula_is_sat() {
        let cnf = Cnf::new();
        assert_eq!(
            CadicalSolver::new(&cnf).solve_now(),
            Some(Outcome::Sat(Assignment::new(vec![])))
        );
    }

    /// A zero-conflict budget forces the budget-exhausted arm on a formula
    /// that cannot be decided by propagation alone (pigeonhole 8-into-7).
    #[test]
    fn conflict_budget_binds() {
        let cnf = pigeonhole(8, 7);
        let mut solver = CadicalSolver::new(&cnf);
        assert_eq!(solver.solve_within(0), None, "0 conflicts must not decide");
        let mut generous = CadicalSolver::new(&cnf);
        assert_eq!(
            generous.solve_within(u64::MAX),
            Some(Outcome::Unsat),
            "an unbudgeted solve decides the same formula"
        );
    }

    /// The enumeration seam: blocking each model over all variables walks the
    /// solution space exactly once per model, then reports UNSAT.
    #[test]
    fn incremental_blocking_enumerates_exactly() {
        // Two free variables ⇒ four models.
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..2).map(|_| cnf.fresh_var()).collect();
        let mut solver = CadicalSolver::new(&cnf);
        let mut seen = Vec::new();
        loop {
            match solver.solve_now() {
                Some(Outcome::Sat(model)) => {
                    seen.push((model.value(vars[0]), model.value(vars[1])));
                    solver.add_clause(crate::block(&model, &vars));
                }
                Some(Outcome::Unsat) => break,
                None => panic!("unbudgeted solve returned unknown"),
            }
        }
        seen.sort_unstable();
        assert_eq!(
            seen,
            vec![(false, false), (false, true), (true, false), (true, true)]
        );
    }

    /// The effort counters run over the solver's whole **life**, not one call:
    /// repeated budgeted solves on the same instance keep adding to them.
    ///
    /// This is precisely what the cumulative enumeration budget charges — it
    /// reads the counters before and after each solve and bills the difference —
    /// so a counter that reset per call would quietly turn a bounded enumeration
    /// into an unbounded one.
    #[test]
    fn effort_counters_accumulate_over_repeated_solves() {
        // Pigeonhole 9-into-8: UNSAT and far beyond a 50-conflict budget, so
        // every call spends its whole allowance and returns a non-answer.
        let cnf = pigeonhole(9, 8);
        let mut solver = CadicalSolver::new(&cnf);
        let spend = |s: &CadicalSolver| (s.total_conflicts(), s.total_decisions(), s.total_props());
        let mut previous = spend(&solver);
        assert_eq!(previous, (0, 0, 0), "a fresh solver has spent nothing");
        for step in 0..3 {
            assert_eq!(solver.solve_within(50), None, "step {step} must run out");
            let now = spend(&solver);
            assert!(
                now.0 > previous.0 && now.1 > previous.1 && now.2 > previous.2,
                "step {step} added nothing to the tally: {previous:?} then {now:?}"
            );
            previous = now;
        }
    }

    /// The counters survive the incremental `add_clause` seam an enumeration is
    /// built on: solving, blocking the model, and solving again never rewinds
    /// them.
    ///
    /// Monotone, not strictly increasing: CaDiCaL can answer a small formula
    /// from propagation and its lucky-phase checks without taking a single
    /// decision, so demanding growth here would pin the solver's cleverness
    /// rather than the counters' contract.
    #[test]
    fn effort_counters_survive_the_incremental_seam() {
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..3).map(|_| cnf.fresh_var()).collect();
        let mut solver = CadicalSolver::new(&cnf);
        let spend = |s: &CadicalSolver| (s.total_conflicts(), s.total_decisions(), s.total_props());
        let mut previous = spend(&solver);
        let mut models = 0;
        while let Some(Outcome::Sat(model)) = solver.solve_now() {
            models += 1;
            let now = spend(&solver);
            assert!(
                now.0 >= previous.0 && now.1 >= previous.1 && now.2 >= previous.2,
                "counters went backwards across the seam: {previous:?} then {now:?}"
            );
            previous = now;
            solver.add_clause(crate::block(&model, &vars));
        }
        assert_eq!(models, 8, "three free variables have eight models");
    }

    /// Tracing a proof changes no verdict, and leaves a real file behind: the
    /// same UNSAT, plus a non-empty DRAT trace once the file is closed.
    #[test]
    fn a_traced_solve_reaches_the_same_verdict_and_writes_a_proof() {
        let cnf = pigeonhole(6, 5);
        let plain = CadicalSolver::new(&cnf).solve_now();

        let path = temp_path("mettle-proof-trace");
        let mut traced = match CadicalSolver::with_proof_trace(&cnf, &path) {
            Ok(solver) => solver,
            Err(e) => panic!("could not start a proof trace at {}: {e}", path.display()),
        };
        assert!(traced.is_proof_tracing());
        assert_eq!(traced.solve_now(), plain, "tracing moved the verdict");
        assert_eq!(plain, Some(Outcome::Unsat), "the fixture must be UNSAT");

        traced.flush_proof_trace();
        traced.close_proof_trace();
        assert!(!traced.is_proof_tracing());
        // Idempotent: CaDiCaL aborts on a second close, so the wrapper must not
        // reach it.
        traced.close_proof_trace();

        let len = match std::fs::metadata(&path) {
            Ok(meta) => meta.len(),
            Err(e) => panic!("no proof file at {}: {e}", path.display()),
        };
        let _ = std::fs::remove_file(&path);
        assert!(len > 0, "the proof trace is empty");
    }

    /// A path CaDiCaL cannot write is a typed refusal, not a solver that
    /// silently runs without producing the certificate it was asked for (and
    /// not, as upstream would have it, a segfault).
    #[test]
    fn an_unwritable_proof_path_is_refused() {
        let cnf = pigeonhole(3, 2);
        let missing = Path::new("/mettle-no-such-directory-9f3a/proof.drat");
        assert_eq!(
            CadicalSolver::with_proof_trace(&cnf, missing).err(),
            Some(ProofTraceError::Open(missing.to_path_buf()))
        );
        let nul = Path::new("proof\0.drat");
        assert_eq!(
            CadicalSolver::with_proof_trace(&cnf, nul).err(),
            Some(ProofTraceError::UnusablePath(nul.to_path_buf()))
        );
    }

    /// A process-unique scratch path under the system temp dir. No `tempfile`
    /// dependency for one test file (STYLE P1/P2); the test removes what it
    /// creates.
    fn temp_path(stem: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!("{stem}-{}.drat", std::process::id()))
    }

    /// `holes + 1` pigeons into `holes` holes — small, UNSAT, and genuinely
    /// conflict-driven, so it exercises the budget rather than propagation.
    fn pigeonhole(pigeons: usize, holes: usize) -> Cnf {
        let mut cnf = Cnf::new();
        let vars: Vec<Vec<Var>> = (0..pigeons)
            .map(|_| (0..holes).map(|_| cnf.fresh_var()).collect())
            .collect();
        for row in &vars {
            cnf.add_clause(row.iter().map(|&v| Lit::positive(v)).collect());
        }
        for (i, row1) in vars.iter().enumerate() {
            for row2 in vars.iter().skip(i + 1) {
                for (a, b) in row1.iter().zip(row2) {
                    cnf.add_clause(vec![Lit::negative(*a), Lit::negative(*b)]);
                }
            }
        }
        cnf
    }
}
