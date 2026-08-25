//! **The backend contract** ([ADR-0027](../../../docs/adr/0027-cadical-only-solver.md)
//! decision 2; the seam itself is
//! [ADR-0019](../../../docs/adr/0019-optional-cadical-backend.md) stage 2,
//! mt-089): which SAT solver a solve runs on, what mettle requires of any
//! solver that wants the job, and the one live-solver type every backend answers
//! through.
//!
//! [`Backend`] is the *choice* — a name a user can write (`--solver <name>`) and
//! a value the pipeline carries in
//! [`SolveOptions`](../../../als_core/struct.SolveOptions.html). [`LiveSolver`]
//! is the *instance*: an enum, not a `dyn Solver`, because the enumeration seam
//! needs `add_clause` + repeated `solve` on a concrete incremental solver, and
//! because a small `match` at a handful of call sites is cheaper to read (and to
//! prove deterministic) than a trait object.
//!
//! # What a backend must provide
//!
//! This is the plugin boundary ADR-0027 decision 2 makes first-class, not a
//! leftover of the migration. Drivers — the CLI, `serve`, the REPL, the
//! conformance gauge — are written against [`Backend`] and [`LiveSolver`] and
//! never against a concrete solver; `--solver <name>` is the whole user surface.
//! A new backend (Kissat, MiniSat, …) is a variant here plus a name, and must
//! supply:
//!
//! - **(a) an incremental `add_clause` across solves** — the enumeration seam:
//!   solve, block the model, solve again on the same live instance;
//! - **(b) a conflict-budgeted [`LiveSolver::solve_within`]**, whose limit is
//!   *per call* ("at most N more conflicts in this solve") and which leaves the
//!   solver usable afterwards;
//! - **(c) model access over the primary variables**, in mettle's own dense
//!   variable numbering, so decoding never depends on the solver;
//! - **(d) optionally, effort reporting** ([`Backend::reports_effort`]) — see
//!   below; required for the cumulative enumeration budget, and a backend
//!   without it is refused up front, typed;
//! - **(e) optionally, proof emission** ([`Backend::supports_proof_trace`]) —
//!   the DRAT/LRAT certificate ADR-0027 decision 4 certifies UNSAT with.
//!
//! The two optional capabilities are queries rather than assumptions on purpose:
//! anything a backend cannot do degrades to a **typed refusal** at the boundary
//! that needs it, never to a silent change of behavior. Charging a budget to a
//! counter-less solver would quietly turn a bounded enumeration into an
//! unbounded one, and that is the shape every future capability must avoid too.
//!
//! [`Backend::COMPILED_OUT`] carries the other half of that contract: a name
//! mettle *has* but this build left out is a different thing from a name that
//! does not exist, and telling them apart is what stops a user hunting for a
//! typo that is not there. It is empty today (the one shipped backend is in
//! every build) and stays because ADR-0027 makes future backends feature-gated
//! plugins, which is exactly what fills it.
//!
//! # Effort, and why it is `Option`
//!
//! A backend counts the work it does — conflicts + decisions + propagation
//! visits — which is what makes the cumulative enumeration budget
//! (`SolveOptions::enum_effort_budget`) both bounding *and* deterministic.
//! CaDiCaL reports it from `Internal::stats` through the accessors
//! `vendor/cadical` adds (the published binding exposes limits but no counters,
//! which is the gap ADR-0019 recorded and mt-120 closed).
//!
//! The `Option` stays because the capability is genuinely optional (d): it is
//! the negative space a counter-less backend would land in, and
//! [`Backend::reports_effort`] is how a caller finds out before it charges
//! anything. A budget is one quantity, but its *price* is a backend's own — the
//! same number buys a different amount of search on each — which is why the
//! gauge defaults are re-paired against whichever backend answers (ADR-0017)
//! rather than fixed by this type.

#![allow(
    clippy::doc_markdown,
    reason = "\"CaDiCaL\" is the solver's own spelling — a proper noun with internal \
              capitals, which doc_markdown mistakes for an unlinked item path (the same \
              allow cadical_backend.rs carries, for the same prose)"
)]

use crate::{Cnf, Lit, Outcome};

/// Which SAT backend decides a CNF.
#[derive(Copy, Clone, PartialEq, Eq, Default, Debug)]
pub enum Backend {
    /// CaDiCaL via the vendored `cadical` binding — **the solver mettle ships**
    /// ([ADR-0027](../../../docs/adr/0027-cadical-only-solver.md) decisions 1
    /// and 3): verdicts, instance and trace enumeration, and both counting nets,
    /// across `exec`, `serve`, the REPL and the conformance gauge.
    ///
    /// Its determinism is **by pinning**: an exact vendored source built with
    /// pinned flags reproduces itself run for run (mt-120's gate measured that
    /// across repeated runs, job counts and instruction sets), and the guarantee
    /// is tied to that build rather than derived from the arithmetic. STYLE D1's
    /// integer-only rule still governs every line mettle itself writes around it.
    #[default]
    Cadical,
}

impl Backend {
    /// Every backend name **this build** can select, in a stable order with the
    /// default first. The CLI lists these when a name does not resolve.
    pub const AVAILABLE: &'static [&'static str] = &["cadical"];

    /// Backend names mettle *has* but this build left out, so a CLI can tell
    /// "there is no such solver" apart from "that solver was not compiled in" —
    /// two different fixes, and conflating them would send a user hunting for a
    /// typo that is not there.
    ///
    /// Empty since mt-121: the shipped backend is compiled into every build.
    /// The mechanism is the contract, not the current contents — ADR-0027
    /// decision 2 makes future backends feature-gated plugins, and this is where
    /// one that was left out announces itself.
    pub const COMPILED_OUT: &'static [&'static str] = &[];

    /// The backend's user-facing name — what `--solver` accepts and what
    /// diagnostics print.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Backend::Cadical => "cadical",
        }
    }

    /// Resolves a `--solver` name, or `None` when this build has no such
    /// backend. Exact match only: no prefixes, no case folding, no aliases —
    /// one spelling per backend, so a recorded command means one thing forever.
    ///
    /// `mettle`, the own CDCL's name until mt-124 deleted it (ADR-0027 decision
    /// 3), is deliberately *not* an alias for the survivor: a recorded command
    /// that asked for the other solver must fail loudly rather than quietly get
    /// this one.
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        match name {
            "cadical" => Some(Backend::Cadical),
            _ => None,
        }
    }

    /// Whether this backend can report the effort it spent, i.e. whether
    /// [`LiveSolver::effort`] is `Some` — capability (d) of the module's
    /// contract, and the precondition for charging the cumulative enumeration
    /// budget.
    ///
    /// The shipped backend can. A future one that cannot is refused where the
    /// budget is set, with a typed error, rather than being charged zero.
    #[must_use]
    pub const fn reports_effort(self) -> bool {
        match self {
            // CaDiCaL's counters come from the vendored binding's stats
            // accessors (mt-120 measured them: deterministic, and cumulative
            // across the incremental seam, which is what enumeration needs).
            Backend::Cadical => true,
        }
    }

    /// The backend's **versioned** identity — what an artifact header stamps so
    /// a measurement names the solver that produced it (ADR-0027 migration debt
    /// 2; [`Self::name`] is the selector, this is the provenance).
    ///
    /// CaDiCaL's own signature (`cadical-1.9.5`), read from the linked library
    /// rather than written down — a hardcoded version here could disagree with
    /// the code that actually answered, which is the whole failure this string
    /// exists to prevent. A future backend supplies its own the same way.
    ///
    /// Deliberately *not* what a stale-artifact check compares (that is
    /// [`Self::name`]): a rebuild whose version string moved must not orphan
    /// every baseline banked before it.
    #[must_use]
    pub fn version_signature(self) -> String {
        match self {
            // Constructing an empty solver just to ask its version is cheap
            // (CaDiCaL allocates nothing until clauses arrive) and is the only
            // route the binding offers — `ccadical_signature` is behind
            // `&self`.
            Backend::Cadical => crate::CadicalSolver::new(&Cnf::new())
                .signature()
                .to_owned(),
        }
    }

    /// Whether this backend can emit a DRAT/LRAT proof of an UNSAT verdict —
    /// capability (e) of the module's contract, and what ADR-0027 decision 4
    /// certifies UNSAT with.
    ///
    /// CaDiCaL can. A backend that cannot is refused at the call site
    /// ([`CadicalSolver::with_proof_trace`](crate::CadicalSolver::with_proof_trace)
    /// is the only constructor that traces), never given a solve that quietly
    /// runs without producing the certificate its caller asked for.
    #[must_use]
    pub const fn supports_proof_trace(self) -> bool {
        match self {
            Backend::Cadical => true,
        }
    }
}

/// A live solver of the selected [`Backend`], holding one CNF and supporting the
/// incremental seam (`add_clause` between solves) enumeration is built on.
///
/// Construct with [`LiveSolver::new`]. One variant per backend, with a surface
/// every arm must present identically, so the pipeline never branches on the
/// backend outside this file.
#[derive(Debug)]
pub enum LiveSolver {
    /// CaDiCaL.
    Cadical(crate::CadicalSolver),
}

impl LiveSolver {
    /// Loads `cnf` into a fresh instance of `backend`.
    #[must_use]
    pub fn new(backend: Backend, cnf: &Cnf) -> Self {
        match backend {
            Backend::Cadical => LiveSolver::Cadical(crate::CadicalSolver::new(cnf)),
        }
    }

    /// Which backend this is.
    #[must_use]
    pub const fn backend(&self) -> Backend {
        match self {
            LiveSolver::Cadical(_) => Backend::Cadical,
        }
    }

    /// Decides the current formula with no budget.
    pub fn solve(&mut self) -> Outcome {
        match self {
            LiveSolver::Cadical(s) => {
                let Some(outcome) = s.solve_now() else {
                    // No budget and no termination callback: CaDiCaL cannot
                    // report "unknown" here (STYLE I3).
                    unreachable!("an unbudgeted, uninterrupted CaDiCaL solve always decides")
                };
                outcome
            }
        }
    }

    /// Decides the current formula within `conflict_limit` conflicts, returning
    /// `None` when the budget is spent first.
    ///
    /// The budget means the same thing on every backend — **at most that many
    /// conflicts in this call** — and on every one it leaves the solver usable
    /// afterwards (contract (b)). What it *cost* is [`Self::effort`].
    pub fn solve_within(&mut self, conflict_limit: u64) -> Option<Outcome> {
        match self {
            LiveSolver::Cadical(s) => s.solve_within(conflict_limit),
        }
    }

    /// Adds a clause to the live solver — the enumeration seam
    /// ([`block`](crate::block) produces exactly these).
    pub fn add_clause(&mut self, lits: Vec<Lit>) {
        match self {
            LiveSolver::Cadical(s) => s.add_clause(lits),
        }
    }

    /// Cumulative effort spent over this solver's whole life — conflicts +
    /// branching decisions + propagation clause-visits — or `None` on a backend
    /// with no counters (module docs).
    ///
    /// The same three terms whichever arm answers, so a budget is one quantity
    /// however it was spent. The magnitudes are a backend's own and are not
    /// comparable across backends (module docs).
    #[must_use]
    pub fn effort(&self) -> Option<u64> {
        match self {
            LiveSolver::Cadical(s) => {
                Some(s.total_conflicts() + s.total_decisions() + s.total_props())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{block, Var};

    /// The backend named by `name`, which every caller here takes from
    /// [`Backend::AVAILABLE`] and so cannot fail to resolve.
    fn backend_of(name: &str) -> Backend {
        match Backend::parse(name) {
            Some(backend) => backend,
            None => panic!("an available backend name must parse: {name}"),
        }
    }

    /// The default is CaDiCaL (ADR-0027 decision 1), and `AVAILABLE` leads with
    /// it — the CLI's help text reads the default off this list, so the two can
    /// never drift into telling a user different things.
    #[test]
    fn the_default_backend_is_cadical_and_leads_the_available_list() {
        assert_eq!(Backend::default(), Backend::Cadical);
        assert_eq!(Backend::default().name(), "cadical");
        assert_eq!(Backend::AVAILABLE[0], Backend::default().name());
    }

    #[test]
    fn every_available_name_parses_back_to_itself() {
        for name in Backend::AVAILABLE {
            assert_eq!(backend_of(name).name(), *name);
        }
    }

    #[test]
    fn unknown_and_compiled_out_names_do_not_parse() {
        assert!(Backend::parse("minisat").is_none());
        assert!(Backend::parse("Cadical").is_none(), "no case folding");
        assert!(Backend::parse("cad").is_none(), "no prefix matching");
        for name in Backend::COMPILED_OUT {
            assert!(
                Backend::parse(name).is_none(),
                "a compiled-out backend must not resolve: {name}"
            );
        }
    }

    /// The own CDCL's name does not quietly become an alias for the survivor
    /// (ADR-0027 decision 3): a script or a recorded command that asks for
    /// `mettle` must be told the name is gone, not handed a different solver.
    #[test]
    fn the_deleted_backends_name_does_not_resolve() {
        assert!(Backend::parse("mettle").is_none());
        assert!(!Backend::AVAILABLE.contains(&"mettle"));
    }

    #[test]
    fn available_and_compiled_out_are_disjoint_and_total() {
        for name in Backend::COMPILED_OUT {
            assert!(!Backend::AVAILABLE.contains(name));
        }
        // Every backend mettle knows about is in exactly one of the two lists.
        assert_eq!(Backend::AVAILABLE.len() + Backend::COMPILED_OUT.len(), 1);
    }

    /// What a backend *claims* about capability (d) and what its live solver
    /// *does* are the same statement — a backend that says it counts effort must
    /// return `Some`, and one that says it does not must return `None` rather
    /// than a fake zero.
    #[test]
    fn effort_matches_the_backend_contract() {
        let cnf = Cnf::new();
        for name in Backend::AVAILABLE {
            let backend = backend_of(name);
            let solver = LiveSolver::new(backend, &cnf);
            assert_eq!(solver.backend(), backend);
            assert_eq!(solver.effort().is_some(), backend.reports_effort());
        }
    }

    /// Every backend's stamped identity names *it* and carries a version, so an
    /// artifact header can never be read as having come from the other one.
    #[test]
    fn every_backend_signs_itself_with_a_version() {
        assert!(
            Backend::Cadical.version_signature().starts_with("cadical-"),
            "expected CaDiCaL's own signature, got {:?}",
            Backend::Cadical.version_signature()
        );
        let signatures: Vec<String> = Backend::AVAILABLE
            .iter()
            .map(|name| backend_of(name).version_signature())
            .collect();
        for signature in &signatures {
            assert!(
                signature.contains(|c: char| c.is_ascii_digit()),
                "a signature without a version pins nothing: {signature}"
            );
        }
        assert_eq!(
            signatures
                .iter()
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            signatures.len(),
            "two backends signed identically: {signatures:?}"
        );
    }

    /// Capability (e) is a query with an answer, not a hope: exactly the
    /// backends that have a proof tracer say they do, and asking a backend that
    /// does not is a refusal a caller can see coming.
    #[test]
    fn only_the_backend_with_a_proof_logger_claims_one() {
        assert!(Backend::Cadical.supports_proof_trace());
        assert!(
            Backend::default().supports_proof_trace(),
            "the default backend is the one with a proof logger, so UNSAT \
             certification needs no backend switch — only the instrument that asks \
             for the trace (mt-123)"
        );
    }

    /// Whatever the backend, the enumeration seam yields the same *set* of
    /// models: four for two free variables, then UNSAT. Order is the backend's
    /// own business (ADR-0019 §1) — the set is not.
    #[test]
    fn every_backend_enumerates_the_same_model_set() {
        for name in Backend::AVAILABLE {
            let backend = backend_of(name);
            let mut cnf = Cnf::new();
            let vars: Vec<Var> = (0..2).map(|_| cnf.fresh_var()).collect();
            let mut solver = LiveSolver::new(backend, &cnf);
            let mut seen = Vec::new();
            while let Outcome::Sat(model) = solver.solve() {
                seen.push((model.value(vars[0]), model.value(vars[1])));
                solver.add_clause(block(&model, &vars));
            }
            seen.sort_unstable();
            assert_eq!(
                seen,
                vec![(false, false), (false, true), (true, false), (true, true)],
                "backend {name} enumerated a different model set"
            );
        }
    }

    /// A spent budget is a non-answer on every backend, and leaves the solver
    /// able to answer when given room (pigeonhole 4-into-3 needs conflicts).
    #[test]
    fn a_zero_budget_decides_nothing_on_any_backend() {
        let mut cnf = Cnf::new();
        let holes = 3;
        let pigeons: Vec<Vec<Var>> = (0..=holes)
            .map(|_| (0..holes).map(|_| cnf.fresh_var()).collect())
            .collect();
        for row in &pigeons {
            cnf.add_clause(row.iter().map(|&v| Lit::positive(v)).collect());
        }
        for (i, row1) in pigeons.iter().enumerate() {
            for row2 in pigeons.iter().skip(i + 1) {
                for (a, b) in row1.iter().zip(row2) {
                    cnf.add_clause(vec![Lit::negative(*a), Lit::negative(*b)]);
                }
            }
        }
        for name in Backend::AVAILABLE {
            let mut solver = LiveSolver::new(backend_of(name), &cnf);
            assert_eq!(solver.solve_within(0), None, "backend {name}");
            assert_eq!(
                solver.solve_within(u64::MAX),
                Some(Outcome::Unsat),
                "backend {name} must still answer after a spent budget"
            );
        }
    }
}
