//! **Backend selection** ([ADR-0019](../../../docs/adr/0019-optional-cadical-backend.md)
//! stage 2, mt-089): which SAT solver a solve runs on, and the one live-solver
//! type both backends answer through.
//!
//! [`Backend`] is the *choice* — a name a user can write (`--solver <name>`) and
//! a value the pipeline carries in
//! [`SolveOptions`](../../../als_core/struct.SolveOptions.html). [`LiveSolver`]
//! is the *instance*: an enum, not a `dyn Solver`, because the enumeration seam
//! needs `add_clause` + repeated `solve` on a concrete incremental solver, and
//! because a two-arm `match` at three call sites is cheaper to read (and to
//! prove deterministic) than a trait object.
//!
//! The default is always [`Backend::Cdcl`] — the own, hand-rolled CDCL, which
//! stays the conformance yardstick and the only backend the byte-identical
//! determinism contract binds (ADR-0019 §2). The alternative is compiled in only
//! under the `cadical` cargo feature: with the feature off, the enum has exactly
//! one variant and the name `cadical` is not selectable at all (the CLI says so
//! out loud rather than falling back — the mt-006 no-silent-default rule).
//!
//! # Effort, and why it is `Option`
//!
//! The own solver counts the work it does (conflicts + decisions + propagation
//! visits), which is what makes the cumulative enumeration budget
//! (`SolveOptions::enum_effort_budget`) both bounding *and* deterministic.
//! CaDiCaL's binding exposes limits but no counters — `ccadical_conflicts` does
//! not exist anywhere in the stack (the C++ `Stats` struct is private to
//! `Internal`, and `ccadical_print_statistics` only prints) — so
//! [`LiveSolver::effort`] returns `None` there. Callers that need to *charge* a
//! budget must refuse an effort-less backend up front rather than silently
//! charging zero, which would turn a budget into no budget.

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
    /// mettle's own deterministic CDCL ([`CdclSolver`](crate::CdclSolver)) — the
    /// default, the conformance yardstick, and the only backend under the
    /// byte-identical determinism contract.
    #[default]
    Cdcl,
    /// CaDiCaL via the `cadical` binding (ADR-0019): a far stronger search,
    /// deliberately **not** held to byte-identical determinism across builds or
    /// platforms.
    #[cfg(feature = "cadical")]
    Cadical,
}

impl Backend {
    /// Every backend name **this build** can select, in a stable order with the
    /// default first. The CLI lists these when a name does not resolve.
    #[cfg(feature = "cadical")]
    pub const AVAILABLE: &'static [&'static str] = &["mettle", "cadical"];
    /// Every backend name this build can select (no `cadical` feature).
    #[cfg(not(feature = "cadical"))]
    pub const AVAILABLE: &'static [&'static str] = &["mettle"];

    /// Backend names mettle *has* but this build left out, so a CLI can tell
    /// "there is no such solver" apart from "that solver was not compiled in" —
    /// two different fixes, and conflating them would send a user hunting for a
    /// typo that is not there.
    #[cfg(feature = "cadical")]
    pub const COMPILED_OUT: &'static [&'static str] = &[];
    /// Backend names left out of this build (no `cadical` feature).
    #[cfg(not(feature = "cadical"))]
    pub const COMPILED_OUT: &'static [&'static str] = &["cadical"];

    /// The backend's user-facing name — what `--solver` accepts and what
    /// diagnostics print.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Backend::Cdcl => "mettle",
            #[cfg(feature = "cadical")]
            Backend::Cadical => "cadical",
        }
    }

    /// Resolves a `--solver` name, or `None` when this build has no such
    /// backend. Exact match only: no prefixes, no case folding, no aliases —
    /// one spelling per backend, so a recorded command means one thing forever.
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        match name {
            "mettle" => Some(Backend::Cdcl),
            #[cfg(feature = "cadical")]
            "cadical" => Some(Backend::Cadical),
            _ => None,
        }
    }

    /// Whether this backend can report the effort it spent, i.e. whether
    /// [`LiveSolver::effort`] is `Some`. Only the own CDCL can, which is why the
    /// cumulative enumeration budget is an own-CDCL-only facility (module docs).
    #[must_use]
    pub const fn reports_effort(self) -> bool {
        match self {
            Backend::Cdcl => true,
            #[cfg(feature = "cadical")]
            Backend::Cadical => false,
        }
    }
}

/// A live solver of the selected [`Backend`], holding one CNF and supporting the
/// incremental seam (`add_clause` between solves) enumeration is built on.
///
/// Construct with [`LiveSolver::new`]; the two arms have deliberately identical
/// surfaces, so the pipeline never branches on the backend outside this file.
#[derive(Debug)]
#[allow(
    clippy::large_enum_variant,
    reason = "the own solver's struct header is ~320 bytes against CaDiCaL's opaque \
              32-byte handle, but exactly ONE LiveSolver exists per solve (never a \
              collection of them) and both variants own multi-megabyte heap arenas \
              behind that header — boxing would add an indirection to every \
              propagation on the default path to save 288 stack bytes once"
)]
pub enum LiveSolver {
    /// The own CDCL.
    Cdcl(crate::CdclSolver),
    /// CaDiCaL.
    #[cfg(feature = "cadical")]
    Cadical(crate::CadicalSolver),
}

impl LiveSolver {
    /// Loads `cnf` into a fresh instance of `backend`.
    #[must_use]
    pub fn new(backend: Backend, cnf: &Cnf) -> Self {
        match backend {
            Backend::Cdcl => LiveSolver::Cdcl(crate::CdclSolver::new(cnf)),
            #[cfg(feature = "cadical")]
            Backend::Cadical => LiveSolver::Cadical(crate::CadicalSolver::new(cnf)),
        }
    }

    /// Which backend this is.
    #[must_use]
    pub const fn backend(&self) -> Backend {
        match self {
            LiveSolver::Cdcl(_) => Backend::Cdcl,
            #[cfg(feature = "cadical")]
            LiveSolver::Cadical(_) => Backend::Cadical,
        }
    }

    /// Decides the current formula with no budget.
    pub fn solve(&mut self) -> Outcome {
        match self {
            LiveSolver::Cdcl(s) => s.solve(),
            #[cfg(feature = "cadical")]
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
    /// The budget means the same thing on both backends — **at most that many
    /// conflicts in this call** — and on both it leaves the solver usable
    /// afterwards. What differs is observability: the own solver also reports
    /// what it spent ([`Self::effort`]), CaDiCaL does not.
    pub fn solve_within(&mut self, conflict_limit: u64) -> Option<Outcome> {
        match self {
            LiveSolver::Cdcl(s) => s.solve_within(conflict_limit),
            #[cfg(feature = "cadical")]
            LiveSolver::Cadical(s) => s.solve_within(conflict_limit),
        }
    }

    /// Adds a clause to the live solver — the enumeration seam
    /// ([`block`](crate::block) produces exactly these).
    pub fn add_clause(&mut self, lits: Vec<Lit>) {
        match self {
            LiveSolver::Cdcl(s) => s.add_clause(lits),
            #[cfg(feature = "cadical")]
            LiveSolver::Cadical(s) => s.add_clause(lits),
        }
    }

    /// Cumulative effort spent over this solver's whole life — conflicts +
    /// branching decisions + propagation clause-visits — or `None` on a backend
    /// with no counters (module docs).
    #[must_use]
    pub fn effort(&self) -> Option<u64> {
        match self {
            LiveSolver::Cdcl(s) => {
                Some(s.total_conflicts() + s.total_decisions() + s.total_props())
            }
            #[cfg(feature = "cadical")]
            LiveSolver::Cadical(_) => None,
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

    #[test]
    fn default_backend_is_the_own_cdcl() {
        assert_eq!(Backend::default(), Backend::Cdcl);
        assert_eq!(Backend::default().name(), "mettle");
        assert_eq!(Backend::AVAILABLE[0], "mettle");
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
        assert!(Backend::parse("Mettle").is_none(), "no case folding");
        assert!(Backend::parse("met").is_none(), "no prefix matching");
        for name in Backend::COMPILED_OUT {
            assert!(
                Backend::parse(name).is_none(),
                "a compiled-out backend must not resolve: {name}"
            );
        }
    }

    #[test]
    fn available_and_compiled_out_are_disjoint_and_total() {
        for name in Backend::COMPILED_OUT {
            assert!(!Backend::AVAILABLE.contains(name));
        }
        // Every backend mettle knows about is in exactly one of the two lists.
        assert_eq!(Backend::AVAILABLE.len() + Backend::COMPILED_OUT.len(), 2);
    }

    /// The own solver charges effort; a backend without counters says so rather
    /// than reporting a fake zero.
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
