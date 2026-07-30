//! The optional **CaDiCaL** backend ([ADR-0019](../../../docs/adr/0019-optional-cadical-backend.md),
//! mt-089) — a second implementation of this crate's SAT boundary, behind the
//! `cadical` cargo feature and **off by default**.
//!
//! The own [`CdclSolver`](crate::CdclSolver) stays the default and the
//! conformance yardstick; this backend exists first as an *instrument* (how
//! much of the `over_budget` tail is genuinely hard vs. our solver being weak)
//! and later as a user-selectable option. It is deliberately **not** held to
//! the byte-identical determinism contract the default path is (ADR-0019 §1):
//! CaDiCaL's inprocessing and its own heuristics own the search.
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
//!
//! One contract gap, recorded rather than papered over: the binding exposes no
//! conflict *counter*, so the "effort spent" half of
//! [`CdclSolver::total_conflicts`](crate::CdclSolver::total_conflicts) has no
//! CaDiCaL twin. Budgets bind; spend is not observable.

#![allow(
    clippy::doc_markdown,
    reason = "\"CaDiCaL\" is the solver's own spelling — a proper noun with internal \
              capitals, which doc_markdown mistakes for an unlinked item path; \
              backticking a product name everywhere it appears would be worse prose"
)]

use std::fmt;

use crate::{Assignment, Cnf, Lit, Outcome, Solver, Var};

/// CaDiCaL's own "no conflict limit" sentinel: `Internal::limit_conflicts`
/// treats any negative value as unlimited (`limit.cpp`).
const UNLIMITED_CONFLICTS: i32 = -1;

/// The DIMACS literal for `lit`: variable `i` becomes `i + 1`, negated
/// literals get a minus sign.
///
/// Total for every literal a [`Cnf`] can hold: [`Cnf::fresh_var`] caps the pool
/// at `u32::MAX / 2 == i32::MAX`, so `index + 1` always fits a positive `i32`.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    reason = "Cnf::fresh_var caps the pool at u32::MAX/2 == i32::MAX, so index+1 is a \
              positive i32 by construction — asserted below"
)]
fn dimacs(lit: Lit) -> i32 {
    let index = lit.var().index();
    assert!(
        index < i32::MAX as usize,
        "variable index {index} outside CaDiCaL's DIMACS range"
    );
    let var = index as i32 + 1;
    if lit.is_positive() {
        var
    } else {
        -var
    }
}

/// An incremental CaDiCaL instance holding one [`Cnf`], mirroring
/// [`CdclSolver`](crate::CdclSolver)'s surface so the two are interchangeable
/// at a call site.
pub struct CadicalSolver {
    inner: cadical::Solver<cadical::Timeout>,
    num_vars: u32,
    /// Per-solve wall limit in seconds, `None` = unbounded. Held here (rather
    /// than installed once) because `cadical::Timeout` restarts its clock on
    /// each `solve`, so the callback has to be re-armed per call to mean "this
    /// solve gets N seconds".
    wall_limit: Option<f32>,
}

impl fmt::Debug for CadicalSolver {
    /// Hand-written because `cadical::Solver` is an opaque FFI handle with no
    /// `Debug` — the useful shape is the problem size, not the pointer.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CadicalSolver")
            .field("num_vars", &self.num_vars)
            .field("num_clauses", &self.inner.num_clauses())
            .field("wall_limit", &self.wall_limit)
            .finish()
    }
}

impl CadicalSolver {
    /// Loads `cnf` into a fresh CaDiCaL instance, in clause order.
    #[must_use]
    pub fn new(cnf: &Cnf) -> Self {
        let mut inner = cadical::Solver::new();
        let mut solver = Self {
            inner: {
                // Reserving up front keeps CaDiCaL from regrowing its arenas
                // clause by clause on the multi-million-variable encodings the
                // instrument runs over.
                if cnf.num_vars() > 0 {
                    let lit = dimacs(Lit::positive(Var::from_index(cnf.num_vars() as usize - 1)));
                    inner.reserve(lit);
                }
                inner
            },
            num_vars: cnf.num_vars(),
            wall_limit: None,
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
    /// wall limit, whichever binds first) and returning `None` — the same
    /// three-way answer [`CdclSolver::solve_within`](crate::CdclSolver::solve_within)
    /// gives.
    ///
    /// The limit is **per call**, exactly like the own solver's: CaDiCaL
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

/// The [`Solver`] implementation for CaDiCaL: a stateless factory, mirroring
/// [`Cdcl`](crate::Cdcl).
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
