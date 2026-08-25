//! The `Solver` trait and CNF interface types (Var, Lit, Cnf, Assignment).
//!
//! This crate depends on nothing of mettle's (not even `als-syntax`): it is the
//! pure boolean-satisfiability boundary. `Solver` is a trait because the backend
//! set is genuinely open (`PORTING_RULES` R2b) — the boundary STYLE P3 reserved
//! for an FFI solver, which
//! [ADR-0027](../../../docs/adr/0027-cadical-only-solver.md) has since filled
//! and made the only one mettle ships. Its one outside dependency is the
//! vendored `cadical` binding, and it reaches no further than
//! [`CadicalSolver`]: the trait and the CNF types are untouched by it.

#![deny(clippy::unwrap_used, clippy::expect_used)]

mod backend;
mod cadical_backend;
mod dimacs;

pub use backend::{Backend, LiveSolver};
pub use cadical_backend::{Cadical, CadicalSolver, ProofTraceError};
pub use dimacs::{write_dimacs, write_dimacs_file};

use std::fmt;
use std::ops::Not;

/// A boolean variable, `0`-based and dense.
///
/// Density is an invariant the CNF builder maintains (STYLE I1): variables
/// are minted in order by [`Cnf::fresh_var`] with no gaps.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Var(u32);

impl Var {
    /// The raw index.
    #[must_use]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Reconstructs a variable from its dense index.
    ///
    /// Internal to the crate: reading a model back out of a backend walks the
    /// dense `0..num_vars` pool and needs to turn an index into a `Var` (STYLE
    /// I1 keeps the pool dense, so this is total for `index < num_vars`).
    #[allow(
        clippy::cast_possible_truncation,
        reason = "the pool is capped at u32::MAX/2 vars by Cnf::fresh_var, so a dense \
                  in-range index always fits u32"
    )]
    pub(crate) fn from_index(index: usize) -> Var {
        debug_assert!(index < u32::MAX as usize / 2, "variable index overflow");
        Var(index as u32)
    }
}

/// A literal: a variable or its negation.
///
/// Encoded as `var << 1 | negated` so negation is one XOR and literals pack
/// densely into solver-side arrays.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(u32);

impl Lit {
    /// The positive literal of `var`.
    #[must_use]
    pub fn positive(var: Var) -> Self {
        Self(var.0 << 1)
    }

    /// The negative literal of `var`.
    #[must_use]
    pub fn negative(var: Var) -> Self {
        Self(var.0 << 1 | 1)
    }

    /// The underlying variable.
    #[must_use]
    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }

    /// Whether this is the positive literal.
    #[must_use]
    pub fn is_positive(self) -> bool {
        self.0 & 1 == 0
    }

    /// The dense literal code (`var << 1 | negated`).
    ///
    /// The natural dense key for anything indexed by literal — a gate cache, a
    /// solver-side array; `code < 2 * num_vars` by construction.
    #[must_use]
    pub fn code(self) -> usize {
        self.0 as usize
    }
}

impl Not for Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_positive() {
            write!(f, "Lit({})", self.var().0)
        } else {
            write!(f, "Lit(!{})", self.var().0)
        }
    }
}

/// A CNF formula under construction: a dense variable pool plus clauses.
///
/// Clause order and variable numbering are exactly insertion order —
/// deterministic by construction (STYLE D1/D2).
#[derive(Debug, Default)]
pub struct Cnf {
    num_vars: u32,
    clauses: Vec<Vec<Lit>>,
}

impl Cnf {
    /// Creates an empty formula.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Mints the next variable.
    ///
    /// # Panics
    /// Panics past `u32::MAX / 2` variables (literal encoding limit) — an
    /// internal capacity invariant, unreachable for realistic problems.
    pub fn fresh_var(&mut self) -> Var {
        assert!(
            self.num_vars < u32::MAX / 2,
            "variable pool overflow: {}",
            self.num_vars
        );
        let var = Var(self.num_vars);
        self.num_vars += 1;
        var
    }

    /// Appends a clause (a disjunction of literals).
    ///
    /// # Panics
    /// Panics if a literal mentions a variable this formula never minted
    /// (STYLE I1: numbering is dense, foreign variables are a builder bug).
    pub fn add_clause(&mut self, clause: Vec<Lit>) {
        for lit in &clause {
            assert!(
                lit.var().0 < self.num_vars,
                "clause mentions unminted variable: {:?} (pool size {})",
                lit.var(),
                self.num_vars
            );
        }
        self.clauses.push(clause);
    }

    /// Number of variables minted so far.
    #[must_use]
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// The clauses, in insertion order.
    #[must_use]
    pub fn clauses(&self) -> &[Vec<Lit>] {
        &self.clauses
    }
}

/// A total assignment: one boolean per minted variable.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Assignment {
    values: Vec<bool>,
}

impl Assignment {
    /// Creates an assignment from per-variable values (index = `Var` index).
    #[must_use]
    pub fn new(values: Vec<bool>) -> Self {
        Self { values }
    }

    /// The value of `var`.
    #[must_use]
    pub fn value(&self, var: Var) -> bool {
        self.values[var.index()]
    }
}

/// Builds a **blocking clause** that rules out `assignment`'s projection onto
/// `vars`: the disjunction of each variable's *currently-false* literal, so any
/// satisfying extension must flip at least one of them.
///
/// The enumeration primitive (mt-033): a driver solves, blocks the model it got
/// with [`LiveSolver::add_clause`], and solves the same live instance again
/// until it answers UNSAT. Passing every variable blocks the exact model
/// (raw-count / SB-0 enumeration); passing a subset blocks the projection
/// (distinct-projection enumeration). An empty `vars` yields an empty clause —
/// the caller should treat that as "no further models to distinguish" and stop,
/// never hand it to a solver.
#[must_use]
pub fn block(assignment: &Assignment, vars: &[Var]) -> Vec<Lit> {
    vars.iter()
        .map(|&v| {
            if assignment.value(v) {
                Lit::negative(v)
            } else {
                Lit::positive(v)
            }
        })
        .collect()
}

/// The result of one solver call.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Outcome {
    /// Satisfiable, with a witnessing assignment.
    Sat(Assignment),
    /// Unsatisfiable.
    Unsat,
}

/// A SAT backend, in its one-shot form: hand it a formula, get a verdict.
///
/// The open extension boundary of the pipeline (`PORTING_RULES` R2b), and
/// deliberately the *smaller* of the two seams. Enumeration needs a live
/// instance that survives between solves, which is [`LiveSolver`]; this trait is
/// for a caller that only wants one answer and does not care which backend
/// gives it.
pub trait Solver {
    /// Decides `cnf`.
    fn solve(&mut self, cnf: &Cnf) -> Outcome;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_encoding_roundtrip() {
        let mut cnf = Cnf::new();
        let v = cnf.fresh_var();
        let pos = Lit::positive(v);
        let neg = Lit::negative(v);
        assert_eq!(!pos, neg);
        assert_eq!(!neg, pos);
        assert_eq!(pos.var(), v);
        assert_eq!(neg.var(), v);
        assert!(pos.is_positive());
        assert!(!neg.is_positive());
    }

    #[test]
    fn variable_numbering_is_dense() {
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..4).map(|_| cnf.fresh_var()).collect();
        let indices: Vec<usize> = vars.iter().map(|v| v.index()).collect();
        assert_eq!(indices, vec![0, 1, 2, 3]);
        cnf.add_clause(vec![Lit::positive(vars[0]), Lit::negative(vars[3])]);
        assert_eq!(cnf.clauses().len(), 1);
    }

    /// A blocking clause is the negation of the model's projection: every
    /// variable contributes the literal that is *false* under it, so the clause
    /// is falsified by exactly that projection and by no other.
    #[test]
    fn blocking_a_model_negates_its_projection() {
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..3).map(|_| cnf.fresh_var()).collect();
        let model = Assignment::new(vec![true, false, true]);
        assert_eq!(
            block(&model, &vars),
            vec![
                Lit::negative(vars[0]),
                Lit::positive(vars[1]),
                Lit::negative(vars[2]),
            ]
        );
        // A subset blocks the projection onto it, in the order given.
        assert_eq!(
            block(&model, &[vars[2], vars[1]]),
            vec![Lit::negative(vars[2]), Lit::positive(vars[1])]
        );
    }

    /// Blocking over no variables yields the empty clause — "nothing left to
    /// distinguish", which a driver must read as a stop rather than feed to a
    /// solver as an instant UNSAT.
    #[test]
    fn blocking_no_variables_yields_the_empty_clause() {
        assert!(block(&Assignment::new(vec![true]), &[]).is_empty());
    }

    #[test]
    #[should_panic(expected = "unminted variable")]
    fn rejects_foreign_variable() {
        let mut other = Cnf::new();
        let foreign = {
            other.fresh_var();
            other.fresh_var()
        };
        let mut cnf = Cnf::new();
        cnf.add_clause(vec![Lit::positive(foreign)]);
    }
}
