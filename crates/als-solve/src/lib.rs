//! The `Solver` trait and CNF interface types (Var, Lit, Cnf, Assignment).
//!
//! This crate is deliberately dependency-free (not even `als-syntax`): it is
//! the pure boolean-satisfiability boundary. `Solver` is a trait because the
//! backend set is genuinely open — pure-Rust SAT first, FFI solvers later
//! behind the same boundary (STYLE P3, `PORTING_RULES` R2b).

#![deny(clippy::unwrap_used, clippy::expect_used)]

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

/// The result of one solver call.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Outcome {
    /// Satisfiable, with a witnessing assignment.
    Sat(Assignment),
    /// Unsatisfiable.
    Unsat,
}

/// A SAT backend.
///
/// The open extension boundary of the pipeline (`PORTING_RULES` R2b). Will
/// grow an incremental/assumption interface when instance enumeration lands
/// (enumeration blocks each found model with a fresh clause); kept minimal
/// until that rung.
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
