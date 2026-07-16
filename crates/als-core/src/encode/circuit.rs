//! A small deterministic **boolean circuit → CNF** layer (Tseitin encoding).
//!
//! Every relational/int operation the encoder performs bottoms out in boolean
//! gates over [`als_solve::Lit`]s. A [`Bool`] is either a compile-time constant
//! or a single literal (a primary variable or a Tseitin auxiliary). The gate
//! constructors ([`Circuit::and_many`], [`Circuit::or_many`], …) fold constants
//! away eagerly and, when a genuine gate remains, mint **one** fresh auxiliary
//! variable and emit its defining clauses — the classic Tseitin transform.
//!
//! Determinism (STYLE D1/D2): auxiliary variables are minted in traversal order
//! straight from [`als_solve::Cnf::fresh_var`], which numbers densely in
//! insertion order; no hash iteration, no wall-clock. The encoder mints all
//! **primary** variables before constructing any [`Circuit`], so every auxiliary
//! sorts after every primary (ADR-0011 decision 3).

use als_solve::{Cnf, Lit, Var};

/// A boolean value in the circuit: a constant or a single literal.
///
/// Keeping "constant" as a first-class case (rather than a fixed true/false
/// literal) lets the gate constructors simplify — a huge fraction of relational
/// cells are constant-true (lower-bound tuples) or constant-false (outside the
/// upper bound), and propagating those keeps the CNF small.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Bool {
    /// A compile-time constant.
    Const(bool),
    /// A solver literal (primary or Tseitin auxiliary).
    Lit(Lit),
}

impl Bool {
    /// The constant-true value.
    pub const TRUE: Bool = Bool::Const(true);
    /// The constant-false value.
    pub const FALSE: Bool = Bool::Const(false);

    /// The positive literal of a primary variable.
    #[must_use]
    pub fn var(v: Var) -> Bool {
        Bool::Lit(Lit::positive(v))
    }
}

/// The CNF being built, plus the gate constructors that extend it.
///
/// Thin wrapper over [`als_solve::Cnf`]: it owns nothing the `Cnf` does not, it
/// only adds the Tseitin gate vocabulary. Borrowed mutably by the encoder for
/// the lifetime of one command's translation.
pub struct Circuit<'a> {
    cnf: &'a mut Cnf,
}

impl<'a> Circuit<'a> {
    /// Wraps a CNF for gate construction.
    pub fn new(cnf: &'a mut Cnf) -> Self {
        Self { cnf }
    }

    /// The negation of `b` — never mints a variable (`¬` is free on a literal).
    ///
    /// Takes `&self` purely so it reads like the other gate constructors at call
    /// sites (`self.circ().not(x)`); it touches no circuit state.
    #[must_use]
    #[allow(
        clippy::unused_self,
        reason = "uniform gate-constructor call shape; negation needs no CNF state"
    )]
    pub fn not(&self, b: Bool) -> Bool {
        match b {
            Bool::Const(x) => Bool::Const(!x),
            Bool::Lit(l) => Bool::Lit(!l),
        }
    }

    /// Conjunction of many values.
    ///
    /// Simplifies against constants (`false` short-circuits, `true` drops out);
    /// an empty/one-element residue needs no gate. Otherwise mints `z` with
    /// clauses `(¬z ∨ lᵢ)` for each input and `(z ∨ ¬l₁ ∨ … ∨ ¬lₙ)`, so
    /// `z ↔ ⋀ lᵢ`.
    #[must_use]
    pub fn and_many(&mut self, items: Vec<Bool>) -> Bool {
        let mut lits = Vec::with_capacity(items.len());
        for b in items {
            match b {
                Bool::Const(false) => return Bool::FALSE,
                Bool::Const(true) => {}
                Bool::Lit(l) => lits.push(l),
            }
        }
        match lits.len() {
            0 => Bool::TRUE,
            1 => Bool::Lit(lits[0]),
            _ => {
                let z = self.cnf.fresh_var();
                let zpos = Lit::positive(z);
                let mut big = Vec::with_capacity(lits.len() + 1);
                big.push(zpos);
                for &l in &lits {
                    self.cnf.add_clause(vec![!zpos, l]);
                    big.push(!l);
                }
                self.cnf.add_clause(big);
                Bool::Lit(zpos)
            }
        }
    }

    /// Disjunction of many values (the De Morgan dual of [`Circuit::and_many`]).
    #[must_use]
    pub fn or_many(&mut self, items: Vec<Bool>) -> Bool {
        let mut lits = Vec::with_capacity(items.len());
        for b in items {
            match b {
                Bool::Const(true) => return Bool::TRUE,
                Bool::Const(false) => {}
                Bool::Lit(l) => lits.push(l),
            }
        }
        match lits.len() {
            0 => Bool::FALSE,
            1 => Bool::Lit(lits[0]),
            _ => {
                let z = self.cnf.fresh_var();
                let zpos = Lit::positive(z);
                let mut big = Vec::with_capacity(lits.len() + 1);
                big.push(!zpos);
                for &l in &lits {
                    self.cnf.add_clause(vec![zpos, !l]);
                    big.push(l);
                }
                self.cnf.add_clause(big);
                Bool::Lit(zpos)
            }
        }
    }

    /// Binary conjunction.
    #[must_use]
    pub fn and(&mut self, a: Bool, b: Bool) -> Bool {
        self.and_many(vec![a, b])
    }

    /// Binary disjunction.
    #[must_use]
    pub fn or(&mut self, a: Bool, b: Bool) -> Bool {
        self.or_many(vec![a, b])
    }

    /// Implication `a → b`.
    #[must_use]
    pub fn implies(&mut self, a: Bool, b: Bool) -> Bool {
        let na = self.not(a);
        self.or(na, b)
    }

    /// Bi-implication `a ↔ b`.
    #[must_use]
    pub fn iff(&mut self, a: Bool, b: Bool) -> Bool {
        match (a, b) {
            (Bool::Const(x), other) | (other, Bool::Const(x)) => {
                if x {
                    other
                } else {
                    self.not(other)
                }
            }
            _ => {
                let ab = self.implies(a, b);
                let ba = self.implies(b, a);
                self.and(ab, ba)
            }
        }
    }

    /// Exclusive-or `a ⊕ b`.
    #[must_use]
    pub fn xor(&mut self, a: Bool, b: Bool) -> Bool {
        let e = self.iff(a, b);
        self.not(e)
    }

    /// If-then-else `c ? t : e` at the boolean level.
    #[must_use]
    pub fn ite(&mut self, c: Bool, t: Bool, e: Bool) -> Bool {
        match c {
            Bool::Const(true) => t,
            Bool::Const(false) => e,
            _ => {
                let nc = self.not(c);
                let ct = self.and(c, t);
                let ne = self.and(nc, e);
                self.or(ct, ne)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    // The gate closures below cannot be reduced to method paths: `Circuit::and`
    // as a fn value fails the HRTB lifetime on `&mut Circuit`.
    #![allow(clippy::redundant_closure_for_method_calls)]

    use super::*;
    use als_solve::{CdclSolver, Outcome};

    /// Forces `g` true (or false) and returns the two variables' solved values,
    /// or `None` if unsatisfiable — a tiny oracle for the gate constructors.
    fn solve_gate(
        build: impl FnOnce(&mut Circuit, Bool, Bool) -> Bool,
        want: bool,
    ) -> Vec<(bool, bool)> {
        let mut cnf = Cnf::new();
        let x = cnf.fresh_var();
        let y = cnf.fresh_var();
        let g = {
            let mut c = Circuit::new(&mut cnf);
            build(&mut c, Bool::var(x), Bool::var(y))
        };
        match g {
            Bool::Const(b) => {
                if b != want {
                    return vec![]; // unsatisfiable under the wanted polarity
                }
            }
            Bool::Lit(l) => cnf.add_clause(vec![if want { l } else { !l }]),
        }
        // Enumerate all satisfying (x, y) pairs.
        let mut solver = CdclSolver::new(&cnf);
        let mut out = Vec::new();
        while let Outcome::Sat(m) = solver.solve() {
            let (bx, by) = (m.value(x), m.value(y));
            out.push((bx, by));
            solver.add_clause(als_solve::block(&m, &[x, y]));
        }
        out.sort_unstable();
        out
    }

    #[test]
    fn and_gate_is_conjunction() {
        // x ∧ y true only at (T,T).
        let got = solve_gate(|c, a, b| c.and(a, b), true);
        assert_eq!(got, vec![(true, true)]);
    }

    #[test]
    fn or_gate_is_disjunction() {
        // x ∨ y false only at (F,F).
        let got = solve_gate(|c, a, b| c.or(a, b), false);
        assert_eq!(got, vec![(false, false)]);
    }

    #[test]
    fn xor_gate_is_exclusive_or() {
        let got = solve_gate(|c, a, b| c.xor(a, b), true);
        assert_eq!(got, vec![(false, true), (true, false)]);
    }

    #[test]
    fn iff_gate_is_equivalence() {
        let got = solve_gate(|c, a, b| c.iff(a, b), true);
        assert_eq!(got, vec![(false, false), (true, true)]);
    }

    #[test]
    fn constants_fold() {
        let mut cnf = Cnf::new();
        let mut c = Circuit::new(&mut cnf);
        assert_eq!(c.and(Bool::TRUE, Bool::FALSE), Bool::FALSE);
        assert_eq!(c.or(Bool::TRUE, Bool::FALSE), Bool::TRUE);
        assert_eq!(c.not(Bool::TRUE), Bool::FALSE);
        // No auxiliary variables were minted for constant folding.
        assert_eq!(cnf.num_vars(), 0);
    }
}
