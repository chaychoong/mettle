//! DIMACS CNF text — the other half of a DRAT certificate.
//!
//! A DRAT proof is only checkable against the formula it refutes, and every
//! checker reads that formula as DIMACS text. So the proof-certification
//! instrument ([ADR-0027](../../../docs/adr/0027-cadical-only-solver.md)
//! decision 4, mt-123) has to be able to write a [`Cnf`] out in exactly the
//! numbering the solver was handed — otherwise the checker is verifying a proof
//! of a *different* formula, and a "verified" verdict means nothing.
//!
//! That is why [`dimacs_lit`] lives here rather than in
//! [`cadical_backend`](crate::cadical_backend): the mapping from a [`Lit`] to a
//! DIMACS literal is a single fact about this crate's boundary, and the file the
//! checker reads and the clauses the solver loaded must agree on it by
//! construction, not by two copies happening to stay in step (STYLE I1).

#![allow(
    clippy::doc_markdown,
    reason = "\"CaDiCaL\" is the solver's own spelling — a proper noun with internal \
              capitals, which doc_markdown mistakes for an unlinked item path"
)]

use std::fmt::Write as _;
use std::fs::File;
use std::io::{self, BufWriter, Write as _};
use std::path::Path;

use crate::{Cnf, Lit};

/// The DIMACS literal for `lit`: variable `i` becomes `i + 1`, negated literals
/// get a minus sign.
///
/// The one mapping between mettle's dense 0-based variables and the 1-based
/// signed integers both CaDiCaL's IPASIR interface and DIMACS text speak.
///
/// Total for every literal a [`Cnf`] can hold: [`Cnf::fresh_var`] caps the pool
/// at `u32::MAX / 2 == i32::MAX`, so `index + 1` always fits a positive `i32`.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    reason = "Cnf::fresh_var caps the pool at u32::MAX/2 == i32::MAX, so index+1 is a \
              positive i32 by construction — asserted below"
)]
pub(crate) fn dimacs_lit(lit: Lit) -> i32 {
    let index = lit.var().index();
    assert!(
        index < i32::MAX as usize,
        "variable index {index} outside the DIMACS range"
    );
    let var = index as i32 + 1;
    if lit.is_positive() {
        var
    } else {
        -var
    }
}

/// Writes `cnf` as DIMACS CNF text: a `p cnf <vars> <clauses>` header, then one
/// space-separated `0`-terminated clause per line, in the formula's own clause
/// order.
///
/// The header counts are the formula's, not a re-derivation: `<vars>` is the
/// size of the minted pool (dense by [`Cnf::fresh_var`], so it is also the
/// largest DIMACS variable that can appear) and `<clauses>` is the clause count
/// a checker will read. An empty clause is a bare `0` line — the standard
/// spelling of the empty disjunction, and the one a trivially refuted formula
/// carries.
///
/// # Errors
/// Whatever `out` reports; nothing here fails on its own.
pub fn write_dimacs<W: io::Write>(cnf: &Cnf, out: &mut W) -> io::Result<()> {
    writeln!(out, "p cnf {} {}", cnf.num_vars(), cnf.clauses().len())?;
    // One reused line buffer rather than a `write!` per literal: the gauge's
    // encodings reach tens of millions of literals, and each `write!` on the
    // sink is a separate formatting dispatch through the `io::Write` vtable.
    let mut line = String::new();
    for clause in cnf.clauses() {
        line.clear();
        for lit in clause {
            // Infallible: `String`'s `fmt::Write` never errors.
            let _ = write!(line, "{} ", dimacs_lit(*lit));
        }
        line.push_str("0\n");
        out.write_all(line.as_bytes())?;
    }
    Ok(())
}

/// Writes `cnf` as DIMACS CNF text to `path`, truncating whatever was there.
///
/// # Errors
/// I/O failures creating, writing or flushing `path`.
pub fn write_dimacs_file(cnf: &Cnf, path: &Path) -> io::Result<()> {
    let mut out = BufWriter::new(File::create(path)?);
    write_dimacs(cnf, &mut out)?;
    // `BufWriter`'s own drop-flush swallows errors; a truncated CNF would make a
    // checker reject a perfectly good proof, so the failure has to surface here.
    out.flush()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Var;

    /// Renders a CNF to a `String` for the golden comparisons below.
    fn render(cnf: &Cnf) -> String {
        let mut buf = Vec::new();
        match write_dimacs(cnf, &mut buf) {
            Ok(()) => {}
            Err(e) => panic!("writing to a Vec cannot fail: {e}"),
        }
        match String::from_utf8(buf) {
            Ok(text) => text,
            Err(e) => panic!("DIMACS output is not UTF-8: {e}"),
        }
    }

    #[test]
    fn literal_mapping_is_one_based_and_signed() {
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..3).map(|_| cnf.fresh_var()).collect();
        assert_eq!(dimacs_lit(Lit::positive(vars[0])), 1);
        assert_eq!(dimacs_lit(Lit::negative(vars[0])), -1);
        assert_eq!(dimacs_lit(Lit::positive(vars[2])), 3);
        assert_eq!(dimacs_lit(Lit::negative(vars[2])), -3);
    }

    #[test]
    fn a_small_formula_renders_clause_by_clause() {
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..3).map(|_| cnf.fresh_var()).collect();
        cnf.add_clause(vec![Lit::positive(vars[0]), Lit::negative(vars[1])]);
        cnf.add_clause(vec![Lit::positive(vars[2])]);
        assert_eq!(render(&cnf), "p cnf 3 2\n1 -2 0\n3 0\n");
    }

    /// The header counts the **minted** pool, not the variables that happen to
    /// appear: a variable nothing constrains is still free, and a checker that
    /// read a smaller pool would be checking a different formula.
    #[test]
    fn the_header_counts_the_whole_variable_pool() {
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..5).map(|_| cnf.fresh_var()).collect();
        cnf.add_clause(vec![Lit::positive(vars[0])]);
        assert_eq!(render(&cnf), "p cnf 5 1\n1 0\n");
    }

    #[test]
    fn an_empty_formula_is_a_bare_header() {
        assert_eq!(render(&Cnf::new()), "p cnf 0 0\n");
    }

    /// The empty clause — the refutation a trivially UNSAT encoding carries —
    /// is the bare `0` line, not a dropped line.
    #[test]
    fn an_empty_clause_is_a_bare_zero_line() {
        let mut cnf = Cnf::new();
        let v = cnf.fresh_var();
        cnf.add_clause(vec![]);
        cnf.add_clause(vec![Lit::negative(v)]);
        assert_eq!(render(&cnf), "p cnf 1 2\n0\n-1 0\n");
    }

    #[test]
    fn writing_to_a_file_round_trips_the_text() {
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..2).map(|_| cnf.fresh_var()).collect();
        cnf.add_clause(vec![Lit::positive(vars[0]), Lit::positive(vars[1])]);
        let path = std::env::temp_dir().join(format!("mettle-dimacs-{}.cnf", std::process::id()));
        match write_dimacs_file(&cnf, &path) {
            Ok(()) => {}
            Err(e) => panic!("writing {}: {e}", path.display()),
        }
        let text = match std::fs::read_to_string(&path) {
            Ok(text) => text,
            Err(e) => panic!("reading {} back: {e}", path.display()),
        };
        let _ = std::fs::remove_file(&path);
        assert_eq!(text, render(&cnf));
    }
}
