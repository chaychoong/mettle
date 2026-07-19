//! String-fidelity conformance (mt-045, LEDGER-007): jar-pinned universe shape
//! and verdicts for the §10.9 probe rows S1–S7 plus solve-level String
//! behavior. Jar-free — each expected value is a constant citing its probe row
//! (translation-ref §13 / probes §10.9), so CI runs it with no oracle.
//!
//! The pinned facts: referenced-literal collection (goal + facts + sig appended
//! facts + field bounds, recursing into *called* funcs only), `"String%d"`
//! padding to an exact `for … but N String` scope (never `unused%d`),
//! `max(N, #referenced)` expansion, the non-exact-scope reject, and string
//! atoms appended **last** in the universe (after the ascending int atoms).
//! Determinism: mettle orders literals lexicographically (the jar's `HashSet`
//! order is nondeterministic but string atoms are symmetric — LEDGER-007).

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, ScopedUniverse, SolveOptions,
    SolveVerdict, TranslateError,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Computes the scoped universe of command 0, or its typed scope-phase error.
fn scoped(src: &str) -> Result<ScopedUniverse, TranslateError> {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    compute_universe(&world, &graph, &world.commands[0])
}

/// The full ordered list of universe atom names of command 0.
fn atoms(src: &str) -> Vec<String> {
    scoped(src)
        .expect("universe")
        .universe
        .iter()
        .map(|(_, n)| n.to_owned())
        .collect()
}

/// The string-atom tail of the universe (the atoms after the sig + int atoms).
fn string_tail(src: &str) -> Vec<String> {
    let su = scoped(src).expect("universe");
    let all: Vec<String> = su.universe.iter().map(|(_, n)| n.to_owned()).collect();
    all[su.string_atom_range()].to_vec()
}

/// Solves command 0 under the canonical (forbid-overflow) options; `true` = SAT.
fn solve(src: &str) -> bool {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let su = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &su, &mut ir);
    let goal = lower_command(&world, &graph, &su, &bounds, &mut ir, 0).expect("lower");
    match solve_goal(&ir, &su, &goal, &bounds, &SolveOptions::default()) {
        Ok(SolveVerdict::Sat(_)) => true,
        Ok(SolveVerdict::Unsat) => false,
        Ok(SolveVerdict::Unknown) => panic!("unbudgeted solve returned Unknown"),
        Err(e) => panic!("unexpected solve defer: {e:?}"),
    }
}

// ------------------------------- S1: non-exact scope rejects ----------------

#[test]
fn s1_nonexact_string_scope_rejects() {
    // probe S1: a non-exact `String` scope is a pre-solve error.
    let e = scoped("sig A {}\nrun { some s: String | s = s } for 3 but 3 String\n").unwrap_err();
    assert!(
        matches!(e, TranslateError::StringScopeNotExact { .. }),
        "{e:?}"
    );
}

// ------------------------------- S2: padding, no literals -------------------

#[test]
fn s2_padding_atoms_after_ints() {
    // probe S2: `exactly 3 String`, one String field, no literals → the tail is
    // exactly the three padding atoms `"String0" "String1" "String2"` (quote
    // characters included), appended after the int atoms.
    let src = "sig A { s: one String }\nrun {} for 3 but exactly 3 String\n";
    assert_eq!(
        string_tail(src),
        &["\"String0\"", "\"String1\"", "\"String2\""]
    );
    // They come after the ascending int atoms (…, 6, 7, then the strings).
    let all = atoms(src);
    let seven = all.iter().position(|a| a == "7").expect("int atom 7");
    assert_eq!(&all[seven + 1..], string_tail(src).as_slice());
    // The `String` relation is bound exactly to them: `#String = 3` SAT, `= 2`
    // UNSAT.
    assert!(solve(&format!(
        "{}\n",
        "sig A { s: one String }\nrun { #String = 3 } for 3 but exactly 3 String"
    )));
    assert!(!solve(
        "sig A { s: one String }\nrun { #String = 2 } for 3 but exactly 3 String\n"
    ));
}

// ------------------------------- S3: literal + padding ----------------------

#[test]
fn s3_one_literal_plus_padding() {
    // probe S3: one referenced literal + `exactly 3 String` → the literal atom
    // plus two padding atoms fill the scope. Referenced literals sort first,
    // then padding (mettle's deterministic order).
    let src =
        "sig A { s: one String }\nfact { all a: A | a.s = \"hello\" }\nrun {} for 3 but exactly 3 String\n";
    assert_eq!(
        string_tail(src),
        &["\"hello\"", "\"String0\"", "\"String1\""]
    );
}

// ------------------------------- S4: expansion past scope -------------------

#[test]
fn s4_expansion_past_scope_no_padding() {
    // probe S4: 3 referenced literals with `exactly 1 String` → the scope
    // EXPANDS to hold all three (max(N, #referenced)); no padding is added.
    let src = "sig A { s: one String }\nfact { all a: A | a.s = \"x\" or a.s = \"y\" or a.s = \"z\" }\nrun {} for 3 but exactly 1 String\n";
    assert_eq!(string_tail(src), &["\"x\"", "\"y\"", "\"z\""]);
}

// ------------------------------- S5: no scope, literal only -----------------

#[test]
fn s5_no_scope_is_exactly_referenced() {
    // probe S5: with no `String` scope (`maxstring = −1`), the atoms are exactly
    // the referenced literals — no padding.
    let src = "sig A { s: one String }\nfact { all a: A | a.s = \"only\" }\nrun {} for 3\n";
    assert_eq!(string_tail(src), &["\"only\""]);
}

// ------------------------------- S6: top-level fact collection --------------

#[test]
fn s6_top_level_fact_collected() {
    // probe S6: a literal reachable only through a top-level (module) fact IS
    // collected.
    let src = "sig A {}\nfact { some s: String | s = \"topfact\" }\nrun {} for 3\n";
    assert_eq!(string_tail(src), &["\"topfact\""]);
}

// ------------------------------- S7: uncalled pred not collected ------------

#[test]
fn s7_uncalled_pred_not_collected() {
    // probe S7: a literal reachable only through an UNCALLED pred is NOT
    // collected; the same literal becomes collected once the pred is the
    // command's target.
    let uncalled = "sig A {}\npred p { some s: String | s = \"u\" }\nrun {} for 3\n";
    assert!(
        string_tail(uncalled).is_empty(),
        "{:?}",
        string_tail(uncalled)
    );

    let called = "sig A {}\npred p { some s: String | s = \"u\" }\nrun p for 3\n";
    assert_eq!(string_tail(called), &["\"u\""]);
}

// ------------------------------- solve-level --------------------------------

#[test]
fn some_string_equals_literal_sat() {
    // A `some s: String | s = "hello"` is SAT — the literal's singleton is a
    // member of `String`.
    assert!(solve("run { some s: String | s = \"hello\" }\n"));
}

#[test]
fn distinct_literals_are_distinct_atoms() {
    // Two distinct literals get two distinct singleton atoms: `"a" != "b"` SAT,
    // `"a" = "b"` UNSAT, `"a" = "a"` SAT.
    assert!(solve("run { \"a\" != \"b\" }\n"));
    assert!(!solve("run { \"a\" = \"b\" }\n"));
    assert!(solve("run { \"a\" = \"a\" }\n"));
}

#[test]
fn string_cardinality_against_exact_scope() {
    // `#String` against a `for … but exactly 2 String` scope: `= 2` SAT, `= 1`
    // and `= 3` UNSAT (the bound is exact).
    assert!(solve(
        "sig A { s: one String }\nrun { #String = 2 } for 2 but exactly 2 String\n"
    ));
    assert!(!solve(
        "sig A { s: one String }\nrun { #String = 1 } for 2 but exactly 2 String\n"
    ));
    assert!(!solve(
        "sig A { s: one String }\nrun { #String = 3 } for 2 but exactly 2 String\n"
    ));
}

#[test]
fn string_field_solves() {
    // A `one String` field forced to a literal: SAT, and the value must be that
    // literal (`a.s = "x"` consistent, `a.s = "y"` with only "x" referenced is
    // UNSAT since "y" is not an atom — it is not collected, so `String` has only
    // "x"). This exercises the String-typed field column bound.
    assert!(solve(
        "some sig A { s: one String }\nfact { all a: A | a.s = \"x\" }\nrun {} for 3\n"
    ));
}
