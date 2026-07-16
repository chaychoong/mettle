//! Warning-parity regression suite (mt-023): one minimal model per §5.2 warning
//! class, each asserting mettle emits the expected [`ResolveWarning`] class at
//! the expected source line. Every model here was verified against the
//! reference jar (Alloy 6.2.0) via `ResolveGaugeShim` — the jar emits the same
//! warning at the same line (columns differ for binary operators: the reference
//! points at the operator glyph, mettle at the node start; see
//! `docs/reference/warning-parity.md`). Warnings never change the ACCEPT
//! verdict (LEDGER-002), so every model here also ACCEPTs.

use als_types::{resolve, MapLoader, ModuleGraph, ResolveWarning};

/// Resolves `src` as `root.als` and returns each warning's `(class, line)`
/// (1-based line), in span order. Panics if the model REJECTS (these are all
/// accept-with-warning models).
fn warns(src: &str) -> Vec<(&'static str, usize)> {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let resolved = resolve(&graph).expect("expected ACCEPT (warnings never reject)");
    resolved
        .warnings
        .iter()
        .map(|w| (w.class(), line_of(src, w.span().start)))
        .collect()
}

/// 1-based line of byte `offset` in `src`.
#[allow(clippy::naive_bytecount)]
fn line_of(src: &str, offset: u32) -> usize {
    1 + src.as_bytes()[..offset as usize]
        .iter()
        .filter(|&&b| b == b'\n')
        .count()
}

/// Asserts some warning of `class` fired at `line`.
fn assert_warns_at(src: &str, class: &str, line: usize) {
    let ws = warns(src);
    assert!(
        ws.iter().any(|&(c, l)| c == class && l == line),
        "expected `{class}` at line {line}, got {ws:?}\n--- src ---\n{src}"
    );
}

/// Asserts no warning of `class` fired anywhere.
fn assert_no_warn(src: &str, class: &str) {
    let ws = warns(src);
    assert!(
        !ws.iter().any(|&(c, _)| c == class),
        "expected no `{class}`, got {ws:?}\n--- src ---\n{src}"
    );
}

// ---- B: unused binder ----

#[test]
fn unused_quantifier_var_mt023() {
    assert_warns_at("sig A {}\nfact { all x: A | some A }\n", "unused-var", 2);
}

#[test]
fn unused_let_var_mt023() {
    assert_warns_at("sig A {}\nfact { let x = A | some A }\n", "unused-var", 2);
}

#[test]
fn used_via_join_spine_head_not_flagged_mt023() {
    // `proc.p` uses `p` as a join spine head — a syntactic use, not unused.
    assert_no_warn(
        "sig P {}\none sig O { proc: P -> P }\nfact { all p: P | lone O.proc.p }\n",
        "unused-var",
    );
}

#[test]
fn comprehension_var_never_flagged_mt023() {
    // `ExprQt.resolve` exempts comprehensions from the unused-var warning.
    assert_no_warn("sig A {}\nfact { some { x: A | some A } }\n", "unused-var");
}

// ---- A1/A2: closure ----

#[test]
fn closure_disjoint_domain_range_mt023() {
    assert_warns_at(
        "sig A {}\nsig B {}\none sig O { r: A -> B }\nfact { some ^(O.r) }\n",
        "closure-redundant",
        4,
    );
}

// ---- A3: equality redundancy ----

#[test]
fn eq_disjoint_mt023() {
    assert_warns_at("sig A {}\nsig B {}\nfact { A = B }\n", "eq-redundant", 3);
}

#[test]
fn eq_same_value_mt023() {
    assert_warns_at("sig A {}\nfact { A = A }\n", "eq-redundant", 2);
}

// ---- A4: subset redundancy ----

#[test]
fn subset_disjoint_mt023() {
    assert_warns_at(
        "sig A {}\nsig B {}\nfact { A in B }\n",
        "subset-redundant",
        3,
    );
}

// ---- A6: intersection ----

#[test]
fn intersect_disjoint_mt023() {
    assert_warns_at(
        "sig A {}\nsig B {}\nfact { no (A & B) }\n",
        "intersect-irrelevant",
        3,
    );
}

// ---- A9: join always empty ----

#[test]
fn join_empty_mt023() {
    assert_warns_at(
        "sig A {}\nsig B {}\none sig O { f: A -> B }\nfact { no B.(O.f) }\n",
        "join-empty",
        4,
    );
}

// ---- A5: int atoms ----

#[test]
fn int_atoms_sum_mt023() {
    assert_warns_at("sig A {}\nfact { sum A > 0 }\n", "int-atoms", 2);
}

// ---- E: static/variable sig mismatch ----

#[test]
fn static_sig_variable_parent_mt023() {
    assert_warns_at(
        "var sig A {}\nsig B extends A {}\n",
        "sig-static-var-parent",
        2,
    );
}

#[test]
fn redundant_var_prim_only_mt023() {
    // `var` sig extending a static sig → redundant-var warning.
    assert_warns_at("sig A {}\nvar sig B extends A {}\n", "sig-redundant-var", 2);
}

#[test]
fn subset_var_never_redundant_mt023() {
    // A subset (`in`) var sig under a static parent does NOT warn redundant-var
    // (the reference's redundant-`var` branch is prim-`extends` only).
    assert_no_warn("sig A {}\nvar sig B in A {}\n", "sig-redundant-var");
}

// ---- F: function return disjoint ----

#[test]
fn function_return_disjoint_mt023() {
    assert_warns_at(
        "sig A {}\nsig B {}\nfun f: A { B }\nfact { some f }\n",
        "return-disjoint",
        3,
    );
}

// ---- warnings never change the verdict (LEDGER-002) ----

#[test]
fn warnings_accept_mt023() {
    // Every warning model ACCEPTs — a warning is never fatal.
    for src in [
        "sig A {}\nfact { all x: A | some A }\n",
        "sig A {}\nsig B {}\nfact { A = B }\n",
        "sig A {}\nsig B {}\nfact { no (A & B) }\n",
    ] {
        let loader = MapLoader::new().with("root.als", src);
        let graph = ModuleGraph::load("root.als", &loader).expect("load");
        assert!(resolve(&graph).is_ok(), "warning turned fatal:\n{src}");
    }
}

// keep the import used even if a variant set shrinks
#[allow(dead_code)]
fn _assert_type(_: &ResolveWarning) {}
