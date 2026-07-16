//! Resolver/type-checker probe suite (mt-018): the resolution-doc §10 probe
//! table recreated as Rust tests, one accept/reject assertion per pinned jar
//! behavior. Each test cites its probe id. These are the reject-taxonomy gauge
//! (§5.1) plus the "accepts, don't over-reject" companions (§6 gotchas).
//!
//! Loading uses the injected [`MapLoader`]; the embedded clean-room stdlib
//! (mt-015) supplies `util/*` through the normal search order, so enum/ordering
//! and `util/integer` probes resolve without disk.

use als_types::{resolve, MapLoader, ModuleGraph, ResolveError};

/// Loads + resolves `src` as `root.als`, returning the first-by-position
/// resolve error (or `Ok`). Load-phase rejects surface here too.
fn check(src: &str) -> Result<(), ResolveError> {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader)?;
    resolve(&graph).map(|_| ())
}

/// Asserts `src` ACCEPTS (resolves without error).
fn accept(src: &str) {
    if let Err(e) = check(src) {
        panic!("expected ACCEPT, got REJECT: {e:?}\n--- src ---\n{src}");
    }
}

/// Asserts `src` REJECTS, and returns the error for variant inspection.
fn reject(src: &str) -> ResolveError {
    match check(src) {
        Ok(()) => panic!("expected REJECT, got ACCEPT\n--- src ---\n{src}"),
        Err(e) => e,
    }
}

// ---- sig hierarchy (§3.1) ----

#[test]
fn dup_sig_rejected_probe_05() {
    let e = reject("sig A {}\nsig A {}\n");
    assert!(matches!(e, ResolveError::DuplicateSig { .. }), "{e:?}");
}

#[test]
fn reserved_sig_name_rejected() {
    // A reserved name as a sig label is rejected — `Int` is a keyword so the
    // parse phase catches it (the `dup` reserved-name guard is the resolver's
    // backstop for any that slip through).
    let e = reject("sig Int {}\n");
    assert!(
        matches!(
            e,
            ResolveError::OpenedFileParse { .. } | ResolveError::DuplicateSig { .. }
        ),
        "{e:?}"
    );
}

#[test]
fn cyclic_inheritance_rejected_probe_07() {
    let e = reject("sig A extends B {}\nsig B extends A {}\n");
    assert!(matches!(e, ResolveError::CyclicInheritance { .. }), "{e:?}");
}

#[test]
fn parent_not_found_rejected() {
    let e = reject("sig A extends Nope {}\n");
    assert!(matches!(e, ResolveError::ParentSigNotFound { .. }), "{e:?}");
}

#[test]
fn extends_subset_sig_rejected() {
    // B is a subset sig (`in`), so `extends B` is illegal.
    let e = reject("sig A {}\nsig B in A {}\nsig C extends B {}\n");
    assert!(matches!(e, ResolveError::ExtendsSubsetSig { .. }), "{e:?}");
}

#[test]
fn multi_parent_subset_accepted_probe_29() {
    accept("sig A {}\nsig B {}\nsig C in A + B {}\n");
}

#[test]
fn abstract_no_children_accepted_probe_30() {
    accept("abstract sig A {}\nrun {}\n");
}

// ---- fields (§3.4) ----

#[test]
fn field_clash_overlapping_sigs_rejected_probe_06() {
    // A and B overlap (B extends A), both declare `f`.
    let e = reject("sig A { f: A }\nsig B extends A { f: A }\n");
    assert!(matches!(e, ResolveError::FieldNameClash { .. }), "{e:?}");
}

#[test]
fn disjoint_sigs_reuse_field_name_accepted() {
    accept("sig A { f: A }\nsig B { f: B }\n");
}

#[test]
fn dup_field_in_one_sig_rejected() {
    let e = reject("sig A { f: A, f: A }\n");
    assert!(matches!(e, ResolveError::DuplicateField { .. }), "{e:?}");
}

// ---- implicit `this` (§3.3) ----

#[test]
fn sig_fact_uses_own_field_probe_22_23() {
    // `some f` inside the sig's appended fact resolves via implicit `this`.
    accept("sig A { f: set A } { some f }\n");
}

#[test]
fn bare_field_at_top_level_accepted_probe_14() {
    // At top level (no rootsig) `some f` is the whole relation, non-empty test.
    accept("sig A { f: set A }\nfact { some f }\n");
}

// ---- enums (§3.2), auto-alias `ordering` (§2.4) ----

#[test]
fn enum_ordering_bare_first_accepted_probe_20() {
    accept("enum Color { Red, Green, Blue }\nfact { some first }\n");
}

#[test]
fn enum_ordering_qualified_accepted_probe_21() {
    accept("enum Color { Red, Green, Blue }\nfact { some ordering/first }\n");
}

#[test]
fn enum_has_no_enumname_namespace_probe_09() {
    // `Color/first` is rejected: the ordering is aliased `ordering`, not `Color`.
    let e = reject("enum Color { Red, Green, Blue }\nfact { some Color/first }\n");
    assert!(matches!(e, ResolveError::UnknownName { .. }), "{e:?}");
}

// ---- expression typing (§4) ----

#[test]
fn unknown_name_rejected_probe_08() {
    let e = reject("sig A {}\nfact { some nope }\n");
    assert!(matches!(e, ResolveError::UnknownName { .. }), "{e:?}");
}

#[test]
fn arity_mismatch_rejected_probe_13() {
    // `A = f` compares a unary sig with a binary field.
    let e = reject("sig A { f: A -> A }\nfact { A = f }\n");
    assert!(matches!(e, ResolveError::ArityMismatch { .. }), "{e:?}");
}

#[test]
fn ambiguous_call_rejected_probe_15() {
    // Two overloaded `foo` both apply to a `univ` argument → ambiguous call.
    let e = reject(
        "sig A {}\nsig B {}\n\
         fun foo[x: A]: A { x }\n\
         fun foo[x: B]: B { x }\n\
         pred p[y: univ] { some foo[y] }\nrun p\n",
    );
    assert!(matches!(e, ResolveError::AmbiguousName { .. }), "{e:?}");
}

#[test]
fn plus_is_set_union_not_arith_probe_03() {
    // `#(1+2) = 2`: `+` is union, so `{1,2}` has cardinality 2 — accepts.
    accept("fact { #(1 + 2) = 2 }\n");
}

#[test]
fn int_field_equals_literal_probe_02() {
    // `a.n = 1`: both sides are `is_int`, so `=` type-checks.
    accept("sig A { n: Int }\nfact { all a: A | a.n = 1 }\n");
}

#[test]
fn util_integer_plus_probe_04() {
    // `plus[1,2] = 3` via the (auto-opened) util/integer.
    accept("fact { plus[1, 2] = 3 }\nrun {}\n");
}

// ---- funcs/preds (§3.5) ----

#[test]
fn overloaded_preds_accepted_probe_68() {
    accept("pred p {}\npred p {}\nrun {}\n");
}

#[test]
fn recursion_not_rejected_probe_12() {
    accept("sig A {}\npred p[a: A] { p[a] }\nrun {}\n");
}

#[test]
fn fun_body_arity_mismatch_rejected_probe_35() {
    // Body `f` is binary, declared return `A` is unary.
    let e = reject("sig A { f: A -> A }\nfun g: A { f }\n");
    assert!(matches!(e, ResolveError::FuncBodyArity { .. }), "{e:?}");
}

#[test]
fn dup_param_rejected() {
    let e = reject("sig A {}\npred p[x: A, x: A] {}\n");
    assert!(matches!(e, ResolveError::DuplicateParam { .. }), "{e:?}");
}

// ---- facts / asserts / macros (§3.3/§3.6/§3.7) ----

#[test]
fn dup_fact_names_accepted_probe_67() {
    accept("fact F {}\nfact F {}\nrun {}\n");
}

#[test]
fn dup_assert_rejected() {
    let e = reject("assert A {}\nassert A {}\n");
    assert!(matches!(e, ResolveError::DuplicateAssert { .. }), "{e:?}");
}

#[test]
fn top_level_macro_accepted_probe_43() {
    accept("sig A { f: A }\nlet g[x] = x.f\nfact { all a: A | some g[a] }\n");
}

#[test]
fn dup_macro_rejected() {
    let e = reject("let m = 1\nlet m = 2\n");
    assert!(matches!(e, ResolveError::DuplicateMacro { .. }), "{e:?}");
}

// ---- commands (§3.6) ----

#[test]
fn run_missing_pred_rejected_probe_32() {
    let e = reject("sig A {}\nrun nope\n");
    assert!(
        matches!(e, ResolveError::CommandTargetNotFound { .. }),
        "{e:?}"
    );
}

#[test]
fn check_missing_assert_rejected_probe_33() {
    let e = reject("sig A {}\ncheck nope\n");
    assert!(
        matches!(e, ResolveError::CommandTargetNotFound { .. }),
        "{e:?}"
    );
}

#[test]
fn scope_missing_sig_rejected_probe_34() {
    let e = reject("sig A {}\nrun {} for 3 but 2 Nope\n");
    assert!(matches!(e, ResolveError::ScopeSigNotFound { .. }), "{e:?}");
}

#[test]
fn named_pred_run_accepted() {
    accept("sig A {}\npred p { some A }\nrun p\n");
}

// ---- empty models (§6 gotcha 4) ----

#[test]
fn only_a_sig_accepted_probe_60() {
    accept("sig A {}\n");
}

#[test]
fn comment_only_accepted_probe_61() {
    accept("// nothing here\n");
}

// ---- string literals (§4.5) ----

#[test]
fn string_literal_field_accepted_probe_28() {
    accept("sig A { name: String }\nfact { all a: A | a.name = \"hello\" }\n");
}

// ---- determinism (STYLE U4) ----

#[test]
fn resolution_is_deterministic() {
    let src = "sig A { f: set A }\nsig B extends A {}\n\
               pred p[x: A] { x in f }\nrun p for 3\n";
    let a = format!("{:?}", check(src));
    let b = format!("{:?}", check(src));
    assert_eq!(a, b, "resolution must be byte-stable across runs");
}
