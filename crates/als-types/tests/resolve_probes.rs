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

// ---- mt-020 differential gauge fixes (docs/reference/alloy4fun-resolve-pass.md) ----
// Each of these is a jar-verified verdict the alloy4fun differential surfaced:
// the reject tests close over-acceptances (mettle used to accept), the accept
// tests close drop-in violations (mettle used to wrongly reject).

#[test]
fn closure_on_non_binary_rejected_mt020() {
    // `^A` on a unary sig: the reference rejects "^ can be used only with a
    // binary relation" (resolution-doc §4.2). mettle used to accept.
    let e = reject("sig A {}\nfact { some ^A }\n");
    assert!(
        matches!(e, ResolveError::UnaryNotBinary { op: "^", .. }),
        "{e:?}"
    );
}

#[test]
fn transpose_on_non_binary_rejected_mt020() {
    let e = reject("sig A {}\nfact { some ~A }\n");
    assert!(
        matches!(e, ResolveError::UnaryNotBinary { op: "~", .. }),
        "{e:?}"
    );
}

#[test]
fn set_as_formula_rejected_mt020() {
    // A bare sig as a fact body is a set, not a formula (`typecheck_as_formula`,
    // resolution-doc §4.3). Jar: "This must be a formula expression."
    let e = reject("sig A {}\nfact { A }\n");
    assert!(matches!(e, ResolveError::NotFormula { .. }), "{e:?}");
}

#[test]
fn formula_as_set_rejected_mt020() {
    // `some (A in A)`: `some` needs a set, but `A in A` is a formula
    // (`typecheck_as_set`). Jar rejects (as a failed typecheck).
    let e = reject("sig A {}\nfact { some (A in A) }\n");
    assert!(matches!(e, ResolveError::NotSet { .. }), "{e:?}");
}

#[test]
fn non_int_comparison_rejected_mt020() {
    // `A < A`: `<` requires integer operands (`typecheck_as_int`). Jar: "This
    // must be an integer expression."
    let e = reject("sig A {}\nfact { A < A }\n");
    assert!(matches!(e, ResolveError::NotInt { .. }), "{e:?}");
}

#[test]
fn subset_sig_implicit_this_accepted_mt020() {
    // Inside a `sig D in P` appended fact, the ancestor field `parts` resolves
    // via implicit `this` (a `D` atom *is* a `P`), so `this not in parts` is
    // unary-vs-unary and type-checks. mettle used to reject with an arity
    // mismatch (subset-sig `isSameOrDescendentOf`). Jar accepts.
    accept("sig P { parts: set P }\nsig D in P {}{ this not in parts }\n");
}

#[test]
fn field_named_like_stdlib_pred_accepted_mt020() {
    // `pos` is both a user field and an (auto-opened) `util/integer` pred. On
    // `t.pos` the pred does not apply to a non-`Int` `t`, so the field-join
    // reading wins. mettle used to commit to the vacuous pred call and reject
    // the result as a non-set. Jar accepts.
    accept("sig T {}\nsig X { pos: lone T }\npred p { all t: X | some t.pos }\nrun p\n");
}

#[test]
fn overload_disambiguated_by_relevant_type_accepted_mt020() {
    // `foo[a + b]` on the RHS of `in` gets the relevant type `A`, which narrows
    // the two `foo` overloads to the `A`-returning one (ADR-0009 decision 3, the
    // top-down retry, applied to call choices). mettle used to reject as
    // ambiguous. Jar accepts. (On the LHS, with no relevant type, both still
    // stay ambiguous — see `ambiguous_call_rejected_probe_15`.)
    accept(
        "sig A {}\nsig B {}\n\
         fun foo[x: A]: A { x }\n\
         fun foo[x: B]: B { x }\n\
         pred p[a: A, b: B] { a in foo[a + b] }\nrun p\n",
    );
}

#[test]
fn higher_order_macro_accepted_mt020() {
    // A macro that receives a callable by name (`m[ax]`) is resolved
    // accept-lean: mettle binds macro params by type, so it cannot reproduce the
    // reference's textual substitution turning `axiom[univ]` into a real call.
    // Used to reject (the substituted body typed as a non-formula). Jar accepts.
    accept("pred ax[x: univ] { some x }\nlet m[axiom] { axiom[univ] }\nfact { m[ax] }\n");
}

// ---- mt-022: precise per-node relevant types (all jar-verified) ----

#[test]
fn illegal_join_rejected_mt022() {
    // `A.A` joins two unary sets → arity-0 join → `ExprBadJoin`. With the
    // faithful `Type::join` (empty products kept with arity) mettle now fires
    // `IllegalJoin` exactly when both operands are unary. Jar: REJECT.
    let e = reject("sig A {}\nfact { some A.A }\n");
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

#[test]
fn legal_but_empty_join_accepted_mt022() {
    // `D.f.C`: `D.f` = A->B, `.C` joins a disjoint column → a `NONE`-headed
    // arity-1 product (empty but a *legal* relation), not an illegal join. The
    // reference keeps the arity; mettle used to drop it. Jar: ACCEPT.
    accept("sig A {}\nsig B {}\nsig C {}\nsig D { f: A -> B }\nfact { some D.f.C }\n");
}

#[test]
fn ambiguous_bare_field_rejected_mt022() {
    // A bare `f` matching two unrelated fields, used at a definite set position
    // (`some f`), is a genuine "This name is ambiguous" reject once mettle
    // resolves the `ExprChoice` against the precise relevant type. Jar: REJECT.
    let e = reject("sig A { f: A }\nsig B { f: B }\nfact { some f }\n");
    assert!(matches!(e, ResolveError::AmbiguousName { .. }), "{e:?}");
}

#[test]
fn at_name_skips_binder_shadow_mt022() {
    // `@t` never binds the lexical env: inside a sig fact with a quantifier
    // `t`, `this.@t` is the field `t` (E->T), not the bound var. Jar: ACCEPT.
    accept("sig T {}\nsig E { t: T } { all t: T | t = this.@t implies some t }\n");
}

#[test]
fn empty_arg_call_applies_mt022() {
    // `max` applies to an argument even when it is statically empty (the
    // reference's `applicable` skips the intersection test for an empty arg),
    // so `p.grades.max` resolves as a call, not an illegal join. Jar: ACCEPT.
    accept(
        "open util/ordering[G]\nsig G {}\nsig P { grades: set G }\n\
         pred q { all p: P | some p.grades.max }\nrun q\n",
    );
}

#[test]
fn domain_restrict_nonunary_rejected_mt022() {
    // The domain of `<:` must be a unary set; `f <: A` with a binary `f` is
    // "This must be a unary set". Jar: REJECT.
    let e = reject("sig A { f: A -> A }\nfact { some (f <: A) }\n");
    assert!(matches!(e, ResolveError::NotUnarySet { .. }), "{e:?}");
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

// ---- mt-025: materialized typed tree / precise top-down relevant threading ----
// The full two-pass structure (ADR-0008 decision 4) lets mettle reproduce the
// reference's `ExprChoice` disambiguation on precise types. Every verdict below
// is jar-verified (Alloy 6.2.0, `parseEverything_fromFile`).

/// Left-of-join field ambiguity: `s.projects` under a `-` whose relevant slice
/// is empty leaves both `projects` fields surviving `hasCommonArity` — the jar's
/// "This name is ambiguous". (The mt-022 remainder this bead closes.)
#[test]
fn left_of_join_ambiguous_rejected_mt025() {
    let e = reject(
        "sig Person { enrolled: set Course, projects: set Project }\n\
         sig Course { projects: set Project }\nsig Project {}\nsig Student in Person {}\n\
         pred p { all s: Student | no s.enrolled - s.projects }\nrun p\n",
    );
    assert!(matches!(e, ResolveError::AmbiguousName { .. }), "{e:?}");
}

/// The companion accept the earlier naive tightening broke: a plain `s.projects`
/// join disambiguates via the join slice (only `Person.projects` joins `s`).
#[test]
fn left_of_join_disambiguated_accepted_mt025() {
    accept(
        "sig Person { enrolled: set Course, projects: set Project }\n\
         sig Course { projects: set Project }\nsig Project {}\nsig Student in Person {}\n\
         pred p { all s: Student | some s.projects }\nrun p\n",
    );
}

/// `~this/next` scopes to the current module's own `next` (`getRawQS`), so it is
/// unambiguous even though `util/integer`'s `next` is auto-opened.
#[test]
fn this_qualified_scopes_to_own_module_accepted_mt025() {
    accept(
        "sig T {}\none sig O { Next: T->T }\nfun next: T -> T { O.Next }\n\
         fun prev: T -> T { ~this/next }\nrun {}\n",
    );
}

/// Bare `~next` in a user module IS ambiguous with the auto-opened
/// `integer/next` (both `T->T` and `Int->Int` survive under `~`).
#[test]
fn bare_next_under_transpose_ambiguous_rejected_mt025() {
    let e = reject(
        "sig T {}\none sig O { Next: T->T }\nfun next: T -> T { O.Next }\n\
         fun prev: T -> T { ~next }\nrun {}\n",
    );
    assert!(matches!(e, ResolveError::AmbiguousName { .. }), "{e:?}");
}

/// Per-call return-type specialization (`DeduceType`): `dom[grades]` yields
/// `Course`, not the declared `univ`, so `dom[grades].projects` is unambiguous.
#[test]
fn call_return_type_specialized_accepted_mt025() {
    accept(
        "open util/ternary\nsig Person { projects: set Project }\n\
         sig Course { projects: set Project, grades: Person -> Grade }\n\
         sig Project {}\nsig Grade {}\n\
         pred t { let c = dom[grades] | some c.projects }\nrun t\n",
    );
}

/// An unknown name as a join right operand is a genuine "cannot be found"
/// reject, not a lenient `univ` (the mt-025 spine-head fix).
#[test]
fn unknown_name_in_join_rejected_mt025() {
    let e = reject(
        "sig Work { source: one State }\nsig State {}\n\
         pred q { some source.s }\nrun q\n",
    );
    assert!(matches!(e, ResolveError::UnknownName { .. }), "{e:?}");
}

/// A comprehension decl that redeclares an earlier variable and calls a func in
/// its bound resolves the bound once with the correct incremental env (the
/// type-computation loop must not re-resolve under the shadowed name).
#[test]
fn comprehension_redeclared_var_accepted_mt025() {
    accept(
        "sig PTCris { notifications: set Notification }\nsig Notification {}\n\
         sig Modification extends Notification {}\nsig Production {}\n\
         fun modifies_[p:PTCris,n:Modification] : Production { Production }\n\
         fun _modifies_ : PTCris -> Modification -> Production {\n\
           {p:PTCris, n:p.notifications&Modification, p:modifies_[p,n]}\n}\nrun {}\n",
    );
}

/// A 0-param `let` macro applied on the right of a join (`enrolled.cProjects`)
/// expands to its body relation and joins — not a spurious macro call that
/// drops the join operand.
#[test]
fn zero_param_macro_join_accepted_mt025() {
    accept(
        "sig Person { enrolled: set Course, projects: set Project }\n\
         sig Course { projects: set Project }\nsig Project {}\nsig Student in Person {}\n\
         let cProjects = Course <: projects\nlet sProjects = Student <: projects\n\
         pred inv { sProjects in enrolled.cProjects }\nrun inv\n",
    );
}
