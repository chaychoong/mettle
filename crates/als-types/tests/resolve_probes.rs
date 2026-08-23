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

// ---- mt-108: the `$` metamodel gate (resolution-doc §1 phase 8, ADR-0024) ----
//
// mettle does not synthesize the reference's meta sigs, so a model that plausibly
// uses them resolves accept-lean (`Cx::lenient`). The gate matches only the names
// `resolveMeta` would actually mint — every stray `$` below is jar-verified as a
// reject, against `oracle/org.alloytools.alloy.dist.jar`.

/// `sig$` is a reserved meta name: the gate fires and the model resolves
/// leniently. Jar: ACCEPT (resolution-doc §10 probe 44, "some sig$").
#[test]
fn builtin_meta_name_is_lenient_mt108() {
    accept("sig A {}\nfact { some sig$ }\nrun {}\n");
}

/// `S$` for a declared sig is a meta name (the reference mints `s.label + \"$\"`),
/// so the whole model stays accept-lean. Jar: SAT on the mt-097 a3/a4 cells.
#[test]
fn meta_sig_name_is_lenient_mt108() {
    accept("sig V { left: lone V, right: lone V }\nrun { some V$ } for 3\n");
    accept("sig V { left: lone V, right: lone V }\nrun { #V$.subfields = 2 } for 3\n");
}

/// `S$f` is a meta name only when `f` is a field **`S` itself declares** — the
/// reference mints `s.label + \"$\" + field.label` per owning sig. A field name
/// that `S` does not own leaves the gate shut, so the name rejects normally.
#[test]
fn meta_field_name_needs_a_real_field_mt108() {
    accept("sig A { f: lone A }\nfact { some A$f }\nrun {}\n");
    let e = reject("sig A { f: lone A }\nfact { some A$g }\nrun {}\n");
    assert!(matches!(e, ResolveError::UnknownName { .. }), "{e:?}");
}

/// A stray `$` buys no leniency. Both shapes are alloy4fun codes the jar rejects
/// with exactly this message: `$Protected` (028779:49:13, "The name
/// \"$Protected\" cannot be found") and a bare `$` (126919:46:25, "The name
/// \"$\" cannot be found").
#[test]
fn stray_dollar_name_rejected_mt108() {
    let e =
        reject("sig File {}\nsig Trash in File {}\npred inv5 { $Protected in Trash }\nrun inv5\n");
    assert!(matches!(e, ResolveError::UnknownName { .. }), "{e:?}");
    let e = reject("sig A { f: lone A }\nfact { some $ }\nrun {}\n");
    assert!(matches!(e, ResolveError::UnknownName { .. }), "{e:?}");
}

/// The gate is a property of the **model**, not of each name — as the
/// reference's own `seenDollar` is. One real meta name therefore excuses the
/// stray one alongside it; that is the accept-lean posture working as designed,
/// not a hole in the narrowing.
#[test]
fn one_meta_name_leniences_the_whole_model_mt108() {
    accept("sig A {}\nfact { some A$ and $stray in A }\nrun {}\n");
}

/// A parameter *alias* is not a meta name: the reference names meta sigs after
/// the argument sig's own label, so `elem$` denotes nothing even inside
/// `util/ordering`'s own module.
#[test]
fn param_alias_is_not_a_meta_name_mt108() {
    let e = reject("sig A {}\nopen util/ordering[A]\nfact { some elem$ }\nrun {}\n");
    assert!(matches!(e, ResolveError::UnknownName { .. }), "{e:?}");
}

// ---- mt-110: three accept-lean leniencies the reference does not grant ----
//
// Each cell below was run against `oracle/org.alloytools.alloy.dist.jar`; the
// three rejects are the jar's "possible incorrect function/predicate call",
// "This must be a set or relation" and `The name "this" cannot be found.`

/// A bare name denoting a func *with parameters*, used as a value, is the
/// reference's `ExprBadCall` — a call spine that never gained its arguments.
/// The dominant corpus shape is `add` from the auto-opened `util/integer`.
#[test]
fn bare_func_with_params_as_value_rejected_mt110() {
    let e = reject("sig A {}\nfun add2[x: A]: A { x }\nrun { some add2 } for 3\n");
    assert!(matches!(e, ResolveError::BadCall { .. }), "{e:?}");
    let e = reject("sig A {}\nrun { some a: add | a in A } for 3\n");
    assert!(matches!(e, ResolveError::BadCall { .. }), "{e:?}");
    // A receiver func's `this` is param 0, so it too needs an argument.
    let e = reject("sig A {}\nfun A.mine[x: A]: A { x }\nrun { some mine } for 3\n");
    assert!(matches!(e, ResolveError::BadCall { .. }), "{e:?}");
    // The leniency the macro path keeps is macro-only: a callable-by-name
    // argument to an ordinary *pred* is the same uncompleted call spine, and the
    // jar rejects it too.
    let e = reject(
        "sig A {}\nfun add2[x: A]: A { x }\npred p[y: univ] { some y }\nrun { p[add2] } for 3\n",
    );
    assert!(matches!(e, ResolveError::BadCall { .. }), "{e:?}");
    // …and as a join base, where the spine's own `BadCall` reading rejects.
    let e = reject("sig A {}\nfun add2[x: A]: A { x }\nrun { some add2.A } for 3\n");
    assert!(matches!(e, ResolveError::BadCall { .. }), "{e:?}");
}

/// The carve-outs. A 0-ary func/pred is a genuine value (a value candidate, so
/// it never reaches the bad-call path), every real call form still completes,
/// and a callable passed to a higher-order macro by bare name stays lenient
/// (mt-040) — the macro binds it by name, not by type.
#[test]
fn real_calls_and_zero_ary_funcs_still_accept_mt110() {
    accept("sig A {}\nfun all_a: A { A }\nrun { some all_a } for 3\n");
    accept("sig A {}\npred p0 {}\nrun { p0 } for 3\n");
    accept("sig A {}\nfun add2[x: A]: A { x }\nrun { some add2[A] } for 3\n");
    accept("sig A { f: set A }\nfun g[x: A]: A { x }\nrun { some A.f.g } for 3\n");
    accept("sig A {}\nfun A.mine[x: A]: A { x }\nrun { some A.mine[A] } for 3\n");
    accept("pred ax[x: univ] { some x }\nlet m[axiom] { axiom[univ] }\nfact { m[ax] }\n");
    accept("sig A {}\nlet m[c] { some c[A] }\nfun add2[x: A]: A { x }\nfact { m[add2] }\n");
}

/// A meta-gate model stays accept-lean throughout: the bad-call reject is
/// suppressed exactly as the name/ambiguity rejects are.
#[test]
fn meta_gate_keeps_bare_callable_lenient_mt110() {
    accept("sig A {}\nfun add2[x: A]: A { x }\nrun { some add2 and some A$ } for 3\n");
}

/// `->` sort-checks its operands even though a formula operand empties the
/// arrow slice (whose fallback then hands the raw FORMULA type back). The
/// corpus shape is a student writing `->` where they meant `implies`.
#[test]
fn arrow_operand_must_be_a_set_mt110() {
    let e = reject("sig A {}\nrun { some A -> (A in A) } for 3\n");
    assert!(matches!(e, ResolveError::NotSet { .. }), "{e:?}");
    let e = reject("sig A {}\nrun { some (A in A) -> A } for 3\n");
    assert!(matches!(e, ResolveError::NotSet { .. }), "{e:?}");
}

/// Ordinary arrows between sets are untouched.
#[test]
fn arrow_between_sets_still_accepts_mt110() {
    accept("sig A {}\nsig B {}\nrun { some A -> B } for 3\n");
    accept("sig A { f: set A }\nrun { A -> A in A -> A } for 3\n");
    accept("sig A {}\nsig B { g: A -> A }\nrun { some g } for 3\n");
}

/// Bare `this` outside any sig context has nothing to bind to.
#[test]
fn bare_this_outside_sig_rejected_mt110() {
    let e = reject("sig A {}\nfact { this in A }\nrun {} for 3\n");
    assert!(matches!(e, ResolveError::UnknownName { .. }), "{e:?}");
    let e = reject("sig A {}\npred p { this in A }\nrun p for 3\n");
    assert!(matches!(e, ResolveError::UnknownName { .. }), "{e:?}");
}

/// `this` keeps working wherever the reference binds it: a sig's appended fact,
/// a field declaration's bound, and a receiver func's body.
#[test]
fn this_in_sig_context_still_accepts_mt110() {
    accept("sig A { f: set A } { this in A }\nrun {} for 3\n");
    accept("sig A { f: set A, g: set this }\nrun {} for 3\n");
    accept("sig A {}\nfun A.mine: A { this }\nrun { some A.mine } for 3\n");
}

// ---- mt-111: the multiplicity-flag positional rule (LEDGER-016) ----
//
// A multiplicity-tagged expression — prefix `set`/`seq` anywhere, prefix
// `some`/`lone`/`one` only where the grammar's `mult()` converts them, arrow
// multiplicities (which propagate up an arrow chain), and `exactly` inside a
// defined-field bound — is legal in six consuming positions and rejected
// everywhere else. Every cell below is one file from the mt-109 probe wave
// (`scratchpad/probe/mt109/{m,n,p,q}/`), verdict-pinned against
// `oracle/org.alloytools.alloy.dist.jar` (Alloy 6.2.0).
//
// The accepts are the drop-in guards: this is the one residual family whose fix
// can *create* drop-in violations (a check placed one level too broadly turns
// legal models into rejects), so they are pinned before the check is switched on.

/// Consume site 1: **sig field decl bounds** take every multiplicity, including
/// an arrow mult and a nested arrow chain. Cells m01 m02 m06 m08 m43 n20 p08.
#[test]
fn mult_in_field_decl_bound_accepted_mt111() {
    accept("sig A {}\nsig B { f: lone A }\nrun {} for 3\n"); // m01
    accept("sig A {}\nsig B { f: A -> lone A }\nrun {} for 3\n"); // m02
    accept("sig A {}\nsig B { f: A -> (A -> lone A) }\nrun {} for 3\n"); // m06
    accept("sig A {}\nsig B { f: set A }\nrun {} for 3\n"); // m08
    accept("sig A {}\nsig B { f: seq A }\nrun {} for 3\n"); // m43
    accept("sig A {}\nsig B { f: A one -> lone A }\nrun {} for 3\n"); // n20
    accept("sig A {}\nsig B { f: some A }\nrun {} for 3\n"); // p08
}

/// Consume sites 2 and 3: **fun/pred parameter decl bounds** (m07 n13) and
/// **function return decls** (m04 q03 m32).
#[test]
fn mult_in_param_and_return_decl_accepted_mt111() {
    accept("sig A {}\npred p[x: lone A] { x = x }\nrun { p[A] } for 3\n"); // m07
    accept("sig A {}\npred p[x: set A] { some x }\nrun { p[A] } for 3\n"); // n13
    accept("sig A {}\nfun f: lone A { A }\nrun { some f } for 3\n"); // m04
    accept("sig A {}\nfun f: set A { A }\nrun { some f } for 3\n"); // q03
    accept("sig A {}\nfun f: A -> lone A { A -> A }\nrun { some f } for 3\n"); // m32
}

/// Consume site 4: **quantifier decl bounds accept every multiplicity** — this
/// is the half of `decl_bound_type` that must stay permissive (the comprehension
/// half is strict; see `comprehension_bound_rejects_all_but_one_of_mt111`).
/// Cells m03 m10 m31 p05 p06 p18, across `all`/`some`/`sum` and multi-decls.
#[test]
fn mult_in_quantifier_bound_accepted_mt111() {
    accept("sig A {}\nrun { all x: lone A | x = x } for 3\n"); // m03
    accept("sig A {}\nrun { some x: set A | x = x } for 3\n"); // m10
    accept("sig A {}\nrun { all x: A -> lone A | some x } for 3\n"); // m31
    accept("sig A {}\nrun { some x: some A | x = x } for 3\n"); // p05
    accept("sig A {}\nfact { (sum x: one A | 1) > 0 }\nrun {} for 3\n"); // p06
    accept("sig A {}\nrun { all x: set A, y: lone A | x = y } for 3\n"); // p18
}

/// Consume site 5: `in` is **asymmetric** — its RIGHT operand consumes the flag.
/// Cells n18 p16 m25 n11 p11. (The left operand rejects: cell m26, below.)
#[test]
fn mult_on_rhs_of_in_accepted_mt111() {
    accept("sig A {}\nfact { A in (set A) }\nrun {} for 3\n"); // n18
    accept("sig A {}\nsig B { f: A }\nfact { B.f in (some A) }\nrun {} for 3\n"); // p16
    accept("sig A {}\nsig B { r: A -> A }\nfact { B.r in A -> lone A }\nrun {} for 3\n"); // m25
    accept("sig A { r: A }\nfact { r in A -> lone A }\nrun {} for 3\n"); // n11
    accept("sig A {}\nfact { let x = A | x in (set A) }\nrun {} for 3\n"); // p11
}

/// Consume site 6, the counterintuitive one: **function and predicate BODIES
/// accept mult.** A "reject everywhere outside the decl list" design breaks
/// these three, so they are the sharpest guard in the suite. Cells m18 q01 q02,
/// plus q06/q07 where such a body's result is then used in an ordinary formula.
#[test]
fn mult_in_fun_body_accepted_mt111() {
    accept("sig A {}\nfun f: A { set A }\nrun { some f } for 3\n"); // m18
    accept("sig A {}\nfun f: A -> A { A -> lone A }\nrun { some f } for 3\n"); // q01
    accept("sig A {}\nfun f: A { (set A) }\nrun { some f } for 3\n"); // q02
    accept("sig A {}\npred p { some A }\nfun f: A { set A }\nfact { f = A }\nrun {} for 3\n"); // q06
    accept("sig A {}\nfun f: A -> lone A { A -> A }\nfact { some f and f = f }\nrun {} for 3\n");
    // q07
}

/// A comprehension bound may be `one`-of, because `ONEOF` is the decl default.
/// Cell p01 — the single accept inside the otherwise-strict comprehension rule.
#[test]
fn comprehension_bound_one_of_accepted_mt111() {
    accept("sig A {}\nfact { some { x: one A | x = x } }\nrun {} for 3\n"); // p01
}

/// A **defined field** (`f = e`) takes a mult-*free* RHS. Cells m33 n05 m37 q08;
/// the mult-carrying spellings n07/n09 reject (below).
#[test]
fn mult_free_defined_field_accepted_mt111() {
    accept("sig A {}\nsig B { f = A }\nrun {} for 3\n"); // m33
    accept("sig A {}\nsig B { f = A, g = f }\nrun {} for 3\n"); // n05
    accept("sig A {}\nsig B { f = A }\nfact { some B.f }\nrun {} for 3\n"); // m37
    accept("sig A {}\nsig B { f = A }\nfact { some { x: B | some x.f } }\nrun {} for 3\n");
    // q08
}

/// The flag does **not** survive macro expansion into the use site: a top-level
/// `let` macro whose body is `set A` is legal, and `some S` at the use site is
/// legal too. Cell q05 — this is why the flag can stay a syntactic predicate on
/// the original node instead of a value carried through resolution.
#[test]
fn mult_does_not_survive_macro_expansion_mt111() {
    accept("sig A {}\nlet S = set A\nfact { some S }\nrun {} for 3\n"); // q05
}

/// `exactly` in a scope is untouched by any of this. Cell m36.
#[test]
fn exactly_in_a_scope_accepted_mt111() {
    accept("sig A {}\nrun {} for exactly 3 A\n"); // m36
}

/// The **precedence trap**, not the mult rule: a bare unparenthesized mult after
/// `in` is a *parse* reject on both sides (mettle's operand tier, "this prefix
/// operator binds too loosely"; the jar's `mult()` tier). Parenthesizing makes
/// the same shape legal — see `mult_on_rhs_of_in_accepted_mt111` (n18). This is
/// why the residual gap lives exclusively in bracketed/argument/body positions.
/// Cells m05 m09 m23 n15.
#[test]
fn bare_mult_after_in_is_a_parse_reject_mt111() {
    for src in [
        "sig A {}\nfact { A in lone A }\nrun {} for 3\n", // m05
        "sig A {}\nfact { A in set A }\nrun {} for 3\n",  // m09
        "sig A {}\nfact { all x: A | x in set A }\nrun {} for 3\n", // m23
        "sig A {}\nrun { some x: A | x in set A } for 3\n", // n15
    ] {
        let e = reject(src);
        assert!(matches!(e, ResolveError::OpenedFileParse { .. }), "{e:?}");
    }
}

/// `exactly` is **not an expression prefix at all** — it is reachable only from
/// a defined-field bound, so every other spelling fails to parse. This refuted
/// the pre-run prediction that `exactly` would merely be a narrower mult; it
/// also makes the jar's "This cannot be an exactly-of expression." effectively
/// unreachable from source syntax. Cells m34 m35 m38 m39 n01 n02 n03 p15.
#[test]
fn exactly_is_not_an_expression_prefix_mt111() {
    for src in [
        "sig A {}\nrun { all x: exactly A | x = x } for 3\n", // m34
        "sig A {}\nfact { some exactly A }\nrun {} for 3\n",  // m35
        "sig A {}\npred p[x: exactly A] { some x }\nrun { p[A] } for 3\n", // m38
        "sig A {}\nsig B { f: A }\nfact { B.f in exactly A }\nrun {} for 3\n", // m39
        "sig A {}\nsig B { f: exactly A }\nrun {} for 3\n",   // n01
        "sig A {}\nfun f: exactly A { A }\nrun { some f } for 3\n", // n02
        "sig A {}\nsig C in exactly A {}\nrun {} for 3\n",    // n03
        "sig A {}\nsig B { f: A -> exactly A }\nrun {} for 3\n", // p15
    ] {
        let e = reject(src);
        assert!(matches!(e, ResolveError::OpenedFileParse { .. }), "{e:?}");
    }
}

/// Where `mult()` does **not** convert them, `some`/`lone`/`one` stay *formula*
/// operators — so these reject as non-sets, for a different reason than the mult
/// rule, and mettle already agrees. Cells m41 (`some (lone A)`) and n08
/// (`f = lone A`, a defined field whose RHS is a formula).
#[test]
fn unconverted_lone_stays_a_formula_mt111() {
    let e = reject("sig A {}\nfact { some (lone A) }\nrun {} for 3\n"); // m41
    assert!(matches!(e, ResolveError::NotSet { .. }), "{e:?}");
    let e = reject("sig A {}\nsig B { f = lone A }\nrun {} for 3\n"); // n08
    assert!(matches!(e, ResolveError::NotSet { .. }), "{e:?}");
}

/// Rejects the mult rule must not swallow: these cells carry a multiplicity but
/// fail first for an ordinary typing reason, and mettle already agrees with the
/// jar on all of them. Cells n06 (a defined field is not a type), n10/n17/p10
/// (arity), n14/p14 (a mult operand under a join that is illegal anyway), q04
/// (`seq` makes the return binary, so a unary body mismatches).
#[test]
fn mult_cells_that_fail_for_ordinary_reasons_mt111() {
    let e = reject("sig A {}\nsig B { f = A, g: f }\nrun {} for 3\n"); // n06
    assert!(matches!(e, ResolveError::UnknownName { .. }), "{e:?}");
    for src in [
        "sig A {}\nfact { A in A -> lone A }\nrun {} for 3\n", // n10
        "sig A { r: A }\nfact { r in A -> A -> lone A }\nrun {} for 3\n", // n17
        "sig A { r: A -> A -> A }\nfact { r in A -> (A -> lone A) }\nrun {} for 3\n", // p10
    ] {
        let e = reject(src);
        assert!(matches!(e, ResolveError::ArityMismatch { .. }), "{e:?}");
    }
    for src in [
        "sig A {}\nfact { some (set A).A }\nrun {} for 3\n", // n14
        "sig A {}\nfact { some A.(set A) }\nrun {} for 3\n", // p14
    ] {
        let e = reject(src);
        assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
    }
    let e = reject("sig A {}\nfun f: seq A { A }\nrun { some f } for 3\n"); // q04
    assert!(matches!(e, ResolveError::FuncBodyArity { .. }), "{e:?}");
    // n19: `exactly` on the builtin `int` scope is redundant, a parse-tier reject.
    let e = reject("sig A {}\nfact { A = A }\nrun {} for exactly 3 A, exactly 4 int\n");
    assert!(matches!(e, ResolveError::OpenedFileParse { .. }), "{e:?}");
}
