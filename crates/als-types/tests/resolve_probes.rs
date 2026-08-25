//! Resolver/type-checker probe suite (mt-018): the resolution-doc §10 probe
//! table recreated as Rust tests, one accept/reject assertion per pinned jar
//! behavior. Each test cites its probe id. These are the reject-taxonomy gauge
//! (§5.1) plus the "accepts, don't over-reject" companions (§6 gotchas).
//!
//! Loading uses the injected [`MapLoader`]; the embedded clean-room stdlib
//! (mt-015) supplies `util/*` through the normal search order, so enum/ordering
//! and `util/integer` probes resolve without disk.

use als_types::{resolve, MapLoader, ModuleGraph, ResolveError, ResolveWarning};

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
    let e = reject("open util/ordering[A]\nsig A {}\nfact { some elem$ }\nrun {}\n");
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
    // n14 reports the *multiplicity* error rather than the illegal join it also
    // is: the mult guard is a make-time `ErrorSyntax` raised ahead of the
    // ordinary type errors, and a join's LEFT operand is a checked position. The
    // jar agrees on the class here (it reports the mult error too). p14 is the
    // mirror image and keeps the join message on both sides, because a join's
    // compound RIGHT operand is only warning-scanned (mt-023), so the guard
    // never runs there.
    let e = reject("sig A {}\nfact { some (set A).A }\nrun {} for 3\n"); // n14
    assert!(
        matches!(e, ResolveError::MultiplicityNotAllowed { .. }),
        "{e:?}"
    );
    let e = reject("sig A {}\nfact { some A.(set A) }\nrun {} for 3\n"); // p14
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
    let e = reject("sig A {}\nfun f: seq A { A }\nrun { some f } for 3\n"); // q04
    assert!(matches!(e, ResolveError::FuncBodyArity { .. }), "{e:?}");
    // n19: `exactly` on the builtin `int` scope is redundant, a parse-tier reject.
    let e = reject("sig A {}\nfact { A = A }\nrun {} for exactly 3 A, exactly 4 int\n");
    assert!(matches!(e, ResolveError::OpenedFileParse { .. }), "{e:?}");
}

// ---- mt-111 phase 2: the 31 over-accepts the check closes ----
//
// Every cell below was an mt-109 over-acceptance (jar REJECT, mettle OK). The
// jar's message decides which variant each one asserts: 24 are "Multiplicity
// expression not allowed here.", 4 are "This cannot be a <kind>-of expression.",
// 1 is "This must be a unary set.", and 2 (m17/p09) surface jar-side as a call
// resolution failure — see `mult_call_argument_rejected_mt111`.

/// Asserts `src` rejects with the multiplicity error.
fn reject_mult(src: &str) {
    let e = reject(src);
    assert!(
        matches!(e, ResolveError::MultiplicityNotAllowed { .. }),
        "{e:?}\n--- src ---\n{src}"
    );
}

/// Unary operands never consume a multiplicity — not the formula prefixes
/// (`some`/`no`), not `~`, not `#`. Parentheses do not strip the flag: the
/// reference's `NOOP` propagates it and mettle has no paren node at all, so it
/// is structurally immune (p13 double-parenthesizes and still rejects). Cells
/// m11 m22 m42 n16 p13 m30 m14 p12.
#[test]
fn mult_under_a_unary_operator_rejected_mt111() {
    reject_mult("sig A {}\nfact { some (set A) }\nrun {} for 3\n"); // m11
    reject_mult("sig A {}\nfact { no (set A) }\nrun {} for 3\n"); // m22
    reject_mult("sig A {}\nfact { some (seq A) }\nrun {} for 3\n"); // m42
    reject_mult("sig A {}\nfact { not some (set A) }\nrun {} for 3\n"); // n16
    reject_mult("sig A {}\nfact { some ((set A)) }\nrun {} for 3\n"); // p13
    reject_mult("sig A {}\nfact { some ~(A -> lone A) }\nrun {} for 3\n"); // m30
    reject_mult("sig A {}\nfact { #(set A) > 0 }\nrun {} for 3\n"); // m14
    reject_mult("sig A {}\nfact { #(A -> lone A) > 0 }\nrun {} for 3\n"); // p12
}

/// Binary operands do not consume it either — both sides of `=`, `+`, `&`, a
/// join's left operand, and `->` **used as an expression** rather than as a decl
/// bound (m24/m29: the arrow chain propagates the flag up to the node the
/// surrounding `some` then consumes). Cells m12 m13 m27 n12 m15 m28 m16 m24 m29.
#[test]
fn mult_under_a_binary_operator_rejected_mt111() {
    reject_mult("sig A {}\nfact { (set A) = A }\nrun {} for 3\n"); // m12
    reject_mult("sig A {}\nfact { A = (set A) }\nrun {} for 3\n"); // m13
    reject_mult("sig A {}\nsig B { r: A -> A }\nfact { B.r = A -> lone A }\nrun {} for 3\n"); // m27
    reject_mult("sig A { r: A }\nfact { r = A -> lone A implies some A }\nrun {} for 3\n"); // n12
    reject_mult("sig A {}\nfact { some ((set A) + A) }\nrun {} for 3\n"); // m15
    reject_mult("sig A {}\nfact { some ((A -> lone A) & (A -> A)) }\nrun {} for 3\n"); // m28
    reject_mult("sig A { r: A }\nfact { some (set A).r }\nrun {} for 3\n"); // m16
    reject_mult("sig A {}\nfact { some (A -> lone A) }\nrun {} for 3\n"); // m24
    reject_mult("sig A {}\nfact { some (A -> (A -> lone A)) }\nrun {} for 3\n");
    // m29
}

/// The asymmetry of `in`, from the rejecting side: its LEFT operand is an
/// ordinary expression position. Cell m26 — the companion accept is n18/m25 in
/// `mult_on_rhs_of_in_accepted_mt111`, and getting this pair backwards in either
/// direction is the classic way to break this rule.
#[test]
fn mult_on_lhs_of_in_rejected_mt111() {
    reject_mult("sig A {}\nsig B { r: A -> A }\nfact { (A -> lone A) in B.r }\nrun {} for 3\n");
}

/// A `let` binding value is not a consuming position, parenthesized or not.
/// Cells m19 p07. (Contrast q05: a top-level `let` *macro* whose body is
/// `set A` is legal, because the flag does not survive macro expansion.)
#[test]
fn mult_as_a_let_value_rejected_mt111() {
    reject_mult("sig A {}\nfact { let x = set A | some x }\nrun {} for 3\n"); // m19
    reject_mult("sig A {}\nfact { let x = (set A) | some x }\nrun {} for 3\n"); // p07
}

/// Inside an `and` list and an if-then-else, the enclosing formula operators do
/// not launder the flag. Cells m20 m21.
#[test]
fn mult_inside_a_list_or_ite_rejected_mt111() {
    reject_mult("sig A {}\nfact { some (set A) and some A }\nrun {} for 3\n"); // m20
    reject_mult("sig A {}\nfact { some A implies some (set A) else some A }\nrun {} for 3\n");
    // m21
}

/// A **defined** field takes a mult-free RHS only: `= e` is the reference's
/// `EXACTLYOF`, whose own `make` rejects a mult-tagged operand. Cells n07 n09 —
/// the accepting companions are m33/n05 above, and n08 (`f = lone A`) is the
/// negative-space pin: `mult()` does not convert `lone` in this position, so it
/// stays a formula operator and keeps its `NotSet` verdict rather than becoming
/// a multiplicity error.
#[test]
fn mult_as_a_defined_field_bound_rejected_mt111() {
    reject_mult("sig A {}\nsig B { f = set A }\nrun {} for 3\n"); // n07
    reject_mult("sig A {}\nsig B { f = A -> lone A }\nrun {} for 3\n"); // n09
    let e = reject("sig A {}\nsig B { f = lone A }\nrun {} for 3\n"); // n08
    assert!(matches!(e, ResolveError::NotSet { .. }), "{e:?}");
}

/// Comprehension bounds are the strictest position in the language, and the one
/// place with its own message family: every `-of` wrapper but `one` is rejected
/// by name. Cells n04 p02 p03 p17 — and p01, in
/// `comprehension_bound_one_of_accepted_mt111`, is the exception that makes this
/// a *different* rule from the quantifier bounds it shares a code path with.
#[test]
fn comprehension_bound_rejects_all_but_one_of_mt111() {
    for (src, kind) in [
        (
            "sig A {}\nfact { some { x: set A | x = x } }\nrun {} for 3\n", // n04
            "set",
        ),
        (
            "sig A {}\nfact { some { x: A, y: set A | x = y } }\nrun {} for 3\n", // p17
            "set",
        ),
        (
            "sig A {}\nfact { some { x: lone A | x = x } }\nrun {} for 3\n", // p02
            "lone",
        ),
        (
            "sig A {}\nfact { some { x: some A | x = x } }\nrun {} for 3\n", // p03
            "some",
        ),
    ] {
        let e = reject(src);
        assert!(
            matches!(e, ResolveError::CannotBeMultOf { kind: k, .. } if k == kind),
            "{e:?}\n--- src ---\n{src}"
        );
    }
}

/// A comprehension bound must also be **unary**, and that check runs *after* the
/// `-of` one. Cell p04: an arrow is not a `-of` wrapper, so despite carrying an
/// arrow multiplicity it falls through to the arity check and reports the
/// unary-set message — which is exactly what the jar does, and the reason the
/// two checks cannot be collapsed into one.
#[test]
fn comprehension_bound_must_be_unary_mt111() {
    let e = reject("sig A {}\nfact { some { x: A -> lone A | some x } }\nrun {} for 3\n");
    assert!(matches!(e, ResolveError::NotUnarySet { .. }), "{e:?}");
}

/// `exactly`-of is rejected by **every quantifier**, and it is the only way the
/// jar's "This cannot be an exactly-of expression." is reachable from source
/// syntax — the mt-109 wave missed it because it probed `exactly` only as an
/// expression *prefix*, where nothing parses. The reachable spelling is a decl
/// written with `=` instead of `:`, which is 20 alloy4fun codes and the real
/// referent of the mt-025 triage's "exactly-of" bucket. Cells r02 s01 s03 s04
/// s05 (`scratchpad/probe/mt111/`, jar-verified 2026-08-23).
#[test]
fn exactly_of_quantifier_bound_rejected_mt111() {
    for src in [
        "sig A {}\nrun { all x: A, y = A | x = y } for 3\n", // s01
        "sig A {}\nrun { some x: A, y = A | x = y } for 3\n", // s03
        "sig A {}\nfact { (sum x: A, y = A | 1) > 0 }\nrun {} for 3\n", // s04
        "sig A {}\nrun { no x: A, y = A | x = y } for 3\n",  // s05
        "sig A { f: A }\nrun { all x: A, y = A.f | some y } for 3\n", // r02
    ] {
        let e = reject(src);
        assert!(
            matches!(
                e,
                ResolveError::CannotBeMultOf {
                    kind: "exactly",
                    ..
                }
            ),
            "{e:?}\n--- src ---\n{src}"
        );
    }
}

/// The two positions that **do** take a defined (`=`) bound, which the check
/// above must not touch: a fun/pred parameter list (cell s06 — the jar accepts,
/// which is what puts the rejection in `ExprQt.Op.make` rather than in the decl
/// machinery) and a sig field (m33, above). Plus the `:` control, cell s07.
#[test]
fn defined_bound_outside_a_quantifier_still_accepts_mt111() {
    accept("sig A {}\npred p[x: A, y = A] { x = y }\nrun { p[A, A] } for 3\n"); // s06
    accept("sig A {}\nrun { all x: A, y: A | x = y } for 3\n"); // s07
}

/// Call arguments. Cells m17 p09: the jar reports these as a call-resolution
/// failure ("possible incorrect function/predicate call"), because a mult-tagged
/// argument makes the call inapplicable before the multiplicity itself is
/// blamed. mettle reaches the same *verdict* by the shorter route — a call
/// argument is an ordinary checked operand position — so the message class
/// differs while accept-vs-reject agrees, which is what the drop-in gauge
/// measures. No special machinery is built for these.
#[test]
fn mult_call_argument_rejected_mt111() {
    reject_mult("sig A {}\npred p[x: A] { some x }\nrun { p[set A] } for 3\n"); // m17
    reject_mult("sig A {}\npred p[x: A] { some x }\nrun { p[(set A)] } for 3\n");
    // p09
}

// ---- ADR-0023 phase (b): the faithful closure operand type (mt-105) ----
//
// The `^`/`*` arm now pushes the reference's `resolveClosure(p, sub.type)` to
// its operand instead of the operand's own binary shape. Measured effect on the
// 150,891-code alloy4fun gauge: **none** — verdicts, error variants and
// warnings are byte-identical to the pre-change run. That is not an accident
// and it is what these tests pin: every route by which the narrower operand
// type could turn an ACCEPT into a REJECT runs through a *compound right
// operand* of a join, whose errors `Fin::Join` still truncates. Phase (d)
// removes that truncation, and only then do the six jar-REJECT cells below
// flip. Until it does, they are load-bearing ACCEPTs: a premature flip here
// means the tightening escaped its phase.
//
// Cells are `scratchpad/probe/mt102/{v,w,x}/`, each with a jar verdict from
// mt-102's `ParseOnly` harness (2026-08-22).

/// The four-`next` ambiguity fixture the whole thread is built on: three
/// `util/ordering` opens plus the auto-opened `util/integer`, so a bare `next`
/// has four candidates. `body` goes inside `run { ... }`.
fn ord4(body: &str) -> String {
    format!(
        "module m\n\
         open util/ordering[Time] as T\n\
         open util/ordering[VSS] as V\n\
         open util/ordering[TTD] as D\n\
         sig Time {{}}\n\
         sig VSS {{}}\n\
         sig TTD {{}}\n\
         sig Train {{ MA: VSS one -> Time }}\n\
         run {{ {body} }} for 3\n"
    )
}

/// The jar-OK half of the cell matrix — every one reaches the closure arm and
/// every one must stay accepted, in this phase and in all later ones. x05 and
/// v01 are called out by ADR-0023 as the live negative space: x05's inner left
/// operand types `Time` (against x02's `univ`), which is the single type
/// difference that decides accept-vs-reject, and v01 is the `ertms_1A[5]`
/// shape phase (c) has to lower.
#[test]
fn closure_operand_jar_ok_cells_still_accept_mt105b() {
    // v01/x01/w01 — the ertms shape; x03 parenthesized; v09 parenthesized left.
    accept(&ord4(
        "some tr1: Train, t6: Time | tr1.MA.(t6.*next) = V/last",
    ));
    accept(&ord4(
        "some tr1: Train, t6: Time | (tr1.MA).(t6.*next) = V/last",
    ));
    accept(&ord4(
        "some tr1: Train, t6: Time | tr1.MA.((t6).*next) = V/last",
    ));
    // x05 — compound (join) left operand, types `Time`. ADR-0023 negative space.
    accept(&ord4(
        "some tr: Train, t: Time, v: VSS | tr.MA.((v.(tr.MA)).*next) = V/last",
    ));
    // v02/v03 — the same shape reached through `let`.
    accept(&ord4(
        "some tr1: Train | let t6 = T/first | tr1.MA.(t6.*next) = V/last",
    ));
    accept(&ord4(
        "some tr1: Train | let t0 = T/first, t6 = t0.next | tr1.MA.(t6.*next) = V/last",
    ));
    // v04/v05 — the unambiguous controls: no closure, and qualified.
    accept(&ord4(
        "some tr1: Train, t6: Time | tr1.MA.(t6.next) = V/last",
    ));
    accept(&ord4(
        "some tr1: Train, t6: Time | tr1.MA.(t6.*T/next) = V/last",
    ));
    // w04/w05/w06 — `^`, `~`, and a union operand under the same slice.
    accept(&ord4("some tr: Train, t: Time | tr.MA.(t.^next) = V/last"));
    accept(&ord4("some tr: Train, t: Time | tr.MA.(t.~next) = V/last"));
    accept(&ord4(
        "some tr: Train, t: Time | tr.MA.(t.(next+next)) = V/last",
    ));
    // w10 — `=` intersects both sides, so the slice is `Time->Time`. Contrast
    // w11 below, which is the same join under `in` and rejects jar-side.
    accept(&ord4("some t: Time, t2: Time | (t.*next) = t2"));
    // v07/x04 — the closure under an outer `some` / `in`, both jar-OK.
    accept(&ord4("some tr1: Train, t6: Time | some tr1.MA.(t6.*next)"));
    accept(&ord4("some tr: Train, t: Time | tr.MA.(t.*next) in VSS"));
}

/// The 28,402-cliff guard. ADR-0009's failed tightening filtered `*next`
/// against the compound's *own* bottom-up type (`univ->univ`, which excludes
/// nothing) and rejected essentially every `util/ordering` model. Nothing in
/// this phase may put those back: an ordering model whose `next` is ambiguous
/// only with the auto-opened `util/integer` — the overwhelmingly common shape —
/// stays accepted under `*`, `^` and `~` alike.
#[test]
fn ordering_closure_cliff_shape_still_accepts_mt105b() {
    accept("open util/ordering[S]\nsig S {}\nrun { all s: S | s in first.*next } for 3\n");
    accept("open util/ordering[S]\nsig S { f: S }\nrun { all s: S | s.f in s.*next } for 3\n");
    accept("open util/ordering[S]\nsig S { f: S }\nrun { all s: S | s.f in s.^next } for 3\n");
    accept("open util/ordering[S]\nsig S { f: S }\nrun { all s: S | s.f in s.~next } for 3\n");
    accept("open util/ordering[S]\nsig S {}\nfact { S = first.*next }\nrun {} for 3\n");
}

/// The six jar-REJECT cells, now **rejecting** — the whole point of phase (d).
/// Each one's reject route is an error raised inside a compound right operand,
/// which `Fin::Join` truncated until this phase; un-truncating lets it reach the
/// verdict, so mettle agrees with the jar on all six. The jar's message on every
/// one is "This name is ambiguous due to multiple matches:" over the *post*-
/// filter candidate list — `AmbiguousName` here, with `next` named and the
/// survivors listed (mt-102 `{v,w,x}/`, jar verdicts 2026-08-22).
///
/// Their causes stay distinct: x02/w03 the inner left types `univ` because `*`
/// yields `univ->univ`; v06/v08/w09 `some` pushes the operand's own type; w02
/// the left matches no ordering; w11 `in` keeps the left's own type; w07/w08 two
/// orderings linked by `resolveClosure` reachability across `sig B extends A`.
#[test]
fn compound_operand_rejects_reach_the_verdict_mt105d() {
    let mut cells = vec![
        // x02, w03.
        ord4("some tr: Train, t: Time | tr.MA.((t.*T/next).*next) = V/last"),
        // v06, v08, w09.
        ord4("some t6: Time | some (t6.*next)"),
        // w02.
        ord4("some tr: Train, x: Train | some (x.*next)"),
        // w11.
        ord4("some t: Time | (t.*next) in Time"),
    ];
    // w07/w08 — orderings over both `A` and `B extends A`.
    for (v, s) in [("b", "B"), ("a", "A")] {
        cells.push(format!(
            "module m\n\
             open util/ordering[A] as OA\n\
             open util/ordering[B] as OB\n\
             sig A {{}}\n\
             sig B extends A {{}}\n\
             sig Holder {{ f: A one -> A }}\n\
             run {{ some h: Holder, {v}: {s} | h.f.({v}.*next) = h.f.({v}.*next) }} for 3\n"
        ));
    }
    for src in &cells {
        let e = reject(src);
        let ResolveError::AmbiguousName {
            name, candidates, ..
        } = &e
        else {
            panic!("expected AmbiguousName, got {e:?}\n--- src ---\n{src}");
        };
        assert_eq!(name, "next", "{e:?}");
        // The list is the survivors, not every `next` in scope: the four-opens
        // cells keep all four, the two-orderings cells keep exactly the two the
        // closure's reachability leaves (`integer/next` is dropped) — which is
        // the list the jar prints for w07/w08.
        assert!(candidates.len() >= 2, "{e:?}");
    }
}

/// The other end of `resolveHelper`'s ladder, and phase (d)'s new variant: no
/// candidate intersects the relevant type and none shares its arity. The jar
/// prints its own message here ("This name cannot be resolved; its relevant type
/// does not intersect with any of the following candidates:") over **every**
/// candidate — there being no survivor subset — and mettle mislabeled it as an
/// ambiguity until this phase.
#[test]
fn no_candidate_matches_the_relevant_type_mt105d() {
    // The leaf twin (`pick_name`): `f` is binary on two sigs, and `&`'s slice
    // hands it the unary right operand's arity — which neither candidate has, so
    // neither the intersect rung nor the common-arity rung keeps anything. The
    // jar rejects this too, on `&`'s own arity rule (alloy4fun 032006's shape).
    let e = reject(
        "sig N {}\n\
         sig P { f: set N }\n\
         sig Q { f: set N }\n\
         run { one (f & N) } for 3\n",
    );
    let ResolveError::NameNotRelevant {
        name, candidates, ..
    } = &e
    else {
        panic!("expected NameNotRelevant, got {e:?}");
    };
    assert_eq!(name, "f", "{e:?}");
    assert_eq!(candidates.len(), 2, "{e:?}");
    assert!(
        candidates.iter().all(|c| c.starts_with("field ")),
        "the full candidate list, not a survivor subset: {candidates:?}"
    );

    // The spine twin (`pick_reading`): the same label on both sides of a join,
    // under `#`. Before this phase the arm finalized the first reading instead
    // of reporting, so the model was accepted (alloy4fun 046692's shape).
    let e = reject(
        "sig Project {}\n\
         sig Person { projects: set Project }\n\
         sig Course { projects: set Project }\n\
         run { all pro: Project | #Course.projects.iden.pro = 1 } for 3\n",
    );
    assert!(
        matches!(e, ResolveError::NameNotRelevant { .. }),
        "expected NameNotRelevant, got {e:?}"
    );
}

// ---- ADR-0023 phase (c): the chosen base is finalized, never re-resolved ----
//
// `Fin::Join` now carries the right operand's **winning candidate** and
// finalizes it in place against the join's right slice, so the operand's
// resolution — and its recording — happen on the verdict path. What it must
// never do is re-resolve the operand by `ExprId`: that re-runs candidate
// selection at a name the enclosing join had already disambiguated.

/// The invariant phase (a) paid for. This model declares the same field label
/// on three sigs, so `dist` alone is ambiguous; only the join that supplies the
/// receiver picks one. A prototype that re-resolved the operand by `ExprId`
/// rejected `corpus/portus-63/.../lc-lenses.als` here, which the jar accepts —
/// a drop-in violation. Both spellings of the fold reach the same base.
#[test]
fn same_label_on_three_sigs_resolves_through_the_chosen_base_mt105c() {
    let m = "module m\n\
             sig N {}\n\
             sig S { dist: S -> one N }\n\
             sig U { dist: U -> one N }\n\
             sig V { dist: V -> one N }\n";
    // The box-join fold: the second argument's base is the bare name `dist`.
    accept(&format!(
        "{m}run {{ all s, s2: S | dist[s, s2] = dist[s2, s] }} for 3\n"
    ));
    // The same spine written as an explicit join.
    accept(&format!(
        "{m}run {{ all s, s2: S | s2.(s.dist) = s.(s2.dist) }} for 3\n"
    ));
    // A mixed spine, and the other two owners, so no single sig is load-bearing.
    accept(&format!(
        "{m}run {{ all u, u2: U | u2.dist[u] = u.dist[u2] }} for 3\n"
    ));
    accept(&format!("{m}run {{ all v: V | some v.dist[v] }} for 3\n"));
}

// ---- mt-112: join legality — arity collapse vs empty-but-legal (probe record) ----
//
// mt-112 pinned the reference's `IllegalJoin` rule against the jar: it fires
// on a make-time arity collapse (result arity < 1) alone, independent of
// whether either operand's type contains `univ`. These are the agreeing
// cells from that probe wave — both mettle and the jar reach the same
// verdict today, on the unmodified resolver. The accept-lean
// `contains_univ` suppression that still overrides the rule for genuine
// `univ` operands is exercised separately (mt-113).

#[test]
fn closure_star_join_accepted_mt112() {
    // `A.*r`: `*r` is `univ->univ ∪ closure(r)`, but the left join keeps
    // arity 1 (`A.(univ->univ)` = `univ`, still unary) so the whole
    // expression never collapses. Jar: ACCEPT.
    accept("sig A { r: A }\nrun { some A.*r }\n");
}

#[test]
fn univ_binary_joins_accepted_mt112() {
    // A join between `univ` and a genuine binary field never collapses
    // arity (1 + 2 - 2 = 1), regardless of join order. Jar: ACCEPT (both).
    accept("sig A { r: A }\nrun { some univ.r }\n");
    accept("sig A { r: A }\nrun { some r.univ }\n");
}

#[test]
fn ambiguous_field_merged_join_accepted_mt112() {
    // `f` is ambiguous (A's own `f: A->A` and B's own `f: B->B`), but the
    // merged make-time type still has a non-empty candidate: `B.f: B->B`
    // joined with `B` survives even though `A.f: A->A` joined with `B` is
    // empty. The make-time union check only rejects when NO candidate
    // combination yields a legal, non-empty join. Jar: ACCEPT.
    accept("sig A { f: A }\nsig B { f: B }\nrun { some f.B }\n");
}

#[test]
fn column_disjoint_legal_arity_join_accepted_with_warning_mt112() {
    // `f.B`: arity 2 . arity 1 = arity 1 — a LEGAL resultant arity — even
    // though `A`'s own `f: A->A` shares no column type with `B`. This is
    // not an illegal join (the arity is fine); it is a statically-empty
    // *legal* relation, which is the A9 "join always empty" warning's
    // territory, not `IllegalJoin`'s. (mt-112 Block B's one miss: the
    // original prediction for this cell assumed column-disjointness alone
    // rejects, which conflates the two mechanisms — corrected here.)
    // Jar: ACCEPT.
    let src = "sig A { f: A }\nsig B {}\nrun { some f.B }\n";
    accept(src);
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let resolved = resolve(&graph).expect("expected ACCEPT");
    assert!(
        resolved
            .warnings
            .iter()
            .any(|w| matches!(w, ResolveWarning::JoinEmpty { .. })),
        "expected a join-empty warning, got {:?}",
        resolved.warnings
    );
}

#[test]
fn closure_over_comprehension_arity_one_accepted_mt112() {
    // A closure over a comprehension (`*{a,b: S | ...}`) that reduces to a
    // binary relation joins cleanly with a unary operand — no arity
    // collapse, regardless of the closure's internal complexity. Jar:
    // ACCEPT.
    accept(
        "sig S {}\nsig E {}\nsig T { tr: S->E->S }\n\
         run { some s: S | some s.(*{a,b: S | some e: E | a->e->b in T.tr}) }\n",
    );
}

#[test]
fn meta_model_join_stays_lenient_mt112() {
    // `A$r.univ`: a genuine meta name (`A$r`) joined with `univ`. mettle's
    // `lenient()` guard keeps a meta model accepting regardless of arity,
    // matching the meta-model leniency already pinned by mt-108.
    accept("sig A { r: A }\nrun { some A$r.univ }\n");
}

#[test]
fn arity_collapse_no_univ_rejected_mt112() {
    // `(A.^r).A`: `^r` keeps `A->A` (no `univ` involved, unlike `*r`), so
    // `A.^r` is unary `A`, and joining that with `A` again collapses to
    // arity 0. Jar: REJECT ("this cannot be a legal relational join").
    let e = reject("sig A { r: A }\nrun { some (A.^r).A }\n");
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

#[test]
fn narrowed_two_sig_join_rejected_mt112() {
    // `A.f.B` and `(B.f).A`: with two sigs each owning their own `f`, the
    // left operand narrows the ambiguous `f` to its own candidate before
    // the outer join is even considered — `A.f`/`B.f` never survives
    // against the other sig's relevant type. mettle rejects earlier, on
    // its candidate-disambiguation ladder (`NameNotRelevant`: no candidate
    // for `f` intersects the relevant type here), not on the join-arity
    // check `IllegalJoin` fires for elsewhere in this suite. The jar's own
    // rejection message for both is its "legal relational join" text (it
    // resolves the merged make-time type and finds every combination
    // empty) — same REJECT verdict, different internal mechanism; mt-112
    // Block B notes these as non-separating consistency cells. Jar: REJECT.
    let e = reject("sig A { f: A }\nsig B { f: B }\nrun { some A.f.B }\n");
    assert!(matches!(e, ResolveError::NameNotRelevant { .. }), "{e:?}");

    let e = reject("sig A { f: A }\nsig B { f: B }\nrun { some (B.f).A }\n");
    assert!(matches!(e, ResolveError::NameNotRelevant { .. }), "{e:?}");
}

#[test]
fn unrelated_unary_sigs_arity_collapse_rejected_mt112() {
    // The column-disjoint-warning-cell follow-up control: two unrelated
    // unary sigs joined directly (`A.B`) collapse to arity 0 regardless of
    // type overlap — the same mechanism as
    // `arity_collapse_no_univ_rejected_mt112`, with no field indirection
    // at all. Confirms `IllegalJoin` is an arity rule, not a
    // type-disjointness rule (the column-disjoint-but-legal-arity case
    // above only warns). Jar: REJECT.
    let e = reject("sig A {}\nsig B {}\nrun { some A.B }\n");
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

// ---- mt-113: the fix — `univ`-typed operands are no longer a suppression ----
//
// The two `contains_univ` conjuncts removed from the `IllegalJoin` condition
// (mt-112's H3 prototype, confirmed against the 150,891-code alloy4fun diff:
// 0 drop-in violations, over-accepts 27 → 18). These are the 9 real
// over-accepts that fix closes — every one now REJECTs, matching the jar.

#[test]
fn univ_dot_univ_rejected_mt113() {
    // `univ.univ`: both operands are the genuine `univ` unary type — arity
    // 1.1 = 0. Jar: REJECT.
    let e = reject("sig A {}\nrun { some univ.univ }\n");
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

#[test]
fn closure_star_join_then_unary_rejected_mt113() {
    // `(A.*r).A`: `A.*r` is unary (`univ`, via `*r`'s `univ->univ` leg), so
    // the outer join with `A` collapses to arity 0 — the 076666 shape.
    // Jar: REJECT.
    let e = reject("sig A { r: A }\nrun { some (A.*r).A }\n");
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

#[test]
fn quantified_univ_var_joined_with_sig_rejected_mt113() {
    // `A.x` with `x: univ`: `A` and `x` are both unary — the 096458 shape.
    // Jar: REJECT.
    let e = reject("sig A { r: A }\nrun { all x: univ | some A.x }\n");
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

#[test]
fn quantified_univ_var_self_joined_rejected_mt113() {
    // `p.p` with `p: univ`: both operands are the same unary quantified
    // variable. Jar: REJECT.
    let e = reject("sig A {}\nrun { all p: univ | some p.p }\n");
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

#[test]
fn real_code_076666_minimized_rejected_mt113() {
    // `Track.*succs.Entry`: `Track.*succs` is unary `univ` (via `*succs`'s
    // `univ->univ` leg), then `.Entry` collapses arity to 0.
    let e = reject(
        "sig Track { succs: set Track }\nsig Entry in Track {}\n\
         pred p { no Track.*succs.Entry }\n",
    );
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

#[test]
fn real_code_083413_minimized_rejected_mt113() {
    // `e.*succs.t` under a quantifier: same `*`-closure arity collapse as
    // 076666, with both flanks quantified variables.
    let e = reject(
        "sig Track { succs: set Track }\nsig Exit in Track {}\n\
         pred p { all t: Track, e: Exit | no e.*succs.t }\n",
    );
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

#[test]
fn real_code_003167_minimized_rejected_mt113() {
    // `i.(*{s1,s2: State | ...}).s`: closure over a comprehension, same
    // mechanism — the comprehension's closure carries `univ->univ`.
    let e = reject(
        "sig State { trans: Event -> State }\nsig Init in State {}\nsig Event {}\n\
         pred p { all i: Init, s: State | some i.(*{s1, s2: State | s1->Event->s2 in trans}).s }\n",
    );
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

#[test]
fn real_code_096458_minimized_rejected_mt113() {
    // `lone (Ad.p)` with `p: univ`: `Ad` and `p` are both unary.
    let e =
        reject("sig Photo {}\nsig Ad extends Photo {}\npred pr { all x: univ | lone (Ad.x) }\n");
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

#[test]
fn real_code_096462_minimized_rejected_mt113() {
    // `u.posts.p` with `p, u: univ`: `u.posts` is unary, `.p` collapses it.
    let e = reject(
        "sig User { posts: set Photo }\nsig Photo {}\n\
         pred pr { all p, u: univ | lone (u.posts.p) }\n",
    );
    assert!(matches!(e, ResolveError::IllegalJoin { .. }), "{e:?}");
}

// ---- overloaded-name empty-middle joins: rule-4 negative space (mt-114) ----
//
// `ExprChoice.resolveHelper`'s rule 4 (the trial-resolve-and-retry firstPass
// step, `scratchpad/probe/mt114/MECHANISM.md`) governs a genuine overloaded
// *dot join* whose right-name candidates tie on the first pass. These cells
// pin the boundary the rule-4 fix must preserve: shapes with no live tie at
// all (single candidate, left-only overload, right-only-overload-but-every-
// trial-succeeds) already agree with the jar today, with no choice-node rule
// 4 in play. Every cell is jar-verified (Alloy 6.2.0,
// `scratchpad/probe/mt114/NOTES.md`).

#[test]
fn right_only_overload_single_candidate_accepted_mt114() {
    // n01: `f.f` — `f` names only `A`'s own field, so `ExprChoice.make`'s
    // size==1 shortcut returns the expr directly: no choice node, no rule 4.
    // The self-join's middle (`P` against `A`) is disjoint, so the join
    // still legally types (arity 2, NONE-filled) and warns "always empty".
    // Jar: ACCEPT + the join-empty warning.
    let src = "sig P {}\nsig A { f: set P }\nrun { one f.f }\n";
    accept(src);
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let resolved = resolve(&graph).expect("expected ACCEPT");
    assert!(
        resolved
            .warnings
            .iter()
            .any(|w| matches!(w, ResolveWarning::JoinEmpty { .. })),
        "expected a join-empty warning, got {:?}",
        resolved.warnings
    );
}

#[test]
fn right_only_overload_every_trial_succeeds_accepted_mt114() {
    // n04: `g.f` — `g` is single (only `C` declares it), `f` is overloaded
    // (`A`, `B`). Both `g.f` combinations are middle-dead (`P` vs `A`/`B`,
    // both disjoint), but unlike the projects.projects family the LEFT
    // operand `g` is never itself ambiguous, so every rule-4 trial resolves
    // cleanly. The retry sees both candidates still `NONE²` — legal-match,
    // tie — rule 6 collapses them to `none²`. This is the load-bearing
    // boundary: the fix must not turn this all-dead-middle join into a
    // reject. Jar: ACCEPT, no warning at all.
    accept(
        "sig P {}\nsig C { g: set P }\nsig A { f: set P }\nsig B { f: set P }\nrun { one g.f }\n",
    );
}

#[test]
fn one_live_combination_narrows_choice_accepted_mt114() {
    // n05: `f.f` — `A`'s `f: P` and `B`'s `f: A`. Only the combination
    // `A.f (: P) . B.f (: A)`-style pairing that actually shares a column
    // survives block-1 slicing before rule 4 ever gets a tie of >1 dead
    // survivors; the live candidate narrows the choice outright. Jar:
    // ACCEPT.
    accept("sig P {}\nsig A { f: set P }\nsig B { f: set A }\nrun { some f.f }\n");
}

#[test]
fn left_only_overload_bare_name_ambiguous_rejected_mt114() {
    // n03: `f.g` — `f` is overloaded (`A`, `B`), `g` is single. The bare
    // left name `f` is ambiguous with or without the join (the join partner
    // `g` plays no role at all — see n03x below): mettle already rejects
    // this byte-identically to the jar via `pick_name`'s leaf-candidate
    // path, whose first-pass retry genuinely is a fixpoint (unlike
    // `pick_reading`'s compound readings). Jar: REJECT, "ambiguous due to
    // multiple matches" at the left `f`.
    let e = reject(
        "sig P {}\nsig A { f: set P }\nsig B { f: set P }\nsig C { g: set P }\nrun { one f.g }\n",
    );
    assert!(matches!(e, ResolveError::AmbiguousName { .. }), "{e:?}");
}

#[test]
fn left_only_overload_join_plays_no_role_rejected_mt114() {
    // n03x: same sigs as n03, but `run { one f }` drops the join entirely.
    // The jar throws the identical ambiguous-name error at the identical
    // column, proving n03's rejection is not about the join `f.g` at all —
    // a bare overloaded name already rejects with zero join context. Jar:
    // REJECT, identical message/span to n03.
    let e = reject(
        "sig P {}\nsig A { f: set P }\nsig B { f: set P }\nsig C { g: set P }\nrun { one f }\n",
    );
    assert!(matches!(e, ResolveError::AmbiguousName { .. }), "{e:?}");
}

#[test]
fn appended_fact_bare_overload_ambiguous_rejected_mt114() {
    // n08: a bare overloaded `f` (declared on `B` and `C`) inside `A`'s own
    // appended fact — no join at all, so rule 4 is out of scope here too;
    // this is `pick_name`'s existing ambiguous-leaf path. Jar: REJECT,
    // "ambiguous due to multiple matches" listing `B <: f` then `C <: f`.
    let e = reject("sig P {}\nsig B { f: set P }\nsig C { f: set P }\nsig A {} { some f }\n");
    assert!(matches!(e, ResolveError::AmbiguousName { .. }), "{e:?}");
}

// ---- overloaded-name empty-middle joins: the rule-4 fix itself (mt-115) ----
//
// The six cells above pin the negative space (shapes with no live rule-4 tie
// at all). These four flip mettle's own verdict/class on the genuine ties —
// a both-flanks-overloaded self-join whose every candidate combination is
// middle-dead, so every rule-4 trial resolution fails and the retry lands in
// `resolveHelper`'s rule-7 second form (`NameNotRelevant`, resolution-doc
// §4.4). Before the fix mettle either over-accepted (n02/n06, via the
// pre-fix `pick_reading` first-reading finalize) or mislabeled the reject as
// `AmbiguousName` (n09, via the whole-join `Ambiguous` collapse instead of
// the jar's per-name rule-7 form). Cells are jar-verified (Alloy 6.2.0,
// `scratchpad/probe/mt114/NOTES.md`); sources reused verbatim from
// `scratchpad/probe/mt114/cells/`.

#[test]
fn right_only_overload_dead_middle_ambiguous_join_rejected_mt115() {
    // n02: `f.f` — both `A` and `B` declare `f`, so every candidate pairing
    // of the self-join is middle-dead (`P` against `A`/`B`, both disjoint).
    // Rule 4 trial-resolves each pooled reading; both trials fail (the
    // block-3 arity-only join fallback hands the left choice the full field
    // merge, which is itself ambiguous inside the trial), so the retry pool
    // is empty. Jar: REJECT, rule-7 second form, a 1-char point span on the
    // right `f` (`@1:51-51`) — not the whole `f.f` join.
    let src = "sig P{} sig A{f: set P} sig B{f: set P} run{one f.f}\n";
    let e = reject(src);
    let ResolveError::NameNotRelevant {
        name,
        span,
        candidates,
    } = &e
    else {
        panic!("expected NameNotRelevant, got {e:?}");
    };
    assert_eq!(name, "field A <: f", "{e:?}");
    assert_eq!(candidates, &["field A <: f", "field B <: f"], "{e:?}");
    let head = u32::try_from(src.rfind('f').expect("source has an `f`")).unwrap();
    assert_eq!(
        (span.start, span.end),
        (head, head + 1),
        "{e:?}\n--- src ---\n{src}"
    );
}

#[test]
fn chained_overload_dead_middle_ambiguous_join_rejected_mt115() {
    // n06: `p.c.p` — `C` and `R` both declare `p`, `c` names only `C`. The
    // nested join's readings all carry the same spine-head (`p.head_expr`
    // propagates through `process_readings`/`join_cand`), so the rule-4
    // retry and its reject land at the rightmost `p`, exactly as for the
    // single-dot n02 shape. Jar: REJECT, rule-7 second form, `@1:71-71`.
    let e = reject("sig Pos{} sig C{p: one Pos} sig R{p: one Pos} run{all c: C | some p.c.p}\n");
    let ResolveError::NameNotRelevant {
        name, candidates, ..
    } = &e
    else {
        panic!("expected NameNotRelevant, got {e:?}");
    };
    assert_eq!(name, "field C <: p", "{e:?}");
    assert_eq!(candidates, &["field C <: p", "field R <: p"], "{e:?}");
}

#[test]
fn mixed_arity_overload_dead_middle_class_realigned_mt115() {
    // n09: `f.f` with `A.f: P` (arity 1) and `B.f: Q->Q` (arity 2) — a
    // mixed-arity overload where every trial still fails. Before the fix
    // mettle collapsed the whole join to `Ambiguous` (the two candidates'
    // types never reached rule 4 as leafs to notice they don't even share
    // an arity); the fix's rule-4 retry pool empties out exactly as n02's
    // does, so the class realigns from `AmbiguousName` to the jar's own
    // `NameNotRelevant`. Jar: REJECT, rule-7 second form, `@1:58-58`.
    let e = reject("sig P{} sig Q{} sig A{f: set P} sig B{f: Q->Q} run{one f.f}\n");
    assert!(matches!(e, ResolveError::NameNotRelevant { .. }), "{e:?}");
}

#[test]
fn equality_context_dead_middle_ambiguous_join_rejected_mt115() {
    // A `=`-context variant of the family (real code 068037's
    // `one projects.projects` shape, ported to `=` to cover a relevant-type
    // derivation other than `one`/`some`): both `A` and `B` declare `f`, and
    // `=` pushes each side's own type down (`compare`'s `CmpOp::Eq` arm), so
    // the left `f.f` still ties its two middle-dead readings under rule 4.
    // Jar mechanism confirmed via the real code (NAME_NOT_RELEVANT, "This
    // name cannot be resolved…", candidate list in declaration order).
    let src = "sig P {}\nsig A { f: set P }\nsig B { f: set P }\nrun { f.f = f.f }\n";
    let e = reject(src);
    let ResolveError::NameNotRelevant {
        name,
        span,
        candidates,
    } = &e
    else {
        panic!("expected NameNotRelevant, got {e:?}");
    };
    assert_eq!(name, "field A <: f", "{e:?}");
    assert_eq!(candidates, &["field A <: f", "field B <: f"], "{e:?}");
    // The left `f.f`'s own spine-head, not the whole `f.f = f.f` comparison.
    let head = u32::try_from(src.find("f.f").expect("source has `f.f`") + 2).unwrap();
    assert_eq!(
        (span.start, span.end),
        (head, head + 1),
        "{e:?}\n--- src ---\n{src}"
    );
}

// ---- mt-116/mt-117: the negative space of five positional rules ----
//
// The mt-116 probe wave (32 cells, `scratchpad/probe/mt116/NOTES.md`, jar =
// Alloy 6.2.0) pinned five rules the reference enforces and mettle did not:
// `open` placement, `abstract` on a subset sig, what a field bound may name,
// where a binder body ends, and multiplicity on a negated `in`'s right
// operand. The cells below are the half where the two tools already agree —
// the guards that say each new check fires only where the jar's does. Sources
// are the cell files verbatim; the `open`/`abstract` half of the negative
// space is pinned at the parse level, in `als-syntax`.

/// Cell f03: a field bound may name an **earlier** field of its own sig — the
/// one field reference a bound is allowed, and the reason the fix cannot be a
/// blanket "no fields in bounds".
#[test]
fn earlier_own_field_in_a_bound_accepted_mt116() {
    accept("sig P {}\nsig R { a: set P, b: one a }\n"); // f03
}

/// Cells f04/f05: a bound naming its own field, or a **later** field of the
/// same sig, is unresolvable — mettle already agrees with the jar here (same
/// message, same one-char span), because a field is not registered until its
/// own bound has been typed.
#[test]
fn self_and_later_own_field_in_a_bound_rejected_mt116() {
    for src in [
        "sig P {}\nsig R { a: set a }\n",           // f04
        "sig P {}\nsig R { b: one a, a: set P }\n", // f05
    ] {
        let e = reject(src);
        let ResolveError::UnknownName { name, span } = &e else {
            panic!("expected UnknownName, got {e:?}\n--- src ---\n{src}");
        };
        assert_eq!(name, "a", "{e:?}");
        // The bare name itself, not the bound or the decl.
        assert_eq!(span.end - span.start, 1, "{e:?}\n--- src ---\n{src}");
    }
}

/// Cell f06: `sig R { position: one position }` where another sig also has a
/// `position` — a reject either way, pinned here at verdict level only (the
/// mechanism realigns with the fix; see the class assertion in the mt-116 fix
/// section).
#[test]
fn bare_self_reference_in_a_bound_rejected_mt116() {
    reject("sig P {}\nsig C { position: one P }\nsig R { position: one position }\n");
    // f06
}

/// Cells g01/g03/x03: a `;` whose tail formula closes over nothing bound by the
/// binder is legal whichever side of the binder it lands on, and the brace-body
/// form (`all u: A { … }`) never involved a `;` at all.
#[test]
fn sequenced_tail_without_a_freed_name_accepted_mt116() {
    accept("sig A {}\npred P { all u: A | some u; some A }\nrun P\n"); // g01
    accept("sig A {}\npred P { all u: A { some u u in A } }\nrun P\n"); // g03
    accept("sig A {}\npred P { let y = A | some y; some A }\nrun P\n"); // x03
}

/// Cell g06: `;` with no binder in scope is the plain top-level sequencing
/// both tools already agreed on — the control for the binder-body change.
#[test]
fn top_level_sequencing_accepted_mt116() {
    accept("sig A {}\npred P { some A; no A }\nrun P for exactly 1 A\n"); // g06
}

/// Cells h02/h03 (mt-117): the multiplicity stays legal on a **plain** `in`'s
/// right operand, and h03 is the boundary that says the trigger is the negated
/// membership *operator*, not a negated membership formula — `!(x in (some
/// y))` parses as `!` applied to an ordinary `in`, and is accepted.
#[test]
fn mult_on_plain_in_rhs_and_under_outer_negation_accepted_mt117() {
    accept("sig Project {}\nsig Course { projects: set Project }\nfact { Project in (some Course.projects) }\n"); // h02
    accept("sig Project {}\nsig Course { projects: set Project }\nfact { !(Project in (some Course.projects)) }\n");
    // h03
}

/// Cell h06 (mt-117): a mult keyword on the **left** of `not in` is not a
/// multiplicity at all — `mult()` converts only the right operand, so the
/// leftover set test fails the sort check. Jar and mettle already agree on
/// class and span alike (`[ErrorType]` over `(some Course.projects)`), which
/// is why the LHS needs no new handling.
#[test]
fn mult_on_not_in_lhs_stays_a_sort_reject_mt117() {
    let src = "sig Project {}\nsig Course { projects: set Project }\nfact { (some Course.projects) not in Project }\n";
    let e = reject(src);
    let ResolveError::NotSet { span, .. } = &e else {
        panic!("expected NotSet, got {e:?}");
    };
    let open = u32::try_from(src.find("(some").expect("source has `(some`")).unwrap();
    assert_eq!(
        (span.start, span.end),
        (
            open + 1,
            open + 1 + u32::try_from("some Course.projects".len()).unwrap()
        ),
        "{e:?}\n--- src ---\n{src}"
    );
}

// ---- mt-116/mt-117: the four resolve-level closes ----
//
// The flips. Three of the wave's five rules land here (the `open`-placement
// and `abstract`-subset rules are parse-level and live in `als-syntax`): what a
// field bound may name, the name a `;`-terminated binder body frees, and the
// multiplicity a negated `in` refuses. Every expected class/span below is the
// jar's, recorded verbatim in `scratchpad/probe/mt116/NOTES.md`.

/// Cells f01/f02: a field bound cannot name **another sig's** field, and the
/// probe's own key result is that this has nothing to do with name collisions —
/// f01's `position` shadows the bound's own label, f02's `pos2` collides with
/// nothing, and the jar rejects both identically at the joined name. The bound
/// of sig `S`'s field sees sigs, `S`'s earlier fields, and `S`'s inherited
/// fields; nothing else.
#[test]
fn cross_sig_field_in_a_bound_rejected_mt116() {
    for (src, label) in [
        (
            "sig P {}\nsig C { position: one P }\nsig R { position: one C.position }\n",
            "position",
        ), // f01
        (
            "sig P {}\nsig C { position: one P }\nsig R { pos2: one C.position }\n",
            "position",
        ), // f02
    ] {
        let e = reject(src);
        let ResolveError::UnknownName { name, span } = &e else {
            panic!("expected UnknownName, got {e:?}\n--- src ---\n{src}");
        };
        assert_eq!(name, label, "{e:?}");
        // The joined name itself (`C.position`'s right half), not the bound.
        let at = u32::try_from(src.rfind("C.position").expect("source has `C.position`") + 2)
            .expect("offset fits");
        assert_eq!(
            (span.start, span.end),
            (at, at + u32::try_from(label.len()).expect("label fits")),
            "{e:?}\n--- src ---\n{src}"
        );
    }
}

/// Cell f06: an inherited field is still visible, so the rule cannot be "no
/// fields at all" — `sig B extends A { g: set f }` reads `A`'s `f`. Three
/// corpus models (`ins.als`, `etl_scd.als`, `INSLabel.als`) depend on exactly
/// this, which is why the check keys on the declared sig's *inheritance chain*
/// rather than on identity.
#[test]
fn inherited_field_in_a_bound_accepted_mt116() {
    accept("sig P {}\nsig A { f: set P }\nsig B extends A { g: set f }\n");
}

/// Cell f06 again, now for its **mechanism**: `sig R { position: one position }`
/// used to reject for an unrelated reason — mettle resolved the bare name to
/// the half-built field itself and then failed a sort check on `one position`
/// at the mult keyword. With the bound's name pool restricted, it rejects where
/// the jar does, on the name, as an unfindable one.
#[test]
fn bare_self_reference_reject_realigned_mt116() {
    let src = "sig P {}\nsig C { position: one P }\nsig R { position: one position }\n";
    let e = reject(src);
    let ResolveError::UnknownName { name, span } = &e else {
        panic!("expected UnknownName, got {e:?}");
    };
    assert_eq!(name, "position", "{e:?}");
    let at = u32::try_from(src.rfind("one position").expect("source has the bound") + 4)
        .expect("offset fits");
    assert_eq!(
        (span.start, span.end),
        (
            at,
            at + u32::try_from("position".len()).expect("label fits")
        ),
        "{e:?}\n--- src ---\n{src}"
    );
}

/// Cells g02/g04/x02: with the binder body ending at the `;`, the tail formula
/// sits *outside* the binder, so a binder variable used there is free — the
/// reference's unfindable-name reject, and mettle's now too. Probed across a
/// `pred` body, a `fact` body, and a `let` (all three carriers of the `|`).
#[test]
fn binder_variable_after_a_seq_is_free_mt116() {
    for (src, var) in [
        (
            "sig A {}\npred P { all u: A | some u; u in A }\nrun P\n",
            "u",
        ), // g02
        ("sig A {}\nfact { all u: A | some u; u in A }\n", "u"), // g04
        (
            "sig A {}\npred P { let y = A | some y; y in A }\nrun P\n",
            "y",
        ), // x02
    ] {
        let e = reject(src);
        let ResolveError::UnknownName { name, .. } = &e else {
            panic!("expected UnknownName, got {e:?}\n--- src ---\n{src}");
        };
        assert_eq!(name, var, "{e:?}\n--- src ---\n{src}");
    }
}

/// Cells h01/h04/h05 (mt-117): the right operand of `not in`/`!in` consumes no
/// multiplicity — only the plain `in` states one. LEDGER-016's positional rule
/// therefore fires there like at any ordinary operand, over the parenthesized
/// mult expression, uniformly across both spellings of the operator and every
/// mult keyword.
#[test]
fn mult_on_not_in_rhs_rejected_mt117() {
    for (src, mult) in [
        (
            "sig Project {}\nsig Course { projects: set Project }\nfact { Project not in (some Course.projects) }\n",
            "some Course.projects",
        ), // h01
        (
            "sig Project {}\nsig Course { projects: set Project }\nfact { Project !in (some Course.projects) }\n",
            "some Course.projects",
        ), // h04
        (
            "sig Project {}\nsig Course { projects: set Project }\nfact { Project not in (lone Course.projects) }\n",
            "lone Course.projects",
        ), // h05
    ] {
        let e = reject(src);
        let ResolveError::MultiplicityNotAllowed { span } = &e else {
            panic!("expected MultiplicityNotAllowed, got {e:?}\n--- src ---\n{src}");
        };
        // The mult expression inside the parens, not the parens or the formula.
        let at = u32::try_from(src.find(mult).expect("source has the mult")).expect("offset fits");
        assert_eq!(
            (span.start, span.end),
            (at, at + u32::try_from(mult.len()).expect("mult fits")),
            "{e:?}\n--- src ---\n{src}"
        );
    }
}

// ---- CAST2INT's relevant-type push (mt-126, ADR-0025 item 5) ----
//
// `ExprUnary.resolve`'s `CAST2INT` case (`int[e]`/`sum e`, one AST node,
// `ExprUnary.java:419-426`) pushes `sub.type.intersect(SIGINT.type)` into its
// operand — the operand's own bottom-up type intersected with `{Int}` — not a
// flat push of the int sig, and independent of the cast's own syntactic
// context. mettle's `UnOp::IntOf | UnOp::SumOf` arm (`resolve/expr.rs`) and
// the `"int"|"sum"` builtin-call arm previously pushed `remove_bool_and_int`,
// a no-op on an already-non-Int operand type — so a same-named field on a
// disjoint, non-Int-domain sig sailed through instead of ever reaching the
// ambiguous-name ladder. Sources and jar verdicts are `scratchpad/probe/mt126/
// {NOTES,PREDICTIONS}.md`, cells `scratchpad/probe/mt126/cells/`.
//
// Group A pins the negative space the fix must not disturb: the
// single-candidate `ExprChoice.make` shortcut (p03/p04/p11/p12/p14, which
// never reach the push-dependent ladder at all), the sig-body scoped-lookup
// cell (p08, whose bare `f` resolves against A's own fields only — a
// different, already-correct code path this fix doesn't touch), and the
// domain-matched-candidate-is-Int-valued cells (p06/p07, where the push
// stays a genuine nonempty `{Int}` and resolution is unaffected). These all
// ACCEPT on the pre-fix tree too — they are boundary cells, not flips.
//
// Group B is the flip set: shapes that mettle over-accepted before this fix
// (ACCEPT + an `IntAtoms` warning) and now correctly REJECTs, matching the
// jar's "ambiguous due to multiple matches" class exactly (position and
// candidate list, in declaration order).

// -- Group A: boundary cells (ACCEPT on both the pre- and post-fix tree) --

#[test]
fn int_cast_single_int_candidate_accepted_mt126_p03() {
    // p03: exactly one field named `f` anywhere, Int-valued.
    // `ExprChoice.make` shortcuts a single-candidate name straight to the
    // field, before any push-dependent ladder runs. Jar: ACCEPT.
    accept("sig A { f: one Int }\npred inv { some x: A | int x.f = 0 }\nrun inv\n");
}

#[test]
fn int_cast_single_non_int_candidate_accepted_with_warning_mt126_p04() {
    // p04: single-candidate `f`, but not Int-valued. Still the
    // `ExprChoice.make` shortcut, so still ACCEPT — just with the A5
    // `IntAtoms` warning attached, since the push (now `{C} ∩ {Int}` =
    // EMPTY) has no tuple. Jar: ACCEPT (OK commands=1).
    let src = "sig C {}\nsig A { f: one C }\npred inv { some x: A | int x.f = 0 }\nrun inv\n";
    accept(src);
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let resolved = resolve(&graph).expect("expected ACCEPT");
    assert!(
        resolved
            .warnings
            .iter()
            .any(|w| matches!(w, ResolveWarning::IntAtoms { .. })),
        "expected an IntAtoms warning, got {:?}",
        resolved.warnings
    );
}

#[test]
fn int_cast_domain_matched_int_candidate_accepted_mt126_p06() {
    // p06: `f:C` on A, `f:Int` on B, disjoint domains, cast receiver is
    // B (Int-valued). `x.f`'s bottom-up type (x:B) is {Int} alone (A.f's
    // domain doesn't match B), so the push stays a nonempty {Int} and JOIN's
    // tier-1 slice uniquely resolves to B.f. Jar: ACCEPT.
    accept(
        "sig C {}\nsig A { f: one C }\nsig B { f: one Int }\npred inv { some x: B | int x.f = 0 }\nrun inv\n",
    );
}

#[test]
fn int_cast_domain_unique_int_candidates_accepted_mt126_p07() {
    // p07: both same-named fields Int-valued, disjoint domains, domain
    // uniquely selects one (x:A picks A.f, B.f's domain doesn't match). The
    // push stays nonempty {Int} either way — the common "two counters with
    // the same name on sibling sigs" real-world shape a fix must not touch.
    // Jar: ACCEPT.
    accept("sig A { f: one Int }\nsig B { f: one Int }\npred inv { some x: A | int x.f = 0 }\nrun inv\n");
}

#[test]
fn sig_body_scoped_ambiguous_name_shielded_accepted_mt126_p08() {
    // p08 (fixed): inside sig A's own appended fact, the bare unqualified
    // `f` auto-prepends to `this.f` and resolves via sig-scoped lookup (only
    // fields declared on A or an ancestor are candidates) — not the general
    // cross-model ambiguous-name `ExprChoice` ladder this bead's fix
    // touches. A same-named, non-Int `B.f` coexists in the model without
    // triggering the ambiguity this fix introduces elsewhere. Jar: ACCEPT,
    // with the A5 IntAtoms warning (A.f is not Int-valued).
    let src = "sig C {}\nsig A { f: one C } {\n  int f >= 0\n}\nsig B { f: one C }\n";
    accept(src);
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let resolved = resolve(&graph).expect("expected ACCEPT");
    assert!(
        resolved
            .warnings
            .iter()
            .any(|w| matches!(w, ResolveWarning::IntAtoms { .. })),
        "expected an IntAtoms warning, got {:?}",
        resolved.warnings
    );
}

#[test]
fn sig_body_scoped_single_int_candidate_accepted_mt126_p11() {
    // p11 (fixed): single-candidate `this`-scoped sanity pair for p08 —
    // isolates that p08's mechanism is sig-scoping, not `this` as a
    // receiver. Jar: ACCEPT, no warning (f is Int-valued).
    accept("sig A { f: one Int } {\n  int f >= 0\n}\n");
}

#[test]
fn sum_cast_single_int_candidate_accepted_mt126_p12() {
    // p12: `sum`'s single-candidate cliff, symmetric to p03's `int[.]` —
    // both are CAST2INT (§4.5), so the shortcut applies identically. Jar:
    // ACCEPT.
    accept("sig A { f: one Int }\npred inv { some x: A | (sum x.f) = 0 }\nrun inv\n");
}

#[test]
fn int_cast_two_hop_join_single_candidate_accepted_mt126_p14() {
    // p14: single-candidate name reached via a 2-hop join (`a.link.f`) —
    // the `ExprChoice.make` shortcut applies regardless of join depth. Jar:
    // ACCEPT.
    accept(
        "sig X { f: one Int }\nsig A { link: one X }\npred inv { all a: A | int a.link.f >= 0 }\nrun inv\n",
    );
}
