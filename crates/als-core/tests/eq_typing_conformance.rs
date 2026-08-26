//! Integer-equality typing conformance (mt-051): jar-pinned verdicts for the
//! ONE-SIDED `Int[·]`-cast shape at `=`/`in`/multiplicity-tests — the rule that
//! retired the old `eq_typing_defer`. Each row is a probe cell from
//! `scratchpad/probe/ProbeEqTyping*.java` (labels preserved); the expected
//! verdicts are the jar's (Alloy 6.2.0), recorded as constants so CI runs with no
//! oracle (translation-ref §10.7c ext).
//!
//! The pinned rule has two parts (see `overflow_guard.rs`): (A) an overflowed
//! overflow-capable cast denotes the EMPTY set in forbid mode, in every context;
//! (B) each capable cast that SURVIVES the jar's matrix folding on the way to the
//! reader threads the §10.7c rules 0–3 polarity guard. The old part (C) — an
//! unconditional escape for a translation-constant cast — was RETRACTED at
//! mt-130: mt-129 measured the jar keeping the guard on a fully ground
//! overflowing cast, and the sheds it does perform are the union/override and
//! `lone`/`one`/`some` fast paths that (B)'s collector now models
//! (`tests/overflow_shedding_conformance.rs`).
//!
//! Rule 4 — the claimed int-ITE / `implies`-antecedent rescue — was RETRACTED in
//! full at mt-090 (translation-ref §10.7f); part C below is its replacement.
//! Part D (mt-095, §10.7g) pins the `visit(ExprITE)` then-branch dispatch that
//! part C's last two cells were waiting on.
//!
//! MIN spelling: the jar's probes spell MIN as `(0-8)`, which the jar folds to an
//! overflow-free `-8` via its `0-(max+1)` MINUS peephole (`TranslateAlloyToKodkod`
//! :1239). mettle has no such peephole (`(0-8)` is the atom `0`), and `negate[8]`
//! itself OVERFLOWS at bitwidth 4 (the literal `8` exceeds max `7`). The builtin
//! `min` is the overflow-free `-8` both tools agree on, so MIN cells use `min` —
//! isolating the mt-051 rule from the unrelated MINUS-peephole gap.

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Solve command 0 of `src`; `true` = allow overflow (probe "allow" column),
/// `false` = forbid (default; probe "forbid" column). `Ok(true)` = SAT,
/// `Ok(false)` = UNSAT, `Err(())` = a typed defer (must never happen post-mt-051).
fn solve(src: &str, allow_overflow: bool) -> Result<bool, ()> {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let opts = SolveOptions {
        allow_overflow,
        ..SolveOptions::default()
    };
    let Ok(goal) = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0) else {
        return Err(());
    };
    match solve_goal(&ir, &scoped, &goal, &bounds, &opts) {
        Ok(SolveVerdict::Sat(_)) => Ok(true),
        Ok(SolveVerdict::Unsat) => Ok(false),
        Ok(SolveVerdict::Unknown) => panic!("unbudgeted solve returned Unknown"),
        Err(_) => Err(()),
    }
}

// ---------------------------- Q1: value semantics (allow pinned) ------------

#[test]
fn q1_value_semantics_is_set_equality_not_int_promotion() {
    // The one-sided shape is Kodkod set equality/subset, never int-promotion
    // (probe Q1). Allow mode is the jar-pinned part; forbid must at least SOLVE
    // (no defer left). At these scopes nothing overflows, so forbid == allow.

    // Q1-union-b: `{#priority}={#pid}∪{1}` at (1,1) collapses to `{1}={1}` — SAT
    // despite 1 ≠ 1+1 (the decisive set-eq cell).
    let union_b = "sig pid {}\nsig priority {}\n\
        run { #priority = #pid + 1 } for exactly 1 pid, exactly 1 priority, 4 int\n";
    assert_eq!(solve(union_b, true), Ok(true));
    assert!(solve(union_b, false).is_ok());

    // Q1-union-a: `{3}` vs `{1,2}` — singleton ≠ 2-set → UNSAT.
    let union_a = "sig pid {}\nsig priority {}\n\
        run { #priority = #pid + 1 } for exactly 2 pid, exactly 3 priority, 4 int\n";
    assert_eq!(solve(union_a, true), Ok(false));
    assert!(solve(union_a, false).is_ok());

    // Q1-multi: singleton cast can never equal the 2-atom set `{0,1}` → UNSAT.
    let multi = "open util/integer\none sig A { f: set Int }\nfact { A.f = 0+1 }\n\
        run { some m: Int | plus[m,1] = A.f } for 3 but 4 int\n";
    assert_eq!(solve(multi, true), Ok(false));
    assert!(solve(multi, false).is_ok());

    // Q1-empty: singleton cast can never equal the empty set → UNSAT.
    let empty = "open util/integer\none sig A { f: lone Int }\nfact { no A.f }\n\
        run { some m: Int | plus[m,1] = A.f } for 3 but 4 int\n";
    assert_eq!(solve(empty, true), Ok(false));
    assert!(solve(empty, false).is_ok());

    // Q1-swap: set equality is symmetric — matches Q1-multi → UNSAT.
    let swap = "open util/integer\none sig A { f: set Int }\nfact { A.f = 0+1 }\n\
        run { some m: Int | A.f = plus[m,1] } for 3 but 4 int\n";
    assert_eq!(solve(swap, true), Ok(false));
    assert!(solve(swap, false).is_ok());

    // Q1-in-1: `{plus[m,1]} ⊆ {0,1}` holds for m=-1 or m=0 → SAT.
    let in1 = "open util/integer\none sig A { f: set Int }\nfact { A.f = 0+1 }\n\
        run { some m: Int | plus[m,1] in A.f } for 3 but 4 int\n";
    assert_eq!(solve(in1, true), Ok(true));
    assert!(solve(in1, false).is_ok());

    // Q1-in-2: `{0,1} ⊆ {plus[m,1]}` — 2 atoms ⊄ singleton → UNSAT.
    let in2 = "open util/integer\none sig A { f: set Int }\nfact { A.f = 0+1 }\n\
        run { some m: Int | A.f in plus[m,1] } for 3 but 4 int\n";
    assert_eq!(solve(in2, true), Ok(false));
    assert!(solve(in2, false).is_ok());
}

// ------------------------- Q2 / GAP: comparison-level guard (B) -------------

#[test]
fn gap1a_existential_driver_excludes() {
    // `all n: Int | some m: Int | plus[m,7] = n`: a bound-Int var is one side of a
    // one-sided cast. Bare-Int ∃ m ⇒ exclude — n=-8..-2 have no non-overflow
    // witness → forbid UNSAT (probe GAP1a).
    let src =
        "open util/integer\nrun { all n: Int | some m: Int | plus[m,7] = n } for 3 but 4 int\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(false));
}

#[test]
fn q2_rescue_bare_int_forall_rescues() {
    // `all m: Int | some n: {x:Int|x!=min} | plus[m,7] = n`: bare-Int ∀ m at the
    // overflow point (m=1) RESCUES the one-sided set-eq — the first jar-confirmed
    // rescue for the set-eq path (probe Q2-rescue). `min` is overflow-free MIN.
    let src = "open util/integer\n\
        run { all m: Int | some n: {x: Int | x != min} | plus[m,7] = n } for 3 but 4 int\n";
    assert_eq!(solve(src, true), Ok(false));
    assert_eq!(solve(src, false), Ok(true));
}

#[test]
fn q2_defect_a_sig_forall_excludes() {
    // `all p: P | plus[p.n,7] = Fixed.v`, p.n=1, Fixed.v=min: p's domain is a sig
    // (not bare Int) → Defect-A default-exclude extends to set-eq → forbid UNSAT
    // (probe Q2-defectA).
    let src = "open util/integer\none sig P { n: one Int }\none sig Fixed { v: one Int }\n\
        fact { P.n = 1 }\nfact { Fixed.v = min }\n\
        run { all p: P | plus[p.n,7] = Fixed.v } for 3 but 4 int\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(false));
}

#[test]
fn q2_noncap_cast_never_guards() {
    // `Int[3] = m`: the cast is of a constant (not overflow-capable) → no guard
    // fires, allow and forbid agree SAT (probe Q2-noncap).
    let src = "run { some m: Int | Int[3] = m } for 3 but 4 int\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(true));
}

// ------------------------- (A) value + (B) guard, non-constant --------------

#[test]
fn closed_circuit_direct_cast_empties() {
    // D4: `plus[F.v,7] = G.w`, F.v=1 (field, non-constant), G.w=min. plus[1,7]
    // wraps to -8 with overflow → (A) empties the cast → ∅ ≠ {-8} → forbid UNSAT.
    let src = "open util/integer\none sig F { v: one Int }\none sig G { w: one Int }\n\
        fact { F.v = 1 }\nfact { G.w = min }\n\
        run { plus[F.v,7] = G.w } for 3 but 4 int\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(false));
}

#[test]
fn closed_circuit_under_union_empties() {
    // T1: the same closed circuit arithmetic under a relational union (`+ 1`), via
    // `=`; the emptied cast leaves `{1}` ≠ `{-8,1}` → forbid UNSAT (probe T1).
    let src = "open util/integer\none sig F { v: one Int }\none sig G { w: set Int }\n\
        fact { F.v = 1 }\nfact { G.w = min + 1 }\n\
        run { plus[F.v,7] + 1 = G.w } for 3 but 4 int\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(false));
}

#[test]
fn closed_circuit_under_union_in_form_empties() {
    // T4: the `in` (subset) form of T1 shares the guard path → forbid UNSAT.
    let src = "open util/integer\none sig F { v: one Int }\none sig G { w: set Int }\n\
        fact { F.v = 1 }\nfact { G.w = min + 1 }\n\
        run { plus[F.v,7] + 1 in G.w } for 3 but 4 int\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(false));
}

#[test]
fn dependent_existential_under_union_excludes() {
    // V-depun: dependent (∃ m) circuit arithmetic under a union — the (B) guard
    // classifies m as a bare-Int ∃ ⇒ exclude, so the only (overflowing) witness
    // m=1 is dropped → forbid UNSAT (probe V-depun).
    let src = "open util/integer\none sig F { v: set Int }\nfact { F.v = min + 1 }\n\
        run { some m: Int | plus[m,7] + 1 = F.v } for 3 but 4 int\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(false));
}

#[test]
fn wrapping_card_direct_cast_empties() {
    // D6: `#A = F.v`, exactly 9 A at bw3 → #A=9 wraps to 1 WITH overflow → (A)
    // empties the LHS cast → ∅ ≠ {1} → forbid UNSAT (probe D6). The cast operand
    // (`#A` over an exactly-bound sig) is translation-constant, so (B) is skipped —
    // yet (A) still fires, which is what governs the verdict.
    let src = "sig A {}\none sig F { v: one Int }\nfact { F.v = 1 }\n\
        run { #A = F.v } for exactly 9 A, 3 int\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(false));
}

#[test]
fn closed_arith_existential_direct_cast_excludes() {
    // D3a: `some i: Int | plus[3,3] = i` at bw3 → plus[3,3]=6 wraps to -2 WITH
    // overflow → (A) empties the cast → no witness i → forbid UNSAT (probe D3a).
    let src = "run { some i: Int | plus[3,3] = i } for 3 but 3 int\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(false));
}

// ------------------- the union fast path over constant casts ----------------

#[test]
fn constant_escape_trio() {
    // Probe R-cardun/T5/T6. All three use `#pid`/`#priority` over exactly-bound
    // sigs — fully constant translations, so the overflowing `Int[#pid]` folds to
    // a cells-EMPTY matrix. It sits on the LEFT of a union, which is exactly
    // where `BooleanMatrix.or`'s fast path drops its `DefCond` (R-b), so no (B)
    // guard reaches the comparison while the (A) value still governs. mt-051 read
    // this as a blanket "translation-constant casts never guard"; mt-129 refuted
    // that (`run { plus[7,7] in Int }` is jar UNSAT) and mt-130 replaced it with
    // the union rule, which reproduces these three unchanged.

    // R-cardun (=): #pid=9 wraps to 1 (of set) → (A) empties `Int[#pid]`, union
    // with `{1}` gives `{1}` = `{#priority}={1}` → SAT (no (B) exclusion).
    let cardun = "sig pid {}\nsig priority {}\n\
        run { #priority = #pid + 1 } for exactly 9 pid, exactly 1 priority, 3 int\n";
    assert_eq!(solve(cardun, true), Ok(true));
    assert_eq!(solve(cardun, false), Ok(true));

    // T5 (in): #pid=10 wraps to 2 (of set) → `Int[#pid]` empties, RHS = `{1}`;
    // `{#priority}={2}` ⊄ `{1}` → UNSAT (from (A), not (B)).
    let t5 = "sig pid {}\nsig priority {}\n\
        run { #priority in #pid + 1 } for exactly 10 pid, exactly 2 priority, 3 int\n";
    assert_eq!(solve(t5, true), Ok(true));
    assert_eq!(solve(t5, false), Ok(false));

    // T6 (negated =): inner `=` is false via (A) (as in T5), so `!(...)` is true →
    // SAT — the (A) emptying is polarity-independent, and (B) is escaped.
    let t6 = "sig pid {}\nsig priority {}\n\
        run { !(#priority = #pid + 1) } for exactly 10 pid, exactly 2 priority, 3 int\n";
    assert_eq!(solve(t6, true), Ok(true));
    assert_eq!(solve(t6, false), Ok(true));
}

// ---------------------------- MultTest (T7) ---------------------------------

#[test]
fn mult_test_threads_the_guard() {
    // T7: `some plus[F.v,7]` (a MultTest over `Int[plus[F.v,7]]`), F.v=1 → the cast
    // overflows → (A) empties it → `some ∅` is false → forbid UNSAT (probe T7).
    let src = "open util/integer\none sig F { v: one Int }\nfact { F.v = 1 }\n\
        run { some plus[F.v,7] } for 3 but 4 int\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(false));
}

// -------------- Part C: the retracted rule-4 sliver (int-compare path) -------

/// The `for 3 but 4 int` Part-C cell shape: a non-bare-`Int` (comprehension)
/// domain over the whole positive range, so every binding overflows `plus[n,7]`.
fn part_c_cell(body: &str) -> String {
    format!(
        "open util/integer\n\
         run {{ all n: {{x: Int | x>=1 and x<=7}} | {body} }} for 3 but 4 int\n"
    )
}

#[test]
fn part_c_no_escape_from_defect_a() {
    // **Rule 4 is RETRACTED (mt-090, translation-ref §10.7f).** There is no
    // escape: `DefCond.isUnivQuant` cannot see any surrounding operator, and
    // `env.negate()` fires only in `visit(NotFormula)`, so an `implies`
    // antecedent does not even flip polarity. Every cell below is plain Defect A
    // (comprehension domain ⇒ existential) at the polarity its `not`-count gives.
    //
    // Re-verified against the jar at mt-090 (`scratchpad/probe/mt090/p4_jar.txt`,
    // probes h0/h4–h9), same spelling, same scopes.

    // h0 direct-ctl: no wrapper — exclude fires → UNSAT/UNSAT.
    let direct = part_c_cell("plus[n,7] >= 0");
    assert_eq!(solve(&direct, true), Ok(false));
    assert_eq!(solve(&direct, false), Ok(false));

    // h5/h6 IMP-P9 / IMP-nested: forbid SAT, and mt-090 re-derives it WITHOUT an
    // escape — the antecedent keeps the `run`'s positive polarity, the Defect-A
    // existential classification forces it FALSE, and the implication is
    // vacuously true. mt-051 read the same verdict as "antecedent ⇒ rescue"
    // because a wrong polarity and a wrong classification cancelled here.
    for body in [
        "(plus[n,7]<0 implies (1=0))",
        "(n>=1 implies (plus[n,7]<0 implies (1=0)))",
    ] {
        let src = part_c_cell(body);
        assert_eq!(solve(&src, true), Ok(false), "allow {body}");
        assert_eq!(solve(&src, false), Ok(true), "forbid {body}");
    }

    // h4 ITE-both: both branches are `util/integer` fun results, so BOTH tools
    // build a relational if-then-else over `Int[·]` casts — the overflowed cast
    // is empty (§10.7e FACT 2) and `sum ∅ = 0 >= 0` holds → forbid SAT. No
    // classification changed; contrast h1/h2/h3 below.
    let ite_both = part_c_cell("(n>3 => plus[n,7] else plus[n,1]) >= 0");
    assert_eq!(solve(&ite_both, true), Ok(false));
    assert_eq!(solve(&ite_both, false), Ok(true));

    // h7 IMP-conseq / h8 AND-ctl / h9 V-not: ordinary exclusion → UNSAT/UNSAT.
    for body in [
        "(n>3 implies plus[n,7]>=0)",
        "(n>=1 and plus[n,7]>=0)",
        "!(plus[n,7] < 0)",
    ] {
        let src = part_c_cell(body);
        assert_eq!(solve(&src, true), Ok(false), "allow {body}");
        assert_eq!(solve(&src, false), Ok(false), "forbid {body}");
    }
}

#[test]
fn part_c_mixed_branch_ite_is_relational_in_the_jar() {
    // Jar verdicts pinned at mt-090 (`scratchpad/probe/mt090/p4_jar.txt`, probes
    // h1/h2/h3 — h1 is mt-051's P12 verbatim). All three are forbid **SAT**
    // because the jar builds a RELATIONAL if-then-else over `Int[·]` casts: the
    // overflowed branch is the empty set and `sum ∅ = 0`, so `>= 0` holds.
    //
    // CLOSED at mt-095 (translation-ref §10.7g): `visit(ExprITE)` dispatches on
    // the `then` branch alone and an Alloy NUMBER literal translates to a SET,
    // so `Lowerer::ite_sort` now reads the sort off the `then` branch with a
    // bare numeral counted as relational. mt-090 predicted a second half — a
    // *dynamic* constant-escape — and the mt-095 probe wave REFUTED it: the
    // guard is shed by structure, not by constant-folding (see
    // `part_d_the_escape_is_structural_not_dynamic`), so no escape work was
    // needed and the encoder/evaluator pair is untouched.
    for body in [
        "(n>0 => plus[n,7] else 0) >= 0",
        "(n>3 => plus[n,7] else 5) >= 0",
        "(n<=3 => 5 else plus[n,7]) >= 0",
    ] {
        let src = part_c_cell(body);
        assert_eq!(solve(&src, true), Ok(false), "allow {body}");
        assert_eq!(solve(&src, false), Ok(true), "forbid {body}");
    }
}

// ------- Part D: the `visit(ExprITE)` then-branch dispatch rule (mt-095) -----
//
// Jar cells from `scratchpad/probe/mt095/` (`q1_dispatch.als` → `i*`,
// `q2_escape.als` → `j*`, `q4_shed.als` → `k*`, `q5_boundary.als` → `m*`; raw
// jar output in the matching `*_jar.txt`, per-cell verdicts in `*_compare.txt`).
// Rule in translation-ref §10.7g. Everything here is jar-free: the expected
// verdicts are constants recorded from that wave.

/// The Part-D cell shape: the Part-C comprehension domain (so `plus[n,7]`
/// overflows at every binding of `n` at bitwidth 4) plus the sigs the branch
/// shapes need. Matches `scratchpad/probe/mt095/q1_dispatch.als` exactly.
fn part_d_cell(body: &str) -> String {
    format!(
        "open util/integer\n\
         sig Node {{}}\n\
         one sig F {{ v: one Int }}\n\
         fact FixV {{ F.v = 1 }}\n\
         run {{ all n: {{x: Int | x>=1 and x<=7}} | {body} }} for 3 but 4 int\n"
    )
}

#[test]
fn part_d_ite_dispatches_on_the_then_branch_alone() {
    // The decisive mirrored pair (i1/i2). Both cells put the SAME overflowing
    // arithmetic in the branch the ground-constant condition SELECTS; only which
    // syntactic slot the int-sorted branch occupies moves. A rule that consulted
    // either branch could not separate them.
    //
    // i1: `then` is a `util/integer` call, whose body the resolver wraps in
    // `Int[·]` ⇒ an `Expression` ⇒ relational ITE ⇒ the overflowed cast is empty
    // ⇒ `sum ∅ = 0 >= 0` ⇒ SAT.
    let i1 = part_d_cell("(n>0 => plus[n,7] else #Node) >= 0");
    assert_eq!(solve(&i1, false), Ok(true), "i1 forbid");
    assert_eq!(solve(&i1, true), Ok(false), "i1 allow");

    // i2: `then` is `#Node` ⇒ CARDINALITY ⇒ an `IntExpression` ⇒ int ITE ⇒ the
    // else is `cint`-coerced, which UNWRAPS the cast and keeps its accumulated
    // overflow ⇒ the Defect-A exclusion fires ⇒ UNSAT.
    let i2 = part_d_cell("(n<=0 => #Node else plus[n,7]) >= 0");
    assert_eq!(solve(&i2, false), Ok(false), "i2 forbid");
    assert_eq!(solve(&i2, true), Ok(false), "i2 allow");
}

#[test]
fn part_d_a_numeral_branch_is_a_set_not_an_int() {
    // i5 vs i2: identical condition, identical else, and the `then` branch is a
    // bare numeral instead of `#Node`. `visit(ExprConstant)` case NUMBER is
    // `IntConstant.constant(n).toExpression()` — an `IntToExprCast`, which is an
    // `Expression`, and `visit(ExprITE)` tests `instanceof Expression` BEFORE
    // `instanceof IntExpression`. So the numeral makes the ITE relational.
    let i5 = part_d_cell("(n<=0 => 0 else plus[n,7]) >= 0");
    assert_eq!(solve(&i5, false), Ok(true), "i5 forbid");
    assert_eq!(solve(&i5, true), Ok(false), "i5 allow");

    // The value of that relational ITE is pinned from three directions, so the
    // SAT above cannot be explained by a lost guard alone:
    //   i6 `> 7`  — UNSAT: `sum ∅` is 0, not the wrapped arithmetic.
    //   i7 `<= 0` — SAT:   0 satisfies it, in BOTH overflow modes.
    //   i21 `= 0` — UNSAT: as a SET the ITE is ∅, and `∅ = {0}` is false
    //               (§10.7e FACT 1 set equality), which an int reading would
    //               have made true. This is the cell that proves the ITE really
    //               denotes the empty SET rather than the integer 0.
    let i6 = part_d_cell("(n<=0 => 0 else plus[n,7]) > 7");
    assert_eq!(solve(&i6, false), Ok(false), "i6 forbid");
    let i7 = part_d_cell("(n<=0 => 0 else plus[n,7]) <= 0");
    assert_eq!(solve(&i7, false), Ok(true), "i7 forbid");
    assert_eq!(solve(&i7, true), Ok(true), "i7 allow");
    let i21 = part_d_cell("(n<=0 => 0 else plus[n,7]) = 0");
    assert_eq!(solve(&i21, false), Ok(false), "i21 forbid");
}

#[test]
fn part_d_then_branch_kinds() {
    // Every shape whose Kodkod class the dispatch reads. Relational (⇒ SAT):
    // a redundant `Int[·]` cast the resolver strips to its operand (i9), a bound
    // quantifier variable (i10), a constant-foldable call (i12).
    for (cell, body) in [
        ("i9", "(n<=0 => Int[F.v] else plus[n,7]) >= 0"),
        ("i10", "(n<=0 => n else plus[n,7]) >= 0"),
        ("i12", "(n<=0 => plus[3,4] else plus[n,7]) >= 0"),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(true), "{cell} forbid");
        assert_eq!(solve(&src, true), Ok(false), "{cell} allow");
    }

    // Int-kind (⇒ UNSAT): a `sum` quantifier (i11), `#` of an Int-typed set
    // rather than of a sig (m6).
    for (cell, body) in [
        ("i11", "(n<=0 => (sum q: Node | 1) else plus[n,7]) >= 0"),
        ("m6", "(n<=0 => #(F.v) else plus[n,7]) >= 0"),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(false), "{cell} forbid");
        assert_eq!(solve(&src, true), Ok(false), "{cell} allow");
    }
}

#[test]
fn part_d_dispatch_recurses_and_ignores_the_untaken_branch() {
    // Nested ITE (i14/i15): the outer `then` is itself an ITE, so the outer sees
    // the INNER's own kind — numeral-then inner ⇒ relational ⇒ SAT;
    // cardinality-then inner ⇒ int ⇒ UNSAT.
    let i14 = part_d_cell("(n<=0 => (n>3 => 0 else 1) else plus[n,7]) >= 0");
    assert_eq!(solve(&i14, false), Ok(true), "i14 forbid");
    let i15 = part_d_cell("(n<=0 => (n>3 => #Node else #Node) else plus[n,7]) >= 0");
    assert_eq!(solve(&i15, false), Ok(false), "i15 forbid");

    // An ITE nested in the ELSE is coerced by the outer arm it lands in (i16
    // relational / i17 int), and either way the outer's own `then` decides.
    let i16 = part_d_cell("(n<=0 => 0 else (n>0 => plus[n,7] else 0)) >= 0");
    assert_eq!(solve(&i16, false), Ok(true), "i16 forbid");
    let i17 = part_d_cell("(n<=0 => #Node else (n>0 => plus[n,7] else 0)) >= 0");
    assert_eq!(solve(&i17, false), Ok(true), "i17 forbid");

    // Negative space: the branch the condition does NOT select contributes
    // nothing, on either dispatch (i3 relational / i4 int, both SAT).
    for (cell, body) in [
        ("i3", "(n<=0 => plus[n,7] else #Node) >= 0"),
        ("i4", "(n>0 => #Node else plus[n,7]) >= 0"),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(true), "{cell} forbid");
        assert_eq!(solve(&src, true), Ok(true), "{cell} allow");
    }
}

#[test]
fn part_d_dispatch_holds_in_operand_position_too() {
    // The ITE as a `util/integer` call ARGUMENT, not as a comparison operand.
    // An argument is `cset`-coerced, so a relational ITE stays a set and its
    // emptied cast reads 0 (i18/m16 SAT), while an int ITE is re-wrapped as
    // `Int[·]` and then UNWRAPPED by the callee's own `cint`, keeping the
    // overflow (i19/m17 UNSAT).
    for (cell, body) in [
        ("i18", "plus[(n<=0 => 0 else plus[n,7]), 0] >= 0"),
        ("m16", "plus[(n<=0 => 0 else plus[n,7]), 3] = 3"),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(true), "{cell} forbid");
        assert_eq!(solve(&src, true), Ok(false), "{cell} allow");
    }
    for (cell, body) in [
        ("i19", "plus[(n<=0 => #Node else plus[n,7]), 0] >= 0"),
        ("m17", "plus[(n<=0 => #Node else plus[n,7]), 3] = 3"),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(false), "{cell} forbid");
        assert_eq!(solve(&src, true), Ok(false), "{cell} allow");
    }
}

#[test]
fn part_d_the_escape_is_structural_not_dynamic() {
    // mt-090 predicted that matching the jar here would need a DYNAMIC constant
    // escape — the jar sheds the DefCond, the theory went, because the ground
    // cast matrix folds to constant-empty. The mt-095 wave REFUTES that: every
    // relational-ITE cell below is forbid SAT no matter how non-constant the
    // cast operand is. The shedding is structural — a cast that `toInt` must
    // read with `.sum()` instead of UNWRAPPING contributes no comparison-level
    // guard, whatever it is built from.
    //
    // j2/j3: the operand is a relation pinned only by a FACT, so it is not a
    // translation constant on any reading (j3 has no quantifier at all).
    // j5: a ground variable mixed with such a relation.
    // j9: only some bindings overflow, so the escape is per-binding. (j6/j7 —
    // an exactly-bound vs a merely-constrained cardinality — were mt-051's
    // evidence for a constant escape mettle no longer has; the `.sum()`
    // fall-through below is what actually sheds here.)
    let escapes = [
        ("j0", "(n>0 => plus[n,7] else 0) >= 0"),
        ("j2", "(n>0 => plus[F.v,7] else 0) >= 0"),
        ("j5", "(n>0 => plus[n,F.v] else 0) >= 0"),
        ("j9", "(n>0 => plus[n,3] else 0) >= 0"),
    ];
    for (cell, body) in escapes {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(true), "{cell} forbid");
    }

    // The controls that keep the rule honest: strip the ITE and the very same
    // arithmetic goes back to UNSAT, because `toInt` then UNWRAPS the cast
    // (`IntToExprCast → intExpr()`) and the guard survives (j1/j4).
    for (cell, body) in [("j1", "plus[n,7] >= 0"), ("j4", "plus[F.v,7] >= 0")] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(false), "{cell} forbid");
    }

    // j10/j11: and the emptied branch really reads 0 — `> 7` and a per-binding
    // `= 0` are both UNSAT, so j9's SAT is not a blanket collapse.
    for (cell, body) in [
        ("j10", "(n>0 => plus[n,3] else 0) > 7"),
        ("j11", "int[(n>0 => plus[n,3] else 0)] = 0"),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(false), "{cell} forbid");
    }
}

#[test]
fn part_d_shedding_is_not_specific_to_the_ite() {
    // The same `.sum()` fall-through shrouds a cast behind ANY set former, so
    // these were already agreeing before mt-095 and must keep agreeing after:
    // a union (k2), an intersection (k5), a difference (k6), a comprehension
    // (k7) — all forbid SAT — against the bare cast (k0), forbid UNSAT.
    for (cell, body) in [
        ("k2", "(plus[n,7] + plus[n,7]) >= 0"),
        ("k5", "(plus[n,7] & Int) >= 0"),
        ("k6", "(plus[n,7] - 0) >= 0"),
        ("k7", "{y: Int | y in plus[n,7]} >= 0"),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(true), "{cell} forbid");
    }
    let k0 = part_d_cell("plus[n,7] >= 0");
    assert_eq!(solve(&k0, false), Ok(false), "k0 forbid");

    // Negative space for the whole rule: a SET-level reader (`=`, `in`, `no`)
    // over a BARE cast still applies the guard — the shedding belongs to the
    // int-reading path, not to sets in general (k13/k14/k15).
    for (cell, body) in [
        ("k13", "plus[n,7] = 0"),
        ("k14", "no plus[n,7]"),
        ("k15", "plus[n,7] in Int"),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(false), "{cell} forbid");
    }
}

#[test]
fn part_d_change_is_inert_where_nothing_overflows() {
    // The dispatch change re-routes every numeral-then ITE through the
    // relational path, including ones with no overflow anywhere. There the
    // relational reading yields the singleton `Int[·]`, whose `sum` is the same
    // number, so the answers must not move (m7/m8/m9/m10/m11/m12).
    for (cell, body, want) in [
        ("m7", "(n>3 => 3 else 5) >= 3", true),
        ("m8", "(n>3 => 3 else 5) = 5", false),
        ("m9", "(n>3 => 3 else 5) < 4", false),
        ("m10", "(n>3 => #Node else #F) >= 0", true),
        ("m11", "(n>3 => 3 else 5) in Int", true),
        ("m12", "some (n>3 => 3 else 5)", true),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(want), "{cell} forbid");
        assert_eq!(solve(&src, true), Ok(want), "{cell} allow");
    }

    // And where the ITE is read as a SET whose selected branch DID overflow, the
    // cast's emptiness plus the set-level guard still exclude it: `some` is
    // false and `no` does not become vacuously true (m13/m14, both UNSAT).
    for (cell, body) in [
        ("m13", "some (n<=0 => 0 else plus[n,7])"),
        ("m14", "no (n<=0 => 0 else plus[n,7])"),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, false), Ok(false), "{cell} forbid");
    }
}

// ------- Part E: the layer-(2) set-former guard corner (mt-096) --------------
//
// Jar cells from `scratchpad/probe/mt096/` (`r1_former_reader.als` → `f*`,
// `r2_union_depth.als` → `u*`, `r3_union_sibling.als` → `v*`, `r4_t1t4.als` →
// `t*`; raw jar output in the matching `*_jar.txt`, per-cell verdicts in
// `*_compare.txt`). Rule and its open edge in translation-ref §10.7h.
//
// LEDGER-010's amended layer (2) says a cast reached through *any* set former
// sheds the comparison-level guard. The mt-096 wave measured that against the
// jar across a former × reader matrix and it is **too broad**: the jar keeps the
// guard through an intersection, a difference, an if-then-else, a join, an
// override and a product. Only the UNION sheds, and only when the operand it
// drops is cells-empty — the rule mt-129 pinned and mt-130 implemented, with the
// full 62-cell matrix in `tests/overflow_shedding_conformance.rs`.
//
// Each cell's reader is chosen to be TRUE on the (empty, or `{3}`) value the
// layer-(1) emptiness leaves behind, so guard ⇒ UNSAT and no-guard ⇒ SAT, and
// the allow column is the internal control: an allow/forbid split IS the guard.

/// The Part-E cell shape — `scratchpad/probe/mt096/r1_former_reader.als`
/// exactly. `plus[n,7]` overflows at every binding of `n` at bitwidth 4.
fn part_e_cell(body: &str) -> String {
    format!(
        "open util/integer\n\
         sig Node {{}}\n\
         run {{ all n: {{x: Int | x>=1 and x<=7}} | {body} }} for 3 but 4 int\n"
    )
}

/// The same, plus the `P.g` diagonal the join cells need.
fn part_e_join_cell(body: &str) -> String {
    format!(
        "open util/integer\n\
         one sig P {{ g: Int -> Int }}\n\
         fact Diag {{ P.g = {{a: Int, b: Int | a = b}} }}\n\
         run {{ all n: {{x: Int | x>=1 and x<=7}} | {body} }} for 3 but 4 int\n"
    )
}

#[test]
fn part_e_every_former_except_union_keeps_the_guard() {
    // The measured negative space, and the reason the `collect_capable_casts`
    // walk still descends through all of these. Each has the allow/forbid split
    // that marks a real guard.
    for (cell, body) in [
        ("f3r1/u2", "(plus[n,7] & Int) in Int"),
        ("u5", "((plus[n,7] & Int) & Int) in Int"),
        ("f4r1", "(plus[n,7] - none) in Int"),
        ("f6r1", "(n>0 => plus[n,7] else 0) in Int"),
        ("f7r1", "(n<=0 => 0 else plus[n,7]) in Int"),
    ] {
        let src = part_e_cell(body);
        assert_eq!(solve(&src, false), Ok(false), "{cell} forbid");
        assert_eq!(solve(&src, true), Ok(true), "{cell} allow");
    }
    // The `no` reader over the same formers: UNSAT in BOTH modes — in allow mode
    // for a value reason (the wrapped cast is a non-empty singleton), in forbid
    // mode because the guard fires on the empty one.
    for (cell, body) in [
        ("f3r2", "no (plus[n,7] & Int)"),
        ("f4r2", "no (plus[n,7] - none)"),
        ("f6r2/m14", "no (n>0 => plus[n,7] else 0)"),
        ("f7r2", "no (n<=0 => 0 else plus[n,7])"),
    ] {
        let src = part_e_cell(body);
        assert_eq!(solve(&src, false), Ok(false), "{cell} forbid");
        assert_eq!(solve(&src, true), Ok(false), "{cell} allow");
    }
    let join = part_e_join_cell("(plus[n,7]).(P.g) in Int");
    assert_eq!(solve(&join, false), Ok(false), "f8r1 forbid");
    assert_eq!(solve(&join, true), Ok(true), "f8r1 allow");
}

#[test]
fn part_e_a_union_of_two_capable_casts_guards() {
    // u11/v3: whatever the union corner turns out to be, it is NOT unconditional
    // shedding — when both operands carry a capable cast the guard survives, and
    // mettle matches the jar here today.
    for (cell, body) in [
        ("v3", "(plus[n,7] + plus[n,7]) in Int"),
        ("u11", "(plus[n,7] + plus[n,1]) in Int"),
    ] {
        let src = part_e_cell(body);
        assert_eq!(solve(&src, false), Ok(false), "{cell} forbid");
        assert_eq!(solve(&src, true), Ok(true), "{cell} allow");
    }
}

#[test]
fn part_e_union_guard_survives_without_a_quantifier() {
    // t4c/t4b — the mt-096 re-probe of mt-051's T1/T4, and the cells that refute
    // every "the union sheds" rule tried at mt-096. `plus[F.v,7] + 1 in Int` is
    // jar forbid UNSAT: a union-nested capable cast, sibling a plain constant
    // cast, and the guard still fires. The ONLY difference from probe u1 (jar
    // forbid SAT, same union shape) is the enclosing comprehension-∀.
    let no_quant = "open util/integer\none sig F { v: one Int }\nfact FixF { F.v = 1 }\n\
        run { plus[F.v,7] + 1 in Int } for 3 but 4 int\n";
    assert_eq!(solve(no_quant, false), Ok(false), "t4c forbid");
    assert_eq!(solve(no_quant, true), Ok(true), "t4c allow");

    // t4e — the same expression under the part-C forall is jar forbid **SAT**,
    // and mettle now matches: the ground `plus[n,7]` folds to a cells-empty
    // matrix, which is the LEFT operand the union's fast path drops (mt-130).
    let quant = part_e_cell("(plus[n,7] + 1) in Int");
    assert_eq!(solve(&quant, true), Ok(true), "t4e allow");
    assert_eq!(solve(&quant, false), Ok(true), "t4e forbid");
}

#[test]
fn part_e_the_sum_reader_sheds_on_every_former() {
    // Unchanged from mt-095 §10.7g and untouched by this bead: an int-position
    // read of a set goes through `.sum()`, which carries no guard whatever the
    // former — so these stay SAT.
    for (cell, body) in [
        ("f1r3", "(plus[n,7] + 3) >= 0"),
        ("f3r3", "(plus[n,7] & Int) >= 0"),
        ("f4r3", "(plus[n,7] - none) >= 0"),
        ("f6r3", "(n>0 => plus[n,7] else 0) >= 0"),
        ("f5r3", "{y: Int | y in plus[n,7]} >= 0"),
    ] {
        let src = part_e_cell(body);
        assert_eq!(solve(&src, false), Ok(true), "{cell} forbid");
    }
    // …while the BARE cast in int position keeps it (`toInt` unwraps).
    let bare = part_e_cell("plus[n,7] >= 0");
    assert_eq!(solve(&bare, false), Ok(false), "f0r3 forbid");
}

#[test]
fn part_e_comprehension_sheds_on_both_sides() {
    // f5: a comprehension body is a Formula position, which the walk already
    // refuses to enter (each inner comparison guards at its own site), and the
    // jar agrees — SAT in both modes for every reader.
    for (cell, body) in [
        ("f5r1", "{y: Int | y in plus[n,7]} in Int"),
        ("f5r2", "no {y: Int | y in plus[n,7]}"),
    ] {
        let src = part_e_cell(body);
        assert_eq!(solve(&src, false), Ok(true), "{cell} forbid");
    }
}

#[test]
fn part_e_non_capable_and_non_overflowing_controls() {
    // u18/u19/u20/v4: the UNSATs above come from overflow capability, not from
    // the shape — a constant cast and a never-overflowing one are SAT in both
    // modes in the very same positions.
    for (cell, body) in [
        ("u19", "Int[3] in Int"),
        ("u18", "(Int[3] & Int) in Int"),
        ("u20", "(plus[n,0] & Int) in Int"),
        ("v4", "plus[n,0] in Int"),
    ] {
        let src = part_e_cell(body);
        assert_eq!(solve(&src, false), Ok(true), "{cell} forbid");
        assert_eq!(solve(&src, true), Ok(true), "{cell} allow");
    }
}

#[test]
fn part_e_union_sheds_under_a_quantifier_in_the_jar() {
    // Jar verdicts pinned at mt-096, LIVE since mt-130 (this test carried an
    // `#[ignore]` for the whole pinned interval). All forbid **SAT**: under the
    // part-C forall, `n` is ground per binding, so `plus[n,7]`'s overflow circuit
    // folds to the constant TRUE and its matrix to zero cells — the operand
    // `BooleanMatrix.or` drops the `DefCond` of.
    //
    // The rule that closes it also explains `part_e_union_guard_survives_without
    // _a_quantifier` (t4c: `F.v` is relation-derived, so the circuit is a gate,
    // the matrix has cells, and nothing sheds) and
    // `part_e_a_union_of_two_capable_casts_guards` (both operands cells-empty ⇒
    // the LEFT test wins and the result carries the RIGHT's live circuit).
    for (cell, body) in [
        ("u1", "(plus[n,7] + 3) in Int"),
        ("u10", "(3 + plus[n,7]) in Int"),
        ("v8", "(plus[n,7] + none) in Int"),
        ("v6", "(plus[n,7] + Node) in univ"),
        ("f1r5/k16", "(plus[n,7] + 3) = 3"),
        ("f2r2", "no (plus[n,7] + none)"),
        ("u12", "some (plus[n,7] + 3)"),
        ("t4e", "(plus[n,7] + 1) in Int"),
        ("u3", "((plus[n,7] + 3) & Int) in Int"),
        ("u4", "((plus[n,7] & Int) + 3) in Int"),
        ("u7", "((n>0 => plus[n,7] else 0) + 3) in Int"),
        ("v9", "(plus[n,7] + 3 + plus[n,1]) in Int"),
    ] {
        let src = part_e_cell(body);
        assert_eq!(solve(&src, false), Ok(true), "{cell} forbid");
    }
}

// ------- Part F: `toInt`'s unwrap and the `=`/`in` split (mt-127) ------------
//
// `cint` (`TranslateAlloyToKodkod.java:683`) is `toInt(visitThis(x))`, and
// `toInt`'s first arm (:691-695) rewrites an `ExprToIntCast` over an
// `IntToExprCast` to that operand's raw `intExpr()` — throwing the cast
// operator away. `Expression.count()` and `Expression.sum()` are Kodkod's two
// `ExprToIntCast` constructors, so `#` and `int[·]` over a **bare** `Int[·]`
// cast read the cast's integer and DISCARD the cardinality.
//
// Which positions reach `cint` is the whole content of the rule, and it is not
// what the surface syntax suggests:
//
// * `<`/`=<`/`>`/`>=`, arithmetic operands, `Int[·]`, a `sum` quantifier's body
//   and an int if-then-else's ELSE branch call `cint` directly.
// * `=`/`!=` do NOT: they reach their operands through `toSet(a,
//   visitThis(a))` (:1285-1306), which wraps without ever calling `toInt`.
// * `in`/`!in` DO — not through the translator but through the **resolver**,
//   which inserts an `Int[·]` (`int->Int`) around each int-typed operand of an
//   `in` before translation. `AstDump` of the resolved tree shows the cast on
//   both `in` operands and on neither `=` operand.
//
// So the same `#(Int[3])` is 1 under `=`, 3 under `>=`, and 3 under `in`. Every
// verdict below is the jar's, measured at `scratchpad/probe/mt127/` on the
// models these helpers build verbatim (`w14_testcells_A.als`,
// `w14_testcells_B.als`); the probe NOTES carry the full 164-cell table.

/// The mt-127 wave-1 model, verbatim.
fn mt127_cell(body: &str, scope: &str) -> String {
    format!(
        "open util/integer\n\
         sig Node {{}}\n\
         one sig F {{ v: Int }}\n\
         fun three: Int {{ 3 }}\n\
         run {{ {body} }} for {scope}\n"
    )
}

/// The mt-127 gate model: two sigs to take cardinalities of, and a field whose
/// value is fixed but not exactly bound.
fn mt127_gate_cell(body: &str, scope: &str) -> String {
    format!(
        "open util/integer\n\
         sig A {{}}\n\
         sig B {{}}\n\
         one sig G {{ w: Int }}\n\
         fact {{ G.w = 7 }}\n\
         run {{ {body} }} for {scope}\n"
    )
}

/// Both overflow modes agree on this cell (nothing in it can overflow).
fn mt127_both(cell: &str, src: &str, sat: bool) {
    assert_eq!(solve(src, false), Ok(sat), "{cell} forbid");
    assert_eq!(solve(src, true), Ok(sat), "{cell} allow");
}

#[test]
fn part_f_cardinality_of_a_bare_cast_unwraps_in_an_int_position() {
    // `Int[3]` is the one-element set {3} and `plus[3,4]` the one-element {7}.
    // Read by `cint`, both give the cast's integer, not 1.
    for (cell, body, sat) in [
        ("a1", "#(Int[3]) >= 3", true),
        ("a2", "#(Int[3]) >= 2", true),
        ("a5", "#(Int[3]) < 3", false), // 3 < 3, not 1 < 3
        ("n6", "#(plus[3,4]) >= 7", true),
        ("n7", "#(plus[3,4]) >= 2", true),
        ("u1", "#(plus[plus[3,0],4]) >= 7", true),
        ("u2", "#(Int[plus[3,4]]) >= 7", true),
        // an arithmetic operand is a `cint` site, so the unwrap fires INSIDE
        // and the enclosing `=` then compares 3 with 3
        ("a6", "plus[#(Int[3]), 0] = 3", true),
        ("s5", "plus[0, #(Int[3])] = 3", true),
    ] {
        mt127_both(cell, &mt127_cell(body, "3 but 4 int"), sat);
    }
    // The `sum`-quantifier body is a `cint` site too (:1588).
    for (cell, body, sat) in [
        ("s3", "(sum n: Node | #(Int[3])) >= 3", true),
        ("s4", "(sum n: Node | #(Int[3])) >= 2", true),
        ("u7", "#(sum n: Node | plus[3,4]) >= 7", true),
    ] {
        mt127_both(cell, &mt127_cell(body, "exactly 1 Node, 4 int"), sat);
    }
}

#[test]
fn part_f_equality_reads_the_same_cardinality_raw() {
    // The decisive contrast with the test above: `=`/`!=` never call `toInt`,
    // so the identical operand is a cardinality of 1. a1 vs a3 is the pair.
    for (cell, body, sat) in [
        ("a3", "#(Int[3]) = 3", false),
        ("a4", "#(Int[3]) = 1", true),
        ("z6", "#(Int[3]) != 3", true),
        ("z7", "#(Int[3]) != 1", false),
        ("n1", "#(plus[3,4]) = 7", false),
        ("n2", "#(plus[3,4]) = 1", true),
        ("s6", "#(Int[3]) = #(Int[5])", true), // 1 = 1
        // A source-written `Int[·]` does not survive resolution as a node of
        // its own (the resolver deletes it and re-derives the coercion from
        // context), so these are a3/a4 again, not `3 = 3`.
        ("z8", "Int[#(Int[3])] = 3", false),
        ("z9", "Int[#(Int[3])] = 1", true),
    ] {
        mt127_both(cell, &mt127_cell(body, "3 but 4 int"), sat);
    }
}

#[test]
fn part_f_membership_casts_both_operands_so_it_unwraps() {
    // `isIn` never consults cast-ness (:1327), but the resolver has already
    // wrapped both int-typed operands in `Int[·]` — and CAST2SIGINT is
    // `cint(sub).toExpression()`. So `in` lands on the unwrapped side of the
    // split even though `=`, its structural twin, does not.
    for (cell, body, sat) in [
        ("a7", "#(Int[3]) in 3", true),  // {3} in {3}
        ("a8", "#(Int[3]) in 1", false), // not {1} in {1}
        ("s7", "#(Int[3]) !in 3", false),
        ("s8", "#(Int[3]) !in 1", true),
    ] {
        mt127_both(cell, &mt127_cell(body, "3 but 4 int"), sat);
    }
}

#[test]
fn part_f_the_int_cast_reader_unwraps_on_both_paths() {
    // `int[·]`/`sum` is CAST2INT → `sum(cset(e))`, and the `sum()` helper
    // (:905-909) strips a bare `IntToExprCast` at CONSTRUCTION — so unlike `#`
    // this reader unwraps under `=` as well.
    for (cell, body, sat) in [
        ("a9", "int[Int[3]] >= 3", true),
        ("a10", "int[Int[3]] = 3", true),
        ("s9", "int[#(Int[3])] = 3", true),
    ] {
        mt127_both(cell, &mt127_cell(body, "3 but 4 int"), sat);
    }
}

#[test]
fn part_f_only_a_bare_cast_unwraps() {
    // The negative space. A union, an intersection, a join and a real relation
    // are not `IntToExprCast`s, so `#` of them stays a real cardinality — in an
    // int position as much as anywhere else.
    for (cell, body, sat) in [
        ("n10", "#(plus[3,4] + plus[1,1]) >= 2", true),
        ("c6", "#(Int[3] + Int[4]) >= 2", true),
        ("c7", "#(Int[3] + Int[4]) >= 3", false),
        ("c8", "#(Int[3] & Int) >= 3", false),
        ("c9", "#(F.v) >= 3", false),
        // A union OPERAND is reached by `cset`, not by a resolver-inserted
        // cast, so it keeps its cardinality: {1} ∪ {1}, not {3} ∪ {1}.
        ("z1", "(#(Int[3]) + Int[1]) = (Int[3] + Int[1])", false),
        ("z2", "(#(Int[3]) + Int[1]) = Int[1]", true),
    ] {
        mt127_both(cell, &mt127_cell(body, "3 but 4 int"), sat);
    }
    mt127_both(
        "c5",
        &mt127_cell("#Node >= 3", "exactly 3 Node, 4 int"),
        true,
    );
}

#[test]
fn part_f_an_if_then_else_operand_is_never_a_bare_cast() {
    // `visit(ExprITE)` builds an IfExpression whenever the then branch
    // translates to an `Expression` — which a `util/integer` call does, its
    // declared return type being the `Int` SIG. An IfExpression is not an
    // `IntToExprCast`, so `#` of one is a real cardinality no matter how the
    // result is read (t1 vs the a1/n6 rows above), and a source `Int[·]` around
    // it changes nothing because the resolver deletes it (u3).
    for (cell, body, sat) in [
        ("c1", "#(some Node => Int[3] else Int[5]) >= 3", false),
        ("c2", "#(some Node => Int[3] else Int[5]) = 1", true),
        ("t1", "#(some Node => plus[3,4] else 0) >= 7", false),
        ("t2", "#(some Node => plus[3,4] else 0) >= 1", true),
        ("t3", "#(some Node => plus[3,4] else 0) = 1", true),
        ("t4", "#(some Node => plus[3,4] else 0) = 7", false),
        ("t5", "#(no Node => 0 else plus[3,4]) >= 7", false),
        ("u3", "#(Int[(some Node => plus[3,4] else 0)]) >= 7", false),
        ("u5", "#(some Node => plus[3,4] else plus[3,4]) >= 7", false),
        (
            "u6",
            "#(let z = (some Node => plus[3,4] else 0) | z) >= 7",
            false,
        ),
    ] {
        mt127_both(cell, &mt127_cell(body, "exactly 1 Node, 4 int"), sat);
    }
}

#[test]
fn part_f_if_then_else_takes_its_then_branch_raw_and_its_else_through_cint() {
    // `visit(ExprITE)`'s int arm is asymmetric (:788): the then branch is
    // `visitThis(x.left)` — its Kodkod class is what selected the arm, so it is
    // never coerced — while the else branch is `cint(x.right)`. c3 (then, no
    // unwrap: 1 >= 3) against s1 (else, unwrap: 7 >= 7) is the pair.
    for (cell, body, sat) in [
        ("c3", "(some Node => #(Int[3]) else 0) >= 3", false),
        ("y8", "(some Node => #(Int[3]) else 0) >= 1", true),
        ("s1", "(no Node => #(Int[1]) else #(plus[3,4])) >= 7", true),
        ("s2", "(no Node => #(Int[1]) else #(plus[3,4])) >= 2", true),
        // A NUMERAL then branch is `IntConstant.constant(n).toExpression()`
        // (:918) — an Expression — so THESE take the relational arm and the
        // else branch goes through `cset`, unwrapping nothing.
        ("c4", "(no Node => 0 else #(Int[3])) >= 3", false),
        ("y4", "(no Node => 0 else #(Int[3])) >= 1", true),
        ("y5", "(no Node => 0 else #(Int[3])) = 1", true),
        ("y9", "(no Node => 0 else #(plus[3,4])) >= 7", false),
        ("y1", "(no Node => 0 else 3) >= 3", true),
        ("y2", "(some Node => 3 else 0) >= 3", true),
    ] {
        mt127_both(cell, &mt127_cell(body, "exactly 1 Node, 4 int"), sat);
    }
}

#[test]
fn part_f_a_call_or_a_let_leaves_the_cast_bare_for_the_enclosing_cint() {
    // `visit(ExprCall)` and `visit(ExprLet)` are pass-throughs: they return
    // `visitThis(body)` unchanged, so the peephole belongs to the enclosing
    // `cint` and not to the inlining. Each `>=` row is unwrapped, each `=` row
    // is not — the same split as a1/a3, one indirection further in.
    for (cell, body, sat) in [
        ("b1", "#(three) >= 3", true),
        ("b2", "#(three) = 1", true),
        ("b3", "let z = Int[3] | #z >= 3", true),
        ("b4", "let z = Int[3] | #z = 1", true),
        ("b5", "let z = plus[3,4] | #z >= 7", true),
    ] {
        mt127_both(cell, &mt127_cell(body, "3 but 4 int"), sat);
    }
    mt127_both(
        "t7",
        &mt127_cell("#(let z = plus[3,4] | z) >= 7", "exactly 1 Node, 4 int"),
        true,
    );
}

#[test]
fn part_f_the_equality_gate_is_both_operands_cast() {
    // §10.7e FACT 1, exercised on shapes with no surface cast anywhere. Two
    // cardinalities both translate to `IntToExprCast` through `toSet`, so `=`
    // int-compares them and keeps the forbid-mode overflow guard; gw1/gw3 are
    // forbid-UNSAT for that reason at a bitwidth their cardinality exceeds,
    // while gw4/gw5/gw6 are ordinary in-range value cells.
    for (cell, body, scope, allow, forbid) in [
        (
            "gw1",
            "#A = #B",
            "exactly 5 A, exactly 5 B, 3 int",
            true,
            false,
        ),
        (
            "gw2",
            "#A in #B",
            "exactly 5 A, exactly 5 B, 3 int",
            true,
            false,
        ),
        (
            "gw3",
            "#A = #B",
            "exactly 2 A, exactly 2 B, 3 int",
            true,
            false,
        ),
        (
            "gw4",
            "#A = #B",
            "exactly 2 A, exactly 3 B, 3 int",
            false,
            false,
        ),
        (
            "gw5",
            "#A = 3",
            "exactly 3 A, exactly 0 B, 4 int",
            true,
            true,
        ),
        (
            "gw6",
            "#A = 2",
            "exactly 3 A, exactly 0 B, 4 int",
            false,
            false,
        ),
    ] {
        let src = mt127_gate_cell(body, scope);
        assert_eq!(solve(&src, true), Ok(allow), "{cell} allow");
        assert_eq!(solve(&src, false), Ok(forbid), "{cell} forbid");
    }

    // The both-literal-cast controls, plus the one-sided shape: with only ONE
    // side an `IntToExprCast` the jar set-compares, and `{7} = {7}` holds.
    let scope = "exactly 0 A, exactly 0 B, 4 int";
    for (cell, body, sat) in [
        ("e1", "Int[3] = Int[3]", true),
        ("e2", "Int[3] = Int[4]", false),
        ("e3", "plus[3,4] = 7", true),
        ("e4", "3 = 3", true),
        ("e5", "3 = 4", false),
        ("e10", "plus[3,4] = G.w", true),
        ("e11", "plus[3,3] = G.w", false),
    ] {
        mt127_both(cell, &mt127_gate_cell(body, scope), sat);
    }
    // An overflowing constant cast: forbid-UNSAT on BOTH the `=` and the `in`
    // path, so the guard does not tell the two readings apart here.
    for (cell, body) in [
        ("e6", "plus[7,1] = plus[7,1]"),
        ("e7", "plus[7,1] in plus[7,1]"),
    ] {
        let src = mt127_gate_cell(body, scope);
        assert_eq!(solve(&src, true), Ok(true), "{cell} allow");
        assert_eq!(solve(&src, false), Ok(false), "{cell} forbid");
    }
}

#[test]
fn part_f_the_corpus_shapes_the_unwrap_moves() {
    // mt-095's k8/k9/k10/k11/k12 — the same `#`/`int[·]` readers under the
    // part-C forall, where the cast can actually overflow. k10 and k12 are the
    // cells the unwrap closes: reading `plus[n,7]` raw carries its overflow
    // flag to the comparison, which the discarded cardinality never did. k8's
    // operand is an if-then-else and k9's a union, so neither unwraps.
    for (cell, body, allow, forbid) in [
        ("k10", "#(plus[n,7]) >= 0", false, false),
        ("k12", "int[plus[n,7]] >= 0", false, false),
        ("k8", "#(n>0 => plus[n,7] else 0) >= 0", true, false),
        ("k11", "#(plus[n,7]) = 0", false, false),
        ("k9", "#(plus[n,7] + 3) >= 0", true, true),
    ] {
        let src = part_e_cell(body);
        assert_eq!(solve(&src, true), Ok(allow), "{cell} allow");
        assert_eq!(solve(&src, false), Ok(forbid), "{cell} forbid");
    }
}

// ------- Part G: one classifier for `visitThis`'s Kodkod class (mt-128) -----
//
// Jar cells from `scratchpad/probe/mt128/` (`x3_verdicts.als` → `v*`,
// `x4_castsep.als` → `c*`, `x7_binders.als` → `y1`–`y6`, `x8_macro.als` →
// `y7`–`y10`; raw jar output in the matching `*_jar.txt`, resolved-AST evidence
// in `x1_ast_dump.txt` and `x2_positions_dump.txt`). Rule in translation-ref
// §10.7l. Jar-free: the expected verdicts are constants recorded from that wave.
//
// mt-095 read the if-then-else dispatch off the then branch and mt-052 read the
// evaluator console's render dispatch off a fragment's root. mt-128 measured
// that these are one question — which Kodkod class `visitThis` returns — and
// merged the two walks, which closed every cell below at once.

#[test]
fn part_g_a_cast_in_a_then_branch_is_a_set() {
    // The resolver re-wraps a source `int[e]` as `Int[int[e]]` in every position
    // that wants a relation, an if-then-else branch included
    // (`x2_positions_dump.txt`), so the branch translates to an `IntToExprCast`
    // — an `Expression` — and the if-then-else is relational. `#e` in the same
    // position is left bare and stays an `IntExpression`. Both carry Alloy type
    // `{Int}`, so nothing but the resolved AST tells them apart.
    for (cell, body, allow, forbid) in [
        (
            "v1/i8",
            "(n<=0 => int[F.v] else plus[n,7]) >= 0",
            false,
            true,
        ),
        ("y9", "(n<=0 => sum F.v else plus[n,7]) >= 0", false, true),
        (
            "i2 control",
            "(n<=0 => #Node else plus[n,7]) >= 0",
            false,
            false,
        ),
        // Nested: the inner if-then-else is relational because *its* then branch
        // is a cast, and the outer one inherits that class.
        (
            "y8",
            "(n<=0 => (n<=0 => int[F.v] else 0) else plus[n,7]) >= 0",
            false,
            true,
        ),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, true), Ok(allow), "{cell} allow");
        assert_eq!(solve(&src, false), Ok(forbid), "{cell} forbid");
    }
}

#[test]
fn part_g_a_written_int_cast_is_deleted_not_relational() {
    // `Int[e]` does not survive resolution: it is deleted and the coercion is
    // re-derived from context (mt-127's finding, `x1_ast_dump.txt` cmd[2]). So
    // `Int[#Node]` in a then branch leaves a bare `#`, and the if-then-else is
    // an **int** one — where classifying `Int[·]` as relational made it a set.
    for (cell, body, allow, forbid) in [
        (
            "v3",
            "(n<=0 => Int[#Node] else plus[n,7]) >= 0",
            false,
            false,
        ),
        ("v4", "(n<=0 => Int[0] else plus[n,7]) >= 0", false, true),
        (
            "v10",
            "(n<=0 => Int[int[F.v]] else plus[n,7]) >= 0",
            false,
            true,
        ),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, true), Ok(allow), "{cell} allow");
        assert_eq!(solve(&src, false), Ok(forbid), "{cell} forbid");
    }
}

#[test]
fn part_g_a_let_inside_the_then_branch_passes_its_class_through() {
    // `visit(ExprLet)` is `env.put(x.var, visitThis(x.expr))`
    // (`TranslateAlloyToKodkod.java:797`) — the value is stored RAW, so the
    // binding's class reaches the dispatch. The sort therefore cannot be read
    // before the binder is in scope, which is what made `let z = #Node | z`
    // relational.
    for (cell, body, allow, forbid) in [
        (
            "v2/i23",
            "(n<=0 => (let z = #Node | z) else plus[n,7]) >= 0",
            false,
            false,
        ),
        (
            "i22",
            "(n<=0 => (let z = 0 | z) else plus[n,7]) >= 0",
            false,
            true,
        ),
        (
            "v5",
            "(n<=0 => (let z = int[F.v] | z) else plus[n,7]) >= 0",
            false,
            true,
        ),
        (
            "v6",
            "(n<=0 => (let z = plus[3,4] | z) else plus[n,7]) >= 0",
            false,
            true,
        ),
        // Shadowing: the innermost binding of the name the body mentions wins.
        (
            "v7",
            "(n<=0 => (let z = 0 | let y = #Node | z) else plus[n,7]) >= 0",
            false,
            true,
        ),
        (
            "v8",
            "(n<=0 => (let z = #Node | let y = 0 | y) else plus[n,7]) >= 0",
            false,
            true,
        ),
    ] {
        let src = part_d_cell(body);
        assert_eq!(solve(&src, true), Ok(allow), "{cell} allow");
        assert_eq!(solve(&src, false), Ok(forbid), "{cell} forbid");
    }
}

/// The Part-G cell shape for a binder that **encloses** the if-then-else rather
/// than sitting inside it: an extra preamble declaration, and a body that is the
/// whole run formula. Matches `scratchpad/probe/mt128/x7_binders.als` and
/// `x8_macro.als` exactly.
fn part_g_binder_cell(preamble: &str, body: &str) -> String {
    format!(
        "open util/integer\n\
         sig Node {{}}\n\
         one sig F {{ v: one Int }}\n\
         fact FixV {{ F.v = 1 }}\n\
         {preamble}\n\
         run {{ {body} }} for 3 but 4 int\n"
    )
}

#[test]
fn part_g_a_substituting_binder_is_raw_and_a_parameter_is_coerced() {
    // The discriminating triple: the same `#Node` bound by a `let`, passed as a
    // func parameter, and passed as a `let`-macro argument. `visit(ExprLet)`
    // (`:797`) and the macro's syntactic substitution keep it an
    // `IntExpression`; `visit(ExprCall)` is
    // `newenv.put(f.get(i), cset(x.args.get(i)))` (`:1013`), which makes a
    // parameter an `Expression` however int-valued the argument was.
    let quant = "all n: {x: Int | x>=1 and x<=7} |";
    let sel = "fun sel[z: Int, n: Int]: Int { (n<=0 => z else plus[n,7]) }";
    let mac = "let sel[z, n] = (n<=0 => z else plus[n,7])";
    for (cell, preamble, body, allow, forbid) in [
        // A `let` outside the if-then-else: raw, so int-sorted.
        (
            "y1",
            "",
            format!("let z = #Node | {quant} (n<=0 => z else plus[n,7]) >= 0"),
            false,
            false,
        ),
        (
            "y2",
            "",
            format!("let z = 0 | {quant} (n<=0 => z else plus[n,7]) >= 0"),
            false,
            true,
        ),
        (
            "y3",
            "",
            format!("let z = int[F.v] | {quant} (n<=0 => z else plus[n,7]) >= 0"),
            false,
            true,
        ),
        // The same `#Node` as a func parameter: `cset`-ed, so relational.
        (
            "y4",
            sel,
            format!("{quant} sel[#Node, n] >= 0"),
            false,
            true,
        ),
        ("y5", sel, format!("{quant} sel[0, n] >= 0"), false, true),
        // ... and as a `let`-macro argument: substituted, so raw again.
        (
            "y7",
            mac,
            format!("{quant} sel[#Node, n] >= 0"),
            false,
            false,
        ),
        ("y10", mac, format!("{quant} sel[0, n] >= 0"), false, true),
    ] {
        let src = part_g_binder_cell(preamble, &body);
        assert_eq!(solve(&src, true), Ok(allow), "{cell} allow");
        assert_eq!(solve(&src, false), Ok(forbid), "{cell} forbid");
    }
}

#[test]
fn part_g_a_multiplicity_test_can_see_an_overflowed_cast() {
    // mt-127 left the resolver's cast on a `some`/`no`/`one`/`lone`/`&` operand
    // unmodelled because no cell then separated the readings. These do: at
    // `exactly 8 Node` with bitwidth 4 the cardinality is out of −8..7, and
    // under `noOverflow` the cast around it is empty (§10.7e FACT 2), which a
    // multiplicity test observes directly. mettle already agreed on all eight —
    // `lower_rel` re-inserts the cast in exactly the positions the resolver
    // does — so this test is here to keep that true, not to record a fix.
    for (cell, body, nodes, allow, forbid) in [
        ("c1", "some (#Node)", 8, true, false),
        ("c2", "no (#Node)", 8, false, false),
        ("c3", "one (#Node)", 8, true, false),
        ("c4", "lone (#Node)", 8, true, true),
        ("c5", "some ((#Node) & Int)", 8, true, false),
        ("c7", "no ((#Node) & Int)", 8, false, false),
        ("c8", "some ((#Node) + 1)", 8, true, true),
        // In range, nothing overflows and the cast is a singleton either way.
        ("c6", "some (#Node)", 7, true, true),
    ] {
        let src = format!("sig Node {{}}\nrun {{ {body} }} for exactly {nodes} Node, 4 int\n");
        assert_eq!(solve(&src, true), Ok(allow), "{cell} allow");
        assert_eq!(solve(&src, false), Ok(forbid), "{cell} forbid");
    }
}
