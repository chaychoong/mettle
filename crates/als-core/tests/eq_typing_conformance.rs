//! Integer-equality typing conformance (mt-051): jar-pinned verdicts for the
//! ONE-SIDED `Int[·]`-cast shape at `=`/`in`/multiplicity-tests — the rule that
//! retired the old `eq_typing_defer`. Each row is a probe cell from
//! `scratchpad/probe/ProbeEqTyping*.java` (labels preserved); the expected
//! verdicts are the jar's (Alloy 6.2.0), recorded as constants so CI runs with no
//! oracle (translation-ref §10.7c ext).
//!
//! The pinned rule has three parts (see `overflow_guard.rs`): (A) an overflowed
//! overflow-capable cast denotes the EMPTY set in forbid mode, in every context;
//! (B) each capable cast reachable through the compared sides' set structure
//! threads the §10.7c rules 0–3 polarity guard; (C) a translation-constant cast
//! contributes no (B) guard (its (A) value already governs).
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

// ---------------------------- (C) the constant escape -----------------------

#[test]
fn constant_escape_trio() {
    // A translation-constant cast contributes NO (B) guard, while its (A) value
    // still applies (probe R-cardun/T5/T6). All three use `#pid`/`#priority` over
    // exactly-bound sigs — fully constant translations.

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
    // j5: a ground variable mixed with such a relation. j6/j7: an exactly-bound
    // vs a merely-constrained cardinality — mettle's own `translation_constant`
    // predicate separates exactly these two, and the jar does not.
    // j9: only some bindings overflow, so the escape is per-binding.
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
// override and a product. Only the UNION sheds, and only sometimes — see the
// `#[ignore]`d pin at the end for why no implementable rule was found.
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

    // t4e — the same expression under the part-C forall is jar forbid **SAT**.
    // mettle answers UNSAT (it keeps guarding); that divergence is the pinned
    // union corner, see `part_e_union_sheds_under_a_quantifier_in_the_jar`.
    let quant = part_e_cell("(plus[n,7] + 1) in Int");
    assert_eq!(solve(&quant, true), Ok(true), "t4e allow");
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
#[ignore = "mt-096 PINNED: a union-nested cast under a quantifier sheds the \
            jar's comparison guard, but no IR-level predicate separates the \
            shedding cells (u1/u10/v6/v7/v8/v9) from the guarding ones \
            (t4c/t4b with no quantifier, u11/v3 with two capable operands, v1 \
            with a sibling that cannot overflow) — translation-ref §10.7h"]
fn part_e_union_sheds_under_a_quantifier_in_the_jar() {
    // Jar verdicts pinned at mt-096. All forbid **SAT**: under the part-C
    // forall, a union whose sibling carries no capable cast sheds the guard.
    // mettle keeps descending through the union and answers UNSAT — the
    // CONSERVATIVE direction (it never turns a jar UNSAT into a mettle SAT).
    //
    // Closing this needs a rule that also explains `part_e_union_guard_survives
    // _without_a_quantifier` (same union shape, jar UNSAT) and
    // `part_e_a_union_of_two_capable_casts_guards`. mt-096 tried three and each
    // was refuted by a cell; the corner is recorded, not guessed at.
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
