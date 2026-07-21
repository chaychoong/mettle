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
//! contributes no (B) guard (its (A) value already governs). Rule 4 (the int-ITE /
//! `implies`-antecedent sliver) is now pinned to rescue.
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

// ---------------------------- Part C: rule-4 sliver (int-compare path) -------

#[test]
fn part_c_ite_and_implies_antecedent_rescue() {
    // The int-compare path is UNCHANGED except rule 4 is now pinned (mt-051): a
    // non-bare-Int ∀ driver reached through an int-ITE branch or an `implies`
    // ANTECEDENT behaves as correctly classified (rescue); consequents and bare
    // negation get ordinary Defect-A exclusion. Domain `{x:Int|x>=1 and x<=7}`
    // (non-bare-Int), `for 3 but 4 int`. Probe Part C.
    let dom = "{x: Int | x>=1 and x<=7}";
    let cell = |body: &str| {
        format!("open util/integer\nrun {{ all n: {dom} | {body} }} for 3 but 4 int\n")
    };

    // Direct-ctl: no wrapper — Defect-A exclude fires → UNSAT/UNSAT.
    let direct = cell("plus[n,7] >= 0");
    assert_eq!(solve(&direct, true), Ok(false));
    assert_eq!(solve(&direct, false), Ok(false));

    // ITE-P12 / real1 / real2 / both: the escape fires regardless of vacuity,
    // branch position, or both branches carrying arithmetic → UNSAT/SAT.
    for body in [
        "(n>0 => plus[n,7] else 0) >= 0",
        "(n>3 => plus[n,7] else 5) >= 0",
        "(n<=3 => 5 else plus[n,7]) >= 0",
        "(n>3 => plus[n,7] else plus[n,1]) >= 0",
    ] {
        let src = cell(body);
        assert_eq!(solve(&src, true), Ok(false), "allow {body}");
        assert_eq!(solve(&src, false), Ok(true), "forbid {body}");
    }

    // IMP-P9 / IMP-nested: arithmetic in the `implies` ANTECEDENT escapes →
    // UNSAT/SAT.
    for body in [
        "(plus[n,7]<0 implies (1=0))",
        "(n>=1 implies (plus[n,7]<0 implies (1=0)))",
    ] {
        let src = cell(body);
        assert_eq!(solve(&src, true), Ok(false), "allow {body}");
        assert_eq!(solve(&src, false), Ok(true), "forbid {body}");
    }

    // IMP-conseq: arithmetic in the CONSEQUENT gets ordinary exclusion →
    // UNSAT/UNSAT.
    let conseq = cell("(n>3 implies plus[n,7]>=0)");
    assert_eq!(solve(&conseq, true), Ok(false));
    assert_eq!(solve(&conseq, false), Ok(false));

    // AND-ctl: `and` (not `implies`) does not flip polarity → ordinary exclusion →
    // UNSAT/UNSAT.
    let and_ctl = cell("(n>=1 and plus[n,7]>=0)");
    assert_eq!(solve(&and_ctl, true), Ok(false));
    assert_eq!(solve(&and_ctl, false), Ok(false));

    // V-not: a bare `!` is NOT an escape context (the boundary that pins the
    // escape to ITE + implies-antecedent) → UNSAT/UNSAT.
    let v_not = cell("!(plus[n,7] < 0)");
    assert_eq!(solve(&v_not, true), Ok(false));
    assert_eq!(solve(&v_not, false), Ok(false));
}
