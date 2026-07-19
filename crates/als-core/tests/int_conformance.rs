//! Integer-fidelity conformance (mt-044): jar-pinned verdicts for the LEDGER-001
//! / LEDGER-005 / LEDGER-006 rows — arithmetic values, div/rem sign + edge cases,
//! the forbid-mode overflow polarity rule (the universal-rescue case I11), and
//! cardinality overflow. Jar-free: each expected verdict is a constant citing its
//! probe row (translation-ref §10.7/§10.7b), so CI runs it with no oracle.
//!
//! Negative integer literals are spelled `negate[k]` (genuine `util/integer`
//! arithmetic), never `(0-k)` — the raw hyphen is relational set-difference and
//! `(0-5)` silently means the atom `0` (§10.7b harness finding). The one
//! exception, the `(0-8)` = MIN peephole, is not exercised here.

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Solve command 0 of `src` under the given overflow mode; `Ok(true)` = SAT,
/// `Ok(false)` = UNSAT, `Err` = a typed defer (lowering/encoding could not
/// proceed — used for the mixed-nesting negative-space rows).
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

/// A ground equality `run { EXPR = VAL }` is SAT iff the arithmetic evaluates to
/// `VAL` (allow mode — the §10.7b tables are allow-mode values).
fn allows(src: &str) -> bool {
    solve(src, true).expect("no defer expected in allow mode")
}

// ------------------------------- arithmetic values (allow, §10.7b) ----------

#[test]
fn div_truncates_toward_zero() {
    // I1/I2: div[-5,2]=-2, div[5,-2]=-2, div[-5,-2]=2.
    assert!(allows("run { div[negate[5], 2] = negate[2] }\n"));
    assert!(!allows("run { div[negate[5], 2] = negate[3] }\n"));
    assert!(allows("run { div[5, negate[2]] = negate[2] }\n"));
    assert!(allows("run { div[negate[5], negate[2]] = 2 }\n"));
}

#[test]
fn rem_takes_sign_of_dividend() {
    // I3: rem[-5,2]=-1, rem[5,-2]=1.
    assert!(allows("run { rem[negate[5], 2] = negate[1] }\n"));
    assert!(allows("run { rem[5, negate[2]] = 1 }\n"));
}

#[test]
fn add_mul_wrap_two_complement() {
    // I5: plus[7,7]=-2, mul[3,3]=-7.
    assert!(allows("run { plus[7, 7] = negate[2] }\n"));
    assert!(allows("run { mul[3, 3] = negate[7] }\n"));
}

#[test]
fn shifts_match_kodkod() {
    // I4: 4<<1=8, (-8)>>1(sha)=-4, (-8)>>>1(shr)=4.
    // `<<`, `>>`, `>>>` are surface operators; spell MIN via negate[8].
    assert!(allows("run { (4 << 1) = 8 }\n"));
    assert!(allows("run { (negate[8] >> 1) = negate[4] }\n"));
    assert!(allows("run { (negate[8] >>> 1) = 4 }\n"));
}

#[test]
fn div_rem_by_zero_edge_values() {
    // §10.7b closed form: div[x,0] = -sign(x); rem[x,0] = x.
    assert!(allows("run { div[5, 0] = negate[1] }\n")); // I6: x>0 → -1
    assert!(allows("run { div[negate[5], 0] = 1 }\n")); // x<0 → 1
    assert!(allows("run { div[0, 0] = 0 }\n")); // x=0 → 0
    assert!(allows("run { div[negate[8], 0] = 1 }\n")); // MIN, no special case
    assert!(allows("run { rem[5, 0] = 5 }\n")); // I7
    assert!(allows("run { rem[negate[8], 0] = negate[8] }\n"));
}

#[test]
fn min_over_minus_one_wraps_to_min() {
    // §10.7b correction: div[MIN,-1] = MIN (two's-complement division overflow).
    assert!(allows("run { div[negate[8], negate[1]] = negate[8] }\n"));
    assert!(!allows("run { div[negate[8], negate[1]] = 1 }\n"));
    assert!(allows("run { rem[negate[8], negate[1]] = 0 }\n"));
}

#[test]
fn builtin_min_max_next_prev() {
    // I14/I15: min=-8, max=7; 3.next=4, 3.prev=2; chain endpoints empty.
    assert!(allows("run { min = negate[8] }\n"));
    assert!(allows("run { max = 7 }\n"));
    assert!(allows("run { 3.next = 4 }\n"));
    assert!(allows("run { 3.prev = 2 }\n"));
    assert!(!allows("run { 7.next = 7 }\n")); // endpoint: 7.next empty ≠ {7}
    assert!(!allows("run { negate[8].prev = negate[8] }\n"));
}

// ------------------------------- overflow polarity (LEDGER-001/005) ---------

#[test]
fn i9_positive_existential_overflow_excluded() {
    // plus[7,7] < 0: allow SAT (-2 < 0), forbid UNSAT (the overflowing witness
    // is excluded — the LEDGER-001 decisive test).
    assert_eq!(solve("run { plus[7, 7] < 0 }\n", true), Ok(true));
    assert_eq!(solve("run { plus[7, 7] < 0 }\n", false), Ok(false));
}

#[test]
fn i11_universal_position_overflow_rescues() {
    // all n: Int | plus[n,7] >= n: allow UNSAT (fails at n=7), forbid SAT — the
    // universal-position rescue a flat `∧ ¬overflow` gets wrong (§11.3).
    let src = "run { all n: Int | plus[n, 7] >= n }\n";
    assert_eq!(solve(src, true), Ok(false));
    assert_eq!(solve(src, false), Ok(true));
}

#[test]
fn i10_div_by_zero_excluded_in_forbid() {
    // Reflexive div-by-zero / MIN÷−1 / rem-by-zero set overflow, so each is
    // excluded at positive polarity in forbid mode; a clean div is SAT control.
    // (`negate[8]` is used for MIN: mettle has no `(0-8)→MIN` peephole, so
    // `(0-8)` is the atom 0 here — the exclusion still holds, whether via the
    // MIN÷−1 overflow or `negate[8]`'s own flag; both give the pinned UNSAT.)
    assert_eq!(solve("run { div[5, 0] = div[5, 0] }\n", false), Ok(false));
    assert_eq!(
        solve(
            "run { div[negate[8], negate[1]] = div[negate[8], negate[1]] }\n",
            false
        ),
        Ok(false)
    );
    assert_eq!(solve("run { rem[5, 0] = rem[5, 0] }\n", false), Ok(false));
    assert_eq!(solve("run { div[5, 2] = div[5, 2] }\n", false), Ok(true));
}

// ------------------------------- cardinality overflow (LEDGER-006) ----------

#[test]
fn i12_cardinality_overflow() {
    // #A = 8 for exactly 8 A: allow SAT (count 8 wraps to -8, =8 ≡ =-8),
    // forbid UNSAT (the count overflow is excluded).
    let src = "sig A {}\nrun { #A = 8 } for exactly 8 A\n";
    assert_eq!(solve(src, true), Ok(true));
    assert_eq!(solve(src, false), Ok(false));
}

#[test]
fn i13_cardinality_overflow_gt() {
    // #A > 0 for exactly 8 A: allow UNSAT (count wraps to -8, -8>0 false),
    // forbid UNSAT (count overflow excluded). #A = 7 for 7 A forbid SAT control.
    let src = "sig A {}\nrun { #A > 0 } for exactly 8 A\n";
    assert_eq!(solve(src, true), Ok(false));
    assert_eq!(solve(src, false), Ok(false));
    assert_eq!(
        solve("sig A {}\nrun { #A = 7 } for exactly 7 A\n", false),
        Ok(true)
    );
}

// ------------------------------- rule 0: non-bare-Int ∀ (§10.7c GAP2) --------

#[test]
fn gap2a_sig_universal_excludes_not_rescues() {
    // `all p: P | plus[#p.f,7] >= #p.f`, with `some f` forcing a nonempty field:
    // the overflow-driver `p` is bound over a **sig**, not bare `Int`, so the jar
    // misclassifies it existential and EXCLUDES the overflowing binding
    // (forbid UNSAT) rather than rescuing (§10.7c rule 0 / GAP2a). The naive
    // §11.3 rule would wrongly predict SAT here.
    let src =
        "sig P { f: set P }\nfact { some f }\nrun { all p: P | plus[#p.f, 7] >= #p.f } for 3\n";
    assert_eq!(solve(src, false), Ok(false)); // sig-∀ excludes → UNSAT
}

#[test]
fn gap2b_bare_int_universal_rescues() {
    // Control: the identical arithmetic shape driven by a bare-`Int` `∀` IS
    // rescued (forbid SAT), isolating the sig domain — not the arithmetic — as
    // rule 0's cause (§10.7c GAP2b).
    let src = "run { all m: Int | plus[m, 7] >= m } for 3\n";
    assert_eq!(solve(src, true), Ok(false)); // allow: fails at m=7
    assert_eq!(solve(src, false), Ok(true)); // bare-Int ∀ rescues → SAT
}

// ------------------------ mixed-type bare-Int nesting (§10.7c, GAP1a-family) --

#[test]
fn mixed_type_bare_int_nesting_solves() {
    // ∀∃ over bare `Int` with an overflow-capable int COMPARISON: "Defect B" is
    // retracted (§10.7c/§10.7d — the apparent nesting-position anomaly was a
    // `negate[8]` domain-emptying confound). The single per-variable rule applies:
    // `m` is a bare-`Int` ∃ → classified existential → the overflowing witness is
    // excluded, so the guard fires and the command SOLVES (no defer). This is the
    // GAP1a family via inequality (one-sided relational `=` stays deferred by the
    // eq-typing fixup, so pin it with `<`).
    //
    // The load-bearing pinned behaviour is that this SOLVES (no defer) in both
    // modes — the per-variable rule applies in mixed nesting, no special case.
    // The exact SAT/UNSAT of the `<` form is not itself a jar-pinned cell (GAP1a
    // pins the `=` form, which the eq-typing fixup defers), so it is left to the
    // encoder↔evaluator differential and the solve-gauge to check for jar-agreement.
    let src = "run { all n: Int | some m: Int | plus[m, 7] < n }\n";
    assert!(solve(src, true).is_ok()); // allow: solves
    assert!(solve(src, false).is_ok()); // forbid: solves (no defer — Defect B lifted)
}

// ------------------- integer-equality typing defer (§10.7c GAP1a) -----------

#[test]
fn arith_eq_plain_int_defers_in_forbid_only() {
    // `plus[X.v,7] = X.v`: an arithmetic `Int[·]` cast compared to a plain
    // `Int`-typed field. The jar int-compares this (guard fires); mettle would
    // lower it as relational equality (guard skipped), so — since that shape is
    // jar-pinned (§10.7c GAP1a) — forbid mode typed-defers rather than answer
    // allow-style. Allow mode stays relational (wrapped-value equality is exact).
    let src = "one sig X { v: one Int }\nrun { plus[X.v, 7] = X.v } for 1\n";
    assert_eq!(solve(src, false), Err(())); // forbid: typed defer
    assert!(solve(src, true).is_ok()); // allow: solves relationally

    // GAP1a's exact shape — nested, over bare `Int`.
    let gap1a = "run { all n: Int | some m: Int | plus[m, 7] = n }\n";
    assert_eq!(solve(gap1a, false), Err(()));
    assert!(solve(gap1a, true).is_ok());
}

#[test]
fn both_cast_equality_still_solves_both_modes() {
    // `div[5,0] = div[5,0]`: BOTH sides are `Int[·]` casts, so the pinned I10
    // both-cast peephole makes it an integer comparison (guard fires) — it is NOT
    // the GAP1a shape and must still solve (forbid UNSAT via div-by-zero, allow
    // SAT since the value equals itself).
    assert_eq!(solve("run { div[5, 0] = div[5, 0] }\n", false), Ok(false));
    assert_eq!(solve("run { div[5, 0] = div[5, 0] }\n", true), Ok(true));
}

#[test]
fn same_type_nesting_solves() {
    // ∀∀ (same-type) with an overflow-capable comparison solves in both modes —
    // `m` is a bare-`Int` ∀ driver → rescued, no defer (§10.7c rule 0/2).
    let src = "run { all n: Int | all m: Int | plus[m, 7] < n }\n";
    assert!(solve(src, false).is_ok());
    assert!(solve(src, true).is_ok());
}

// ------------------------------- shift semantics (§10.7d) -------------------

#[test]
fn shift_mask_and_junk_bit_overflow() {
    // §10.7d FACT 1 — only the low ⌈log2 w⌉ amount bits affect the value, so a
    // masked-away amount leaves the value unchanged (allow-mode value checks).
    assert!(allows("run { (1 << 4) = 1 }\n")); // bw4 mask 2: 4&3=0 → 1<<0
    assert!(allows("run { (5 << 4) = 5 }\n"));
    assert!(allows("run { (1 << 8) = 1 } for 3 but 5 int\n")); // bw5 mask 3: 8&7=0
    assert!(allows("run { (1 << 4) = 1 } for 3 but 3 int\n")); // bw3 mask 2

    // §10.7d FACT 2 — `<<`'s junk-bit overflow: a masked-away set amount bit still
    // flags overflow when the shiftee's bit pattern has a transition in the
    // inspected region. So `5<<4`/`3<<4`/`1<<4` (value unchanged) are forbid-UNSAT
    // (spurious overflow excludes), while `0<<4` (uniform pattern, no transition)
    // is forbid-SAT.
    assert_eq!(solve("run { (5 << 4) = 5 }\n", false), Ok(false));
    assert_eq!(solve("run { (3 << 4) = 3 }\n", false), Ok(false));
    assert_eq!(solve("run { (1 << 4) = 1 }\n", false), Ok(false));
    assert_eq!(solve("run { (0 << 4) = 0 }\n", false), Ok(true));

    // A genuine wrap sets `<<` overflow too: 4<<1 = 8 wraps to −8.
    assert_eq!(solve("run { (4 << 1) < 0 }\n", true), Ok(true)); // allow: −8 < 0
    assert_eq!(solve("run { (4 << 1) < 0 }\n", false), Ok(false)); // forbid: excluded

    // bw6: 6 is within the 3-bit mask window, so 1<<6 shifts fully out of a 6-bit
    // register — genuine overflow (allow SAT value 0, forbid UNSAT).
    assert_eq!(
        solve("run { (1 << 6) = 0 } for 3 but 6 int\n", true),
        Ok(true)
    );
    assert_eq!(
        solve("run { (1 << 6) = 0 } for 3 but 6 int\n", false),
        Ok(false)
    );
}

#[test]
fn right_shifts_never_self_overflow() {
    // §10.7d FACT 2 — `>>` (sha) and `>>>` (shr) have their own overflow bit
    // hardcoded FALSE, so these solve in **forbid** mode (no self-overflow to
    // exclude). Clean spellings only: `negate[1]` (=−1) is overflow-free.
    assert_eq!(solve("run { (1 >>> 1) = 0 }\n", false), Ok(true));
    assert_eq!(solve("run { (1 >> 1) = 0 }\n", false), Ok(true));
    assert_eq!(solve("run { (3 >>> 3) = 0 }\n", false), Ok(true));
    // −1 arithmetic-right-shifted keeps −1 (sign-fill), no overflow → forbid SAT.
    assert_eq!(
        solve("run { (negate[1] >> 1) = negate[1] }\n", false),
        Ok(true)
    );
}
