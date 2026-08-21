//! The bare out-of-range integer literal (mt-101): jar-pinned verdicts for the
//! forbid-mode overflow flag a numeral outside the bitwidth range raises.
//!
//! Rule: translation-ref §10.7k. Alloy's `visit(ExprConstant)` raises nothing —
//! the flag comes from Kodkod, where an out-of-range `IntConstant`'s
//! `accumOverflow` is the **constant TRUE** and `DefCond.ensureDef` folds the
//! enclosing comparison to `and(value, not(TRUE))`. Two layers follow, exactly
//! as §10.7e pinned them for casts:
//!
//! - **(A) value** — in forbid mode the literal's cast denotes the EMPTY set.
//!   Implemented at mt-101; this file's live tests pin it.
//! - **(B) comparison-level guard** — pinned open, NOT implemented. Reproducing
//!   it faithfully needs a constant-empty analysis (a union folds a
//!   constant-empty operand away, taking its `DefCond`; `none + 8` does not),
//!   and implementing it naively over-guards 41 otherwise-agreeing cells. The
//!   `#[ignore]`d tests at the bottom carry those jar verdicts so the gap stays
//!   measured rather than forgotten.
//!
//! Cells come from `scratchpad/probe/mt101/` (`m1.als` → the former × reader
//! grid whose readers are layer-(A)-sensitive, `m3.als` → the layer-(B)-isolating
//! grid, `m4.als` → the bitwidth/union stress, `oor.als` → mt-052's banked
//! g01–g07). Expected verdicts are the jar's (Alloy 6.2.0, sat4j, symmetry 0,
//! both `noOverflow` settings), recorded as constants so CI runs with no oracle.

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

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

/// The signature of an overflow flag reaching a reader: satisfiable when
/// overflow is allowed to wrap, excluded when it is forbidden. An allow-mode
/// UNSAT would mean the cell never discriminated in the first place.
#[track_caller]
fn splits(src: &str, cell: &str) {
    assert_eq!(solve(src, true), Ok(true), "{cell} (allow)");
    assert_eq!(solve(src, false), Ok(false), "{cell} (forbid)");
}

/// No flag anywhere: the same verdict in both modes.
#[track_caller]
fn agrees(src: &str, want: bool, cell: &str) {
    assert_eq!(solve(src, true), Ok(want), "{cell} (allow)");
    assert_eq!(solve(src, false), Ok(want), "{cell} (forbid)");
}

const H: &str = "sig H { u: set Int }\nfact { one H }\n";

// ---- (A) the literal's cast is EMPTY in forbid mode -------------------------

#[test]
fn oor_literal_cast_is_empty_in_forbid_mode() {
    // L1/L2/L5 (m3.als): the decisive pair. `0 + 8` is `{0, -8}` when overflow
    // wraps and exactly `{0}` when it is forbidden — so the union's cardinality
    // is 2 in allow mode and 1 in forbid mode, and the in-range twin is 2 in
    // both. L1 reads the same fact from the other side (`H.u = 0` becomes
    // satisfiable only once the literal has emptied).
    assert_eq!(
        solve(
            &format!("{H}run {{ H.u = (0 + 8) and H.u = 0 }} for 3 but 4 int\n"),
            true
        ),
        Ok(false),
        "L1 (allow)"
    );
    assert_eq!(
        solve(
            &format!("{H}run {{ H.u = (0 + 8) and H.u = 0 }} for 3 but 4 int\n"),
            false
        ),
        Ok(true),
        "L1 (forbid)"
    );
    splits(
        &format!("{H}run {{ H.u = (0 + 8) and #H.u = 2 }} for 3 but 4 int\n"),
        "L2",
    );
    agrees(
        &format!("{H}run {{ H.u = (0 + 7) and #H.u = 2 }} for 3 but 4 int\n"),
        true,
        "L5 in-range control",
    );
}

#[test]
fn oor_literal_excludes_readers_that_are_false_on_the_empty_set() {
    // m1 f01/f05/f07 × the layer-(A)-sensitive readers. Each of these is TRUE on
    // the wrapped value `{-8}` and FALSE on `∅`, so forbidding overflow excludes
    // the instance — and this is the half mt-101 implemented.
    splits(&format!("{H}run {{ 8 = min }} for 3 but 4 int\n"), "f01/ra");
    splits(&format!("{H}run {{ some 8 }} for 3 but 4 int\n"), "f01/rc");
    splits(
        &format!("{H}run {{ #(8) = 1 }} for 3 but 4 int\n"),
        "f01/re",
    );
    splits(
        &format!("{H}run {{ not (no 8) }} for 3 but 4 int\n"),
        "f01/rg",
    );
    // The flag survives the set formers that keep it, and the indirections
    // mt-100 made lowerable.
    splits(
        &format!("{H}run {{ some (Int & 8) }} for 3 but 4 int\n"),
        "f05/rc",
    );
    splits(
        &format!("{H}run {{ some {{x: Int | x = 8}} }} for 3 but 4 int\n"),
        "f07/rc",
    );
    splits(
        &format!("{H}run {{ (let k = 8 | k) = min }} for 3 but 4 int\n"),
        "f12/ra",
    );
    splits(
        &format!("{H}let mm = 8\nrun {{ mm = min }} for 3 but 4 int\n"),
        "f13/ra macro body",
    );
    splits(
        &format!("{H}fun ff: Int {{ 8 }}\nrun {{ ff = min }} for 3 but 4 int\n"),
        "f14/ra fun body",
    );
}

#[test]
fn oor_literal_guards_a_both_cast_int_comparison() {
    // mt-052's banked g01/g05/g04, now agreeing. `8 = 8` is a both-cast int
    // comparison (§10.7e FACT 1), so the flag reaches the guard mettle already
    // had; g04 is layer (A) instead (`#∅ = 0 ≠ 1`). g06 is the in-range control.
    splits("run { 8 = 8 } for 3 but 4 int\n", "g01");
    splits("run { 9 = 9 } for 3 but 4 int\n", "g05");
    splits("run { #(8) = 1 } for 3 but 4 int\n", "g04");
    agrees(
        "run { 7 = 7 } for 3 but 4 int\n",
        true,
        "g06 in-range control",
    );
}

#[test]
fn the_trigger_is_the_command_bitwidth() {
    // m4 b01..b10: purely `n < min(bw) || n > max(bw)`, re-read per command. The
    // same numeral is a flag at one bitwidth and an ordinary atom at another.
    agrees(
        "run { 8 = 8 } for 3 but 5 int\n",
        true,
        "b01 8 in range at bw 5",
    );
    splits(
        "run { 8 = 8 } for 3 but 3 int\n",
        "b02 8 out of range at bw 3",
    );
    splits(
        "run { 16 = 16 } for 3 but 5 int\n",
        "b05 16 out of range at bw 5",
    );
    agrees(
        "run { 16 = 16 } for 3 but 6 int\n",
        true,
        "b06 16 in range at bw 6",
    );
    splits(
        "run { 15 = 15 } for 3 but 4 int\n",
        "b07 15 out of range at bw 4",
    );
    agrees(
        "run { 7 = 7 } for 3 but 4 int\n",
        true,
        "b08 in-range control",
    );
}

// ---- negative space: the shed families mettle must NOT start guarding -------

#[test]
fn a_union_sibling_and_a_comprehension_shed_the_flag() {
    // m3 f03/f07/f16/f17/f19 and m4 u01/u02/u06/u07: a union whose other operand
    // is a non-empty, non-overflowing set folds the constant-empty cast away —
    // guard and all — and the shed is PERMANENT (m5 s01–s06: wrapping the union
    // in a difference, a join, `#` or a field equality does not bring it back).
    // These are jar SAT in BOTH modes and mettle must agree; the (B) work that
    // was backed out at mt-101 broke exactly this family.
    agrees(
        &format!("{H}run {{ (0 + 8) in Int }} for 3 but 4 int\n"),
        true,
        "f03/rb",
    );
    agrees(
        &format!("{H}run {{ H.u = (0 + 8) }} for 3 but 4 int\n"),
        true,
        "f03/rf (mt-052 g03)",
    );
    agrees(
        &format!("{H}run {{ (7 + 8) in Int }} for 3 but 4 int\n"),
        true,
        "f16/rb",
    );
    agrees(
        &format!("{H}run {{ ((0 + 8) & Int) in Int }} for 3 but 4 int\n"),
        true,
        "f19/rb nested union",
    );
    agrees(
        &format!("{H}run {{ ((0 + 8) - 0) in Int }} for 3 but 4 int\n"),
        true,
        "s01 shed persists through a difference",
    );
    agrees(
        &format!("{H}run {{ {{x: Int | x in 8}} in Int }} for 3 but 4 int\n"),
        true,
        "f25 comprehension body",
    );
    // …and the readers that shed regardless of the former.
    agrees(
        &format!("{H}run {{ lone 8 }} for 3 but 4 int\n"),
        true,
        "f01/rd `lone`",
    );
    agrees(
        &format!("{H}run {{ all x: 8 | x != 5 }} for 3 but 4 int\n"),
        true,
        "f01/rk quantifier decl bound",
    );
}

#[test]
fn an_in_range_literal_never_raises_a_flag() {
    // The m2 control grid in miniature: 102/102 of its discriminating cells are
    // forbid-SAT, which is what makes every forbid-UNSAT above the literal's.
    for (cell, expr) in [
        ("bare", "7 = 7"),
        ("union", "(0 + 7) in Int"),
        ("inter", "some (Int & 7)"),
        ("card", "#(7) = 1"),
        ("compr", "some {x: Int | x = 7}"),
        ("min edge", "(0-8) = min"),
    ] {
        agrees(
            &format!("{H}run {{ {expr} }} for 3 but 4 int\n"),
            true,
            cell,
        );
    }
}

// ---- the pinned-open remainder (§10.7k layer (B)) ---------------------------

#[test]
#[ignore = "mt-101 layer (B): pinned open — mettle over-accepts, see translation-ref §10.7k"]
fn part_b_set_level_readers_guard_in_the_jar() {
    // The honest gap. Every cell below is jar forbid-UNSAT and mettle forbid-SAT:
    // the reader is TRUE on `∅`, so layer (A) cannot reach it and only the (B)
    // comparison-level guard would. Implementing (B) for constant sources needs
    // a constant-empty analysis (a union sheds, but `none + 8` does NOT), which
    // mt-101 measured, costed at 41 new over-guarding cells, and backed out.
    splits(
        &format!("{H}run {{ H.u = 8 }} for 3 but 4 int\n"),
        "g02 — jar UNSAT, mettle SAT",
    );
    splits(
        &format!("{H}run {{ no (0 & 8) }} for 3 but 4 int\n"),
        "g07 — jar UNSAT, mettle SAT",
    );
    splits(
        &format!("{H}run {{ 8 in Int }} for 3 but 4 int\n"),
        "f01/rb — jar UNSAT, mettle SAT",
    );
    splits(
        &format!("{H}run {{ (8 + 8) in Int }} for 3 but 4 int\n"),
        "f04/rb union of two out-of-range — jar UNSAT, mettle SAT",
    );
    splits(
        &format!("{H}run {{ (none + 8) in Int }} for 3 but 4 int\n"),
        "u08 constant-empty sibling — jar UNSAT, mettle SAT",
    );
}

#[test]
#[ignore = "mt-101 also-found: the `#`/`sum` operand corner, wider than §10.7e's wording"]
fn part_b_card_operand_guards_in_the_jar_for_every_source_kind() {
    // m8 w07/w08: `#(X) <= 1` is jar forbid-UNSAT for a literal, a constant cast
    // AND a variable cast alike, so this is not a constant-ness effect — it is
    // the documented "cast nested inside a Card operand" corner, and it accounts
    // for the 16 `ri_cardle` cells in the mt-101 residual.
    splits(
        &format!("{H}run {{ #(8) <= 1 }} for 3 but 4 int\n"),
        "w08 literal",
    );
    splits(
        &format!("{H}one sig F {{ v: Int }}\nfact {{ F.v = 7 }}\nrun {{ #(plus[F.v,1]) <= 1 }} for 3 but 4 int\n"),
        "w07 variable cast",
    );
}
