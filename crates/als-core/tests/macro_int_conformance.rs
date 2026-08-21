//! Module-level macros in **integer** position (mt-100): jar-pinned verdicts for
//! the `integer-position name` / `integer-position spine` defers — every macro
//! whose *body* is `Int`-sorted (`#A`, a bare numeral, the `0-(max+1)` fold,
//! `plus[…]` through a parameter).
//!
//! Rule: translation-ref §10.7j. A macro use is inlined **before** translation,
//! so the body's own translated class is what the surrounding context sees;
//! integer position is no exception. Cells come from `scratchpad/probe/mt100/`
//! (`named.als` → `a*`, `factpos.als` → `f*`, `fold.als` → `b*`,
//! `param.als` → `c*`, `nested.als` → `d*`, `ovf.als` → `e*`,
//! `relsort.als` → `g*`); the expected verdicts are the jar's (Alloy 6.2.0,
//! sat4j, symmetry 0, both `noOverflow` settings), recorded as constants so CI
//! runs with no oracle.

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Solve command `idx` of `src` under the given overflow mode. `Ok(true)` = SAT,
/// `Ok(false)` = UNSAT, `Err(())` = a typed defer (which is what these rows used
/// to be, before this bead).
fn solve_at(src: &str, idx: usize, allow_overflow: bool) -> Result<bool, ()> {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[idx]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let opts = SolveOptions {
        allow_overflow,
        ..SolveOptions::default()
    };
    let Ok(goal) = lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx) else {
        return Err(());
    };
    match solve_goal(&ir, &scoped, &goal, &bounds, &opts) {
        Ok(SolveVerdict::Sat(_)) => Ok(true),
        Ok(SolveVerdict::Unsat) => Ok(false),
        Ok(SolveVerdict::Unknown) => panic!("unbudgeted solve returned Unknown"),
        Err(_) => Err(()),
    }
}

/// Every cell in families (a)–(d) and (f) is `noOverflow`-insensitive in the
/// jar, so both modes are asserted to the same verdict — a macro that leaked an
/// overflow flag the inline body does not carry would break exactly this.
#[track_caller]
fn both_modes(src: &str, want: bool, cell: &str) {
    assert_eq!(solve_at(src, 0, true), Ok(want), "{cell} (allow)");
    assert_eq!(solve_at(src, 0, false), Ok(want), "{cell} (forbid)");
}

// ---- (a) a bare name whose macro body is Int-sorted -------------------------

const NAMED: &str = "sig A {}\nlet k = #A\nlet j = plus[1, 2]\nlet n = 3\n";

#[test]
fn a_int_bodied_macro_name_is_its_body() {
    // a01/a02/a03/a04: `k = N` is `#A = N`, so the scope decides.
    both_modes(&format!("{NAMED}run {{ k = 1 }} for 3\n"), true, "a01");
    both_modes(&format!("{NAMED}run {{ k = 3 }} for 3\n"), true, "a02");
    both_modes(&format!("{NAMED}run {{ k = 4 }} for 3\n"), false, "a03");
    both_modes(&format!("{NAMED}run {{ k = 0 }} for 3\n"), true, "a04");
    // a06/a07: the same macro at a wider scope — the body is re-lowered against
    // the command being solved, never cached from an earlier one.
    both_modes(&format!("{NAMED}run {{ k = 4 }} for 5\n"), true, "a06");
    both_modes(&format!("{NAMED}run {{ k = 6 }} for 5\n"), false, "a07");
    // a17/a18: a bare-numeral body — the smallest Int-sorted body there is.
    both_modes(&format!("{NAMED}run {{ n = 3 }} for 3\n"), true, "a17");
    both_modes(&format!("{NAMED}run {{ n = 4 }} for 3\n"), false, "a18");
}

#[test]
fn a_int_bodied_macro_reaches_every_integer_context() {
    // a08/a09/a10/a11/a12: argument of `plus`, an int comparison, both sides of
    // one comparison, and a `sum` body.
    both_modes(
        &format!("{NAMED}run {{ plus[k, 1] = 2 }} for 3\n"),
        true,
        "a08",
    );
    both_modes(
        &format!("{NAMED}run {{ plus[k, 1] = 5 }} for 3\n"),
        false,
        "a09",
    );
    both_modes(&format!("{NAMED}run {{ k > 1 }} for 3\n"), true, "a10");
    both_modes(&format!("{NAMED}run {{ #A = k }} for 3\n"), true, "a11");
    both_modes(
        &format!("{NAMED}run {{ (sum a: A | k) = 4 }} for 3\n"),
        true,
        "a12",
    );
    // a13/a14: and back out through an explicit `Int[·]` into set position.
    both_modes(
        &format!("{NAMED}run {{ Int[k] = Int[1] }} for 3\n"),
        true,
        "a13",
    );
    both_modes(
        &format!("{NAMED}run {{ #(Int[k]) = 1 }} for 3\n"),
        true,
        "a14",
    );
    // a15/a16/a19: a `fun/…`-call body is Rel-sorted, so it never reached the
    // defer — the negative-space control that the fix did not disturb it.
    both_modes(&format!("{NAMED}run {{ j = 3 }} for 3\n"), true, "a15");
    both_modes(&format!("{NAMED}run {{ j = 4 }} for 3\n"), false, "a16");
    both_modes(
        &format!("{NAMED}run {{ plus[j, 1] = 4 }} for 3\n"),
        true,
        "a19",
    );
}

#[test]
fn a_int_bodied_macro_works_in_a_module_fact() {
    // f01..f05: the same macro inside a top-level `fact` rather than a command
    // body — a different lowering entry point onto the same arm.
    const FACT: &str = "sig A {}\nlet k = #A\nfact { k = 2 }\n";
    both_modes(&format!("{FACT}run {{ some A }} for 3\n"), true, "f01");
    both_modes(&format!("{FACT}run {{ #A = 1 }} for 3\n"), false, "f02");
    both_modes(&format!("{FACT}run {{ #A = 2 }} for 3\n"), true, "f03");
    both_modes(&format!("{FACT}run {{ k = 2 }} for 3\n"), true, "f04");
    both_modes(
        &format!("{FACT}run {{ plus[k, 1] = 3 }} for 3\n"),
        true,
        "f05",
    );
}

// ---- (b) the §10.7i `0-(max+1)` fold under a macro --------------------------

const FOLD: &str = "sig F { v: Int }\nsig G { w: set Int }\nfact { one F and one G }\n\
     let m4 = 0-8\nlet m3 = 0-4\nlet c4 = 0-2\n";

#[test]
fn b_the_minus_peephole_survives_macro_expansion() {
    // b01/b02: `let m4 = 0-8` at bw 4 is the int constant `min`, not `{0}` —
    // the jar folds the body after inlining, so the macro is transparent.
    both_modes(
        &format!("{FOLD}run {{ m4 = min }} for 3 but 4 int\n"),
        true,
        "b01",
    );
    both_modes(
        &format!("{FOLD}run {{ m4 = 0 }} for 3 but 4 int\n"),
        false,
        "b02",
    );
    // b04/b05: and it is int-*sorted*, so `plus` takes it unwrapped: −8+1 = −7.
    // (`minus[0,7]` is a genuine `IMINUS`; `0-7` would be the SET `{0}`.)
    both_modes(
        &format!("{FOLD}run {{ plus[m4, 1] = minus[0, 7] }} for 3 but 4 int\n"),
        true,
        "b04",
    );
    both_modes(
        &format!("{FOLD}run {{ plus[m4, 1] = 1 }} for 3 but 4 int\n"),
        false,
        "b05",
    );
    // b11/b12: set position through the macro — one Int atom, not empty.
    both_modes(
        &format!("{FOLD}run {{ G.w = m4 and no G.w }} for 3 but 4 int\n"),
        false,
        "b11",
    );
    both_modes(
        &format!("{FOLD}run {{ #(Int[m4]) = 1 }} for 3 but 4 int\n"),
        true,
        "b12",
    );
}

#[test]
fn b_the_fold_under_a_macro_still_tracks_the_command_bitwidth() {
    // b06/b07/b08: the guard is on the *command's* `max+1`, and inlining does
    // not freeze it — `let m3 = 0-4` folds at bw 3 and is plain `{0}` at bw 4.
    both_modes(
        &format!("{FOLD}run {{ m3 = min }} for 3 but 3 int\n"),
        true,
        "b06",
    );
    both_modes(
        &format!("{FOLD}run {{ m3 = min }} for 3 but 4 int\n"),
        false,
        "b07",
    );
    both_modes(
        &format!("{FOLD}run {{ m3 = 0 }} for 3 but 4 int\n"),
        true,
        "b08",
    );
    // b09/b10: negative space — an in-range right operand never folds, macro or
    // not, so `let c4 = 0-2` stays the set `{0}`.
    both_modes(
        &format!("{FOLD}run {{ c4 = 0 }} for 3 but 4 int\n"),
        true,
        "b09",
    );
    both_modes(
        &format!("{FOLD}run {{ c4 = min }} for 3 but 4 int\n"),
        false,
        "b10",
    );
}

// ---- (c) a parameterized macro in integer position (the spine arm) ----------

const PARAM: &str = "sig A {}\nlet f[x] = plus[x, 1]\nlet card[s] = #s\n";

#[test]
fn c_parameterized_macro_with_an_int_bodied_result_lowers() {
    // c07/c08/c09: `card`'s body is `#s`, so the *spine* `card[A]` is
    // Int-sorted — the `integer-position spine` half of the defer.
    both_modes(
        &format!("{PARAM}run {{ card[A] = 2 }} for 3\n"),
        true,
        "c07",
    );
    both_modes(
        &format!("{PARAM}run {{ card[A] = 4 }} for 3\n"),
        false,
        "c08",
    );
    both_modes(
        &format!("{PARAM}run {{ plus[card[A], 1] = 3 }} for 3\n"),
        true,
        "c09",
    );
    // c01/c02/c03/c10/c11: a Rel-sorted body reaches int position through the
    // `Sort::Rel` coercion instead — unchanged controls, including one with an
    // Int-sorted ARGUMENT (`f[#A]`), which `bind_macro` lowers in the caller.
    both_modes(&format!("{PARAM}run {{ f[2] = 3 }} for 3\n"), true, "c01");
    both_modes(&format!("{PARAM}run {{ f[2] = 4 }} for 3\n"), false, "c02");
    both_modes(
        &format!("{PARAM}run {{ plus[f[2], 1] = 4 }} for 3\n"),
        true,
        "c03",
    );
    both_modes(&format!("{PARAM}run {{ f[#A] = 3 }} for 3\n"), true, "c10");
    both_modes(&format!("{PARAM}run {{ f[2] > 2 }} for 3\n"), true, "c11");
}

// ---- (d) macro inside a macro, in integer position (§3.7a carries over) -----

const NESTED: &str = "sig A {}\n\
     let inner = #A\n\
     let outer = plus[inner, 1]\n\
     let g[y] = plus[y, inner]\n\
     let h[z] = g[plus[z, 1]]\n\
     let deep = g[inner]\n\
     let shadow[inner2] = plus[inner2, inner]\n";

#[test]
fn d_a_macro_used_inside_another_macros_body_lowers_in_int_position() {
    // d01/d02: `outer`'s body mentions `inner`, resolved in `outer`'s own
    // (nested) choice table. At `for 3`, `#A + 1` ranges over 1..4.
    both_modes(&format!("{NESTED}run {{ outer = 3 }} for 3\n"), true, "d01");
    both_modes(
        &format!("{NESTED}run {{ outer = 5 }} for 3\n"),
        false,
        "d02",
    );
    // d04/d05: mt-097 family B in int position — `h`'s body applies `g` to an
    // expression built from `h`'s OWN parameter, so the argument must resolve
    // in the caller's table (`bind_macro`, which `replay_macro_int` reuses
    // rather than copying).
    both_modes(&format!("{NESTED}run {{ h[0] = 3 }} for 3\n"), true, "d04");
    both_modes(&format!("{NESTED}run {{ h[0] = 6 }} for 3\n"), false, "d05");
    // d06/d07: an Int-sorted macro passed as another macro's argument —
    // `#A + #A` is even, so an odd target is UNSAT at every scope.
    both_modes(&format!("{NESTED}run {{ deep = 4 }} for 3\n"), true, "d06");
    both_modes(&format!("{NESTED}run {{ deep = 5 }} for 3\n"), false, "d07");
    // d03/d08/d09: a plain application, a parameter that shadows nothing but
    // sits beside a captured macro, and one more arithmetic layer on top.
    both_modes(&format!("{NESTED}run {{ g[1] = 3 }} for 3\n"), true, "d03");
    both_modes(
        &format!("{NESTED}run {{ shadow[1] = 3 }} for 3\n"),
        true,
        "d08",
    );
    both_modes(
        &format!("{NESTED}run {{ plus[h[0], 1] = 4 }} for 3\n"),
        true,
        "d09",
    );
}

// ---- (e) overflow: a macro body is guarded exactly like the same text inline -

const OVF: &str = "sig A {}\nlet ov = plus[7, 1]\nlet ovarg = plus[ov, 0]\n\
     let f[x] = plus[x, 1]\n";

#[test]
fn e_a_macro_body_carries_the_same_overflow_flag_as_the_inline_text() {
    // e01..e09: the decisive pairs. Each macro cell is asserted against the
    // literal inline spelling in BOTH modes — the fix must not add or drop a
    // guard, and it does not, because the body is lowered by the very same arm.
    for (cell, macro_src, inline_src) in [
        (
            "e01/e02",
            "run { ov = negate[8] } for 3 but 4 int\n",
            "run { plus[7, 1] = negate[8] } for 3 but 4 int\n",
        ),
        (
            "e03/e04",
            "run { ov = 8 } for 3 but 4 int\n",
            "run { plus[7, 1] = 8 } for 3 but 4 int\n",
        ),
        (
            "e05/e06",
            "run { ov = 8 } for 3 but 5 int\n",
            "run { plus[7, 1] = 8 } for 3 but 5 int\n",
        ),
        (
            "e08/e09",
            "run { f[7] = negate[8] } for 3 but 4 int\n",
            "run { plus[7, 1] = negate[8] } for 3 but 4 int\n",
        ),
    ] {
        for allow in [true, false] {
            let m = solve_at(&format!("{OVF}{macro_src}"), 0, allow);
            let i = solve_at(&format!("{OVF}{inline_src}"), 0, allow);
            assert_eq!(m, i, "{cell} macro vs inline (allow={allow})");
        }
    }
    // And the absolute verdicts, so the pair-equality above cannot pass by both
    // sides being wrong together: at bw 4 `plus[7,1]` wraps to −8 (allow) and
    // is excluded (forbid); at bw 5 it is in range and both modes agree.
    assert_eq!(
        solve_at(
            &format!("{OVF}run {{ ov = negate[8] }} for 3 but 4 int\n"),
            0,
            true
        ),
        Ok(true),
        "e01 allow"
    );
    assert_eq!(
        solve_at(
            &format!("{OVF}run {{ ov = negate[8] }} for 3 but 4 int\n"),
            0,
            false
        ),
        Ok(false),
        "e01 forbid"
    );
    both_modes(
        &format!("{OVF}run {{ ov = 8 }} for 3 but 5 int\n"),
        true,
        "e05",
    );
    // e07: one macro layer further in — `ovarg`'s body reads `ov`.
    assert_eq!(
        solve_at(
            &format!("{OVF}run {{ ovarg = negate[8] }} for 3 but 4 int\n"),
            0,
            false
        ),
        Ok(false),
        "e07 forbid"
    );
    // e11: an overflow-free control, so the forbid-mode UNSATs above are the
    // guard firing and not something structural about macros.
    both_modes(
        &format!("{OVF}run {{ f[2] = 3 }} for 3 but 4 int\n"),
        true,
        "e11",
    );
}

// ---- (f) Rel-sorted macro bodies in int position (regression) ---------------

const RELSORT: &str = "sig A {}\none sig B { n: Int }\nfact { B.n = 2 }\n\
     let s = A\nlet r = B.n\nlet pick[x] = x.n\n";

#[test]
fn f_rel_sorted_macro_bodies_still_take_the_coercion_path() {
    // g01..g08: these never reached the defer — a `Rel`-sorted body is handled
    // by `lower_int`'s `Sort::Rel` early path (an implicit `int[·]`), and the
    // new macro arm must stay out of its way. All eight were already
    // jar-matching before the fix; they are the negative space for it.
    both_modes(&format!("{RELSORT}run {{ #s = 2 }} for 3\n"), true, "g01");
    both_modes(&format!("{RELSORT}run {{ #s = 4 }} for 3\n"), false, "g02");
    both_modes(&format!("{RELSORT}run {{ r = 2 }} for 3\n"), true, "g03");
    both_modes(
        &format!("{RELSORT}run {{ plus[r, 1] = 3 }} for 3\n"),
        true,
        "g04",
    );
    both_modes(
        &format!("{RELSORT}run {{ (sum b: B | r) = 2 }} for 3\n"),
        true,
        "g05",
    );
    both_modes(
        &format!("{RELSORT}run {{ pick[B] = 2 }} for 3\n"),
        true,
        "g06",
    );
    both_modes(
        &format!("{RELSORT}run {{ plus[pick[B], 1] = 3 }} for 3\n"),
        true,
        "g07",
    );
    both_modes(
        &format!("{RELSORT}run {{ plus[#s, r] = 4 }} for 3\n"),
        true,
        "g08",
    );
}
