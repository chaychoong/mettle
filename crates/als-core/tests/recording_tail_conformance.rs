//! The mt-040 recording tail (mt-097): jar-pinned verdicts for the two families
//! of the `lowering` defer bucket that mt-097 converted — a macro applied inside
//! **another macro's body**, and `run` on a **fun**. Cells come from
//! `scratchpad/probe/mt097/` (`b_macro.als` → `b*`, `c_runfun.als` → `c*`/`f*`,
//! `c2_predcontrol.als`); the expected verdicts are the jar's (Alloy 6.2.0),
//! recorded as constants so CI runs with no oracle.
//!
//! Rules: translation-ref §3.7a (nested macro argument context) and §2.5(3a)
//! (`run` on a fun).

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Solve command `idx` of `src`. `Ok(true)` = SAT, `Ok(false)` = UNSAT,
/// `Err(())` = a typed defer (which is what these rows used to be).
fn solve_at(src: &str, idx: usize) -> Result<bool, ()> {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[idx]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let Ok(goal) = lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx) else {
        return Err(());
    };
    match solve_goal(&ir, &scoped, &goal, &bounds, &SolveOptions::default()) {
        Ok(SolveVerdict::Sat(_)) => Ok(true),
        Ok(SolveVerdict::Unsat) => Ok(false),
        Ok(SolveVerdict::Unknown) => panic!("unbudgeted solve returned Unknown"),
        Err(_) => Err(()),
    }
}

fn solve(src: &str) -> Result<bool, ()> {
    solve_at(src, 0)
}

// ---- Family B: a macro applied inside another macro's body (§3.7a) ---------
//
// `expand_macro` resolves a macro application's ARGUMENTS in its own context
// before recursing into the body, so for a nested application the arguments'
// choices live in the enclosing macro's *nested* table. The lowerer's
// `bind_macro` used to rebuild a module-level context to lower them, which
// dropped that table — the argument name then had no recorded resolution and the
// command deferred. It now lowers arguments in the caller's context.

const NESTED_PRELUDE: &str = "open util/ordering[Time]\n\
     sig Time {}\n\
     let range[s,e] = (s + s.nexts) - e.nexts\n\
     let overlap[s1,e1,s2,e2] = some (range[s1,e1] & range[s2,e2])\n";

#[test]
fn b_macro_used_inside_another_macros_body_lowers() {
    // b1/b2 — the overlapping-ranges[0] shape: `overlap`'s body applies `range`
    // to `overlap`'s OWN parameters. Both must lower (not defer) and match the
    // jar. `[t0,t0] ∩ [t0,tn]` always overlaps, so the check is valid.
    let b1 = format!("{NESTED_PRELUDE}check {{ overlap[first, first, first, last] }} for 5\n");
    assert_eq!(solve(&b1), Ok(false), "b1 (check: no counterexample)");
    let b2 = format!("{NESTED_PRELUDE}run {{ overlap[first, last, first, last] }} for 5\n");
    assert_eq!(solve(&b2), Ok(true), "b2");
}

const RECV_PRELUDE: &str = "sig Thing {}\n\
     one sig Tbl { setting: set Thing }\n\
     let upd[t, s] = t.setting = s\n";

#[test]
fn b_macro_with_a_parameter_receiver_lowers() {
    // b3 — the philosophers `table\".update[..]` shape: a macro applied with
    // RECEIVER syntax whose receiver is a parameter of the enclosing macro.
    let b3 = format!(
        "{RECV_PRELUDE}let take[x, t] {{ t.upd[ x ] }}\n\
         run {{ some x: set Thing | take[x, Tbl] }} for 3\n"
    );
    assert_eq!(solve(&b3), Ok(true), "b3");

    // b4 — one level deeper, with a `let` VALUE binding between the two macro
    // layers (the philosophers `eat` shape).
    let b4 = format!(
        "{RECV_PRELUDE}let eat[x, t] {{ let ss = t.setting {{ t.upd[ ss + x ] }} }}\n\
         run {{ some x: set Thing | eat[x, Tbl] }} for 3\n"
    );
    assert_eq!(solve(&b4), Ok(true), "b4");
}

#[test]
fn b_direct_macro_uses_are_unchanged() {
    // b5/b6/b7 — the same macros applied directly (not nested) worked before
    // mt-097 and must still: the caller's context IS the module context there,
    // so the change is inert.
    let b5 = format!("{NESTED_PRELUDE}run {{ some range[first, last] }} for 5\n");
    assert_eq!(solve(&b5), Ok(true), "b5");
    let b6 = format!("{RECV_PRELUDE}run {{ Tbl.upd[ Thing ] }} for 3\n");
    assert_eq!(solve(&b6), Ok(true), "b6");
    let b7 = format!("{RECV_PRELUDE}run {{ some x: set Thing | Tbl.upd[ x ] }} for 3\n");
    assert_eq!(solve(&b7), Ok(true), "b7");
}

// ---- Family C: `run` on a fun (§2.5(3a)) -----------------------------------
//
// `run f` existentially quantifies the fun's parameters over their declared
// bounds and asserts NOTHING about the result — the body is ignored. Pinned by
// the pred/fun pair and by the parameter-multiplicity cells.

const FUNS: &str = "sig A {}\nsig B {}\n\
     fun f_ident[x: A]: set A { x }\n\
     fun f_empty[x: A]: set A { x - x }\n\
     fun f_noarg: set A { A }\n\
     fun f_noarg_empty: set A { none }\n\
     fun f_two[x: A, y: B]: set A { x }\n";

#[test]
fn c_run_on_a_fun_ignores_the_body() {
    // c3/c4 and c7/c8 are the decisive pairs: asserting `some <result>` is UNSAT
    // for an always-empty fun, but `run <that fun>` is SAT — so the body cannot
    // be part of the command.
    let desugar_empty = format!("{FUNS}run {{ some x: A | some f_empty[x] }} for 3\n");
    assert_eq!(solve(&desugar_empty), Ok(false), "c3 `some f_empty[x]`");
    let run_empty = format!("{FUNS}run f_empty for 3\n");
    assert_eq!(solve(&run_empty), Ok(true), "c4 `run f_empty`");

    let desugar_noarg = format!("{FUNS}run {{ some f_noarg_empty }} for 3\n");
    assert_eq!(solve(&desugar_noarg), Ok(false), "c7 `some f_noarg_empty`");
    let run_noarg = format!("{FUNS}run f_noarg_empty for 3\n");
    assert_eq!(solve(&run_noarg), Ok(true), "c8 `run f_noarg_empty`");
}

#[test]
fn c_run_on_a_fun_still_demands_its_parameters() {
    // c11/c12 — the params ARE quantified: at an empty scope for the param's sig
    // the command is UNSAT, exactly as the hand-written existential is.
    let desugar = format!("{FUNS}run {{ some x: A | some f_ident[x] }} for 0 A, 3 B\n");
    assert_eq!(solve(&desugar), Ok(false), "c11");
    let run_fun = format!("{FUNS}run f_ident for 0 A, 3 B\n");
    assert_eq!(solve(&run_fun), Ok(false), "c12");
    // …and both params of a two-param fun.
    let two = format!("{FUNS}run f_two for 3\n");
    assert_eq!(solve(&two), Ok(true), "c10");
    let noarg = format!("{FUNS}run f_noarg for 3\n");
    assert_eq!(solve(&noarg), Ok(true), "c6");
}

#[test]
fn c_parameter_multiplicity_is_respected() {
    // A plain `x: A` (implicitly `one`) and an explicit `one` demand a non-empty
    // A; `lone` and `set` do not. All four at `for 0 A`.
    let src = "sig A {}\nsig B {}\n\
        fun f_lone[x: lone A]: set A { x }\n\
        fun f_set[x: set A]: set A { x }\n\
        fun f_one[x: one A]: set A { x }\n\
        fun f_plain[x: A]: set A { x }\n";
    for (cell, cmd, want) in [
        ("f_lone", "run f_lone for 0 A, 3 B\n", true),
        ("f_set", "run f_set for 0 A, 3 B\n", true),
        ("f_one", "run f_one for 0 A, 3 B\n", false),
        ("f_plain", "run f_plain for 0 A, 3 B\n", false),
    ] {
        assert_eq!(solve(&format!("{src}{cmd}")), Ok(want), "{cell}");
    }
}

#[test]
fn c_run_on_a_pred_still_uses_its_body() {
    // The asymmetry that makes the fun rule meaningful: a pred's body IS the
    // command, so a contradictory one is UNSAT where the fun analogue is SAT.
    let src = "sig A {}\n\
        pred p_false[x: A] { x != x }\n\
        pred p_true[x: A] { x = x }\n\
        pred p_noarg_false { some none }\n";
    assert_eq!(
        solve(&format!("{src}run p_false for 3\n")),
        Ok(false),
        "p_false"
    );
    assert_eq!(
        solve(&format!("{src}run p_true for 3\n")),
        Ok(true),
        "p_true"
    );
    assert_eq!(
        solve(&format!("{src}run p_noarg_false for 3\n")),
        Ok(false),
        "p_noarg_false"
    );
}
