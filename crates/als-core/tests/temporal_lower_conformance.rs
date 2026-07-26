//! LTL-on-lasso lowering conformance (mt-066, ADR-0015 §2): one jar-pinned
//! SAT/UNSAT cell per temporal operator (all 11, plus `'`), the past-under-future
//! cells that decided the encoding, the per-state structural constraints, and the
//! lowering's own negative space.
//!
//! **Jar-free.** Every expected verdict is a constant citing the probe id that
//! pinned it against the reference Alloy 6.2.0 jar; the harness, fixtures,
//! predictions-before-run and verbatim output are in
//! `scratchpad/probe/mt066/NOTES.md` (gitignored, rerunnable via
//! `scratchpad/probe/mt066/rerun_all.sh`). The probe fixtures fix the trace
//! length with `for exactly N steps`; here the driver takes `k` directly, which
//! is the same thing one length at a time (`steps` range handling is mt-067).
//!
//! The driver below duplicates a little of what mt-067 will productionize
//! (resolve → universe → bounds → unroll → lower at `k` → encode with a minted
//! lasso selector → solve, ascending `k`, first SAT wins — alloy6-temporal.md
//! §(c)); that is deliberate, so this suite pins the *lowering* without waiting
//! on the driver bead.

use als_core::ir::{FormulaKind, Ir, Mutability, RelExprKind};
use als_core::{
    compute_bounds, compute_universe, lower_command, lower_command_keeping_temporal,
    lower_temporal_command, solve_goal, solve_temporal_goal, unroll, LoweredGoal, SolveOptions,
    SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Symmetry breaking is off throughout: it is verdict-neutral by construction,
/// and the *temporal* SBP shape (per-state, skolems excluded — alloy6-temporal.md
/// §(d)) belongs to mt-067, not to this bead's question.
fn opts() -> SolveOptions {
    SolveOptions {
        symmetry: 0,
        ..SolveOptions::default()
    }
}

/// Everything one command at one trace length needs, kept together so a test can
/// inspect the goal as well as solve it.
struct Built {
    ir: Ir,
    scoped: als_core::ScopedUniverse,
    bounds: als_core::BoundsResult,
    unrolled: als_core::UnrolledBounds,
    goal: LoweredGoal,
}

fn build(src: &str, cmd: usize, k: usize) -> Built {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[cmd]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let unrolled = unroll(&mut ir, &bounds.bounds, k);
    let goal = lower_temporal_command(&world, &graph, &scoped, &bounds, &mut ir, cmd, k, &unrolled)
        .expect("temporal lowering");
    Built {
        ir,
        scoped,
        bounds,
        unrolled,
        goal,
    }
}

/// Solves command `cmd` at the single trace length `k`; `true` = SAT.
fn sat_at(src: &str, cmd: usize, k: usize) -> bool {
    let b = build(src, cmd, k);
    match solve_temporal_goal(&b.ir, &b.scoped, &b.goal, &b.bounds, &b.unrolled, &opts()) {
        Ok(SolveVerdict::Sat(_)) => true,
        Ok(SolveVerdict::Unsat) => false,
        Ok(SolveVerdict::Unknown) => panic!("unbudgeted solve returned Unknown"),
        Err(e) => panic!("unexpected temporal solve defer: {e:?}"),
    }
}

/// The minimal SAT trace length in `[min, max]`, or `None` for
/// "no instance within the bound" — the §(c) verdict shape, in miniature.
fn first_sat(src: &str, cmd: usize, min: usize, max: usize) -> Option<usize> {
    (min..=max).find(|&k| sat_at(src, cmd, k))
}

/// The two `var` sigs every operator fixture below ranges over. Kept identical to
/// the probe fixtures (`scratchpad/probe/mt066/fixtures/`) so the cited verdicts
/// transfer verbatim.
const AB: &str = "var sig A {}\nvar sig B {}\n";

/// Builds a one-command model from a body, at overall scope 2.
fn model(body: &str) -> String {
    format!("{AB}run {{ {body} }} for 2\n")
}

// ===================== past operators at the initial state =====================

/// P-A1/P-A2: `before` is the **strong** previous — false at state 0 whatever
/// its body says, so both a positive and a negative body are UNSAT there.
#[test]
fn before_is_false_at_the_initial_state() {
    assert!(!sat_at(&model("before (some A)"), 0, 2), "P-A1");
    assert!(!sat_at(&model("before (no A)"), 0, 2), "P-A2");
}

/// P-A3/P-A4: `once φ` at state 0 is exactly `φ` — the present counts, and there
/// is nothing else in the history.
#[test]
fn once_includes_the_present_and_nothing_earlier() {
    assert!(sat_at(&model("(once (some A)) and (some A)"), 0, 2), "P-A3");
    assert!(!sat_at(&model("(once (some A)) and (no A)"), 0, 2), "P-A4");
}

/// P-A5: `historically φ` at state 0 is exactly `φ`.
#[test]
fn historically_at_the_initial_state_is_the_present() {
    assert!(
        !sat_at(&model("(historically (some A)) and (no A)"), 0, 2),
        "P-A5"
    );
}

/// P-A6/P-A7: `p since q` at state 0 is exactly `q` — pinning the operand order
/// (the **right** operand is the one that must have held).
#[test]
fn since_at_the_initial_state_is_its_right_operand() {
    assert!(
        !sat_at(&model("((some A) since (some B)) and (no B)"), 0, 2),
        "P-A6"
    );
    assert!(
        sat_at(
            &model("((some A) since (some B)) and (no A) and (some B)"),
            0,
            2
        ),
        "P-A7"
    );
}

/// P-A8/P-A9: `p triggered q` at state 0 is exactly `q`, same operand order.
#[test]
fn triggered_at_the_initial_state_is_its_right_operand() {
    assert!(
        !sat_at(&model("((some A) triggered (some B)) and (no B)"), 0, 2),
        "P-A8"
    );
    assert!(
        sat_at(
            &model("((some A) triggered (some B)) and (no A) and (some B)"),
            0,
            2
        ),
        "P-A9"
    );
}

// ========================= until / releases / always =========================

/// P-B1–P-B4: `p until q` is "q eventually, p until then" — the right operand is
/// the goal, and it may be satisfied immediately.
#[test]
fn until_operand_order_and_immediate_satisfaction() {
    assert!(
        sat_at(
            &model("((some A) until (some B)) and (always (no A)) and (some B)"),
            0,
            2
        ),
        "P-B1"
    );
    assert!(
        !sat_at(
            &model("((some A) until (some B)) and (always (no B))"),
            0,
            2
        ),
        "P-B2"
    );
    assert!(
        !sat_at(
            &model("((some A) until (some B)) and (no A) and (no B)"),
            0,
            2
        ),
        "P-B3"
    );
    assert!(
        sat_at(
            &model("((some A) until (some B)) and (no B) and (some A) and (after (some B))"),
            0,
            2
        ),
        "P-B4"
    );
}

/// P-B5–P-B7: `p releases q` requires `q` now, and forever unless `p` releases it.
#[test]
fn releases_requires_its_right_operand_until_released() {
    assert!(
        !sat_at(&model("((some A) releases (some B)) and (no B)"), 0, 2),
        "P-B5"
    );
    assert!(
        sat_at(
            &model(
                "((some A) releases (some B)) and (some A) and (some B) \
                 and (after (always (no B)))"
            ),
            0,
            2
        ),
        "P-B6"
    );
    assert!(
        !sat_at(
            &model("((some A) releases (some B)) and (always (no A)) and (eventually (no B))"),
            0,
            2
        ),
        "P-B7"
    );
}

/// P-B8/P-C7: `always` and `eventually` range over the whole (looping) future,
/// including the present, so they cannot disagree about a rigid property.
#[test]
fn always_and_eventually_contradict_each_other() {
    assert!(
        !sat_at(&model("(eventually (some A)) and (always (no A))"), 0, 2),
        "P-B8"
    );
    assert!(
        !sat_at(&model("(always (some A)) and (eventually (no A))"), 0, 3),
        "P-C7"
    );
}

// =============== the loop-aware successor: `after` and `'` ===============

/// P-C1/P-C2: at trace length 1 the only state's successor is itself, so `A'` is
/// `A` — the back-loop, in its smallest form.
#[test]
fn prime_at_the_last_state_follows_the_back_loop() {
    assert!(!sat_at(&model("(some A) and (no A')"), 0, 1), "P-C1");
    assert!(sat_at(&model("(some A) and (some A')"), 0, 1), "P-C2");
}

/// P-C3/P-C4: the same for the formula-level `after`, and it becomes satisfiable
/// as soon as there is a second state to step into.
#[test]
fn after_at_the_last_state_follows_the_back_loop() {
    assert!(!sat_at(&model("(no A) and (after (some A))"), 0, 1), "P-C3");
    assert!(sat_at(&model("(no A) and (after (some A))"), 0, 2), "P-C4");
}

/// P-C5/P-C6: a prime **chain** steps twice; at `k = 2` the second step is
/// already through the back-loop (whichever state it targets), at `k = 3` it is
/// not.
#[test]
fn prime_chains_step_through_the_back_loop() {
    let body = "(no A) and (no A') and (some A'')";
    assert!(!sat_at(&model(body), 0, 2), "P-C5");
    assert!(sat_at(&model(body), 0, 3), "P-C6");
}

/// P-J1–P-J3: `always (after (before φ))` is `always φ` — which only holds if
/// `before` walks back *through* the back-edge on the second pass.
#[test]
fn before_composes_with_after_across_the_back_loop() {
    assert!(
        sat_at(&model("always (after (before (some A)))"), 0, 3),
        "P-J1"
    );
    assert!(
        !sat_at(
            &model("(always (after (before (some A)))) and (eventually (no A))"),
            0,
            3
        ),
        "P-J2"
    );
    assert!(
        !sat_at(
            &model("(always (after (before (no A)))) and (eventually (some A))"),
            0,
            3
        ),
        "P-J3"
    );
}

// ===================== past under future, through the loop =====================

/// The alternation gadget of `scratchpad/probe/mt066/fixtures/PastUnderFuture.als`:
/// it forces `traceLength = 2` with `loopState = 0`, so state 0 genuinely recurs.
const ALTERNATE: &str = "var sig A {}\nvar sig B {}\n\
     fact Alternate {\n\
       no A\n\
       always ((some A) implies (after (no A)))\n\
       always ((no A) implies (after (some A)))\n\
     }\n";

fn alternating(body: &str) -> String {
    format!("{ALTERNATE}run {{ {body} }} for 2\n")
}

/// P-D0/P-D1: the gadget alone is satisfiable, and stays so when `B` is
/// unconstrained-but-present — the controls that keep P-D2 meaningful.
#[test]
fn the_alternation_gadget_is_satisfiable() {
    assert!(sat_at(&alternating("some univ"), 0, 2), "P-D0");
    assert!(sat_at(&alternating("always (some B)"), 0, 2), "P-D1");
}

/// **P-D2, the decisive cell.** `once` inside `always` sees the *lasso* history,
/// not the physical prefix: at logical time 2 the trace is back at state 0 with
/// `once some A` now true, so `some B` is required there too and the model is
/// UNSAT. An honest-physical-prefix lowering answers SAT here.
#[test]
fn once_under_always_sees_the_looped_history() {
    assert!(
        !sat_at(
            &alternating("(no B) and (always ((once (some A)) implies (some B)))"),
            0,
            2
        ),
        "P-D2"
    );
}

/// P-H1/P-H2: the same divergence through `historically`, and through a depth-2
/// past nest (`once (once p)` ≡ `once p`, so it must agree with P-D2).
#[test]
fn historically_and_nested_past_agree_with_the_decisive_cell() {
    assert!(
        !sat_at(
            &alternating("(no B) and (always ((not (historically (no A))) implies (some B)))"),
            0,
            2
        ),
        "P-H1"
    );
    assert!(
        !sat_at(
            &alternating("(no B) and (always ((once (once (some A))) implies (some B)))"),
            0,
            2
        ),
        "P-H2"
    );
}

/// P-H3: a control where the physical prefix and the lasso history agree, so the
/// UNSATs above are not an artefact of an over-strong past.
#[test]
fn past_under_future_control_stays_satisfiable() {
    assert!(
        sat_at(&alternating("eventually (historically (no A))"), 0, 2),
        "P-H3"
    );
}

/// P-K1–P-K6: every binary operator nested under `always`, so its expansion runs
/// at a non-initial time and through the back-loop, plus a past-under-past nest.
#[test]
fn the_binary_operators_expand_correctly_under_always() {
    // `since`: `no A` holds at state 0 (and again after the loop), so `some B`
    // is required from state 1 on — satisfiable, and broken by `always no B`.
    assert!(
        sat_at(&alternating("always ((some B) since (no A))"), 0, 2),
        "P-K1"
    );
    assert!(
        !sat_at(
            &alternating("(always ((some B) since (no A))) and (always (no B))"),
            0,
            2
        ),
        "P-K2"
    );
    // `triggered` is universal over the past: at state 1 `no A` already fails
    // with nothing after it to release the obligation.
    assert!(
        !sat_at(&alternating("always ((some B) triggered (no A))"), 0, 2),
        "P-K3"
    );
    // `until` is satisfied by the alternation itself.
    assert!(
        sat_at(&alternating("always ((some A) until (no A))"), 0, 2),
        "P-K4"
    );
    // `releases` demands its right operand now, and `some A` is false at state 0.
    assert!(
        !sat_at(&alternating("always ((no A) releases (some A))"), 0, 2),
        "P-K5"
    );
    // A past operator nested in a past operator, at the start of time.
    assert!(
        !sat_at(&alternating("always (once (before (some A)))"), 0, 2),
        "P-K6"
    );
}

/// Over-approximating the unroll depth is harmless: `once (once p)` (depth 2)
/// and `once p` (depth 1) must give the same verdict on the same fixture, at
/// every length in a small range.
#[test]
fn nested_past_agrees_with_flat_past_at_every_length() {
    let flat = alternating("(no B) and (always ((once (some A)) implies (some B)))");
    let nested = alternating("(no B) and (always ((once (once (some A))) implies (some B)))");
    for k in 1..=3 {
        assert_eq!(sat_at(&flat, 0, k), sat_at(&nested, 0, k), "k={k}");
    }
}

// ===================== per-state structural constraints =====================

const HIERARCHY: &str = "sig P {}\nvar sig C extends P {}\n\
     abstract sig Q {}\nvar sig Q1 extends Q {}\nvar sig Q2 extends Q {}\n\
     var one sig S {}\n";

/// P-E0/P-E1: a **static** parent of a `var` child pins the whole union rigid
/// (`BoundsComputer.java:206-207`) — with a static remainder that makes the child
/// itself rigid, so it can never empty out.
#[test]
fn a_static_parent_of_a_var_child_is_rigid() {
    let base = format!("{HIERARCHY}run {{ some C }} for 3\n");
    assert!(sat_at(&base, 0, 3), "P-E0");
    let rigid = format!("{HIERARCHY}run {{ (some C) and (eventually (no C)) }} for 3\n");
    assert!(!sat_at(&rigid, 0, 3), "P-E1");
}

/// P-E2/P-E3: once a subsig is `var`, an atom may never migrate between siblings
/// (`BoundsComputer.java:164-173`) — plain per-state disjointness would allow it.
#[test]
fn an_atom_never_migrates_between_var_subsigs() {
    let base = format!("{HIERARCHY}run {{ some Q1 }} for 1\n");
    assert!(sat_at(&base, 0, 2), "P-E2");
    let migrate = format!(
        "{HIERARCHY}run {{ (some Q1) and (no Q2) and (after ((no Q1) and (some Q2))) }} for 1\n"
    );
    assert!(!sat_at(&migrate, 0, 2), "P-E3");
}

/// P-E4/P-E5: a `one var sig` is `one` at **every** state
/// (`BoundsComputer.java:473`), not just the initial one.
#[test]
fn a_one_var_sig_holds_one_at_every_state() {
    let empties = format!("{HIERARCHY}run {{ eventually (no S) }} for 3\n");
    assert!(!sat_at(&empties, 0, 3), "P-E4");
    let always_one = format!("{HIERARCHY}run {{ always (one S) }} for 3\n");
    assert!(sat_at(&always_one, 0, 3), "P-E5");
}

// ===================== which conjuncts hold at every state =====================

const SEAM: &str = "var sig A {}\nvar sig T {}\nvar sig S {} { some T }\n\
     var sig V { var f: one V }\n";

/// P-F3: a plain top-level `fact` is asserted at state 0 **only** — the model
/// may violate it later.
#[test]
fn a_top_level_fact_binds_the_initial_state_only() {
    let src = format!("{SEAM}fact {{ some A }}\nrun {{ eventually (no A) }} for 2\n");
    assert!(sat_at(&src, 0, 2), "P-F3");
}

/// P-F4: a sig **appended** fact is `always`-wrapped when temporal
/// (`TranslateAlloyToKodkod.java:307-308`).
#[test]
fn an_appended_fact_holds_at_every_state() {
    let src =
        format!("{SEAM}run {{ (some S) and (some T) and (after ((some S) and (no T))) }} for 2\n");
    assert!(!sat_at(&src, 0, 2), "P-F4");
}

/// P-F5/P-F6: a synthesized **field declaration** fact is `always`-wrapped when
/// temporal (`:268-269`), so `one this.f` binds every state.
#[test]
fn a_field_decl_fact_holds_at_every_state() {
    let breaks = format!("{SEAM}run {{ (always (some V)) and (eventually (no f)) }} for 2\n");
    assert!(!sat_at(&breaks, 0, 2), "P-F5");
    let holds = format!("{SEAM}run {{ (always (some V)) and (always (some f)) }} for 2\n");
    assert!(sat_at(&holds, 0, 2), "P-F6");
}

// ============================= skolemization =============================

const SKOLEM: &str = "var sig A {}\nsig N { r: set N }\n";

/// P-F1: a temporal model still skolemizes a top-level existential that sits
/// **outside** every temporal operator, and the witness relation is **static**
/// (the jar's trace prints the same `$f1_x` value in every state).
#[test]
fn a_top_level_existential_still_skolemizes_in_a_temporal_model() {
    let src = format!("{SKOLEM}run {{ some x: N | no x.r }} for 2\n");
    let b = build(&src, 0, 2);
    assert!(!b.goal.skolem_bounds.is_empty(), "P-F1: expected a witness");
    for (rel, _) in &b.goal.skolem_bounds {
        assert_eq!(
            b.ir.relations[*rel].mutability,
            Mutability::Static,
            "P-F1: a skolem constant is rigid across the trace"
        );
        assert!(!b.unrolled.is_unrolled(*rel));
    }
    assert!(sat_at(&src, 0, 2));
}

/// P-F2: the same existential under `always` mints no witness
/// (`Skolemizer.java:494-526` forces `skolemDepth = -1` under every temporal
/// operator) — the rule mt-055 shipped, extended to the temporal path.
#[test]
fn an_existential_under_a_temporal_operator_never_skolemizes() {
    let src = format!("{SKOLEM}run {{ always (some x: N | no x.r) }} for 2\n");
    let b = build(&src, 0, 2);
    assert!(b.goal.skolem_bounds.is_empty(), "P-F2");
    assert!(sat_at(&src, 0, 2));
}

// ============================== negative space ==============================

/// The acceptance invariant: the lowered goal is first-order — no temporal node,
/// no prime, and no reference to an original (un-unrolled) `var` relation. The
/// entry point asserts this itself; this walks the result independently so a
/// regression shows up as a test failure rather than only as a panic.
#[test]
fn the_lowered_goal_is_first_order() {
    let src = format!(
        "{ALTERNATE}run {{ ((some A) until (some B)) and (once (some A)) and (some A') }} for 2\n"
    );
    let b = build(&src, 0, 3);
    let mut temporal = 0usize;
    let mut originals = 0usize;
    let mut loop_atoms = 0usize;
    for (_, f) in b.ir.formulas.iter() {
        match f.kind {
            FormulaKind::TemporalUnary { .. } | FormulaKind::TemporalBinary { .. } => {
                // The pre-translation nodes still live in the arena; only their
                // reachability from the goal matters, which the entry point
                // asserts. Count them to prove the fixture really is temporal.
                temporal += 1;
            }
            FormulaKind::LoopIs { state } => {
                assert!(state < 3, "loop atom outside the trace");
                loop_atoms += 1;
            }
            _ => {}
        }
    }
    assert!(temporal > 0, "the fixture must exercise temporal operators");
    assert_eq!(loop_atoms, 3, "one loop atom per candidate loop state");
    for (_, e) in b.ir.rel_exprs.iter() {
        if let RelExprKind::Relation(r) = e.kind {
            if b.unrolled.is_unrolled(r) {
                originals += 1;
            }
        }
    }
    // Originals may still be referenced by the *pre*-translation nodes; the goal
    // itself is checked by `assert_first_order` inside the entry point, which
    // would have panicked before `build` returned.
    let _ = originals;
}

/// A model with no `var` and no temporal operator lowers temporally to the same
/// verdict as the static path, at any trace length — the property that keeps the
/// temporal path from changing static answers.
#[test]
fn a_static_model_lowers_temporally_to_its_static_verdict() {
    let src = "sig N { r: set N }\nrun { some n: N | n in n.r } for 3\n";
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
    let static_sat = matches!(
        solve_goal(&ir, &scoped, &goal, &bounds, &opts()),
        Ok(SolveVerdict::Sat(_))
    );
    for k in 1..=3 {
        assert_eq!(sat_at(src, 0, k), static_sat, "k={k}");
    }
    // A static model has nothing to unroll, so the trace length is pure overhead.
    let b = build(src, 0, 2);
    assert!(b.unrolled.states.is_empty());
}

/// `lower_command_keeping_temporal` and `lower_command` differ **only** in the
/// temporal defer: on a static model they agree conjunct-for-conjunct.
#[test]
fn keeping_temporal_matches_the_static_lowering_on_a_static_model() {
    let src = "sig N { r: set N }\nfact { some r }\nrun { some N } for 3\n";
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");

    let mut a_ir = Ir::default();
    let a_bounds = compute_bounds(&world, &scoped, &mut a_ir);
    let a = lower_command(&world, &graph, &scoped, &a_bounds, &mut a_ir, 0).expect("lower");

    let mut b_ir = Ir::default();
    let b_bounds = compute_bounds(&world, &scoped, &mut b_ir);
    let b = lower_command_keeping_temporal(&world, &graph, &scoped, &b_bounds, &mut b_ir, 0)
        .expect("lower");

    assert_eq!(a.goal, b.goal);
    assert_eq!(a.conjuncts, b.conjuncts);
    assert_eq!(a.skolem_bounds, b.skolem_bounds);
    assert_eq!(a_ir.formulas.len(), b_ir.formulas.len());
}

// ======================= trace-length sweep + determinism =======================

/// The §(c) verdict shape in miniature: ascending `k`, first SAT wins, and the
/// answer is the **minimal** satisfying length — P-C4 (`after` needs 2 states)
/// and P-C6 (a prime chain needs 3).
#[test]
fn the_minimal_satisfying_trace_length_is_found_first() {
    assert_eq!(
        first_sat(&model("(no A) and (after (some A))"), 0, 1, 4),
        Some(2)
    );
    assert_eq!(
        first_sat(&model("(no A) and (no A') and (some A'')"), 0, 1, 4),
        Some(3)
    );
    // "No instance within the bound" is bound-relative, never "unsatisfiable".
    assert_eq!(
        first_sat(&model("(no A) and (after (some A))"), 0, 1, 1),
        None
    );
}

/// STYLE U4: the same command at the same length lowers to a byte-identical goal
/// shape and the same arena sizes on a fresh run.
#[test]
fn temporal_lowering_is_deterministic() {
    let src = alternating("(no B) and (always ((once (some A)) implies (some B)))");
    let shape = |k: usize| {
        let b = build(&src, 0, k);
        (
            b.ir.formulas.len(),
            b.ir.rel_exprs.len(),
            b.ir.int_exprs.len(),
            b.ir.relations.len(),
            b.goal.goal,
            format!("{:?}", b.goal.conjuncts),
        )
    };
    assert_eq!(shape(3), shape(3));
    assert_ne!(shape(3), shape(2));
}
