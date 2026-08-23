//! Temporal solve-driver conformance (mt-067, ADR-0015 §3): the `steps` surface,
//! the ascending `for k in [min,max]` sweep and its verdicts, the typed defers,
//! lasso loop-target recovery, the per-state trace decode, and per-state
//! symmetry breaking.
//!
//! **Jar-free.** Every expected value is a constant citing the probe id that
//! pinned it against the reference Alloy 6.2.0 jar (`T-NN` = the mt-063/mt-064
//! contract waves, `P-XN` = the mt-066 lowering wave); the harnesses, fixtures,
//! predictions-before-run and verbatim jar output live in
//! `scratchpad/probe/mt063/`, `mt064/` and `mt066/` (all gitignored, each
//! rerunnable via its own `rerun_all.sh`). The prose contract is
//! `docs/reference/alloy6-temporal.md` §(a)-(d).

use als_core::ir::{Ir, RelId};
use als_core::{
    compute_bounds, compute_universe, solve_temporal_command, BoundsResult, ScopedUniverse,
    SolveOptions, TemporalSolveConfig, TemporalTrace, TemporalVerdict, TranslateError,
};
use als_types::{
    is_temporal_model, resolve, MapLoader, ModuleGraph, ResolvedWorld, StepsMax, DEFAULT_STEPS,
};

// ================================ harness ================================

/// Resolves `src` as the root module, or returns the resolve error.
fn try_resolve(src: &str) -> Result<(ResolvedWorld, ModuleGraph), als_types::ResolveError> {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph)?.world;
    Ok((world, graph))
}

fn resolved(src: &str) -> (ResolvedWorld, ModuleGraph) {
    try_resolve(src).unwrap_or_else(|e| panic!("resolve failed: {e:?}"))
}

/// Everything the driver needs for one command, built the way `mettle exec` and
/// the solve gauge build it.
struct Built {
    world: ResolvedWorld,
    graph: ModuleGraph,
    scoped: ScopedUniverse,
    bounds: BoundsResult,
    ir: Ir,
}

fn build(src: &str, cmd: usize) -> Built {
    let (world, graph) = resolved(src);
    let scoped = compute_universe(&world, &graph, &world.commands[cmd]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    Built {
        world,
        graph,
        scoped,
        bounds,
        ir,
    }
}

/// Symmetry breaking is on at the jar's own default (20) unless a test says
/// otherwise, and the self-check runs in every build so a wrong trace is loud.
fn cfg(symmetry: u32) -> TemporalSolveConfig {
    TemporalSolveConfig {
        opts: SolveOptions {
            symmetry,
            ..SolveOptions::default()
        },
        primary_var_cap: None,
        self_check: true,
    }
}

/// Runs the driver over command `cmd` of `src`.
fn drive(src: &str, cmd: usize, symmetry: u32) -> Result<TemporalVerdict, TranslateError> {
    let mut b = build(src, cmd);
    solve_temporal_command(
        &b.world,
        &b.graph,
        &b.scoped,
        &b.bounds,
        &mut b.ir,
        cmd,
        &cfg(symmetry),
    )
}

/// The solved trace, at the jar's default symmetry.
fn trace(src: &str, cmd: usize) -> TemporalTrace {
    match drive(src, cmd, 20) {
        Ok(TemporalVerdict::Sat(t)) => {
            assert!(
                t.self_check.is_none(),
                "temporal self-check failed (a mettle bug): {:?}",
                t.self_check
            );
            t
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// The minimal satisfying trace length, or `None` for UNSAT-within-bound.
fn minimal_k(src: &str, cmd: usize) -> Option<usize> {
    match drive(src, cmd, 20) {
        Ok(TemporalVerdict::Sat(t)) => Some(t.k()),
        Ok(TemporalVerdict::Unsat) => None,
        other => panic!("expected a verdict, got {other:?}"),
    }
}

/// The relation id whose name is exactly `name`.
fn rel_named(ir: &Ir, name: &str) -> RelId {
    let mut found = None;
    for (id, r) in ir.relations.iter() {
        if r.name == name {
            assert!(found.is_none(), "two relations named {name}");
            found = Some(id);
        }
    }
    found.unwrap_or_else(|| panic!("no relation named {name}"))
}

// ========================= (b) the `steps` surface =========================

/// **T-04/T-06/T-07/T-05/L6/T-08b** — the six surface shapes resolve to the
/// pinned ranges. The load-bearing one is the second: a bare `for N steps` means
/// the range `[1, N]`, **not** "exactly N states".
#[test]
fn the_six_steps_shapes_resolve_to_the_pinned_ranges() {
    let cases: [(&str, u32, StepsMax); 6] = [
        // No `steps` clause at all → `ScopeComputer`'s field defaults (T-01/T-02/T-04).
        ("var sig A {}\nrun {} for 2\n", 1, StepsMax::Bounded(10)),
        // Bare `for N steps` leaves `minprefix` at its -1 sentinel (T-06).
        (
            "var sig A {}\nrun {} for 2 but 3 steps\n",
            1,
            StepsMax::Bounded(3),
        ),
        // `exactly N` desugars to `N..N` (T-07).
        (
            "var sig A {}\nrun {} for 2 but exactly 3 steps\n",
            3,
            StepsMax::Bounded(3),
        ),
        // An explicit range round-trips unchanged (T-05).
        (
            "var sig A {}\nrun {} for 2 but 2..4 steps\n",
            2,
            StepsMax::Bounded(4),
        ),
        // `exactly` OVERRIDES a written range end: `exactly N..M` collapses to
        // `N..N` and `M` is discarded (L6/L6b).
        (
            "var sig A {}\nrun {} for 2 but exactly 2..4 steps\n",
            2,
            StepsMax::Bounded(2),
        ),
        // `1..` sets `maxprefix = Integer.MAX_VALUE` (T-08b).
        (
            "var sig A {}\nrun {} for 2 but 1.. steps\n",
            1,
            StepsMax::Unbounded,
        ),
    ];
    for (src, min, max) in cases {
        let (world, _) = resolved(src);
        let range = world.commands[0].steps_range();
        assert_eq!((range.min, range.max), (min, max), "{src}");
    }
    assert_eq!(
        (DEFAULT_STEPS.min, DEFAULT_STEPS.max),
        (1, StepsMax::Bounded(10))
    );
}

/// **L6/L6b** — `exactly N..M steps` discards `M` and searches `[N, N]`.
///
/// The jar collapses it at `Command`-construction time: `Command.toString()`
/// renders a source `exactly 3..5 steps` back as `"for 3..3 steps"` (L6, on a
/// static command, isolating the parse-time collapse), and a genuinely temporal
/// solve of the same shape reports `getMinTrace()==3, getMaxTrace()==3` against
/// the control `3..5 steps`'s `3`/`5` (L6b). Keeping `[N, M]` would search
/// **wider** than the jar — see
/// [`exactly_collapses_the_search_range_not_just_its_rendering`] for the
/// verdict this changes.
#[test]
fn exactly_discards_a_written_steps_range_end() {
    for (src, expected) in [
        ("var sig A {}\nrun {} for 2 but exactly 3..5 steps\n", 3),
        // The control from L6/L6b's own fixtures: without `exactly`, `M` stands.
        ("var sig A {}\nrun {} for 2 but 3..5 steps\n", 5),
    ] {
        let (world, _) = resolved(src);
        let range = world.commands[0].steps_range();
        assert_eq!(range.min, 3, "{src}");
        assert_eq!(range.max, StepsMax::Bounded(expected), "{src}");
    }
}

/// The verdict consequence of L6/L6b, which is why the collapse is not cosmetic:
/// a model satisfiable **only** above `N` answers UNSAT-within-bound under
/// `exactly N..M steps`, because the search range really is `[N, N]`.
///
/// The fixture is P-C6's prime chain — `(no A) and (no A') and (some A'')`
/// needs exactly 3 states — put under `exactly 2..4 steps`. Reading the range as
/// the written `[2, 4]` would find the length-3 witness and answer SAT; reading
/// it as the jar's `[2, 2]` cannot. The control at plain `2..4 steps` shows the
/// witness is genuinely there.
#[test]
fn exactly_collapses_the_search_range_not_just_its_rendering() {
    let body = "(no A) and (no A') and (some A'')";
    assert_eq!(
        minimal_k(
            &format!("{AB}run {{ {body} }} for 2 but exactly 2..4 steps\n"),
            0
        ),
        None,
        "L6/L6b: the range is [2,2], so the length-3 witness is out of bounds"
    );
    assert_eq!(
        minimal_k(&format!("{AB}run {{ {body} }} for 2 but 2..4 steps\n"), 0),
        Some(3),
        "control: the same command over the written range [2,4] finds it"
    );
}

/// `ScopeComputer.java:484-492`'s clamp: an inverted range collapses onto its
/// upper bound rather than searching an empty interval.
#[test]
fn an_inverted_steps_range_clamps_to_its_upper_bound() {
    let (world, _) = resolved("var sig A {}\nrun {} for 2 but 5..3 steps\n");
    let range = world.commands[0].steps_range();
    assert_eq!((range.min, range.max), (3, StepsMax::Bounded(3)));
}

/// **T-03** — a `steps` scope on a *static* command is a reject, verbatim in the
/// jar's own words (`ScopeComputer.java:479`/`:487`). Gated on the pinned
/// discriminator, so the identical scope on a `var` model is fine.
#[test]
fn steps_on_a_static_model_is_the_pinned_reject() {
    let src = "sig A {}\nfact { some A }\nrun {} for 2 but 3 steps\n";
    let (world, graph) = resolved(src);
    assert!(
        !is_temporal_model(&world, &graph, &world.commands[0]),
        "T-03"
    );
    let err = compute_universe(&world, &graph, &world.commands[0]).expect_err("T-03 rejects");
    assert!(
        matches!(err, TranslateError::StepsScopeInStaticModel { .. }),
        "{err:?}"
    );
    assert_eq!(
        err.to_string(),
        "You cannot set a scope on \"steps\" in static models."
    );

    // The same clause on a temporal model is accepted (T-01: `var` alone makes
    // it temporal, with no temporal operator anywhere).
    let ok = "var sig A {}\nfact { some A }\nrun {} for 2 but 3 steps\n";
    let (world, graph) = resolved(ok);
    assert!(is_temporal_model(&world, &graph, &world.commands[0]));
    assert!(compute_universe(&world, &graph, &world.commands[0]).is_ok());
}

/// **T-08a** — an open `steps` range must start at 1; the jar rejects any other
/// start verbatim. (The jar catches it in its grammar, mettle in the resolver —
/// both are file-level rejects, so the accept/reject answer is the same.)
#[test]
fn an_open_steps_range_must_start_at_one() {
    let err = try_resolve("var sig A {}\nrun {} for 2 but 3.. steps\n").expect_err("T-08a rejects");
    assert_eq!(err.to_string(), "Unbounded time scope must start at 1.");
    // `1..` itself parses and resolves — it is the *solver* that refuses it.
    assert!(try_resolve("var sig A {}\nrun {} for 2 but 1.. steps\n").is_ok());
}

/// A `steps` growth increment must be 1 (grammar-ref §4.5: `1:2 steps` is a
/// jar reject, while `1:2 A` on a sig scope is legal). Closes the deferral
/// LIMITATIONS recorded at mt-011.
#[test]
fn a_steps_increment_other_than_one_is_rejected() {
    assert!(try_resolve("var sig A {}\nrun {} for 2 but 1:2 steps\n").is_err());
    assert!(try_resolve("var sig A {}\nrun {} for 2 but 1..4:2 steps\n").is_err());
    // Increment 1 is fine, and a sig scope keeps taking any increment.
    assert!(try_resolve("var sig A {}\nrun {} for 2 but 1:1 steps\n").is_ok());
    assert!(try_resolve("sig A {}\nrun {} for 1:2 A\n").is_ok());
}

// ===================== (c) the sweep and its verdicts =====================

const AB: &str = "var sig A {}\nvar sig B {}\n";

/// **T-09/T-10b, P-C4/P-C6** — ascending `k`, first SAT wins: the driver returns
/// the *minimal* satisfying length, never a longer one that also fits.
#[test]
fn the_sweep_returns_the_minimal_satisfying_trace_length() {
    // `after` needs a second state (P-C4); the default range `[1,10]` would
    // happily admit every longer length too.
    assert_eq!(
        minimal_k(
            &format!("{AB}run {{ (no A) and (after (some A)) }} for 2\n"),
            0
        ),
        Some(2)
    );
    // A prime chain needs three (P-C6).
    assert_eq!(
        minimal_k(
            &format!("{AB}run {{ (no A) and (no A') and (some A'') }} for 2\n"),
            0
        ),
        Some(3)
    );
    // An explicit range starting above the minimum starts there, not at 1.
    assert_eq!(
        minimal_k(&format!("{AB}run {{ some A }} for 2 but 4..6 steps\n"), 0),
        Some(4)
    );
}

/// **T-10b** — UNSAT is *bound-relative*: the same command flips to SAT once the
/// `steps` bound is large enough. The driver never claims anything stronger than
/// "no instance within the bound".
#[test]
fn unsat_within_bound_flips_when_the_bound_grows() {
    let body = "(no A) and (after (some A))";
    assert_eq!(
        minimal_k(
            &format!("{AB}run {{ {body} }} for 2 but exactly 1 steps\n"),
            0
        ),
        None
    );
    assert_eq!(
        minimal_k(&format!("{AB}run {{ {body} }} for 2 but 2 steps\n"), 0),
        Some(2)
    );
}

/// The whole `steps` range is searched before UNSAT is reported: a command whose
/// only satisfying length is the last one in the range still answers SAT.
#[test]
fn the_sweep_searches_the_whole_range_before_answering_unsat() {
    let sat = format!("{AB}run {{ (no A) and (no A') and (some A'') }} for 2 but 3 steps\n");
    assert_eq!(minimal_k(&sat, 0), Some(3));
    let unsat = format!("{AB}run {{ (no A) and (no A') and (some A'') }} for 2 but 2 steps\n");
    assert_eq!(minimal_k(&unsat, 0), None);
}

// ============================ the typed defers ============================

/// **T-08b** — `for 1.. steps` asks for complete model checking, which the
/// reference's default bounded engine refuses outright, in these exact words.
/// Reconfirmed jar-side by two real `trash.als` corpus commands.
#[test]
fn unbounded_steps_is_the_pinned_engine_rejection() {
    let err = drive(
        &format!("{AB}run {{ some A }} for 2 but 1.. steps\n"),
        0,
        20,
    )
    .expect_err("T-08b rejects");
    assert!(
        matches!(err, TranslateError::UnboundedSteps { .. }),
        "{err:?}"
    );
    assert_eq!(
        err.to_string(),
        "Bounded engines do not support complete model checking."
    );
}

/// **P-077-1** — a `check` at a one-state bound is *answered*, not refused
/// (mt-077). `always some Flag` is falsified by the single-state lasso in which
/// `Flag` is empty, so the counterexample is a 1-state trace looping on state 0.
///
/// Jar cell (`fixtures/P1_CounterexampleAtOne.als`): `check AlwaysSome for 2 but
/// 1 steps` → `sat=true traceLength=1 loopState=0`, and its dual `run { not
/// (always some Flag) } for 2 but 1 steps` → the same. The jar answers this one
/// directly — the T-10a `NullPointerException` fires only when the translation
/// constant-folds (P-077-4), not for every one-state `check`.
#[test]
fn a_check_at_a_one_state_bound_finds_its_one_state_counterexample() {
    let src = "var sig Flag {}\nassert AlwaysSome { always some Flag }\ncheck AlwaysSome for 2 but 1 steps\n";
    let t = trace(src, 0);
    assert_eq!(t.k(), 1, "the counterexample is a single state");
    assert_eq!(t.loop_state, 0, "a 1-state lasso loops on state 0");
}

/// **P-077-2** — the dual boundary: an assertion that holds on *every* one-state
/// trace is VALID-within-1-step and only fails once the bound admits a second
/// state. On a self-loop `after X` is `X`, so `some Flag implies after some Flag`
/// is `X implies X`.
///
/// Jar cells (`fixtures/P2_HoldsAtOneFailsAtTwo.als`): `run notPersists for 2 but
/// 1 steps` → UNSAT and `check Persists for 2 but 1 steps` → UNSAT (the jar
/// answers both); `run notPersists for 2 but 2 steps` → SAT at `traceLength=2
/// loopState=1`, matching `check Persists for 2 but 2 steps`.
#[test]
fn a_check_holding_at_one_state_is_unsat_within_bound_and_fails_at_two() {
    let assertion =
        "var sig Flag {}\nassert Persists { always (some Flag implies after some Flag) }\n";
    let at_one = format!("{assertion}check Persists for 2 but 1 steps\n");
    assert_eq!(
        minimal_k(&at_one, 0),
        None,
        "no counterexample within 1 step"
    );
    let at_two = format!("{assertion}check Persists for 2 but 2 steps\n");
    assert_eq!(
        minimal_k(&at_two, 0),
        Some(2),
        "it takes two states to fail"
    );
}

/// **P-077-3** — every temporal operator collapses at a one-state self-loop:
/// `after X` ≡ `eventually X` ≡ `always X` ≡ `once X` ≡ `historically X` ≡ `X`,
/// `X until Y` ≡ `Y`, and `before X` is false.
///
/// Jar cell (`fixtures/P3b_OperatorEvalAtSelfLoop.als`): each operator evaluated
/// on a solved single-state instance, once with `Flag` nonempty and once empty —
/// positive evidence, because the equivalence-negation form constant-folds hard
/// enough to trip the jar's own `maxtrace == 1` crash (P-077-4). Here the same
/// equivalences are asserted the way mettle can check them jar-free: each
/// collapsed form is UNSAT to violate at `k = 1`.
#[test]
fn the_temporal_operators_collapse_at_a_one_state_self_loop() {
    let sig = "var sig Flag {}\n";
    // `not (op iff collapsed)` must be unsatisfiable at a one-state bound.
    for (op, collapsed) in [
        ("after some Flag", "some Flag"),
        ("eventually some Flag", "some Flag"),
        ("always some Flag", "some Flag"),
        ("once some Flag", "some Flag"),
        ("historically some Flag", "some Flag"),
        ("(some Flag) until (no Flag)", "no Flag"),
    ] {
        let src = format!("{sig}run {{ not (({op}) iff ({collapsed})) }} for 2 but 1 steps\n");
        assert_eq!(
            minimal_k(&src, 0),
            None,
            "`{op}` does not collapse to `{collapsed}`"
        );
    }
    // `before` has no predecessor at state 0, so it is false there whatever the
    // state holds — unsatisfiable, and its negation trivially satisfiable.
    let holds = format!("{sig}run {{ before some Flag }} for 2 but 1 steps\n");
    assert_eq!(minimal_k(&holds, 0), None, "`before` held at state 0");
    let fails = format!("{sig}run {{ not (before some Flag) }} for 2 but 1 steps\n");
    assert_eq!(minimal_k(&fails, 0), Some(1));
}

/// **P-077-5** — the three spellings of a `[1, 1]` steps range share one code
/// path (the *resolved* bound, not the surface syntax), so all three answer.
///
/// Jar cell (`fixtures/P5_Spellings.als`): `1 steps`, `exactly 1 steps` and
/// `1..1 steps` all report `mintrace=1 maxtrace=1` and all three `check`s come
/// back `sat=true traceLength=1 loopState=0`.
#[test]
fn every_spelling_of_a_one_state_bound_answers() {
    let assertion = "var sig Flag {}\nassert AlwaysSome { always some Flag }\n";
    for clause in ["1 steps", "exactly 1 steps", "1..1 steps"] {
        let src = format!("{assertion}check AlwaysSome for 2 but {clause}\n");
        assert_eq!(minimal_k(&src, 0), Some(1), "{clause}");
    }
}

/// **mt-077, jar-free** — the negation dual is the internal invariant the whole
/// decision rests on: `check P` *is* `run { not P }`, so mettle's own verdicts
/// for the two must be exact opposites at the same one-state bound. This test
/// needs no oracle — it catches a `check`-only regression in the sweep that a
/// jar-cited constant could not.
#[test]
fn a_one_state_check_is_the_negation_dual_of_its_run() {
    let sig = "var sig Flag {}\n";
    for goal in [
        "always some Flag",
        "always (some Flag implies after some Flag)",
        "eventually no Flag",
        "(some Flag) until (no Flag)",
        "before some Flag",
    ] {
        let checked = format!("{sig}assert P {{ {goal} }}\ncheck P for 2 but 1 steps\n");
        let dual = format!("{sig}run {{ not ({goal}) }} for 2 but 1 steps\n");
        assert_eq!(
            minimal_k(&checked, 0).is_some(),
            minimal_k(&dual, 0).is_some(),
            "`check {{ {goal} }}` and `run {{ not ({goal}) }}` disagree at a one-state bound"
        );
    }
}

// ==================== the trace: loop target + per-state ====================

/// The mt-066 alternation gadget, which forces `traceLength = 2, loopState = 0`
/// (probe P-D2's fixture): at state 1 `some A` holds, so its successor must have
/// `no A` — only state 0 qualifies, so the back-loop can only target 0.
const ALTERNATE: &str = "var sig A {}\nvar sig B {}\n\
     fact Alternate {\n\
       no A\n\
       always ((some A) implies (after (no A)))\n\
       always ((no A) implies (after (some A)))\n\
     }\n";

/// The loop target is recovered from the solved model, not guessed: on a fixture
/// that forces the back-edge, the driver reports exactly that state.
#[test]
fn the_loop_target_is_recovered_from_the_solved_model() {
    let t = trace(
        &format!("{ALTERNATE}run {{ some univ }} for 2 but exactly 2 steps\n"),
        0,
    );
    assert_eq!(t.k(), 2);
    assert_eq!(t.loop_state, 0, "P-D2's gadget forces the back-edge to 0");
    // Every lasso has a valid target — there is no non-looping trace in this
    // engine (alloy6-temporal.md §(c)).
    assert!(t.loop_state < t.k());
}

/// A solved trace normalizes an evaluator's state index by the pinned rule
/// (alloy6-temporal.md §(h), probes T-22/T-23): past the end it wraps through
/// the loop, below zero it clamps, and it is never an error.
#[test]
fn a_solved_trace_normalizes_an_evaluator_state_index() {
    let t = trace(
        &format!("{ALTERNATE}run {{ some univ }} for 2 but exactly 2 steps\n"),
        0,
    );
    assert_eq!((t.k(), t.loop_state), (2, 0));
    let at = |state| t.normalize_state(state);
    assert_eq!((at(0), at(1)), (0, 1));
    assert_eq!((at(2), at(3), at(10)), (0, 1, 0), "wraps through the loop");
    assert_eq!((at(-1), at(-9), at(i64::MIN)), (0, 0, 0), "clamps at zero");
}

/// A one-state trace can only self-loop (P-C1/P-C2: the only state's successor
/// is itself).
#[test]
fn a_one_state_trace_loops_onto_itself() {
    let t = trace(
        "var sig A {}\nrun { some A } for 2 but exactly 1 steps\n",
        0,
    );
    assert_eq!((t.k(), t.loop_state), (1, 0));
}

/// The per-state decode: a static relation is byte-identical in every state
/// (probe T-13 — rigid content is re-emitted per state, never factored out),
/// while a `var` relation carries that state's own value. Both are keyed by the
/// **original** relation ids, so no `name@s` copy is ever visible.
#[test]
fn the_trace_decodes_statics_rigidly_and_vars_per_state() {
    let src = "sig S {}\nvar sig A in S {}\n\
               run { (no A) and (after (some A)) } for 2 but exactly 2 steps\n";
    let b = build(src, 0);
    let s = rel_named(&b.ir, "this/S");
    let a = rel_named(&b.ir, "this/A");
    let t = trace(src, 0);
    assert_eq!(t.k(), 2);

    for state in &t.states {
        assert!(state.get(s).is_some(), "the static sig is in every state");
        assert!(state.get(a).is_some(), "the var sig is in every state");
    }
    assert_eq!(
        t.states[0].get(s),
        t.states[1].get(s),
        "atoms are rigid: a static relation cannot change between states"
    );
    assert!(
        t.states[0]
            .get(a)
            .is_some_and(als_core::bounds::TupleSet::is_empty),
        "the goal forces `no A` at state 0"
    );
    assert!(
        t.states[1].get(a).is_some_and(|ts| !ts.is_empty()),
        "the goal forces `some A` at state 1"
    );
    // The per-state copies themselves never reach the rendered trace.
    for state in &t.states {
        for (rel, _) in state.iter() {
            assert!(
                !b.ir.relations[rel].name.contains('@'),
                "a per-state copy leaked into the trace: {}",
                b.ir.relations[rel].name
            );
        }
    }
}

/// The self-check is green on every SAT fixture: a solved trace re-evaluates to
/// `true` against its own lowered goal, with `LoopIs` resolved through the
/// recovered loop target (mt-067 closed mt-066's gap here).
#[test]
fn the_temporal_self_check_passes_on_solved_traces() {
    let fixtures = [
        format!("{AB}run {{ (no A) and (after (some A)) }} for 2\n"),
        format!("{ALTERNATE}run {{ always (some B) }} for 2 but exactly 2 steps\n"),
        "var sig A {}\nrun { some A } for 2 but exactly 1 steps\n".to_owned(),
        "sig S {}\nvar sig A in S {}\nrun { eventually (some A) } for 3 but 4 steps\n".to_owned(),
    ];
    for src in &fixtures {
        // `trace` asserts `self_check.is_none()`; debug builds also assert it
        // inside the driver.
        let _ = trace(src, 0);
    }
}

// ==================== (d) per-state symmetry breaking ====================

/// Symmetry breaking is verdict-neutral under time, exactly as it is statically:
/// the lex-leader predicate is Tseitin-only and soft-capped, so switching it on
/// or off can change neither the verdict nor the minimal trace length.
#[test]
fn per_state_symmetry_breaking_is_verdict_neutral() {
    let fixtures = [
        format!("{AB}run {{ (no A) and (after (some A)) }} for 3\n"),
        format!("{ALTERNATE}run {{ some univ }} for 3 but exactly 2 steps\n"),
        "sig S {}\nvar sig A in S {}\nrun { eventually (some A) } for 3 but 4 steps\n".to_owned(),
        "var sig A {}\nassert NeverA { always (no A) }\ncheck NeverA for 3 but 4 steps\n"
            .to_owned(),
        format!("{AB}run {{ (no A) and (no A') and (some A'') }} for 2 but 2 steps\n"),
    ];
    for src in &fixtures {
        let broken = drive(src, 0, 20).expect("symmetry 20");
        let unbroken = drive(src, 0, 0).expect("symmetry 0");
        let shape = |v: &TemporalVerdict| match v {
            TemporalVerdict::Sat(t) => Some(t.k()),
            TemporalVerdict::Unsat => None,
            other => panic!("expected a verdict, got {other:?}"),
        };
        assert_eq!(shape(&broken), shape(&unbroken), "{src}");
    }
}

/// STYLE U4/D1: the same command drives to a byte-identical trace on a fresh
/// run, at both symmetry settings — per-state SBP generation adds no
/// nondeterminism.
#[test]
fn the_driver_is_deterministic_at_both_symmetry_settings() {
    let src = format!("{ALTERNATE}run {{ always (some B) }} for 3 but 3 steps\n");
    for symmetry in [20, 0] {
        let a = format!("{:?}", drive(&src, 0, symmetry).expect("drive"));
        let b = format!("{:?}", drive(&src, 0, symmetry).expect("drive"));
        assert_eq!(a, b, "symmetry {symmetry}");
    }
}

// ============================== budget honesty ==============================

/// A length that ends in a budget/capacity outcome makes the **whole command**
/// that outcome — never UNSAT-within-bound over a range with a hole in it.
#[test]
fn an_inconclusive_length_never_becomes_unsat() {
    let src = "sig S {}\nvar sig A in S {}\nrun { eventually (some A) } for 3 but 4 steps\n";
    let mut b = build(src, 0);
    let capped = TemporalSolveConfig {
        primary_var_cap: Some(0),
        ..cfg(20)
    };
    let v = solve_temporal_command(
        &b.world, &b.graph, &b.scoped, &b.bounds, &mut b.ir, 0, &capped,
    )
    .expect("driver");
    assert!(
        matches!(v, TemporalVerdict::PrimaryVarCap { k: 1, .. }),
        "{v:?}"
    );

    let mut b = build(src, 0);
    let starved = TemporalSolveConfig {
        opts: SolveOptions {
            encode_budget: Some(1),
            ..cfg(20).opts
        },
        ..cfg(20)
    };
    let e = solve_temporal_command(
        &b.world, &b.graph, &b.scoped, &b.bounds, &mut b.ir, 0, &starved,
    )
    .expect_err("encode budget");
    assert!(
        matches!(e, TranslateError::CapacityExceeded { .. }),
        "{e:?}"
    );
}

// ===================== `;` ends the binder body (mt-116) =====================
//
// `;` desugars to `lhs and after rhs`, so a command carrying one is temporal
// (mt-069 K3) and lands in this driver. Where the `;` sits relative to an
// enclosing binder is therefore a **verdict** question, not a diagnostic one:
// cells g05/g06 of the mt-116 wave (`scratchpad/probe/mt116/NOTES.md`) are the
// pair that separates the two readings, both UNSAT against the reference jar
// (`scratchpad/probe/mt069/PerCommandProbe.java`, jar defaults symmetry=20
// noOverflow=false sat4j).

/// **Cell g06** — the control: with no binder in scope, `;` is the plain
/// top-level sequencing both tools always agreed on. `some A ; no A` at
/// `exactly 1 A` cannot hold, in either reading.
#[test]
fn top_level_sequencing_solves_unsat_mt116() {
    let src = "sig A {}\npred P { some A; no A }\nrun P for exactly 1 A\n";
    assert_eq!(minimal_k(src, 0), None, "{src}");
}

/// **Cell g05 — the witness.** `pred P { all u: A - A | some u; no A }` at
/// `exactly 2 A`. `A - A` is empty, so the two readings of the `;` disagree on
/// the *verdict*, not just on a diagnostic: with the `no A` folded inside the
/// body (mettle's parse before mt-116) the whole formula is vacuously true and
/// mettle returned SAT with `A = {A$0, A$1}`; with the body ending at the `;`
/// the run reduces to `after no A` alongside a vacuous quantifier, which cannot
/// hold at `exactly 2 A`. The jar answers UNSAT.
#[test]
fn a_seq_after_a_vacuous_quantifier_solves_unsat_mt116() {
    let src = "sig A {}\npred P { all u: A - A | some u; no A }\nrun P for exactly 2 A\n";
    assert_eq!(minimal_k(src, 0), None, "{src}");
}
