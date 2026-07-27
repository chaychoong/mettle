//! Trace-enumeration conformance (mt-076): the reference GUI's five
//! exploration buttons, and the counting semantics behind them.
//!
//! **Jar-free.** Every expected number is a constant citing the mt-076 probe
//! that pinned it against the reference Alloy 6.2.0 jar; the harness
//! (`EnumProbe.java`), fixtures, predictions-before-run and verbatim jar output
//! live in `scratchpad/probe/mt076/` (gitignored, rerunnable via `run.sh`). The
//! prose contract is `docs/reference/alloy6-temporal.md` §(g)'s "The mt-076
//! probe wave" and §(i)'s correction.
//!
//! Every fixture here is the probe fixture verbatim, so a number that moves
//! here is a number that would move against the jar.

use std::fmt::Write as _;

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, BoundsResult, ScopedUniverse, SolveOptions,
    TemporalSolveConfig, TraceAdvance, TraceEnumerator, TraceStep, TranslateError,
};
use als_syntax::ArenaId as _;
use als_types::{resolve, MapLoader, ModuleGraph, ResolvedWorld};

// ================================ harness ================================

struct Built {
    world: ResolvedWorld,
    graph: ModuleGraph,
    scoped: ScopedUniverse,
    bounds: BoundsResult,
    ir: Ir,
}

fn build(src: &str, cmd: usize) -> Built {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph)
        .unwrap_or_else(|e| panic!("resolve failed: {e:?}"))
        .world;
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

fn cfg(symmetry: u32) -> TemporalSolveConfig {
    TemporalSolveConfig {
        opts: SolveOptions {
            symmetry,
            ..SolveOptions::default()
        },
        primary_var_cap: None,
        // The self-check runs in every build, so a trace that does not satisfy
        // its own goal is loud rather than silently counted.
        self_check: true,
    }
}

/// An enumerator over command `cmd` of `src`, plus the arena it was cloned from
/// (kept alive because the enumerator borrows the world it was built against).
struct Session {
    built: Built,
}

impl Session {
    fn new(src: &str, cmd: usize) -> Self {
        Session {
            built: build(src, cmd),
        }
    }

    fn open(&self, cmd: usize, symmetry: u32) -> TraceEnumerator<'_> {
        TraceEnumerator::new(
            &self.built.world,
            &self.built.graph,
            &self.built.scoped,
            &self.built.bounds,
            &self.built.ir,
            cmd,
            &cfg(symmetry),
        )
        .expect("enumerator")
    }

    fn open_with(&self, cmd: usize, cfg: &TemporalSolveConfig) -> TraceEnumerator<'_> {
        TraceEnumerator::new(
            &self.built.world,
            &self.built.graph,
            &self.built.scoped,
            &self.built.bounds,
            &self.built.ir,
            cmd,
            cfg,
        )
        .expect("enumerator")
    }
}

/// One trace, rendered the way the probe's `trace:` digest renders it: the
/// per-state value of every relation the model declares, plus the loop target.
/// Two traces compare equal here exactly when the jar's `toString(-1)` blocks do.
fn digest(trace: &als_core::TemporalTrace) -> String {
    let mut out = String::new();
    for (i, state) in trace.states.iter().enumerate() {
        let _ = write!(out, "s{i}{{");
        for (rel, ts) in state.iter() {
            let _ = write!(out, "{}={};", rel.index(), ts.len());
        }
        out.push_str("} ");
    }
    let _ = write!(out, "loop={}", trace.loop_state);
    out
}

/// Runs `NextPath` until the enumerator says the space is empty, returning every
/// trace's `(k, loop)` in order. Panics on a budget stop — a test that wants one
/// asks for it explicitly.
fn walk(en: &mut TraceEnumerator<'_>, cap: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for _ in 0..cap {
        match en.advance(TraceStep::NextPath).expect("advance") {
            TraceAdvance::Trace(t) => out.push((t.k(), t.loop_state)),
            TraceAdvance::Exhausted => return out,
            other => panic!("unexpected advance: {other:?}"),
        }
    }
    panic!("enumeration did not terminate within {cap} steps: {out:?}")
}

// ============================= the fixtures ==============================

/// `scratchpad/probe/mt076/fixtures/RangeExact2.als` — mt-064's `RangeEnum`
/// model pinned to one exact length.
const RANGE_EXACT_2: &str = "\
one sig X {}
var sig Flag in X {}
fact { no Flag }
fact { eventually Flag = X }
run {} for exactly 2 steps
";

/// `RangeExact3.als` — the same model at exactly 3 steps.
const RANGE_EXACT_3: &str = "\
one sig X {}
var sig Flag in X {}
fact { no Flag }
fact { eventually Flag = X }
run {} for exactly 3 steps
";

/// mt-064's `RangeEnum.als` (T-19's fixture): a genuine `1..3` range.
const RANGE_ENUM: &str = "\
one sig X {}
var sig Flag in X {}
fact { no Flag }
fact { eventually Flag = X }
run {} for 1..3 steps
";

/// `StaticMultiConfig.als` — three genuinely non-isomorphic configurations.
const STATIC_MULTI_CONFIG: &str = "\
sig X {}
var sig A in X {}
run { some X } for 3 but exactly 2 steps
";

/// `NoStaticFree.als` — every static relation exact-bounded.
const NO_STATIC_FREE: &str = "\
one sig X {}
var sig A in X {}
run { eventually some A } for exactly 3 steps
";

/// `StaticFreeOneConfig.als` — free static primaries, no non-isomorphic
/// alternate configuration.
const STATIC_FREE_ONE_CONFIG: &str = "\
sig X {}
var sig A in X {}
run { #X = 2 } for exactly 3 steps
";

// ======================== P-076-4: the duplicate unit ========================

/// P-076-4, first half: **within one length the loop target is part of the
/// solution's identity.** The jar reports exactly 2 solutions here whose
/// per-state contents are *identical* and which differ only in `loopState` — so
/// mettle's blocking clause must cover the lasso selector, not only the relation
/// primaries. Drop the selector from the blocking set and this test reports 1.
#[test]
fn the_loop_target_is_part_of_a_solutions_identity() {
    let s = Session::new(RANGE_EXACT_2, 0);
    let mut en = s.open(0, 20);
    let seen = walk(&mut en, 32);
    assert_eq!(
        seen.len(),
        2,
        "probe P-076-4: exactly 2 at k=2, got {seen:?}"
    );
    let loops: Vec<usize> = seen.iter().map(|&(_, l)| l).collect();
    assert_eq!(loops, vec![1, 0], "the two differ only in the loop target");
    assert!(seen.iter().all(|&(k, _)| k == 2));
}

/// P-076-4, second half: **at one exact length, two representations of the same
/// infinite trace are BOTH emitted.** `exactly 3 steps` gives 9 — all three
/// admissible `(Flag@1, Flag@2)` combinations times three loop targets —
/// including `({},{X},{X})` at `loop=2` and at `loop=1`, which denote the same
/// infinite trace `{} ({X})^ω`. A de-duplication that ran *within* a length
/// would report 7 here.
#[test]
fn within_one_length_duplicate_infinite_traces_are_both_emitted() {
    let s = Session::new(RANGE_EXACT_3, 0);
    let mut en = s.open(0, 20);
    let seen = walk(&mut en, 32);
    assert_eq!(
        seen.len(),
        9,
        "probe P-076-4: exactly 9 at k=3, got {seen:?}"
    );
}

/// P-076-4 / T-19 together: over a real `1..3` range the sweep gives **8** —
/// 2 at length 2, then only **6 of the 9** at length 3, because the three
/// missing ones denote infinite traces already emitted at length 2. This single
/// number is the whole across-length de-duplication contract.
#[test]
fn across_lengths_an_infinite_trace_is_emitted_once() {
    let s = Session::new(RANGE_ENUM, 0);
    let mut en = s.open(0, 20);
    let seen = walk(&mut en, 32);
    assert_eq!(seen.len(), 8, "probe P-076-4 / T-19: got {seen:?}");
    let lengths: Vec<usize> = seen.iter().map(|&(k, _)| k).collect();
    assert_eq!(
        lengths,
        vec![2, 2, 3, 3, 3, 3, 3, 3],
        "T-19: each length is exhausted before the next is entered"
    );
    assert_eq!(
        seen.len(),
        2 + 6,
        "9 raw length-3 solutions minus the 3 already shown at length 2"
    );
}

// ================== P-076-5: the configuration is held ==================

/// P-076-5, the wave's headline and the correction to §(i): plain `next()`
/// **never leaves the configuration the first solution landed on**. Three
/// configurations exist here (`|X|` = 1, 2, 3 — cardinality is
/// symmetry-invariant, so no SB collapses them), yet the enumeration is exactly
/// 8 traces: 4 per-state `A` combinations times 2 loop targets, all in one
/// configuration.
#[test]
fn plain_next_never_changes_the_configuration() {
    let s = Session::new(STATIC_MULTI_CONFIG, 0);
    let mut en = s.open(0, 20);
    let seen = walk(&mut en, 64);
    assert_eq!(seen.len(), 8, "probe P-076-5: got {seen:?}");
}

/// The same at `symmetry = 0`, which is what the SB-0 counting net runs: the
/// raw space there holds all seven non-empty subsets of a 3-atom `X`, and the
/// answer is still 8. This is the cell that rules out "it is just symmetry
/// breaking".
#[test]
fn the_configuration_is_held_at_symmetry_zero_too() {
    let s = Session::new(STATIC_MULTI_CONFIG, 0);
    let mut en = s.open(0, 0);
    let seen = walk(&mut en, 64);
    assert_eq!(seen.len(), 8, "probe P-076-5 at sym=0: got {seen:?}");
}

/// Every trace of one enumeration agrees on every static relation — stated
/// directly rather than inferred from the count, so the property survives a
/// fixture change.
#[test]
fn every_trace_of_one_enumeration_shares_one_configuration() {
    let s = Session::new(STATIC_MULTI_CONFIG, 0);
    let mut en = s.open(0, 20);
    let mut sizes: Option<usize> = None;
    loop {
        match en.advance(TraceStep::NextPath).expect("advance") {
            TraceAdvance::Trace(t) => {
                // `X` is the model's only static relation; its cardinality is
                // the configuration, and it may not move.
                let x = t.states[0]
                    .iter()
                    .map(|(_, ts)| ts.len())
                    .max()
                    .expect("some relation");
                match sizes {
                    None => sizes = Some(x),
                    Some(first) => assert_eq!(x, first, "the configuration moved mid-enumeration"),
                }
            }
            TraceAdvance::Exhausted => break,
            other => panic!("unexpected advance: {other:?}"),
        }
    }
    assert!(sizes.is_some(), "the fixture is SAT");
}

// =================== P-076-1: `fork(-1)` / "New Config" ===================

/// P-076-1, arm 1: with **no free static primary variables** there is nothing to
/// block, and the reference re-derives and re-displays the byte-identical
/// original. mettle answers it without solving, and says so in the type.
#[test]
fn new_config_on_a_model_with_no_free_statics_is_the_same_config() {
    let s = Session::new(NO_STATIC_FREE, 0);
    let mut en = s.open(0, 20);
    let TraceAdvance::Trace(first) = en.advance(TraceStep::NextPath).expect("advance") else {
        panic!("the fixture is SAT")
    };
    assert_eq!(
        en.advance(TraceStep::NextConfig).expect("advance"),
        TraceAdvance::SameConfig,
        "probe P-076-1: `one sig X` is exact-bounded, so there is nothing to block"
    );
    assert_eq!(
        en.current().map(digest),
        Some(digest(&first)),
        "the displayed trace is unchanged, exactly as the jar leaves it"
    );
}

/// P-076-1, arm 2: with free static primaries but no non-isomorphic alternate,
/// the block goes in and the configuration space really is empty.
#[test]
fn new_config_with_no_alternative_is_exhaustion_not_the_same_config() {
    let s = Session::new(STATIC_FREE_ONE_CONFIG, 0);
    let mut en = s.open(0, 20);
    assert!(matches!(
        en.advance(TraceStep::NextPath).expect("advance"),
        TraceAdvance::Trace(_)
    ));
    assert_eq!(
        en.advance(TraceStep::NextConfig).expect("advance"),
        TraceAdvance::Exhausted,
        "probe P-076-1: free static primaries, no alternate config"
    );
}

/// P-076-1, arm 3: three configurations, walked in turn and then exhausted —
/// the jar's `X={X$0}` → `{X$0,X$1}` → `{X$0,X$1,X$2}` → UNSAT chain. The
/// traces are asserted pairwise distinct, which is the observable that
/// separates "a new configuration" from "the same one again".
#[test]
fn new_config_walks_every_configuration_once() {
    let s = Session::new(STATIC_MULTI_CONFIG, 0);
    let mut en = s.open(0, 20);
    let TraceAdvance::Trace(first) = en.advance(TraceStep::NextPath).expect("advance") else {
        panic!("the fixture is SAT")
    };
    let mut configs = vec![digest(&first)];
    loop {
        match en.advance(TraceStep::NextConfig).expect("advance") {
            TraceAdvance::Trace(t) => configs.push(digest(&t)),
            TraceAdvance::Exhausted => break,
            other => panic!("unexpected advance: {other:?}"),
        }
        assert!(configs.len() <= 4, "did not terminate: {configs:?}");
    }
    assert_eq!(
        configs.len(),
        3,
        "probe P-076-1: |X| = 1, 2, 3 — three configurations, then UNSAT"
    );
    let mut unique = configs.clone();
    unique.sort();
    unique.dedup();
    assert_eq!(
        unique.len(),
        3,
        "no configuration is shown twice: {configs:?}"
    );
}

// ============ P-076-6: `fork(p)` / "New Init" and "New Fork" ============

/// P-076-6, the discriminating cell: `fact { no Flag }` pins state 0 to a single
/// value, so **"New Init" is exhaustion** — even though eight other solutions
/// with a different state 1 or 2 exist. A `fork` that only required the *trace*
/// to differ would return one of them; this is what proves state `p` itself is
/// the constraint.
#[test]
fn new_init_is_exhaustion_when_the_initial_state_is_pinned() {
    let s = Session::new(RANGE_EXACT_3, 0);
    let mut en = s.open(0, 20);
    assert!(matches!(
        en.advance(TraceStep::NextPath).expect("advance"),
        TraceAdvance::Trace(_)
    ));
    assert_eq!(
        en.advance(TraceStep::Fork { hold: 0 }).expect("advance"),
        TraceAdvance::Exhausted,
        "probe P-076-6: state 0 has exactly one admissible value"
    );
}

/// The prefix really is held byte-identical, and the forked state really does
/// differ — the T-20/T-21 property, restated as an assertion over states rather
/// than over a count.
#[test]
fn a_fork_holds_its_prefix_and_changes_the_forked_state() {
    let s = Session::new(RANGE_EXACT_3, 0);
    let mut en = s.open(0, 20);
    let TraceAdvance::Trace(before) = en.advance(TraceStep::NextPath).expect("advance") else {
        panic!("the fixture is SAT")
    };
    let TraceAdvance::Trace(after) = en.advance(TraceStep::Fork { hold: 1 }).expect("advance")
    else {
        panic!("probe P-076-6: state 1 has an alternative")
    };
    assert_eq!(
        before.states[0], after.states[0],
        "states before the fork point are byte-identical"
    );
    assert_ne!(
        before.states[1], after.states[1],
        "the forked state itself differs"
    );
}

/// `hold >= k` is exhaustion, because there is no state `hold` to force
/// different — which is exactly what "New Fork" on the last displayed state
/// means (`current + 1 == k`).
#[test]
fn new_fork_past_the_last_state_is_exhaustion() {
    let s = Session::new(RANGE_EXACT_3, 0);
    let mut en = s.open(0, 20);
    let TraceAdvance::Trace(t) = en.advance(TraceStep::NextPath).expect("advance") else {
        panic!("the fixture is SAT")
    };
    assert_eq!(t.k(), 3);
    for hold in [3usize, 4, 40] {
        assert_eq!(
            en.advance(TraceStep::Fork { hold }).expect("advance"),
            TraceAdvance::Exhausted,
            "probe P-076-6: no state {hold} to force different"
        );
    }
}

// ========================= budgets and defers =========================

/// Every long operation is bounded: a tiny cumulative effort budget stops the
/// enumeration **typed**, and the enumerator says the space was never shown
/// empty — so a count taken from it is a lower bound, never reported as exact.
#[test]
fn a_spent_budget_ends_the_enumeration_typed() {
    let s = Session::new(STATIC_MULTI_CONFIG, 0);
    let budgeted = TemporalSolveConfig {
        opts: SolveOptions {
            enum_effort_budget: Some(1),
            ..SolveOptions::default()
        },
        primary_var_cap: None,
        self_check: false,
    };
    let mut en = s.open_with(0, &budgeted);
    let mut advances = 0;
    loop {
        match en.advance(TraceStep::NextPath).expect("advance") {
            TraceAdvance::Trace(_) => advances += 1,
            TraceAdvance::BudgetExhausted => break,
            TraceAdvance::Exhausted => {
                panic!("a 1-unit budget cannot have proven the space empty")
            }
            other => panic!("unexpected advance: {other:?}"),
        }
        assert!(advances < 8, "the budget never bit");
    }
    assert!(
        en.budget_spent(),
        "the enumerator must report itself budget-stopped, not exhausted"
    );
    // And it stays stopped: a further click cannot quietly resume.
    assert_eq!(
        en.advance(TraceStep::NextPath).expect("advance"),
        TraceAdvance::BudgetExhausted
    );
}

/// A length whose unrolled bounds outgrow the cap is a typed non-answer, never
/// silent exhaustion — the same posture the sweep takes.
#[test]
fn a_length_past_the_primary_var_cap_is_typed_not_exhaustion() {
    let s = Session::new(STATIC_MULTI_CONFIG, 0);
    let capped = TemporalSolveConfig {
        primary_var_cap: Some(1),
        ..cfg(20)
    };
    let mut en = s.open_with(0, &capped);
    assert!(matches!(
        en.advance(TraceStep::NextPath).expect("advance"),
        TraceAdvance::PrimaryVarCap { .. }
    ));
}

/// The two typed defers the sweep raises are raised at construction, so a caller
/// cannot build an enumerator that could never answer.
#[test]
fn the_sweeps_typed_defers_are_refused_up_front() {
    let unbounded = "var sig A {}\nrun {} for 1.. steps\n";
    let s = Session::new(unbounded, 0);
    assert!(matches!(
        TraceEnumerator::new(
            &s.built.world,
            &s.built.graph,
            &s.built.scoped,
            &s.built.bounds,
            &s.built.ir,
            0,
            &cfg(20),
        ),
        Err(TranslateError::UnboundedSteps { .. })
    ));

    let check_at_one = "var sig A {}\nassert P { always some A }\ncheck P for exactly 1 steps\n";
    let s = Session::new(check_at_one, 0);
    assert!(matches!(
        TraceEnumerator::new(
            &s.built.world,
            &s.built.graph,
            &s.built.scoped,
            &s.built.bounds,
            &s.built.ir,
            0,
            &cfg(20),
        ),
        Err(TranslateError::TemporalCheckAtOneStep { .. })
    ));
}

/// An UNSAT command enumerates to nothing at once, and stays that way.
#[test]
fn an_unsat_command_is_immediately_exhausted() {
    let src = "var sig A {}\nfact { always some A }\nrun { always no A } for exactly 2 steps\n";
    let s = Session::new(src, 0);
    let mut en = s.open(0, 20);
    assert_eq!(
        en.advance(TraceStep::NextPath).expect("advance"),
        TraceAdvance::Exhausted
    );
    assert_eq!(
        en.advance(TraceStep::NextPath).expect("advance"),
        TraceAdvance::Exhausted
    );
    assert!(en.current().is_none());
}

/// The first trace an enumerator yields is the one the sweep yields — the
/// property `mettle serve` rests on when it shows a trace and then offers to
/// advance from it.
#[test]
fn the_first_enumerated_trace_is_the_sweeps_trace() {
    for src in [RANGE_ENUM, STATIC_MULTI_CONFIG, NO_STATIC_FREE] {
        let s = Session::new(src, 0);
        let mut b = build(src, 0);
        let swept = als_core::solve_temporal_command(
            &b.world,
            &b.graph,
            &b.scoped,
            &b.bounds,
            &mut b.ir,
            0,
            &cfg(20),
        )
        .expect("sweep");
        let als_core::TemporalVerdict::Sat(swept) = swept else {
            panic!("fixture is SAT")
        };
        let mut en = s.open(0, 20);
        let TraceAdvance::Trace(first) = en.advance(TraceStep::NextPath).expect("advance") else {
            panic!("fixture is SAT")
        };
        assert_eq!(
            digest(&swept),
            digest(&first),
            "the enumerator's first trace must be the sweep's"
        );
    }
}

/// A `NextPath` after a fork continues the **fork's** question — it does not
/// silently reopen the unrestricted length sweep.
///
/// `fork(p)` is pinned never to move the trace length (probe P-076-2), so a
/// restricted sweep that runs out is exhausted rather than widened. This is the
/// one place mt-076 chose a behavior the probes did not directly pin (the jar's
/// `next()`-after-`nextS` was not exercised); the conservative reading is the
/// one that cannot re-show a trace the user already saw.
#[test]
fn next_after_a_fork_stays_inside_the_forks_question() {
    let s = Session::new(STATIC_MULTI_CONFIG, 0);
    let mut en = s.open(0, 20);
    let TraceAdvance::Trace(first) = en.advance(TraceStep::NextPath).expect("advance") else {
        panic!("the fixture is SAT")
    };
    assert_eq!(first.k(), 2, "the minimal length");
    // Fork at state 1 of the 2-state trace, then walk the restriction dry.
    let mut seen = 0;
    let mut step = TraceStep::Fork { hold: 1 };
    loop {
        match en.advance(step).expect("advance") {
            TraceAdvance::Trace(t) => {
                assert_eq!(t.k(), 2, "a fork never moves the trace length");
                seen += 1;
            }
            TraceAdvance::Exhausted => break,
            other => panic!("unexpected advance: {other:?}"),
        }
        step = TraceStep::NextPath;
        assert!(seen < 8, "the restricted sweep did not terminate");
    }
    assert!(seen >= 1, "state 1 has an alternative to fork to");
}

/// A `NextConfig` after a fork lifts the restriction: the new configuration
/// gets the whole length range again.
#[test]
fn new_config_lifts_a_forks_restriction() {
    let s = Session::new(STATIC_MULTI_CONFIG, 0);
    let mut en = s.open(0, 20);
    assert!(matches!(
        en.advance(TraceStep::NextPath).expect("advance"),
        TraceAdvance::Trace(_)
    ));
    assert!(matches!(
        en.advance(TraceStep::Fork { hold: 0 }).expect("advance"),
        TraceAdvance::Trace(_)
    ));
    assert!(matches!(
        en.advance(TraceStep::NextConfig).expect("advance"),
        TraceAdvance::Trace(_)
    ));
    // …and the fresh configuration enumerates its own full path space rather
    // than staying inside the fork's one-state restriction. (The size is the
    // configuration's own, not the first one's: this fixture's second
    // configuration has a strictly larger `X`, so it has strictly more paths —
    // which is exactly the point.)
    let mut seen = 1;
    loop {
        match en.advance(TraceStep::NextPath).expect("advance") {
            TraceAdvance::Trace(_) => seen += 1,
            TraceAdvance::Exhausted => break,
            other => panic!("unexpected advance: {other:?}"),
        }
        assert!(seen <= 256, "did not terminate");
    }
    assert!(
        seen > 1,
        "the restriction was lifted, so more than the fork's answer is reachable"
    );
}
