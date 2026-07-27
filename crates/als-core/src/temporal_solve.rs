//! The **temporal solve driver** (ADR-0015 decision 3, mt-067): sweep the
//! command's `steps` range ascending, first SAT wins.
//!
//! [`solve_temporal_command`] is the entry point every temporal caller uses —
//! `mettle exec` and the conformance solve-gauge share it, so "what a temporal
//! verdict means" is decided in exactly one place. Given a command the pinned
//! discriminator ([`als_types::is_temporal_model`]) called temporal, it runs
//!
//! ```text
//! for k in [mintrace, maxtrace]:          # ascending
//!     unroll(bounds, k)                   # per-state relation copies (mt-065)
//!     lower_temporal_command(.., k)       # LTL-on-lasso at that length (mt-066)
//!     encode + solve                      # one deterministic CNF per length
//!     if SAT: return the k-state lasso trace
//! return UNSAT-within-bound
//! ```
//!
//! which is `TemporalPardinusSolver.solve`'s own loop (alloy6-temporal.md
//! §(c), bytecode-confirmed): **the returned trace is the minimal satisfying
//! length**, not the maximum available (probes T-09/T-10b).
//!
//! # What the verdicts mean, exactly
//!
//! - [`TemporalVerdict::Sat`] carries the whole trace: `k` states, the back-loop
//!   target `l ∈ [0, k)`, and per-state relation values. Every SAT temporal
//!   instance is a lasso — a finite non-looping trace does not exist in this
//!   engine (§(c); the loop selector is part of the encoding by construction).
//! - [`TemporalVerdict::Unsat`] is **UNSAT-within-bound** and nothing stronger:
//!   "no instance / no counterexample up to `maxtrace` states". Raising the
//!   bound can flip it (probe T-10b: the same `check` is UNSAT `for 2 steps`
//!   and SAT `for 3 steps`). It is *not* "the assertion holds".
//! - [`TemporalVerdict::Unknown`] / [`TemporalVerdict::PrimaryVarCap`] are not
//!   verdicts at all. A budget or capacity outcome **at any single length**
//!   makes the whole command that outcome: skipping an inconclusive length and
//!   continuing would let the sweep report UNSAT-within-bound for a range it
//!   never actually searched (STYLE E5 — never a wrong verdict).
//!
//! One `steps` shape never reaches the loop: `1..` (open above) is the typed
//! defer [`TranslateError::UnboundedSteps`] (see that variant's docs).
//!
//! # The one-state bound (`for 1 steps`) is answered, not refused (mt-077)
//!
//! A `k == 1` trace is an ordinary lasso whose only state is its own loop
//! target, so the sweep handles it with no special case: every future operator
//! collapses to "now" (`after X` ≡ `eventually X` ≡ `always X` ≡ `X`,
//! `X until Y` ≡ `Y`), `before X` is false, and `once`/`historically` collapse
//! to "now" as well — all jar-confirmed by evaluating each operator on a solved
//! single-state instance (probe P-077-3).
//!
//! The jar cannot always be asked directly: a temporal command whose translation
//! constant-folds at `maxtrace == 1` dies with a `NullPointerException` instead
//! of answering (probes T-10a/T-11, re-pinned and **narrowed** by P-077-4 —
//! the crash is not `check`-specific, plain `run`s trip it too). Where the jar
//! does answer, mettle agrees (P-077-1/2/5); where it crashes, mettle answers
//! the negation-dual the jar itself computes fine, since `check P` is the
//! negated `run { not P }`.
//!
//! # Determinism and cost
//!
//! Every length is a fresh, independent encode+solve — no incrementality across
//! lengths (ADR-0015: correct first). The sweep is a pure function of the
//! command, so the trace, the verdict and the CNF are byte-reproducible; nothing
//! here reads a clock or iterates a hash container.
//!
//! The per-length work accumulates in the shared [`Ir`] arena: length `k`
//! allocates its own `k` copies per variable relation and its own lowered
//! branches, and earlier lengths' nodes stay allocated (arenas are append-only).
//! That is deliberate — the alternative, a fresh `Ir` per length, would
//! invalidate the [`RelId`](crate::ir::RelId)s the caller's `bounds` already
//! hold. Only the *current* length's copies are ever bound, so a stale copy
//! mints no primary variable and cannot enter a CNF.

use als_types::{is_temporal_model, ModuleGraph, ResolvedWorld, StepsMax};

use crate::bounds_builder::BoundsResult;
use crate::error::TranslateError;
use crate::eval::SelfCheckFailure;
use crate::ir::Ir;
use crate::lower::LoweredGoal;
use crate::scope::ScopedUniverse;
use crate::solve::{solve_temporal_goal_checked, Instance, SolveOptions, TemporalSolution};
use crate::temporal::{unroll, UnrolledBounds};
use crate::temporal_lower::lower_temporal_command;

/// The driver's knobs: the ordinary per-solve [`SolveOptions`] plus the two
/// things that only make sense **per trace length**.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct TemporalSolveConfig {
    /// Per-length solver options. [`SolveOptions::conflict_budget`] and
    /// [`SolveOptions::encode_budget`] are charged afresh at every length —
    /// they bound one encode+solve, and each length is one.
    pub opts: SolveOptions,
    /// Ceiling on a single length's primary-variable count, checked against the
    /// **unrolled** bounds before lowering; `None` = no ceiling. The static
    /// pipeline's equivalent guard lives in the gauge, which computes it from
    /// the un-unrolled bounds; unrolling multiplies the variable relations by
    /// `k`, so the honest place to apply it is inside the sweep.
    pub primary_var_cap: Option<usize>,
    /// Re-evaluate a solved trace against its own lowered goal in **any** build
    /// (the gauge's release-mode net). Debug builds assert it regardless.
    pub self_check: bool,
}

/// A solved lasso trace: `k` states plus the back-loop target.
///
/// The shape mirrors the jar's `TemporalInstance` (`states: List<Instance>`,
/// `loop: int`): the infinite trace is `0, 1, …, k−1, l, l+1, …, k−1, l, …`.
/// Each state is a full [`Instance`] keyed by the **original**
/// [`RelId`](crate::ir::RelId)s — the per-state copies are decoded back through
/// [`UnrolledBounds::states`], so a renderer never sees a `name@s` relation.
/// Static relations (including skolems, which are rigid under temporal
/// operators — probe P-F1) carry byte-identical values in every state.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TemporalTrace {
    /// One [`Instance`] per state, index-ascending; never empty.
    pub states: Vec<Instance>,
    /// The back-loop target, `< states.len()`.
    pub loop_state: usize,
    /// The self-check's verdict when [`TemporalSolveConfig::self_check`] was
    /// set: a failure means the solved trace does not satisfy its own lowered
    /// goal — a mettle bug, never a user error (ADR-0011 decision 5).
    pub self_check: Option<SelfCheckFailure>,
    /// What a post-solve **per-state evaluator** needs beyond the rendered
    /// states (mt-068) — kept because the winning length's artifacts are alive
    /// here anyway and cannot be rebuilt afterwards without re-solving (a second
    /// `lower_temporal_command` would mint *different* skolem relations, which
    /// nothing ever assigned).
    ///
    /// Boxed so that a [`TemporalVerdict`] stays cheap to move and match on: the
    /// evaluation view is several hundred bytes that only the REPL ever reads.
    pub artifacts: Box<TraceArtifacts>,
}

/// The winning trace length's solve artifacts, kept for the REPL (mt-068).
///
/// [`TemporalTrace::states`] is the *rendering* view (original relation ids, one
/// instance per state); this is the *evaluation* view — the flat instance and
/// the unrolled bounds the lowered fragments actually resolve against.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TraceArtifacts {
    /// The winning length's unrolled view: the bridge from an original variable
    /// relation to its per-state copies, plus those copies' bounds.
    pub unrolled: UnrolledBounds,
    /// The **flat** solved instance — per-state copies as ordinary relations,
    /// exactly as the encoder and the self-check saw them.
    pub instance: Instance,
    /// The goal lowered at the winning length. Only its skolem bounds and
    /// builtin-`Int` relation ids matter downstream (an evaluator context binds
    /// the same relations the solve did), but keeping the whole goal costs
    /// nothing and keeps the shape identical to the static path's.
    pub goal: LoweredGoal,
}

impl TemporalTrace {
    /// The trace length `k` (number of states).
    #[must_use]
    pub fn k(&self) -> usize {
        self.states.len()
    }

    /// Normalizes an evaluator's `state` argument onto this trace
    /// ([`normalize_state`] against this trace's own length and loop target).
    #[must_use]
    pub fn normalize_state(&self, state: i64) -> usize {
        normalize_state(state, self.k(), self.loop_state)
    }
}

/// The pinned evaluator state-index rule (alloy6-temporal.md §(h), probes
/// T-22/T-23/T-25): **never an error**.
///
/// - `state ∈ [0, k)` is that literal state;
/// - `state >= k` **wraps through the loop**:
///   `((state − l) % (k − l)) + l`, `TemporalInstance.normalizedIndex`'s own
///   formula, which `A4Solution.toString(int state)` applies inline too
///   (`scratchpad/src794/A4Solution.java:1794-1795`);
/// - `state < 0` **clamps to 0** — jar-verified behavior on every eval path
///   probed (a naive read of the bytecode says it should throw; it does not).
///
/// Written as the jar writes it (`Math.max(0, state)` then the `state > l`
/// guard) rather than as the equivalent "if `state >= k`" so the two stay
/// visibly the same rule.
///
/// # Panics
/// Panics if `k == 0` or `loop_state >= k` — a solved lasso always has at least
/// one state and an in-range back-loop target (STYLE I5: internal invariants,
/// while `state` itself is user input and is therefore normalized, not asserted).
#[must_use]
pub fn normalize_state(state: i64, k: usize, loop_state: usize) -> usize {
    assert!(k >= 1, "a trace has at least one state, got k={k}");
    assert!(
        loop_state < k,
        "loop target outside the trace: loop_state={loop_state} k={k}"
    );
    // `max(0)` is the clamp; the conversion cannot fail on any 64-bit target
    // (and saturating rather than erroring keeps the "never an error" rule on a
    // hypothetical 32-bit one, where such an index wraps into the loop anyway).
    let clamped = usize::try_from(state.max(0)).unwrap_or(usize::MAX);
    let normalized = if clamped > loop_state {
        ((clamped - loop_state) % (k - loop_state)) + loop_state
    } else {
        clamped
    };
    debug_assert!(
        normalized < k,
        "normalized state escaped the trace: {normalized} not in [0,{k})"
    );
    normalized
}

/// A temporal command's outcome (see the module docs for what each *means*).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TemporalVerdict {
    /// Satisfiable at the **minimal** length in the `steps` range.
    Sat(TemporalTrace),
    /// No instance / no counterexample at any length in the range —
    /// UNSAT-**within-bound**, never "unsatisfiable".
    Unsat,
    /// [`SolveOptions::conflict_budget`] ran out at trace length `k`, so the
    /// range was never fully searched. Not a verdict.
    Unknown {
        /// The length whose solve gave up.
        k: usize,
    },
    /// Trace length `k`'s unrolled bounds outgrew
    /// [`TemporalSolveConfig::primary_var_cap`]. Not a verdict.
    PrimaryVarCap {
        /// The length that outgrew the cap.
        k: usize,
        /// Its primary-variable count.
        primaries: usize,
    },
}

/// Solves one **temporal** command over its whole `steps` range (ADR-0015
/// decision 3).
///
/// `command_index` indexes [`ResolvedWorld::commands`]; `bounds` is that
/// command's ordinary static bounds ([`crate::compute_bounds`]) — the sweep
/// unrolls them per length itself. `ir` is the arena those bounds were built
/// into and grows as the sweep proceeds (module docs).
///
/// # Errors
/// - [`TranslateError::UnboundedSteps`] for a `1..` (open-above) `steps` scope —
///   the reference's bounded engine refuses it (probe T-08b).
/// - Anything [`lower_temporal_command`] or the encoder can raise, including
///   [`TranslateError::CapacityExceeded`] when a length outgrows
///   [`SolveOptions::encode_budget`].
///
/// # Panics
/// Debug builds assert that `command_index` really is a temporal command — the
/// caller owns that dispatch, and running a static command through the lasso
/// encoding would silently waste `k` solves on a `k`-invariant problem.
pub fn solve_temporal_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    bounds: &BoundsResult,
    ir: &mut Ir,
    command_index: usize,
    cfg: &TemporalSolveConfig,
) -> Result<TemporalVerdict, TranslateError> {
    let command = &world.commands[command_index];
    debug_assert!(
        is_temporal_model(world, graph, command),
        "solve_temporal_command on a static command — dispatch is the caller's job"
    );

    let range = command.steps_range();
    let max = match range.max {
        // `for 1.. steps`: the jar's `maxprefix = Integer.MAX_VALUE` sets
        // `setRunUnbounded(true)`, and the default bounded engine throws before
        // any solving (probe T-08b). mettle matches the jar-without-electrod.
        StepsMax::Unbounded => {
            return Err(TranslateError::UnboundedSteps {
                span: steps_span(world, command_index),
            })
        }
        StepsMax::Bounded(max) => max,
    };

    // `max == 1` is deliberately NOT special-cased (mt-077): a one-state lasso
    // is an ordinary trace, and refusing it would diverge from the jar on every
    // such command the jar answers cleanly (module docs).
    for k in range.min..=max {
        let k = k as usize;
        let unrolled = unroll(ir, &bounds.bounds, k);
        if let Some(cap) = cfg.primary_var_cap {
            let primaries = primary_var_count(&unrolled);
            if primaries > cap {
                return Ok(TemporalVerdict::PrimaryVarCap { k, primaries });
            }
        }
        let goal = lower_temporal_command(
            world,
            graph,
            scoped,
            bounds,
            ir,
            command_index,
            k,
            &unrolled,
        )?;
        match solve_temporal_goal_checked(
            ir,
            scoped,
            &goal,
            bounds,
            &unrolled,
            &cfg.opts,
            cfg.self_check,
        )? {
            TemporalSolution::Unsat => {}
            // An inconclusive length poisons the whole sweep: continuing would
            // let a later exhaustion report UNSAT over a range with a hole in it.
            TemporalSolution::Unknown => return Ok(TemporalVerdict::Unknown { k }),
            TemporalSolution::Sat {
                instance,
                loop_state,
                self_check,
            } => {
                let states = split_states(&unrolled, &instance);
                return Ok(TemporalVerdict::Sat(TemporalTrace {
                    states,
                    loop_state,
                    self_check,
                    artifacts: Box::new(TraceArtifacts {
                        unrolled,
                        instance,
                        goal,
                    }),
                }));
            }
        }
    }
    Ok(TemporalVerdict::Unsat)
}

/// The primary-variable count one trace length's unrolled bounds imply
/// (`Σ upper − lower`), mirroring the gauge's static guard.
fn primary_var_count(unrolled: &UnrolledBounds) -> usize {
    unrolled
        .bounds
        .iter()
        .map(|(_, b)| b.upper().len() - b.lower().len())
        .sum()
}

/// Splits the flat solved instance (per-state copies as ordinary relations) into
/// one [`Instance`] per state, keyed by the **original** relation ids.
///
/// A static relation is copied into every state unchanged — the jar renders
/// exactly the same way (probe T-13: non-`var` sigs, builtins included, are
/// re-emitted byte-identically in every `<instance>` block, with no
/// factoring-out of rigid content).
fn split_states(unrolled: &UnrolledBounds, flat: &Instance) -> Vec<Instance> {
    let copies: std::collections::BTreeSet<crate::ir::RelId> = unrolled
        .states
        .values()
        .flat_map(|cs| cs.iter().copied())
        .collect();
    // The statics, once — identical in every state by construction.
    let statics: Vec<(crate::ir::RelId, crate::bounds::TupleSet)> = flat
        .iter()
        .filter(|(rel, _)| !copies.contains(rel))
        .map(|(rel, ts)| (rel, ts.clone()))
        .collect();

    (0..unrolled.k)
        .map(|state| {
            let mut rels = statics.clone();
            for (&original, cs) in &unrolled.states {
                let copy = cs[state];
                let Some(value) = flat.get(copy) else {
                    // Every copy is bound, and `decode` covers every bounded
                    // relation, so a miss is a layout bug (STYLE I3).
                    unreachable!("solved instance is missing a per-state copy: {copy:?}")
                };
                rels.push((original, value.clone()));
            }
            Instance::from_relations(flat.universe.clone(), rels)
        })
        .collect()
}

/// The span to blame for a `steps`-scope defer: the scope entry when one was
/// written, else the command itself (a defaulted range).
fn steps_span(world: &ResolvedWorld, command_index: usize) -> als_syntax::Span {
    let command = &world.commands[command_index];
    command.steps.map_or(command.span, |s| s.span)
}

#[cfg(test)]
mod tests {
    use super::normalize_state;

    /// alloy6-temporal.md §(h) / probe T-22: on the wave-2 fixture's own trace
    /// (`traceLength=3, loopState=2` — the T-13 shape), every index `>= 3`
    /// wraps onto state 2, which is *not* what a plain `% k` would give.
    #[test]
    fn indices_past_the_end_wrap_through_the_loop() {
        let t13 = |state| normalize_state(state, 3, 2);
        assert_eq!((t13(0), t13(1), t13(2)), (0, 1, 2));
        assert_eq!((t13(3), t13(4), t13(10)), (2, 2, 2));
        assert_ne!(
            t13(3),
            3 % 3,
            "the loop, not the trace length, is the period"
        );

        // A two-state loop inside a three-state trace: the period is `k - l`.
        let span2 = |state| normalize_state(state, 3, 1);
        assert_eq!(
            (span2(3), span2(4), span2(5), span2(6)),
            (1, 2, 1, 2),
            "((state - l) % (k - l)) + l"
        );

        // Loop at state 0: the wrap degenerates to the plain modulo.
        let from_zero = |state| normalize_state(state, 2, 0);
        assert_eq!((from_zero(2), from_zero(3), from_zero(4)), (0, 1, 0));

        // The degenerate single-state trace absorbs everything.
        for state in [0, 1, 7, i64::MAX] {
            assert_eq!(normalize_state(state, 1, 0), 0);
        }
    }

    /// §(h) / probes T-23/T-25: a negative index **clamps to 0 and never
    /// errors** — jar-verified behavior on every eval path probed, including the
    /// one a naive reading of the bytecode says should throw.
    #[test]
    fn negative_indices_clamp_to_the_initial_state() {
        for state in [-1, -2, -5, -100, i64::MIN] {
            assert_eq!(normalize_state(state, 3, 2), 0);
            assert_eq!(normalize_state(state, 2, 0), 0);
            assert_eq!(normalize_state(state, 1, 0), 0);
        }
    }

    /// Whatever the input, the answer is a real state of the trace — the
    /// property the REPL's "a state index is never an error" rests on.
    #[test]
    fn every_index_lands_inside_the_trace() {
        for k in 1..5usize {
            for loop_state in 0..k {
                for state in -6..12 {
                    assert!(normalize_state(state, k, loop_state) < k);
                }
                assert!(normalize_state(i64::MAX, k, loop_state) < k);
            }
        }
    }

    #[test]
    #[should_panic(expected = "a trace has at least one state")]
    fn a_zero_length_trace_is_a_caller_bug() {
        let _ = normalize_state(0, 0, 0);
    }

    #[test]
    #[should_panic(expected = "loop target outside the trace")]
    fn a_loop_target_outside_the_trace_is_a_caller_bug() {
        let _ = normalize_state(0, 2, 2);
    }
}
