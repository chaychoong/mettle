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
//! Two `steps` shapes never reach the loop, each a typed defer:
//! [`TranslateError::UnboundedSteps`] for `1..` and
//! [`TranslateError::TemporalCheckAtOneStep`] for the pinned `check`-at-one-state
//! jar bug (see those variants' docs).
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
}

impl TemporalTrace {
    /// The trace length `k` (number of states).
    #[must_use]
    pub fn k(&self) -> usize {
        self.states.len()
    }
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
/// - [`TranslateError::TemporalCheckAtOneStep`] for a `check` at a one-state
///   bound — the pinned jar `NullPointerException`, an open owner fork.
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

    // The pinned jar bug: any `check` whose resolved `maxtrace == 1` throws a
    // NullPointerException instead of answering (probes T-10a/T-11). mettle
    // cannot conform to a crash and the divergence is an open owner fork, so
    // the boundary is a typed defer naming the bug — not an answer.
    if matches!(command.kind, als_syntax::ast::CmdKind::Check) && max == 1 {
        return Err(TranslateError::TemporalCheckAtOneStep { span: command.span });
    }

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
                return Ok(TemporalVerdict::Sat(TemporalTrace {
                    states: split_states(&unrolled, &instance),
                    loop_state,
                    self_check,
                }))
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
