//! **Trace enumeration** (mt-076): the solver side of the reference GUI's five
//! exploration buttons, and the primitive the temporal counting net runs on.
//!
//! [`solve_temporal_command`](crate::temporal_solve::solve_temporal_command)
//! answers *one* question — is there a trace? — and stops at the first one.
//! [`TraceEnumerator`] keeps the sweep alive so a caller can ask for the next
//! trace, a new configuration, or a fork at a chosen state, exactly as
//! `A4Solution.next()`/`fork(p)` do.
//!
//! # The pinned contract
//!
//! Everything here implements
//! [alloy6-temporal.md §(g)](../../../docs/reference/alloy6-temporal.md)'s
//! mt-076 probe wave (`scratchpad/probe/mt076/NOTES.md`), which closed the four
//! corners wave 2 left open. In one table:
//!
//! | operator | GUI button | semantics |
//! |---|---|---|
//! | [`TraceStep::NextPath`] | "New" / "New Trace" | the next raw `(states, loop)` solution **inside the current configuration** at the current length; when that length is exhausted, advance through `[mintrace, maxtrace]`, skipping any solution whose infinite trace was already emitted at a **shorter** length |
//! | [`TraceStep::NextConfig`] | "New Config" | block the current static assignment and re-run the whole sweep from `mintrace` |
//! | [`TraceStep::Fork`] | "New Init" (`hold = 0`) / "New Fork" (`hold = current + 1`) | hold states `0..hold` byte-identical, force state `hold` **itself** to differ; nothing beyond it is constrained |
//!
//! Four findings drive the design, and each is a probe, not a reading:
//!
//! - **The configuration is held by plain `next()`** (P-076-5). A model with
//!   three non-isomorphic static configurations yields *eight* successive
//!   traces and then UNSAT, all in the first configuration — at `symmetry = 0`
//!   as well, so it is not a symmetry-breaking artifact. `fork(-1)` is the only
//!   way out. This is why the private `Config` exists at all.
//! - **`fork(-2)` is byte-for-byte `fork(-3)`** (P-076-3), which is why this
//!   module has one `NextPath` and not two operators.
//! - **The duplicate unit is two-level** (P-076-4): *within* a length, the raw
//!   `(per-state contents, loop state)` assignment — two solutions with
//!   identical contents but different loop targets are distinct, and even two
//!   that denote the same infinite trace are both emitted; *across* lengths,
//!   the **infinite trace** — a k+1-state solution whose unrolling was already
//!   emitted at k is skipped. Hence the private `TraceKey` and the two-set
//!   discipline (`emitted` / `emitted_here`) inside [`TraceEnumerator`].
//! - **`fork(p)` constrains state `p` itself** (P-076-6), which is why `p >= k`
//!   is exhaustion rather than "hold everything": there is no state `p` to
//!   force different.
//!
//! # Determinism and cost
//!
//! Same regime as the rest of the pipeline (STYLE D1): every length is a fresh,
//! deterministic encode+solve, the arena grows append-only, and nothing reads a
//! clock or iterates a hash container. [`enum_effort_budget`](crate::solve::SolveOptions::enum_effort_budget) is
//! charged across the *whole* enumeration — every length, every operator — so a
//! runaway exploration ends typed ([`TraceAdvance::BudgetExhausted`]) rather
//! than hanging, and never truncates a count silently.

use std::collections::{BTreeMap, BTreeSet};

use als_solve::{block, CdclSolver, Cnf, Lit, Outcome, Var};
use als_types::{is_temporal_model, ModuleGraph, ResolvedWorld, StepsMax};

use crate::bounds::{Tuple, TupleSet, Universe};
use crate::bounds_builder::BoundsResult;
use crate::error::TranslateError;
use crate::ir::{Ir, RelId};
use crate::lower::LoweredGoal;
use crate::scope::ScopedUniverse;
use crate::solve::{Instance, RelDecode};
use crate::temporal::{unroll, LassoSelector, UnrolledBounds};
use crate::temporal_lower::lower_temporal_command;
use crate::temporal_solve::{TemporalSolveConfig, TemporalTrace, TraceArtifacts};

/// One exploration command, named after the reference GUI's buttons rather than
/// after `A4Solution.fork`'s integer code (alloy6-temporal.md §(g)).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum TraceStep {
    /// "New" (`fork(-3)`) and "New Trace" (`fork(-2)`), which the probe wave
    /// found to be **the same operator** (P-076-3): the next path inside the
    /// current configuration.
    NextPath,
    /// "New Config" (`fork(-1)`): a different assignment to the model's static
    /// (non-`var`) relations, restarting the length sweep.
    NextConfig,
    /// "New Init" (`hold = 0`) and "New Fork" (`hold = current + 1`), the same
    /// `p >= 0` dispatch branch with a different index.
    Fork {
        /// How many leading states stay byte-identical. State `hold` itself is
        /// forced to differ; `hold >= k` is [`TraceAdvance::Exhausted`].
        hold: usize,
    },
}

/// What one [`TraceEnumerator::advance`] produced.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TraceAdvance {
    /// A further trace, now the enumerator's current one.
    Trace(TemporalTrace),
    /// Nothing further to show — the operator's space is empty (the jar's
    /// UNSAT). A *verdict* about this operator, not about the command.
    Exhausted,
    /// [`TraceStep::NextConfig`] on a model whose static relations have **no
    /// free primary variables**: there is nothing to block, so the reference
    /// re-derives and re-displays the byte-identical original (probe P-076-1,
    /// which is what wave 2's split `EnumDemo`/`TraceDemo` observation was).
    /// The current trace is unchanged.
    SameConfig,
    /// [`enum_effort_budget`](crate::solve::SolveOptions::enum_effort_budget) ran out. **Not** exhaustion: the
    /// space was never shown empty, so a count taken here is a lower bound.
    BudgetExhausted,
    /// A trace length's unrolled bounds outgrew
    /// [`TemporalSolveConfig::primary_var_cap`] before it could be searched.
    /// Not exhaustion, for the same reason.
    PrimaryVarCap {
        /// The length that outgrew the cap.
        k: usize,
        /// Its primary-variable count.
        primaries: usize,
    },
}

/// The **configuration**: the solved value of every static (non-`var`) relation,
/// which plain `next()` holds fixed for its whole enumeration (probe P-076-5).
///
/// Keyed by the *original* [`RelId`], which `unroll` leaves untouched for static
/// relations — so one configuration carries across every trace length without
/// translation. Goal skolem relations are deliberately **not** part of it: they
/// are minted afresh per length by
/// [`lower_temporal_command`], so their ids do not survive a length change, and
/// they are a lowering artifact rather than part of the model's static shape.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Config {
    rels: BTreeMap<RelId, TupleSet>,
}

/// The identity of an **infinite** lasso trace, for the across-length
/// de-duplication (probe P-076-4).
///
/// Two solutions at different trace lengths denote the same infinite trace iff
/// their canonical `(prefix, period, states)` forms agree, so that — and not the
/// raw `(states, loop)` assignment — is the key. Only the *variable* relations
/// enter it: the statics are pinned by the [`Config`] for the whole sweep, and
/// skolem relations are per-length artifacts.
type StateKey = Vec<(RelId, Vec<Tuple>)>;
type TraceKey = (usize, usize, Vec<StateKey>);

/// One trace length's live solver, kept between advances so `next` really is
/// incremental.
struct Stage {
    k: usize,
    solver: CdclSolver,
    /// Everything a blocking clause covers: every primary variable plus the
    /// lasso selector's. The selector **must** be in here — probe P-076-4 found
    /// two solutions whose per-state contents are identical and which differ
    /// only in the loop target, and the jar reports them as two.
    blocking_vars: Vec<Var>,
    layout: Vec<RelDecode>,
    universe: Universe,
    lasso: LassoSelector,
    unrolled: UnrolledBounds,
    goal: LoweredGoal,
    bounds: crate::bounds::Bounds,
    /// `true` once this stage's solver has reported UNSAT: the length is done.
    spent: bool,
}

/// A live enumeration over one temporal command's traces.
///
/// Built by [`TraceEnumerator::new`], driven by [`TraceEnumerator::advance`].
/// The enumerator owns its own [`Ir`] clone because each new trace length
/// allocates per-state relation copies into it, and the caller's arena must not
/// grow underneath whatever else is reading it.
pub struct TraceEnumerator<'a> {
    world: &'a ResolvedWorld,
    graph: &'a ModuleGraph,
    scoped: &'a ScopedUniverse,
    bounds: &'a BoundsResult,
    command_index: usize,
    cfg: TemporalSolveConfig,
    /// The enumerator's private arena (module docs).
    ir: Ir,
    min: usize,
    max: usize,
    stage: Option<Stage>,
    /// The trace the caller is currently looking at; `None` before the first
    /// advance.
    current: Option<TemporalTrace>,
    /// The configuration every path advance holds fixed, adopted from the first
    /// solution and replaced by [`TraceStep::NextConfig`].
    config: Option<Config>,
    /// Configurations already visited, each blocked out of every later stage so
    /// "New Config" never shows one twice.
    blocked_configs: Vec<Config>,
    /// Infinite traces emitted at **strictly shorter** lengths of the current
    /// configuration's sweep — the across-length de-duplication set.
    emitted: BTreeSet<TraceKey>,
    /// Infinite traces emitted at the length currently being enumerated. Held
    /// separately, and merged into [`Self::emitted`] only when the length
    /// advances, because within one length duplicates are legal and *are*
    /// emitted by the reference (probe P-076-4).
    emitted_here: BTreeSet<TraceKey>,
    /// Remaining cumulative effort; `None` = unbudgeted.
    budget_remaining: Option<u64>,
    /// Set once the budget ran out — the enumeration stopped short of proving
    /// the space empty, so no count taken from it is exact.
    budget_spent: bool,
    /// Set while the live stage carries a [`TraceStep::Fork`]'s prefix
    /// constraints, so a following [`TraceStep::NextPath`] continues *that*
    /// question rather than silently reopening the unrestricted length sweep.
    /// Cleared by [`TraceStep::NextConfig`], which starts a whole new sweep.
    restricted: bool,
    /// Whether the length lowered so far minted a higher-order skolem. Read by
    /// the counting net, which excludes that family from jar comparison
    /// (`skip_ho_skolem`) exactly as the static arm does.
    higher_order_skolem: bool,
}

impl std::fmt::Debug for TraceEnumerator<'_> {
    /// Hand-written because a [`CdclSolver`]'s internals are not worth printing
    /// and the borrowed world would dwarf everything that matters.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TraceEnumerator")
            .field("command_index", &self.command_index)
            .field("range", &(self.min, self.max))
            .field("k", &self.stage.as_ref().map(|s| s.k))
            .field("configs_visited", &self.blocked_configs.len())
            .field("budget_remaining", &self.budget_remaining)
            .finish_non_exhaustive()
    }
}

impl<'a> TraceEnumerator<'a> {
    /// Opens an enumeration over one **temporal** command.
    ///
    /// Nothing is solved here: the first [`TraceStep::NextPath`] finds the first
    /// trace, so a caller that only wants a verdict should use
    /// [`solve_temporal_command`](crate::temporal_solve::solve_temporal_command)
    /// instead. `ir` is cloned; the caller's arena is left alone.
    ///
    /// # Errors
    /// [`TranslateError::UnboundedSteps`] for a `1..` steps scope and
    /// [`TranslateError::TemporalCheckAtOneStep`] for the pinned
    /// `check`-at-one-state jar bug — the same two typed defers the sweep
    /// raises, refused here rather than at the first advance so a caller cannot
    /// build an enumerator that could never answer.
    ///
    /// # Panics
    /// Debug builds assert that `command_index` really is a temporal command;
    /// dispatch is the caller's job.
    pub fn new(
        world: &'a ResolvedWorld,
        graph: &'a ModuleGraph,
        scoped: &'a ScopedUniverse,
        bounds: &'a BoundsResult,
        ir: &Ir,
        command_index: usize,
        cfg: &TemporalSolveConfig,
    ) -> Result<Self, TranslateError> {
        let command = &world.commands[command_index];
        debug_assert!(
            is_temporal_model(world, graph, command),
            "TraceEnumerator on a static command — dispatch is the caller's job"
        );
        let range = command.steps_range();
        let StepsMax::Bounded(max) = range.max else {
            return Err(TranslateError::UnboundedSteps {
                span: command.steps.map_or(command.span, |s| s.span),
            });
        };
        if matches!(command.kind, als_syntax::ast::CmdKind::Check) && max == 1 {
            return Err(TranslateError::TemporalCheckAtOneStep { span: command.span });
        }
        Ok(TraceEnumerator {
            world,
            graph,
            scoped,
            bounds,
            command_index,
            cfg: *cfg,
            ir: ir.clone(),
            min: range.min as usize,
            max: max as usize,
            stage: None,
            current: None,
            config: None,
            blocked_configs: Vec::new(),
            emitted: BTreeSet::new(),
            emitted_here: BTreeSet::new(),
            budget_remaining: cfg.opts.enum_effort_budget,
            budget_spent: false,
            restricted: false,
            higher_order_skolem: false,
        })
    }

    /// The enumerator's own arena.
    ///
    /// Every trace it yields references relations allocated **here** — the
    /// per-state copies of the length it was found at, and that length's goal
    /// skolems — none of which exist in the arena the enumerator was built
    /// from. A caller that renders or evaluates a trace (`mettle serve`) must
    /// therefore take its copy of the arena from this, not from its own
    /// pre-solve one, or a freshly-allocated relation id will collide with a
    /// per-state copy the trace is already using. The arena is append-only, so a
    /// clone taken any time after an advance contains everything that advance's
    /// trace needs.
    #[must_use]
    pub fn ir(&self) -> &Ir {
        &self.ir
    }

    /// The trace currently on display, or `None` before the first advance.
    #[must_use]
    pub fn current(&self) -> Option<&TemporalTrace> {
        self.current.as_ref()
    }

    /// Whether any trace length lowered so far minted a **higher-order**
    /// skolem relation — the divergence family the counting net excludes from
    /// jar comparison. Meaningful only after the first advance.
    #[must_use]
    pub fn has_higher_order_skolem(&self) -> bool {
        self.higher_order_skolem
    }

    /// Whether the enumeration stopped because
    /// [`enum_effort_budget`](crate::solve::SolveOptions::enum_effort_budget) ran out rather than because the
    /// space was empty. A caller counting traces **must** check this before
    /// trusting the count.
    #[must_use]
    pub fn budget_spent(&self) -> bool {
        self.budget_spent
    }

    /// Performs one exploration command.
    ///
    /// # Errors
    /// Anything [`lower_temporal_command`] or the encoder can raise, including
    /// [`TranslateError::CapacityExceeded`] when a length outgrows
    /// [`encode_budget`](crate::solve::SolveOptions::encode_budget).
    pub fn advance(&mut self, step: TraceStep) -> Result<TraceAdvance, TranslateError> {
        if self.budget_spent {
            return Ok(TraceAdvance::BudgetExhausted);
        }
        match step {
            TraceStep::NextPath => self.next_path(),
            TraceStep::NextConfig => self.next_config(),
            TraceStep::Fork { hold } => self.fork(hold),
        }
    }

    /// "New" / "New Trace": the next path of the current configuration, walking
    /// the length range as the current length runs out.
    fn next_path(&mut self) -> Result<TraceAdvance, TranslateError> {
        loop {
            if self.stage.is_none() {
                // The first advance of a sweep: open at the shortest length.
                match self.open_stage(self.min)? {
                    StageOpen::Ready => {}
                    StageOpen::Refused(outcome) => return Ok(outcome),
                }
            }
            match self.solve_current_stage()? {
                Some(trace) => return Ok(TraceAdvance::Trace(trace)),
                None if self.budget_spent => return Ok(TraceAdvance::BudgetExhausted),
                None if self.restricted => {
                    // A fork asked about ONE trace length ("hold this prefix,
                    // change state `hold`"), and `fork(p)` is pinned never to
                    // move the length (probe P-076-2). Widening the search to
                    // `k+1` behind the caller's back would answer a question it
                    // did not ask — and would re-show traces the unrestricted
                    // sweep already showed. So a restricted sweep ends here.
                    self.stage = None;
                    return Ok(TraceAdvance::Exhausted);
                }
                None => {
                    // This length is spent. Its traces become the shorter-length
                    // set the next length de-duplicates against.
                    self.emitted.append(&mut self.emitted_here);
                    let Some(next_k) = self.stage.as_ref().map(|s| s.k + 1) else {
                        unreachable!("a spent stage is still a stage (STYLE I3)")
                    };
                    if next_k > self.max {
                        self.stage = None;
                        return Ok(TraceAdvance::Exhausted);
                    }
                    match self.open_stage(next_k)? {
                        StageOpen::Ready => {}
                        StageOpen::Refused(outcome) => return Ok(outcome),
                    }
                }
            }
            if self.budget_spent {
                return Ok(TraceAdvance::BudgetExhausted);
            }
        }
    }

    /// "New Config": block the current static assignment and restart the sweep.
    ///
    /// The no-free-static-primaries case is answered without solving, because
    /// that is exactly what the reference does — with nothing to block it
    /// re-derives the same model (probe P-076-1).
    fn next_config(&mut self) -> Result<TraceAdvance, TranslateError> {
        let Some(config) = self.config.clone() else {
            // Nothing shown yet, so there is no configuration to move off:
            // "next config" degenerates to "find the first trace".
            return self.next_path();
        };
        if !self.config_has_free_primaries() {
            return Ok(TraceAdvance::SameConfig);
        }
        self.blocked_configs.push(config);
        self.config = None;
        self.stage = None;
        self.restricted = false;
        self.emitted.clear();
        self.emitted_here.clear();
        self.next_path()
    }

    /// "New Init" / "New Fork": hold `hold` leading states, force state `hold`
    /// to differ.
    ///
    /// A fresh stage at the current length, because the constraint is a
    /// different question about the same length rather than a continuation of
    /// the current one — the reference's `nextS(state, 1, rels)` likewise opens
    /// a restricted iteration rather than resuming the unrestricted one.
    fn fork(&mut self, hold: usize) -> Result<TraceAdvance, TranslateError> {
        let Some(current) = self.current.clone() else {
            // With nothing on display there is no prefix to hold; the honest
            // answer is the first trace.
            return self.next_path();
        };
        if hold >= current.k() {
            // There is no state `hold` to force different (probe P-076-6).
            return Ok(TraceAdvance::Exhausted);
        }
        match self.open_stage(current.k())? {
            StageOpen::Ready => {}
            StageOpen::Refused(outcome) => return Ok(outcome),
        }
        let Some(stage) = self.stage.as_mut() else {
            unreachable!("open_stage returned Ready without a stage (STYLE I3)")
        };
        // Hold: unit-fix every per-state copy of every variable relation, for
        // every state strictly before `hold`. Snapshotted first because the
        // walk reads the stage's bridge map while the fixing writes its solver.
        let mut fixed: Vec<(RelId, TupleSet)> = Vec::new();
        let mut differ_copies: Vec<(RelId, TupleSet)> = Vec::new();
        for (&original, copies) in &stage.unrolled.states {
            for (state, &copy) in copies.iter().enumerate().take(hold) {
                let Some(value) = current.states[state].get(original) else {
                    unreachable!("the displayed trace is missing a variable relation (STYLE I3)")
                };
                fixed.push((copy, value.clone()));
            }
            let Some(value) = current.states[hold].get(original) else {
                unreachable!("the displayed trace is missing a variable relation (STYLE I3)")
            };
            differ_copies.push((copies[hold], value.clone()));
        }
        for (copy, value) in &fixed {
            fix_relation(stage, *copy, value);
        }
        // Differ: state `hold` must not be the displayed trace's state `hold`.
        // One clause over that state's copies only — the negation of "every
        // copy equals what it was" (STYLE I2: an empty clause would be a
        // silently-unsatisfiable stage, so a state with no floating variables
        // is exhaustion, not a contradiction to install).
        let differ: Vec<Lit> = differ_copies
            .iter()
            .flat_map(|(copy, value)| relation_differs(stage, *copy, value))
            .collect();
        if differ.is_empty() {
            self.stage = None;
            return Ok(TraceAdvance::Exhausted);
        }
        stage.solver.add_clause(differ);
        // A fork is a fresh question, so nothing it finds is a "duplicate" of
        // what the unrestricted sweep already showed.
        self.emitted.clear();
        self.emitted_here.clear();
        self.restricted = true;
        match self.solve_current_stage()? {
            Some(trace) => Ok(TraceAdvance::Trace(trace)),
            None => Ok(if self.budget_spent {
                TraceAdvance::BudgetExhausted
            } else {
                TraceAdvance::Exhausted
            }),
        }
    }

    /// Whether the configuration has anything to block — i.e. whether any static
    /// relation has a floating (non-fixed) tuple.
    ///
    /// Read off the *bounds* rather than the stage, so it is the same answer at
    /// every trace length and is available before anything is solved.
    fn config_has_free_primaries(&self) -> bool {
        self.bounds.bounds.iter().any(|(rel, bound)| {
            self.ir.relations[rel].mutability == crate::ir::Mutability::Static
                && bound.upper().len() > bound.lower().len()
        })
    }

    /// Builds the stage for trace length `k`: unroll, lower, translate, then
    /// re-apply the configuration lock and every blocked configuration.
    fn open_stage(&mut self, k: usize) -> Result<StageOpen, TranslateError> {
        let unrolled = unroll(&mut self.ir, &self.bounds.bounds, k);
        if let Some(cap) = self.cfg.primary_var_cap {
            let primaries: usize = unrolled
                .bounds
                .iter()
                .map(|(_, b)| b.upper().len() - b.lower().len())
                .sum();
            if primaries > cap {
                self.stage = None;
                return Ok(StageOpen::Refused(TraceAdvance::PrimaryVarCap {
                    k,
                    primaries,
                }));
            }
        }
        let goal = lower_temporal_command(
            self.world,
            self.graph,
            self.scoped,
            self.bounds,
            &mut self.ir,
            self.command_index,
            k,
            &unrolled,
        )?;
        self.higher_order_skolem |= goal.has_higher_order_skolem;
        let t = crate::solve::translate(
            &self.ir,
            self.scoped,
            &goal,
            self.bounds,
            Some(&unrolled),
            self.cfg.opts,
        )?;
        let Some(lasso) = t.lasso else {
            unreachable!("a temporal translate always mints a lasso selector (STYLE I3)")
        };
        let mut cnf: Cnf = t.cnf;
        if t.trivially_unsat {
            // The same shape `enumerate` uses: an empty clause makes the first
            // solve report UNSAT and the stage terminate cleanly.
            cnf.add_clause(vec![]);
        }
        let mut blocking_vars = t.primary_vars;
        blocking_vars.extend_from_slice(lasso.vars());
        let mut stage = Stage {
            k,
            solver: CdclSolver::new(&cnf),
            blocking_vars,
            layout: t.layout,
            universe: t.universe,
            lasso,
            unrolled,
            goal,
            bounds: t.bounds,
            spent: false,
        };
        if let Some(config) = self.config.clone() {
            lock_config(&mut stage, &config);
        }
        for blocked in &self.blocked_configs {
            block_config(&mut stage, blocked);
        }
        self.stage = Some(stage);
        Ok(StageOpen::Ready)
    }

    /// Draws solutions from the current stage until one is emittable, blocking
    /// each as it goes. `None` means the stage is spent (or the budget is).
    fn solve_current_stage(&mut self) -> Result<Option<TemporalTrace>, TranslateError> {
        loop {
            let Some(stage) = self.stage.as_mut() else {
                return Ok(None);
            };
            if stage.spent {
                return Ok(None);
            }
            let outcome = match solve_charged(&mut stage.solver, &mut self.budget_remaining) {
                Charged::Outcome(outcome) => outcome,
                Charged::OutOfBudget => {
                    self.budget_spent = true;
                    stage.spent = true;
                    return Ok(None);
                }
            };
            let Outcome::Sat(model) = outcome else {
                stage.spent = true;
                return Ok(None);
            };
            let clause = block(&model, &stage.blocking_vars);
            if clause.is_empty() {
                // No distinguishable variables at all: this is the one and only
                // solution of the length.
                stage.spent = true;
            } else {
                stage.solver.add_clause(clause);
            }
            let loop_state = crate::solve::recover_loop_state(&stage.lasso, &model);
            let instance = crate::solve::decode(&stage.layout, &stage.universe, &model);
            let self_check = if self.cfg.self_check {
                crate::eval::self_check_temporal(
                    &self.ir,
                    self.scoped,
                    &stage.goal,
                    &instance,
                    &self.cfg.opts,
                    &stage.bounds,
                    loop_state,
                )
                .err()
            } else {
                None
            };
            crate::solve::debug_self_check_temporal(
                &self.ir,
                self.scoped,
                &stage.goal,
                &instance,
                self.cfg.opts,
                &stage.bounds,
                loop_state,
            );
            let states = split_states(&stage.unrolled, &instance);
            let key = trace_key(&stage.unrolled, &states, loop_state);
            if self.emitted.contains(&key) {
                // Already shown at a shorter length: the reference does not
                // repeat it (probe P-076-4). Keep drawing.
                continue;
            }
            self.emitted_here.insert(key);
            if self.config.is_none() {
                self.config = Some(read_config(&stage.unrolled, &stage.goal, &instance));
                let Some(config) = self.config.clone() else {
                    unreachable!("just assigned (STYLE I3)")
                };
                // Hold it for the rest of *this* stage too, not only for the
                // stages after it — plain `next()` never changes configuration
                // (probe P-076-5).
                lock_config(stage, &config);
            }
            let trace = TemporalTrace {
                states,
                loop_state,
                self_check,
                artifacts: Box::new(TraceArtifacts {
                    unrolled: stage.unrolled.clone(),
                    instance,
                    goal: stage.goal.clone(),
                }),
            };
            self.current = Some(trace.clone());
            return Ok(Some(trace));
        }
    }
}

/// [`TraceEnumerator::open_stage`]'s two outcomes: a usable stage, or a typed
/// refusal that must reach the caller untouched.
enum StageOpen {
    Ready,
    Refused(TraceAdvance),
}

/// One budgeted solve's result.
enum Charged {
    Outcome(Outcome),
    OutOfBudget,
}

/// Solves, charging effort (conflicts + decisions + propagation clause-visits)
/// against the remaining budget — the same three terms
/// [`crate::solve::InstanceEnumerator`] charges, and for the same reason: the
/// propagation term is what actually tracks wall time on a big-but-easy CNF.
fn solve_charged(solver: &mut CdclSolver, remaining: &mut Option<u64>) -> Charged {
    let Some(left) = *remaining else {
        return Charged::Outcome(solver.solve());
    };
    if left == 0 {
        return Charged::OutOfBudget;
    }
    let effort = |s: &CdclSolver| s.total_conflicts() + s.total_decisions() + s.total_props();
    let before = effort(solver);
    let Some(outcome) = solver.solve_within(left) else {
        return Charged::OutOfBudget;
    };
    let spent = effort(solver).saturating_sub(before);
    *remaining = Some(left.saturating_sub(spent));
    Charged::Outcome(outcome)
}

/// Reads the configuration — every **model** static relation's solved value —
/// out of a flat solved instance.
///
/// Two families are excluded, and the second is load-bearing:
///
/// - the per-state copies, which are the *path*, not the configuration;
/// - the goal's **skolem relations**. Those are static in mettle's IR (mt-066:
///   skolemization is off *under* a temporal operator, but a top-level
///   existential outside them still skolemizes into a rigid constant), so a
///   filter that only asked "is this relation static?" would sweep them in —
///   and freezing an existential's witness for the whole enumeration collapses
///   the count. The jar cannot have this problem: it does not skolemize a
///   temporal problem at all, so its notion of "the non-variable relations" has
///   no skolems in it. Getting this wrong cost three SB-20 `COUNT_MISMATCH`
///   rows (`buffer.als` 1 vs 4431, 1 vs 4175; `leader.als` 1 vs 10001) before
///   it was caught, which is why the exclusion is spelled out here.
fn read_config(unrolled: &UnrolledBounds, goal: &LoweredGoal, flat: &Instance) -> Config {
    let copies: BTreeSet<RelId> = unrolled
        .states
        .values()
        .flat_map(|cs| cs.iter().copied())
        .collect();
    let skolems: BTreeSet<RelId> = goal.skolem_bounds.iter().map(|(rel, _)| *rel).collect();
    Config {
        rels: flat
            .iter()
            .filter(|(rel, _)| !copies.contains(rel) && !skolems.contains(rel))
            .map(|(rel, ts)| (rel, ts.clone()))
            .collect(),
    }
}

/// Unit-fixes every relation of `config` that this stage actually binds.
///
/// A stage may bind relations the configuration does not mention (goal skolems,
/// minted per length) and — after a `NextConfig` at a different length — the
/// other way round is impossible, since static relation ids do not move. Only
/// the intersection is fixed, which is exactly the model's static shape.
fn lock_config(stage: &mut Stage, config: &Config) {
    for (rel, value) in &config.rels {
        fix_relation(stage, *rel, value);
    }
}

/// Adds the clause forbidding `config`'s static assignment, so a later "New
/// Config" cannot land on it again.
fn block_config(stage: &mut Stage, config: &Config) {
    let mut clause: Vec<Lit> = Vec::new();
    for (rel, value) in &config.rels {
        clause.extend(relation_differs(stage, *rel, value));
    }
    if !clause.is_empty() {
        stage.solver.add_clause(clause);
    }
}

/// Unit-fixes `rel`'s floating variables to exactly `value`.
fn fix_relation(stage: &mut Stage, rel: RelId, value: &TupleSet) {
    let Some(decode) = stage.layout.iter().find(|d| d.rel == rel) else {
        return;
    };
    let units: Vec<Lit> = decode
        .floating
        .iter()
        .map(|(tuple, var)| {
            if value.contains(tuple) {
                Lit::positive(*var)
            } else {
                Lit::negative(*var)
            }
        })
        .collect();
    for unit in units {
        stage.solver.add_clause(vec![unit]);
    }
}

/// The literals saying "`rel` is not exactly `value`", for use inside a larger
/// disjunction. Empty when `rel` has no floating variables — a relation that
/// *cannot* differ contributes nothing to the disjunction, which is why
/// callers check for an all-empty clause rather than installing one.
fn relation_differs(stage: &Stage, rel: RelId, value: &TupleSet) -> Vec<Lit> {
    let Some(decode) = stage.layout.iter().find(|d| d.rel == rel) else {
        return Vec::new();
    };
    decode
        .floating
        .iter()
        .map(|(tuple, var)| {
            if value.contains(tuple) {
                Lit::negative(*var)
            } else {
                Lit::positive(*var)
            }
        })
        .collect()
}

/// Splits a flat solved instance into one [`Instance`] per state, keyed by the
/// original relation ids — the same view
/// [`solve_temporal_command`](crate::temporal_solve::solve_temporal_command)
/// hands a renderer.
fn split_states(unrolled: &UnrolledBounds, flat: &Instance) -> Vec<Instance> {
    let copies: BTreeSet<RelId> = unrolled
        .states
        .values()
        .flat_map(|cs| cs.iter().copied())
        .collect();
    let statics: Vec<(RelId, TupleSet)> = flat
        .iter()
        .filter(|(rel, _)| !copies.contains(rel))
        .map(|(rel, ts)| (rel, ts.clone()))
        .collect();
    (0..unrolled.k)
        .map(|state| {
            let mut rels = statics.clone();
            for (&original, cs) in &unrolled.states {
                let Some(value) = flat.get(cs[state]) else {
                    unreachable!("solved instance is missing a per-state copy (STYLE I3)")
                };
                rels.push((original, value.clone()));
            }
            Instance::from_relations(flat.universe.clone(), rels)
        })
        .collect()
}

/// The canonical identity of the infinite trace `states` + `loop_state` denotes:
/// its **minimal** prefix length, its **minimal** period, and the variable
/// content of those `prefix + period` logical states.
///
/// Two lasso representations denote the same infinite trace exactly when this
/// agrees, which is the across-length de-duplication test probe P-076-4 pins.
/// Minimising both terms is what makes it canonical: `({},{X},{X})` with
/// `loop = 2` and the same content with `loop = 1` both reduce to
/// `prefix = 1, period = 1`, and so both are recognised as the length-2 trace
/// `{} ({X})^ω` that was already emitted.
fn trace_key(unrolled: &UnrolledBounds, states: &[Instance], loop_state: usize) -> TraceKey {
    let k = states.len();
    let cycle = k - loop_state;
    let at = |i: usize| -> &Instance {
        &states[if i < k {
            i
        } else {
            ((i - loop_state) % cycle) + loop_state
        }]
    };
    let same = |a: &Instance, b: &Instance| -> bool {
        unrolled.states.keys().all(|&rel| a.get(rel) == b.get(rel))
    };
    // The minimal period divides the cycle length, so only divisors need trying
    // — and the smallest that reproduces the whole cycle is minimal by
    // construction.
    let mut period = cycle;
    for q in 1..=cycle {
        if !cycle.is_multiple_of(q) {
            continue;
        }
        if (loop_state..k).all(|i| same(at(i), at(loop_state + (i - loop_state) % q))) {
            period = q;
            break;
        }
    }
    // Shrink the prefix while the state just before it already repeats.
    let mut prefix = loop_state;
    while prefix > 0 && same(at(prefix - 1), at(prefix - 1 + period)) {
        prefix -= 1;
    }
    let content = (0..prefix + period)
        .map(|i| {
            let inst = at(i);
            unrolled
                .states
                .keys()
                .map(|&rel| {
                    let tuples = inst
                        .get(rel)
                        .map(|ts| ts.iter().cloned().collect::<Vec<Tuple>>())
                        .unwrap_or_default();
                    (rel, tuples)
                })
                .collect::<StateKey>()
        })
        .collect();
    (prefix, period, content)
}
