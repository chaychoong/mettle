//! mt-138 `bench --solve`: the mettle-side timed run.
//!
//! Drives the same pipeline `solve_gauge::execute::classify_command` does
//! (`compute_universe -> compute_bounds -> lower_command -> solve_goal`, plus
//! the temporal arm via `solve_temporal_command`) at solve-gauge's stage-1
//! defaults, but stripped of the baseline-comparison and counting-net
//! machinery neither of which this bench needs -- the verdict to compare
//! against comes from the live jar run this module's caller already made,
//! not a cached baseline. Duplicated rather than imported from
//! `solve_gauge::execute` (whose types are `pub(super)` to that module) for
//! the same reason `bench::mettle_side` duplicates `resolve_gauge.rs`'s
//! verdict bucketing: a different caller with a different shape of work,
//! reusing the *pipeline calls*, not the glue around them.
//!
//! Runs single-threaded and times each command with `Instant`, wrapping both
//! the per-file resolve and each command's solve in `catch_unwind` (mt-039
//! discipline: one adversarial input must not abort the whole sweep).

use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use als_core::bounds::Bounds;
use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, self_check, solve_goal,
    solve_temporal_command, Backend, ScopedUniverse, SolveOptions, SolveVerdict,
    TemporalSolveConfig, TemporalVerdict, TranslateError,
};
use als_types::{is_temporal_model, FilesystemLoader, ModuleGraph, ResolvedWorld};

/// Solve-gauge stage-1's pinned defaults (`src/bin/solve_gauge.rs`'s
/// `parse_args`), re-stated here rather than threaded through a config: this
/// bench measures the one standing configuration the corpus is swept at, not
/// an arbitrary one, so there is nothing for a caller to legitimately override.
const CONFLICT_BUDGET: u64 = 1_000_000;
const ENCODE_BUDGET: u64 = 256_000_000;
const PRIMARY_VAR_CAP: usize = 20_000;
const SYMMETRY: u32 = 20;

/// One command's mettle-side outcome.
pub(super) enum MettleOutcome {
    /// A verdict was reached: `true` = SAT.
    Verdict(bool),
    /// A typed, budget-shaped reason the command produced no verdict --
    /// mirrors `solve_gauge`'s `mettle_defer:*` bucket vocabulary (STYLE
    /// E5: never a silent skip, never a wrong answer).
    Defer(&'static str),
    /// Solved, but the solved instance failed to re-satisfy its own lowered
    /// goal (STYLE I2) -- a mettle bug, not a verdict either side can trust.
    SelfCheckFail(String),
    /// The command's solve panicked; caught so one adversarial file cannot
    /// abort the whole sweep (mt-039).
    Panicked(String),
}

pub(super) struct MettleTiming {
    pub(super) outcome: MettleOutcome,
    pub(super) elapsed: Duration,
}

/// One resolved file: enough to time every root-module command against,
/// computed once and reused for the whole file (mirrors
/// `solve_gauge::execute::ResolvedFile`, duplicated for the reason in the
/// module doc).
struct ResolvedFile {
    graph: ModuleGraph,
    world: ResolvedWorld,
    command_indices: Vec<usize>,
}

fn resolve_file(path: &Path) -> Option<ResolvedFile> {
    let loader = FilesystemLoader::new();
    let canon = std::fs::canonicalize(path).ok()?;
    let root_str = canon.to_string_lossy().replace('\\', "/");
    let graph = ModuleGraph::load(&root_str, &loader).ok()?;
    let world = als_types::resolve(&graph).ok()?.world;
    let root_file = graph.modules[graph.root].file;
    let command_indices = world
        .commands
        .iter()
        .enumerate()
        .filter(|(_, c)| c.span.file == root_file)
        .map(|(idx, _)| idx)
        .collect();
    Some(ResolvedFile {
        graph,
        world,
        command_indices,
    })
}

/// The number of primary variables the bounds imply (`Sigma upper - lower`);
/// mirrors `solve_gauge::execute::primary_var_count`.
fn primary_var_count(bounds: &Bounds) -> usize {
    bounds
        .iter()
        .map(|(_, b)| b.upper().len() - b.lower().len())
        .sum()
}

fn defer(reason: &'static str, elapsed: Duration) -> MettleTiming {
    MettleTiming {
        outcome: MettleOutcome::Defer(reason),
        elapsed,
    }
}

/// Times one root-module command through the static (non-temporal) arm of
/// the pipeline: `compute_bounds -> lower_command -> solve_goal`, self-checking
/// a SAT verdict exactly as `solve_gauge`'s release-mode net does.
fn time_static_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    idx: usize,
    opts: &SolveOptions,
    started: Instant,
) -> MettleTiming {
    let mut ir = Ir::default();
    let bounds = compute_bounds(world, scoped, &mut ir);

    let Ok(goal) = lower_command(world, graph, scoped, &bounds, &mut ir, idx) else {
        return defer("mettle_defer:lower", started.elapsed());
    };
    if primary_var_count(&bounds.bounds) > PRIMARY_VAR_CAP {
        return defer("mettle_defer:primary_var_cap", started.elapsed());
    }

    match solve_goal(&ir, scoped, &goal, &bounds, opts) {
        Ok(SolveVerdict::Sat(inst)) => {
            let self_check_result = self_check(&ir, scoped, &goal, &inst, opts, &bounds.bounds);
            let elapsed = started.elapsed();
            match self_check_result {
                Ok(()) => MettleTiming {
                    outcome: MettleOutcome::Verdict(true),
                    elapsed,
                },
                Err(f) => MettleTiming {
                    outcome: MettleOutcome::SelfCheckFail(f.to_string()),
                    elapsed,
                },
            }
        }
        Ok(SolveVerdict::Unsat) => MettleTiming {
            outcome: MettleOutcome::Verdict(false),
            elapsed: started.elapsed(),
        },
        Ok(SolveVerdict::Unknown) => defer("mettle_defer:over_budget", started.elapsed()),
        Err(TranslateError::CapacityExceeded { .. }) => {
            defer("mettle_defer:capacity", started.elapsed())
        }
        Err(_) => defer("mettle_defer:encode", started.elapsed()),
    }
}

/// Times one root-module command through the temporal arm
/// (`solve_temporal_command`'s whole `steps`-range sweep), mirroring
/// `solve_gauge::execute::classify_temporal_command` minus the
/// baseline/count logic.
fn time_temporal_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    idx: usize,
    opts: SolveOptions,
    started: Instant,
) -> MettleTiming {
    let mut ir = Ir::default();
    let bounds = compute_bounds(world, scoped, &mut ir);
    let temporal_cfg = TemporalSolveConfig {
        opts,
        primary_var_cap: Some(PRIMARY_VAR_CAP),
        self_check: true,
    };
    match solve_temporal_command(world, graph, scoped, &bounds, &mut ir, idx, &temporal_cfg) {
        Ok(TemporalVerdict::Sat(trace)) => {
            let elapsed = started.elapsed();
            match trace.self_check {
                None => MettleTiming {
                    outcome: MettleOutcome::Verdict(true),
                    elapsed,
                },
                Some(f) => MettleTiming {
                    outcome: MettleOutcome::SelfCheckFail(f.to_string()),
                    elapsed,
                },
            }
        }
        Ok(TemporalVerdict::Unsat) => MettleTiming {
            outcome: MettleOutcome::Verdict(false),
            elapsed: started.elapsed(),
        },
        Ok(TemporalVerdict::Unknown { .. }) => defer("mettle_defer:over_budget", started.elapsed()),
        Ok(TemporalVerdict::PrimaryVarCap { .. }) => {
            defer("mettle_defer:primary_var_cap", started.elapsed())
        }
        Err(TranslateError::UnboundedSteps { .. }) => {
            defer("mettle_defer:temporal:unbounded_steps", started.elapsed())
        }
        Err(TranslateError::CapacityExceeded { .. }) => {
            defer("mettle_defer:capacity", started.elapsed())
        }
        Err(_) => defer("mettle_defer:lower", started.elapsed()),
    }
}

/// Times one root-module command end to end, dispatching static vs. temporal
/// exactly as the Rung-6 static/temporal split does (`is_temporal_model`),
/// and catching a panic so it becomes a typed outcome rather than aborting
/// the sweep.
fn time_command(world: &ResolvedWorld, graph: &ModuleGraph, idx: usize) -> MettleTiming {
    let started = Instant::now();
    let outcome = panic::catch_unwind(AssertUnwindSafe(|| {
        let Ok(scoped) = compute_universe(world, graph, &world.commands[idx]) else {
            return defer("mettle_defer:scope", started.elapsed());
        };
        // `expect 1` forces symmetry off (translation-ref sec 3/16.4) -- the
        // same rule solve_gauge's classify_command applies.
        let expect_one = matches!(
            world.commands[idx].expect,
            Some(als_syntax::ast::Expect::Sat)
        );
        let opts = SolveOptions {
            allow_overflow: false,
            conflict_budget: Some(CONFLICT_BUDGET),
            encode_budget: Some(ENCODE_BUDGET),
            symmetry: if expect_one { 0 } else { SYMMETRY },
            backend: Backend::default(),
            ..SolveOptions::default()
        };
        if is_temporal_model(world, graph, &world.commands[idx]) {
            time_temporal_command(world, graph, &scoped, idx, opts, started)
        } else {
            time_static_command(world, graph, &scoped, idx, &opts, started)
        }
    }));
    outcome.unwrap_or_else(|payload| {
        let msg = payload
            .downcast_ref::<&str>()
            .map(|s| (*s).to_owned())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "non-string panic payload".to_owned());
        MettleTiming {
            outcome: MettleOutcome::Panicked(msg),
            elapsed: started.elapsed(),
        }
    })
}

/// One file's mettle-side outcome: either it resolved (with a timed result
/// per root-module command index) or it did not (the whole file is
/// unavailable mettle-side, e.g. a parse/load/resolve failure or a panic
/// during resolve).
pub(super) enum FileRun {
    Resolved(Vec<(usize, MettleTiming)>),
    Unresolved,
}

/// Resolves and times every root-module command of one file, single-threaded.
/// The file-level resolve is itself panic-guarded (mirrors
/// `bench::mettle_side::resolve_stage`'s `catch_unwind` use).
pub(super) fn run_file(path: &Path) -> FileRun {
    let resolved = panic::catch_unwind(AssertUnwindSafe(|| resolve_file(path)));
    let Ok(Some(file)) = resolved else {
        return FileRun::Unresolved;
    };
    let results = file
        .command_indices
        .iter()
        .map(|&idx| (idx, time_command(&file.world, &file.graph, idx)))
        .collect();
    FileRun::Resolved(results)
}

/// Runs every file's timed sweep, single-threaded, in the given order.
/// Returns `(file, FileRun)` pairs in the same order as `files`.
pub(super) fn run_all(files: &[PathBuf]) -> Vec<(PathBuf, FileRun)> {
    files.iter().map(|f| (f.clone(), run_file(f))).collect()
}
