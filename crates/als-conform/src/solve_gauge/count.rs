//! Stage-2 counting classification: bucketing a mettle-SAT command's exact
//! count against the cached count baseline, or — under `--live-jar` — against
//! a live per-file JVM oracle run.

use std::collections::BTreeMap;
use std::path::PathBuf;

use als_core::ir::Ir;
use als_core::{
    enumerate, BoundsResult, LoweredGoal, ScopedUniverse, SolveOptions, TemporalSolveConfig,
    TraceAdvance, TraceEnumerator, TraceStep, TranslateError,
};
use als_types::{ModuleGraph, ResolvedWorld};

use crate::config::{EnumerationCap, OracleConfig};
use crate::error::ConformError;
use crate::model::{FileOutcome, Outcome};
use crate::shim::{ensure_shim_compiled, run_oracle_on_file};

use super::count_baseline::{CountBaseline, CountResolution};
use super::detect::ordered_abstract_partition;
use super::parallel::parallel_fold;
use super::report::SolveGaugeReport;
use super::{GaugeConfig, JAR_SOLVER};

/// The stage-2 disposition of one SAT command after mettle-side classification.
#[derive(Clone, Copy)]
pub(super) enum CountOutcome {
    /// A typed skip: the given `count_buckets` key.
    Skip(&'static str),
    /// Eligible: mettle's exact SB count, awaiting the jar comparison.
    JarTodo(u64),
    /// A **temporal** command's exact count where mettle's own configuration is
    /// *not* the only one (mt-076, probe P-076-5/P-076-7).
    ///
    /// The count is real and is still compared: an **agreement** is a genuine
    /// `count_match`. But a **disagreement** carries no signal about mettle —
    /// the jar's `next()` walked sat4j's first configuration and mettle's walked
    /// mettle's, and on such a command those are provably different sets (the
    /// measured case: `leader.als[3]`, jar's first solution a full three-node
    /// ring counting to the 10001 cap, mettle's the empty model whose whole
    /// space is one trace). So a disagreement here is bucketed
    /// `skip_temporal_config` rather than raised as a `COUNT_MISMATCH`, which in
    /// this repo means "mettle counted wrong".
    JarTodoConfigRelative(u64),
}

/// The stage-2 disposition after cache lookup (or deferred to the live jar stage).
pub(super) enum CountDisp {
    None,
    Resolved {
        bucket: String,
        mismatch: Option<String>,
    },
    PendingJar(u64),
    /// As [`CountDisp::PendingJar`], for a configuration-relative temporal
    /// count: the live jar stage softens a disagreement the same way
    /// [`resolve_count`] does for the cached path.
    PendingJarConfigRelative(u64),
}

/// A live-jar todo: `(relpath, command index, mettle count, per_command index,
/// configuration-relative?)`. The last flag softens a disagreement exactly as
/// [`resolve_count`] does on the cached path (see
/// [`CountOutcome::JarTodoConfigRelative`]).
pub(super) type JarTodo = (String, usize, u64, usize, bool);

/// Resolves a mettle-side [`CountOutcome`] into its report disposition: a typed
/// skip stays resolved; a `JarTodo` is resolved against the cache (default) or
/// deferred to the live jar stage (`--live-jar`).
pub(super) fn resolve_count(
    outcome: Option<CountOutcome>,
    live_jar: bool,
    count_baseline: Option<&CountBaseline>,
    rel: &str,
    idx: usize,
) -> CountDisp {
    match outcome {
        None => CountDisp::None,
        Some(CountOutcome::Skip(k)) => CountDisp::Resolved {
            bucket: k.to_owned(),
            mismatch: None,
        },
        Some(CountOutcome::JarTodo(n)) => {
            if live_jar {
                CountDisp::PendingJar(n)
            } else {
                let (bucket, mismatch) = count_baseline.map_or_else(
                    || ("skip_no_count_baseline".to_owned(), None),
                    |cb| cb.disposition(rel, idx, n),
                );
                CountDisp::Resolved { bucket, mismatch }
            }
        }
        Some(CountOutcome::JarTodoConfigRelative(n)) => {
            if live_jar {
                CountDisp::PendingJarConfigRelative(n)
            } else {
                let (bucket, mismatch) = count_baseline.map_or_else(
                    || ("skip_no_count_baseline".to_owned(), None),
                    |cb| cb.disposition(rel, idx, n),
                );
                CountDisp::Resolved {
                    bucket: soften(&bucket),
                    mismatch: soften_line(&bucket, mismatch),
                }
            }
        }
    }
}

/// A `COUNT_MISMATCH` on a configuration-relative temporal count is not a
/// mismatch (see [`CountOutcome::JarTodoConfigRelative`]); everything else
/// stands.
fn soften(bucket: &str) -> String {
    if bucket == "COUNT_MISMATCH" {
        "skip_temporal_config".to_owned()
    } else {
        bucket.to_owned()
    }
}

/// The matching half of [`soften`]: a softened bucket must not also file the
/// `COUNT_MISMATCH` line, or a fail-fast run would stop on a non-finding.
fn soften_line(bucket: &str, mismatch: Option<String>) -> Option<String> {
    if bucket == "COUNT_MISMATCH" {
        None
    } else {
        mismatch
    }
}

/// The count bucket this command is **already** in before anything is
/// enumerated, or `None` when only a real count can decide it (mt-059).
///
/// The rule lives once, in [`CountResolution`], next to the `disposition` that
/// buckets a counted command — so "skip the enumeration" and "bucket the
/// result" cannot drift into disagreeing. Two callers here are deliberately not
/// asked:
/// - `--live-jar` recomputes the jar side per file *after* the sweep, so
///   nothing is known up front and every eligible command must be enumerated;
/// - `--enumerate-all` opts back into the enumeration precisely to keep
///   exercising the incremental enumerator on non-comparable models.
///
/// With no count baseline loaded at all, every command is a miss — the same
/// answer [`resolve_count`] gives after the fact.
pub(super) fn presettled_count_bucket(
    cfg: &GaugeConfig,
    count_baseline: Option<&CountBaseline>,
    rel: &str,
    idx: usize,
) -> Option<&'static str> {
    if cfg.live_jar || cfg.enumerate_all {
        return None;
    }
    let Some(cb) = count_baseline else {
        return Some("skip_no_count_baseline");
    };
    match cb.resolution(rel, idx) {
        CountResolution::Fixed(bucket) => Some(bucket),
        CountResolution::NeedsCount(_) => None,
    }
}

/// Classifies the count disposition of a mettle-SAT command: documented
/// divergence families are typed skips; a command the count baseline has already
/// settled is its settled bucket; everything else is enumerated to an exact
/// mettle count (or `skip_mettle_cap` past the cap / budget).
///
/// `presettled` is the mt-059 reordering: an exhaustive enumeration (solve →
/// block → solve, at symmetry 0 over the raw solution space) is the most
/// expensive thing the gauge does, and for roughly half the corpus no possible
/// result of it could change the bucket. It is consulted **after** the
/// divergence families deliberately — those are free to compute and strictly
/// more informative than "no comparison exists", so keeping their order leaves
/// `skip_ho_skolem`/`skip_ordered_abstract` counts exactly as they were.
#[allow(
    clippy::too_many_arguments,
    reason = "the lowered command plus the two stage-2 policy inputs"
)]
pub(super) fn classify_count(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    world: &ResolvedWorld,
    opts: &SolveOptions,
    count_cap: u64,
    presettled: Option<&'static str>,
) -> CountOutcome {
    if goal.has_higher_order_skolem {
        return CountOutcome::Skip("skip_ho_skolem");
    }
    if ordered_abstract_partition(world, scoped) {
        return CountOutcome::Skip("skip_ordered_abstract");
    }
    if let Some(bucket) = presettled {
        return CountOutcome::Skip(bucket);
    }

    let mut it = match enumerate(ir, scoped, goal, bounds, opts) {
        Ok(it) => it,
        // The enumeration budget on a backend with no effort counters
        // (ADR-0027 decision 2). Its own bucket, not folded into the
        // encode-budget skip above it: a capability gap and capacity pressure
        // are different findings with different fixes, and the mt-120 spike hit
        // exactly this as an assert that took the row's *verdict* down with it.
        Err(TranslateError::BackendCapability { .. }) => {
            return CountOutcome::Skip("skip_backend_capability")
        }
        Err(_) => return CountOutcome::Skip("skip_mettle_cap"),
    };
    let mut n = 0u64;
    for _ in it.by_ref() {
        n += 1;
        if n > count_cap {
            break;
        }
    }
    if it.exhausted() {
        CountOutcome::Skip("skip_enum_budget")
    } else if n > count_cap {
        CountOutcome::Skip("skip_mettle_cap")
    } else {
        CountOutcome::JarTodo(n)
    }
}

/// A live jar-stage per-file result: for each todo, its count bucket, an optional
/// `COUNT_MISMATCH` line, and the `per_command` index to patch.
type JarFileResult = Vec<(&'static str, Option<String>, usize)>;

/// Runs the jar over every file with an eligible command (`--live-jar` only),
/// parallel per file under `--jobs`, folding in sorted-canon order. Returns the
/// fail-fast trigger (a `COUNT_MISMATCH`) if any.
pub(super) fn run_jar_stage(
    cfg: &GaugeConfig,
    jar_todo: &BTreeMap<PathBuf, Vec<JarTodo>>,
    report: &mut SolveGaugeReport,
    progress: &mut dyn FnMut(&str),
) -> Result<Option<String>, ConformError> {
    let oracle_cfg = OracleConfig::new(&cfg.jar_path, &cfg.shim_source)
        .with_symmetry(i32::try_from(cfg.count_symmetry).unwrap_or(i32::MAX))
        .with_no_overflow(!cfg.allow_overflow)
        .with_solver(JAR_SOLVER)
        .with_timeout(cfg.jar_timeout);
    let shim_classes = ensure_shim_compiled(&oracle_cfg)?;
    let cap = u32::try_from(cfg.count_cap + 1).unwrap_or(u32::MAX);

    // Materialize the todo map as an ordered Vec (BTreeMap iterates in canon
    // order) so the parallel fold-in is deterministic.
    let items: Vec<(PathBuf, Vec<JarTodo>)> = jar_todo
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();

    progress(&format!(
        "stage 2: jar enumeration over {} files",
        items.len()
    ));
    let work = |item: &(PathBuf, Vec<JarTodo>), send: &mut dyn FnMut(&str)| -> JarFileResult {
        send(&format!("stage 2: jar {}", item.0.display()));
        let result = run_oracle_on_file(
            &oracle_cfg,
            &shim_classes,
            &item.0,
            EnumerationCap::UpTo(cap),
        );
        item.1
            .iter()
            .map(|(rel, idx, mettle_count, pos, config_relative)| {
                let (bucket, mismatch) = jar_bucket(&result.outcome, *idx, *mettle_count, rel);
                if *config_relative && bucket == "COUNT_MISMATCH" {
                    ("skip_temporal_config", None, *pos)
                } else {
                    (bucket, mismatch, *pos)
                }
            })
            .collect()
    };
    let mut noop = |_: usize, _: &JarFileResult| {};
    let (results, trig) = parallel_fold(
        &items,
        cfg.jobs,
        cfg.fail_fast,
        progress,
        |item| item.0.display().to_string(),
        &mut noop,
        work,
        |rs: &JarFileResult| {
            rs.iter()
                .find_map(|(_, m, _)| m.clone().map(|line| format!("COUNT_MISMATCH {line}")))
        },
    );

    for rs in results.iter().flatten() {
        for (bucket, mismatch, pos) in rs {
            *report
                .count_buckets
                .entry((*bucket).to_owned())
                .or_default() += 1;
            if let Some(m) = mismatch {
                report.count_mismatches.push(m.clone());
            }
            if let Some(pc) = report.per_command.get_mut(*pos) {
                pc.count_bucket = Some((*bucket).to_owned());
            }
        }
    }
    Ok(trig)
}

/// The count bucket for one command given the jar's file outcome, returning a
/// `COUNT_MISMATCH` line when the counts differ (mirrors the cache-mode
/// `CountBaseline::disposition` mapping).
fn jar_bucket(
    outcome: &FileOutcome,
    idx: usize,
    mettle_count: u64,
    rel: &str,
) -> (&'static str, Option<String>) {
    match outcome {
        FileOutcome::Timeout => ("skip_jar_timeout", None),
        FileOutcome::Error { .. } => ("skip_jar_error", None),
        FileOutcome::Commands(cmds) => {
            match cmds.iter().find(|c| c.index == idx).map(|c| &c.outcome) {
                Some(Outcome::Sat {
                    instance_count: Some(j),
                }) => {
                    if u64::from(*j) == mettle_count {
                        ("count_match", None)
                    } else {
                        (
                            "COUNT_MISMATCH",
                            Some(format!("{rel}[{idx}]: mettle={mettle_count} jar={j}")),
                        )
                    }
                }
                _ => ("skip_jar_error", None),
            }
        }
    }
}

/// The temporal twin of [`classify_count`] (mt-076): count a temporal command's
/// traces the way the jar's own baseline generator does — but only where that
/// number is comparable at all.
///
/// `OracleShim.countInstances` enumerates a temporal command by repeated
/// `A4Solution.next()` (alloy6-temporal.md §(i), source-cited), and mt-076's
/// probe wave pinned what that loop actually walks: the traces of **one static
/// configuration**, across every length in the `steps` range, counting
/// `(states, loop)` assignments raw at each length but never re-emitting an
/// infinite trace already shown at a shorter one.
/// [`TraceEnumerator`] is that loop, so this arm is the same shape as the
/// static one — solve, block, repeat — with the temporal semantics living in
/// `als-core` where they can be tested jar-free.
///
/// **A disagreement is checked before it is called a mismatch.** Because the
/// walk is confined to *one* configuration — whichever the solver's first
/// solution landed on (probe P-076-5) — the jar's banked number is "the traces
/// of sat4j's first configuration" and mettle's is "the traces of mettle's".
/// Where a command's configuration space has more than one member those are
/// **different sets**: measured, `leader.als[3]` gives mettle=1 jar=10001,
/// because the jar's first solution is a full three-node ring and mettle's is
/// the empty model, whose whole space genuinely is one trace (probe P-076-7).
/// So this arm reports the count as [`CountOutcome::JarTodoConfigRelative`]
/// whenever a second configuration exists — an **agreement** still counts as
/// `count_match`, but a **disagreement** is bucketed `skip_temporal_config`
/// instead of raised as a `COUNT_MISMATCH`, which in this repo means "mettle
/// counted wrong". Only a command with a unique configuration can produce a
/// temporal `COUNT_MISMATCH`, and there the alarm means what it says.
///
/// The uniqueness probe costs two solves and runs after the enumeration, whose
/// cost dominates.
#[allow(
    clippy::too_many_arguments,
    reason = "the temporal command plus the same two stage-2 policy inputs as the static arm"
)]
pub(super) fn classify_temporal_count(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    bounds: &BoundsResult,
    ir: &Ir,
    idx: usize,
    cfg: &TemporalSolveConfig,
    count_cap: u64,
    presettled: Option<&'static str>,
) -> CountOutcome {
    if let Some(bucket) = presettled {
        return CountOutcome::Skip(bucket);
    }
    let mut it = match TraceEnumerator::new(world, graph, scoped, bounds, ir, idx, cfg) {
        Ok(it) => it,
        // The budget-on-a-counter-less-backend refusal, bucketed apart exactly
        // as the static arm buckets it (ADR-0027 decision 2).
        Err(TranslateError::BackendCapability { .. }) => {
            return CountOutcome::Skip("skip_backend_capability")
        }
        // The typed steps-scope defers; the verdict arm already bucketed them,
        // so there is nothing here to compare.
        Err(_) => return CountOutcome::Skip("skip_mettle_cap"),
    };
    let mut n = 0u64;
    loop {
        match it.advance(TraceStep::NextPath) {
            Ok(TraceAdvance::Trace(_)) => {
                n += 1;
                if n > count_cap {
                    return CountOutcome::Skip("skip_mettle_cap");
                }
            }
            Ok(TraceAdvance::Exhausted) => break,
            Ok(TraceAdvance::BudgetExhausted) => return CountOutcome::Skip("skip_enum_budget"),
            // A cap hit or an encoder capacity failure is a non-answer, not a
            // count; the verdict arm has already said so in its own bucket.
            Ok(TraceAdvance::PrimaryVarCap { .. } | TraceAdvance::SameConfig) | Err(_) => {
                return CountOutcome::Skip("skip_mettle_cap")
            }
        }
    }
    if it.has_higher_order_skolem() {
        // Same exclusion the static arm applies, decided after the fact because
        // a temporal command lowers once per trace length.
        return CountOutcome::Skip("skip_ho_skolem");
    }
    if unique_configuration(world, graph, scoped, bounds, ir, idx, cfg) {
        CountOutcome::JarTodo(n)
    } else {
        CountOutcome::JarTodoConfigRelative(n)
    }
}

/// Whether this command has exactly **one** static configuration — the
/// condition under which a count *disagreement* is a real finding rather than
/// the two engines counting different sets (see [`classify_temporal_count`]).
///
/// Costs two solves: the first trace, then one `NextConfig`. **Inconclusive is
/// `false`.** A probe that runs out of effort has not shown the configuration
/// unique, and the conservative reading — treat the count as
/// configuration-relative — costs only alarm sensitivity on that one command,
/// while the alternative (dropping the count) would throw away a perfectly good
/// `count_match`. Measured: making this `Err` instead cost one SB-0 match on a
/// command whose re-sweep is expensive.
fn unique_configuration(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    bounds: &BoundsResult,
    ir: &Ir,
    idx: usize,
    cfg: &TemporalSolveConfig,
) -> bool {
    let Ok(mut probe) = TraceEnumerator::new(world, graph, scoped, bounds, ir, idx, cfg) else {
        return false;
    };
    if !matches!(
        probe.advance(TraceStep::NextPath),
        Ok(TraceAdvance::Trace(_))
    ) {
        return false;
    }
    matches!(
        probe.advance(TraceStep::NextConfig),
        // No other configuration exists — either because nothing static is free
        // to vary (`SameConfig`, probe P-076-1) or because the search proved it.
        Ok(TraceAdvance::SameConfig | TraceAdvance::Exhausted)
    )
}
