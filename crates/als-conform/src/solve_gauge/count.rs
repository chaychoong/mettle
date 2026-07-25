//! Stage-2 counting classification: bucketing a mettle-SAT command's exact
//! count against the cached count baseline, or — under `--live-jar` — against
//! a live per-file JVM oracle run.

use std::collections::BTreeMap;
use std::path::PathBuf;

use als_core::ir::Ir;
use als_core::{enumerate, BoundsResult, LoweredGoal, ScopedUniverse, SolveOptions};
use als_types::ResolvedWorld;

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
}

/// The stage-2 disposition after cache lookup (or deferred to the live jar stage).
pub(super) enum CountDisp {
    None,
    Resolved {
        bucket: String,
        mismatch: Option<String>,
    },
    PendingJar(u64),
}

/// A live-jar todo: `(relpath, command index, mettle count, per_command index)`.
pub(super) type JarTodo = (String, usize, u64, usize);

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

    let Ok(mut it) = enumerate(ir, scoped, goal, bounds, opts) else {
        return CountOutcome::Skip("skip_mettle_cap");
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
            .map(|(rel, idx, mettle_count, pos)| {
                let (bucket, mismatch) = jar_bucket(&result.outcome, *idx, *mettle_count, rel);
                (bucket, mismatch, *pos)
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
