//! mt-138 -- `conform bench --solve`: a solve-time head-to-head between
//! mettle (`CaDiCaL`) and the reference Alloy jar (`sat4j`), per command, over
//! the same 167-file corpus [`super::discover_corpus`] finds by default.
//!
//! Both sides run one command at a time (STYLE D1/D4/D5: no parallelism
//! anywhere near a recorded time):
//!
//! - **jar side** ([`crate::shim::run_oracle_on_files`], reused unchanged):
//!   one JVM per file at the LEDGER-001 defaults (symmetry 20, `noOverflow`
//!   true, solver `sat4j`), `OracleShim` timing each command's
//!   translation+solve in-JVM (`elapsed_ms`, mt-138's additive shim field).
//! - **mettle side** ([`mettle::run_all`]): the same pipeline solve-gauge's
//!   stage 1 runs (`compute_universe -> compute_bounds -> lower_command ->
//!   solve_goal`, symmetry 20, solve-gauge's pinned default budgets),
//!   single-threaded, `Instant`-timed per command.
//!
//! The two sides are joined on `(file, command index)`. A row enters the
//! **both-answered** set only when both sides reached an actual SAT/UNSAT
//! verdict (and the jar's timer fired -- see [`Side::Excluded`]'s
//! `jar_missing_elapsed_ms` case); everything else is excluded with a typed,
//! counted reason (a mettle defer bucket, a self-check failure, a jar
//! timeout, a jar per-command error, or a whole file unavailable on one
//! side). Verdict agreement on every both-answered row is asserted here
//! (not solve-gauge's job, whose baseline this bench does not consult) and
//! surfaced as [`SolveBenchReport::disagreements`] -- non-empty is a loud,
//! non-zero-exit failure at the CLI (`bin/conform.rs`), the same pattern
//! [`super::BenchReport`]'s own `disagreements` already uses, chosen over a
//! hard `panic!`/`Err` so the rest of the report -- which is exactly the
//! diagnostic evidence for the disagreement -- still prints (STYLE E2:
//! panics are for internal invariants, not a live cross-check that could
//! legitimately fail on a real bug).

mod mettle;
mod render;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::Duration;

use serde::Serialize;

use crate::config::{EnumerationCap, OracleConfig};
use crate::error::ConformError;
use crate::model::{FileOutcome, Outcome};
use mettle::{FileRun, MettleOutcome, MettleTiming};

use super::CorpusInfo;

#[derive(Debug, Clone)]
pub struct SolveBenchConfig {
    /// Corpus roots to scan recursively for `.als` files. Defaults to
    /// [`super::DEFAULT_CORPUS_ROOTS`] -- the same file set the solve gauge
    /// sweeps.
    pub corpus_roots: Vec<PathBuf>,
    pub jar_path: PathBuf,
    pub shim_source: PathBuf,
    /// Per-file JVM wall-clock budget (LEDGER-001 default: 60s).
    pub jvm_timeout: Duration,
    /// Keep only files whose path contains any of these substrings (empty =
    /// keep all). For scoping a smoke run to a couple of small files without
    /// a second corpus directory.
    pub only: Vec<String>,
}

impl Default for SolveBenchConfig {
    fn default() -> Self {
        Self {
            corpus_roots: super::DEFAULT_CORPUS_ROOTS
                .iter()
                .map(PathBuf::from)
                .collect(),
            jar_path: PathBuf::from("oracle/org.alloytools.alloy.dist.jar"),
            shim_source: PathBuf::from(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/shim/OracleShim.java"
            )),
            jvm_timeout: Duration::from_mins(1),
            only: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct SolveBenchReport {
    pub corpus: CorpusInfo,
    pub summary: SolveBenchSummary,
    /// The 20 both-answered rows with the largest jar time, descending.
    pub top20: Vec<SolveBenchRow>,
    /// Every both-answered row whose verdicts disagreed. Always empty in a
    /// healthy run -- non-empty means a real regression, not a wiring bug
    /// (see module doc).
    pub disagreements: Vec<SolveDisagreement>,
    /// `"file[idx]: mettle_self_check_fail: <detail>"` /
    /// `"file[idx]: mettle_panic: <detail>"` lines for every command excluded
    /// for one of those two reasons -- the `excluded` counts above say how
    /// many, this says which and why (STYLE I2/mt-039: a self-check failure
    /// or panic is a mettle bug, never silently folded into a bare count).
    pub anomalies: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct SolveBenchSummary {
    pub both_answered: usize,
    pub jar_total_ms: f64,
    pub mettle_total_ms: f64,
    pub jar_median_ms: f64,
    pub mettle_median_ms: f64,
    /// Rows excluded from the both-answered set, grouped by typed reason,
    /// sorted by reason (the map is a `BTreeMap`, so this is deterministic
    /// without a sort step).
    pub excluded: Vec<ExcludedReason>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ExcludedReason {
    pub reason: String,
    pub count: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct SolveBenchRow {
    pub file: PathBuf,
    pub index: usize,
    /// `"SAT"` or `"UNSAT"` (the agreed verdict).
    pub verdict: String,
    pub jar_ms: f64,
    pub mettle_ms: f64,
}

#[derive(Debug, Clone, Serialize)]
pub struct SolveDisagreement {
    pub file: PathBuf,
    pub index: usize,
    pub mettle_verdict: String,
    pub jar_verdict: String,
}

impl SolveBenchReport {
    /// # Errors
    /// Only if serialization itself fails.
    pub fn to_json(&self) -> Result<String, ConformError> {
        Ok(serde_json::to_string_pretty(self)?)
    }

    #[must_use]
    pub fn render_text(&self) -> String {
        render::render_text(self)
    }
}

/// Runs the full solve head-to-head and returns the deterministic report.
///
/// # Errors
/// [`ConformError`] from discovering/reading the corpus, compiling/running
/// the jar shim, or an internal file-list misalignment between the jar run
/// and the mettle run (both are driven from the same sorted, deduped file
/// list, so a mismatch is a harness bug, not a corpus issue).
pub fn run_solve_bench(cfg: &SolveBenchConfig) -> Result<SolveBenchReport, ConformError> {
    let discovered = super::discover_corpus(&cfg.corpus_roots);
    let mut files: Vec<PathBuf> = discovered
        .iter()
        .map(|f| std::fs::canonicalize(f).unwrap_or_else(|_| f.clone()))
        .collect();
    files.sort();
    files.dedup();
    if !cfg.only.is_empty() {
        files.retain(|f| {
            let s = f.to_string_lossy();
            cfg.only.iter().any(|needle| s.contains(needle.as_str()))
        });
    }

    let oracle_cfg =
        OracleConfig::new(&cfg.jar_path, &cfg.shim_source).with_timeout(cfg.jvm_timeout);
    let scorecard =
        crate::shim::run_oracle_on_files(&oracle_cfg, &files, EnumerationCap::VerdictOnly)?;
    verify_aligned(&files, &scorecard.files)?;

    let mettle_runs = mettle::run_all(&files);

    let mut top20_pool: Vec<SolveBenchRow> = Vec::new();
    let mut disagreements = Vec::new();
    let mut excluded: BTreeMap<String, usize> = BTreeMap::new();
    let mut anomalies = Vec::new();
    let mut jar_times = Vec::new();
    let mut mettle_times = Vec::new();

    for ((file, mettle_run), jar_result) in
        files.iter().zip(mettle_runs).zip(scorecard.files.iter())
    {
        join_one_file(
            file,
            &jar_result.outcome,
            mettle_run.1,
            &mut top20_pool,
            &mut disagreements,
            &mut excluded,
            &mut anomalies,
            &mut jar_times,
            &mut mettle_times,
        );
    }

    // Descending by jar time; ties broken by (file, index) for a stable,
    // deterministic ordering regardless of join order.
    top20_pool.sort_by(|a, b| {
        b.jar_ms
            .partial_cmp(&a.jar_ms)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| a.file.cmp(&b.file))
            .then_with(|| a.index.cmp(&b.index))
    });
    top20_pool.truncate(20);

    let summary = SolveBenchSummary {
        both_answered: jar_times.len(),
        jar_total_ms: jar_times.iter().sum(),
        mettle_total_ms: mettle_times.iter().sum(),
        jar_median_ms: super::median(jar_times),
        mettle_median_ms: super::median(mettle_times),
        excluded: excluded
            .into_iter()
            .map(|(reason, count)| ExcludedReason { reason, count })
            .collect(),
    };

    Ok(SolveBenchReport {
        corpus: CorpusInfo {
            roots: cfg.corpus_roots.clone(),
            file_count: files.len(),
        },
        summary,
        top20: top20_pool,
        disagreements,
        anomalies,
    })
}

/// One jar command's classification: a real verdict (with its timer, when
/// present) or a typed exclusion reason.
enum JarCmd {
    Verdict(bool, Option<u64>),
    Error(String),
}

/// One side's per-command status for the join: an actual verdict with its
/// timing in milliseconds, or a typed reason it does not count.
enum Side {
    Verdict(bool, f64),
    Excluded(String),
}

fn jar_side(entry: Option<&JarCmd>, file_reason: Option<&str>) -> Side {
    match entry {
        None => Side::Excluded(
            file_reason.map_or_else(|| "jar_missing_command".to_owned(), str::to_owned),
        ),
        Some(JarCmd::Error(reason)) => Side::Excluded(reason.clone()),
        // Recorded by an older cached `OracleShim.class` that predates
        // mt-138's timer -- excluded rather than silently timed as zero, so
        // a stale cache degrades loudly instead of skewing the medians.
        Some(JarCmd::Verdict(_, None)) => Side::Excluded("jar_missing_elapsed_ms".to_owned()),
        #[allow(
            clippy::cast_precision_loss,
            reason = "millisecond counts here never approach 2^53"
        )]
        Some(JarCmd::Verdict(v, Some(ms))) => Side::Verdict(*v, *ms as f64),
    }
}

fn mettle_side(entry: Option<&MettleTiming>, file_reason: Option<&str>) -> Side {
    match entry {
        None => Side::Excluded(
            file_reason.map_or_else(|| "mettle_missing_command".to_owned(), str::to_owned),
        ),
        Some(timing) => match &timing.outcome {
            MettleOutcome::Verdict(v) => Side::Verdict(*v, timing.elapsed.as_secs_f64() * 1_000.0),
            MettleOutcome::Defer(reason) => Side::Excluded((*reason).to_owned()),
            MettleOutcome::SelfCheckFail(_) => Side::Excluded("mettle_self_check_fail".to_owned()),
            MettleOutcome::Panicked(_) => Side::Excluded("mettle_panic".to_owned()),
        },
    }
}

#[allow(
    clippy::too_many_arguments,
    reason = "one file's whole join step: its two outcomes plus the report's accumulators"
)]
fn join_one_file(
    file: &Path,
    jar_outcome: &FileOutcome,
    mettle_run: FileRun,
    rows: &mut Vec<SolveBenchRow>,
    disagreements: &mut Vec<SolveDisagreement>,
    excluded: &mut BTreeMap<String, usize>,
    anomalies: &mut Vec<String>,
    jar_times: &mut Vec<f64>,
    mettle_times: &mut Vec<f64>,
) {
    let (jar_cmds, jar_file_reason): (BTreeMap<usize, JarCmd>, Option<String>) = match jar_outcome {
        FileOutcome::Timeout => (BTreeMap::new(), Some("jar_timeout".to_owned())),
        FileOutcome::Error { kind, .. } => {
            (BTreeMap::new(), Some(format!("jar_error:file:{kind:?}")))
        }
        FileOutcome::Commands(cmds) => {
            let map = cmds
                .iter()
                .map(|c| {
                    let cmd = match &c.outcome {
                        Outcome::Sat { .. } => JarCmd::Verdict(true, c.elapsed_ms),
                        Outcome::Unsat { .. } => JarCmd::Verdict(false, c.elapsed_ms),
                        Outcome::Error { kind, .. } => {
                            JarCmd::Error(format!("jar_error:command:{kind:?}"))
                        }
                    };
                    (c.index, cmd)
                })
                .collect();
            (map, None)
        }
    };

    let (mettle_cmds, mettle_file_reason): (BTreeMap<usize, MettleTiming>, Option<String>) =
        match mettle_run {
            FileRun::Unresolved => (BTreeMap::new(), Some("mettle_unresolved".to_owned())),
            FileRun::Resolved(results) => (results.into_iter().collect(), None),
        };

    let mut indices: BTreeSet<usize> = jar_cmds.keys().copied().collect();
    indices.extend(mettle_cmds.keys().copied());

    if indices.is_empty() {
        if jar_file_reason.is_some() || mettle_file_reason.is_some() {
            *excluded
                .entry("both_sides_unavailable".to_owned())
                .or_default() += 1;
        }
        return;
    }

    for idx in indices {
        let mettle_entry = mettle_cmds.get(&idx);
        if let Some(timing) = mettle_entry {
            match &timing.outcome {
                MettleOutcome::SelfCheckFail(detail) => anomalies.push(format!(
                    "{}[{idx}]: mettle_self_check_fail: {detail}",
                    file.display()
                )),
                MettleOutcome::Panicked(detail) => {
                    anomalies.push(format!("{}[{idx}]: mettle_panic: {detail}", file.display()));
                }
                MettleOutcome::Verdict(_) | MettleOutcome::Defer(_) => {}
            }
        }
        let js = jar_side(jar_cmds.get(&idx), jar_file_reason.as_deref());
        let ms = mettle_side(mettle_entry, mettle_file_reason.as_deref());
        match (js, ms) {
            (Side::Verdict(jv, jar_ms), Side::Verdict(mv, mettle_ms)) => {
                if jv == mv {
                    jar_times.push(jar_ms);
                    mettle_times.push(mettle_ms);
                    rows.push(SolveBenchRow {
                        file: file.to_path_buf(),
                        index: idx,
                        verdict: if jv { "SAT" } else { "UNSAT" }.to_owned(),
                        jar_ms,
                        mettle_ms,
                    });
                } else {
                    disagreements.push(SolveDisagreement {
                        file: file.to_path_buf(),
                        index: idx,
                        mettle_verdict: verdict_label(mv),
                        jar_verdict: verdict_label(jv),
                    });
                }
            }
            (Side::Excluded(jar_reason), Side::Excluded(mettle_reason)) => {
                // Both sides failed to answer, for possibly different
                // reasons -- attribute the row to both rather than
                // arbitrarily picking one (typed and honest, STYLE E5).
                let reason = if jar_reason == mettle_reason {
                    jar_reason
                } else {
                    format!("{jar_reason}+{mettle_reason}")
                };
                *excluded.entry(reason).or_default() += 1;
            }
            (Side::Excluded(reason), Side::Verdict(..))
            | (Side::Verdict(..), Side::Excluded(reason)) => {
                *excluded.entry(reason).or_default() += 1;
            }
        }
    }
}

fn verdict_label(sat: bool) -> String {
    if sat { "SAT" } else { "UNSAT" }.to_owned()
}

/// Both runs are driven off the exact same sorted, deduped `files` list, so
/// their per-file results must line up 1:1 -- checked rather than trusted
/// (mirrors [`super::verify_aligned`]).
fn verify_aligned(
    files: &[PathBuf],
    jar_files: &[crate::model::FileResult],
) -> Result<(), ConformError> {
    if jar_files.len() != files.len() {
        return Err(ConformError::JvmFailed {
            class_name: "OracleShim".to_owned(),
            message: format!(
                "solve bench: expected {} jar file results, got {}",
                files.len(),
                jar_files.len()
            ),
        });
    }
    for (f, jf) in files.iter().zip(jar_files.iter()) {
        if &jf.file != f {
            return Err(ConformError::JvmFailed {
                class_name: "OracleShim".to_owned(),
                message: format!(
                    "solve bench: jar output out of order: expected {}, got {}",
                    f.display(),
                    jf.file.display()
                ),
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
