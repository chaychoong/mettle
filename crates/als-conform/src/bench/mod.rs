//! mt-024 — one-command conformance + speed benchmark, mettle vs. the
//! pinned reference jar.
//!
//! `conform bench [<corpus-dir>]` (the `bin/conform.rs` subcommand this
//! module backs) produces ONE deterministic report with two sections:
//!
//! - **conformance** — per-stage agreement between mettle and the jar,
//!   reusing the mt-020 `resolve_gauge`/`ResolveGaugeShim` machinery (this
//!   module drives the same shim directly rather than through
//!   `resolve_gauge.rs`, which is a binary, not library surface). Stages
//!   today: `parse` (front end only) and `resolve` (full load+resolve
//!   pipeline, the jar's fused `parseEverything_fromFile` verdict). A
//!   Rung-3 `solve` stage slots in as one more [`StageConformance`] entry —
//!   no schema change.
//! - **speed** — mettle timed per stage (warm, `--threads`-parallel);
//!   the jar timed two honestly-separate ways: **batch** (one JVM,
//!   amortized startup, per-file median from in-JVM timers) and **cold**
//!   (one fresh JVM per file over a small deterministic size-spread
//!   sample, so JVM startup is visible rather than hidden). Ratios are
//!   reported only for the one like-for-like pair (mettle's `resolve`
//!   stage total vs. the jar's batch total — both are "whole fused
//!   pipeline over the whole corpus, one process" numbers).
//!
//! Determinism (STYLE D1-D5): file order is sorted+deduped once at
//! discovery and preserved through every downstream vector (no
//! `HashMap`/completion-order dependence); every JSON struct here derives
//! `Serialize` with fields in a fixed declared order, so key order is
//! stable; timing values obviously vary run to run and are confined to the
//! `speed` section — nothing in `conformance` depends on wall-clock.
//!
//! ## Usage
//!
//! ```text
//! cargo build --release -p als-conform
//! ./target/release/conform bench                       # default 167-file corpus, jar + mettle
//! ./target/release/conform bench --json report.json     # also write the JSON artifact
//! ./target/release/conform bench --skip-jar             # mettle-only, no JDK required
//! ./target/release/conform bench corpus/alloy4fun-mini   # a different corpus dir
//! ./target/release/conform bench --help                 # full flag reference
//! ```
//!
//! Requires the pinned jar at `oracle/org.alloytools.alloy.dist.jar` (see
//! [reference/alloy6-reference.md](../../../../docs/reference/alloy6-reference.md)
//! for how it's fetched/pinned) and a JDK on `PATH` for the jar side;
//! `--skip-jar` needs neither. On the default 167-file corpus this
//! completes in single-digit seconds (well under the bead's 2-minute
//! budget) even from a debug build.

// A benchmark/report module: precision loss converting counts/nanos to
// `f64` for a percentage or a millisecond figure is immaterial (matches
// `resolve_gauge.rs`'s same allow for the same reason).
#![allow(clippy::cast_precision_loss)]

mod jar_side;
mod mettle_side;

use std::path::{Path, PathBuf};
use std::time::Duration;

use serde::Serialize;

use crate::error::ConformError;

// ---------------------------------------------------------------------------
// Report schema
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize)]
pub struct BenchReport {
    pub corpus: CorpusInfo,
    pub conformance: ConformanceSection,
    pub speed: SpeedSection,
}

#[derive(Debug, Clone, Serialize)]
pub struct CorpusInfo {
    /// The roots bench was asked to scan (as given, not canonicalized).
    pub roots: Vec<PathBuf>,
    /// `.als` files found under them, sorted + deduplicated.
    pub file_count: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct ConformanceSection {
    /// `false` under `--skip-jar`: no jar ran, so no agreement was
    /// computed (`stages` is empty; `mettle_summary` is still populated).
    pub jar_available: bool,
    /// Mettle's own accept/reject/panic counts per stage — always
    /// populated, jar or no jar (useful on its own: e.g. confirming zero
    /// panics).
    pub mettle_summary: Vec<StageSummary>,
    /// Per-stage mettle-vs-jar agreement. Empty when `jar_available` is
    /// false. One entry per pipeline stage, in stage order (`parse`,
    /// `resolve`, and `solve` once Rung 3 lands) — appending a stage here
    /// is the whole extension story.
    pub stages: Vec<StageConformance>,
}

#[derive(Debug, Clone, Serialize)]
pub struct StageSummary {
    pub stage: String,
    pub total: usize,
    pub accept: usize,
    pub reject: usize,
    pub panics: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct StageConformance {
    pub stage: String,
    pub compared: usize,
    pub agree: usize,
    pub disagree: usize,
    pub agreement_pct: f64,
    /// `(file, mettle verdict, jar verdict)` for every disagreement,
    /// sorted by file. Expected empty (see docs/reference/
    /// alloy4fun-resolve-pass.md: 167/167 corpus agreement) — a non-empty
    /// list here means the harness found a real regression, not a wiring
    /// bug, and should be investigated as such.
    pub disagreements: Vec<Disagreement>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Disagreement {
    pub file: PathBuf,
    /// `"accept"` or `"reject:<phase>"`.
    pub mettle_verdict: String,
    /// `"accept"` or `"reject:<phase>"`.
    pub jar_verdict: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct SpeedSection {
    pub mettle: MettleSpeed,
    /// `None` under `--skip-jar`.
    pub jar: Option<JarSpeed>,
    /// Only the like-for-like comparisons (see module doc); empty when
    /// `jar` is `None`.
    pub ratios: Vec<RatioEntry>,
}

#[derive(Debug, Clone, Serialize)]
pub struct MettleSpeed {
    pub stages: Vec<StageTiming>,
}

#[derive(Debug, Clone, Serialize)]
pub struct StageTiming {
    pub stage: String,
    pub files: usize,
    /// Wall-clock of the whole timed pass (warm, `--threads`-parallel).
    /// **Timing — varies run to run.**
    pub total_ms: f64,
    /// Median of each file's own `Instant`-measured duration.
    /// **Timing — varies run to run.**
    pub median_us: f64,
}

#[derive(Debug, Clone, Serialize)]
pub struct JarSpeed {
    pub batch: JarBatchTiming,
    pub cold: JarColdTiming,
}

#[derive(Debug, Clone, Serialize)]
pub struct JarBatchTiming {
    pub files: usize,
    /// Whole-process wall-clock around the one JVM (includes its one JVM
    /// startup). **Timing.**
    pub total_ms: f64,
    /// Sum of the shim's own per-file in-JVM timers (excludes startup).
    /// **Timing.**
    pub in_jvm_total_ms: f64,
    /// Median of the shim's per-file in-JVM timers. **Timing.**
    pub median_us: f64,
}

#[derive(Debug, Clone, Serialize)]
pub struct JarColdTiming {
    /// The deterministic size-spread subset actually sampled, in sampled
    /// order.
    pub sample_files: Vec<PathBuf>,
    /// Whole-process wall-clock per sampled file (startup included by
    /// design), same order as `sample_files`. **Timing.**
    pub per_file_ms: Vec<f64>,
    pub median_ms: f64,
    pub mean_ms: f64,
}

#[derive(Debug, Clone, Serialize)]
pub struct RatioEntry {
    pub stage: String,
    pub mettle_total_ms: f64,
    pub jar_batch_total_ms: f64,
    pub jar_over_mettle: f64,
}

impl BenchReport {
    /// Renders the report as pretty-printed JSON (stable key order: struct
    /// field declaration order, no `HashMap`).
    ///
    /// # Errors
    /// Only if serialization itself fails, which does not happen for this
    /// module's own `Serialize` types short of an allocation failure.
    pub fn to_json(&self) -> Result<String, ConformError> {
        Ok(serde_json::to_string_pretty(self)?)
    }

    /// Renders the human-readable text report.
    #[must_use]
    pub fn render_text(&self) -> String {
        render::render_text(self)
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct BenchConfig {
    /// Corpus roots to scan recursively for `.als` files. Defaults to
    /// [`DEFAULT_CORPUS_ROOTS`].
    pub corpus_roots: Vec<PathBuf>,
    pub jar_path: PathBuf,
    pub shim_source: PathBuf,
    pub shim_classes_dir: PathBuf,
    pub threads: usize,
    pub skip_jar: bool,
    /// How many files the cold (fresh-JVM-per-file) sample contains.
    pub cold_sample: usize,
    /// Per-JVM-invocation wall-clock budget (applies to the batch pass and
    /// to each cold-pass invocation individually).
    pub jvm_timeout: Duration,
}

/// The 167-file corpus this bead's spec names by default: alloytools
/// models (jar-pinned build) + portus-63.
pub const DEFAULT_CORPUS_ROOTS: &[&str] = &["corpus/alloytools-models/models", "corpus/portus-63"];

impl Default for BenchConfig {
    fn default() -> Self {
        Self {
            corpus_roots: DEFAULT_CORPUS_ROOTS.iter().map(PathBuf::from).collect(),
            jar_path: PathBuf::from("oracle/org.alloytools.alloy.dist.jar"),
            shim_source: PathBuf::from(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/shim/ResolveGaugeShim.java"
            )),
            shim_classes_dir: std::env::temp_dir().join("als-conform-bench-shim"),
            threads: std::thread::available_parallelism().map_or(4, std::num::NonZero::get),
            skip_jar: false,
            cold_sample: 10,
            jvm_timeout: Duration::from_mins(1),
        }
    }
}

// ---------------------------------------------------------------------------
// Corpus discovery
// ---------------------------------------------------------------------------

/// Recursively collects every `.als` file under each of `roots`, sorted and
/// deduplicated (STYLE D2/C2: no directory-iteration-order dependence
/// survives into the file list `bench` runs over).
#[must_use]
pub fn discover_corpus(roots: &[PathBuf]) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for root in roots {
        collect_into(root, &mut out);
    }
    out.sort();
    out.dedup();
    out
}

fn collect_into(path: &Path, out: &mut Vec<PathBuf>) {
    if path.is_dir() {
        let Ok(entries) = std::fs::read_dir(path) else {
            return;
        };
        let mut children: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
        children.sort();
        for child in children {
            collect_into(&child, out);
        }
    } else if path.extension().is_some_and(|ext| ext == "als") {
        out.push(path.to_path_buf());
    }
}

/// Picks a deterministic, size-spread sample of `k` files from `files` for
/// the cold-JVM pass: sorts by source length (ties broken by path) and
/// takes `k` evenly-spaced indices, so the sample always includes the
/// smallest and largest files and is reproducible run to run without any
/// randomness (STYLE D4).
fn pick_cold_sample(files: &[(PathBuf, String)], k: usize) -> Vec<PathBuf> {
    if files.is_empty() || k == 0 {
        return Vec::new();
    }
    let mut by_size: Vec<&(PathBuf, String)> = files.iter().collect();
    by_size.sort_by(|a, b| a.1.len().cmp(&b.1.len()).then_with(|| a.0.cmp(&b.0)));
    let n = by_size.len();
    let k = k.min(n);
    if k <= 1 {
        return vec![by_size[n / 2].0.clone()];
    }
    (0..k)
        .map(|i| by_size[i * (n - 1) / (k - 1)].0.clone())
        .collect()
}

// ---------------------------------------------------------------------------
// Orchestration
// ---------------------------------------------------------------------------

/// Runs the full bench: discovers the corpus, runs mettle's `parse` and
/// `resolve` stages (warm, timed), and -- unless `cfg.skip_jar` -- compiles
/// and drives `ResolveGaugeShim` for the batch + cold jar timings, then
/// assembles the deterministic [`BenchReport`].
///
/// # Errors
/// Any [`ConformError`] from reading corpus files, compiling the shim, or
/// running the JVM (jar missing, shim source missing, compile failure,
/// spawn failure, timeout, or malformed shim output). Under `cfg.skip_jar`
/// none of the jar-related errors can occur.
pub fn run_bench(cfg: &BenchConfig) -> Result<BenchReport, ConformError> {
    let discovered = discover_corpus(&cfg.corpus_roots);
    let mut files: Vec<PathBuf> = discovered
        .iter()
        .map(|f| std::fs::canonicalize(f).unwrap_or_else(|_| f.clone()))
        .collect();
    files.sort();
    files.dedup();

    let mut sourced: Vec<(PathBuf, String)> = Vec::with_capacity(files.len());
    for f in &files {
        let source = std::fs::read_to_string(f)?;
        sourced.push((f.clone(), source));
    }

    let parse_run = mettle_side::run_parse_stage(&sourced, cfg.threads);
    let resolve_run = mettle_side::run_resolve_stage(&sourced, cfg.threads);

    let mettle_summary = vec![
        stage_summary("parse", &parse_run),
        stage_summary("resolve", &resolve_run),
    ];
    let mettle_speed = MettleSpeed {
        stages: vec![
            stage_timing("parse", &parse_run),
            stage_timing("resolve", &resolve_run),
        ],
    };

    let (stages, jar_speed) = if cfg.skip_jar {
        (Vec::new(), None)
    } else {
        let classpath =
            jar_side::ensure_compiled(&cfg.jar_path, &cfg.shim_source, &cfg.shim_classes_dir)?;
        let (jar_lines, batch_wall) = jar_side::run_batch(&classpath, &files, cfg.jvm_timeout)?;
        verify_aligned(&files, &jar_lines)?;

        let stages = vec![
            build_parse_conformance(&files, &parse_run, &jar_lines),
            build_resolve_conformance(&files, &resolve_run, &jar_lines),
        ];

        let in_jvm_total_ms: f64 = jar_lines.iter().map(|l| l.nanos as f64 / 1_000_000.0).sum();
        let jar_median_us = median(jar_lines.iter().map(|l| l.nanos as f64 / 1_000.0).collect());
        let batch = JarBatchTiming {
            files: jar_lines.len(),
            total_ms: duration_ms(batch_wall),
            in_jvm_total_ms,
            median_us: jar_median_us,
        };

        let cold_sample = pick_cold_sample(&sourced, cfg.cold_sample);
        let cold_results = jar_side::run_cold(&classpath, &cold_sample, cfg.jvm_timeout)?;
        let per_file_ms: Vec<f64> = cold_results.iter().map(|(_, d)| duration_ms(*d)).collect();
        let cold = JarColdTiming {
            sample_files: cold_results.iter().map(|(p, _)| p.clone()).collect(),
            median_ms: median(per_file_ms.clone()),
            mean_ms: mean(&per_file_ms),
            per_file_ms,
        };

        (stages, Some(JarSpeed { batch, cold }))
    };

    // Looked up by name, not position: the jar's verdict is a fused
    // parse+resolve call, so the only like-for-like mettle number is
    // whichever stage represents "the whole pipeline" -- today that's
    // `"resolve"`, but a positional index would silently point at the
    // wrong stage if a future stage were inserted before it.
    let ratios = jar_speed
        .as_ref()
        .and_then(|js| {
            mettle_speed
                .stages
                .iter()
                .find(|s| s.stage == "resolve")
                .map(|resolve_stage| {
                    vec![RatioEntry {
                        stage: "resolve".to_string(),
                        mettle_total_ms: resolve_stage.total_ms,
                        jar_batch_total_ms: js.batch.total_ms,
                        jar_over_mettle: if resolve_stage.total_ms > 0.0 {
                            js.batch.total_ms / resolve_stage.total_ms
                        } else {
                            0.0
                        },
                    }]
                })
        })
        .unwrap_or_default();

    Ok(BenchReport {
        corpus: CorpusInfo {
            roots: cfg.corpus_roots.clone(),
            file_count: files.len(),
        },
        conformance: ConformanceSection {
            jar_available: !cfg.skip_jar,
            mettle_summary,
            stages,
        },
        speed: SpeedSection {
            mettle: mettle_speed,
            jar: jar_speed,
            ratios,
        },
    })
}

/// The batch shim output must be exactly `files.len()` lines in `files`
/// order (the shim's own contract: "one object per input file, in list
/// order") -- checked explicitly rather than trusted, since a silent
/// misalignment would make every downstream conformance number meaningless.
fn verify_aligned(files: &[PathBuf], jar_lines: &[jar_side::JarLine]) -> Result<(), ConformError> {
    if jar_lines.len() != files.len() {
        return Err(ConformError::JvmFailed {
            class_name: "ResolveGaugeShim".to_string(),
            message: format!(
                "expected {} verdict lines, got {}",
                files.len(),
                jar_lines.len()
            ),
        });
    }
    for (f, line) in files.iter().zip(jar_lines.iter()) {
        if line.file != f.to_string_lossy() {
            return Err(ConformError::JvmFailed {
                class_name: "ResolveGaugeShim".to_string(),
                message: format!(
                    "shim output out of order: expected {}, got {}",
                    f.display(),
                    line.file
                ),
            });
        }
    }
    Ok(())
}

fn stage_summary(stage: &str, run: &mettle_side::StageRun) -> StageSummary {
    let total = run.results.len();
    let accept = run.results.iter().filter(|r| r.verdict.ok).count();
    let panics = run
        .results
        .iter()
        .filter(|r| r.verdict.phase == "panic")
        .count();
    StageSummary {
        stage: stage.to_string(),
        total,
        accept,
        reject: total - accept,
        panics,
    }
}

fn stage_timing(stage: &str, run: &mettle_side::StageRun) -> StageTiming {
    let micros: Vec<f64> = run
        .results
        .iter()
        .map(|r| r.elapsed.as_secs_f64() * 1_000_000.0)
        .collect();
    StageTiming {
        stage: stage.to_string(),
        files: run.results.len(),
        total_ms: duration_ms(run.wall_total),
        median_us: median(micros),
    }
}

fn mettle_label(verdict: &mettle_side::StageVerdict) -> String {
    if verdict.ok {
        "accept".to_string()
    } else {
        format!("reject:{}", verdict.phase)
    }
}

fn jar_label(ok: bool, phase: Option<&str>) -> String {
    if ok {
        "accept".to_string()
    } else {
        format!("reject:{}", phase.unwrap_or("unknown"))
    }
}

/// Builds the `parse` stage's conformance table. mettle's parse-stage
/// verdict comes from the dedicated `parse_run` (front end only); the
/// jar's parse-stage verdict is derived from the fused shim call: it
/// failed at the parse stage only if `phase == "parse"` (a `"resolve"`
/// rejection means the file *did* parse, matching mettle's own
/// `phase == "load" | "resolve"` cases counting as parse-accept).
fn build_parse_conformance(
    files: &[PathBuf],
    parse_run: &mettle_side::StageRun,
    jar_lines: &[jar_side::JarLine],
) -> StageConformance {
    let mut disagreements = Vec::new();
    let mut agree = 0usize;
    for ((file, m), j) in files
        .iter()
        .zip(parse_run.results.iter())
        .zip(jar_lines.iter())
    {
        let mettle_ok = m.verdict.ok;
        let jar_ok = j.ok || j.phase.as_deref() != Some("parse");
        if mettle_ok == jar_ok {
            agree += 1;
        } else {
            disagreements.push(Disagreement {
                file: file.clone(),
                mettle_verdict: mettle_label(&m.verdict),
                jar_verdict: jar_label(jar_ok, j.phase.as_deref()),
            });
        }
    }
    finish_stage("parse", files.len(), agree, disagreements)
}

/// Builds the `resolve` stage's conformance table: mettle's full
/// load+resolve verdict vs. the jar's fused `ok` field directly.
fn build_resolve_conformance(
    files: &[PathBuf],
    resolve_run: &mettle_side::StageRun,
    jar_lines: &[jar_side::JarLine],
) -> StageConformance {
    let mut disagreements = Vec::new();
    let mut agree = 0usize;
    for ((file, m), j) in files
        .iter()
        .zip(resolve_run.results.iter())
        .zip(jar_lines.iter())
    {
        if m.verdict.ok == j.ok {
            agree += 1;
        } else {
            disagreements.push(Disagreement {
                file: file.clone(),
                mettle_verdict: mettle_label(&m.verdict),
                jar_verdict: jar_label(j.ok, j.phase.as_deref()),
            });
        }
    }
    finish_stage("resolve", files.len(), agree, disagreements)
}

fn finish_stage(
    stage: &str,
    compared: usize,
    agree: usize,
    disagreements: Vec<Disagreement>,
) -> StageConformance {
    StageConformance {
        stage: stage.to_string(),
        compared,
        agree,
        disagree: compared - agree,
        agreement_pct: if compared > 0 {
            100.0 * agree as f64 / compared as f64
        } else {
            0.0
        },
        disagreements,
    }
}

fn duration_ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1_000.0
}

fn median(mut values: Vec<f64>) -> f64 {
    if values.is_empty() {
        return 0.0;
    }
    values.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let n = values.len();
    if n % 2 == 1 {
        values[n / 2]
    } else {
        f64::midpoint(values[n / 2 - 1], values[n / 2])
    }
}

fn mean(values: &[f64]) -> f64 {
    if values.is_empty() {
        0.0
    } else {
        values.iter().sum::<f64>() / values.len() as f64
    }
}

mod render;

#[cfg(test)]
mod tests;
