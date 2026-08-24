//! The mt-037 differential **solve gauge** + counting net, with the mt-054
//! throughput & feedback-loop upgrades.
//!
//! Two stages over the corpus (`corpus/alloytools-models/models`,
//! `corpus/portus-63`, or any given roots):
//!
//! **Stage 1 (always).** Run mettle's own solve pipeline — `compute_universe →
//! compute_bounds → lower_command → solve_goal` — over every root-module command
//! of every `.als` file, under the smoke test's resource discipline (the mt-039
//! lesson: deterministic budgets, `catch_unwind` per command). Compare mettle's
//! SAT/UNSAT against the cached jar verdict ([`baseline`]) and bucket each
//! command into exactly one verdict-stage bucket (asserted: the buckets sum to
//! the command count).
//!
//! Stage 1 runs in two phases under `--jobs` ([`parallel`]). **Phase A** resolves
//! every file once, in parallel. **Phase B** takes the *command* as the unit of
//! work, fanning every command of every file across the pool over a shared
//! `Arc<ResolvedFile>`. Command granularity is what keeps one pathological file
//! from being the whole schedule: `correctChord.als` sums to ~556s across 39
//! commands, so a file-granular sweep bounds at 556s of serial chain no matter
//! how many cores there are, while a command-granular one bounds at its single
//! longest command (~190s). The report is folded in item order — file-sorted,
//! index-ascending — so it stays byte-identical at any job count (STYLE D1/D5).
//!
//! **Stage 2 (`--count`).** For every mettle-SAT command outside the documented
//! count-divergence families ([`detect`]), compare mettle's SB count against the
//! jar's. By default this reads a **cached** [`count_baseline`] (no JVM);
//! `--live-jar` restores the per-file live-JVM path. Everything else is a **typed
//! skip**, never a fabricated mismatch.
//!
//! **The baseline is consulted BEFORE the enumeration (mt-059).** A counting-net
//! command is an exhaustive enumeration — solve, block, solve again — and for
//! roughly half the corpus the cached baseline holds no count to compare
//! against, so no possible result of that enumeration could change the command's
//! bucket. [`count_baseline::CountResolution`] states, once, which baseline
//! entries depend on mettle's count; `classify_count` skips the enumeration for
//! the rest. This declines no comparison — the comparison does not exist — but
//! it does lapse exercise of the incremental enumerator on those models, so
//! `--enumerate-all` forces the old behavior back on deliberately.
//!
//! **The sweep artifact (mt-057).** A committed [`sweep_baseline`]
//! (`baselines/*-sweep-sb<N>.json`) records every command's bucket plus an
//! advisory wall time, and does two things that cost **no coverage**: it
//! supplies the per-command costs the LPT schedule sorts on, and `--delta`
//! reports what moved instead of absolute numbers. It never gates what the
//! gauge runs — every run sweeps every command.
//!
//! This module never prints and never exits (STYLE E3); the bin renders
//! [`SolveGaugeReport`] and sets the process exit code.
//!
//! Split across submodules by concern: `execute` holds the phase-A/phase-B
//! executor (resolve, build, solve, self-check); `count` holds the stage-2
//! counting classification and the live-jar path; `report` holds the report
//! types and the deterministic text renderer. This module keeps the config,
//! file selection/filtering, and [`run_gauge`] orchestration that ties them
//! together.
//!
//! Still over S2's ~500-line soft cap (justification, per S2): what remains is
//! one doc-heavy config struct, the orchestration `run_gauge` feeds, and the
//! in-file test module — splitting further only widens the `pub(super)` surface.

pub mod baseline;
mod count;
pub mod count_baseline;
pub mod detect;
mod execute;
pub(crate) mod parallel;
pub mod refresh;
mod report;
pub mod sweep_baseline;
pub mod telemetry;
pub mod watch;

use std::collections::BTreeMap;
use std::panic;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::error::ConformError;

use baseline::load_baselines;
use count::{run_jar_stage, CountDisp, JarTodo};
use count_baseline::load_count_baselines;
use execute::{command_items, compute_command, resolve_phase, CmdGaugeResult, CmdItem};
use parallel::{lpt_order, parallel_fold_ordered};
pub use report::{PerCommand, SolveGaugeReport};
use sweep_baseline::{command_key, load_sweep_baselines, mode_key, SweepConfig};
use telemetry::{RowId, RunDoneEvent, RunStartEvent, TelemetryEvent, TelemetrySink};

/// Default corpus roots (mirrors [`crate::DEFAULT_CORPUS_ROOTS`] but relative to
/// the workspace root the gauge is handed).
pub const DEFAULT_CORPUS_SUBDIRS: [&str; 2] =
    ["corpus/alloytools-models/models", "corpus/portus-63"];

/// The jar solver factory the counting net pins on both sides (zero native
/// deps). Also the value written into / validated against count-baseline headers.
pub(crate) const JAR_SOLVER: &str = "sat4j";

/// Everything the gauge needs for one run. Budgets default higher than the
/// smoke test's (this is the gauge, not a fast CI net).
#[derive(Debug, Clone)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "independent CLI switches (count/live_jar/fail_fast/allow_overflow), not a state enum"
)]
pub struct GaugeConfig {
    /// Corpus roots to scan — each a directory (walked recursively for `.als`)
    /// or a single `.als` file. Absent roots are skipped cleanly.
    pub roots: Vec<PathBuf>,
    /// Workspace root, for computing the relpath keys the baselines are keyed on.
    pub workspace_root: PathBuf,
    /// Directory holding `*-verdict.json` and `*-count-sb<N>.json` baselines.
    pub baselines_dir: PathBuf,
    /// Per-command SAT conflict budget (over-budget → a typed defer bucket).
    pub conflict_budget: u64,
    /// Per-command encode-effort budget (exceeded → a typed defer bucket).
    pub encode_budget: u64,
    /// Skip encoding a command with more than this many primary variables
    /// (reported as `mettle_defer:primary_var_cap`, never silent).
    pub primary_var_cap: usize,
    /// LEDGER-001 overflow switch: forbid (default) or allow (wrap).
    pub allow_overflow: bool,
    /// Symmetry-breaking predicate cap for **stage 1** (the verdict net).
    pub symmetry: u32,
    /// Symmetry-breaking predicate cap for **stage 2** (the counting net) on both
    /// sides. Default **0**: the ADR-0002 SB-0 counting yardstick.
    pub count_symmetry: u32,
    /// Whether to run stage 2 (the counting net).
    pub count: bool,
    /// Enumerate at most this many mettle instances before skipping a command as
    /// `skip_mettle_cap` (and the jar side is capped at `count_cap + 1`).
    pub count_cap: u64,
    /// Cumulative **effort** budget across one command's whole enumeration.
    pub enum_budget: u64,
    /// mt-059 escape hatch: enumerate every eligible command even where the
    /// count baseline has already settled its bucket, so the *incremental*
    /// enumeration path (`block()` + retained learned clauses) keeps being
    /// exercised on models the baseline cannot compare. Costs a great deal of
    /// wall time and can change nothing but which `skip_*` bucket a
    /// non-comparable command lands in.
    pub enumerate_all: bool,
    /// Reference jar (stage 2 with `--live-jar`, or `--refresh-counts`).
    pub jar_path: PathBuf,
    /// `OracleShim.java` source (stage 2 / refresh).
    pub shim_source: PathBuf,
    /// Per-file JVM timeout for the live jar path / refresh.
    pub jar_timeout: Duration,
    /// mt-054 (a): parallel worker count for stage 1 (and the live jar stage /
    /// refresh). `1` reproduces the pre-mt-054 sequential behavior.
    pub jobs: usize,
    /// mt-054 (b): stage 2 uses the cached count baselines (default) unless this
    /// is set, in which case it runs one live JVM per file.
    pub live_jar: bool,
    /// mt-054 (c): stop the sweep at the first `DISAGREE` / panic / self-check
    /// failure / `COUNT_MISMATCH` (a `partial` report, exit 1).
    pub fail_fast: bool,
    /// mt-054 (c): keep only files whose workspace relpath contains any of these
    /// substrings (empty = keep all).
    pub only: Vec<String>,
    /// mt-054 (c): delta mode — a prior `--json-out` report to filter against.
    pub from_report: Option<PathBuf>,
    /// mt-054 (c): the verdict/count buckets that select a file for a delta re-run.
    pub from_buckets: Vec<String>,
    /// mt-057 (3): diff this run against the sweep baseline and report what
    /// moved (an *extra* section; the canonical report text is untouched).
    pub delta: bool,
    /// mt-057 (3): capture mode — write/refresh the sweep baseline artifact at
    /// this path from this run's results. Implies an unabridged run.
    pub capture_sweep: Option<PathBuf>,
    /// mt-057 (3): the commit to stamp a captured artifact with, for triage.
    /// Advisory metadata only — never validated at load.
    pub capture_commit: Option<String>,
    /// Which SAT backend decides every command (`--solver`, mt-121). The
    /// standing backend selector after ADR-0027 — not a dev knob — but the sweep
    /// and count **baselines are measured on the default**, so a run under any
    /// other backend is comparing against numbers a different solver produced.
    pub backend: als_core::Backend,
}

/// Recursively collects `.als` files under `root` (a dir) or `root` itself (a
/// file), into `out`.
fn collect_als(root: &Path, out: &mut Vec<PathBuf>) {
    if root.is_dir() {
        let Ok(entries) = std::fs::read_dir(root) else {
            return;
        };
        for entry in entries.flatten() {
            collect_als(&entry.path(), out);
        }
    } else if root.extension().is_some_and(|ext| ext == "als") {
        out.push(root.to_path_buf());
    }
}

/// Collects, sorts, and de-duplicates every `.als` file under `roots`.
pub(crate) fn collect_sorted_als(roots: &[PathBuf]) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for root in roots {
        collect_als(root, &mut files);
    }
    files.sort();
    files.dedup();
    files
}

/// The workspace-relative, `/`-normalized key a file is reported under (falling
/// back to the full path when it is outside the workspace).
pub(crate) fn workspace_relpath(path: &Path, workspace_root: &Path) -> String {
    path.strip_prefix(workspace_root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

/// Runs the full gauge and returns the deterministic report.
///
/// `progress` receives transient status lines (phase transitions; `[k/N]` per
/// file; per-command heartbeats). The report never goes through it — the library
/// stays render-free (STYLE E3); the bin points `progress` at stderr (and tees a
/// status file), tests pass a no-op.
///
/// `telemetry` (mt-094) is an optional per-row JSONL sink for `conform watch`'s
/// live dashboard — an observability side channel, like `progress`, that never
/// influences the returned report: every call site below is additive next to
/// something that already runs for another reason (the phase-B completion
/// hook, the per-command start heartbeat), so the report is byte-identical
/// with `telemetry: None` and with a sink attached, at any `--jobs` count. See
/// [`telemetry`]'s module doc.
///
/// # Errors
/// A genuine **tool** failure: a count-baseline whose header disagrees with the
/// run's config (`--count` cache mode), or — under `--count --live-jar` — the
/// reference jar / shim could not be compiled.
///
/// # Panics
/// On an internal accounting bug only (STYLE I1): if the verdict buckets fail to
/// partition the processed commands.
pub fn run_gauge(
    cfg: &GaugeConfig,
    telemetry: Option<&TelemetrySink>,
    progress: &mut dyn FnMut(&str),
) -> Result<SolveGaugeReport, ConformError> {
    // Telemetry-only: seeds `run_done`'s `total_secs`. Never enters the report
    // (STYLE D1/D4) -- the deterministic timing story stays `millis`/`emit_slowest`.
    let run_started = std::time::Instant::now();
    let baseline = load_baselines(&cfg.baselines_dir);

    // Cache stage 2 loads (and config-validates) the count baselines up front;
    // live-jar mode skips them (it recomputes counts per file).
    let count_baseline = if cfg.count && !cfg.live_jar {
        let cb = load_count_baselines(
            &cfg.baselines_dir,
            cfg.count_symmetry,
            cfg.count_cap,
            !cfg.allow_overflow,
            JAR_SOLVER,
            cfg.jar_timeout.as_secs(),
        )?;
        for w in &cb.warnings {
            progress(w);
        }
        Some(cb)
    } else {
        None
    };
    let count_files = count_baseline
        .as_ref()
        .map(|cb| cb.loaded.clone())
        .unwrap_or_default();

    // mt-057: the artifact supplies LPT scheduling costs and, under `--delta`,
    // the buckets to diff against. It is validated *strictly* — a header
    // mismatch is a hard error — exactly when its content can reach the answer,
    // which is `--delta` alone; otherwise a stale one is ignored with a warning
    // rather than failing an unrelated run.
    let sweep = load_sweep_baselines(&cfg.baselines_dir, &sweep_config(cfg), cfg.delta)?;
    for w in &sweep.warnings {
        progress(w);
    }

    let files = select_files(cfg)?;

    let mut report = SolveGaugeReport::new(cfg, &baseline, count_files);

    // Silence per-panic backtraces during the sweep; every panic is caught and
    // bucketed per command (mt-039 discipline). Restored after the parallel region.
    let prev_hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));

    // Phase A: resolve every file once, in parallel. Cheap relative to solving,
    // and it is what lets phase B treat the *command* as the work unit without
    // re-paying parse/resolve per command.
    let resolved = resolve_phase(&files, cfg, progress);
    let items = command_items(&resolved);

    // Phase B: one work item per command. `correctChord`'s 39 commands no longer
    // form a serial chain inside a single worker — the sweep bounds at its single
    // longest command instead of the sum of a file's commands.
    progress(&format!(
        "stage 1: mettle sweep over {} commands in {} files",
        items.len(),
        files.len()
    ));
    let cb_ref = count_baseline.as_ref();
    let work = |item: &CmdItem, send: &mut dyn FnMut(&str)| {
        compute_command(item, cfg, &baseline, cb_ref, telemetry, send)
    };
    // mt-094: `on_result` fires on the coordinator thread in **completion**
    // order (`parallel.rs`'s module doc) — the natural `row_done` hook. It
    // never touches `report`/`jar_todo`/`timings` (those are folded
    // separately, in position order, below), so telemetry cannot move a byte
    // of the deterministic fold.
    let mut on_result = |i: usize, r: &CmdGaugeResult| emit_row_done(telemetry, i, r);
    // mt-057 (2): dispatch longest-first so the tail starts instead of finishing
    // last. Results still come back indexed by their position in `items`, which
    // is (file-sorted, index-ascending) — so this cannot move a byte (STYLE D5).
    // mt-059: hints are read per **mode** — a stage-1 recording says nothing
    // about what the same command costs when a counting run enumerates it.
    let mode = mode_key(&sweep_config(cfg));
    emit_run_start(telemetry, cfg, &mode, &items);
    let order = lpt_order(&items, |it| {
        sweep.command_millis(&it.file.rel, it.idx, &mode)
    });
    let (results, stage1_trig) = parallel_fold_ordered(
        &items,
        &order,
        cfg.jobs,
        cfg.fail_fast,
        progress,
        |it| command_key(&it.file.rel, it.idx),
        &mut on_result,
        work,
        command_trigger,
    );

    panic::set_hook(prev_hook);

    // Fold in item order (never completion order — STYLE D5). `items` is built
    // file-sorted / index-ascending, so this is the same order the pre-mt-057
    // per-file fold produced.
    let mut jar_todo: BTreeMap<PathBuf, Vec<JarTodo>> = BTreeMap::new();
    let mut timings: Vec<(f64, String)> = Vec::new();
    for r in results.iter().flatten() {
        fold_command(r, &mut report, &mut jar_todo, &mut timings);
    }

    // Wall times stay on this side of the wall: they seed the next run's LPT
    // schedule through the artifact, and the stderr slowest-10 table. They never
    // enter the report (STYLE D1/D4).
    let millis = millis_by_command(&timings);
    emit_slowest(&mut timings, progress);

    // Negative space (STYLE I1): every processed command lands in exactly one
    // verdict bucket, so the buckets sum to the command count.
    let bucket_sum: usize = report.verdict_buckets.values().sum();
    assert_eq!(
        bucket_sum, report.commands,
        "verdict buckets must partition the commands"
    );

    let mut trigger = stage1_trig;

    // Live-jar stage 2 (parallel per-file JVMs, ordered fold-in). Cache mode has
    // already resolved every count bucket inside the workers.
    if cfg.count && cfg.live_jar {
        let jar_trig = run_jar_stage(cfg, &jar_todo, &mut report, progress)?;
        if trigger.is_none() {
            trigger = jar_trig;
        }
    }

    report.partial = trigger.is_some();
    report.fail_fast_trigger = trigger;

    // Both of these come last: the delta and the artifact must see the count
    // buckets the live-jar stage patched in.
    if cfg.delta && !sweep.is_empty() {
        report.delta = Some(sweep.delta(&report));
    }
    if let Some(out) = &cfg.capture_sweep {
        write_sweep_capture(cfg, &report, &millis, out, progress)?;
    }
    emit_run_done(telemetry, run_started, &report);
    Ok(report)
}

/// mt-094: the `run_done` telemetry event. A no-op when no sink is attached.
fn emit_run_done(
    telemetry: Option<&TelemetrySink>,
    run_started: std::time::Instant,
    report: &SolveGaugeReport,
) {
    let Some(sink) = telemetry else { return };
    sink.emit(&TelemetryEvent::RunDone(RunDoneEvent {
        ts_ms: telemetry::now_ms(),
        total_secs: run_started.elapsed().as_secs_f64(),
        verdict_buckets: report.verdict_buckets.clone(),
    }));
}

/// mt-094: the `run_start` telemetry event — the run's config plus the whole
/// grid, in [`command_items`]'s file-sorted/index-ascending order (never
/// LPT dispatch order, which is a scheduling detail the grid must not show).
/// A no-op when no sink is attached.
fn emit_run_start(
    telemetry: Option<&TelemetrySink>,
    cfg: &GaugeConfig,
    mode: &str,
    items: &[CmdItem],
) {
    let Some(sink) = telemetry else { return };
    let rows: Vec<RowId> = items
        .iter()
        .enumerate()
        .map(|(i, it)| RowId {
            i,
            key: command_key(&it.file.rel, it.idx),
        })
        .collect();
    sink.emit(&TelemetryEvent::RunStart(RunStartEvent {
        ts_ms: telemetry::now_ms(),
        mode: mode.to_owned(),
        solver: JAR_SOLVER.to_owned(),
        backend: cfg.backend.name().to_owned(),
        backend_signature: Some(cfg.backend.version_signature()),
        jobs: cfg.jobs,
        conflict_budget: cfg.conflict_budget,
        encode_budget: cfg.encode_budget,
        primary_var_cap: cfg.primary_var_cap,
        symmetry: cfg.symmetry,
        count: cfg.count,
        count_symmetry: cfg.count_symmetry,
        rows,
    }));
}

/// mt-094: the `row_done` telemetry event for one folded command result — the
/// `on_result` hook [`parallel::parallel_fold_ordered`] calls in completion
/// order (never folded into `report` itself). A no-op when no sink is
/// attached.
fn emit_row_done(telemetry: Option<&TelemetrySink>, i: usize, r: &CmdGaugeResult) {
    let Some(sink) = telemetry else { return };
    let c = &r.record;
    sink.emit(&TelemetryEvent::RowDone(telemetry::RowDoneEvent {
        ts_ms: telemetry::now_ms(),
        i,
        key: command_key(&c.rel, c.idx),
        bucket: c.verdict_bucket.clone(),
        secs: r.secs,
        disagreement: c.disagreement.clone(),
        self_check_fail: c.self_check_fail.clone(),
        panic_line: c.panic_line.clone(),
    }));
}

/// The run's pinned sweep-baseline header — the fields that decide what a bucket
/// *means*, so a mismatch invalidates the artifact.
fn sweep_config(cfg: &GaugeConfig) -> SweepConfig {
    SweepConfig {
        symmetry: cfg.symmetry,
        conflict_budget: cfg.conflict_budget,
        encode_budget: cfg.encode_budget,
        primary_var_cap: cfg.primary_var_cap,
        no_overflow: !cfg.allow_overflow,
        solver: JAR_SOLVER.to_owned(),
        backend: cfg.backend.name().to_owned(),
        backend_signature: Some(cfg.backend.version_signature()),
        count_enabled: cfg.count,
        count_symmetry: cfg.count_symmetry,
        count_cap: cfg.count_cap,
        enum_budget: cfg.enum_budget,
        enumerate_all: cfg.enumerate_all,
        capture_commit: cfg.capture_commit.clone(),
    }
}

/// `relpath[idx] → rounded milliseconds`, from the collected wall times.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "float→int casts saturate in Rust; the guard keeps the value finite and non-negative"
)]
fn millis_by_command(timings: &[(f64, String)]) -> BTreeMap<String, u64> {
    timings
        .iter()
        .map(|(secs, key)| {
            let ms = (secs * 1000.0).round();
            (key.clone(), if ms > 0.0 { ms as u64 } else { 0 })
        })
        .collect()
}

/// Writes the sweep-baseline artifact for a finished run, refusing any run that
/// cannot honestly serve as a baseline.
///
/// Two ways a run fails that bar, the same failure at bottom — it did not
/// observe every command, so what it records is silence, not fact: fail-fast
/// stopped it, or a `--only` / `--from-report` filter narrowed it. The
/// artifact is *committed*, so a
/// narrowed capture outlives the session and the next reader cannot tell a
/// deliberately-narrow file from an accidentally-narrowed one. There is no
/// opt-out: capture the whole corpus or don't capture.
///
/// # Errors
/// [`ConformError::SweepCaptureRefused`] for a partial or filtered run; I/O or
/// serialization failure from the write itself.
fn write_sweep_capture(
    cfg: &GaugeConfig,
    report: &SolveGaugeReport,
    millis: &BTreeMap<String, u64>,
    out: &Path,
    progress: &mut dyn FnMut(&str),
) -> Result<(), ConformError> {
    if report.partial {
        return Err(ConformError::SweepCaptureRefused {
            reason: "the run stopped early (--fail-fast), so most commands have no recorded bucket",
        });
    }
    if is_filtered(cfg) {
        return Err(ConformError::SweepCaptureRefused {
            reason: "the run was filtered (--only / --from-report), which would overwrite the committed artifact with a narrow one; capture unfiltered",
        });
    }
    // Carry the modes this run did not measure forward from whatever is already
    // at `out` (mt-059): a stage-1 capture must not erase the counting nets'
    // recorded times, and vice versa.
    let prior = sweep_baseline::read_prior(out);
    let file = sweep_baseline::capture(sweep_config(cfg), report, millis, prior.as_ref());
    file.write_atomic(out)?;
    progress(&format!(
        "capture-sweep: {} commands recorded → {}",
        file.entries.len(),
        out.display()
    ));
    Ok(())
}

/// Whether any filter can reduce the command set below "everything under
/// `roots`" — the [`select_files`] switches, in one place so the two stay in
/// step. `from_buckets` is inert without `from_report`, but it is counted
/// anyway: over-refusing a capture costs a re-run, under-refusing commits a lie.
///
/// Narrowed `roots` are deliberately **not** a filter: naming a corpus is how
/// per-corpus artifacts get captured (the count baselines work the same way),
/// and the artifact's own filename records which corpus it covers.
fn is_filtered(cfg: &GaugeConfig) -> bool {
    !cfg.only.is_empty() || cfg.from_report.is_some() || !cfg.from_buckets.is_empty()
}

/// Applies the `--only` and `--from-report` filters to the collected file set.
fn select_files(cfg: &GaugeConfig) -> Result<Vec<PathBuf>, ConformError> {
    let mut files = collect_sorted_als(&cfg.roots);
    if !cfg.only.is_empty() {
        files.retain(|p| keep_only(&workspace_relpath(p, &cfg.workspace_root), &cfg.only));
    }
    if let Some(report_path) = &cfg.from_report {
        let text = std::fs::read_to_string(report_path)?;
        let value: serde_json::Value = serde_json::from_str(&text)?;
        let (present, selected) = from_report_sets(&value, &cfg.from_buckets);
        files.retain(|p| {
            let rel = workspace_relpath(p, &cfg.workspace_root);
            // A file absent from the prior report is always included; otherwise
            // it must have a command in a selected bucket.
            !present.contains(&rel) || selected.contains(&rel)
        });
    }
    Ok(files)
}

/// True when `rel` contains any of the `--only` substrings (empty = keep all).
fn keep_only(rel: &str, only: &[String]) -> bool {
    only.is_empty() || only.iter().any(|s| rel.contains(s))
}

/// From a prior `--json-out` report, the set of relpaths it covered and the set
/// whose `per_command` has any command in a `--from-buckets` bucket.
fn from_report_sets(
    value: &serde_json::Value,
    buckets: &[String],
) -> (
    std::collections::BTreeSet<String>,
    std::collections::BTreeSet<String>,
) {
    let mut present = std::collections::BTreeSet::new();
    let mut selected = std::collections::BTreeSet::new();
    let Some(per_command) = value.get("per_command").and_then(|v| v.as_array()) else {
        return (present, selected);
    };
    for entry in per_command {
        let Some(key) = entry.get("key").and_then(|k| k.as_str()) else {
            continue;
        };
        let rel = key.rsplit_once('[').map_or(key, |(r, _)| r).to_owned();
        present.insert(rel.clone());
        let vb = entry.get("verdict_bucket").and_then(|v| v.as_str());
        let cb = entry.get("count_bucket").and_then(|v| v.as_str());
        let hit = vb.is_some_and(|b| buckets.iter().any(|x| x == b))
            || cb.is_some_and(|b| buckets.iter().any(|x| x == b));
        if hit {
            selected.insert(rel);
        }
    }
    (present, selected)
}

/// Sorts and prints the stderr slowest-commands table (wall-clock; observability
/// only). Ties broken stably by name so the table order is at least stable.
fn emit_slowest(timings: &mut [(f64, String)], progress: &mut dyn FnMut(&str)) {
    timings.sort_by(|a, b| {
        b.0.partial_cmp(&a.0)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| a.1.cmp(&b.1))
    });
    if !timings.is_empty() {
        progress("slowest commands (wall):");
        for (secs, name) in timings.iter().take(10) {
            progress(&format!("  {secs:8.1}s  {name}"));
        }
    }
}

/// The fail-fast trigger one command's result implies, if any.
fn command_trigger(r: &CmdGaugeResult) -> Option<String> {
    let c = &r.record;
    if c.disagreement.is_some() {
        return Some(format!("DISAGREE {}[{}]", c.rel, c.idx));
    }
    if c.panic_line.is_some() {
        return Some(format!("panic {}[{}]", c.rel, c.idx));
    }
    if c.self_check_fail.is_some() {
        return Some(format!("self-check failure {}[{}]", c.rel, c.idx));
    }
    if let CountDisp::Resolved { bucket, .. } = &c.count {
        if bucket == "COUNT_MISMATCH" {
            return Some(format!("COUNT_MISMATCH {}[{}]", c.rel, c.idx));
        }
    }
    None
}

/// Folds one command's result into the report (all shared-state mutation lives
/// here, on the coordinator thread, in item order).
fn fold_command(
    r: &CmdGaugeResult,
    report: &mut SolveGaugeReport,
    jar_todo: &mut BTreeMap<PathBuf, Vec<JarTodo>>,
    timings: &mut Vec<(f64, String)>,
) {
    let c = &r.record;
    timings.push((r.secs, command_key(&c.rel, c.idx)));
    report.commands += 1;
    *report
        .verdict_buckets
        .entry(c.verdict_bucket.clone())
        .or_default() += 1;
    if let Some(d) = &c.disagreement {
        report.disagreements.push(d.clone());
    }
    if let Some(sc) = &c.self_check_fail {
        report.self_check_failures.push(sc.clone());
    }
    if let Some(p) = &c.panic_line {
        report.panics.push(p.clone());
    }
    let pos = report.per_command.len();
    let mut count_bucket = None;
    match &c.count {
        CountDisp::None => {}
        CountDisp::Resolved { bucket, mismatch } => {
            *report.count_buckets.entry(bucket.clone()).or_default() += 1;
            if let Some(m) = mismatch {
                report.count_mismatches.push(m.clone());
            }
            count_bucket = Some(bucket.clone());
        }
        CountDisp::PendingJar(n) => {
            jar_todo.entry(c.canon.clone()).or_default().push((
                c.rel.clone(),
                c.idx,
                *n,
                pos,
                false,
            ));
        }
        CountDisp::PendingJarConfigRelative(n) => {
            jar_todo.entry(c.canon.clone()).or_default().push((
                c.rel.clone(),
                c.idx,
                *n,
                pos,
                true,
            ));
        }
    }
    report.per_command.push(PerCommand {
        key: command_key(&c.rel, c.idx),
        verdict_bucket: c.verdict_bucket.clone(),
        count_bucket,
    });
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "test fixtures assert on known-good values"
)]
mod tests {
    use super::*;

    #[test]
    fn only_filter_matches_any_substring() {
        assert!(keep_only("corpus/book/appendixA/x.als", &[]));
        assert!(keep_only(
            "corpus/book/appendixA/x.als",
            &["appendixA".to_owned()]
        ));
        assert!(!keep_only(
            "corpus/book/chapter2/x.als",
            &["appendixA".to_owned(), "toys".to_owned()]
        ));
        assert!(keep_only(
            "corpus/examples/toys/x.als",
            &["appendixA".to_owned(), "toys".to_owned()]
        ));
    }

    #[test]
    fn from_report_selection() {
        let value = serde_json::json!({
            "per_command": [
                { "key": "a.als[0]", "verdict_bucket": "agree_sat", "count_bucket": "count_match" },
                { "key": "a.als[1]", "verdict_bucket": "DISAGREE" },
                { "key": "b.als[0]", "verdict_bucket": "agree_unsat", "count_bucket": "skip_no_count_baseline" },
            ]
        });
        let (present, selected) = from_report_sets(&value, &["DISAGREE".to_owned()]);
        assert!(present.contains("a.als"));
        assert!(present.contains("b.als"));
        // a.als has a DISAGREE command → selected; b.als does not.
        assert!(selected.contains("a.als"));
        assert!(!selected.contains("b.als"));

        // Selecting by a count bucket picks b.als instead.
        let (_, selected2) = from_report_sets(&value, &["skip_no_count_baseline".to_owned()]);
        assert!(selected2.contains("b.als"));
        assert!(!selected2.contains("a.als"));
    }

    /// Every filter that can shrink the command set bars a capture; nothing else
    /// does. Kept in lockstep with `select_files`.
    #[test]
    fn is_filtered_covers_every_command_set_filter() {
        let base = bare_config();
        assert!(!is_filtered(&base));

        let mut only = bare_config();
        only.only = vec!["portus".to_owned()];
        assert!(is_filtered(&only));

        let mut from_report = bare_config();
        from_report.from_report = Some(PathBuf::from("prior.json"));
        assert!(is_filtered(&from_report));

        // Inert on its own, still counted: over-refusing costs a re-run.
        let mut from_buckets = bare_config();
        from_buckets.from_buckets = vec!["DISAGREE".to_owned()];
        assert!(is_filtered(&from_buckets));

        // Naming a corpus is not a filter — that is how a per-corpus artifact
        // is captured.
        let mut roots = bare_config();
        roots.roots = vec![PathBuf::from("corpus/portus-63")];
        assert!(!is_filtered(&roots));
    }

    #[test]
    fn exit_status_reflects_partial() {
        let cfg = bare_config();
        let mut report = SolveGaugeReport::new(&cfg, &baseline::Baseline::default(), vec![]);
        assert_eq!(report.exit_status(), 0);
        report.partial = true;
        report.fail_fast_trigger = Some("DISAGREE x[0]".to_owned());
        assert_eq!(report.exit_status(), 1);
        assert!(report
            .render_text()
            .contains("PARTIAL (fail-fast after DISAGREE x[0])"));
    }

    /// A zeroed config; tests set only the fields they exercise.
    fn bare_config() -> GaugeConfig {
        GaugeConfig {
            roots: vec![],
            workspace_root: PathBuf::new(),
            baselines_dir: PathBuf::new(),
            conflict_budget: 0,
            encode_budget: 0,
            primary_var_cap: 0,
            allow_overflow: false,
            symmetry: 0,
            count_symmetry: 0,
            count: false,
            count_cap: 0,
            enum_budget: 0,
            enumerate_all: false,
            jar_path: PathBuf::new(),
            shim_source: PathBuf::new(),
            jar_timeout: Duration::from_secs(1),
            jobs: 1,
            live_jar: false,
            fail_fast: false,
            only: vec![],
            from_report: None,
            from_buckets: vec![],
            delta: false,
            capture_sweep: None,
            capture_commit: None,
            backend: als_core::Backend::default(),
        }
    }
}
