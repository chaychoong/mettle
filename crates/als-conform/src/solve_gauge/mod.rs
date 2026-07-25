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
//! **Over STYLE S2's ~500-line soft cap** (justification, per S2): the gauge's
//! two stages, its parallel driver, and its report renderer share one
//! `GaugeConfig`/`SolveGaugeReport` pair and one fold order, so splitting them
//! trades a long file for a wide cross-module surface of `pub(crate)` internals.
//! A split is filed as its own bead rather than done piecemeal here.

pub mod baseline;
pub mod count_baseline;
pub mod detect;
pub(crate) mod parallel;
pub mod refresh;
pub mod sweep_baseline;

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::time::Duration;

use als_core::bounds::Bounds;
use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, enumerate, lower_command, self_check, solve_goal,
    BoundsResult, LoweredGoal, ScopedUniverse, SolveOptions, SolveVerdict, TranslateError,
};
use als_types::{FilesystemLoader, ModuleGraph, ResolvedWorld};
use serde::Serialize;

use crate::config::{EnumerationCap, OracleConfig};
use crate::error::ConformError;
use crate::model::{FileOutcome, Outcome};
use crate::shim::{ensure_shim_compiled, run_oracle_on_file};

use baseline::{load_baselines, JarVerdict};
use count_baseline::{load_count_baselines, CountBaseline};
use detect::{lower_defer_class, ordered_abstract_partition};
use parallel::{lpt_order, parallel_fold, parallel_fold_ordered};
use sweep_baseline::{command_key, load_sweep_baselines, SweepConfig, SweepDelta};

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
}

/// One command's entry in the deterministic per-command report array (mt-054 (c),
/// for delta mode). Filled in file-sorted, index-ascending order.
#[derive(Debug, Clone, Serialize)]
pub struct PerCommand {
    /// `relpath[idx]`.
    pub key: String,
    /// The verdict-stage bucket this command landed in.
    pub verdict_bucket: String,
    /// The counting-net bucket, when stage 2 ran and covered this command.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub count_bucket: Option<String>,
}

/// The gauge's deterministic report. `BTreeMap`s serialize/iterate in key order
/// and every `Vec` is filled in file-sorted, index-ascending order, so a full
/// (non-fail-fast) run is byte-identical run to run and at any job count (STYLE
/// D1). A fail-fast `partial` run is explicitly not byte-stable across job counts.
#[derive(Debug, Clone, Serialize)]
pub struct SolveGaugeReport {
    /// Total root-module commands processed.
    pub commands: usize,
    /// Names of the `*-verdict.json` baselines merged.
    pub baseline_files: Vec<String>,
    /// Names of the `*-count-sb<N>.json` count baselines merged (cache stage 2).
    pub count_baseline_files: Vec<String>,
    /// Per-command baseline entries loaded.
    pub baseline_entries: usize,
    /// Verdict-stage buckets; these sum to [`Self::commands`] (asserted).
    pub verdict_buckets: BTreeMap<String, usize>,
    /// Every verdict disagreement, `relpath[idx]: mettle=… jar=…`.
    pub disagreements: Vec<String>,
    /// Every SAT instance that failed its own self-check (a mettle bug).
    pub self_check_failures: Vec<String>,
    /// Every command whose mettle pipeline panicked (a mettle bug).
    pub panics: Vec<String>,
    /// Stage-1 symmetry-breaking cap the verdict net ran at.
    pub symmetry: u32,
    /// Stage-2 symmetry-breaking cap the counting net ran at on both sides.
    pub count_symmetry: u32,
    /// Whether stage 2 ran.
    pub count_enabled: bool,
    /// Counting-net buckets (`count_match` / `COUNT_MISMATCH` / `skip_*`).
    pub count_buckets: BTreeMap<String, usize>,
    /// Every count mismatch, `relpath[idx]: mettle=m jar=j`.
    pub count_mismatches: Vec<String>,
    /// mt-054 (c): per-command results, in file-sorted, index-ascending order.
    pub per_command: Vec<PerCommand>,
    /// mt-054 (c): a fail-fast run that stopped early is a partial report.
    pub partial: bool,
    /// mt-054 (c): what tripped fail-fast (for the `PARTIAL (...)` marker).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fail_fast_trigger: Option<String>,
    /// mt-057 (3): what moved relative to the sweep baseline (`--delta`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub delta: Option<SweepDelta>,
}

impl SolveGaugeReport {
    fn new(cfg: &GaugeConfig, baseline: &baseline::Baseline, count_files: Vec<String>) -> Self {
        Self {
            commands: 0,
            baseline_files: baseline.loaded.clone(),
            count_baseline_files: count_files,
            baseline_entries: baseline.command_count(),
            verdict_buckets: BTreeMap::new(),
            disagreements: Vec::new(),
            self_check_failures: Vec::new(),
            panics: Vec::new(),
            symmetry: cfg.symmetry,
            count_symmetry: cfg.count_symmetry,
            count_enabled: cfg.count,
            count_buckets: BTreeMap::new(),
            count_mismatches: Vec::new(),
            per_command: Vec::new(),
            partial: false,
            fail_fast_trigger: None,
            delta: None,
        }
    }
}

/// The number of primary variables the bounds imply (`Σ upper − lower`).
fn primary_var_count(bounds: &Bounds) -> usize {
    bounds
        .iter()
        .map(|(_, b)| b.upper().len() - b.lower().len())
        .sum()
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

/// The stage-2 disposition of one SAT command after mettle-side classification.
#[derive(Clone, Copy)]
enum CountOutcome {
    /// A typed skip: the given `count_buckets` key.
    Skip(&'static str),
    /// Eligible: mettle's exact SB count, awaiting the jar comparison.
    JarTodo(u64),
}

/// The fully-computed result of classifying one command — no shared state is
/// mutated inside the `catch_unwind`d closure.
struct CmdResult {
    verdict_bucket: String,
    disagreement: Option<String>,
    self_check_fail: Option<String>,
    count: Option<CountOutcome>,
}

impl CmdResult {
    fn defer(reason: String) -> Self {
        Self {
            verdict_bucket: reason,
            disagreement: None,
            self_check_fail: None,
            count: None,
        }
    }
}

/// The stage-2 disposition after cache lookup (or deferred to the live jar stage).
enum CountDisp {
    None,
    Resolved {
        bucket: String,
        mismatch: Option<String>,
    },
    PendingJar(u64),
}

/// One command, resolved into everything the coordinator needs to fold it into
/// the report deterministically — computed entirely on a worker thread.
struct CmdRecord {
    rel: String,
    idx: usize,
    canon: PathBuf,
    verdict_bucket: String,
    disagreement: Option<String>,
    /// Pre-formatted `relpath[idx]: <detail>` self-check line.
    self_check_fail: Option<String>,
    /// Pre-formatted `relpath[idx]: <msg>` panic line.
    panic_line: Option<String>,
    count: CountDisp,
}

/// One file's parse + module-load + resolve result, computed once in phase A and
/// then shared **read-only** across every command worker in phase B.
///
/// This is what makes command-level parallelism affordable: the per-file work
/// commands used to share by running serially in one worker is still paid
/// exactly once, and the commands fan out over an `Arc` of it.
struct ResolvedFile {
    rel: String,
    canon: PathBuf,
    graph: ModuleGraph,
    world: ResolvedWorld,
    /// The root module's command indices, ascending — the only ones the gauge
    /// sweeps (an imported module's commands are not this file's).
    command_indices: Vec<usize>,
}

/// One unit of phase-B work: a command, plus the shared resolve of its file.
struct CmdItem {
    file: std::sync::Arc<ResolvedFile>,
    idx: usize,
}

/// One command's fully-computed gauge result (no shared state touched).
struct CmdGaugeResult {
    record: CmdRecord,
    /// Wall seconds — the stderr slowest-10 table and the next run's LPT
    /// schedule. Nondeterministic; never enters the report (STYLE D1/D4).
    secs: f64,
}

/// Runs the full gauge and returns the deterministic report.
///
/// `progress` receives transient status lines (phase transitions; `[k/N]` per
/// file; per-command heartbeats). The report never goes through it — the library
/// stays render-free (STYLE E3); the bin points `progress` at stderr (and tees a
/// status file), tests pass a no-op.
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
    progress: &mut dyn FnMut(&str),
) -> Result<SolveGaugeReport, ConformError> {
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
        compute_command(item, cfg, &baseline, cb_ref, send)
    };
    let mut noop = |_: usize, _: &CmdGaugeResult| {};
    // mt-057 (2): dispatch longest-first so the tail starts instead of finishing
    // last. Results still come back indexed by their position in `items`, which
    // is (file-sorted, index-ascending) — so this cannot move a byte (STYLE D5).
    let order = lpt_order(&items, |it| sweep.command_millis(&it.file.rel, it.idx));
    let (results, stage1_trig) = parallel_fold_ordered(
        &items,
        &order,
        cfg.jobs,
        cfg.fail_fast,
        progress,
        |it| command_key(&it.file.rel, it.idx),
        &mut noop,
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
    Ok(report)
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
        count_enabled: cfg.count,
        count_symmetry: cfg.count_symmetry,
        count_cap: cfg.count_cap,
        enum_budget: cfg.enum_budget,
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
    let file = sweep_baseline::capture(sweep_config(cfg), report, millis);
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

/// A live-jar todo: `(relpath, command index, mettle count, per_command index)`.
type JarTodo = (String, usize, u64, usize);

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
            jar_todo
                .entry(c.canon.clone())
                .or_default()
                .push((c.rel.clone(), c.idx, *n, pos));
        }
    }
    report.per_command.push(PerCommand {
        key: command_key(&c.rel, c.idx),
        verdict_bucket: c.verdict_bucket.clone(),
        count_bucket,
    });
}

/// **Phase A** — parse, module-load and resolve every file, in parallel, once.
///
/// A file that fails to canonicalize / load / resolve yields `None` and simply
/// contributes no commands, exactly as the pre-mt-057 per-file sweep did.
/// Emits a resolve-cost summary through `progress` so the phase's share of the
/// run stays observable rather than assumed.
fn resolve_phase(
    files: &[PathBuf],
    cfg: &GaugeConfig,
    progress: &mut dyn FnMut(&str),
) -> Vec<Option<std::sync::Arc<ResolvedFile>>> {
    progress(&format!("phase A: resolving {} files", files.len()));
    let work = |path: &PathBuf, _send: &mut dyn FnMut(&str)| {
        let started = std::time::Instant::now();
        let file = resolve_file(path, &cfg.workspace_root);
        (
            file.map(std::sync::Arc::new),
            started.elapsed().as_secs_f64(),
        )
    };
    let mut noop = |_: usize, _: &(Option<std::sync::Arc<ResolvedFile>>, f64)| {};
    // No LPT here: resolve cost is not recorded in the artifact, and this phase
    // is cheap enough that a schedule would be noise.
    let (results, _) = parallel_fold(
        files,
        cfg.jobs,
        false,
        progress,
        |p| workspace_relpath(p, &cfg.workspace_root),
        &mut noop,
        work,
        |_| None,
    );

    let mut costs: Vec<(f64, String)> = Vec::new();
    let mut resolved = Vec::with_capacity(files.len());
    for (r, path) in results.into_iter().zip(files) {
        let (file, secs) = r.unwrap_or((None, 0.0));
        costs.push((secs, workspace_relpath(path, &cfg.workspace_root)));
        resolved.push(file);
    }
    report_resolve_cost(&mut costs, progress);
    resolved
}

/// Summarizes phase A's cost on stderr: the total and the five worst files, so
/// "is the hoist paying for itself" is measured rather than assumed.
fn report_resolve_cost(costs: &mut [(f64, String)], progress: &mut dyn FnMut(&str)) {
    let total: f64 = costs.iter().map(|(s, _)| s).sum();
    costs.sort_by(|a, b| {
        b.0.partial_cmp(&a.0)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| a.1.cmp(&b.1))
    });
    progress(&format!("phase A: {total:.1}s of resolve work (summed)"));
    for (secs, name) in costs.iter().take(5) {
        progress(&format!("  {secs:8.2}s  {name}"));
    }
}

/// Loads and resolves one `.als` file into the shared, read-only form phase B
/// fans out over. Returns `None` for any file the pipeline cannot get as far as
/// a resolved world for.
fn resolve_file(path: &Path, workspace_root: &Path) -> Option<ResolvedFile> {
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
        rel: workspace_relpath(path, workspace_root),
        canon,
        graph,
        world,
        command_indices,
    })
}

/// Flattens phase A into the phase-B work queue, in **file-sorted,
/// index-ascending** order — the order the report folds in, so a command's
/// position in this vector is its position in `per_command`.
///
/// A fast-lane-skipped command stays in the queue and returns its typed skip
/// immediately. Dropping it here would be marginally cheaper and would delete it
/// from `verdict_buckets` and `per_command` — the skip must stay *counted*
/// (STYLE I1: the buckets partition the commands), so it keeps its slot.
fn command_items(resolved: &[Option<std::sync::Arc<ResolvedFile>>]) -> Vec<CmdItem> {
    let mut items = Vec::new();
    for file in resolved.iter().flatten() {
        for &idx in &file.command_indices {
            items.push(CmdItem {
                file: std::sync::Arc::clone(file),
                idx,
            });
        }
    }
    items
}

/// **Phase B** — builds, solves and (if `--count`) counts one command, on a
/// worker thread, touching no shared report state. Emits a start heartbeat and,
/// when slow, an elapsed line through `send` (stderr — the report stays
/// deterministic; wall-clock lives only here).
fn compute_command(
    item: &CmdItem,
    cfg: &GaugeConfig,
    baseline: &baseline::Baseline,
    count_baseline: Option<&CountBaseline>,
    send: &mut dyn FnMut(&str),
) -> CmdGaugeResult {
    let file = &item.file;
    let (rel, idx) = (file.rel.as_str(), item.idx);
    let Ok(scoped) = compute_universe(&file.world, &file.graph, &file.world.commands[idx]) else {
        return CmdGaugeResult {
            record: CmdRecord {
                rel: rel.to_owned(),
                idx,
                canon: file.canon.clone(),
                verdict_bucket: "mettle_defer:scope".to_owned(),
                disagreement: None,
                self_check_fail: None,
                panic_line: None,
                count: CountDisp::None,
            },
            secs: 0.0,
        };
    };

    send(&format!("  {rel}[{idx}] …"));
    let started = std::time::Instant::now();
    let outcome = panic::catch_unwind(AssertUnwindSafe(|| {
        classify_command(&file.world, &file.graph, &scoped, baseline, cfg, rel, idx)
    }));
    let secs = started.elapsed().as_secs_f64();
    if secs > 5.0 {
        send(&format!("  {rel}[{idx}] took {secs:.1}s"));
    }

    let record = match outcome {
        Ok(cmd) => {
            let count = resolve_count(cmd.count, cfg.live_jar, count_baseline, rel, idx);
            CmdRecord {
                rel: rel.to_owned(),
                idx,
                canon: file.canon.clone(),
                verdict_bucket: cmd.verdict_bucket,
                disagreement: cmd.disagreement,
                self_check_fail: cmd.self_check_fail.map(|sc| format!("{rel}[{idx}]: {sc}")),
                panic_line: None,
                count,
            }
        }
        Err(payload) => {
            let msg = payload
                .downcast_ref::<&str>()
                .map(|s| (*s).to_owned())
                .or_else(|| payload.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "non-string panic payload".to_owned());
            CmdRecord {
                rel: rel.to_owned(),
                idx,
                canon: file.canon.clone(),
                verdict_bucket: "panic".to_owned(),
                disagreement: None,
                self_check_fail: None,
                panic_line: Some(format!("{rel}[{idx}]: {msg}")),
                count: CountDisp::None,
            }
        }
    };
    CmdGaugeResult { record, secs }
}

/// Resolves a mettle-side [`CountOutcome`] into its report disposition: a typed
/// skip stays resolved; a `JarTodo` is resolved against the cache (default) or
/// deferred to the live jar stage (`--live-jar`).
fn resolve_count(
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

/// Builds, solves, and (if `--count`) classifies the count for one command.
/// Returns a fully-computed [`CmdResult`]; mutates nothing shared.
fn classify_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    baseline: &baseline::Baseline,
    cfg: &GaugeConfig,
    rel: &str,
    idx: usize,
) -> CmdResult {
    let mut ir = Ir::default();
    let bounds = compute_bounds(world, scoped, &mut ir);
    let goal = match lower_command(world, graph, scoped, &bounds, &mut ir, idx) {
        Ok(g) => g,
        Err(e) => return CmdResult::defer(format!("mettle_defer:lower:{}", lower_defer_class(&e))),
    };
    if primary_var_count(&bounds.bounds) > cfg.primary_var_cap {
        return CmdResult::defer("mettle_defer:primary_var_cap".to_owned());
    }

    // `expect 1` forces symmetry off on both stages (translation-ref §3/§16.4).
    let expect_one = matches!(
        world.commands[idx].expect,
        Some(als_syntax::ast::Expect::Sat)
    );
    let stage1_sym = if expect_one { 0 } else { cfg.symmetry };
    let stage2_sym = if expect_one { 0 } else { cfg.count_symmetry };

    let opts = SolveOptions {
        allow_overflow: cfg.allow_overflow,
        conflict_budget: Some(cfg.conflict_budget),
        encode_budget: Some(cfg.encode_budget),
        symmetry: stage1_sym,
        ..SolveOptions::default()
    };
    let (sat, self_check_fail) = match solve_goal(&ir, scoped, &goal, &bounds, &opts) {
        Ok(SolveVerdict::Sat(inst)) => {
            let sc = self_check(&ir, scoped, &goal, &inst, &opts, &bounds.bounds)
                .err()
                .map(|f| f.to_string());
            (true, sc)
        }
        Ok(SolveVerdict::Unsat) => (false, None),
        Ok(SolveVerdict::Unknown) => {
            return CmdResult::defer("mettle_defer:over_budget".to_owned())
        }
        Err(TranslateError::CapacityExceeded { .. }) => {
            return CmdResult::defer("mettle_defer:capacity".to_owned())
        }
        Err(_) => return CmdResult::defer("mettle_defer:encode".to_owned()),
    };

    let baseline_v = baseline.lookup(rel, idx);
    let (verdict_bucket, disagreement) = compare_verdict(baseline_v, sat, rel, idx);

    let count = if cfg.count && sat && matches!(baseline_v, None | Some(JarVerdict::Sat)) {
        let enum_opts = SolveOptions {
            enum_effort_budget: Some(cfg.enum_budget),
            symmetry: stage2_sym,
            ..opts
        };
        Some(classify_count(
            &ir,
            scoped,
            &goal,
            &bounds,
            world,
            &enum_opts,
            cfg.count_cap,
        ))
    } else {
        None
    };

    CmdResult {
        verdict_bucket,
        disagreement,
        self_check_fail,
        count,
    }
}

/// Maps `(baseline verdict, mettle sat)` to the single verdict bucket + optional
/// disagreement line.
fn compare_verdict(
    baseline_v: Option<JarVerdict>,
    sat: bool,
    rel: &str,
    idx: usize,
) -> (String, Option<String>) {
    match baseline_v {
        None => ("no_baseline".to_owned(), None),
        Some(JarVerdict::Nonverdict) => ("jar_nonverdict".to_owned(), None),
        Some(JarVerdict::Sat) => {
            if sat {
                ("agree_sat".to_owned(), None)
            } else {
                (
                    "DISAGREE".to_owned(),
                    Some(format!("{rel}[{idx}]: mettle=UNSAT jar=SAT")),
                )
            }
        }
        Some(JarVerdict::Unsat) => {
            if sat {
                (
                    "DISAGREE".to_owned(),
                    Some(format!("{rel}[{idx}]: mettle=SAT jar=UNSAT")),
                )
            } else {
                ("agree_unsat".to_owned(), None)
            }
        }
    }
}

/// Classifies the count disposition of a mettle-SAT command: documented
/// divergence families are typed skips; everything else is enumerated to an exact
/// mettle count (or `skip_mettle_cap` past the cap / budget).
fn classify_count(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    world: &ResolvedWorld,
    opts: &SolveOptions,
    count_cap: u64,
) -> CountOutcome {
    if goal.has_higher_order_skolem {
        return CountOutcome::Skip("skip_ho_skolem");
    }
    if ordered_abstract_partition(world, scoped) {
        return CountOutcome::Skip("skip_ordered_abstract");
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
fn run_jar_stage(
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

impl SolveGaugeReport {
    /// The process exit code this report implies: `1` for a fail-fast partial
    /// run, else `0` (a gauge, not a test — disagreements alone do not fail).
    #[must_use]
    pub fn exit_status(&self) -> u8 {
        u8::from(self.partial)
    }

    /// Renders the deterministic human-readable report.
    #[must_use]
    pub fn render_text(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "=== mt-037 solve gauge ===");
        if self.partial {
            let _ = writeln!(
                out,
                "PARTIAL (fail-fast after {})",
                self.fail_fast_trigger.as_deref().unwrap_or("<trigger>")
            );
        }
        let _ = writeln!(out, "commands          : {}", self.commands);
        let _ = writeln!(out, "stage-1 symmetry  : {}", self.symmetry);
        let _ = writeln!(
            out,
            "baselines         : {} ({} command entries)",
            if self.baseline_files.is_empty() {
                "<none>".to_owned()
            } else {
                self.baseline_files.join(", ")
            },
            self.baseline_entries
        );

        let _ = writeln!(out, "\nverdict buckets (sum = {}):", self.commands);
        for (bucket, n) in &self.verdict_buckets {
            let _ = writeln!(out, "  {bucket:<32} {n}");
        }

        render_list(&mut out, "DISAGREE", &self.disagreements);
        render_list(&mut out, "self-check failures", &self.self_check_failures);
        render_list(&mut out, "panics", &self.panics);

        if self.count_enabled {
            let _ = writeln!(
                out,
                "\n=== counting net (--count, symmetry {}) ===",
                self.count_symmetry
            );
            let _ = writeln!(
                out,
                "count baselines   : {}",
                if self.count_baseline_files.is_empty() {
                    "<none / live jar>".to_owned()
                } else {
                    self.count_baseline_files.join(", ")
                }
            );
            if self.count_buckets.is_empty() {
                let _ = writeln!(out, "  (no SAT commands reached the counting net)");
            }
            for (bucket, n) in &self.count_buckets {
                let _ = writeln!(out, "  {bucket:<32} {n}");
            }
            render_list(&mut out, "COUNT_MISMATCH", &self.count_mismatches);
        }

        self.render_delta(&mut out);
        out
    }

    /// The `--delta` section: what moved relative to the sweep baseline.
    fn render_delta(&self, out: &mut String) {
        let Some(delta) = &self.delta else {
            return;
        };
        let _ = writeln!(
            out,
            "\n=== delta vs {} ===",
            if delta.baseline_files.is_empty() {
                "<none>".to_owned()
            } else {
                delta.baseline_files.join(", ")
            }
        );
        let _ = writeln!(out, "unchanged         : {}", delta.unchanged);
        if !delta.count_compared {
            let _ = writeln!(
                out,
                "count buckets     : not compared (one side ran without --count)"
            );
        }
        render_list(out, "changed", &delta.changed);
        render_list(out, "new commands", &delta.new_commands);
        render_list(out, "gone commands", &delta.gone_commands);
        if delta.is_clean() {
            let _ = writeln!(out, "\nNO CHANGE vs the recorded baseline.");
        }
    }

    /// Renders the report as stable pretty JSON.
    ///
    /// # Errors
    /// Only if serialization itself fails (does not happen short of allocation
    /// failure).
    pub fn to_json(&self) -> Result<String, ConformError> {
        Ok(serde_json::to_string_pretty(self)?)
    }
}

/// Prints a titled list with its count (the count line always appears, so a clean
/// run shows an explicit `0` rather than silence).
fn render_list(out: &mut String, title: &str, items: &[String]) {
    let _ = writeln!(out, "\n{title}: {}", items.len());
    for item in items {
        let _ = writeln!(out, "  {item}");
    }
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
        }
    }
}
