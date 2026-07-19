//! The mt-037 differential **solve gauge** + **SB-0 counting net**.
//!
//! Two stages over the corpus (`corpus/alloytools-models/models`,
//! `corpus/portus-63`, or any given roots):
//!
//! **Stage 1 (always).** Run mettle's own solve pipeline — `compute_universe →
//! compute_bounds → lower_command → solve_goal` — over every root-module command
//! of every `.als` file, inline under the smoke test's resource discipline (the
//! mt-039 lesson: no worker threads, deterministic budgets, `catch_unwind` per
//! command). Compare mettle's SAT/UNSAT against the cached jar verdict
//! ([`baseline`]) and bucket each command into exactly one verdict-stage bucket
//! (asserted: the buckets sum to the command count).
//!
//! **Stage 2 (`--count`, needs the jar).** For every command mettle called SAT
//! and the baseline agrees, enumerate mettle's SB-0 model count and — for goals
//! outside the documented count-divergence families ([`detect`]) — compare it to
//! the jar's own SB-0 count at `symmetry = 0` (ADR-0002). Everything else is a
//! **typed skip**, never a fabricated mismatch.
//!
//! This module never prints and never exits (STYLE E3); the bin renders
//! [`SolveGaugeReport`] and sets the process exit code.

pub mod baseline;
pub mod detect;

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
use detect::{has_skolemizable_fo_existential, lower_defer_class, ordered_abstract_partition};

/// Default corpus roots (mirrors [`crate::DEFAULT_CORPUS_ROOTS`] but relative to
/// the workspace root the gauge is handed).
pub const DEFAULT_CORPUS_SUBDIRS: [&str; 2] =
    ["corpus/alloytools-models/models", "corpus/portus-63"];

/// Everything the gauge needs for one run. Budgets default higher than the
/// smoke test's (this is the gauge, not a fast CI net).
#[derive(Debug, Clone)]
pub struct GaugeConfig {
    /// Corpus roots to scan — each a directory (walked recursively for `.als`)
    /// or a single `.als` file. Absent roots are skipped cleanly.
    pub roots: Vec<PathBuf>,
    /// Workspace root, for computing the relpath keys the baselines are keyed on.
    pub workspace_root: PathBuf,
    /// Directory holding `*-verdict.json` baselines.
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
    /// Whether to run stage 2 (the SB-0 counting net; needs the jar).
    pub count: bool,
    /// Enumerate at most this many mettle instances before skipping a command as
    /// `skip_mettle_cap` (and the jar side is capped at `count_cap + 1`).
    pub count_cap: u64,
    /// Cumulative SAT-conflict budget across one command's whole SB-0
    /// enumeration (all instance solves summed), independent of `count_cap`: a
    /// model can pass the primary-var cap and still grind for hours because each
    /// individual instance solve is expensive. Exhausting it ends enumeration in
    /// a typed `skip_enum_budget`, never a silently truncated count.
    pub enum_budget: u64,
    /// Reference jar (stage 2 only).
    pub jar_path: PathBuf,
    /// `OracleShim.java` source (stage 2 only).
    pub shim_source: PathBuf,
    /// Per-file JVM timeout for the stage-2 jar enumeration.
    pub jar_timeout: Duration,
}

/// The gauge's deterministic report. `BTreeMap`s serialize/iterate in key order
/// and every `Vec` is filled in file-sorted, index-ascending order, so the
/// whole report is byte-identical run to run (STYLE D1).
#[derive(Debug, Clone, Serialize)]
pub struct SolveGaugeReport {
    /// Total root-module commands processed.
    pub commands: usize,
    /// Names of the `*-verdict.json` baselines merged.
    pub baseline_files: Vec<String>,
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
    /// Whether stage 2 ran.
    pub count_enabled: bool,
    /// Counting-net buckets (`count_match` / `COUNT_MISMATCH` / `skip_*`).
    pub count_buckets: BTreeMap<String, usize>,
    /// Every count mismatch, `relpath[idx]: mettle=m jar=j`.
    pub count_mismatches: Vec<String>,
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

/// The stage-2 disposition of one SAT command after mettle-side classification.
enum CountOutcome {
    /// A typed skip: the given `count_buckets` key.
    Skip(&'static str),
    /// Eligible: mettle's exact SB-0 count, awaiting the jar comparison.
    JarTodo(u64),
}

/// The fully-computed result of classifying one command — no shared state is
/// mutated inside the `catch_unwind`d closure, so the caller can attribute
/// exactly one verdict bucket per command even when a later command panics.
struct CmdResult {
    /// The single verdict-stage bucket key.
    verdict_bucket: String,
    /// A disagreement line, if this was a `DISAGREE`.
    disagreement: Option<String>,
    /// A self-check failure line, if the SAT instance failed self-check.
    self_check_fail: Option<String>,
    /// The stage-2 disposition (only when `--count` and stage-2-eligible).
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

/// Runs the full gauge and returns the deterministic report.
///
/// `progress` receives transient status lines (stage transitions; one line per
/// jar file in stage 2, whose fresh-JVM enumeration runs are the slow part) so
/// a long run is visibly alive. The report itself never goes through it — the
/// library stays render-free (STYLE E3); the bin points `progress` at stderr
/// and tests pass a no-op.
///
/// # Errors
/// Only a genuine **tool** failure: in `--count` mode, the reference jar / shim
/// could not be compiled (`ConformError`). Stage 1 never errors — a broken
/// command is bucketed, not propagated.
///
/// # Panics
/// On an internal accounting bug only (STYLE I1): if the verdict buckets fail to
/// partition the processed commands.
pub fn run_gauge(
    cfg: &GaugeConfig,
    progress: &mut dyn FnMut(&str),
) -> Result<SolveGaugeReport, ConformError> {
    let baseline = load_baselines(&cfg.baselines_dir);

    let mut files = Vec::new();
    for root in &cfg.roots {
        collect_als(root, &mut files);
    }
    files.sort();
    files.dedup();

    let mut report = SolveGaugeReport {
        commands: 0,
        baseline_files: baseline.loaded.clone(),
        baseline_entries: baseline.command_count(),
        verdict_buckets: BTreeMap::new(),
        disagreements: Vec::new(),
        self_check_failures: Vec::new(),
        panics: Vec::new(),
        count_enabled: cfg.count,
        count_buckets: BTreeMap::new(),
        count_mismatches: Vec::new(),
    };
    // (canon file path) → [(relpath, idx, mettle_count)] eligible for the jar.
    let mut jar_todo: BTreeMap<PathBuf, Vec<(String, usize, u64)>> = BTreeMap::new();

    // Silence per-panic backtraces during the sweep; every panic is caught and
    // bucketed per command (the solve_corpus / mt-039 discipline). Restored
    // immediately after the loop.
    let prev_hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));

    progress(&format!("stage 1: mettle sweep over {} files", files.len()));
    let loader = FilesystemLoader::new();
    for path in &files {
        run_file(path, cfg, &loader, &baseline, &mut report, &mut jar_todo);
    }

    panic::set_hook(prev_hook);

    // Negative space (STYLE I1): every command lands in exactly one verdict
    // bucket, so the buckets sum to the command count.
    let bucket_sum: usize = report.verdict_buckets.values().sum();
    assert_eq!(
        bucket_sum, report.commands,
        "verdict buckets must partition the commands"
    );

    if cfg.count {
        run_jar_stage(cfg, &jar_todo, &mut report, progress)?;
    }

    Ok(report)
}

/// Loads and sweeps one `.als` file, updating `report` and `jar_todo`.
fn run_file(
    path: &Path,
    cfg: &GaugeConfig,
    loader: &FilesystemLoader,
    baseline: &baseline::Baseline,
    report: &mut SolveGaugeReport,
    jar_todo: &mut BTreeMap<PathBuf, Vec<(String, usize, u64)>>,
) {
    let Ok(canon) = std::fs::canonicalize(path) else {
        return;
    };
    let root_str = canon.to_string_lossy().replace('\\', "/");
    let Ok(graph) = ModuleGraph::load(&root_str, loader) else {
        return;
    };
    let Ok(resolved) = als_types::resolve(&graph) else {
        return;
    };
    let world = resolved.world;
    let root_file = graph.modules[graph.root].file;
    let rel = path
        .strip_prefix(&cfg.workspace_root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/");

    for (idx, _) in world
        .commands
        .iter()
        .enumerate()
        .filter(|(_, c)| c.span.file == root_file)
    {
        report.commands += 1;
        let Ok(scoped) = compute_universe(&world, &graph, &world.commands[idx]) else {
            *report
                .verdict_buckets
                .entry("mettle_defer:scope".to_owned())
                .or_default() += 1;
            continue;
        };

        let outcome = panic::catch_unwind(AssertUnwindSafe(|| {
            classify_command(&world, &graph, &scoped, baseline, cfg, &rel, idx)
        }));

        match outcome {
            Ok(result) => apply_result(result, &rel, idx, &canon, report, jar_todo),
            Err(payload) => {
                let msg = payload
                    .downcast_ref::<&str>()
                    .map(|s| (*s).to_owned())
                    .or_else(|| payload.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "non-string panic payload".to_owned());
                *report
                    .verdict_buckets
                    .entry("panic".to_owned())
                    .or_default() += 1;
                report.panics.push(format!("{rel}[{idx}]: {msg}"));
            }
        }
    }
}

/// Folds a computed [`CmdResult`] into the report (all shared-state mutation
/// lives here, outside the `catch_unwind`).
fn apply_result(
    result: CmdResult,
    rel: &str,
    idx: usize,
    canon: &Path,
    report: &mut SolveGaugeReport,
    jar_todo: &mut BTreeMap<PathBuf, Vec<(String, usize, u64)>>,
) {
    *report
        .verdict_buckets
        .entry(result.verdict_bucket)
        .or_default() += 1;
    if let Some(d) = result.disagreement {
        report.disagreements.push(d);
    }
    if let Some(sc) = result.self_check_fail {
        report
            .self_check_failures
            .push(format!("{rel}[{idx}]: {sc}"));
    }
    match result.count {
        Some(CountOutcome::Skip(key)) => {
            *report.count_buckets.entry(key.to_owned()).or_default() += 1;
        }
        Some(CountOutcome::JarTodo(mettle_count)) => {
            jar_todo.entry(canon.to_path_buf()).or_default().push((
                rel.to_owned(),
                idx,
                mettle_count,
            ));
        }
        None => {}
    }
}

/// Builds, solves, and (if `--count`) classifies the SB-0 count for one command.
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

    let opts = SolveOptions {
        allow_overflow: cfg.allow_overflow,
        conflict_budget: Some(cfg.conflict_budget),
        encode_budget: Some(cfg.encode_budget),
        ..SolveOptions::default()
    };
    let (sat, self_check_fail) = match solve_goal(&ir, scoped, &goal, &bounds, &opts) {
        Ok(SolveVerdict::Sat(inst)) => {
            let sc = self_check(&ir, scoped, &goal, &inst, &opts)
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

    // Stage 2 runs only for a mettle-SAT command the baseline agrees on (SAT) or
    // does not cover — a no_baseline SAT command (e.g. `oracle/test1.als`) still
    // gets its jar count live in stage 2.
    let count = if cfg.count && sat && matches!(baseline_v, None | Some(JarVerdict::Sat)) {
        // Thread the enumeration's cumulative conflict budget onto the options
        // used for stage 2 only (mirrors how `count_cap` reaches `classify_count`
        // as a value derived from `cfg`): `opts` itself stays the stage-1
        // (verdict/self-check) options, unaffected by this per-enumeration knob.
        let enum_opts = SolveOptions {
            enum_conflict_budget: Some(cfg.enum_budget),
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

/// Classifies the SB-0 count disposition of a mettle-SAT command: the documented
/// divergence families are typed skips; everything else is enumerated to an
/// exact mettle count (or `skip_mettle_cap` past the cap / budget).
fn classify_count(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    world: &ResolvedWorld,
    opts: &SolveOptions,
    count_cap: u64,
) -> CountOutcome {
    // Higher-order-skolemized goals: LIMITATIONS says these now count exactly
    // (mt-038), but the claim is unverified on a large model like `ringlead`, so
    // the gauge skips them typed rather than risk a fabricated mismatch.
    if !goal.skolem_bounds.is_empty() {
        return CountOutcome::Skip("skip_ho_skolem");
    }
    // A first-order top-level existential the jar skolemizes as a depth-0 skolem
    // constant (translation-ref §10.4): the jar counts its assignments too.
    if has_skolemizable_fo_existential(ir, goal.goal) {
        return CountOutcome::Skip("skip_fo_skolem");
    }
    // The T14a/T14d ordered-partition family (translation-ref §10.1).
    if ordered_abstract_partition(world, scoped) {
        return CountOutcome::Skip("skip_ordered_abstract");
    }

    // Enumerate mettle's exact SB-0 count, stopping one past the cap. `opts`
    // carries the cumulative conflict budget bounding the whole enumeration's
    // effort (independent of the instance-count cap above): some corpus models
    // pass the primary-var cap yet grind for hours because each individual
    // instance solve is expensive.
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
    // Check exhaustion first: an enumeration that ran out of budget mid-count
    // is a lower bound, never a trustworthy exact or capped count.
    if it.exhausted() {
        CountOutcome::Skip("skip_enum_budget")
    } else if n > count_cap {
        CountOutcome::Skip("skip_mettle_cap")
    } else {
        CountOutcome::JarTodo(n)
    }
}

/// Runs the jar over every file with an eligible command and finishes the
/// counting net. One JVM per file, `symmetry = 0` via `A4Options` (the CLI `-y`
/// flag is a no-op in 6.2.0), `noOverflow` per the LEDGER-001 switch, capped at
/// `count_cap + 1` instances.
fn run_jar_stage(
    cfg: &GaugeConfig,
    jar_todo: &BTreeMap<PathBuf, Vec<(String, usize, u64)>>,
    report: &mut SolveGaugeReport,
    progress: &mut dyn FnMut(&str),
) -> Result<(), ConformError> {
    // Symmetry is set to 0 explicitly here, so the jar's own `expect 1 →
    // symmetry = 0` internal override (which would matter at default symmetry)
    // is moot — the SB-0 count is what we compare (ADR-0002).
    let oracle_cfg = OracleConfig::new(&cfg.jar_path, &cfg.shim_source)
        .with_symmetry(0)
        .with_no_overflow(!cfg.allow_overflow)
        .with_solver("sat4j")
        .with_timeout(cfg.jar_timeout);
    let shim_classes = ensure_shim_compiled(&oracle_cfg)?;

    let cap = u32::try_from(cfg.count_cap + 1).unwrap_or(u32::MAX);

    let total = jar_todo.len();
    for (i, (canon, todos)) in jar_todo.iter().enumerate() {
        progress(&format!(
            "stage 2: jar enumeration {}/{total}: {}",
            i + 1,
            canon.display()
        ));
        let result =
            run_oracle_on_file(&oracle_cfg, &shim_classes, canon, EnumerationCap::UpTo(cap));
        for (rel, idx, mettle_count) in todos {
            let key = jar_count_bucket(&result.outcome, *idx, *mettle_count, rel, report);
            *report.count_buckets.entry(key.to_owned()).or_default() += 1;
        }
    }
    Ok(())
}

/// The count bucket for one command given the jar's file outcome, recording a
/// `COUNT_MISMATCH` line when the counts differ.
fn jar_count_bucket(
    outcome: &FileOutcome,
    idx: usize,
    mettle_count: u64,
    rel: &str,
    report: &mut SolveGaugeReport,
) -> &'static str {
    match outcome {
        FileOutcome::Timeout => "skip_jar_timeout",
        FileOutcome::Error { .. } => "skip_jar_error",
        FileOutcome::Commands(cmds) => {
            match cmds.iter().find(|c| c.index == idx).map(|c| &c.outcome) {
                Some(Outcome::Sat {
                    instance_count: Some(j),
                }) => {
                    if u64::from(*j) == mettle_count {
                        "count_match"
                    } else {
                        report
                            .count_mismatches
                            .push(format!("{rel}[{idx}]: mettle={mettle_count} jar={j}"));
                        "COUNT_MISMATCH"
                    }
                }
                // The jar answered UNSAT / errored / gave no count for a command
                // mettle called SAT: can't compare counts (never a fabricated
                // mismatch).
                _ => "skip_jar_error",
            }
        }
    }
}

impl SolveGaugeReport {
    /// Renders the deterministic human-readable report.
    #[must_use]
    pub fn render_text(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "=== mt-037 solve gauge ===");
        let _ = writeln!(out, "commands          : {}", self.commands);
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
            let _ = writeln!(out, "\n=== SB-0 counting net (--count) ===");
            if self.count_buckets.is_empty() {
                let _ = writeln!(out, "  (no SAT commands reached the counting net)");
            }
            for (bucket, n) in &self.count_buckets {
                let _ = writeln!(out, "  {bucket:<32} {n}");
            }
            render_list(&mut out, "COUNT_MISMATCH", &self.count_mismatches);
        }

        out
    }

    /// Renders the report as stable pretty JSON.
    ///
    /// # Errors
    /// Only if serialization itself fails (does not happen for this type short
    /// of allocation failure).
    pub fn to_json(&self) -> Result<String, ConformError> {
        Ok(serde_json::to_string_pretty(self)?)
    }
}

/// Prints a titled list with its count (the count line always appears, so a
/// clean run shows an explicit `0` rather than silence).
fn render_list(out: &mut String, title: &str, items: &[String]) {
    let _ = writeln!(out, "\n{title}: {}", items.len());
    for item in items {
        let _ = writeln!(out, "  {item}");
    }
}
