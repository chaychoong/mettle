//! Phase A/phase B execution: resolving each `.als` file once (phase A) and
//! then building, solving and (if `--count`) counting each of its commands on
//! a worker thread (phase B), touching no shared report state.

use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};

use als_core::bounds::Bounds;
use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, self_check, solve_goal,
    solve_temporal_command, BoundsResult, ScopedUniverse, SolveOptions, SolveVerdict,
    TemporalSolveConfig, TemporalVerdict, TranslateError,
};
use als_types::{is_temporal_model, FilesystemLoader, ModuleGraph, ResolvedWorld};

use super::baseline;
use super::baseline::JarVerdict;
use super::count::{
    classify_count, classify_temporal_count, presettled_count_bucket, resolve_count, CountDisp,
    CountOutcome,
};
use super::count_baseline::CountBaseline;
use super::detect::lower_defer_class;
use super::parallel::parallel_fold;
use super::sweep_baseline::command_key;
use super::telemetry::{self, TelemetryEvent, TelemetrySink};
use super::{workspace_relpath, GaugeConfig};

/// The number of primary variables the bounds imply (`Σ upper − lower`).
fn primary_var_count(bounds: &Bounds) -> usize {
    bounds
        .iter()
        .map(|(_, b)| b.upper().len() - b.lower().len())
        .sum()
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

/// One command, resolved into everything the coordinator needs to fold it into
/// the report deterministically — computed entirely on a worker thread.
pub(super) struct CmdRecord {
    pub(super) rel: String,
    pub(super) idx: usize,
    pub(super) canon: PathBuf,
    pub(super) verdict_bucket: String,
    pub(super) disagreement: Option<String>,
    /// Pre-formatted `relpath[idx]: <detail>` self-check line.
    pub(super) self_check_fail: Option<String>,
    /// Pre-formatted `relpath[idx]: <msg>` panic line.
    pub(super) panic_line: Option<String>,
    pub(super) count: CountDisp,
}

/// One file's parse + module-load + resolve result, computed once in phase A and
/// then shared **read-only** across every command worker in phase B.
///
/// This is what makes command-level parallelism affordable: the per-file work
/// commands used to share by running serially in one worker is still paid
/// exactly once, and the commands fan out over an `Arc` of it.
pub(super) struct ResolvedFile {
    pub(super) rel: String,
    canon: PathBuf,
    graph: ModuleGraph,
    world: ResolvedWorld,
    /// The root module's command indices, ascending — the only ones the gauge
    /// sweeps (an imported module's commands are not this file's).
    command_indices: Vec<usize>,
}

/// One unit of phase-B work: a command, plus the shared resolve of its file.
pub(super) struct CmdItem {
    pub(super) file: std::sync::Arc<ResolvedFile>,
    pub(super) idx: usize,
    /// This item's position in the flat, file-sorted/index-ascending queue
    /// [`command_items`] builds — the same position `report.per_command`
    /// folds into and, under `--progress-jsonl` (mt-094), the row index a
    /// `row_start` telemetry event names. Dispatch order (LPT) can differ
    /// from this; `pos` is what stays fixed regardless.
    pub(super) pos: usize,
}

/// One command's fully-computed gauge result (no shared state touched).
pub(super) struct CmdGaugeResult {
    pub(super) record: CmdRecord,
    /// Wall seconds — the stderr slowest-10 table and the next run's LPT
    /// schedule. Nondeterministic; never enters the report (STYLE D1/D4).
    pub(super) secs: f64,
}

/// **Phase A** — parse, module-load and resolve every file, in parallel, once.
///
/// A file that fails to canonicalize / load / resolve yields `None` and simply
/// contributes no commands, exactly as the pre-mt-057 per-file sweep did.
/// Emits a resolve-cost summary through `progress` so the phase's share of the
/// run stays observable rather than assumed.
pub(super) fn resolve_phase(
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
pub(super) fn command_items(resolved: &[Option<std::sync::Arc<ResolvedFile>>]) -> Vec<CmdItem> {
    let mut items = Vec::new();
    for file in resolved.iter().flatten() {
        for &idx in &file.command_indices {
            items.push(CmdItem {
                pos: items.len(),
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
pub(super) fn compute_command(
    item: &CmdItem,
    cfg: &GaugeConfig,
    baseline: &baseline::Baseline,
    count_baseline: Option<&CountBaseline>,
    telemetry: Option<&TelemetrySink>,
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
    // mt-094: this is the same "a row truly began" moment the heartbeat
    // above marks — `send` is the pre-existing stderr/status channel,
    // `telemetry` (when attached) is the structured mirror of it.
    if let Some(sink) = telemetry {
        sink.emit(&TelemetryEvent::RowStart(telemetry::RowStartEvent {
            ts_ms: telemetry::now_ms(),
            i: item.pos,
            key: command_key(rel, idx),
        }));
    }
    let started = std::time::Instant::now();
    let outcome = panic::catch_unwind(AssertUnwindSafe(|| {
        classify_command(
            &file.world,
            &file.graph,
            &scoped,
            baseline,
            count_baseline,
            cfg,
            rel,
            idx,
        )
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

/// Builds, solves, and (if `--count`) classifies the count for one command.
/// Returns a fully-computed [`CmdResult`]; mutates nothing shared.
#[allow(
    clippy::too_many_arguments,
    reason = "one command's whole input: the resolve, both baselines, its key"
)]
fn classify_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    baseline: &baseline::Baseline,
    count_baseline: Option<&CountBaseline>,
    cfg: &GaugeConfig,
    rel: &str,
    idx: usize,
) -> CmdResult {
    let mut ir = Ir::default();
    let bounds = compute_bounds(world, scoped, &mut ir);

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
        backend: cfg.backend,
        ..SolveOptions::default()
    };

    // Rung-6 dispatch (mt-067): the pinned discriminator decides which pipeline
    // owns the command, exactly as `CompUtil.isTemporalModel` does jar-side. A
    // temporal command never reaches `lower_command` (which would defer it) —
    // it runs the `steps`-range sweep instead.
    if is_temporal_model(world, graph, &world.commands[idx]) {
        return classify_temporal_command(
            world,
            graph,
            scoped,
            &bounds,
            &mut ir,
            baseline,
            count_baseline,
            cfg,
            rel,
            idx,
            &opts,
            stage2_sym,
        );
    }

    let goal = match lower_command(world, graph, scoped, &bounds, &mut ir, idx) {
        Ok(g) => g,
        Err(e) => return CmdResult::defer(format!("mettle_defer:lower:{}", lower_defer_class(&e))),
    };
    if primary_var_count(&bounds.bounds) > cfg.primary_var_cap {
        return CmdResult::defer("mettle_defer:primary_var_cap".to_owned());
    }

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
            presettled_count_bucket(cfg, count_baseline, rel, idx),
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

/// The Rung-6 arm of [`classify_command`] (mt-067): sweep the command's `steps`
/// range and bucket the outcome.
///
/// Every bucket a temporal command can land in is typed and visible:
///
/// | outcome | bucket |
/// |---|---|
/// | SAT / UNSAT-within-bound | the ordinary verdict comparison — `no_baseline` until mt-069 banks the four temporal files |
/// | conflict budget out at some length | `mettle_defer:over_budget` |
/// | a length outgrew the primary-variable cap | `mettle_defer:primary_var_cap` |
/// | encode budget out | `mettle_defer:capacity` |
/// | `for 1.. steps` | `mettle_defer:temporal:unbounded_steps` |
/// | anything the temporal lowering still defers | `mettle_defer:lower:<class>` |
///
/// `check … for 1 steps` is **not** a bucket as of mt-077: a one-state lasso is
/// an ordinary trace length and the sweep answers it like any other.
///
/// Stage 2 **does** enumerate a temporal command as of mt-076: the typed skip
/// `skip_temporal_trace` (ADR-0015 consequence 4's deliberate deferral) is
/// retired, and [`classify_temporal_count`] runs `als_core`'s
/// [`TraceEnumerator`](als_core::TraceEnumerator) — the jar's own
/// `next()`-until-UNSAT loop, with the configuration-hold and across-length
/// de-duplication mt-076's probes pinned. A command whose enumeration outgrows
/// the effort budget lands in the existing `skip_enum_budget`, not a new
/// bucket.
#[allow(
    clippy::too_many_arguments,
    reason = "the temporal arm of `classify_command`, threading the same context"
)]
fn classify_temporal_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    bounds: &BoundsResult,
    ir: &mut Ir,
    baseline: &baseline::Baseline,
    count_baseline: Option<&CountBaseline>,
    cfg: &GaugeConfig,
    rel: &str,
    idx: usize,
    opts: &SolveOptions,
    stage2_sym: u32,
) -> CmdResult {
    let temporal_cfg = TemporalSolveConfig {
        opts: *opts,
        primary_var_cap: Some(cfg.primary_var_cap),
        // The gauge is a release build, so the driver's `debug_assert` net is
        // compiled out; ask for the check explicitly, as the static arm does.
        self_check: true,
    };
    let (sat, self_check_fail) =
        match solve_temporal_command(world, graph, scoped, bounds, ir, idx, &temporal_cfg) {
            Ok(TemporalVerdict::Sat(trace)) => (true, trace.self_check.map(|f| f.to_string())),
            Ok(TemporalVerdict::Unsat) => (false, None),
            Ok(TemporalVerdict::Unknown { .. }) => {
                return CmdResult::defer("mettle_defer:over_budget".to_owned())
            }
            Ok(TemporalVerdict::PrimaryVarCap { .. }) => {
                return CmdResult::defer("mettle_defer:primary_var_cap".to_owned())
            }
            Err(TranslateError::UnboundedSteps { .. }) => {
                return CmdResult::defer("mettle_defer:temporal:unbounded_steps".to_owned())
            }
            Err(TranslateError::CapacityExceeded { .. }) => {
                return CmdResult::defer("mettle_defer:capacity".to_owned())
            }
            Err(e) => {
                return CmdResult::defer(format!("mettle_defer:lower:{}", lower_defer_class(&e)))
            }
        };

    let baseline_v = baseline.lookup(rel, idx);
    let (verdict_bucket, disagreement) = compare_verdict(baseline_v, sat, rel, idx);
    // Same gate as the static arm: only a mettle-SAT command the jar also calls
    // SAT (or has no verdict for) can be compared on a count.
    let count = if cfg.count && sat && matches!(baseline_v, None | Some(JarVerdict::Sat)) {
        let enum_cfg = TemporalSolveConfig {
            opts: SolveOptions {
                enum_effort_budget: Some(cfg.enum_budget),
                symmetry: stage2_sym,
                ..*opts
            },
            ..temporal_cfg
        };
        Some(classify_temporal_count(
            world,
            graph,
            scoped,
            bounds,
            ir,
            idx,
            &enum_cfg,
            cfg.count_cap,
            presettled_count_bucket(cfg, count_baseline, rel, idx),
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
