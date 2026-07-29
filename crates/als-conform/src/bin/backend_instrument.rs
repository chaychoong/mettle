//! `backend-instrument` — the ADR-0019 stage-1 instrument (mt-089).
//!
//! Runs a **named worklist of commands** through mettle's ordinary pipeline
//! (resolve → universe → bounds → lower → translate) and decides each one with
//! a chosen SAT backend, so "how much of the `over_budget` tail is genuinely
//! hard vs. our own solver being weak" becomes a measurement instead of a
//! guess. Not shipped product: it is compiled only under the
//! `cadical-instrument` feature and is `dist = false` like every other bin in
//! this crate.
//!
//! ```text
//! backend-instrument --rows worklist.txt --backend cadical \
//!     --conflicts 100000 --encode 64000000 --wall 600 --jobs 8 --out rows.json
//! ```
//!
//! A row is a gauge key: `<workspace-relative path>[<command index>]`. Each row
//! is classified into exactly one of the buckets the solve gauge uses, so the
//! table lines up with the mt-088 census it is measured against.
//!
//! Determinism: the report is sorted by row key and carries no wall-clock
//! **in the verdicts** — the `*_ms` fields are measurements, printed and
//! recorded as such (STYLE D1/D4).

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use als_conform::solve_gauge::baseline::{load_baselines, Baseline, JarVerdict};
use als_core::instrument::{
    solve_goal_with_backend, InstrumentBackend, InstrumentOutcome, InstrumentVerdict,
};
use als_core::ir::Ir;
use als_core::{compute_bounds, compute_universe, lower_command, SolveOptions, TranslateError};
use als_types::{is_temporal_model, FilesystemLoader, ModuleGraph};

/// Everything one run needs, parsed from `argv`.
struct Config {
    rows: Vec<(String, usize)>,
    backend: InstrumentBackend,
    conflicts: u64,
    encode: u64,
    wall_secs: Option<f32>,
    /// Symmetry-breaking predicate cap. `None` = the jar default (20, forced
    /// to 0 by `expect 1`); an explicit value overrides both — the knob that
    /// separates "the SBP is unsound here" from "the core encoding is wrong"
    /// when a verdict disagreement shows up.
    symmetry: Option<u32>,
    /// LEDGER-001 overflow regime: `false` (default, and the jar's
    /// `noOverflow=true`) excludes overflowing instances, `true` wraps. A knob
    /// because an int-encoding over-constraint shows up as exactly this
    /// difference.
    allow_overflow: bool,
    jobs: usize,
    root: PathBuf,
    baselines: PathBuf,
    out: Option<PathBuf>,
}

/// One measured row, as it lands in the JSON artifact.
struct Row {
    key: String,
    bucket: String,
    verdict: Option<InstrumentVerdict>,
    jar: Option<JarVerdict>,
    agreement: &'static str,
    outcome: Option<InstrumentOutcome>,
    secs: f64,
}

fn main() {
    let cfg = match parse_args() {
        Ok(cfg) => cfg,
        Err(msg) => {
            eprintln!("backend-instrument: {msg}");
            std::process::exit(2);
        }
    };
    let baseline = load_baselines(&cfg.baselines);
    let rows = run(&cfg, &baseline);
    print_table(&cfg, &rows);
    if let Some(path) = &cfg.out {
        if let Err(e) = write_json(path, &cfg, &rows) {
            eprintln!("backend-instrument: writing {}: {e}", path.display());
            std::process::exit(1);
        }
    }
}

/// Parses `argv`; every flag is required to be well-formed (a typo in a budget
/// would silently change what the run measures).
#[allow(clippy::too_many_lines, reason = "flat flag parsing, one arm per flag")]
fn parse_args() -> Result<Config, String> {
    let mut rows_path: Option<PathBuf> = None;
    let mut backend = InstrumentBackend::Cadical;
    let mut conflicts: u64 = 100_000;
    let mut encode: u64 = 64_000_000;
    let mut wall_secs: Option<f32> = Some(600.0);
    let mut symmetry: Option<u32> = None;
    let mut allow_overflow = false;
    let mut jobs: usize = 1;
    let mut root = PathBuf::from(".");
    let mut baselines: Option<PathBuf> = None;
    let mut out: Option<PathBuf> = None;

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        let mut value = || args.next().ok_or_else(|| format!("{arg} needs a value"));
        match arg.as_str() {
            "--rows" => rows_path = Some(PathBuf::from(value()?)),
            "--backend" => {
                backend = match value()?.as_str() {
                    "cdcl" => InstrumentBackend::Cdcl,
                    "cadical" => InstrumentBackend::Cadical,
                    other => return Err(format!("unknown backend {other:?}")),
                }
            }
            "--conflicts" => {
                conflicts = value()?.parse().map_err(|_| "--conflicts: not a number")?;
            }
            "--encode" => encode = value()?.parse().map_err(|_| "--encode: not a number")?,
            "--wall" => {
                let secs: f32 = value()?.parse().map_err(|_| "--wall: not a number")?;
                wall_secs = if secs > 0.0 { Some(secs) } else { None };
            }
            "--symmetry" => {
                symmetry = Some(value()?.parse().map_err(|_| "--symmetry: not a number")?);
            }
            "--allow-overflow" => allow_overflow = true,
            "--jobs" => jobs = value()?.parse().map_err(|_| "--jobs: not a number")?,
            "--root" => root = PathBuf::from(value()?),
            "--baselines" => baselines = Some(PathBuf::from(value()?)),
            "--out" => out = Some(PathBuf::from(value()?)),
            other => return Err(format!("unknown flag {other:?}")),
        }
    }
    let rows_path = rows_path.ok_or("--rows is required")?;
    let text = std::fs::read_to_string(&rows_path)
        .map_err(|e| format!("reading {}: {e}", rows_path.display()))?;
    let mut rows = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        rows.push(parse_key(line)?);
    }
    let baselines = baselines.unwrap_or_else(|| root.join("baselines"));
    Ok(Config {
        rows,
        backend,
        conflicts,
        encode,
        wall_secs,
        symmetry,
        allow_overflow,
        jobs: jobs.max(1),
        root,
        baselines,
        out,
    })
}

/// Splits a gauge key `path/to/model.als[7]` into its parts.
fn parse_key(key: &str) -> Result<(String, usize), String> {
    let open = key
        .rfind('[')
        .ok_or_else(|| format!("row {key:?} is not `path[idx]`"))?;
    let close = key
        .strip_suffix(']')
        .ok_or_else(|| format!("row {key:?} is not `path[idx]`"))?;
    let idx: usize = close[open + 1..]
        .parse()
        .map_err(|_| format!("row {key:?} has a non-numeric index"))?;
    Ok((key[..open].to_owned(), idx))
}

/// Runs every row, `jobs` at a time, and returns them in worklist order.
fn run(cfg: &Config, baseline: &Baseline) -> Vec<Row> {
    let slots: Vec<Mutex<Option<Row>>> = cfg.rows.iter().map(|_| Mutex::new(None)).collect();
    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let total = cfg.rows.len();
    std::thread::scope(|scope| {
        for _ in 0..cfg.jobs.min(total.max(1)) {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                if i >= total {
                    return;
                }
                let (path, idx) = &cfg.rows[i];
                eprintln!("  start {path}[{idx}]");
                let _ = std::io::stderr().flush();
                let started = std::time::Instant::now();
                let row = measure_row(cfg, baseline, path, *idx, started);
                let finished = done.fetch_add(1, Ordering::SeqCst) + 1;
                eprintln!(
                    "  [{finished}/{total}] {} → {} ({:.1}s)",
                    row.key, row.bucket, row.secs
                );
                let _ = std::io::stderr().flush();
                if let Ok(mut slot) = slots[i].lock() {
                    *slot = Some(row);
                }
            });
        }
    });
    slots
        .into_iter()
        .filter_map(|s| s.into_inner().ok().flatten())
        .collect()
}

/// Resolves, lowers and solves one row.
fn measure_row(
    cfg: &Config,
    baseline: &Baseline,
    relpath: &str,
    idx: usize,
    started: std::time::Instant,
) -> Row {
    let key = format!("{relpath}[{idx}]");
    let jar = baseline.lookup(relpath, idx);
    let finish = |bucket: &str,
                  verdict: Option<InstrumentVerdict>,
                  outcome: Option<InstrumentOutcome>| Row {
        key: key.clone(),
        bucket: bucket.to_owned(),
        verdict,
        jar,
        agreement: agreement(verdict, jar),
        outcome,
        secs: started.elapsed().as_secs_f64(),
    };

    let Some((graph, world)) = resolve(&cfg.root.join(relpath)) else {
        return finish("resolve_failed", None, None);
    };
    let Some(command) = world.commands.get(idx) else {
        return finish("no_such_command", None, None);
    };
    if is_temporal_model(&world, &graph, command) {
        // The temporal pipeline is a per-length sweep, not a single translate;
        // out of scope for a stage-1 verdict instrument, and typed rather than
        // silently mismeasured.
        return finish("temporal_out_of_scope", None, None);
    }
    let Ok(scoped) = compute_universe(&world, &graph, command) else {
        return finish("mettle_defer:scope", None, None);
    };
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let expect_one = matches!(command.expect, Some(als_syntax::ast::Expect::Sat));
    let opts = SolveOptions {
        allow_overflow: cfg.allow_overflow,
        conflict_budget: Some(cfg.conflicts),
        encode_budget: Some(cfg.encode),
        symmetry: cfg.symmetry.unwrap_or(if expect_one { 0 } else { 20 }),
        ..SolveOptions::default()
    };
    let goal = match lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx) {
        Ok(g) => g,
        Err(e) => return finish(&format!("mettle_defer:lower:{e}"), None, None),
    };
    match solve_goal_with_backend(
        &ir,
        &scoped,
        &goal,
        &bounds,
        &opts,
        cfg.backend,
        cfg.wall_secs,
    ) {
        Ok(outcome) => {
            let bucket = match outcome.verdict {
                InstrumentVerdict::Unknown => "mettle_defer:over_budget".to_owned(),
                v => format!("answered_{}", v.name()),
            };
            finish(&bucket, Some(outcome.verdict), Some(outcome))
        }
        Err(TranslateError::CapacityExceeded { .. }) => finish("mettle_defer:capacity", None, None),
        Err(_) => finish("mettle_defer:encode", None, None),
    }
}

/// The stop-the-line comparison: a backend answer against the banked jar
/// verdict.
fn agreement(verdict: Option<InstrumentVerdict>, jar: Option<JarVerdict>) -> &'static str {
    match (verdict, jar) {
        (Some(InstrumentVerdict::Sat), Some(JarVerdict::Sat))
        | (Some(InstrumentVerdict::Unsat), Some(JarVerdict::Unsat)) => "agree",
        (Some(InstrumentVerdict::Sat), Some(JarVerdict::Unsat))
        | (Some(InstrumentVerdict::Unsat), Some(JarVerdict::Sat)) => "DISAGREE",
        (Some(InstrumentVerdict::Sat | InstrumentVerdict::Unsat), Some(JarVerdict::Nonverdict)) => {
            "jar_nonverdict"
        }
        (Some(InstrumentVerdict::Sat | InstrumentVerdict::Unsat), None) => "no_baseline",
        _ => "no_answer",
    }
}

/// Loads and resolves one `.als` file.
fn resolve(path: &Path) -> Option<(ModuleGraph, als_types::ResolvedWorld)> {
    let loader = FilesystemLoader::new();
    let canon = std::fs::canonicalize(path).ok()?;
    let root = canon.to_string_lossy().replace('\\', "/");
    let graph = ModuleGraph::load(&root, &loader).ok()?;
    let world = als_types::resolve(&graph).ok()?.world;
    Some((graph, world))
}

/// The human-readable table (stdout).
fn print_table(cfg: &Config, rows: &[Row]) {
    println!(
        "backend={} conflicts={} encode={} wall={:?} rows={}",
        cfg.backend.name(),
        cfg.conflicts,
        cfg.encode,
        cfg.wall_secs,
        rows.len()
    );
    println!(
        "{:<72} {:<26} {:<10} {:>9} {:>12} {:>12} {:>10}",
        "row", "bucket", "jar", "secs", "vars", "clauses", "conflicts"
    );
    for row in rows {
        let outcome = row.outcome.as_ref();
        println!(
            "{:<72} {:<26} {:<10} {:>9.1} {:>12} {:>12} {:>10}",
            row.key,
            row.bucket,
            match row.jar {
                Some(JarVerdict::Sat) => "sat",
                Some(JarVerdict::Unsat) => "unsat",
                Some(JarVerdict::Nonverdict) => "nonverdict",
                None => "-",
            },
            row.secs,
            outcome.map_or(0, |o| o.num_vars as usize),
            outcome.map_or(0, |o| o.num_clauses),
            outcome
                .and_then(|o| o.conflicts_used)
                .map_or_else(|| "-".to_owned(), |c| c.to_string()),
        );
    }
    let answered = rows.iter().filter(|r| r.verdict.is_some()).count();
    let stuck = rows
        .iter()
        .filter(|r| r.verdict == Some(InstrumentVerdict::Unknown))
        .count();
    let disagree: Vec<&str> = rows
        .iter()
        .filter(|r| r.agreement == "DISAGREE")
        .map(|r| r.key.as_str())
        .collect();
    let self_check: Vec<&str> = rows
        .iter()
        .filter(|r| {
            r.outcome
                .as_ref()
                .is_some_and(|o| o.self_check_fail.is_some())
        })
        .map(|r| r.key.as_str())
        .collect();
    println!(
        "\nanswered {} / {} (still stuck {stuck}) · DISAGREE {} · self-check failures {}",
        answered - stuck,
        rows.len(),
        disagree.len(),
        self_check.len()
    );
    for key in disagree {
        println!("  DISAGREE: {key}");
    }
    for key in self_check {
        println!("  SELF-CHECK FAIL: {key}");
    }
}

/// Writes the JSON artifact by hand — this bin has no serde dependency and the
/// shape is four scalar fields per row.
fn write_json(path: &Path, cfg: &Config, rows: &[Row]) -> std::io::Result<()> {
    use std::fmt::Write as _;

    let mut s = String::new();
    s.push_str("{\n");
    let _ = writeln!(s, "  \"backend\": \"{}\",", cfg.backend.name());
    let _ = writeln!(s, "  \"conflicts\": {},", cfg.conflicts);
    let _ = writeln!(s, "  \"encode_budget\": {},", cfg.encode);
    let _ = writeln!(
        s,
        "  \"wall_secs\": {},",
        cfg.wall_secs
            .map_or_else(|| "null".to_owned(), |w| format!("{w}"))
    );
    s.push_str("  \"rows\": [\n");
    for (i, row) in rows.iter().enumerate() {
        let outcome = row.outcome.as_ref();
        let _ = write!(
            s,
            concat!(
                "    {{\"key\": \"{}\", \"bucket\": \"{}\", \"verdict\": \"{}\", ",
                "\"jar\": \"{}\", \"agreement\": \"{}\", \"secs\": {:.2}, ",
                "\"vars\": {}, \"clauses\": {}, \"encode_ms\": {}, \"solve_ms\": {}, ",
                "\"conflicts_used\": {}, \"self_check_fail\": {}}}{}\n"
            ),
            row.key,
            row.bucket,
            row.verdict.map_or("-", InstrumentVerdict::name),
            match row.jar {
                Some(JarVerdict::Sat) => "sat",
                Some(JarVerdict::Unsat) => "unsat",
                Some(JarVerdict::Nonverdict) => "nonverdict",
                None => "-",
            },
            row.agreement,
            row.secs,
            outcome.map_or(0, |o| o.num_vars as usize),
            outcome.map_or(0, |o| o.num_clauses),
            outcome.map_or(0, |o| o.encode_ms),
            outcome.map_or(0, |o| o.solve_ms),
            outcome
                .and_then(|o| o.conflicts_used)
                .map_or_else(|| "null".to_owned(), |c| c.to_string()),
            outcome
                .and_then(|o| o.self_check_fail.as_deref())
                .map_or_else(
                    || "null".to_owned(),
                    |f| format!("\"{}\"", f.escape_debug())
                ),
            if i + 1 == rows.len() { "" } else { "," },
        );
    }
    s.push_str("  ]\n}\n");
    std::fs::write(path, s)
}
