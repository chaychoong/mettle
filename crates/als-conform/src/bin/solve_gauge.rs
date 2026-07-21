//! mt-037 — the differential **solve gauge** + counting net, with the mt-054
//! throughput & feedback-loop upgrades.
//!
//! Drives mettle's own solve pipeline over the corpus (parallel under `--jobs`),
//! diffs verdicts against the cached `baselines/*-verdict.json` jar answers, and
//! — under `--count` — compares model counts against the cached
//! `baselines/*-count-sb<N>.json` count baselines (or a live jar with
//! `--live-jar`).
//!
//! ```text
//!   solve-gauge [ROOT...] [OPTIONS]
//!   solve-gauge --refresh-counts OUT.json [ROOT...] [OPTIONS]
//! ```
//! `ROOT` is a directory (walked for `.als`) or a single `.als` file; the default
//! is the two corpus dirs.
//!
//! This bin prints and sets the exit code (STYLE E3); the library never does.
//! Exit is `0` unless the **tool** itself failed (e.g. `--count --live-jar` with
//! no reference jar, or a count-baseline config mismatch) or a `--fail-fast` run
//! stopped early (exit `1`).

use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

use als_conform::{refresh_counts, run_gauge, GaugeConfig, StatusFile};

/// Absolute workspace root (`crates/als-conform/../..`).
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn default_shim() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/shim/OracleShim.java"))
}

/// The default parallel worker count (all logical CPUs), or 1 if unknown.
fn default_jobs() -> usize {
    std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get)
}

fn print_usage() {
    eprintln!(
        "usage: solve-gauge [ROOT...] [OPTIONS]\n\
         \x20\x20\x20\x20\x20\x20 solve-gauge --refresh-counts OUT.json [ROOT...] [OPTIONS]\n\
         \n\
         ROOT                     a directory (walked for .als) or a single .als file\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20(default: corpus/alloytools-models/models + corpus/portus-63)\n\
         \n\
         Stage 1 (always): mettle verdict vs baselines/*-verdict.json.\n\
         Stage 2 (--count): model count vs cached baselines/*-count-sb<N>.json (or --live-jar).\n\
         \n\
         Determinism: the stdout report and --json-out are byte-identical at ANY --jobs\n\
         count for a FULL run. A --fail-fast PARTIAL report is not byte-stable across jobs.\n\
         \n\
         Options:\n\
         \x20\x20--count                enable stage 2 (cached count baselines by default)\n\
         \x20\x20--live-jar             stage 2 runs one live JVM per file (needs the jar)\n\
         \x20\x20--jobs N               parallel workers (default: all CPUs; 1 = sequential)\n\
         \x20\x20--fail-fast            stop at the first DISAGREE/panic/self-check/COUNT_MISMATCH (exit 1)\n\
         \x20\x20--only SUBSTR          keep only files whose relpath contains SUBSTR (repeatable)\n\
         \x20\x20--from-report PATH     delta mode: a prior --json-out report to filter against\n\
         \x20\x20--from-buckets B1,B2   re-run only files with a command in these buckets (+ files absent from PATH)\n\
         \x20\x20--symmetry N           stage-1 (verdict net) symmetry cap (default 20; 0 = no SBP)\n\
         \x20\x20--count-symmetry N     stage-2 (count net) symmetry on BOTH sides (default 0 = SB-0 yardstick)\n\
         \x20\x20--conflicts N          per-command SAT conflict budget (default 10000)\n\
         \x20\x20--encode-budget N      per-command encode-effort budget (default 4000000)\n\
         \x20\x20--primary-var-cap N    skip a command past this many primary vars (default 20000)\n\
         \x20\x20--count-cap N          enumerate at most N instances per command (default 10000)\n\
         \x20\x20--enum-budget N        total effort across one command's enumeration (default 250000000)\n\
         \x20\x20--allow-overflow       set noOverflow=false on both sides (default: forbid)\n\
         \x20\x20--jar PATH             reference jar (default oracle/org.alloytools.alloy.dist.jar)\n\
         \x20\x20--shim PATH            OracleShim.java source (default: the crate copy)\n\
         \x20\x20--jar-timeout SECS     per-file JVM timeout (default 300)\n\
         \x20\x20--baselines DIR        baselines dir (default: <workspace>/baselines)\n\
         \x20\x20--json-out PATH        write the report as JSON to PATH\n\
         \x20\x20--refresh-counts OUT   refresh mode: write a count baseline for every .als to OUT (jar; no stage 1)\n\
         \x20\x20--resume               refresh mode: skip files already present in OUT\n\
         \x20\x20--status-file PATH     owner-facing status monitor path (default: <workspace>/status/<tool>.txt)\n\
         \x20\x20--no-status            disable the status monitor"
    );
}

/// A parsed invocation.
struct Cli {
    cfg: GaugeConfig,
    json_out: Option<PathBuf>,
    status_file: Option<PathBuf>,
    no_status: bool,
    refresh_out: Option<PathBuf>,
    resume: bool,
}

/// Parses arguments, or `None` to print usage/help.
#[allow(
    clippy::too_many_lines,
    reason = "one flat, self-evident flag dispatch; splitting would only scatter it"
)]
fn parse_args() -> Option<Cli> {
    let root = workspace_root();
    let mut roots: Vec<PathBuf> = Vec::new();
    let mut cfg = GaugeConfig {
        roots: Vec::new(),
        workspace_root: root.clone(),
        baselines_dir: root.join("baselines"),
        // Measured budgets that keep the two-corpus sweep tractable (mt-037,
        // re-tuned mt-049). mt-049's solver `reduce_db` + env-cached grounding
        // memoisation made each conflict and each encode cheaper, so the conflict
        // budget was raised 5k → 10k (sweep ~16 min, converting more over_budget
        // commands into verdicts) while the **encode budget stays 4M**: raising it
        // is intractable for the default sweep — 8M timed out past 40 min and
        // 24/50M grinds single commands for CPU-hours (the mt-037 grind mode).
        // The 20k primary-var cap is likewise unchanged. Scale any of them up
        // per-run via the flags for a deeper (slower) gauge.
        conflict_budget: 10_000,
        encode_budget: 4_000_000,
        primary_var_cap: 20_000,
        allow_overflow: false,
        // SB-20 is the default-config verdict net (translation-ref §16.4); SB-0
        // stays the counting yardstick (ADR-0002), byte-identical to pre-mt-048.
        symmetry: 20,
        count_symmetry: 0,
        count: false,
        count_cap: 10_000,
        enum_budget: 250_000_000,
        jar_path: root.join("oracle/org.alloytools.alloy.dist.jar"),
        shim_source: default_shim(),
        jar_timeout: Duration::from_mins(5),
        jobs: default_jobs(),
        live_jar: false,
        fail_fast: false,
        only: Vec::new(),
        from_report: None,
        from_buckets: Vec::new(),
    };
    let mut json_out: Option<PathBuf> = None;
    let mut status_file: Option<PathBuf> = None;
    let mut no_status = false;
    let mut refresh_out: Option<PathBuf> = None;
    let mut resume = false;

    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--count" => cfg.count = true,
            "--live-jar" => cfg.live_jar = true,
            "--jobs" => cfg.jobs = it.next()?.parse::<usize>().ok()?.max(1),
            "--fail-fast" => cfg.fail_fast = true,
            "--only" => cfg.only.push(it.next()?),
            "--from-report" => cfg.from_report = Some(PathBuf::from(it.next()?)),
            "--from-buckets" => {
                cfg.from_buckets.extend(
                    it.next()?
                        .split(',')
                        .map(str::to_owned)
                        .filter(|s| !s.is_empty()),
                );
            }
            "--symmetry" => cfg.symmetry = it.next()?.parse().ok()?,
            "--count-symmetry" => cfg.count_symmetry = it.next()?.parse().ok()?,
            "--allow-overflow" => cfg.allow_overflow = true,
            "--conflicts" => cfg.conflict_budget = it.next()?.parse().ok()?,
            "--encode-budget" => cfg.encode_budget = it.next()?.parse().ok()?,
            "--primary-var-cap" => cfg.primary_var_cap = it.next()?.parse().ok()?,
            "--count-cap" => cfg.count_cap = it.next()?.parse().ok()?,
            "--enum-budget" => cfg.enum_budget = it.next()?.parse().ok()?,
            "--jar" => cfg.jar_path = PathBuf::from(it.next()?),
            "--shim" => cfg.shim_source = PathBuf::from(it.next()?),
            "--jar-timeout" => cfg.jar_timeout = Duration::from_secs(it.next()?.parse().ok()?),
            "--baselines" => cfg.baselines_dir = PathBuf::from(it.next()?),
            "--json-out" => json_out = Some(PathBuf::from(it.next()?)),
            "--refresh-counts" => refresh_out = Some(PathBuf::from(it.next()?)),
            "--resume" => resume = true,
            "--status-file" => status_file = Some(PathBuf::from(it.next()?)),
            "--no-status" => no_status = true,
            "-h" | "--help" => return None,
            other if other.starts_with("--") => {
                eprintln!("solve-gauge: unknown option {other}");
                return None;
            }
            other => roots.push(PathBuf::from(other)),
        }
    }

    cfg.roots = if roots.is_empty() {
        als_conform::solve_gauge::DEFAULT_CORPUS_SUBDIRS
            .iter()
            .map(|sub| root.join(sub))
            .collect()
    } else {
        roots
    };
    Some(Cli {
        cfg,
        json_out,
        status_file,
        no_status,
        refresh_out,
        resume,
    })
}

/// A one-line summary of the invocation, for the status header.
fn args_summary() -> String {
    let args: Vec<String> = std::env::args().skip(1).collect();
    format!("[args: {}]", args.join(" "))
}

/// Builds the status monitor for `tool`, honoring `--status-file` / `--no-status`.
fn make_status(cli: &Cli, tool: &str, default_name: &str) -> StatusFile {
    if cli.no_status {
        return StatusFile::disabled();
    }
    let path = cli
        .status_file
        .clone()
        .unwrap_or_else(|| cli.cfg.workspace_root.join("status").join(default_name));
    StatusFile::new(path, tool, &args_summary())
}

fn main() -> ExitCode {
    let Some(cli) = parse_args() else {
        print_usage();
        return ExitCode::from(2);
    };

    if cli.refresh_out.is_some() {
        run_refresh(&cli)
    } else {
        run_gauge_mode(&cli)
    }
}

/// The `--refresh-counts` path: build a count baseline, no stage 1.
fn run_refresh(cli: &Cli) -> ExitCode {
    let out = cli.refresh_out.clone().unwrap_or_default();
    let mut status = make_status(cli, "refresh-counts", "refresh-counts.txt");
    let result = {
        let mut progress = |line: &str| {
            eprintln!("{line}");
            status.heartbeat(line);
        };
        refresh_counts(&cli.cfg, &out, cli.resume, &mut progress)
    };
    match result {
        Ok(()) => {
            status.done(&format!("refresh complete → {}", out.display()));
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("solve-gauge: {e}");
            status.done(&format!("FAILED: {e}"));
            ExitCode::from(2)
        }
    }
}

/// The gauge path (stage 1 + optional stage 2).
fn run_gauge_mode(cli: &Cli) -> ExitCode {
    let mut status = make_status(cli, "solve-gauge", "solve-gauge.txt");
    let result = {
        let mut progress = |line: &str| {
            eprintln!("{line}");
            status.heartbeat(line);
        };
        run_gauge(&cli.cfg, &mut progress)
    };

    let report = match result {
        Ok(report) => report,
        Err(als_conform::ConformError::JarNotFound(path)) => {
            eprintln!(
                "solve-gauge: reference jar not found at {} (needed for --count --live-jar / --refresh-counts)\n\
                 Fetch it per docs/reference/alloy6-reference.md, or use cached count baselines.",
                path.display()
            );
            status.done("FAILED: jar not found");
            return ExitCode::from(2);
        }
        Err(e) => {
            eprintln!("solve-gauge: {e}");
            status.done(&format!("FAILED: {e}"));
            return ExitCode::from(2);
        }
    };

    print!("{}", report.render_text());

    if let Some(path) = &cli.json_out {
        match report.to_json() {
            Ok(json) => {
                if let Err(e) = std::fs::write(path, json) {
                    eprintln!("solve-gauge: failed to write {}: {e}", path.display());
                    status.done("FAILED: json write");
                    return ExitCode::from(2);
                }
            }
            Err(e) => {
                eprintln!("solve-gauge: {e}");
                status.done(&format!("FAILED: {e}"));
                return ExitCode::from(2);
            }
        }
    }

    let summary = format!(
        "{} commands, {} DISAGREE, {} panics, {} COUNT_MISMATCH{}",
        report.commands,
        report.disagreements.len(),
        report.panics.len(),
        report.count_mismatches.len(),
        if report.partial { " (PARTIAL)" } else { "" }
    );
    status.done(&summary);

    // A fail-fast partial run exits 1; otherwise a gauge is exit 0 even with
    // disagreements/mismatches (only a tool failure, handled above, is nonzero).
    ExitCode::from(report.exit_status())
}
