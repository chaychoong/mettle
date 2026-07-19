//! mt-037 — the differential **solve gauge** + **SB-0 counting net**.
//!
//! Drives mettle's own solve pipeline over the corpus, diffs verdicts against
//! the cached `baselines/*-verdict.json` jar answers, and — under `--count` —
//! enumerates SB-0 model counts against the pinned reference jar for goals
//! outside the documented count-divergence families (ADR-0002, LIMITATIONS).
//!
//! ```text
//!   solve-gauge [ROOT...] [OPTIONS]
//! ```
//! `ROOT` is a directory (walked for `.als`) or a single `.als` file; the
//! default is the two corpus dirs. Verdict stage always runs; `--count` adds
//! the jar-backed counting net.
//!
//! This bin prints and sets the exit code (STYLE E3); the library never does.
//! Exit code is `0` (it's a gauge, not a test) unless the **tool** itself failed
//! — e.g. `--count` with no reference jar to compile the shim against.

use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

use als_conform::{run_gauge, GaugeConfig};

/// Absolute workspace root (`crates/als-conform/../..`), so every default path
/// resolves the same regardless of the invoking cwd.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn default_shim() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/shim/OracleShim.java"))
}

fn print_usage() {
    eprintln!(
        "usage: solve-gauge [ROOT...] [OPTIONS]\n\
         \n\
         ROOT                     a directory (walked for .als) or a single .als file\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20(default: corpus/alloytools-models/models + corpus/portus-63)\n\
         \n\
         Stage 1 (always): mettle verdict vs baselines/*-verdict.json.\n\
         Stage 2 (--count): SB-0 model count vs the pinned jar at symmetry 0.\n\
         \n\
         Options:\n\
         \x20\x20--count                enable stage 2 (needs the reference jar)\n\
         \x20\x20--conflicts N          per-command SAT conflict budget (default 10000)\n\
         \x20\x20--encode-budget N      per-command encode-effort budget (default 4000000)\n\
         \x20\x20--primary-var-cap N    skip a command past this many primary vars (default 20000)\n\
         \x20\x20--count-cap N          enumerate at most N instances per command (default 10000)\n\
         \x20\x20--allow-overflow       set noOverflow=false on both sides (default: forbid)\n\
         \x20\x20--jar PATH             reference jar (default oracle/org.alloytools.alloy.dist.jar)\n\
         \x20\x20--shim PATH            OracleShim.java source (default: the crate copy)\n\
         \x20\x20--jar-timeout SECS     per-file JVM timeout for stage 2 (default 300)\n\
         \x20\x20--baselines DIR        baselines dir (default: <workspace>/baselines)\n\
         \x20\x20--json-out PATH        write the report as JSON to PATH"
    );
}

/// Parses arguments into a [`GaugeConfig`], or `None` to print usage/help.
#[allow(
    clippy::too_many_lines,
    reason = "one flat, self-evident flag dispatch; splitting would only scatter it"
)]
fn parse_args() -> Option<(GaugeConfig, Option<PathBuf>)> {
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
        // 24M+ grinds for CPU-hours on single huge commands (the mt-037 grind
        // mode). The 20k primary-var cap is likewise unchanged. Scale any of them
        // up per-run via the flags for a deeper (slower) gauge.
        conflict_budget: 10_000,
        encode_budget: 4_000_000,
        primary_var_cap: 20_000,
        allow_overflow: false,
        count: false,
        count_cap: 10_000,
        jar_path: root.join("oracle/org.alloytools.alloy.dist.jar"),
        shim_source: default_shim(),
        jar_timeout: Duration::from_mins(5),
    };
    let mut json_out: Option<PathBuf> = None;

    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--count" => cfg.count = true,
            "--allow-overflow" => cfg.allow_overflow = true,
            "--conflicts" => cfg.conflict_budget = it.next()?.parse().ok()?,
            "--encode-budget" => cfg.encode_budget = it.next()?.parse().ok()?,
            "--primary-var-cap" => cfg.primary_var_cap = it.next()?.parse().ok()?,
            "--count-cap" => cfg.count_cap = it.next()?.parse().ok()?,
            "--jar" => cfg.jar_path = PathBuf::from(it.next()?),
            "--shim" => cfg.shim_source = PathBuf::from(it.next()?),
            "--jar-timeout" => cfg.jar_timeout = Duration::from_secs(it.next()?.parse().ok()?),
            "--baselines" => cfg.baselines_dir = PathBuf::from(it.next()?),
            "--json-out" => json_out = Some(PathBuf::from(it.next()?)),
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
    Some((cfg, json_out))
}

fn main() -> ExitCode {
    let Some((cfg, json_out)) = parse_args() else {
        print_usage();
        return ExitCode::from(2);
    };

    let report = match run_gauge(&cfg, &mut |line| eprintln!("{line}")) {
        Ok(report) => report,
        Err(als_conform::ConformError::JarNotFound(path)) => {
            eprintln!(
                "solve-gauge: reference jar not found at {} (needed for --count)\n\
                 Fetch it per docs/reference/alloy6-reference.md, or drop --count for the verdict stage only.",
                path.display()
            );
            return ExitCode::from(2);
        }
        Err(e) => {
            eprintln!("solve-gauge: {e}");
            return ExitCode::from(2);
        }
    };

    print!("{}", report.render_text());

    if let Some(path) = &json_out {
        match report.to_json() {
            Ok(json) => {
                if let Err(e) = std::fs::write(path, json) {
                    eprintln!("solve-gauge: failed to write {}: {e}", path.display());
                    return ExitCode::from(2);
                }
            }
            Err(e) => {
                eprintln!("solve-gauge: {e}");
                return ExitCode::from(2);
            }
        }
    }

    // A gauge, not a test: exit 0 even with disagreements/mismatches. Only a
    // tool failure (handled above) is nonzero.
    ExitCode::SUCCESS
}
