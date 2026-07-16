//! CLI runner for `als-conform` (mt-006 v0): drives the reference Alloy
//! jar over one or more `.als` files/directories, runs Net 0 (`expect`
//! annotation cross-check), prints a text scorecard, optionally writes a
//! JSON artifact, and exits nonzero when any command mismatches its
//! `expect` annotation.
//!
//! This is the only place in the crate allowed to print or call
//! `process::exit` (STYLE E3) -- `als_conform` the library never does.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;

use als_conform::{EnumerationCap, OracleConfig};

struct Args {
    inputs: Vec<PathBuf>,
    jar: PathBuf,
    shim: PathBuf,
    symmetry: i32,
    no_overflow: bool,
    solver: String,
    enumeration: EnumerationCap,
    timeout: Duration,
    json_out: Option<PathBuf>,
}

impl Default for Args {
    fn default() -> Self {
        Self {
            inputs: Vec::new(),
            jar: PathBuf::from("oracle/org.alloytools.alloy.dist.jar"),
            // The shim source ships inside this crate (oracle/ is
            // git-ignored; the jar is re-downloadable, our own code is not).
            shim: PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/shim/OracleShim.java")),
            symmetry: 20,
            no_overflow: true,
            solver: "sat4j".to_string(),
            enumeration: EnumerationCap::VerdictOnly,
            timeout: Duration::from_mins(1),
            json_out: None,
        }
    }
}

fn print_usage() {
    eprintln!(
        "usage: conform [OPTIONS] <file.als|dir>...\n\
         \x20\x20\x20conform bench [<corpus-dir>] [OPTIONS]   (mt-024: conformance + speed report; conform bench --help)\n\
         \n\
         Options:\n\
         \x20\x20--jar PATH             reference jar (default oracle/org.alloytools.alloy.dist.jar)\n\
         \x20\x20--shim PATH            OracleShim.java source (default: the copy in crates/als-conform/shim/)\n\
         \x20\x20--symmetry N           A4Options.symmetry (default 20; ADR-0002 counting net uses 0)\n\
         \x20\x20--allow-overflow       set noOverflow=false (default: forbid, per LEDGER-001)\n\
         \x20\x20--solver NAME          A4Options solver factory (default sat4j)\n\
         \x20\x20--enumerate verdict|exhaustive|N   enumeration cap (default verdict)\n\
         \x20\x20--timeout SECS         per-file JVM timeout in seconds (default 60)\n\
         \x20\x20--json-out PATH        write the scorecard as JSON to PATH"
    );
}

/// Hand-rolled argument parsing: the flag set is small and fixed, so a
/// dependency like `clap` isn't justified here (STYLE P1/P2).
fn parse_args() -> Option<Args> {
    let mut args = Args::default();
    let mut it = std::env::args().skip(1).peekable();
    it.peek()?;
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--jar" => args.jar = PathBuf::from(it.next()?),
            "--shim" => args.shim = PathBuf::from(it.next()?),
            "--symmetry" => args.symmetry = it.next()?.parse().ok()?,
            "--allow-overflow" => args.no_overflow = false,
            "--solver" => args.solver = it.next()?,
            "--enumerate" => {
                args.enumeration = match it.next()?.as_str() {
                    "verdict" => EnumerationCap::VerdictOnly,
                    "exhaustive" => EnumerationCap::Exhaustive,
                    n => EnumerationCap::UpTo(n.parse().ok()?),
                };
            }
            "--timeout" => args.timeout = Duration::from_secs(it.next()?.parse().ok()?),
            "--json-out" => args.json_out = Some(PathBuf::from(it.next()?)),
            "-h" | "--help" => return None,
            other => args.inputs.push(PathBuf::from(other)),
        }
    }
    if args.inputs.is_empty() {
        return None;
    }
    Some(args)
}

/// Expands files/directories into a flat list of `.als` files.
/// Non-recursive-directory ordering doesn't matter: `run_oracle_on_files`
/// sorts and dedups before running (STYLE C2/C3).
fn collect_als_files(inputs: &[PathBuf]) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for input in inputs {
        collect_into(input, &mut out);
    }
    out
}

fn collect_into(path: &Path, out: &mut Vec<PathBuf>) {
    if path.is_dir() {
        let Ok(entries) = std::fs::read_dir(path) else {
            return;
        };
        for entry in entries.flatten() {
            collect_into(&entry.path(), out);
        }
    } else if path.extension().is_some_and(|ext| ext == "als") {
        out.push(path.to_path_buf());
    }
}

// ---------------------------------------------------------------------------
// `bench` subcommand (mt-024): one-command conformance + speed report.
// ---------------------------------------------------------------------------

fn print_bench_usage() {
    eprintln!(
        "usage: conform bench [<corpus-dir>] [OPTIONS]\n\
         \n\
         Runs mettle's parse+resolve pipeline and (unless --skip-jar) the pinned\n\
         reference jar over the same corpus, and prints one deterministic\n\
         conformance + speed report (text to stdout, optionally JSON via --json).\n\
         \n\
         <corpus-dir>            scan this directory recursively for .als files\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20(default: corpus/alloytools-models/models + corpus/portus-63, 167 files)\n\
         \n\
         Options:\n\
         \x20\x20--jar PATH           reference jar (default oracle/org.alloytools.alloy.dist.jar)\n\
         \x20\x20--shim PATH          ResolveGaugeShim.java source (default: the copy in crates/als-conform/shim/)\n\
         \x20\x20--threads N          mettle-side parallelism (default: available cores)\n\
         \x20\x20--skip-jar           mettle-only run -- no JDK required, no jar conformance/timing\n\
         \x20\x20--cold-sample N      fresh-JVM-per-file sample size (default 10)\n\
         \x20\x20--timeout SECS       per-JVM-invocation wall-clock budget in seconds (default 60)\n\
         \x20\x20--json PATH          write the report as JSON to PATH"
    );
}

fn missing_value(flag: &str) -> ExitCode {
    eprintln!("conform bench: missing value for {flag}");
    print_bench_usage();
    ExitCode::from(2)
}

/// Parses `conform bench`'s own argument grammar and runs it. Kept
/// separate from [`parse_args`]/the legacy Net-0 flow entirely -- `bench`
/// has different inputs (a config struct, not `OracleConfig` + enumeration
/// cap) and a different report shape, so bolting it onto the existing flag
/// set would conflate two independent command surfaces.
fn bench_main(args: &[String]) -> ExitCode {
    let mut cfg = als_conform::BenchConfig::default();
    let mut json_out: Option<PathBuf> = None;
    let mut corpus_dir: Option<PathBuf> = None;

    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--jar" => {
                let Some(v) = it.next() else {
                    return missing_value("--jar");
                };
                cfg.jar_path = PathBuf::from(v);
            }
            "--shim" => {
                let Some(v) = it.next() else {
                    return missing_value("--shim");
                };
                cfg.shim_source = PathBuf::from(v);
            }
            "--threads" => {
                let Some(n) = it.next().and_then(|v| v.parse().ok()) else {
                    return missing_value("--threads");
                };
                cfg.threads = n;
            }
            "--skip-jar" => cfg.skip_jar = true,
            "--cold-sample" => {
                let Some(n) = it.next().and_then(|v| v.parse().ok()) else {
                    return missing_value("--cold-sample");
                };
                cfg.cold_sample = n;
            }
            "--timeout" => {
                let Some(secs) = it.next().and_then(|v| v.parse().ok()) else {
                    return missing_value("--timeout");
                };
                cfg.jvm_timeout = Duration::from_secs(secs);
            }
            "--json" => {
                let Some(v) = it.next() else {
                    return missing_value("--json");
                };
                json_out = Some(PathBuf::from(v));
            }
            "-h" | "--help" => {
                print_bench_usage();
                return ExitCode::SUCCESS;
            }
            other if other.starts_with("--") => {
                eprintln!("conform bench: unknown option {other}");
                print_bench_usage();
                return ExitCode::from(2);
            }
            other if corpus_dir.is_none() => corpus_dir = Some(PathBuf::from(other)),
            other => {
                eprintln!("conform bench: unexpected extra argument {other}");
                print_bench_usage();
                return ExitCode::from(2);
            }
        }
    }

    if let Some(dir) = corpus_dir {
        cfg.corpus_roots = vec![dir];
    }

    let report = match als_conform::run_bench(&cfg) {
        Ok(report) => report,
        Err(als_conform::ConformError::JarNotFound(path)) => {
            eprintln!(
                "conform bench: reference jar not found at {}\n\
                 Fetch it per docs/reference/alloy6-reference.md, or pass --skip-jar for a mettle-only run.",
                path.display()
            );
            return ExitCode::from(2);
        }
        Err(e) => {
            eprintln!("conform bench: {e}");
            return ExitCode::from(2);
        }
    };

    print!("{}", report.render_text());

    if let Some(path) = &json_out {
        match report.to_json() {
            Ok(json) => {
                if let Err(e) = std::fs::write(path, json) {
                    eprintln!("conform bench: failed to write {}: {e}", path.display());
                    return ExitCode::from(2);
                }
            }
            Err(e) => {
                eprintln!("conform bench: {e}");
                return ExitCode::from(2);
            }
        }
    }

    let any_disagreement = report.conformance.stages.iter().any(|s| s.disagree > 0);
    if any_disagreement {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}

fn main() -> ExitCode {
    let raw_args: Vec<String> = std::env::args().collect();
    if raw_args.get(1).map(String::as_str) == Some("bench") {
        return bench_main(&raw_args[2..]);
    }

    let Some(args) = parse_args() else {
        print_usage();
        return ExitCode::from(2);
    };

    let files = collect_als_files(&args.inputs);
    if files.is_empty() {
        eprintln!("conform: no .als files found among the given inputs");
        return ExitCode::from(2);
    }

    let cfg = OracleConfig::new(&args.jar, &args.shim)
        .with_symmetry(args.symmetry)
        .with_no_overflow(args.no_overflow)
        .with_solver(&args.solver)
        .with_timeout(args.timeout);

    let scorecard = match als_conform::run_oracle_on_files(&cfg, &files, args.enumeration) {
        Ok(scorecard) => scorecard,
        Err(e) => {
            eprintln!("conform: {e}");
            return ExitCode::from(2);
        }
    };

    print!("{}", scorecard.render_text());

    if let Some(json_path) = &args.json_out {
        match scorecard.to_json() {
            Ok(json) => {
                if let Err(e) = std::fs::write(json_path, json) {
                    eprintln!("conform: failed to write {}: {e}", json_path.display());
                    return ExitCode::from(2);
                }
            }
            Err(e) => {
                eprintln!("conform: {e}");
                return ExitCode::from(2);
            }
        }
    }

    if scorecard.totals.mismatches > 0
        || scorecard.totals.timeouts > 0
        || scorecard.totals.errors > 0
    {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}
