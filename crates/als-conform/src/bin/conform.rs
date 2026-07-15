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

fn main() -> ExitCode {
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
