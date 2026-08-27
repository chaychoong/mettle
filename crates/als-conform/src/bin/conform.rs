//! CLI runner for `als-conform` (mt-006 v0): drives the reference Alloy
//! jar over one or more `.als` files/directories, runs Net 0 (`expect`
//! annotation cross-check), prints a text scorecard, optionally writes a
//! JSON artifact, and exits nonzero when any command mismatches its
//! `expect` annotation.
//!
//! This is the only place in the crate allowed to print or call
//! `process::exit` (STYLE E3) -- `als_conform` the library never does.

use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;

use als_conform::{EnumerationCap, OracleConfig, WatchServer};

/// Absolute workspace root (`crates/als-conform/../..`), for resolving
/// `conform watch`'s default baseline path the same way `solve-gauge` finds
/// its default `--baselines` dir.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

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
         \x20\x20\x20conform watch <progress.jsonl> [OPTIONS]  (mt-094: live solve-gauge dashboard; conform watch --help)\n\
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
         \x20\x20\x20conform bench --solve [OPTIONS]        (mt-138: solve-time head-to-head, mettle vs. jar)\n\
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
         \x20\x20--json PATH          write the report as JSON to PATH\n\
         \n\
         --solve mode (mt-138): per-command solve-time head-to-head, mettle (CaDiCaL) vs. the\n\
         reference jar (sat4j), at the LEDGER-001 defaults (symmetry 20, forbid overflow, sat4j).\n\
         Replaces the parse+resolve report above; ignores --skip-jar/--threads/--cold-sample.\n\
         \x20\x20--jar PATH           reference jar (as above)\n\
         \x20\x20--shim PATH          OracleShim.java source (default: the copy in crates/als-conform/shim/)\n\
         \x20\x20--timeout SECS       per-file JVM wall-clock budget in seconds (default 60)\n\
         \x20\x20--only SUBSTR        keep only files whose path contains SUBSTR (repeatable)\n\
         \x20\x20--json PATH          write the report as JSON to PATH"
    );
}

fn missing_value(flag: &str) -> ExitCode {
    eprintln!("conform bench: missing value for {flag}");
    print_bench_usage();
    ExitCode::from(2)
}

/// The parsed result of `conform bench`'s own argument grammar.
struct BenchArgs {
    cfg: als_conform::BenchConfig,
    json_out: Option<PathBuf>,
    corpus_dir: Option<PathBuf>,
    /// `--solve` (mt-138): dispatch to [`solve_bench_main`] instead of the
    /// default parse+resolve report.
    solve: bool,
    /// `--only` (mt-138, `--solve`-only): row-selection filter.
    only: Vec<String>,
}

/// Parses `conform bench`'s own argument grammar, or returns the `ExitCode`
/// to exit with immediately (`--help`, or a parse error). Split out of
/// [`bench_main`] to keep that function under the line-count cap -- this is
/// pure argument parsing, no I/O.
fn parse_bench_args(args: &[String]) -> Result<BenchArgs, ExitCode> {
    let mut out = BenchArgs {
        cfg: als_conform::BenchConfig::default(),
        json_out: None,
        corpus_dir: None,
        solve: false,
        only: Vec::new(),
    };

    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--jar" => {
                let Some(v) = it.next() else {
                    return Err(missing_value("--jar"));
                };
                out.cfg.jar_path = PathBuf::from(v);
            }
            "--shim" => {
                let Some(v) = it.next() else {
                    return Err(missing_value("--shim"));
                };
                out.cfg.shim_source = PathBuf::from(v);
            }
            "--threads" => {
                let Some(n) = it.next().and_then(|v| v.parse().ok()) else {
                    return Err(missing_value("--threads"));
                };
                out.cfg.threads = n;
            }
            "--skip-jar" => out.cfg.skip_jar = true,
            "--cold-sample" => {
                let Some(n) = it.next().and_then(|v| v.parse().ok()) else {
                    return Err(missing_value("--cold-sample"));
                };
                out.cfg.cold_sample = n;
            }
            "--timeout" => {
                let Some(secs) = it.next().and_then(|v| v.parse().ok()) else {
                    return Err(missing_value("--timeout"));
                };
                out.cfg.jvm_timeout = Duration::from_secs(secs);
            }
            "--json" => {
                let Some(v) = it.next() else {
                    return Err(missing_value("--json"));
                };
                out.json_out = Some(PathBuf::from(v));
            }
            "--solve" => out.solve = true,
            "--only" => {
                let Some(v) = it.next() else {
                    return Err(missing_value("--only"));
                };
                out.only.push(v.clone());
            }
            "-h" | "--help" => {
                print_bench_usage();
                return Err(ExitCode::SUCCESS);
            }
            other if other.starts_with("--") => {
                eprintln!("conform bench: unknown option {other}");
                print_bench_usage();
                return Err(ExitCode::from(2));
            }
            other if out.corpus_dir.is_none() => out.corpus_dir = Some(PathBuf::from(other)),
            other => {
                eprintln!("conform bench: unexpected extra argument {other}");
                print_bench_usage();
                return Err(ExitCode::from(2));
            }
        }
    }
    Ok(out)
}

/// Runs `conform bench`. Kept separate from [`parse_args`]/the legacy Net-0
/// flow entirely -- `bench` has different inputs (a config struct, not
/// `OracleConfig` + enumeration cap) and a different report shape, so
/// bolting it onto the existing flag set would conflate two independent
/// command surfaces.
fn bench_main(args: &[String]) -> ExitCode {
    let BenchArgs {
        mut cfg,
        json_out,
        corpus_dir,
        solve,
        only,
    } = match parse_bench_args(args) {
        Ok(parsed) => parsed,
        Err(code) => return code,
    };

    if solve {
        return solve_bench_main(&cfg, corpus_dir, only, json_out.as_deref());
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

/// `conform bench --solve` (mt-138): the solve-time head-to-head report.
/// Shares `bench`'s `--jar`/`--shim`/`--timeout`/`--json` values (already
/// parsed into `cfg` by [`bench_main`]) and the positional `<corpus-dir>`,
/// but builds and runs a [`als_conform::SolveBenchConfig`] instead --
/// `--skip-jar`/`--threads`/`--cold-sample` don't apply to this mode (there
/// is no jar-optional path: the whole point is the jar comparison).
fn solve_bench_main(
    cfg: &als_conform::BenchConfig,
    corpus_dir: Option<PathBuf>,
    only: Vec<String>,
    json_out: Option<&Path>,
) -> ExitCode {
    let mut solve_cfg = als_conform::SolveBenchConfig {
        jar_path: cfg.jar_path.clone(),
        shim_source: cfg.shim_source.clone(),
        jvm_timeout: cfg.jvm_timeout,
        only,
        ..als_conform::SolveBenchConfig::default()
    };
    if let Some(dir) = corpus_dir {
        solve_cfg.corpus_roots = vec![dir];
    }

    let report = match als_conform::run_solve_bench(&solve_cfg) {
        Ok(report) => report,
        Err(als_conform::ConformError::JarNotFound(path)) => {
            eprintln!(
                "conform bench --solve: reference jar not found at {}\n\
                 Fetch it per docs/reference/alloy6-reference.md.",
                path.display()
            );
            return ExitCode::from(2);
        }
        Err(e) => {
            eprintln!("conform bench --solve: {e}");
            return ExitCode::from(2);
        }
    };

    print!("{}", report.render_text());

    if let Some(path) = json_out {
        match report.to_json() {
            Ok(json) => {
                if let Err(e) = std::fs::write(path, json) {
                    eprintln!(
                        "conform bench --solve: failed to write {}: {e}",
                        path.display()
                    );
                    return ExitCode::from(2);
                }
            }
            Err(e) => {
                eprintln!("conform bench --solve: {e}");
                return ExitCode::from(2);
            }
        }
    }

    if report.disagreements.is_empty() {
        ExitCode::SUCCESS
    } else {
        eprintln!(
            "conform bench --solve: {} verdict disagreement(s) between mettle and the jar -- see above",
            report.disagreements.len()
        );
        ExitCode::from(1)
    }
}

// ---------------------------------------------------------------------------
// `watch` subcommand (mt-094): a live dashboard over a solve-gauge
// `--progress-jsonl` run.
// ---------------------------------------------------------------------------

/// `baselines/corpus-sweep-sb20.json`, relative to the workspace root —
/// `solve-gauge`'s default sweep-symmetry-20 artifact, and the one
/// `--capture-sweep` refreshes by default (ADR-0016/mt-057).
fn default_watch_baseline() -> PathBuf {
    workspace_root().join("baselines/corpus-sweep-sb20.json")
}

fn print_watch_usage() {
    eprintln!(
        "usage: conform watch <progress.jsonl> [OPTIONS]\n\
         \n\
         Serves a live dashboard (mt-094) of a `solve-gauge --progress-jsonl <progress.jsonl>` run:\n\
         a grid of every row's progress, polling the file roughly once a second. Safe to start\n\
         BEFORE the sweep -- the page reads \"waiting for run\" until the file has a run_start event.\n\
         \n\
         <progress.jsonl>        the file passed to `solve-gauge --progress-jsonl` (need not exist yet)\n\
         \n\
         Options:\n\
         \x20\x20--port N              listen port on 127.0.0.1 (default 4031)\n\
         \x20\x20--baseline PATH       sweep baseline for historical wall times\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20(default <workspace>/baselines/corpus-sweep-sb20.json; missing is fine, just no history)"
    );
}

fn watch_missing_value(flag: &str) -> ExitCode {
    eprintln!("conform watch: missing value for {flag}");
    print_watch_usage();
    ExitCode::from(2)
}

fn watch_main(args: &[String]) -> ExitCode {
    let mut port: u16 = 4031;
    let mut baseline: Option<PathBuf> = None;
    let mut jsonl: Option<PathBuf> = None;

    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--port" => {
                let Some(n) = it.next().and_then(|v| v.parse().ok()) else {
                    return watch_missing_value("--port");
                };
                port = n;
            }
            "--baseline" => {
                let Some(v) = it.next() else {
                    return watch_missing_value("--baseline");
                };
                baseline = Some(PathBuf::from(v));
            }
            "-h" | "--help" => {
                print_watch_usage();
                return ExitCode::SUCCESS;
            }
            other if other.starts_with("--") => {
                eprintln!("conform watch: unknown option {other}");
                print_watch_usage();
                return ExitCode::from(2);
            }
            other if jsonl.is_none() => jsonl = Some(PathBuf::from(other)),
            other => {
                eprintln!("conform watch: unexpected extra argument {other}");
                print_watch_usage();
                return ExitCode::from(2);
            }
        }
    }

    let Some(jsonl) = jsonl else {
        print_watch_usage();
        return ExitCode::from(2);
    };
    // `WatchServer` always resolves against SOME baseline path; a missing
    // file just means `/data` never gets a `hist_ms` to report (read_prior
    // degrades any unusable file to "no baseline" rather than failing).
    let baseline = baseline.unwrap_or_else(default_watch_baseline);

    let listener = match TcpListener::bind(("127.0.0.1", port)) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("conform watch: failed to bind 127.0.0.1:{port}: {e}");
            return ExitCode::from(2);
        }
    };
    eprintln!(
        "conform watch: http://127.0.0.1:{port}  (jsonl: {}, baseline: {})",
        jsonl.display(),
        baseline.display()
    );
    let server = WatchServer::new(jsonl, baseline);
    server.accept_loop(&listener);
    ExitCode::SUCCESS
}

fn main() -> ExitCode {
    let raw_args: Vec<String> = std::env::args().collect();
    if raw_args.get(1).map(String::as_str) == Some("bench") {
        return bench_main(&raw_args[2..]);
    }
    if raw_args.get(1).map(String::as_str) == Some("watch") {
        return watch_main(&raw_args[2..]);
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
