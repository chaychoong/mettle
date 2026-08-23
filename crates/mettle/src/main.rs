//! The `mettle` CLI.
//!
//! Rung 1 shipped `parse`; Rung 2 added `check`, the names-and-types
//! human-testable front end; Rung 3 added `exec`, which drives a model's
//! commands to a verdict; Rung 5 adds `serve`, which visualizes one of them:
//!
//! ```text
//! mettle parse <file.als> [--ast]
//! mettle check <file.als>
//! mettle exec <file.als> [--command <sel>] [--allow-overflow] [--conflicts N] [--encode-budget N]
//!                         [--solver <name>]
//! mettle serve <file.als> [--command <sel>] [--port N] [--bind <addr>] [--solver <name>]
//! mettle -h | --help
//! mettle -V | --version
//! ```
//!
//! `parse` parses a module and, on success, prints it back as canonical
//! Alloy 6 source (or, with `--ast`, the span-free structural dump).
//! `check` additionally loads the module graph (`open`s and all) and runs
//! the mt-018 resolver/type checker, printing any warnings and a one-line
//! success summary. `exec` (mt-036, [`exec`]) goes one rung further: for
//! each `run`/`check` command in the root module it runs the full
//! `compute_universe` → `compute_bounds` → `lower_command` → `solve_goal`
//! pipeline and prints the verdict (and any SAT instance / counterexample).
//! `serve` (mt-072, [`serve`]) solves **one** command and then answers the
//! Sterling provider protocol about it on a local port until Ctrl-C. Both
//! solving subcommands take `--solver <name>` (mt-089, ADR-0019): the default
//! `mettle` backend is the deterministic yardstick, and an optional stronger one
//! can be selected where a build has it ([`parse_solver`], [`solver_help`]).
//! Parse/lex/resolve errors render to stderr as a rustc-style caret-and-label
//! block (mt-013, [`diagnostics`]) with exit code 1; usage or I/O problems
//! exit with code 2.
//!
//! This crate is the only place that renders diagnostics or touches process
//! exit codes (STYLE E3); `als-syntax`/`als-types`/`als-core` stay print-free.

mod diagnostics;
mod exec;
mod repl;
mod serve;

use std::fmt::Write as _;
use std::io::{self, Write as _};
use std::process::ExitCode;

// `ArenaId` brings `FileId::from_index` into scope.
use als_syntax::{dump, parse, ArenaId as _, FileId};
use als_types::{FilesystemLoader, ModuleGraph, ResolveError};

/// The Alloy version mettle's conformance is measured against — the pinned
/// oracle jar (ADR-0002, `docs/reference/alloy6-reference.md`). mettle's own
/// version is independent and zero-versioned by intention (owner, 2026-07-28:
/// 0.x makes no production-readiness claim; the scorecard carries the maturity
/// signal); this constant is how `--version` states the target without
/// mirroring its number.
const TRACKED_ALLOY_VERSION: &str = "6.2.0";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(exit) => exit,
    }
}

/// Dispatches on the subcommand. Returns the process exit code to use on
/// failure; `Ok(())` means success (exit 0).
fn run(args: &[String]) -> Result<(), ExitCode> {
    match args.first().map(String::as_str) {
        Some("parse") => run_parse(&args[1..]),
        Some("check") => run_check(&args[1..]),
        Some("exec") => exec::run_exec(&args[1..]),
        Some("serve") => serve::run_serve(&args[1..]),
        // `-V`/`--version` is a top-level flag, not a subcommand (matches
        // every other single-binary Rust CLI's convention); it prints and
        // exits 0 same as `-h`/`--help` below, never reaching subcommand
        // dispatch.
        // The tracked Alloy version rides along — mettle states its
        // conformance target instead of mirroring its number (owner,
        // 2026-07-28; posture on TRACKED_ALLOY_VERSION above).
        Some("-V" | "--version") => write_stdout(format!(
            "mettle {} (tracking Alloy {TRACKED_ALLOY_VERSION})\n",
            env!("CARGO_PKG_VERSION")
        )),
        Some("-h" | "--help") | None => {
            print_usage();
            // A bare `--help`/no-args is a successful help request; an
            // unknown/missing subcommand path below is the usage error.
            if args.is_empty() {
                Err(ExitCode::from(2))
            } else {
                Ok(())
            }
        }
        Some(other) => {
            eprintln!("mettle: unknown subcommand `{other}`");
            print_usage();
            Err(ExitCode::from(2))
        }
    }
}

fn print_usage() {
    // Built once and interpolated twice: `--solver`'s valid names depend on how
    // this binary was compiled (see [`solver_help`]), and both subcommands that
    // take the flag list the same set.
    let solver = solver_help();
    eprintln!(
        "usage: mettle parse <file.als> [--ast]\n\
         \x20\x20\x20\x20\x20mettle check <file.als> [--strict]\n\
         \x20\x20\x20\x20\x20mettle exec <file.als> [--command <name|index>] [--allow-overflow]\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20[--conflicts N] [--encode-budget N]\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20[--repl] [--eval <EXPR>] [--state N]\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20[--xml <PATH>] [--solver <name>]\n\
         \x20\x20\x20\x20\x20mettle serve <file.als> [--command <name|index>] [--port N]\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20[--bind <addr>] [--solver <name>]\n\
         \x20\x20\x20\x20\x20mettle -h | --help\n\
         \x20\x20\x20\x20\x20mettle -V | --version\n\
         \n\
         Options:\n\
         \x20\x20-h, --help             print this usage text\n\
         \x20\x20-V, --version          print the mettle version\n\
         \n\
         Subcommands:\n\
         \x20\x20parse <file.als>       parse a module and print it back as canonical Alloy 6\n\
         \x20\x20check <file.als>       load, resolve, and type-check a module (and its opens)\n\
         \x20\x20exec <file.als>        run every root-module command to a verdict/instance\n\
         \x20\x20serve <file.als>       solve one command and visualize it in a browser\n\
         \n\
         Options (parse):\n\
         \x20\x20--ast                  print the span-free structural AST dump instead of source\n\
         \n\
         Options (check):\n\
         \x20\x20--strict               exit non-zero if any warning fired (verdict unchanged)\n\
         \n\
         Options (exec):\n\
         \x20\x20--command <sel>        run one command only: by 0-based index, label, or target name\n\
         \x20\x20--allow-overflow       wrap on integer overflow instead of excluding the instance\n\
         \x20\x20--conflicts N          cap SAT search effort (default: unlimited)\n\
         \x20\x20--encode-budget N      cap encode effort (default: unlimited)\n\
         \x20\x20--eval <EXPR>          evaluate EXPR against the command's instance (repeatable)\n\
         \x20\x20--repl                 evaluate expressions interactively against the instance\n\
         \x20\x20--xml <PATH>           write the command's instance as Alloy instance XML\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20(one command; not combinable with --repl/--eval/--state)\n\
         \x20\x20--state N              evaluate at trace state N (temporal commands; N wraps\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20through the loop, negatives clamp to 0; `:state N` moves in --repl)\n\
         {solver}\n\
         \n\
         Options (serve):\n\
         \x20\x20--command <sel>        the command to visualize (required unless there is one)\n\
         \x20\x20--port N               listen on <bind>:N (default 4030; 0 picks a free port)\n\
         \x20\x20--bind <addr>          address to listen on (default 127.0.0.1; 0.0.0.0 for a\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20container/remote box — the socket is unauthenticated)\n\
         {solver}"
    );
}

/// Resolves a `--solver <name>` value for subcommand `sub`, or renders the usage
/// error and returns exit code 2 (ADR-0019 stage 2, mt-089).
///
/// Three outcomes, deliberately distinct (the mt-006 no-silent-default rule): a
/// known name resolves; a name mettle *has* but this build compiled out says so
/// and names the build flag that fixes it; anything else is a typo and gets the
/// list of what this binary actually offers. Never a fallback to the default —
/// a solver the user did not ask for is a wrong answer to the question they did.
fn parse_solver(sub: &str, value: &str) -> Result<als_solve::Backend, ExitCode> {
    if let Some(backend) = als_solve::Backend::parse(value) {
        return Ok(backend);
    }
    if als_solve::Backend::COMPILED_OUT.contains(&value) {
        eprintln!(
            "mettle {sub}: solver `{value}` is not in this build (compiled without the \
             `{value}` cargo feature)\n\
             mettle {sub}: build from source with `cargo build --release -p mettle \
             --features {value}`, or pick one of: {}",
            als_solve::Backend::AVAILABLE.join(", ")
        );
    } else {
        eprintln!(
            "mettle {sub}: unknown solver `{value}`; available: {}",
            als_solve::Backend::AVAILABLE.join(", ")
        );
    }
    Err(ExitCode::from(2))
}

/// The `--solver` help lines, built from what this build can actually select so
/// the text never promises a backend the binary does not have.
fn solver_help() -> String {
    let mut help = format!(
        "\x20\x20--solver <name>        SAT backend, one of: {} (default: {})\n",
        als_solve::Backend::AVAILABLE.join(", "),
        als_solve::Backend::default().name()
    );
    if !als_solve::Backend::COMPILED_OUT.is_empty() {
        let _ = writeln!(
            help,
            "\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\
             not in this build: {} (rebuild with the matching cargo feature)",
            als_solve::Backend::COMPILED_OUT.join(", ")
        );
    }
    // The honesty the alternative backend owes the user, stated here as well as
    // in LIMITATIONS (ADR-0019 §4): what it gives up, and the one budget flag
    // whose meaning narrows under it.
    help.push_str(
        "\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\
         `mettle` is the deterministic yardstick: a fixed build gives\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\
         byte-identical answers everywhere, and it is what the conformance\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\
         scorecard measures. Any other backend searches harder but is only\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\
         deterministic per build (which instance/trace you see, and the\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\
         enumeration order, are its own); with `cadical`, --conflicts still\n\
         \x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\
         caps each solve but the conflicts it spent are not observable.",
    );
    help
}

/// Writes `text` to stdout, treating a closed pipe (`mettle parse … | head`)
/// as a quiet early exit — code 141 (128 + SIGPIPE), what a default-disposition
/// Unix tool reports — rather than the `print!` macro's panic.
fn write_stdout(text: impl std::fmt::Display) -> Result<(), ExitCode> {
    let mut out = io::stdout().lock();
    match write!(out, "{text}").and_then(|()| out.flush()) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == io::ErrorKind::BrokenPipe => Err(ExitCode::from(141)),
        Err(e) => {
            eprintln!("mettle: cannot write to stdout: {e}");
            Err(ExitCode::from(2))
        }
    }
}

/// `mettle parse <file.als> [--ast]` — hand-rolled arg parsing (no clap), per
/// the `als-conform` precedent (STYLE P1/P2, zero new deps).
fn run_parse(args: &[String]) -> Result<(), ExitCode> {
    let mut path: Option<&str> = None;
    let mut as_ast = false;
    for arg in args {
        match arg.as_str() {
            "--ast" => as_ast = true,
            "-h" | "--help" => {
                print_usage();
                return Ok(());
            }
            other if other.starts_with('-') => {
                eprintln!("mettle parse: unknown option `{other}`");
                print_usage();
                return Err(ExitCode::from(2));
            }
            other => {
                if path.replace(other).is_some() {
                    eprintln!("mettle parse: expected exactly one input file");
                    print_usage();
                    return Err(ExitCode::from(2));
                }
            }
        }
    }

    let Some(path) = path else {
        eprintln!("mettle parse: missing <file.als>");
        print_usage();
        return Err(ExitCode::from(2));
    };

    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("mettle parse: cannot read {path}: {e}");
            return Err(ExitCode::from(2));
        }
    };

    match parse(&source, FileId::from_index(0)) {
        Ok(ast) => {
            if as_ast {
                write_stdout(dump(&ast))
            } else {
                write_stdout(ast.pretty())
            }
        }
        Err(err) => {
            eprint!(
                "{}",
                diagnostics::render(&source, path, err.span(), &err.to_string())
            );
            Err(ExitCode::from(1))
        }
    }
}

/// `mettle check <file.als>` — same hand-rolled arg shape as `run_parse`
/// (mt-019). Loads the module graph (root + transitive `open`s, via
/// [`FilesystemLoader`]), then runs the mt-018 resolver/type checker.
/// Warnings print to stderr labeled `warning:` (never fatal — the mt-020
/// gauge is binary ACCEPT/REJECT per resolution-doc §0/§5.3); on ACCEPT a
/// one-line summary prints to stdout.
fn run_check(args: &[String]) -> Result<(), ExitCode> {
    let mut path: Option<&str> = None;
    let mut strict = false;
    for arg in args {
        match arg.as_str() {
            "-h" | "--help" => {
                print_usage();
                return Ok(());
            }
            "--strict" => strict = true,
            other if other.starts_with('-') => {
                eprintln!("mettle check: unknown option `{other}`");
                print_usage();
                return Err(ExitCode::from(2));
            }
            other => {
                if path.replace(other).is_some() {
                    eprintln!("mettle check: expected exactly one input file");
                    print_usage();
                    return Err(ExitCode::from(2));
                }
            }
        }
    }

    let Some(path) = path else {
        eprintln!("mettle check: missing <file.als>");
        print_usage();
        return Err(ExitCode::from(2));
    };

    // Read the root ourselves (rather than letting `ModuleGraph::load` do
    // it): on a load-phase failure whose span lands in the root file we
    // still have its (path, source) in hand to render a caret with, same as
    // `run_parse`'s precedent.
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("mettle check: cannot read {path}: {e}");
            return Err(ExitCode::from(2));
        }
    };

    let loader = FilesystemLoader::new();
    let graph = match ModuleGraph::load_with_source(path, source.clone(), &loader) {
        Ok(graph) => graph,
        Err(err) => {
            render_load_error(path, &source, &err);
            return Err(ExitCode::from(1));
        }
    };

    match als_types::resolve(&graph) {
        Ok(resolved) => {
            // Post-load, every span (errors and warnings alike) names a file
            // that is genuinely in `graph.files` -- `resolve` only ever
            // walks the already-loaded graph, so this lookup can't miss.
            for warning in &resolved.warnings {
                let file = graph.files.file(warning.span().file);
                eprint!(
                    "{}",
                    diagnostics::render_label(
                        &file.source,
                        &file.path,
                        warning.span(),
                        "warning",
                        &diagnostics::warning_message(warning)
                    )
                );
            }
            let n_sigs = resolved
                .world
                .sigs
                .iter()
                .filter(|(_, sig)| !sig.is_builtin)
                .count();
            let n_funcs = resolved.world.funcs.len();
            let n_warnings = resolved.warnings.len();
            // `--strict` promotes any warning to a failing exit (the accept
            // verdict itself is unchanged — resolution-doc §5.3 / LEDGER-002).
            if strict && n_warnings > 0 {
                write_stdout(format!(
                    "{path}: FAILED (strict): {n_warnings} warning(s) \
                     ({n_sigs} sigs, {n_funcs} funcs)\n"
                ))?;
                return Err(ExitCode::from(1));
            }
            write_stdout(format!(
                "{path}: ok ({n_sigs} sigs, {n_funcs} funcs, {n_warnings} warnings)\n"
            ))
        }
        Err(err) => {
            let file = graph.files.file(err.span().file);
            eprint!(
                "{}",
                diagnostics::render_error(&file.source, &file.path, &err)
            );
            Err(ExitCode::from(1))
        }
    }
}

/// Renders a [`ResolveError`] raised while *loading* the module graph (before
/// any [`als_types::ModuleGraph`] exists to look a `FileId` up in). This is
/// the one genuinely multi-file-tricky spot (mt-019): the failing load
/// returns only the error value, not the partially-built file table, so the
/// source text for a non-root file is not generally recoverable through the
/// `als-types` API. Two things save most real cases:
///
/// - `OpenedFileParse` always carries the offending file's `path` outright
///   (independent of any table), so its source can be re-read from disk
///   (matching what `FilesystemLoader` itself would have read) even though
///   the graph never got far enough to cache it.
/// - The root file is always `FileId` index 0 by construction (it's the
///   first file interned, before any `open` is processed) and the CLI
///   already holds its `(path, source)` from its own read above -- so any
///   error whose span lands in the root (the common case: a bad `open` in
///   the root itself, or the root failing to parse) renders precisely.
///
/// Anything else (a module-phase reject -- missing file, cycle, duplicate
/// alias, etc. -- whose span points into a *non-root* file we have no path
/// for) falls back to a spanless one-liner: never a caret guessed into the
/// wrong file, never a panic.
fn render_load_error(root_path: &str, root_source: &str, err: &ResolveError) {
    let is_root = |file: FileId| file == FileId::from_index(0);
    match err {
        ResolveError::OpenedFileParse { path, source, .. } => {
            let inner_span = source.span();
            let normalized_root = als_types::path::normalize(root_path);
            if *path == normalized_root {
                eprint!(
                    "{}",
                    diagnostics::render(root_source, root_path, inner_span, &err.to_string())
                );
            } else if let Ok(text) = std::fs::read_to_string(path) {
                eprint!(
                    "{}",
                    diagnostics::render(&text, path, inner_span, &err.to_string())
                );
            } else {
                eprint!(
                    "{}",
                    diagnostics::render_spanless("error", Some(path), &err.to_string())
                );
            }
        }
        other => {
            let span = other.span();
            if is_root(span.file) {
                eprint!(
                    "{}",
                    diagnostics::render(root_source, root_path, span, &err.to_string())
                );
            } else {
                eprint!(
                    "{}",
                    diagnostics::render_spanless("error", None, &err.to_string())
                );
            }
        }
    }
}
