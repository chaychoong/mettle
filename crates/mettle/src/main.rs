//! The `mettle` CLI.
//!
//! Rung 1 shipped `parse`; Rung 2 adds `check`, the names-and-types
//! human-testable front end:
//!
//! ```text
//! mettle parse <file.als> [--ast]
//! mettle check <file.als>
//! ```
//!
//! `parse` parses a module and, on success, prints it back as canonical
//! Alloy 6 source (or, with `--ast`, the span-free structural dump).
//! `check` additionally loads the module graph (`open`s and all) and runs
//! the mt-018 resolver/type checker, printing any warnings and a one-line
//! success summary. Parse/lex/resolve errors render to stderr as a
//! rustc-style caret-and-label block (mt-013, [`diagnostics`]) with exit
//! code 1; usage or I/O problems exit with code 2.
//!
//! This crate is the only place that renders diagnostics or touches process
//! exit codes (STYLE E3); `als-syntax`/`als-types` stay print-free.

mod diagnostics;

use std::io::{self, Write as _};
use std::process::ExitCode;

// `ArenaId` brings `FileId::from_index` into scope.
use als_syntax::{dump, parse, ArenaId as _, FileId};
use als_types::{FilesystemLoader, ModuleGraph, ResolveError};

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
    eprintln!(
        "usage: mettle parse <file.als> [--ast]\n\
         \x20\x20\x20\x20\x20mettle check <file.als>\n\
         \n\
         Subcommands:\n\
         \x20\x20parse <file.als>       parse a module and print it back as canonical Alloy 6\n\
         \x20\x20check <file.als>       load, resolve, and type-check a module (and its opens)\n\
         \n\
         Options (parse):\n\
         \x20\x20--ast                  print the span-free structural AST dump instead of source"
    );
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
    for arg in args {
        match arg.as_str() {
            "-h" | "--help" => {
                print_usage();
                return Ok(());
            }
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
            write_stdout(format!(
                "{path}: ok ({n_sigs} sigs, {n_funcs} funcs, {n_warnings} warnings)\n"
            ))
        }
        Err(err) => {
            let file = graph.files.file(err.span().file);
            eprint!(
                "{}",
                diagnostics::render(&file.source, &file.path, err.span(), &err.to_string())
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
