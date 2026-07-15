//! The `mettle` CLI.
//!
//! Rung 1 ships one subcommand, `parse`, the human-testable front end:
//!
//! ```text
//! mettle parse <file.als> [--ast]
//! ```
//!
//! It parses a module and, on success, prints it back as canonical Alloy 6
//! source (or, with `--ast`, the span-free structural dump). Parse/lex
//! errors render to stderr as a rustc-style caret-and-label block (mt-013,
//! [`diagnostics`]) with exit code 1; usage or I/O problems exit with code 2.
//!
//! This crate is the only place that renders diagnostics or touches process
//! exit codes (STYLE E3); `als-syntax` stays print-free.

mod diagnostics;

use std::process::ExitCode;

// `ArenaId` brings `FileId::from_index` into scope.
use als_syntax::{dump, parse, ArenaId as _, FileId};

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
         \n\
         Subcommands:\n\
         \x20\x20parse <file.als>       parse a module and print it back as canonical Alloy 6\n\
         \n\
         Options (parse):\n\
         \x20\x20--ast                  print the span-free structural AST dump instead of source"
    );
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
                print!("{}", dump(&ast));
            } else {
                print!("{}", ast.pretty());
            }
            Ok(())
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
