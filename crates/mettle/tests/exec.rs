//! Integration tests for `mettle exec` (mt-036), spawning the built binary
//! (`env!("CARGO_BIN_EXE_mettle")`, the `check.rs` idiom) against
//! `tests/fixtures/exec/commands.als` — one small model whose four commands
//! cover every verdict shape: SAT `run`, VALID `check`, a `check` with a
//! COUNTEREXAMPLE, and `expect` both matching and mismatching. A second
//! fixture (`temporal.als`) exercises the honest `CANNOT EXECUTE` defer.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/exec")
        .join(name)
}

fn run_exec(file: &Path, extra_args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("exec")
        .arg(file)
        .args(extra_args)
        .output()
        .expect("failed to spawn mettle")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// (a) A SAT `run` renders `SAT`, a known relation line, and `expect 1: ok`.
/// The whole default run also mismatches command 3's `expect 0` (see (d)),
/// so the full-file exit code is 1 -- this test targets command 0 alone via
/// `--command` to isolate the SAT case.
#[test]
fn sat_run_renders_verdict_and_instance() {
    let file = fixture("commands.als");
    let out = run_exec(&file, &["--command", "0"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("[0] run p"), "{text}");
    assert!(text.contains("SAT"), "{text}");
    // The instance carries a nonempty `A` relation (some atom, `A$`-named).
    assert!(text.contains("A = {A$"), "{text}");
    assert!(text.contains("expect 1: ok"), "{text}");
    assert_eq!(stderr(&out), "");
}

/// (b) A `check` that holds within scope: `VALID (no counterexample)`.
#[test]
fn valid_check_reports_no_counterexample() {
    let file = fixture("commands.als");
    let out = run_exec(&file, &["--command", "1"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("[1] check AlwaysTrue"), "{text}");
    assert!(text.contains("VALID (no counterexample)"), "{text}");
    assert!(text.contains("expect 0: ok"), "{text}");
}

/// (c) A `check` that fails within scope: `COUNTEREXAMPLE` + the witnessing
/// instance. Command 2 has no `expect`, so this alone exits 0.
#[test]
fn failing_check_renders_counterexample() {
    let file = fixture("commands.als");
    let out = run_exec(&file, &["--command", "2"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("[2] check Bogus"), "{text}");
    assert!(text.contains("COUNTEREXAMPLE"), "{text}");
    assert!(text.contains("A = {A$"), "{text}");
    assert!(!text.contains("expect"), "{text}");
}

/// (d) `expect` mismatch: command 3 is identical to command 2 but declares
/// `expect 0` (no counterexample expected); since one is found, this must
/// render `MISMATCH` and exit 1.
#[test]
fn expect_mismatch_fails_the_run() {
    let file = fixture("commands.als");
    let out = run_exec(&file, &["--command", "3"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("expect 0: MISMATCH (got SAT)"), "{text}");
}

/// Running the whole file (no `--command`) executes every root command in
/// source order and fails overall because of command 3's mismatch, even
/// though commands 0-2 are individually fine.
#[test]
fn default_run_executes_every_command_and_propagates_the_one_failure() {
    let file = fixture("commands.als");
    let out = run_exec(&file, &[]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("[0] run p"), "{text}");
    assert!(text.contains("[1] check AlwaysTrue"), "{text}");
    assert!(text.contains("[2] check Bogus"), "{text}");
    assert!(text.contains("[3] check Bogus"), "{text}");
    assert!(text.contains("expect 1: ok"), "{text}");
    assert!(text.contains("expect 0: ok"), "{text}");
    assert!(text.contains("expect 0: MISMATCH (got SAT)"), "{text}");
}

/// (e) A temporal model (`var sig` + `'`) is an honest, typed defer: every
/// command prints `CANNOT EXECUTE` with the `TranslateError`'s message, and
/// the process exits 1 -- never a wrong verdict (STYLE E5).
#[test]
fn temporal_model_cannot_execute() {
    let file = fixture("temporal.als");
    let out = run_exec(&file, &[]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("CANNOT EXECUTE"), "{text}");
    assert!(text.contains("temporal"), "{text}");
}

/// (f) `--command` selection by index and by name, plus the no-match error
/// (exit 2, listing every available command).
#[test]
fn command_selection_by_index_and_by_name() {
    let file = fixture("commands.als");

    let by_index = run_exec(&file, &["--command", "1"]);
    assert!(by_index.status.success(), "stderr: {}", stderr(&by_index));
    assert!(stdout(&by_index).contains("[1] check AlwaysTrue"));

    let by_name = run_exec(&file, &["--command", "AlwaysTrue"]);
    assert!(by_name.status.success(), "stderr: {}", stderr(&by_name));
    assert!(stdout(&by_name).contains("[1] check AlwaysTrue"));
    // Selecting by index or by name for the same command produces the exact
    // same stdout.
    assert_eq!(stdout(&by_index), stdout(&by_name));

    let by_pred_name = run_exec(&file, &["--command", "p"]);
    assert!(
        by_pred_name.status.success(),
        "stderr: {}",
        stderr(&by_pred_name)
    );
    assert!(stdout(&by_pred_name).contains("[0] run p"));
}

#[test]
fn command_selection_no_match_exits_two_and_lists_commands() {
    let file = fixture("commands.als");
    let out = run_exec(&file, &["--command", "nonexistent"]);
    assert_eq!(out.status.code(), Some(2));
    let err = stderr(&out);
    assert!(err.contains("no command matches `nonexistent`"), "{err}");
    assert!(err.contains("available commands:"), "{err}");
    assert!(err.contains("[0] run p"), "{err}");
    assert!(err.contains("[3] check Bogus"), "{err}");
    assert_eq!(stdout(&out), "");
}

/// (g) Determinism: the same command run twice produces byte-identical
/// stdout (STYLE D1 -- no `HashMap` iteration, no wall-clock, fixed solver
/// decision order).
#[test]
fn sat_run_is_deterministic_across_invocations() {
    let file = fixture("commands.als");
    let first = run_exec(&file, &["--command", "0"]);
    let second = run_exec(&file, &["--command", "0"]);
    assert!(first.status.success(), "stderr: {}", stderr(&first));
    assert!(second.status.success(), "stderr: {}", stderr(&second));
    assert_eq!(stdout(&first), stdout(&second));
}

#[test]
fn unknown_command_selector_lists_available_commands_even_when_numeric_out_of_range() {
    let file = fixture("commands.als");
    let out = run_exec(&file, &["--command", "99"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(
        stderr(&out).contains("no command at index 99"),
        "{}",
        stderr(&out)
    );
}

#[test]
fn unknown_option_exits_two() {
    let file = fixture("commands.als");
    let out = run_exec(&file, &["--bogus"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr(&out).contains("unknown option"));
}

#[test]
fn missing_file_exits_two() {
    let file = fixture("does_not_exist.als");
    let out = run_exec(&file, &[]);
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr(&out).contains("cannot read"));
}
