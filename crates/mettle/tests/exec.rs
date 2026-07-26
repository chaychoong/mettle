//! Integration tests for `mettle exec` (mt-036), spawning the built binary
//! (`env!("CARGO_BIN_EXE_mettle")`, the `check.rs` idiom) against
//! `tests/fixtures/exec/commands.als` — one small model whose four commands
//! cover every verdict shape: SAT `run`, VALID `check`, a `check` with a
//! COUNTEREXAMPLE, and `expect` both matching and mismatching.
//!
//! Five more fixtures cover the Rung-6 surface: `temporal.als` solves to the
//! degenerate one-state trace, `trace.als` (mt-064's own probe model) and
//! `trace_alt.als` pin the state-by-state **trace rendering** of mt-068 —
//! including where the `(loop)` marker sits and that rigid content repeats in
//! every block — `temporal_check.als` covers the bound-relative `check` and the
//! two typed temporal defers, and `static_steps.als` the
//! `steps`-on-a-static-model reject.

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

/// (e) A temporal model (`var sig` + `'`) **solves** since mt-067, and since
/// mt-068 renders as a trace: the degenerate case is one state that loops onto
/// itself, and it still gets the full `---Trace---` framing (the reference's
/// `toString(-1)` has no special case for `traceLength == 1` either —
/// alloy6-temporal.md §(f), probe T-14).
#[test]
fn temporal_model_solves_and_renders_its_trace() {
    let file = fixture("temporal.als");
    let out = run_exec(&file, &[]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("[0] run p"), "{text}");
    // `A' = A` is satisfied by the minimal, self-looping single-state trace.
    assert_eq!(
        trace_shape(&text),
        vec![
            "SAT",
            "---Trace---",
            "------State 0 (loop)-------",
            "  this/A = {}"
        ],
        "{text}"
    );
}

/// The verdict line, the state headers, and the user-sig lines of a rendered
/// trace — everything but the builtin relations, which are identical in every
/// block of every model and would bury the shape being asserted.
fn trace_shape(text: &str) -> Vec<&str> {
    text.lines()
        .filter(|line| {
            line.starts_with("---")
                || line.starts_with("------State")
                || line.starts_with("  this/")
                || matches!(*line, "SAT" | "COUNTEREXAMPLE")
        })
        .collect()
}

/// (e5) The pinned trace shape (alloy6-temporal.md §(f), source-pinned at
/// `A4Solution.java:1767-1816` and jar-captured as probe T-13): a `---Trace---`
/// header, then one `------State N-------` block per state with `(loop)` on the
/// back-loop target, each block listing **every** relation at that state.
///
/// The fixture is T-13's own model, so the *values* below are the jar's
/// captured trace, reproduced here without a jar: state0 = (no A, no B),
/// state1 = (A, no B), state2 = (no A, B), looping on state 2.
#[test]
fn a_forced_trace_renders_state_by_state_with_the_loop_marked() {
    let out = run_exec(&fixture("trace.als"), &[]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert_eq!(
        trace_shape(&text),
        vec![
            "COUNTEREXAMPLE",
            "---Trace---",
            "------State 0-------",
            "  this/Counter = {Counter$0}",
            "  this/A = {}",
            "  this/B = {}",
            "------State 1-------",
            "  this/Counter = {Counter$0}",
            "  this/A = {Counter$0}",
            "  this/B = {}",
            "------State 2 (loop)-------",
            "  this/Counter = {Counter$0}",
            "  this/A = {}",
            "  this/B = {Counter$0}",
        ],
        "{text}"
    );
}

/// (e6) The `(loop)` marker sits on the state the trace returns to, wherever
/// that is: `trace.als` above loops onto its *last* state, this fixture's
/// alternation forces a loop back to state **0**.
#[test]
fn the_loop_marker_follows_the_back_loop_target() {
    let out = run_exec(&fixture("trace_alt.als"), &[]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("------State 0 (loop)-------"), "{text}");
    assert!(text.contains("------State 1-------"), "{text}");
    assert!(!text.contains("------State 1 (loop)"), "{text}");
    assert_eq!(
        text.matches("(loop)").count(),
        1,
        "exactly one state is the loop target: {text}"
    );
}

/// (e7) Rigid content is **re-emitted in full in every state block**, never
/// factored out (alloy6-temporal.md §(f), probe T-13: non-`var` sigs and all
/// four builtins appear byte-identically in each block).
#[test]
fn rigid_relations_are_re_emitted_in_every_state_block() {
    let out = run_exec(&fixture("trace_alt.als"), &[]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    let blocks: Vec<&str> = text.split("------State ").skip(1).collect();
    assert_eq!(blocks.len(), 2, "{text}");
    for rigid in [
        "  this/Rigid = {Rigid$0, Rigid$1}\n",
        "  Int/zero = {0}\n",
        "  seq/Int = {0, 1, 2, 3}\n",
    ] {
        assert!(
            blocks.iter().all(|block| block.contains(rigid)),
            "`{rigid}` missing from a state block: {text}"
        );
    }
    // ...while the `var` sig genuinely differs between them.
    assert!(blocks[0].contains("  this/A = {}\n"), "{text}");
    assert!(blocks[1].contains("  this/A = {A$0}\n"), "{text}");
}

/// (e2) A temporal `check` that finds nothing says so **bound-relatively** —
/// "within N steps", never "the assertion holds" (alloy6-temporal.md §(c)).
#[test]
fn a_temporal_check_reports_unsat_within_the_steps_bound() {
    let file = fixture("temporal_check.als");
    let out = run_exec(&file, &["--command", "0"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(
        text.contains("VALID (no counterexample within 4 steps)"),
        "{text}"
    );
    assert!(
        text.contains("4 steps"),
        "the scope line names the bound: {text}"
    );
}

/// (e3) The two Rung-6 typed defers still print `CANNOT EXECUTE` and exit 1 —
/// an unbounded `steps` range (the jar's own engine rejection) and a `check` at
/// a one-state bound (the pinned jar `NullPointerException`).
#[test]
fn temporal_defers_are_typed_and_fail_the_run() {
    let out = run_exec(&fixture("temporal_check.als"), &["--command", "1"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stdout(&out).contains("Bounded engines do not support complete model checking."),
        "{}",
        stdout(&out)
    );

    let out = run_exec(&fixture("temporal_check.als"), &["--command", "2"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stdout(&out).contains("NullPointerException"),
        "{}",
        stdout(&out)
    );
}

/// (e4) A `steps` scope on a **static** model is the jar's own reject, verbatim
/// (probe T-03).
#[test]
fn steps_on_a_static_model_cannot_execute() {
    let out = run_exec(&fixture("static_steps.als"), &[]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", stderr(&out));
    assert!(
        stdout(&out).contains("You cannot set a scope on \"steps\" in static models."),
        "{}",
        stdout(&out)
    );
}

/// (e8) `--state` names a place in a *trace*, so asking for one where there is
/// none is a usage error rather than a silent "you got state 0" (mt-068).
#[test]
fn a_state_index_without_a_trace_is_a_usage_error() {
    // A plain run prints every state already.
    let out = run_exec(&fixture("trace.als"), &["--state", "1"]);
    assert_eq!(out.status.code(), Some(2), "stdout: {}", stdout(&out));
    assert!(
        stderr(&out).contains("--state applies to --repl/--eval"),
        "{}",
        stderr(&out)
    );
    assert_eq!(stdout(&out), "");

    // A static command's instance is a single state.
    let out = run_exec(
        &fixture("commands.als"),
        &["--command", "0", "--state", "1", "--eval", "A"],
    );
    assert_eq!(out.status.code(), Some(2), "stdout: {}", stdout(&out));
    assert!(
        stderr(&out).contains("not temporal, so its instance has a single state"),
        "{}",
        stderr(&out)
    );
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
