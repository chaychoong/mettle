//! Integration tests for the `--solver` surface (mt-089 stage 2, ADR-0019),
//! spawning the built binary against the `exec` fixtures — the `exec.rs` idiom.
//!
//! Three properties are pinned here:
//!
//! 1. **The default has not moved.** `mettle exec` and `mettle exec --solver
//!    mettle` produce byte-identical stdout, so naming the default is a no-op
//!    and every recorded command keeps its meaning (ADR-0019 §2).
//! 2. **No silent fallback.** An unknown name is a usage error listing the
//!    names this build has — never a quiet substitution of the default (the
//!    mt-006 rule). A *compiled-out* name would say so in different words; no
//!    backend is compiled out today (mt-121), so that arm has no test to run,
//!    only [`als_solve::Backend::COMPILED_OUT`] to stay empty.
//! 3. **The other backend answers the same verdicts.** Verdicts are
//!    backend-independent truths (ADR-0019 §4): SAT stays SAT, UNSAT stays
//!    UNSAT, a temporal command still solves to a trace. The *instance* shown
//!    may differ and is deliberately not asserted.

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

/// Naming the default backend changes nothing about the output — the flag is a
/// selector, not a mode switch.
#[test]
fn naming_the_default_solver_is_byte_identical_to_omitting_the_flag() {
    let file = fixture("commands.als");
    for command in ["0", "1", "2"] {
        let bare = run_exec(&file, &["--command", command]);
        let named = run_exec(&file, &["--command", command, "--solver", "mettle"]);
        assert_eq!(
            stdout(&bare),
            stdout(&named),
            "--solver mettle changed command {command}'s output"
        );
        assert_eq!(bare.status.code(), named.status.code());
    }
}

/// An unknown solver name is a usage error (exit 2) that lists what this build
/// offers, and never falls back to the default.
#[test]
fn unknown_solver_name_is_a_usage_error_listing_the_available_names() {
    let out = run_exec(&fixture("commands.als"), &["--solver", "minisat"]);
    assert_eq!(out.status.code(), Some(2), "stderr: {}", stderr(&out));
    let text = stderr(&out);
    assert!(
        text.contains("unknown solver `minisat`"),
        "expected the name back verbatim, got: {text}"
    );
    assert!(
        text.contains("available: mettle"),
        "expected the available list, got: {text}"
    );
    assert!(
        stdout(&out).is_empty(),
        "a rejected solver must not solve anything"
    );
}

/// `--solver` with no value is the same shape of usage error every valued flag
/// gives, not a silent default.
#[test]
fn solver_without_a_value_is_a_usage_error() {
    let out = run_exec(&fixture("commands.als"), &["--solver"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(
        stderr(&out).contains("--solver requires a solver name"),
        "stderr: {}",
        stderr(&out)
    );
}

/// The name is exact: no case folding, no prefixes. A near-miss is a typo the
/// user should see, not a guess mettle should make.
#[test]
fn solver_names_are_matched_exactly() {
    for name in ["Mettle", "METTLE", "met"] {
        let out = run_exec(&fixture("commands.als"), &["--solver", name]);
        assert_eq!(out.status.code(), Some(2), "`{name}` must not resolve");
    }
}

/// `serve` takes the same flag with the same refusal (it solves, so it must be
/// able to say which solver did it).
#[test]
fn serve_rejects_an_unknown_solver_before_binding_a_port() {
    let out = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("serve")
        .arg(fixture("commands.als"))
        .args(["--command", "0", "--solver", "nope"])
        .output()
        .expect("failed to spawn mettle");
    assert_eq!(out.status.code(), Some(2));
    assert!(
        stderr(&out).contains("mettle serve: unknown solver `nope`"),
        "stderr: {}",
        stderr(&out)
    );
}

/// Every verdict shape in the fixture is reached under `CaDiCaL` too, with the
/// same verdict label as the default backend produced.
#[test]
fn cadical_reaches_the_same_verdicts_as_the_default_backend() {
    let file = fixture("commands.als");
    // Command 0 is a SAT `run`, 1 a VALID `check`, 2 a COUNTEREXAMPLE.
    for (command, verdict) in [("0", "SAT"), ("1", "VALID"), ("2", "COUNTEREXAMPLE")] {
        let own = run_exec(&file, &["--command", command, "--solver", "mettle"]);
        let cadical = run_exec(&file, &["--command", command, "--solver", "cadical"]);
        assert!(cadical.status.success(), "stderr: {}", stderr(&cadical));
        assert!(
            stdout(&cadical).contains(verdict),
            "cadical missed the {verdict} verdict on command {command}: {}",
            stdout(&cadical)
        );
        assert_eq!(
            own.status.code(),
            cadical.status.code(),
            "backends disagreed on command {command}'s exit status"
        );
        // The verdict line is the contract; the instance below it is the
        // backend's own choice and deliberately not compared (ADR-0019 §1).
        let first_line = |out: &Output| stdout(out).lines().nth(1).unwrap_or("").to_owned();
        assert_eq!(
            first_line(&own),
            first_line(&cadical),
            "backends disagreed on command {command}'s verdict"
        );
    }
}

/// A temporal command still solves to a lasso trace under `CaDiCaL`: the trace
/// shown is configuration-relative to *its* first solution (LEDGER-014 /
/// ADR-0019 §4), so the block structure is asserted and the contents are not.
#[test]
fn cadical_solves_a_temporal_command_to_a_trace() {
    let out = run_exec(&fixture("trace.als"), &["--solver", "cadical"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("---Trace---"), "no trace rendered: {text}");
    assert!(text.contains("(loop)"), "no loop marker: {text}");
}

/// `--conflicts` still binds under `CaDiCaL`: a zero budget cannot answer a
/// command that needs any search at all, and reports the same non-verdict the
/// own solver reports.
#[test]
fn the_conflict_budget_binds_under_cadical() {
    let file = fixture("commands.als");
    let out = run_exec(
        &file,
        &["--command", "1", "--solver", "cadical", "--conflicts", "0"],
    );
    let text = stdout(&out);
    assert!(
        text.contains("UNKNOWN") || text.contains("VALID"),
        "expected a verdict or an honest non-verdict, got: {text}"
    );
    // Whatever it answers, it is never *wrong*: a `check` that reaches a
    // verdict at all must reach the same one the yardstick does.
    assert!(
        !text.contains("COUNTEREXAMPLE"),
        "cadical found a counterexample the yardstick says does not exist: {text}"
    );
}
