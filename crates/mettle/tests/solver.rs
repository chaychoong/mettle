//! Integration tests for the `--solver` surface (mt-089 stage 2, ADR-0019;
//! ADR-0027 decision 2 keeps it as the plugin seam's user surface), spawning the
//! built binary against the `exec` fixtures — the `exec.rs` idiom.
//!
//! Three properties are pinned here:
//!
//! 1. **Naming the default is a no-op.** `mettle exec` and `mettle exec
//!    --solver <the default>` produce byte-identical stdout, so the flag is a
//!    selector rather than a mode switch (ADR-0019 §2). The default itself is
//!    read from the type, not spelled here — mt-121 moved it to `cadical`.
//! 2. **No silent fallback.** An unknown name is a usage error listing the
//!    names this build has — never a quiet substitution of the default (the
//!    mt-006 rule). `mettle`, the own CDCL's name until mt-124 deleted it, is a
//!    live case of that: a script that still asks for it must be told the name
//!    is gone. A *compiled-out* name would say so in different words; nothing is
//!    compiled out today, so that arm has no test to run, only
//!    [`als_solve::Backend::COMPILED_OUT`] to stay empty.
//! 3. **Every backend answers the same verdicts.** Verdicts are
//!    backend-independent truths (ADR-0019 §4): SAT stays SAT, UNSAT stays
//!    UNSAT, a temporal command still solves to a trace. The *instance* shown is
//!    the backend's own and is deliberately not asserted.

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
/// selector, not a mode switch. Read off [`als_solve::Backend::default`] rather
/// than spelled, so this keeps testing the property when the default moves
/// (mt-121 moved it to `cadical`).
#[test]
fn naming_the_default_solver_is_byte_identical_to_omitting_the_flag() {
    let file = fixture("commands.als");
    let default = als_solve::Backend::default().name();
    for command in ["0", "1", "2"] {
        let bare = run_exec(&file, &["--command", command]);
        let named = run_exec(&file, &["--command", command, "--solver", default]);
        assert_eq!(
            stdout(&bare),
            stdout(&named),
            "--solver {default} changed command {command}'s output"
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
        text.contains(&format!(
            "available: {}",
            als_solve::Backend::AVAILABLE.join(", ")
        )),
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
    for name in ["Cadical", "CADICAL", "cad"] {
        let out = run_exec(&fixture("commands.als"), &["--solver", name]);
        assert_eq!(out.status.code(), Some(2), "`{name}` must not resolve");
    }
}

/// `--solver mettle` selected the own CDCL until mt-124 deleted it (ADR-0027
/// decision 3). It must now be refused like any other unknown name, listing what
/// this build does have — never quietly answered by the surviving backend, which
/// would make an old recorded command silently mean something else.
#[test]
fn the_deleted_solver_name_is_refused_like_any_other_unknown() {
    let out = run_exec(&fixture("commands.als"), &["--solver", "mettle"]);
    assert_eq!(out.status.code(), Some(2), "stdout: {}", stdout(&out));
    let text = stderr(&out);
    assert!(
        text.contains("unknown solver `mettle`"),
        "expected the name back verbatim, got: {text}"
    );
    assert!(
        text.contains(&format!(
            "available: {}",
            als_solve::Backend::AVAILABLE.join(", ")
        )),
        "expected the available list, got: {text}"
    );
    assert!(
        stdout(&out).is_empty(),
        "a rejected solver must not solve anything"
    );
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

/// Every verdict shape in the fixture comes out the same under every backend
/// this build offers — the jar-pinned label, and the same exit status.
///
/// The verdict line is the contract; the instance below it is the backend's own
/// choice and deliberately not compared (ADR-0019 §1).
#[test]
fn every_available_solver_reaches_the_same_verdicts() {
    let file = fixture("commands.als");
    // Command 0 is a SAT `run`, 1 a VALID `check`, 2 a COUNTEREXAMPLE.
    for (command, verdict) in [("0", "SAT"), ("1", "VALID"), ("2", "COUNTEREXAMPLE")] {
        let bare = run_exec(&file, &["--command", command]);
        let first_line = |out: &Output| stdout(out).lines().nth(1).unwrap_or("").to_owned();
        for name in als_solve::Backend::AVAILABLE {
            let named = run_exec(&file, &["--command", command, "--solver", name]);
            assert!(named.status.success(), "stderr: {}", stderr(&named));
            assert!(
                stdout(&named).contains(verdict),
                "{name} missed the {verdict} verdict on command {command}: {}",
                stdout(&named)
            );
            assert_eq!(
                bare.status.code(),
                named.status.code(),
                "{name} changed command {command}'s exit status"
            );
            assert_eq!(
                first_line(&bare),
                first_line(&named),
                "{name} changed command {command}'s verdict"
            );
        }
    }
}

/// A temporal command solves to a lasso trace on every backend: the trace shown
/// is configuration-relative to *that* backend's first solution (LEDGER-014 /
/// ADR-0019 §4), so the block structure is asserted and the contents are not.
#[test]
fn every_available_solver_reaches_a_temporal_trace() {
    for name in als_solve::Backend::AVAILABLE {
        let out = run_exec(&fixture("trace.als"), &["--solver", name]);
        assert!(out.status.success(), "stderr: {}", stderr(&out));
        let text = stdout(&out);
        assert!(text.contains("---Trace---"), "{name}: no trace: {text}");
        assert!(text.contains("(loop)"), "{name}: no loop marker: {text}");
    }
}

/// `--conflicts` binds on every backend: a zero budget cannot answer a command
/// that needs any search at all, and the non-answer it reports is never a wrong
/// verdict.
#[test]
fn the_conflict_budget_binds_on_every_available_solver() {
    let file = fixture("commands.als");
    for name in als_solve::Backend::AVAILABLE {
        let out = run_exec(
            &file,
            &["--command", "1", "--solver", name, "--conflicts", "0"],
        );
        let text = stdout(&out);
        assert!(
            text.contains("UNKNOWN") || text.contains("VALID"),
            "{name}: expected a verdict or an honest non-verdict, got: {text}"
        );
        // Whatever it answers, it is never *wrong*: command 1 is a `check` the
        // jar proves has no counterexample.
        assert!(
            !text.contains("COUNTEREXAMPLE"),
            "{name} found a counterexample that does not exist: {text}"
        );
    }
}
