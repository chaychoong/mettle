//! Running an external **DRAT proof checker** over a certificate
//! ([ADR-0027](../../../docs/adr/0027-cadical-only-solver.md) decision 4,
//! mt-123).
//!
//! The checker is drat-trim (`tools/drat-trim/drat-trim`, built by
//! `scripts/fetch-drat-trim.sh`), and it is deliberately an *external process*:
//! a certificate checked by code that shares mettle's own encoder, solver
//! binding, or assumptions would be checking itself. The only thing this module
//! knows about it is its command line — `<checker> <cnf> <proof>` — and how it
//! reports a verdict.
//!
//! Two rules the rest of the instrument depends on:
//!
//! - **`s VERIFIED` is the only success.** Not exit status alone (upstream
//!   returns 0 for `s VERIFIED` today, but a checker's exit convention is not a
//!   contract mettle should bet a stop-the-line signal on), and not a substring
//!   match anywhere in the output (`c VERIFIED derivation: …` is a progress
//!   line drat-trim prints while still deciding). Both must hold, and the
//!   verdict line must be a line.
//! - **Every run has a deadline.** Proof checking is superlinear in proof size
//!   and the gauge's proofs reach hundreds of megabytes; without a hard kill one
//!   row can eat a whole audit. A deadline is wall-clock and therefore not a
//!   verdict — [`CheckerStatus::Timeout`] is a *non-answer*, exactly like a spent
//!   conflict budget, never a failed certification (STYLE D1/D4).

#![allow(
    clippy::doc_markdown,
    reason = "\"CaDiCaL\" is the solver's own spelling — a proper noun with internal \
              capitals, which doc_markdown mistakes for an unlinked item path"
)]

use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// How long to wait between `try_wait` polls while a check runs. Long enough
/// that polling costs nothing over a ten-minute check, short enough that a fast
/// row does not sit idle waiting to be reaped.
const POLL_INTERVAL: Duration = Duration::from_millis(25);

/// What the checker said about one certificate.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum CheckerStatus {
    /// The proof was verified: the formula really is unsatisfiable.
    Verified,
    /// The checker ran and did **not** verify the proof. Stop the line — a
    /// CaDiCaL UNSAT whose own proof does not check is a solver or binding bug,
    /// not a measurement.
    NotVerified,
    /// The deadline ran out and the checker was killed. Says nothing about the
    /// proof.
    Timeout,
    /// The checker could not be run, or its output could not be read. A broken
    /// instrument, not a finding about the proof — but still a reason to stop,
    /// since an audit that cannot check is not an audit.
    ToolFailure,
}

impl CheckerStatus {
    /// The artifact spelling (upper-case for the two that must never appear in
    /// a clean run, so neither can be skimmed past in a table).
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            CheckerStatus::Verified => "certified",
            CheckerStatus::NotVerified => "NOT_CERTIFIED",
            CheckerStatus::Timeout => "checker_timeout",
            CheckerStatus::ToolFailure => "CHECKER_FAILED",
        }
    }

    /// Whether this status must fail the run. A timeout is the one non-answer
    /// here; the other two are bugs.
    #[must_use]
    pub fn is_fatal(self) -> bool {
        match self {
            CheckerStatus::Verified | CheckerStatus::Timeout => false,
            CheckerStatus::NotVerified | CheckerStatus::ToolFailure => true,
        }
    }
}

/// One checker run: its verdict, what it said, and how long it took.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CheckerReport {
    /// The verdict.
    pub status: CheckerStatus,
    /// The checker's own last word — its `s …` result line, or the failure that
    /// stopped it. Carried so a `NOT_CERTIFIED` row says *what* the checker
    /// found without the reader opening the log.
    pub detail: String,
    /// Wall milliseconds the checker ran. A measurement (STYLE D4).
    pub elapsed_ms: u128,
}

/// Whether `checker` looks like something that can be run, before a run starts.
///
/// Checked up front rather than per row so an audit fails in the first second
/// instead of after the first proof — the same posture the gauge takes toward a
/// missing reference jar.
///
/// # Errors
/// A message naming the fetch script, ready for the CLI to print (STYLE E3
/// keeps the rendering at the caller).
pub fn ensure_usable(checker: &Path) -> Result<(), String> {
    let meta = std::fs::metadata(checker).map_err(|e| {
        format!(
            "no DRAT checker at `{}` ({e}) — build one with scripts/fetch-drat-trim.sh",
            checker.display()
        )
    })?;
    if !meta.is_file() {
        return Err(format!(
            "`{}` is not a file — build a DRAT checker with scripts/fetch-drat-trim.sh",
            checker.display()
        ));
    }
    if !is_executable(&meta) {
        return Err(format!(
            "`{}` is not executable — rebuild it with scripts/fetch-drat-trim.sh",
            checker.display()
        ));
    }
    Ok(())
}

/// Whether a file's mode has any execute bit set.
#[cfg(unix)]
fn is_executable(meta: &std::fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt as _;
    meta.permissions().mode() & 0o111 != 0
}

/// Non-unix targets expose no execute bit; existence is all that can be checked
/// up front, and a genuinely unrunnable checker still surfaces as
/// [`CheckerStatus::ToolFailure`] on the first row.
#[cfg(not(unix))]
fn is_executable(_meta: &std::fs::Metadata) -> bool {
    true
}

/// Runs `<checker> <cnf> <proof>`, writing its output to `log`, and reports
/// whether the proof verified — killing the checker if it outlives `timeout`.
///
/// Output goes to a file rather than a pipe because this function polls for
/// completion instead of blocking on the child: a pipe nobody is draining fills
/// and deadlocks the checker on a chatty proof, and the log is the artifact a
/// failing row wants kept anyway.
///
/// Never returns an error: every way this can go wrong is a
/// [`CheckerStatus`] the report has to show, and a row that vanished into an
/// `Err` would be a certificate silently not checked.
#[must_use]
pub fn verify(
    checker: &Path,
    cnf: &Path,
    proof: &Path,
    log: &Path,
    timeout: Duration,
) -> CheckerReport {
    let started = Instant::now();
    let report = |status, detail: String| CheckerReport {
        status,
        detail,
        elapsed_ms: started.elapsed().as_millis(),
    };

    let sink = match std::fs::File::create(log) {
        Ok(f) => f,
        Err(e) => {
            return report(
                CheckerStatus::ToolFailure,
                format!("cannot create checker log `{}`: {e}", log.display()),
            )
        }
    };
    let errors = match sink.try_clone() {
        Ok(f) => f,
        Err(e) => {
            return report(
                CheckerStatus::ToolFailure,
                format!("cannot open checker log `{}` twice: {e}", log.display()),
            )
        }
    };
    let mut child = match Command::new(checker)
        .arg(cnf)
        .arg(proof)
        .stdin(Stdio::null())
        .stdout(sink)
        .stderr(errors)
        .spawn()
    {
        Ok(child) => child,
        Err(e) => {
            return report(
                CheckerStatus::ToolFailure,
                format!("cannot run `{}`: {e}", checker.display()),
            )
        }
    };

    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {}
            Err(e) => {
                let _ = child.kill();
                return report(
                    CheckerStatus::ToolFailure,
                    format!("waiting on `{}`: {e}", checker.display()),
                );
            }
        }
        if started.elapsed() >= timeout {
            let _ = child.kill();
            // Reaped so the checker cannot outlive the run as a zombie holding
            // the log file open.
            let _ = child.wait();
            return report(
                CheckerStatus::Timeout,
                format!("killed after {}s", timeout.as_secs()),
            );
        }
        std::thread::sleep(POLL_INTERVAL);
    };

    let output = match std::fs::read_to_string(log) {
        Ok(text) => text,
        Err(e) => {
            return report(
                CheckerStatus::ToolFailure,
                format!("cannot read checker log `{}`: {e}", log.display()),
            )
        }
    };
    let said = result_line(&output);
    if status.success() && said.as_deref() == Some("s VERIFIED") {
        report(CheckerStatus::Verified, "s VERIFIED".to_owned())
    } else {
        report(
            CheckerStatus::NotVerified,
            said.unwrap_or_else(|| format!("no `s` result line; exit {status}")),
        )
    }
}

/// The checker's result line — the last line that starts with `s `.
///
/// drat-trim rewrites its progress display with carriage returns, so a
/// "line" here is split on `\r` as well as `\n`; the result line arrives as
/// `\rs VERIFIED\n` and would otherwise be read as part of the progress text
/// glued in front of it.
fn result_line(output: &str) -> Option<String> {
    output
        .split(['\n', '\r'])
        .map(str::trim_end)
        .rfind(|line| line.starts_with("s "))
        .map(str::to_owned)
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "test fixtures assert on known-good values"
)]
mod tests {
    use super::*;

    /// Writes an executable shell script that fakes a checker, and returns its
    /// path. No `tempfile` dependency for a handful of tests (STYLE P1/P2).
    fn fake_checker(stem: &str, body: &str) -> std::path::PathBuf {
        let path = std::env::temp_dir().join(format!("mettle-fake-checker-{stem}.sh"));
        std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("write fake checker");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
                .expect("chmod fake checker");
        }
        path
    }

    /// Runs `checker` against throwaway paths; the fakes ignore their arguments.
    fn run(checker: &Path, secs: u64) -> CheckerReport {
        let dir = std::env::temp_dir();
        let log = dir.join(format!(
            "mettle-fake-checker-{}.log",
            checker.file_stem().unwrap_or_default().to_string_lossy()
        ));
        verify(
            checker,
            &dir.join("nothing.cnf"),
            &dir.join("nothing.drat"),
            &log,
            Duration::from_secs(secs),
        )
    }

    #[test]
    fn a_verified_proof_is_the_only_success() {
        let checker = fake_checker("ok", "printf 'c working\\rs VERIFIED\\n'");
        let report = run(&checker, 30);
        let _ = std::fs::remove_file(&checker);
        assert_eq!(report.status, CheckerStatus::Verified);
        assert!(!report.status.is_fatal());
    }

    #[test]
    fn a_refused_proof_is_fatal_and_says_what_the_checker_said() {
        let checker = fake_checker("bad", "printf '\\ns NOT VERIFIED\\n'; exit 1");
        let report = run(&checker, 30);
        let _ = std::fs::remove_file(&checker);
        assert_eq!(report.status, CheckerStatus::NotVerified);
        assert_eq!(report.detail, "s NOT VERIFIED");
        assert!(report.status.is_fatal());
    }

    /// `s DERIVATION` means drat-trim proved something weaker than a
    /// refutation. Success is one exact line, so this is not it.
    #[test]
    fn a_weaker_result_line_is_not_a_certificate() {
        let checker = fake_checker("deriv", "printf '\\rs DERIVATION\\n'");
        let report = run(&checker, 30);
        let _ = std::fs::remove_file(&checker);
        assert_eq!(report.status, CheckerStatus::NotVerified);
        assert_eq!(report.detail, "s DERIVATION");
    }

    /// The progress line drat-trim prints *while still deciding* contains the
    /// word VERIFIED. A substring match over the whole log would bless a proof
    /// the checker went on to refuse.
    #[test]
    fn the_progress_line_is_not_mistaken_for_the_verdict() {
        let checker = fake_checker(
            "progress",
            "printf 'c VERIFIED derivation: all lemmas preserve satisfiability\\n'; \
             printf '\\ns NOT VERIFIED\\n'; exit 1",
        );
        let report = run(&checker, 30);
        let _ = std::fs::remove_file(&checker);
        assert_eq!(report.status, CheckerStatus::NotVerified);
    }

    /// A checker that says the right words but exits nonzero is not trusted:
    /// both halves of the contract have to hold.
    #[test]
    fn a_failing_exit_status_overrides_the_verdict_line() {
        let checker = fake_checker("liar", "printf 's VERIFIED\\n'; exit 3");
        let report = run(&checker, 30);
        let _ = std::fs::remove_file(&checker);
        assert_eq!(report.status, CheckerStatus::NotVerified);
    }

    /// The deadline really kills: a checker that would run for half an hour is
    /// gone in a second, and reported as a non-answer rather than a refusal.
    #[test]
    fn the_deadline_hard_kills_a_runaway_checker() {
        let checker = fake_checker("slow", "sleep 1800");
        let report = run(&checker, 1);
        let _ = std::fs::remove_file(&checker);
        assert_eq!(report.status, CheckerStatus::Timeout);
        assert!(!report.status.is_fatal(), "a deadline is not a refusal");
    }

    #[test]
    fn a_missing_checker_is_refused_up_front() {
        let missing = std::env::temp_dir().join("mettle-no-such-drat-checker");
        let Err(msg) = ensure_usable(&missing) else {
            panic!("a missing checker must be refused")
        };
        assert!(msg.contains("fetch-drat-trim.sh"), "{msg}");
    }

    #[test]
    fn a_non_executable_checker_is_refused_up_front() {
        let path = std::env::temp_dir().join("mettle-not-executable-checker");
        std::fs::write(&path, "not a program").expect("write file");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).expect("chmod");
            let result = ensure_usable(&path);
            let _ = std::fs::remove_file(&path);
            let Err(msg) = result else {
                panic!("a non-executable checker must be refused")
            };
            assert!(msg.contains("not executable"), "{msg}");
        }
    }

    #[test]
    fn an_unrunnable_checker_is_a_tool_failure_not_a_refusal() {
        let missing = std::env::temp_dir().join("mettle-no-such-drat-checker");
        let report = run(&missing, 30);
        assert_eq!(report.status, CheckerStatus::ToolFailure);
        assert!(report.status.is_fatal());
    }
}
