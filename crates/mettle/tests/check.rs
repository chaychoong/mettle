//! Integration tests for `mettle check` (mt-019), spawning the built binary
//! (`env!("CARGO_BIN_EXE_mettle")`, the standard cargo pattern) against
//! checked-in fixtures under `tests/fixtures/check/`. This exercises the
//! actual CLI surface (arg parsing, exit codes, rendered diagnostics) rather
//! than any library-internal helper, since diagnostics rendering is CLI-only
//! (STYLE E3) and there is nothing else to call into.
//!
//! The one subtle thing under test is multi-file diagnostics: a resolve
//! error whose span lands in a transitively-`open`ed file must render with
//! *that* file's path and source, not the root's (see `root_opens_sub` /
//! `submodule_error_points_into_submodule`).

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/check")
        .join(name)
}

fn run_check(file: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("check")
        .arg(file)
        .output()
        .expect("failed to spawn mettle")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

#[test]
fn good_model_exits_zero_with_a_summary_line() {
    let file = fixture("good.als");
    let out = run_check(&file);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains(&file.display().to_string()), "{text}");
    assert!(text.contains(": ok ("), "{text}");
    // 2 declared sigs (A, B); util/integer's funcs are auto-opened so the
    // func count is nonzero but its exact value is an als-types stdlib
    // implementation detail this test does not pin.
    assert!(text.contains("2 sigs"), "{text}");
    assert!(text.contains("0 warnings"), "{text}");
    assert_eq!(stderr(&out), "");
}

#[test]
fn root_type_error_renders_a_caret_at_the_root() {
    let file = fixture("root_type_error.als");
    let out = run_check(&file);
    assert_eq!(out.status.code(), Some(1));
    let err = stderr(&out);
    assert!(
        err.starts_with("error: the name `Bogus` cannot be found"),
        "{err}"
    );
    assert!(
        err.contains(&format!("--> {}:2:15", file.display())),
        "{err}"
    );
    assert!(err.contains("^^^^^"), "{err}");
    assert_eq!(stdout(&out), "");
}

#[test]
fn submodule_error_points_into_submodule_not_root() {
    let root = fixture("root_opens_sub.als");
    let sub = fixture("sub_error.als");
    let out = run_check(&root);
    assert_eq!(out.status.code(), Some(1));
    let err = stderr(&out);
    assert!(err.contains("the name `Bogus2` cannot be found"), "{err}");
    // The caret location names the submodule's path and line, not the root's.
    assert!(
        err.contains(&format!("--> {}:2:15", sub.display())),
        "{err}"
    );
    assert!(!err.contains(&root.display().to_string()), "{err}");
    assert_eq!(stdout(&out), "");
}

#[test]
fn missing_root_file_exits_two() {
    let file = fixture("does_not_exist.als");
    let out = run_check(&file);
    assert_eq!(out.status.code(), Some(2));
    let err = stderr(&out);
    assert!(err.contains("cannot read"), "{err}");
    assert_eq!(stdout(&out), "");
}

#[test]
fn root_parse_error_exits_one_with_a_caret() {
    let file = fixture("parse_error.als");
    let out = run_check(&file);
    assert_eq!(out.status.code(), Some(1));
    let err = stderr(&out);
    assert!(err.starts_with("error:"), "{err}");
    assert!(err.contains(&file.display().to_string()), "{err}");
    assert_eq!(stdout(&out), "");
}

#[test]
fn warnings_print_but_do_not_fail_the_check() {
    let file = fixture("warn.als");
    let out = run_check(&file);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let err = stderr(&out);
    assert!(
        err.starts_with("warning: variable `x` is never used"),
        "{err}"
    );
    let text = stdout(&out);
    assert!(text.contains("1 warnings"), "{text}");
}

#[test]
fn missing_open_target_reports_at_the_open_directive() {
    let file = fixture("root_missing_open.als");
    let out = run_check(&file);
    assert_eq!(out.status.code(), Some(1));
    let err = stderr(&out);
    assert!(
        err.contains("module file for `nonexistent_module_xyz` cannot be found"),
        "{err}"
    );
    assert!(
        err.contains(&format!("--> {}:1:1", file.display())),
        "{err}"
    );
}

/// The one genuinely hard case: a **load-phase** parse failure (before any
/// `ModuleGraph` exists) in a **non-root**, transitively-`open`ed file. The
/// failing load returns only the `ResolveError` value, not the partial file
/// table, so the CLI's fallback (re-read the file from disk by the path the
/// error itself carries) is what makes this render correctly instead of
/// falling back to a spanless message.
#[test]
fn submodule_parse_error_falls_back_to_a_disk_reread() {
    let root = fixture("root_opens_bad_sub.als");
    let sub = fixture("sub_parse_error.als");
    let out = run_check(&root);
    assert_eq!(out.status.code(), Some(1));
    let err = stderr(&out);
    assert!(err.contains("could not parse opened module"), "{err}");
    assert!(err.contains(&sub.display().to_string()), "{err}");
    // A real caret block, not the spanless fallback -- proves the disk
    // re-read succeeded and did not have to give up.
    assert!(err.contains('^'), "{err}");
}

#[test]
fn unknown_option_exits_two() {
    let out = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .args(["check", "--bogus"])
        .output()
        .expect("failed to spawn mettle");
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr(&out).contains("unknown option"));
}

#[test]
fn missing_argument_exits_two() {
    let out = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("check")
        .output()
        .expect("failed to spawn mettle");
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr(&out).contains("missing <file.als>"));
}

#[test]
fn parse_subcommand_is_unchanged_by_check() {
    let file = fixture("good.als");
    let out = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("parse")
        .arg(&file)
        .output()
        .expect("failed to spawn mettle");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert!(stdout(&out).contains("sig A"), "{}", stdout(&out));
}
