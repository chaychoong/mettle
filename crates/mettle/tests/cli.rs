//! Top-level CLI dispatch (mt-073): `-V`/`--version`, exercised end-to-end
//! against the built binary (`env!("CARGO_BIN_EXE_mettle")`), same pattern
//! as `check.rs`/`exec.rs`. This is the one piece of `mettle`'s surface with
//! no subcommand and no fixture to drive it through, so it gets its own
//! (tiny) file rather than being wedged into an existing one.

use std::process::{Command, Output};

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_mettle"))
        .args(args)
        .output()
        .expect("failed to spawn mettle")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn dash_capital_v_prints_the_cargo_package_version_and_exits_zero() {
    let out = run(&["-V"]);
    assert!(out.status.success());
    assert_eq!(
        stdout(&out),
        format!("mettle {}\n", env!("CARGO_PKG_VERSION"))
    );
}

#[test]
fn dash_dash_version_matches_dash_capital_v() {
    let short = run(&["-V"]);
    let long = run(&["--version"]);
    assert!(long.status.success());
    assert_eq!(stdout(&short), stdout(&long));
}
