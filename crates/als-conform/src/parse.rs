//! Parses `OracleShim`'s JSON-Lines stdout protocol into typed
//! [`FileOutcome`]s. Pure string-in, value-out -- no process spawning, no
//! I/O -- so it is unit-tested against fixture strings without the jar
//! (this bead's requirement 3).

use serde::Deserialize;

use crate::model::{CommandResult, FileOutcome, Outcome, ShimErrorKind};

#[derive(Debug, Deserialize)]
struct RawShimError {
    kind: String,
    message: String,
}

#[derive(Debug, Deserialize)]
struct RawCommand {
    index: usize,
    label: String,
    check: bool,
    expects: i32,
    #[serde(default)]
    verdict: Option<String>,
    #[serde(default)]
    instance_count: Option<u32>,
    #[serde(default)]
    error: Option<RawShimError>,
}

/// One line of `OracleShim`'s stdout: either a per-command result (has
/// `index`) or a whole-file error envelope (has only `error`). Untagged:
/// serde picks `Command` when the required fields (`index`, `label`,
/// `check`, `expects`) are present, and falls back to `FileError`
/// otherwise -- the two shapes are structurally disjoint by construction.
#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum ShimLine {
    Command(RawCommand),
    FileError { error: RawShimError },
}

fn parse_kind(raw: &str) -> ShimErrorKind {
    match raw {
        "parse" => ShimErrorKind::Parse,
        "command" => ShimErrorKind::Command,
        "usage" => ShimErrorKind::Usage,
        _ => ShimErrorKind::Protocol,
    }
}

/// Converts one already-deserialized shim line into a typed
/// [`CommandResult`], or an `(kind, message)` protocol-error pair if the
/// line's fields don't make sense (e.g. `expects` outside `-1..=1`, or an
/// unrecognized `verdict` string). Malformed content, not malformed JSON,
/// so this is a value-returning failure rather than a parse error.
fn to_command_result(raw: RawCommand) -> Result<CommandResult, (ShimErrorKind, String)> {
    let expects = match raw.expects {
        -1 => None,
        0 => Some(false),
        1 => Some(true),
        other => {
            return Err((
                ShimErrorKind::Protocol,
                format!("command {}: unexpected expects value {other}", raw.index),
            ))
        }
    };

    let outcome = if let Some(err) = raw.error {
        Outcome::Error {
            kind: parse_kind(&err.kind),
            message: err.message,
        }
    } else {
        match raw.verdict.as_deref() {
            Some("SAT") => Outcome::Sat {
                instance_count: raw.instance_count,
            },
            Some("UNSAT") => Outcome::Unsat {
                instance_count: raw.instance_count,
            },
            other => {
                return Err((
                    ShimErrorKind::Protocol,
                    format!("command {}: unexpected verdict {other:?}", raw.index),
                ))
            }
        }
    };

    Ok(CommandResult {
        index: raw.index,
        label: raw.label,
        check: raw.check,
        expects,
        outcome,
    })
}

/// Parses the full captured stdout of one `OracleShim` run into a
/// [`FileOutcome`]. Never panics: any line that isn't valid JSON, or is
/// valid JSON but doesn't match the protocol, becomes
/// `FileOutcome::Error { kind: Protocol, .. }` rather than propagating a
/// parse exception (STYLE E2/E3 -- this crate is a library, it returns
/// values).
pub(crate) fn parse_shim_output(stdout: &str) -> FileOutcome {
    let mut commands = Vec::new();
    for line in stdout.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        match serde_json::from_str::<ShimLine>(line) {
            Ok(ShimLine::FileError { error }) => {
                return FileOutcome::Error {
                    kind: parse_kind(&error.kind),
                    message: error.message,
                };
            }
            Ok(ShimLine::Command(raw)) => match to_command_result(raw) {
                Ok(cr) => commands.push(cr),
                Err((kind, message)) => return FileOutcome::Error { kind, message },
            },
            Err(e) => {
                return FileOutcome::Error {
                    kind: ShimErrorKind::Protocol,
                    message: format!("malformed shim output line ({e}): {line}"),
                };
            }
        }
    }
    if commands.is_empty() {
        return FileOutcome::Error {
            kind: ShimErrorKind::Protocol,
            message: "shim produced no output".to_string(),
        };
    }
    FileOutcome::Commands(commands)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_verdict_only_commands() {
        let stdout = concat!(
            "{\"index\":0,\"label\":\"show\",\"check\":false,\"expects\":-1,\"verdict\":\"SAT\",\"instance_count\":null}\n",
            "{\"index\":1,\"label\":\"NoEmpty\",\"check\":true,\"expects\":-1,\"verdict\":\"SAT\",\"instance_count\":null}\n",
        );
        let outcome = parse_shim_output(stdout);
        let FileOutcome::Commands(cmds) = outcome else {
            panic!("expected Commands, got {outcome:?}")
        };
        assert_eq!(cmds.len(), 2);
        assert_eq!(cmds[0].index, 0);
        assert_eq!(cmds[0].label, "show");
        assert!(!cmds[0].check);
        assert_eq!(cmds[0].expects, None);
        assert_eq!(
            cmds[0].outcome,
            Outcome::Sat {
                instance_count: None
            }
        );
        assert!(cmds[1].check);
    }

    #[test]
    fn parses_enumeration_counts() {
        let stdout = "{\"index\":0,\"label\":\"show\",\"check\":false,\"expects\":-1,\"verdict\":\"SAT\",\"instance_count\":87}\n";
        let FileOutcome::Commands(cmds) = parse_shim_output(stdout) else {
            panic!("expected Commands")
        };
        assert_eq!(
            cmds[0].outcome,
            Outcome::Sat {
                instance_count: Some(87)
            }
        );
    }

    #[test]
    fn maps_expects_sentinel_to_option() {
        let stdout = concat!(
            "{\"index\":0,\"label\":\"impossible\",\"check\":false,\"expects\":0,\"verdict\":\"UNSAT\",\"instance_count\":null}\n",
            "{\"index\":1,\"label\":\"possible\",\"check\":false,\"expects\":1,\"verdict\":\"SAT\",\"instance_count\":null}\n",
            "{\"index\":2,\"label\":\"possible\",\"check\":false,\"expects\":0,\"verdict\":\"SAT\",\"instance_count\":null}\n",
        );
        let FileOutcome::Commands(cmds) = parse_shim_output(stdout) else {
            panic!("expected Commands")
        };
        assert_eq!(cmds[0].expects, Some(false));
        assert!(!cmds[0].outcome.is_sat());
        assert_eq!(cmds[1].expects, Some(true));
        assert!(cmds[1].outcome.is_sat());
        // deliberately-wrong-expectation case: expects UNSAT but is SAT.
        assert_eq!(cmds[2].expects, Some(false));
        assert!(cmds[2].outcome.is_sat());
    }

    #[test]
    fn parses_per_command_error() {
        let stdout = "{\"index\":0,\"label\":\"broken\",\"check\":false,\"expects\":-1,\"error\":{\"kind\":\"command\",\"message\":\"boom\"}}\n";
        let FileOutcome::Commands(cmds) = parse_shim_output(stdout) else {
            panic!("expected Commands")
        };
        assert_eq!(
            cmds[0].outcome,
            Outcome::Error {
                kind: ShimErrorKind::Command,
                message: "boom".to_string()
            }
        );
    }

    #[test]
    fn parses_file_level_parse_error() {
        let stdout = "{\"error\":{\"kind\":\"parse\",\"message\":\"File cannot be found.\"}}\n";
        let outcome = parse_shim_output(stdout);
        assert_eq!(
            outcome,
            FileOutcome::Error {
                kind: ShimErrorKind::Parse,
                message: "File cannot be found.".to_string()
            }
        );
    }

    #[test]
    fn rejects_malformed_json_as_protocol_error() {
        let outcome = parse_shim_output("not json at all\n");
        let FileOutcome::Error { kind, .. } = outcome else {
            panic!("expected Error, got {outcome:?}")
        };
        assert_eq!(kind, ShimErrorKind::Protocol);
    }

    #[test]
    fn empty_output_is_a_protocol_error() {
        let outcome = parse_shim_output("");
        let FileOutcome::Error { kind, .. } = outcome else {
            panic!("expected Error, got {outcome:?}")
        };
        assert_eq!(kind, ShimErrorKind::Protocol);
    }

    #[test]
    fn rejects_out_of_range_expects_as_protocol_error() {
        let stdout = "{\"index\":0,\"label\":\"x\",\"check\":false,\"expects\":5,\"verdict\":\"SAT\",\"instance_count\":null}\n";
        let outcome = parse_shim_output(stdout);
        let FileOutcome::Error { kind, .. } = outcome else {
            panic!("expected Error, got {outcome:?}")
        };
        assert_eq!(kind, ShimErrorKind::Protocol);
    }

    #[test]
    fn ignores_blank_lines() {
        let stdout = "\n\n{\"index\":0,\"label\":\"x\",\"check\":false,\"expects\":-1,\"verdict\":\"UNSAT\",\"instance_count\":null}\n\n";
        let FileOutcome::Commands(cmds) = parse_shim_output(stdout) else {
            panic!("expected Commands")
        };
        assert_eq!(cmds.len(), 1);
    }
}
