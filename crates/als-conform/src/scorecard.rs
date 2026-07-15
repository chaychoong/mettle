//! Aggregates per-file oracle results into a deterministic scorecard and
//! renders it as JSON (machine-readable artifact) or a text table
//! (human-readable). Pure aggregation/rendering logic -- no process
//! spawning -- so it is unit-tested without the jar.

use std::fmt::Write as _;

use serde::Serialize;

use crate::error::ConformError;
use crate::model::{FileOutcome, FileResult, Outcome};

/// Net 0 totals: mining `expect 0`/`expect 1` annotations as a free
/// cross-check of the oracle verdict (ADR-0002 item 3).
///
/// `errors` counts both whole-file errors (parse failure, protocol
/// failure) and per-command errors (one throw inside an otherwise-healthy
/// file) -- each such event contributes exactly one to this total; the
/// per-file/per-command detail is preserved in `Scorecard::files` for
/// anyone who needs the breakdown.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
pub struct Totals {
    pub commands: usize,
    pub with_expect: usize,
    pub matches: usize,
    pub mismatches: usize,
    pub timeouts: usize,
    pub errors: usize,
}

impl Totals {
    fn compute(files: &[FileResult]) -> Self {
        let mut totals = Totals::default();
        for file in files {
            match &file.outcome {
                FileOutcome::Timeout => totals.timeouts += 1,
                FileOutcome::Error { .. } => totals.errors += 1,
                FileOutcome::Commands(commands) => {
                    for command in commands {
                        totals.commands += 1;
                        match &command.outcome {
                            Outcome::Error { .. } => totals.errors += 1,
                            Outcome::Sat { .. } | Outcome::Unsat { .. } => {
                                if let Some(expected_sat) = command.expects {
                                    totals.with_expect += 1;
                                    if command.outcome.is_sat() == expected_sat {
                                        totals.matches += 1;
                                    } else {
                                        totals.mismatches += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        totals
    }
}

/// A full conformance run: one [`crate::model::FileResult`] per input
/// file plus aggregated [`Totals`].
///
/// Deterministic by construction (STYLE D1/D2/C1-C3): `files` is sorted
/// by path (`PathBuf`'s `Ord` is lexicographic component order) and each
/// file's commands are sorted by index, so rendering never depends on
/// `HashMap` iteration or on the order oracle runs happened to complete
/// in.
#[derive(Debug, Clone, Serialize)]
pub struct Scorecard {
    pub files: Vec<FileResult>,
    pub totals: Totals,
}

impl Scorecard {
    /// Builds a scorecard from per-file results, re-asserting the sort
    /// order that makes rendering deterministic regardless of the order
    /// `files` was collected in.
    #[must_use]
    pub fn new(mut files: Vec<FileResult>) -> Self {
        files.sort_by(|a, b| a.file.cmp(&b.file));
        for file in &mut files {
            if let FileOutcome::Commands(commands) = &mut file.outcome {
                commands.sort_by_key(|c| c.index);
            }
        }
        let totals = Totals::compute(&files);
        Self { files, totals }
    }

    /// Renders the scorecard as pretty-printed JSON.
    ///
    /// # Errors
    /// Only if serialization itself fails, which does not happen for this
    /// crate's own `Serialize` types short of an allocation failure.
    pub fn to_json(&self) -> Result<String, ConformError> {
        Ok(serde_json::to_string_pretty(self)?)
    }

    /// Renders a human-readable text table: one row per command (or one
    /// row per file for `Timeout`/`Error` outcomes), followed by a totals
    /// summary.
    #[must_use]
    pub fn render_text(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(
            out,
            "{:<40} {:>4} {:<5} {:<20} {:<7} {:<6} {:>6} {:<5}",
            "FILE", "IDX", "KIND", "LABEL", "EXPECT", "VERDICT", "COUNT", "NET0"
        );
        for file in &self.files {
            render_file_rows(&mut out, file);
        }
        let _ = writeln!(out);
        let t = &self.totals;
        let _ = writeln!(
            out,
            "commands={} with_expect={} matches={} mismatches={} timeouts={} errors={}",
            t.commands, t.with_expect, t.matches, t.mismatches, t.timeouts, t.errors
        );
        out
    }
}

fn render_file_rows(out: &mut String, file: &FileResult) {
    let path = file.file.display();
    match &file.outcome {
        FileOutcome::Timeout => {
            let _ = writeln!(
                out,
                "{path:<40} {:>4} {:<5} {:<20} {:<7} {:<6} {:>6} {:<5}",
                "-", "-", "<TIMEOUT>", "-", "-", "-", "-"
            );
        }
        FileOutcome::Error { kind, message } => {
            let _ = writeln!(
                out,
                "{path:<40} {:>4} {:<5} <ERROR:{kind:?}> {message}",
                "-", "-"
            );
        }
        FileOutcome::Commands(commands) => {
            for command in commands {
                let kind = if command.check { "check" } else { "run" };
                let expect = match command.expects {
                    None => "-".to_string(),
                    Some(true) => "sat".to_string(),
                    Some(false) => "unsat".to_string(),
                };
                let (verdict, count) = match &command.outcome {
                    Outcome::Sat { instance_count } => {
                        ("SAT".to_string(), fmt_count(*instance_count))
                    }
                    Outcome::Unsat { instance_count } => {
                        ("UNSAT".to_string(), fmt_count(*instance_count))
                    }
                    Outcome::Error { kind, message } => {
                        (format!("<ERROR:{kind:?}> {message}"), "-".to_string())
                    }
                };
                let net0 = match (command.expects, &command.outcome) {
                    (Some(expected_sat), Outcome::Sat { .. } | Outcome::Unsat { .. }) => {
                        if command.outcome.is_sat() == expected_sat {
                            "ok"
                        } else {
                            "MISMATCH"
                        }
                    }
                    _ => "-",
                };
                let _ = writeln!(
                    out,
                    "{path:<40} {:>4} {kind:<5} {:<20} {expect:<7} {verdict:<6} {count:>6} {net0:<5}",
                    command.index, command.label
                );
            }
        }
    }
}

fn fmt_count(count: Option<u32>) -> String {
    count.map_or_else(|| "-".to_string(), |n| n.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{CommandResult, ShimErrorKind};
    use std::path::PathBuf;

    fn sat(index: usize, expects: Option<bool>) -> CommandResult {
        CommandResult {
            index,
            label: "show".to_string(),
            check: false,
            expects,
            outcome: Outcome::Sat {
                instance_count: None,
            },
        }
    }

    fn unsat(index: usize, expects: Option<bool>) -> CommandResult {
        CommandResult {
            index,
            label: "impossible".to_string(),
            check: false,
            expects,
            outcome: Outcome::Unsat {
                instance_count: None,
            },
        }
    }

    #[test]
    fn totals_count_matches_and_mismatches() {
        let files = vec![FileResult {
            file: PathBuf::from("a.als"),
            outcome: FileOutcome::Commands(vec![
                unsat(0, Some(false)), // expect 0, is UNSAT -> match
                sat(1, Some(true)),    // expect 1, is SAT -> match
                sat(2, Some(false)),   // expect 0, is SAT -> mismatch
                sat(3, None),          // no expectation -> not counted
            ]),
        }];
        let card = Scorecard::new(files);
        assert_eq!(card.totals.commands, 4);
        assert_eq!(card.totals.with_expect, 3);
        assert_eq!(card.totals.matches, 2);
        assert_eq!(card.totals.mismatches, 1);
        assert_eq!(card.totals.timeouts, 0);
        assert_eq!(card.totals.errors, 0);
    }

    #[test]
    fn totals_count_timeouts_and_errors_at_both_levels() {
        let files = vec![
            FileResult {
                file: PathBuf::from("b.als"),
                outcome: FileOutcome::Timeout,
            },
            FileResult {
                file: PathBuf::from("c.als"),
                outcome: FileOutcome::Error {
                    kind: ShimErrorKind::Parse,
                    message: "bad".to_string(),
                },
            },
            FileResult {
                file: PathBuf::from("d.als"),
                outcome: FileOutcome::Commands(vec![CommandResult {
                    index: 0,
                    label: "broken".to_string(),
                    check: false,
                    expects: None,
                    outcome: Outcome::Error {
                        kind: ShimErrorKind::Command,
                        message: "boom".to_string(),
                    },
                }]),
            },
        ];
        let card = Scorecard::new(files);
        assert_eq!(card.totals.timeouts, 1);
        assert_eq!(card.totals.errors, 2); // one file-level + one command-level
        assert_eq!(card.totals.commands, 1); // only the d.als command counts
    }

    #[test]
    fn scorecard_sorts_files_by_path_and_commands_by_index() {
        let files = vec![
            FileResult {
                file: PathBuf::from("z.als"),
                outcome: FileOutcome::Commands(vec![sat(1, None), sat(0, None)]),
            },
            FileResult {
                file: PathBuf::from("a.als"),
                outcome: FileOutcome::Commands(vec![sat(0, None)]),
            },
        ];
        let card = Scorecard::new(files);
        assert_eq!(card.files[0].file, PathBuf::from("a.als"));
        assert_eq!(card.files[1].file, PathBuf::from("z.als"));
        let FileOutcome::Commands(cmds) = &card.files[1].outcome else {
            panic!("expected Commands")
        };
        assert_eq!(cmds[0].index, 0);
        assert_eq!(cmds[1].index, 1);
    }

    #[test]
    fn rendering_is_deterministic_across_runs() {
        let files = vec![FileResult {
            file: PathBuf::from("a.als"),
            outcome: FileOutcome::Commands(vec![sat(0, Some(true)), unsat(1, Some(false))]),
        }];
        let card1 = Scorecard::new(files.clone());
        let card2 = Scorecard::new(files);
        assert_eq!(card1.render_text(), card2.render_text());
        let json1 = card1
            .to_json()
            .unwrap_or_else(|e| panic!("card1 failed to serialize: {e}"));
        let json2 = card2
            .to_json()
            .unwrap_or_else(|e| panic!("card2 failed to serialize: {e}"));
        assert_eq!(json1, json2);
    }
}
