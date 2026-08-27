use std::path::PathBuf;
use std::time::Duration;

use super::mettle::{FileRun, MettleOutcome, MettleTiming};
use super::*;
use crate::model::{CommandResult, FileResult, ShimErrorKind};

fn jar_cmd(index: usize, sat: bool, elapsed_ms: Option<u64>) -> CommandResult {
    CommandResult {
        index,
        label: "run".to_owned(),
        check: false,
        expects: None,
        outcome: if sat {
            Outcome::Sat {
                instance_count: None,
            }
        } else {
            Outcome::Unsat {
                instance_count: None,
            }
        },
        elapsed_ms,
    }
}

fn jar_error_cmd(index: usize) -> CommandResult {
    CommandResult {
        index,
        label: "broken".to_owned(),
        check: false,
        expects: None,
        outcome: Outcome::Error {
            kind: ShimErrorKind::Command,
            message: "boom".to_owned(),
        },
        elapsed_ms: None,
    }
}

fn mettle_verdict(sat: bool, ms: u64) -> MettleTiming {
    MettleTiming {
        outcome: MettleOutcome::Verdict(sat),
        elapsed: Duration::from_millis(ms),
    }
}

fn mettle_defer(reason: &'static str) -> MettleTiming {
    MettleTiming {
        outcome: MettleOutcome::Defer(reason),
        elapsed: Duration::from_millis(1),
    }
}

fn join(
    jar_outcome: &FileOutcome,
    mettle_run: FileRun,
) -> (
    Vec<SolveBenchRow>,
    Vec<SolveDisagreement>,
    BTreeMap<String, usize>,
) {
    let mut rows = Vec::new();
    let mut disagreements = Vec::new();
    let mut excluded = BTreeMap::new();
    let mut anomalies = Vec::new();
    let mut jar_times = Vec::new();
    let mut mettle_times = Vec::new();
    join_one_file(
        &PathBuf::from("x.als"),
        jar_outcome,
        mettle_run,
        &mut rows,
        &mut disagreements,
        &mut excluded,
        &mut anomalies,
        &mut jar_times,
        &mut mettle_times,
    );
    assert_eq!(rows.len(), jar_times.len());
    assert_eq!(rows.len(), mettle_times.len());
    (rows, disagreements, excluded)
}

#[test]
fn agreeing_verdicts_join_into_a_row() {
    let jar = FileOutcome::Commands(vec![jar_cmd(0, true, Some(42))]);
    let mettle = FileRun::Resolved(vec![(0, mettle_verdict(true, 7))]);
    let (rows, disagreements, excluded) = join(&jar, mettle);
    assert_eq!(rows.len(), 1);
    assert!(disagreements.is_empty());
    assert!(excluded.is_empty());
    assert_eq!(rows[0].verdict, "SAT");
    assert!((rows[0].jar_ms - 42.0).abs() < f64::EPSILON);
    assert!((rows[0].mettle_ms - 7.0).abs() < f64::EPSILON);
}

#[test]
fn disagreeing_verdicts_are_flagged_not_dropped() {
    let jar = FileOutcome::Commands(vec![jar_cmd(0, true, Some(10))]);
    let mettle = FileRun::Resolved(vec![(0, mettle_verdict(false, 5))]);
    let (rows, disagreements, excluded) = join(&jar, mettle);
    assert!(rows.is_empty());
    assert!(excluded.is_empty());
    assert_eq!(disagreements.len(), 1);
    assert_eq!(disagreements[0].jar_verdict, "SAT");
    assert_eq!(disagreements[0].mettle_verdict, "UNSAT");
}

#[test]
fn mettle_defer_excludes_with_its_own_typed_reason() {
    let jar = FileOutcome::Commands(vec![jar_cmd(0, true, Some(10))]);
    let mettle = FileRun::Resolved(vec![(0, mettle_defer("mettle_defer:over_budget"))]);
    let (rows, disagreements, excluded) = join(&jar, mettle);
    assert!(rows.is_empty());
    assert!(disagreements.is_empty());
    assert_eq!(excluded.get("mettle_defer:over_budget"), Some(&1));
}

#[test]
fn jar_command_error_excludes_with_a_typed_reason() {
    let jar = FileOutcome::Commands(vec![jar_error_cmd(0)]);
    let mettle = FileRun::Resolved(vec![(0, mettle_verdict(true, 5))]);
    let (rows, _disagreements, excluded) = join(&jar, mettle);
    assert!(rows.is_empty());
    assert_eq!(excluded.get("jar_error:command:Command"), Some(&1));
}

#[test]
fn jar_timeout_marks_every_mettle_known_command() {
    let jar = FileOutcome::Timeout;
    let mettle = FileRun::Resolved(vec![
        (0, mettle_verdict(true, 5)),
        (1, mettle_verdict(false, 5)),
    ]);
    let (rows, _disagreements, excluded) = join(&jar, mettle);
    assert!(rows.is_empty());
    assert_eq!(excluded.get("jar_timeout"), Some(&2));
}

#[test]
fn mettle_unresolved_marks_every_jar_known_command() {
    let jar = FileOutcome::Commands(vec![jar_cmd(0, true, Some(1)), jar_cmd(1, false, Some(2))]);
    let mettle = FileRun::Unresolved;
    let (rows, _disagreements, excluded) = join(&jar, mettle);
    assert!(rows.is_empty());
    assert_eq!(excluded.get("mettle_unresolved"), Some(&2));
}

#[test]
fn both_sides_unavailable_counts_once_for_the_whole_file() {
    let jar = FileOutcome::Timeout;
    let mettle = FileRun::Unresolved;
    let (rows, disagreements, excluded) = join(&jar, mettle);
    assert!(rows.is_empty());
    assert!(disagreements.is_empty());
    assert_eq!(excluded.get("both_sides_unavailable"), Some(&1));
}

#[test]
fn missing_elapsed_ms_excludes_rather_than_faking_a_zero_time() {
    let jar = FileOutcome::Commands(vec![jar_cmd(0, true, None)]);
    let mettle = FileRun::Resolved(vec![(0, mettle_verdict(true, 5))]);
    let (rows, disagreements, excluded) = join(&jar, mettle);
    assert!(rows.is_empty());
    assert!(disagreements.is_empty());
    assert_eq!(excluded.get("jar_missing_elapsed_ms"), Some(&1));
}

#[test]
fn verify_aligned_rejects_a_length_mismatch() {
    let files = vec![PathBuf::from("a.als"), PathBuf::from("b.als")];
    let jar_files = vec![FileResult {
        file: PathBuf::from("a.als"),
        outcome: FileOutcome::Commands(vec![]),
    }];
    assert!(verify_aligned(&files, &jar_files).is_err());
}

#[test]
fn verify_aligned_rejects_out_of_order_results() {
    let files = vec![PathBuf::from("a.als"), PathBuf::from("b.als")];
    let jar_files = vec![
        FileResult {
            file: PathBuf::from("b.als"),
            outcome: FileOutcome::Commands(vec![]),
        },
        FileResult {
            file: PathBuf::from("a.als"),
            outcome: FileOutcome::Commands(vec![]),
        },
    ];
    assert!(verify_aligned(&files, &jar_files).is_err());
}

#[test]
fn verify_aligned_accepts_a_matching_list() {
    let files = vec![PathBuf::from("a.als"), PathBuf::from("b.als")];
    let jar_files = vec![
        FileResult {
            file: PathBuf::from("a.als"),
            outcome: FileOutcome::Commands(vec![]),
        },
        FileResult {
            file: PathBuf::from("b.als"),
            outcome: FileOutcome::Commands(vec![]),
        },
    ];
    assert!(verify_aligned(&files, &jar_files).is_ok());
}
