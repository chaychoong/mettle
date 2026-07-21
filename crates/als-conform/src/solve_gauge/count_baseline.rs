//! Cached reference-jar **count** baselines (mt-054 (b)).
//!
//! Jar model counts at a pinned config (`count_symmetry`, `count_cap`, overflow,
//! solver) are immutable facts; running a live JVM per sweep just to recompute
//! them is waste. This module defines the on-disk baseline format
//! (`baselines/<name>-count-sb<N>.json`), a deterministic writer (used by the
//! `--refresh-counts` mode), and a loader that mirrors [`super::baseline`]: it
//! merges every `*-count-sb<N>.json` matching the run's `count_symmetry`, keying
//! each command's outcome by `(relpath, index)`.
//!
//! **Config-mismatch is a hard error, never a silent skip:** a baseline whose
//! header disagrees with the run on `count_cap`/overflow/`count_symmetry`/`solver`
//! (the fields that change *what the counts mean*) fails the load with a
//! [`ConformError::CountBaselineConfigMismatch`]. `jar_timeout` may differ (it
//! affects only which entries are `timeout`) with a warning.
//!
//! Everything is `BTreeMap`-ordered so the pretty JSON is byte-identical run to
//! run (STYLE D1); this module never prints (STYLE E3) — warnings are returned
//! for the caller to surface through its progress channel.

use std::collections::BTreeMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::error::ConformError;
use crate::model::{FileOutcome, Outcome};

/// One command's (or one file's) jar count outcome. `unsat`/`nonverdict`/
/// `timeout`/`error` are bare-string markers; a successful count is `{"count":n}`.
///
/// Only `Serialize` is derived: reads go through [`read_count_baseline`] via
/// `serde_json::Value` (serde's `untagged` *de*serialization does not compose
/// through nested untagged enums / integer map keys, so a derived `Deserialize`
/// would silently fail the load).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CountMarker {
    Unsat,
    Nonverdict,
    Timeout,
    Error,
}

impl CountMarker {
    fn from_str(s: &str) -> Option<Self> {
        match s {
            "unsat" => Some(Self::Unsat),
            "nonverdict" => Some(Self::Nonverdict),
            "timeout" => Some(Self::Timeout),
            "error" => Some(Self::Error),
            _ => None,
        }
    }
}

/// A per-command entry: either an exact count or a typed marker.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(untagged)]
pub enum CountEntry {
    /// `{"count": n}` — the jar's SB-`count_symmetry` model count (capped at
    /// `count_cap + 1`, matching the live enumeration).
    Count { count: u64 },
    /// A bare string: `"unsat" | "nonverdict" | "timeout" | "error"`.
    Marker(CountMarker),
}

/// One file's recorded outcome: either per-command entries, or a file-level
/// marker (a JVM timeout / spawn error yields no per-command rows, so — like the
/// verdict baseline's `file_nonverdict` set — it answers for every index).
///
/// The command map is keyed by the index rendered as a string (JSON object keys
/// are strings regardless); `BTreeMap<String>` gives a deterministic key order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(untagged)]
pub enum FileCounts {
    /// A file-level `"timeout"` / `"error"` (no command rows exist).
    Level(CountMarker),
    /// Per-command entries, keyed by the command index as a string.
    Commands(BTreeMap<String, CountEntry>),
}

/// The pinned config a count baseline was produced at. Byte-identical fields are
/// compared field-by-field against the run's config at load (a mismatch on the
/// meaning-bearing fields is a hard error). This one is a plain struct, so a
/// derived `Deserialize` composes fine.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CountConfig {
    pub count_symmetry: u32,
    pub count_cap: u64,
    pub jar_timeout_secs: u64,
    pub no_overflow: bool,
    pub solver: String,
}

/// The whole on-disk baseline file (`config` header + per-file entries).
#[derive(Debug, Clone, Serialize)]
pub struct CountBaselineFile {
    pub config: CountConfig,
    pub entries: BTreeMap<String, FileCounts>,
}

impl CountBaselineFile {
    /// Renders the baseline as stable pretty JSON (`BTreeMap` key order).
    ///
    /// # Errors
    /// Only if serialization itself fails (allocation failure).
    pub fn to_json(&self) -> Result<String, ConformError> {
        Ok(serde_json::to_string_pretty(self)?)
    }
}

/// Reads a count-baseline document (`config` + `entries`) from JSON text,
/// interpreting `entries` through `serde_json::Value` so nested untagged shapes
/// round-trip reliably. Returns `None` if the text is not valid JSON or lacks a
/// well-formed `config` header.
pub(crate) fn read_count_baseline(
    text: &str,
) -> Option<(CountConfig, BTreeMap<String, FileCounts>)> {
    let value: serde_json::Value = serde_json::from_str(text).ok()?;
    let config: CountConfig = serde_json::from_value(value.get("config")?.clone()).ok()?;
    let mut entries = BTreeMap::new();
    if let Some(obj) = value.get("entries").and_then(|e| e.as_object()) {
        for (rel, v) in obj {
            if let Some(fc) = parse_file_counts(v) {
                entries.insert(rel.clone(), fc);
            }
        }
    }
    Some((config, entries))
}

/// Interprets one `entries[relpath]` value: a bare marker string, or an object of
/// per-command cells.
fn parse_file_counts(v: &serde_json::Value) -> Option<FileCounts> {
    if let Some(s) = v.as_str() {
        return CountMarker::from_str(s).map(FileCounts::Level);
    }
    let cells = v.as_object()?;
    let mut m = BTreeMap::new();
    for (idx, cell) in cells {
        let entry = if let Some(count) = cell.get("count").and_then(serde_json::Value::as_u64) {
            CountEntry::Count { count }
        } else if let Some(marker) = cell.as_str().and_then(CountMarker::from_str) {
            CountEntry::Marker(marker)
        } else {
            continue;
        };
        m.insert(idx.clone(), entry);
    }
    Some(FileCounts::Commands(m))
}

/// Maps one jar [`FileOutcome`] to its recorded [`FileCounts`] (the `--refresh`
/// writer's core). A file-level timeout/error becomes a file-level marker; a
/// `commands` outcome records every command's typed outcome.
#[must_use]
pub fn file_counts_from_outcome(outcome: &FileOutcome) -> FileCounts {
    match outcome {
        FileOutcome::Timeout => FileCounts::Level(CountMarker::Timeout),
        FileOutcome::Error { .. } => FileCounts::Level(CountMarker::Error),
        FileOutcome::Commands(cmds) => {
            let mut m = BTreeMap::new();
            for c in cmds {
                let entry = match &c.outcome {
                    Outcome::Sat {
                        instance_count: Some(j),
                    } => CountEntry::Count {
                        count: u64::from(*j),
                    },
                    // Enumeration was requested (`UpTo(cap+1)`), so a SAT command
                    // with no count is a jar protocol oddity, not comparable.
                    Outcome::Sat {
                        instance_count: None,
                    } => CountEntry::Marker(CountMarker::Nonverdict),
                    Outcome::Unsat { .. } => CountEntry::Marker(CountMarker::Unsat),
                    Outcome::Error { .. } => CountEntry::Marker(CountMarker::Error),
                };
                m.insert(c.index.to_string(), entry);
            }
            FileCounts::Commands(m)
        }
    }
}

/// The disposition of looking up one command in the merged baseline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CountLookup {
    /// An exact recorded count to compare mettle's against.
    Count(u64),
    /// A typed non-count outcome (the command maps to a `skip_jar_*` bucket).
    Marker(CountMarker),
    /// No baseline covers this command (`skip_no_count_baseline`).
    Miss,
}

/// The merged count baseline over every loaded `*-count-sb<N>.json`.
#[derive(Debug, Default)]
pub struct CountBaseline {
    files: BTreeMap<String, FileCounts>,
    /// Names of the baseline files merged in (for the report header).
    pub loaded: Vec<String>,
    /// Non-fatal load warnings (e.g. a differing `jar_timeout`), for the caller
    /// to surface through its progress channel (this library never prints).
    pub warnings: Vec<String>,
}

impl CountBaseline {
    /// The recorded outcome for `relpath[idx]`. A file-level marker answers for
    /// every index of that file.
    #[must_use]
    pub fn lookup(&self, relpath: &str, idx: usize) -> CountLookup {
        match self.files.get(relpath) {
            Some(FileCounts::Level(m)) => CountLookup::Marker(*m),
            Some(FileCounts::Commands(map)) => match map.get(&idx.to_string()) {
                Some(CountEntry::Count { count }) => CountLookup::Count(*count),
                Some(CountEntry::Marker(m)) => CountLookup::Marker(*m),
                None => CountLookup::Miss,
            },
            None => CountLookup::Miss,
        }
    }

    /// The gauge's stage-2 disposition for a mettle-SAT command whose exact SB
    /// count is `mettle_count`: the count bucket key plus an optional
    /// `COUNT_MISMATCH` line. Mirrors the live `jar_count_bucket` mapping exactly
    /// (a jar UNSAT / error / non-verdict for a mettle-SAT command is a
    /// `skip_jar_error`, never a fabricated mismatch), and adds the new typed
    /// `skip_no_count_baseline` on a miss.
    #[must_use]
    pub fn disposition(
        &self,
        relpath: &str,
        idx: usize,
        mettle_count: u64,
    ) -> (String, Option<String>) {
        match self.lookup(relpath, idx) {
            CountLookup::Count(j) => {
                if j == mettle_count {
                    ("count_match".to_owned(), None)
                } else {
                    (
                        "COUNT_MISMATCH".to_owned(),
                        Some(format!("{relpath}[{idx}]: mettle={mettle_count} jar={j}")),
                    )
                }
            }
            CountLookup::Marker(CountMarker::Timeout) => ("skip_jar_timeout".to_owned(), None),
            CountLookup::Marker(_) => ("skip_jar_error".to_owned(), None),
            CountLookup::Miss => ("skip_no_count_baseline".to_owned(), None),
        }
    }
}

/// Loads and merges every `*-count-sb<N>.json` (for `N = count_symmetry`) under
/// `baselines_dir`, validating each file's config header against the run's
/// pinned config.
///
/// Files are visited in sorted name order (deterministic merge; a later file
/// wins on a duplicate key). A missing directory yields an empty baseline (every
/// command becomes `skip_no_count_baseline`); an unreadable/malformed *file* is
/// skipped with a warning, but a readable file whose header disagrees on a
/// meaning-bearing field is a hard error.
///
/// # Errors
/// [`ConformError::CountBaselineConfigMismatch`] if any loaded baseline's header
/// disagrees with the run on `count_cap`/`no_overflow`/`count_symmetry`/`solver`.
pub fn load_count_baselines(
    baselines_dir: &Path,
    count_symmetry: u32,
    count_cap: u64,
    no_overflow: bool,
    solver: &str,
    jar_timeout_secs: u64,
) -> Result<CountBaseline, ConformError> {
    let mut baseline = CountBaseline::default();
    let suffix = format!("-count-sb{count_symmetry}.json");
    let Ok(entries) = std::fs::read_dir(baselines_dir) else {
        return Ok(baseline);
    };
    let mut paths: Vec<_> = entries
        .flatten()
        .map(|e| e.path())
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.ends_with(&suffix))
        })
        .collect();
    paths.sort();

    for path in &paths {
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("<count-baseline>")
            .to_owned();
        let Ok(text) = std::fs::read_to_string(path) else {
            baseline
                .warnings
                .push(format!("count baseline {name}: unreadable, skipped"));
            continue;
        };
        let Some((config, entries)) = read_count_baseline(&text) else {
            baseline
                .warnings
                .push(format!("count baseline {name}: malformed, skipped"));
            continue;
        };
        check_config(
            &config,
            &name,
            count_symmetry,
            count_cap,
            no_overflow,
            solver,
            jar_timeout_secs,
            &mut baseline.warnings,
        )?;
        for (relpath, counts) in entries {
            baseline.files.insert(relpath, counts);
        }
        baseline.loaded.push(name);
    }
    Ok(baseline)
}

/// Validates a loaded header against the run's pinned config. A mismatch on a
/// meaning-bearing field is a hard error; a differing `jar_timeout` is a warning.
#[allow(clippy::too_many_arguments, reason = "one flat field-by-field check")]
fn check_config(
    header: &CountConfig,
    name: &str,
    count_symmetry: u32,
    count_cap: u64,
    no_overflow: bool,
    solver: &str,
    jar_timeout_secs: u64,
    warnings: &mut Vec<String>,
) -> Result<(), ConformError> {
    let mismatch =
        |field, expected: String, found: String| ConformError::CountBaselineConfigMismatch {
            file: name.to_owned(),
            field,
            expected,
            found,
        };
    if header.count_symmetry != count_symmetry {
        return Err(mismatch(
            "count_symmetry",
            count_symmetry.to_string(),
            header.count_symmetry.to_string(),
        ));
    }
    if header.count_cap != count_cap {
        return Err(mismatch(
            "count_cap",
            count_cap.to_string(),
            header.count_cap.to_string(),
        ));
    }
    if header.no_overflow != no_overflow {
        return Err(mismatch(
            "no_overflow",
            no_overflow.to_string(),
            header.no_overflow.to_string(),
        ));
    }
    if header.solver != solver {
        return Err(mismatch("solver", solver.to_owned(), header.solver.clone()));
    }
    if header.jar_timeout_secs != jar_timeout_secs {
        warnings.push(format!(
            "count baseline {name}: jar_timeout differs (baseline={}s, run={jar_timeout_secs}s) — affects only which entries are `timeout`",
            header.jar_timeout_secs
        ));
    }
    Ok(())
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "test fixtures assert on known-good values"
)]
mod tests {
    use super::*;
    use crate::model::{CommandResult, ShimErrorKind};

    fn write(dir: &Path, name: &str, file: &CountBaselineFile) {
        std::fs::write(dir.join(name), file.to_json().unwrap()).unwrap();
    }

    fn header() -> CountConfig {
        CountConfig {
            count_symmetry: 0,
            count_cap: 10_000,
            jar_timeout_secs: 300,
            no_overflow: true,
            solver: "sat4j".to_owned(),
        }
    }

    #[test]
    fn round_trip_write_then_load() {
        let dir = std::env::temp_dir().join(format!("als-count-bl-rt-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();

        let mut entries = BTreeMap::new();
        let mut cmds = BTreeMap::new();
        cmds.insert("0".to_owned(), CountEntry::Count { count: 1129 });
        cmds.insert("1".to_owned(), CountEntry::Marker(CountMarker::Unsat));
        entries.insert("a.als".to_owned(), FileCounts::Commands(cmds));
        entries.insert("t.als".to_owned(), FileCounts::Level(CountMarker::Timeout));
        let file = CountBaselineFile {
            config: header(),
            entries,
        };
        write(&dir, "x-count-sb0.json", &file);

        let loaded = load_count_baselines(&dir, 0, 10_000, true, "sat4j", 300).unwrap();
        assert_eq!(loaded.loaded, vec!["x-count-sb0.json".to_owned()]);
        assert_eq!(loaded.lookup("a.als", 0), CountLookup::Count(1129));
        assert_eq!(
            loaded.lookup("a.als", 1),
            CountLookup::Marker(CountMarker::Unsat)
        );
        // File-level timeout answers for every index.
        assert_eq!(
            loaded.lookup("t.als", 7),
            CountLookup::Marker(CountMarker::Timeout)
        );
        // Missing index / file → Miss.
        assert_eq!(loaded.lookup("a.als", 9), CountLookup::Miss);
        assert_eq!(loaded.lookup("nope.als", 0), CountLookup::Miss);

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn skip_no_count_baseline_bucketing() {
        // A miss is the new typed bucket; a jar UNSAT/error is skip_jar_error; a
        // timeout is skip_jar_timeout; a matching count is count_match.
        let mut entries = BTreeMap::new();
        let mut cmds = BTreeMap::new();
        cmds.insert("0".to_owned(), CountEntry::Count { count: 5 });
        cmds.insert("1".to_owned(), CountEntry::Marker(CountMarker::Unsat));
        cmds.insert("2".to_owned(), CountEntry::Marker(CountMarker::Timeout));
        entries.insert("a.als".to_owned(), FileCounts::Commands(cmds));
        let cb = CountBaseline {
            files: entries,
            loaded: vec![],
            warnings: vec![],
        };
        assert_eq!(cb.disposition("a.als", 0, 5).0, "count_match");
        assert_eq!(cb.disposition("a.als", 0, 6).0, "COUNT_MISMATCH");
        assert_eq!(cb.disposition("a.als", 1, 5).0, "skip_jar_error");
        assert_eq!(cb.disposition("a.als", 2, 5).0, "skip_jar_timeout");
        assert_eq!(cb.disposition("a.als", 9, 5).0, "skip_no_count_baseline");
        assert_eq!(
            cb.disposition("missing.als", 0, 5).0,
            "skip_no_count_baseline"
        );
    }

    #[test]
    fn config_mismatch_is_hard_error() {
        let dir = std::env::temp_dir().join(format!("als-count-bl-mm-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let mut cfg = header();
        cfg.count_cap = 999; // disagrees with the run's 10_000
        write(
            &dir,
            "y-count-sb0.json",
            &CountBaselineFile {
                config: cfg,
                entries: BTreeMap::new(),
            },
        );
        let err = load_count_baselines(&dir, 0, 10_000, true, "sat4j", 300).unwrap_err();
        match err {
            ConformError::CountBaselineConfigMismatch { field, .. } => {
                assert_eq!(field, "count_cap");
            }
            other => panic!("expected count_cap mismatch, got {other:?}"),
        }
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn jar_timeout_difference_is_only_a_warning() {
        let dir = std::env::temp_dir().join(format!("als-count-bl-wt-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        write(
            &dir,
            "z-count-sb0.json",
            &CountBaselineFile {
                config: header(),
                entries: BTreeMap::new(),
            },
        );
        // Different jar_timeout: loads fine, one warning.
        let loaded = load_count_baselines(&dir, 0, 10_000, true, "sat4j", 600).unwrap();
        assert_eq!(loaded.warnings.len(), 1);
        assert!(loaded.warnings[0].contains("jar_timeout"));
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn file_counts_from_commands_and_levels() {
        let cmds = FileOutcome::Commands(vec![
            CommandResult {
                index: 0,
                label: "a".to_owned(),
                check: false,
                expects: None,
                outcome: Outcome::Sat {
                    instance_count: Some(3),
                },
            },
            CommandResult {
                index: 1,
                label: "b".to_owned(),
                check: true,
                expects: None,
                outcome: Outcome::Unsat {
                    instance_count: None,
                },
            },
            CommandResult {
                index: 2,
                label: "c".to_owned(),
                check: false,
                expects: None,
                outcome: Outcome::Error {
                    kind: ShimErrorKind::Command,
                    message: "boom".to_owned(),
                },
            },
        ]);
        let FileCounts::Commands(m) = file_counts_from_outcome(&cmds) else {
            panic!("expected commands");
        };
        assert_eq!(m.get("0"), Some(&CountEntry::Count { count: 3 }));
        assert_eq!(m.get("1"), Some(&CountEntry::Marker(CountMarker::Unsat)));
        assert_eq!(m.get("2"), Some(&CountEntry::Marker(CountMarker::Error)));
        assert_eq!(
            file_counts_from_outcome(&FileOutcome::Timeout),
            FileCounts::Level(CountMarker::Timeout)
        );
    }
}
