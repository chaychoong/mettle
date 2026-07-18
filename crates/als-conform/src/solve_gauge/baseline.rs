//! Loads the cached reference-jar verdicts (`baselines/*-verdict.json`) into a
//! `(relpath, command-index) → verdict` lookup for the solve gauge (mt-037).
//!
//! Each file is a serialized [`crate::scorecard::Scorecard`] (the format
//! `conform --json-out` writes); rather than teach the `model` types
//! `Deserialize`, this reads the fixed shape through `serde_json::Value`, which
//! keeps the read tolerant of extra fields (`totals`, `instance_count`) the
//! gauge does not need. Every `baselines/*-verdict.json` present is merged, and
//! a command with no entry is reported as `no_baseline` by the caller — the
//! `portus-63-verdict.json` produced in parallel simply drops in.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

/// One command's jar verdict as the gauge compares against it. A command-level
/// `error`, a file-level `timeout`, and a file-level `error` all collapse to
/// [`JarVerdict::Nonverdict`]: the jar produced no SAT/UNSAT answer, so the
/// command lands in the gauge's `jar_nonverdict` bucket rather than being
/// scored as an agreement or a disagreement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JarVerdict {
    Sat,
    Unsat,
    Nonverdict,
}

/// The merged baseline over every loaded `*-verdict.json`.
#[derive(Debug, Default)]
pub struct Baseline {
    /// Per-command verdicts, keyed by (workspace-relative path, command index).
    commands: BTreeMap<(String, usize), JarVerdict>,
    /// Files whose whole run was a non-verdict (timeout / file-level error):
    /// every command of such a file is [`JarVerdict::Nonverdict`], even though
    /// no per-command rows exist to key on.
    file_nonverdict: BTreeSet<String>,
    /// Names of the `*-verdict.json` files merged in, for the report header.
    pub loaded: Vec<String>,
}

impl Baseline {
    /// The jar verdict for `relpath[idx]`, or `None` when no baseline covers it
    /// (the gauge's `no_baseline` bucket). A file-level non-verdict answers for
    /// every index of that file.
    #[must_use]
    pub fn lookup(&self, relpath: &str, idx: usize) -> Option<JarVerdict> {
        if let Some(v) = self.commands.get(&(relpath.to_owned(), idx)) {
            return Some(*v);
        }
        if self.file_nonverdict.contains(relpath) {
            return Some(JarVerdict::Nonverdict);
        }
        None
    }

    /// Number of per-command entries merged (report diagnostics).
    #[must_use]
    pub fn command_count(&self) -> usize {
        self.commands.len()
    }
}

/// Loads and merges every `*-verdict.json` under `baselines_dir`. A missing
/// directory or an unreadable/malformed file is skipped (best-effort: this is a
/// gauge, and a command with no entry is simply `no_baseline`), so the merge is
/// still deterministic — files are visited in sorted name order.
#[must_use]
pub fn load_baselines(baselines_dir: &Path) -> Baseline {
    let mut baseline = Baseline::default();
    let Ok(entries) = std::fs::read_dir(baselines_dir) else {
        return baseline;
    };
    let mut paths: Vec<_> = entries
        .flatten()
        .map(|e| e.path())
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.ends_with("-verdict.json"))
        })
        .collect();
    paths.sort();
    for path in &paths {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        let Ok(value) = serde_json::from_str::<serde_json::Value>(&text) else {
            continue;
        };
        merge_scorecard(&value, &mut baseline);
        if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
            baseline.loaded.push(name.to_owned());
        }
    }
    baseline
}

/// Merges one parsed scorecard value into `baseline`.
fn merge_scorecard(value: &serde_json::Value, baseline: &mut Baseline) {
    let Some(files) = value.get("files").and_then(|f| f.as_array()) else {
        return;
    };
    for file in files {
        let Some(relpath) = file.get("file").and_then(|f| f.as_str()) else {
            continue;
        };
        let Some(outcome) = file.get("outcome") else {
            continue;
        };
        match outcome.get("type").and_then(|t| t.as_str()) {
            Some("commands") => merge_commands(relpath, outcome, baseline),
            // A file-level timeout or error: no SAT/UNSAT for any command.
            Some("timeout" | "error") => {
                baseline.file_nonverdict.insert(relpath.to_owned());
            }
            _ => {}
        }
    }
}

/// Merges the per-command rows of one `commands` file outcome.
fn merge_commands(relpath: &str, outcome: &serde_json::Value, baseline: &mut Baseline) {
    let Some(data) = outcome.get("data").and_then(|d| d.as_array()) else {
        return;
    };
    for command in data {
        let Some(idx) = command.get("index").and_then(serde_json::Value::as_u64) else {
            continue;
        };
        let verdict = match command
            .get("outcome")
            .and_then(|o| o.get("type"))
            .and_then(|t| t.as_str())
        {
            Some("sat") => JarVerdict::Sat,
            Some("unsat") => JarVerdict::Unsat,
            // A per-command error (a translation/solve throw) is a non-verdict.
            Some("error") => JarVerdict::Nonverdict,
            _ => continue,
        };
        baseline.commands.insert(
            (
                relpath.to_owned(),
                usize::try_from(idx).unwrap_or(usize::MAX),
            ),
            verdict,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_commands_sat_unsat_and_error() {
        let json = serde_json::json!({
            "files": [
                { "file": "a.als", "outcome": { "type": "commands", "data": [
                    { "index": 0, "outcome": { "type": "sat", "instance_count": null } },
                    { "index": 1, "outcome": { "type": "unsat", "instance_count": null } },
                    { "index": 2, "outcome": { "type": "error", "kind": "command", "message": "boom" } }
                ]}},
                { "file": "b.als", "outcome": { "type": "timeout" } },
                { "file": "c.als", "outcome": { "type": "error", "kind": "parse", "message": "bad" } }
            ],
            "totals": { "commands": 3 }
        });
        let mut baseline = Baseline::default();
        merge_scorecard(&json, &mut baseline);

        assert_eq!(baseline.lookup("a.als", 0), Some(JarVerdict::Sat));
        assert_eq!(baseline.lookup("a.als", 1), Some(JarVerdict::Unsat));
        assert_eq!(baseline.lookup("a.als", 2), Some(JarVerdict::Nonverdict));
        // No such index and file is not a non-verdict → no_baseline.
        assert_eq!(baseline.lookup("a.als", 9), None);
        // File-level timeout/error answers for every index.
        assert_eq!(baseline.lookup("b.als", 0), Some(JarVerdict::Nonverdict));
        assert_eq!(baseline.lookup("c.als", 7), Some(JarVerdict::Nonverdict));
        // A file with no baseline at all.
        assert_eq!(baseline.lookup("unknown.als", 0), None);
        assert_eq!(baseline.command_count(), 3);
    }

    #[test]
    fn later_file_wins_on_duplicate_key() {
        // Deterministic merge: a second scorecard mentioning the same key
        // overwrites (sorted-name visit order makes this stable).
        let mut baseline = Baseline::default();
        merge_scorecard(
            &serde_json::json!({ "files": [
                { "file": "a.als", "outcome": { "type": "commands", "data": [
                    { "index": 0, "outcome": { "type": "sat" } } ]}}
            ]}),
            &mut baseline,
        );
        merge_scorecard(
            &serde_json::json!({ "files": [
                { "file": "a.als", "outcome": { "type": "commands", "data": [
                    { "index": 0, "outcome": { "type": "unsat" } } ]}}
            ]}),
            &mut baseline,
        );
        assert_eq!(baseline.lookup("a.als", 0), Some(JarVerdict::Unsat));
    }
}
