//! The committed per-run **sweep baseline** artifact (mt-057).
//!
//! One artifact — `baselines/*-sweep-sb<N>.json` — carries, per command, the
//! verdict/count bucket it landed in *and* an advisory wall-time, and feeds two
//! things:
//!
//! 1. **Longest-processing-time-first scheduling.** The recorded per-command
//!    wall-times feed a descending sort on the work queue
//!    ([`super::parallel::lpt_order`]) so the tail starts first. They are
//!    **scheduling hints only** and never enter the report (STYLE D1/D4).
//!    Times are keyed by **run mode** ([`mode_key`]) — a stage-1 time is not a
//!    hint for a counting run, which enumerates rather than solving once — and
//!    a capture carries the modes it did not measure forward, so one artifact
//!    accumulates the whole battery's schedule (mt-059).
//! 2. **Deltas for free (`--delta`).** [`SweepBaseline::delta`] diffs a finished
//!    report against the artifact, so "what changed" costs no second run.
//!
//! **Neither costs any coverage, so neither needs an opt-in.** The artifact
//! deliberately does not gate what the gauge *runs*: an earlier revision of this
//! bead let it skip commands recorded as capacity/over-budget defers, which was
//! deleted once command-level parallelism made the saving 6% — far too little to
//! pay for a lane that could hide a newly-solvable-and-newly-wrong command. Two
//! caches could disagree with each other; one cannot — hence the single file.
//!
//! **Anti-rot.** The header pins every config field that changes what a bucket
//! *means* (symmetry, the conflict/encode/primary-var budgets, overflow, the
//! jar-side solver, the mettle-side backend, and — when the run counts — the
//! counting budgets). It also *records* the backend's version
//! ([`SweepConfig::backend_signature`]) without comparing it: which solver
//! answered is identity, which build of it answered is provenance. A mismatch is
//! a **hard
//! error** whenever the artifact's *content* can reach the answer, which since
//! the skip lane's removal means exactly one consumer: `--delta`, whose whole
//! output is a comparison against these buckets. Diffing against buckets
//! produced at other budgets is a fabricated delta, so that fails loudly, as
//! [`super::count_baseline`] does. Without `--delta` the artifact can only
//! supply scheduling hints — nothing it says can reach the report — so a
//! mismatch downgrades to "ignored, with a warning". Hard-erroring there would
//! fail every deep-budget sweep over an artifact it was never going to consult.
//!
//! Everything is `BTreeMap`-ordered so the pretty JSON is byte-identical run to
//! run (STYLE D1); this module never prints (STYLE E3) — warnings are returned
//! for the caller to surface through its progress channel.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::error::ConformError;

use super::SolveGaugeReport;

/// `relpath[idx]` — the key both [`super::PerCommand`] and this artifact use.
#[must_use]
pub fn command_key(relpath: &str, idx: usize) -> String {
    format!("{relpath}[{idx}]")
}

/// The **scheduling mode** a recorded time belongs to (mt-059).
///
/// The same command costs wildly different amounts in a verdict-only run and in
/// a counting run, because a counting run *enumerates* it rather than solving it
/// once: `mesh.als[0]` is 0.7s in stage 1 and was 753s in the SB-0 counting net.
/// A time recorded in one mode is therefore not a hint for another — feeding
/// stage-1 times to a counting net's LPT schedules that net's true tail **last**,
/// the exact pathology mt-057 fixed for stage 1. Times are keyed by this string
/// so each run type schedules on its own measurements; a mode with no recording
/// is simply unknown (LPT dispatches unknowns first), never mis-hinted.
///
/// `--enumerate-all` is part of the key because it changes what a counting run
/// *does* — it re-enumerates the commands mt-059 settles from the baseline — so
/// its times are not the normal net's times either.
#[must_use]
pub fn mode_key(cfg: &SweepConfig) -> String {
    if !cfg.count_enabled {
        return "stage1".to_owned();
    }
    let all = if cfg.enumerate_all { "-all" } else { "" };
    format!("count-sb{}{all}", cfg.count_symmetry)
}

/// The backend an artifact that predates the field must have come from: mt-121
/// added `--solver` to the gauge, so every earlier capture is an own-solver one
/// by construction, not by assumption.
///
/// Deliberately the literal name, not `Backend::default().name()` — this states
/// a fact about the past, and must not move when the default backend does.
fn default_backend() -> String {
    "mettle".to_owned()
}

/// The `relpath` part of a `relpath[idx]` key (the whole key if it has no `[`).
fn relpath_of(key: &str) -> &str {
    key.rsplit_once('[').map_or(key, |(rel, _)| rel)
}

/// The pinned config a sweep baseline was captured at.
///
/// Every field except `capture_commit` is compared field-by-field against the
/// run at load; the count-only fields are compared only when both sides ran the
/// counting net (a stage-2 budget cannot change what a stage-1 bucket means).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SweepConfig {
    pub symmetry: u32,
    pub conflict_budget: u64,
    pub encode_budget: u64,
    pub primary_var_cap: usize,
    pub no_overflow: bool,
    /// The **jar-side** solver the counting net pins (see
    /// [`super::JAR_SOLVER`]). Constant today, and deliberately *not* mettle's
    /// own backend — that is [`Self::backend`]. The name predates there being
    /// two solver identities to tell apart; renaming it would invalidate every
    /// committed artifact for no gain.
    pub solver: String,
    /// Which mettle backend produced these buckets
    /// ([`als_core::Backend::name`]). Compared field-by-field like every other
    /// bucket-defining field: a run on one backend must never silently consume
    /// a baseline banked on another, because "which solver answered" changes
    /// which rows land in `over_budget` (ADR-0027 migration debt 2).
    ///
    /// Defaults to `mettle` for artifacts captured before mt-121, which is not
    /// a guess: the gauge had no `--solver` flag then, so every one of them is
    /// an own-solver capture by construction.
    #[serde(default = "default_backend")]
    pub backend: String,
    /// The versioned identity of that backend
    /// ([`als_core::Backend::version_signature`]) — `mettle-cdcl-0.1.1`,
    /// `cadical-1.9.5`. **Provenance, not identity**: it is written on every
    /// capture and never compared, because a crate-version bump on a rebuilt
    /// own solver must not orphan every baseline banked before it.
    ///
    /// `None` in artifacts captured before mt-121. No real signature is empty,
    /// so absence is its own answer rather than a blank string pretending to be
    /// one.
    #[serde(default)]
    pub backend_signature: Option<String>,
    /// Whether the capture ran stage 2. When false, `count_bucket` is absent
    /// everywhere and count deltas are unavailable.
    pub count_enabled: bool,
    pub count_symmetry: u32,
    pub count_cap: u64,
    pub enum_budget: u64,
    /// mt-059: whether the capture forced enumeration of commands the count
    /// baseline had already settled. It changes which `skip_*` bucket those
    /// commands land in, so — like the other stage-2 fields — a `--delta`
    /// against a capture that differs here would be a fabricated delta.
    /// `#[serde(default)]`: absent in pre-mt-059 artifacts, where it was false.
    #[serde(default)]
    pub enumerate_all: bool,
    /// The commit the artifact was captured at, for triage. Advisory only —
    /// never validated (every commit would otherwise be a hard error).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub capture_commit: Option<String>,
}

/// One command's recorded outcome plus its advisory cost.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SweepEntry {
    /// The verdict-stage bucket the command landed in.
    pub verdict_bucket: String,
    /// The counting-net bucket, when the capture ran stage 2 and covered it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub count_bucket: Option<String>,
    /// Wall time in **milliseconds**, rounded, for the mode the artifact's own
    /// header describes. A *scheduling hint only*: it is nondeterministic and
    /// must never reach report output (STYLE D1/D4). Integer milliseconds (not
    /// float seconds) so the LPT sort is a total order and the JSON is
    /// byte-stable.
    ///
    /// Kept alongside [`Self::ms_by_mode`] for backward compatibility: a
    /// pre-mt-059 artifact has only this field, and the loader folds it into the
    /// map under the mode its header pins ([`mode_key`]).
    #[serde(default)]
    pub ms: u64,
    /// mt-059: wall milliseconds **per scheduling mode** (`stage1`,
    /// `count-sb0`, …). One artifact accumulates every mode the battery runs,
    /// and each run reads only its own — a stage-1 time is not a hint for a
    /// counting run. Empty in a pre-mt-059 artifact until the loader migrates
    /// [`Self::ms`] into it.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub ms_by_mode: BTreeMap<String, u64>,
}

impl SweepEntry {
    /// This entry's timings with the legacy scalar [`Self::ms`] folded in under
    /// `mode` — the mode of the header that wrote it. An explicit `ms_by_mode`
    /// value always wins, so migrating twice is a no-op.
    fn timings(&self, mode: &str) -> BTreeMap<String, u64> {
        let mut by_mode = self.ms_by_mode.clone();
        by_mode.entry(mode.to_owned()).or_insert(self.ms);
        by_mode
    }
}

/// The whole on-disk artifact (`config` header + per-command entries keyed by
/// `relpath[idx]`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SweepBaselineFile {
    pub config: SweepConfig,
    pub entries: BTreeMap<String, SweepEntry>,
}

impl SweepBaselineFile {
    /// Renders the artifact as stable pretty JSON (`BTreeMap` key order).
    ///
    /// # Errors
    /// Only if serialization itself fails (allocation failure).
    pub fn to_json(&self) -> Result<String, ConformError> {
        Ok(serde_json::to_string_pretty(self)?)
    }

    /// Serializes and writes to `out_path` atomically (temp file in the same
    /// directory + rename), mirroring the count-baseline refresh writer.
    ///
    /// # Errors
    /// Serialization or I/O failure.
    pub fn write_atomic(&self, out_path: &Path) -> Result<(), ConformError> {
        let json = self.to_json()?;
        let tmp = out_path.with_extension("json.tmp");
        std::fs::write(&tmp, json)?;
        std::fs::rename(&tmp, out_path)?;
        Ok(())
    }
}

/// The merged artifact over every loaded `*-sweep-sb<N>.json`.
#[derive(Debug, Default)]
pub struct SweepBaseline {
    entries: BTreeMap<String, SweepEntry>,
    /// Names of the artifacts merged in (for the report header).
    pub loaded: Vec<String>,
    /// Non-fatal load warnings, for the caller to surface through its progress
    /// channel (this library never prints).
    pub warnings: Vec<String>,
    /// True only when *every* loaded artifact recorded stage-2 buckets.
    pub count_enabled: bool,
}

impl SweepBaseline {
    /// True when nothing loaded — LPT and deltas are both inert.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.loaded.is_empty()
    }

    /// The recorded cost of `relpath[idx]` **in `mode`** ([`mode_key`]), or
    /// `None` when the command has no recording for that mode (LPT then
    /// schedules it as "unknown", i.e. first).
    ///
    /// The unit is the **command**, not the file: the gauge's work queue is
    /// command-granular, and a file's cost can be dominated by one of its
    /// commands (`correctChord.als` sums to 556s across 39 commands, of which
    /// the worst single one is ~190s — scheduling by file total would put the
    /// whole chain on one worker).
    ///
    /// The unit is also the **mode** (mt-059): a stage-1 time answers only a
    /// stage-1 run. Returning `None` across modes is deliberate — an unmeasured
    /// command is scheduled first, which is neutral, whereas a stage-1 time fed
    /// to a counting net is actively wrong (`mesh.als[0]`: 0.7s vs 753s).
    #[must_use]
    pub fn command_millis(&self, relpath: &str, idx: usize, mode: &str) -> Option<u64> {
        self.entries
            .get(&command_key(relpath, idx))
            .and_then(|e| e.ms_by_mode.get(mode).copied())
    }

    /// Number of merged command entries (report diagnostics).
    #[must_use]
    pub fn command_count(&self) -> usize {
        self.entries.len()
    }

    /// Diffs a finished report against the artifact.
    ///
    /// Only files this run actually swept are considered "gone"-eligible, so a
    /// `--only`-filtered run does not report the whole rest of the corpus as
    /// deleted. Count buckets are compared only when both sides ran stage 2.
    #[must_use]
    pub fn delta(&self, report: &SolveGaugeReport) -> SweepDelta {
        let count_compared = report.count_enabled && self.count_enabled;
        let mut delta = SweepDelta {
            baseline_files: self.loaded.clone(),
            count_compared,
            ..SweepDelta::default()
        };

        let mut swept_files: BTreeSet<&str> = BTreeSet::new();
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        for pc in &report.per_command {
            swept_files.insert(relpath_of(&pc.key));
            seen.insert(pc.key.as_str());
            let Some(prev) = self.entries.get(&pc.key) else {
                delta.new_commands.push(pc.key.clone());
                continue;
            };
            let mut changed = false;
            if prev.verdict_bucket != pc.verdict_bucket {
                delta.changed.push(format!(
                    "{}: verdict {} -> {}",
                    pc.key, prev.verdict_bucket, pc.verdict_bucket
                ));
                changed = true;
            }
            if count_compared && prev.count_bucket != pc.count_bucket {
                delta.changed.push(format!(
                    "{}: count {} -> {}",
                    pc.key,
                    prev.count_bucket.as_deref().unwrap_or("<none>"),
                    pc.count_bucket.as_deref().unwrap_or("<none>")
                ));
                changed = true;
            }
            if !changed {
                delta.unchanged += 1;
            }
        }

        // A recorded command that this run swept the file of, but did not
        // produce — the command was removed or renumbered.
        for key in self.entries.keys() {
            if !seen.contains(key.as_str()) && swept_files.contains(relpath_of(key)) {
                delta.gone_commands.push(key.clone());
            }
        }
        delta
    }
}

/// What a run changed relative to the artifact (mt-057).
///
/// Deterministic by construction: `per_command` is filled in file-sorted,
/// index-ascending order and `entries` is a `BTreeMap`.
#[derive(Debug, Clone, Default, Serialize)]
pub struct SweepDelta {
    /// The artifacts the delta was taken against.
    pub baseline_files: Vec<String>,
    /// Whether count buckets took part (both sides ran stage 2).
    pub count_compared: bool,
    /// Commands whose bucket(s) match the artifact. Every swept command is
    /// verified — the gauge has no "assumed unchanged" category.
    pub unchanged: usize,
    /// One line per changed bucket, `key: verdict|count old -> new`.
    pub changed: Vec<String>,
    /// Commands this run produced that the artifact does not record.
    pub new_commands: Vec<String>,
    /// Commands the artifact records for a swept file that this run did not
    /// produce.
    pub gone_commands: Vec<String>,
}

impl SweepDelta {
    /// True when nothing moved (and nothing appeared or vanished).
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.changed.is_empty() && self.new_commands.is_empty() && self.gone_commands.is_empty()
    }
}

/// Builds the artifact for a finished run. `millis` maps `relpath[idx]` to the
/// command's measured wall time; a command with no measurement records `0`.
///
/// `prior` is the artifact already at the output path, if any: this run measured
/// exactly one mode, so the **other** modes' timings are carried forward rather
/// than erased (mt-059). Only timings are carried — every bucket comes from this
/// run, so a capture still records only what it observed.
#[must_use]
pub fn capture(
    config: SweepConfig,
    report: &SolveGaugeReport,
    millis: &BTreeMap<String, u64>,
    prior: Option<&SweepBaselineFile>,
) -> SweepBaselineFile {
    let mode = mode_key(&config);
    let prior_mode = prior.map(|p| mode_key(&p.config));
    let entries = report
        .per_command
        .iter()
        .map(|pc| {
            let ms = millis.get(&pc.key).copied().unwrap_or(0);
            let mut ms_by_mode = match (prior, &prior_mode) {
                (Some(p), Some(pm)) => p
                    .entries
                    .get(&pc.key)
                    .map(|e| e.timings(pm))
                    .unwrap_or_default(),
                _ => BTreeMap::new(),
            };
            ms_by_mode.insert(mode.clone(), ms);
            (
                pc.key.clone(),
                SweepEntry {
                    verdict_bucket: pc.verdict_bucket.clone(),
                    count_bucket: pc.count_bucket.clone(),
                    ms,
                    ms_by_mode,
                },
            )
        })
        .collect();
    SweepBaselineFile { config, entries }
}

/// Reads the artifact already at `path`, for [`capture`] to carry its other
/// modes' timings forward. Every failure — absent, unreadable, malformed — is
/// `None`: a capture must never fail because an old artifact is unusable, and
/// the worst case is losing advisory hints.
#[must_use]
pub fn read_prior(path: &Path) -> Option<SweepBaselineFile> {
    let text = std::fs::read_to_string(path).ok()?;
    serde_json::from_str(&text).ok()
}

/// Loads and merges every `*-sweep-sb<N>.json` (for `N = run.symmetry`) under
/// `baselines_dir`, validating each header against the run's pinned config.
///
/// Files are visited in sorted name order (deterministic merge; a later file
/// wins on a duplicate key). A missing directory yields an empty baseline (the
/// LPT and deltas both go inert — fail-safe: an unscheduled sweep, never a
/// wrong one); an
/// unreadable/malformed *file* is skipped with a warning.
///
/// **`strict` decides what a config mismatch costs**, and it must be set exactly
/// when the artifact's *content* bears on the answer. Since the skip lane was
/// removed there is one such consumer: **`--delta`**, whose entire output is a
/// comparison against these buckets, so a mismatch there is a **hard error** —
/// diffing against buckets produced at other budgets is a fabricated delta.
///
/// Without `--delta` the artifact supplies **scheduling hints only**: nothing it
/// says can reach the report, so a mismatch means the hints are merely
/// irrelevant, and the file is ignored with a warning rather than failing an
/// unrelated run. That distinction is not academic — a strict-always loader
/// makes *any* run at non-default budgets (a deep-budget sweep, the jar smoke
/// test) fail outright the moment an artifact is committed, over an artifact it
/// was never going to consult.
///
/// # Errors
/// [`ConformError::SweepBaselineConfigMismatch`] if `strict` and any loaded
/// artifact's header disagrees with the run on a field that changes what a
/// bucket means.
pub fn load_sweep_baselines(
    baselines_dir: &Path,
    run: &SweepConfig,
    strict: bool,
) -> Result<SweepBaseline, ConformError> {
    let mut baseline = SweepBaseline {
        count_enabled: true,
        ..SweepBaseline::default()
    };
    let suffix = format!("-sweep-sb{}.json", run.symmetry);
    let Ok(dir) = std::fs::read_dir(baselines_dir) else {
        baseline.count_enabled = false;
        return Ok(baseline);
    };
    let mut paths: Vec<_> = dir
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
            .unwrap_or("<sweep-baseline>")
            .to_owned();
        let Ok(text) = std::fs::read_to_string(path) else {
            baseline
                .warnings
                .push(format!("sweep baseline {name}: unreadable, skipped"));
            continue;
        };
        let Ok(file) = serde_json::from_str::<SweepBaselineFile>(&text) else {
            baseline
                .warnings
                .push(format!("sweep baseline {name}: malformed, skipped"));
            continue;
        };
        if let Some((field, expected, found)) = config_mismatch(&file.config, run) {
            if strict {
                return Err(ConformError::SweepBaselineConfigMismatch {
                    file: name,
                    field,
                    expected,
                    found,
                });
            }
            baseline.warnings.push(format!(
                "sweep baseline {name}: config field `{field}` differs (baseline={found}, run={expected}); ignored — without --delta it can only supply scheduling hints, and --delta would hard-error on it"
            ));
            continue;
        }
        if run.count_enabled && !file.config.count_enabled {
            baseline.warnings.push(format!(
                "sweep baseline {name}: captured without --count, so count deltas are unavailable"
            ));
        }
        baseline.count_enabled &= file.config.count_enabled;
        let file_mode = mode_key(&file.config);
        for (key, mut entry) in file.entries {
            // Buckets: later file wins outright. Timings: merged per mode, so
            // one file's stage-1 recording and another's counting recording both
            // survive (mt-059); within a mode the later file still wins.
            entry.ms_by_mode = entry.timings(&file_mode);
            if let Some(prev) = baseline.entries.get(&key) {
                for (mode, ms) in &prev.ms_by_mode {
                    entry.ms_by_mode.entry(mode.clone()).or_insert(*ms);
                }
            }
            baseline.entries.insert(key, entry);
        }
        baseline.loaded.push(name);
    }

    if baseline.loaded.is_empty() {
        baseline.count_enabled = false;
    }
    Ok(baseline)
}

/// The first field on which a loaded header disagrees with the run, as
/// `(field, run value, baseline value)` — or `None` when the artifact is
/// comparable. Pure: the *caller* decides whether a mismatch is fatal.
///
/// Stage-1 fields are always checked; stage-2 budgets only when both sides ran
/// the counting net (a counting budget cannot change what a stage-1 bucket
/// means, and a capture made without `--count` simply has no count buckets).
fn config_mismatch(
    header: &SweepConfig,
    run: &SweepConfig,
) -> Option<(&'static str, String, String)> {
    let stage1 = [
        (
            "symmetry",
            run.symmetry.to_string(),
            header.symmetry.to_string(),
        ),
        (
            "conflict_budget",
            run.conflict_budget.to_string(),
            header.conflict_budget.to_string(),
        ),
        (
            "encode_budget",
            run.encode_budget.to_string(),
            header.encode_budget.to_string(),
        ),
        (
            "primary_var_cap",
            run.primary_var_cap.to_string(),
            header.primary_var_cap.to_string(),
        ),
        (
            "no_overflow",
            run.no_overflow.to_string(),
            header.no_overflow.to_string(),
        ),
        ("solver", run.solver.clone(), header.solver.clone()),
        // The mettle-side backend. `backend_signature` is deliberately absent
        // from this list: it is provenance, and comparing it would orphan every
        // baseline the moment the crate version moves under a rebuilt own
        // solver (see `SweepConfig::backend_signature`).
        ("backend", run.backend.clone(), header.backend.clone()),
    ];
    if let Some(hit) = stage1.into_iter().find(|(_, run, base)| run != base) {
        return Some(hit);
    }
    if !run.count_enabled || !header.count_enabled {
        return None;
    }
    let stage2 = [
        (
            "count_symmetry",
            run.count_symmetry.to_string(),
            header.count_symmetry.to_string(),
        ),
        (
            "count_cap",
            run.count_cap.to_string(),
            header.count_cap.to_string(),
        ),
        (
            "enum_budget",
            run.enum_budget.to_string(),
            header.enum_budget.to_string(),
        ),
        (
            "enumerate_all",
            run.enumerate_all.to_string(),
            header.enumerate_all.to_string(),
        ),
    ];
    stage2.into_iter().find(|(_, run, base)| run != base)
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "test fixtures assert on known-good values"
)]
mod tests {
    use super::*;
    use crate::solve_gauge::PerCommand;

    fn header() -> SweepConfig {
        SweepConfig {
            symmetry: 20,
            conflict_budget: 10_000,
            encode_budget: 4_000_000,
            primary_var_cap: 20_000,
            no_overflow: true,
            solver: "sat4j".to_owned(),
            backend: "mettle".to_owned(),
            backend_signature: Some("mettle-cdcl-test".to_owned()),
            count_enabled: true,
            count_symmetry: 0,
            count_cap: 10_000,
            enum_budget: 250_000_000,
            enumerate_all: false,
            capture_commit: Some("deadbeef".to_owned()),
        }
    }

    /// A pre-mt-059-shaped entry: a bare `ms`, no mode map. The loader migrates
    /// it under the mode of the header it came with.
    fn entry(verdict: &str, count: Option<&str>, ms: u64) -> SweepEntry {
        SweepEntry {
            verdict_bucket: verdict.to_owned(),
            count_bucket: count.map(str::to_owned),
            ms,
            ms_by_mode: BTreeMap::new(),
        }
    }

    fn tmp_dir(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("als-sweep-bl-{tag}-{}", std::process::id()));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn report_with(per_command: Vec<PerCommand>, count_enabled: bool) -> SolveGaugeReport {
        SolveGaugeReport {
            commands: per_command.len(),
            baseline_files: vec![],
            count_baseline_files: vec![],
            baseline_entries: 0,
            verdict_buckets: BTreeMap::new(),
            disagreements: vec![],
            self_check_failures: vec![],
            panics: vec![],
            symmetry: 20,
            count_symmetry: 0,
            count_enabled,
            count_buckets: BTreeMap::new(),
            count_mismatches: vec![],
            per_command,
            partial: false,
            fail_fast_trigger: None,
            delta: None,
        }
    }

    fn pc(key: &str, verdict: &str, count: Option<&str>) -> PerCommand {
        PerCommand {
            key: key.to_owned(),
            verdict_bucket: verdict.to_owned(),
            count_bucket: count.map(str::to_owned),
        }
    }

    #[test]
    fn round_trip_write_then_load() {
        let dir = tmp_dir("rt");
        let mut entries = BTreeMap::new();
        entries.insert(
            "a.als[0]".to_owned(),
            entry("agree_sat", Some("count_match"), 1_234),
        );
        entries.insert(
            "a.als[1]".to_owned(),
            entry("mettle_defer:capacity", None, 183_000),
        );
        entries.insert(
            "b.als[0]".to_owned(),
            entry("mettle_defer:over_budget", None, 175_500),
        );
        let file = SweepBaselineFile {
            config: header(),
            entries,
        };
        file.write_atomic(&dir.join("x-sweep-sb20.json")).unwrap();

        let loaded = load_sweep_baselines(&dir, &header(), true).unwrap();
        assert_eq!(loaded.loaded, vec!["x-sweep-sb20.json".to_owned()]);
        assert_eq!(loaded.command_count(), 3);
        assert!(loaded.count_enabled);
        assert!(loaded.warnings.is_empty());

        // Cost is per command, not per file — the work queue is command-granular.
        let mode = mode_key(&header());
        assert_eq!(mode, "count-sb0");
        assert_eq!(loaded.command_millis("a.als", 0, &mode), Some(1_234));
        assert_eq!(loaded.command_millis("a.als", 1, &mode), Some(183_000));
        assert_eq!(loaded.command_millis("b.als", 0, &mode), Some(175_500));
        assert_eq!(loaded.command_millis("a.als", 9, &mode), None);
        assert_eq!(loaded.command_millis("nope.als", 0, &mode), None);
        // …and per mode: these are a counting run's times, so a stage-1 run
        // (or the other counting symmetry) is told nothing rather than lied to.
        assert_eq!(loaded.command_millis("a.als", 0, "stage1"), None);
        assert_eq!(loaded.command_millis("a.als", 0, "count-sb20"), None);

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn writer_output_is_byte_stable() {
        // Same content built in a different insertion order must serialize
        // identically (BTreeMap key order — STYLE D1).
        let mut a = BTreeMap::new();
        a.insert("z.als[0]".to_owned(), entry("agree_sat", None, 5));
        a.insert("a.als[0]".to_owned(), entry("agree_unsat", None, 7));
        let mut b = BTreeMap::new();
        b.insert("a.als[0]".to_owned(), entry("agree_unsat", None, 7));
        b.insert("z.als[0]".to_owned(), entry("agree_sat", None, 5));
        let fa = SweepBaselineFile {
            config: header(),
            entries: a,
        };
        let fb = SweepBaselineFile {
            config: header(),
            entries: b,
        };
        assert_eq!(fa.to_json().unwrap(), fb.to_json().unwrap());
    }

    #[test]
    fn missing_dir_is_inert_not_an_error() {
        let loaded =
            load_sweep_baselines(Path::new("/nonexistent/als-sweep-bl"), &header(), true).unwrap();
        assert!(loaded.is_empty());
        assert!(!loaded.count_enabled);
        assert_eq!(loaded.command_millis("a.als", 0, "stage1"), None);
    }

    #[test]
    fn stage1_config_mismatch_is_hard_error() {
        let dir = tmp_dir("mm1");
        let mut cfg = header();
        cfg.encode_budget = 8_000_000; // widened budgets could solve a capped command
        SweepBaselineFile {
            config: cfg,
            entries: BTreeMap::new(),
        }
        .write_atomic(&dir.join("y-sweep-sb20.json"))
        .unwrap();

        let err = load_sweep_baselines(&dir, &header(), true).unwrap_err();
        match err {
            ConformError::SweepBaselineConfigMismatch { field, .. } => {
                assert_eq!(field, "encode_budget");
            }
            other => panic!("expected encode_budget mismatch, got {other:?}"),
        }
        std::fs::remove_dir_all(&dir).ok();
    }

    /// A baseline banked on one backend is refused by a run on another, through
    /// the same loud path every other bucket-defining field uses (ADR-0027
    /// migration debt 2). Silently consuming it would diff one solver's buckets
    /// against the other's and call the difference a regression.
    #[test]
    fn a_baseline_from_another_backend_is_refused() {
        let dir = tmp_dir("mm-backend");
        let mut cfg = header();
        cfg.backend = "cadical".to_owned();
        cfg.backend_signature = Some("cadical-1.9.5".to_owned());
        SweepBaselineFile {
            config: cfg,
            entries: BTreeMap::new(),
        }
        .write_atomic(&dir.join("y-sweep-sb20.json"))
        .unwrap();

        let err = load_sweep_baselines(&dir, &header(), true).unwrap_err();
        match err {
            ConformError::SweepBaselineConfigMismatch {
                field,
                expected,
                found,
                ..
            } => {
                assert_eq!(field, "backend");
                assert_eq!((expected.as_str(), found.as_str()), ("mettle", "cadical"));
            }
            other => panic!("expected a backend mismatch, got {other:?}"),
        }
        // Without --delta it is the usual downgrade: ignored, with a warning.
        let loaded = load_sweep_baselines(&dir, &header(), false).unwrap();
        assert!(loaded.warnings[0].contains("backend"));
        std::fs::remove_dir_all(&dir).ok();
    }

    /// The signature is provenance, not identity: a rebuilt own solver with a
    /// bumped crate version must not orphan every baseline banked before it.
    #[test]
    fn a_differing_backend_signature_alone_is_not_a_mismatch() {
        let mut older = header();
        older.backend_signature = Some("mettle-cdcl-0.0.9".to_owned());
        let mut newer = header();
        newer.backend_signature = Some("mettle-cdcl-9.9.9".to_owned());
        assert_eq!(config_mismatch(&older, &newer), None);
        assert_eq!(config_mismatch(&newer, &older), None);
    }

    /// An artifact banked before mt-121 has no backend fields. It must still
    /// load — `baselines/*-sweep-sb20.json` is one — and it must read as the own
    /// solver, which is what produced it: the gauge had no `--solver` then.
    #[test]
    fn a_pre_mt121_header_reads_as_the_own_solver() {
        let json = r#"{
          "config": {
            "symmetry": 20, "conflict_budget": 10000, "encode_budget": 4000000,
            "primary_var_cap": 20000, "no_overflow": true, "solver": "sat4j",
            "count_enabled": true, "count_symmetry": 0, "count_cap": 10000,
            "enum_budget": 250000000, "enumerate_all": false,
            "capture_commit": "deadbeef"
          },
          "entries": {}
        }"#;
        let file: SweepBaselineFile = serde_json::from_str(json).unwrap();
        assert_eq!(file.config.backend, "mettle");
        assert_eq!(
            file.config.backend_signature, None,
            "an unrecorded signature stays unrecorded rather than being invented"
        );
        // And it therefore still matches an own-solver run of the same config.
        assert_eq!(config_mismatch(&file.config, &header()), None);
    }

    /// The other half of the strictness rule: when nothing the artifact says can
    /// reach the report, a stale header must not fail the run.
    #[test]
    fn non_strict_load_ignores_a_mismatched_header() {
        let dir = tmp_dir("lenient");
        let mut cfg = header();
        cfg.conflict_budget = 200_000; // e.g. the jar smoke test's budgets
        let mut entries = BTreeMap::new();
        entries.insert(
            "a.als[0]".to_owned(),
            entry("mettle_defer:capacity", None, 5),
        );
        SweepBaselineFile {
            config: cfg,
            entries,
        }
        .write_atomic(&dir.join("y-sweep-sb20.json"))
        .unwrap();

        let loaded = load_sweep_baselines(&dir, &header(), false).unwrap();
        assert!(loaded.is_empty(), "the artifact must not be merged");
        assert_eq!(loaded.warnings.len(), 1);
        assert!(loaded.warnings[0].contains("conflict_budget"));
        // Nothing from it can leak into scheduling either.
        assert_eq!(
            loaded.command_millis("a.als", 0, &mode_key(&header())),
            None
        );

        // The same file under --delta is still a hard error.
        assert!(load_sweep_baselines(&dir, &header(), true).is_err());
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn count_config_mismatch_only_bites_a_counting_run() {
        let dir = tmp_dir("mm2");
        let mut cfg = header();
        cfg.count_cap = 999;
        SweepBaselineFile {
            config: cfg,
            entries: BTreeMap::new(),
        }
        .write_atomic(&dir.join("y-sweep-sb20.json"))
        .unwrap();

        // A stage-1-only run does not care what the counting cap was.
        let mut run = header();
        run.count_enabled = false;
        assert!(load_sweep_baselines(&dir, &run, true).is_ok());

        // A counting run does.
        let err = load_sweep_baselines(&dir, &header(), true).unwrap_err();
        assert!(matches!(
            err,
            ConformError::SweepBaselineConfigMismatch {
                field: "count_cap",
                ..
            }
        ));
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn countless_capture_warns_instead_of_erroring() {
        let dir = tmp_dir("nocount");
        let mut cfg = header();
        cfg.count_enabled = false;
        cfg.count_cap = 1; // a stage-2 field that disagrees, but is unmeaning here
        SweepBaselineFile {
            config: cfg,
            entries: BTreeMap::new(),
        }
        .write_atomic(&dir.join("y-sweep-sb20.json"))
        .unwrap();

        let loaded = load_sweep_baselines(&dir, &header(), true).unwrap();
        assert_eq!(loaded.warnings.len(), 1);
        assert!(loaded.warnings[0].contains("without --count"));
        assert!(!loaded.count_enabled);
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn malformed_file_is_a_warning_not_an_error() {
        let dir = tmp_dir("bad");
        std::fs::write(dir.join("bad-sweep-sb20.json"), "{ not json").unwrap();
        let loaded = load_sweep_baselines(&dir, &header(), true).unwrap();
        assert!(loaded.is_empty());
        assert_eq!(loaded.warnings.len(), 1);
        assert!(loaded.warnings[0].contains("malformed"));
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn later_file_wins_on_duplicate_key() {
        let dir = tmp_dir("merge");
        let mut a = BTreeMap::new();
        a.insert(
            "a.als[0]".to_owned(),
            entry("mettle_defer:capacity", None, 10),
        );
        SweepBaselineFile {
            config: header(),
            entries: a,
        }
        .write_atomic(&dir.join("a-sweep-sb20.json"))
        .unwrap();
        let mut b = BTreeMap::new();
        b.insert("a.als[0]".to_owned(), entry("agree_sat", None, 20));
        SweepBaselineFile {
            config: header(),
            entries: b,
        }
        .write_atomic(&dir.join("b-sweep-sb20.json"))
        .unwrap();

        let loaded = load_sweep_baselines(&dir, &header(), true).unwrap();
        assert_eq!(loaded.loaded.len(), 2);
        // b- sorts after a-, so its entry wins.
        assert_eq!(
            loaded.command_millis("a.als", 0, &mode_key(&header())),
            Some(20)
        );
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn delta_reports_moves_arrivals_and_departures() {
        let mut entries = BTreeMap::new();
        entries.insert(
            "a.als[0]".to_owned(),
            entry("agree_sat", Some("count_match"), 1),
        );
        entries.insert(
            "a.als[1]".to_owned(),
            entry("mettle_defer:capacity", None, 2),
        );
        entries.insert("a.als[2]".to_owned(), entry("agree_unsat", None, 3));
        entries.insert("gone.als[0]".to_owned(), entry("agree_sat", None, 4));
        let baseline = SweepBaseline {
            entries,
            loaded: vec!["x-sweep-sb20.json".to_owned()],
            warnings: vec![],
            count_enabled: true,
        };

        let report = report_with(
            vec![
                // unchanged
                pc("a.als[0]", "agree_sat", Some("count_match")),
                // still capped: unchanged, and verified rather than assumed
                pc("a.als[1]", "mettle_defer:capacity", None),
                // moved
                pc("a.als[2]", "agree_sat", None),
                // brand new
                pc("a.als[3]", "agree_sat", None),
            ],
            true,
        );

        let d = baseline.delta(&report);
        assert_eq!(d.unchanged, 2);
        assert_eq!(
            d.changed,
            vec!["a.als[2]: verdict agree_unsat -> agree_sat"]
        );
        assert_eq!(d.new_commands, vec!["a.als[3]"]);
        // gone.als was not swept by this run, so it is filtered-out, not gone.
        assert!(d.gone_commands.is_empty());
        assert!(!d.is_clean());
    }

    #[test]
    fn delta_flags_a_removed_command_of_a_swept_file() {
        let mut entries = BTreeMap::new();
        entries.insert("a.als[0]".to_owned(), entry("agree_sat", None, 1));
        entries.insert("a.als[1]".to_owned(), entry("agree_sat", None, 1));
        let baseline = SweepBaseline {
            entries,
            loaded: vec!["x-sweep-sb20.json".to_owned()],
            warnings: vec![],
            count_enabled: true,
        };
        let report = report_with(vec![pc("a.als[0]", "agree_sat", None)], true);
        let d = baseline.delta(&report);
        assert_eq!(d.gone_commands, vec!["a.als[1]"]);
    }

    #[test]
    fn count_delta_is_skipped_when_either_side_lacks_counts() {
        let mut entries = BTreeMap::new();
        entries.insert(
            "a.als[0]".to_owned(),
            entry("agree_sat", Some("count_match"), 1),
        );
        let baseline = SweepBaseline {
            entries,
            loaded: vec!["x-sweep-sb20.json".to_owned()],
            warnings: vec![],
            count_enabled: true,
        };
        // This run did not count, so the vanished count bucket is not a change.
        let report = report_with(vec![pc("a.als[0]", "agree_sat", None)], false);
        let d = baseline.delta(&report);
        assert!(!d.count_compared);
        assert!(d.is_clean());
        assert_eq!(d.unchanged, 1);
    }

    /// mt-059: the committed artifact predates `ms_by_mode`, so its bare `ms`
    /// must keep scheduling the mode it was captured in — and only that mode.
    #[test]
    fn a_legacy_ms_is_migrated_under_its_own_headers_mode() {
        let dir = tmp_dir("legacy");
        let mut cfg = header();
        cfg.count_enabled = false; // as captured by a stage-1-only run
        let mut entries = BTreeMap::new();
        entries.insert("a.als[0]".to_owned(), entry("agree_sat", None, 738));
        SweepBaselineFile {
            config: cfg,
            entries,
        }
        .write_atomic(&dir.join("legacy-sweep-sb20.json"))
        .unwrap();

        let mut stage1 = header();
        stage1.count_enabled = false;
        let loaded = load_sweep_baselines(&dir, &stage1, false).unwrap();
        assert_eq!(loaded.command_millis("a.als", 0, "stage1"), Some(738));
        // `mesh.als[0]` is the cautionary tale: 738ms in stage 1, 753_000ms in
        // the SB-0 counting net. A counting run must be told nothing here.
        assert_eq!(loaded.command_millis("a.als", 0, "count-sb0"), None);
        std::fs::remove_dir_all(&dir).ok();
    }

    /// One artifact accumulates the whole battery: capturing a counting run over
    /// a stage-1 capture keeps both modes' times, and each mode reads its own.
    #[test]
    fn a_capture_carries_the_modes_it_did_not_measure_forward() {
        let mut stage1_cfg = header();
        stage1_cfg.count_enabled = false;
        let report = report_with(vec![pc("a.als[0]", "agree_sat", None)], false);
        let mut millis = BTreeMap::new();
        millis.insert("a.als[0]".to_owned(), 738);
        let first = capture(stage1_cfg, &report, &millis, None);
        assert_eq!(first.entries["a.als[0]"].ms_by_mode["stage1"], 738);

        // Now the SB-0 counting net captures over it: 753s for the same command.
        let count_report = report_with(
            vec![pc("a.als[0]", "agree_sat", Some("skip_jar_timeout"))],
            true,
        );
        let mut count_millis = BTreeMap::new();
        count_millis.insert("a.als[0]".to_owned(), 753_100);
        let second = capture(header(), &count_report, &count_millis, Some(&first));
        let by_mode = &second.entries["a.als[0]"].ms_by_mode;
        assert_eq!(by_mode["stage1"], 738, "the stage-1 time must survive");
        assert_eq!(by_mode["count-sb0"], 753_100);
        // The buckets, unlike the times, are wholly this run's.
        assert_eq!(
            second.entries["a.als[0]"].count_bucket.as_deref(),
            Some("skip_jar_timeout")
        );
        assert_eq!(second.entries["a.als[0]"].ms, 753_100);
    }

    /// `--enumerate-all` is a different run: its times are not the normal net's,
    /// and a `--delta` across the switch would compare different skip buckets.
    #[test]
    fn enumerate_all_is_its_own_mode_and_its_own_delta_domain() {
        let base = header();
        let mut all = header();
        all.enumerate_all = true;
        assert_eq!(mode_key(&base), "count-sb0");
        assert_eq!(mode_key(&all), "count-sb0-all");
        assert_eq!(
            config_mismatch(&all, &base).map(|(f, _, _)| f),
            Some("enumerate_all")
        );
        // …but only for a counting run: it cannot change a stage-1 bucket.
        let mut stage1 = header();
        stage1.count_enabled = false;
        assert_eq!(config_mismatch(&all, &stage1), None);
    }

    #[test]
    fn capture_round_trips_through_a_report() {
        let report = report_with(
            vec![
                pc("a.als[0]", "agree_sat", Some("count_match")),
                pc("a.als[1]", "mettle_defer:capacity", None),
            ],
            true,
        );
        let mut millis = BTreeMap::new();
        millis.insert("a.als[0]".to_owned(), 42);
        let file = capture(header(), &report, &millis, None);
        assert_eq!(file.entries.len(), 2);
        assert_eq!(file.entries["a.als[0]"].ms, 42);
        // A command with no measurement records 0 rather than being dropped.
        assert_eq!(file.entries["a.als[1]"].ms, 0);
        assert_eq!(
            file.entries["a.als[1]"].verdict_bucket,
            "mettle_defer:capacity"
        );

        let text = file.to_json().unwrap();
        let back: SweepBaselineFile = serde_json::from_str(&text).unwrap();
        assert_eq!(back, file);
    }
}
