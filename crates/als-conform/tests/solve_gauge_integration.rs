//! Integration smoke for the mt-037 solve gauge + SB-0 counting net, driving
//! the *real* reference jar. Skips cleanly (not fails) when the jar is absent
//! (CI has no JDK), matching `oracle_integration.rs`.
//!
//! Pins the golden from the task spec on the crate fixture `test1.als` at `--count`:
//! - `run show` (`run { some r } for 3`) has no skolemizable existential and no
//!   ordered-abstract partition, so it reaches the net and its SB-0 count
//!   matches the jar exactly (1129 = 1129) → `count_match`;
//! - `check NoEmpty` (`all b: B | some b.r`, negated) is a first-order top-level
//!   existential that mettle now skolemizes at depth 0 (mt-047), so its SB-0 count
//!   matches the jar too (561 = 561) → `count_match` (was `skip_fo_skolem`).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Duration;

use als_conform::{
    refresh_counts, run_gauge, GaugeConfig, SweepBaselineFile, SweepConfig, SweepEntry,
    TelemetrySink,
};

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn jar_path() -> PathBuf {
    workspace_root().join("oracle/org.alloytools.alloy.dist.jar")
}

fn test1_config() -> GaugeConfig {
    let root = workspace_root();
    GaugeConfig {
        roots: vec![root.join("crates/als-conform/fixtures/test1.als")],
        workspace_root: root.clone(),
        baselines_dir: root.join("baselines"),
        conflict_budget: 200_000,
        encode_budget: 50_000_000,
        primary_var_cap: 200_000,
        allow_overflow: false,
        symmetry: 20,
        count_symmetry: 0,
        count: true,
        count_cap: 10_000,
        enum_budget: 2_000_000,
        enumerate_all: false,
        jar_path: jar_path(),
        shim_source: PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/shim/OracleShim.java")),
        jar_timeout: Duration::from_mins(5),
        jobs: 1,
        // The smoke pins the golden against the *live* jar counts (1129/561), so
        // stage 2 must run the live JVM path rather than a cached baseline.
        live_jar: true,
        fail_fast: false,
        only: Vec::new(),
        from_report: None,
        from_buckets: Vec::new(),
        delta: false,
        capture_sweep: None,
        capture_commit: None,
    }
}

#[test]
fn test1_count_smoke_matches_jar() {
    if !jar_path().is_file() {
        eprintln!(
            "SKIP {}: reference jar not found at {} (expected for CI)",
            module_path!(),
            jar_path().display()
        );
        return;
    }

    let report = run_gauge(&test1_config(), None, &mut |_| {})
        .unwrap_or_else(|e| panic!("run_gauge failed: {e}"));

    assert_eq!(report.commands, 2, "test1.als has two commands");
    // Both commands reach the net and match the jar's SB-0 count exactly:
    // `run show` at 1129, and `check NoEmpty` at 561 now that mt-047 skolemizes
    // its top-level first-order existential (was the `skip_fo_skolem` divergence).
    assert_eq!(
        report.count_buckets.get("count_match"),
        Some(&2),
        "both commands must land count_match (1129=1129, 561=561); buckets={:?}",
        report.count_buckets
    );
    assert_eq!(
        report.count_buckets.get("skip_fo_skolem"),
        None,
        "skip_fo_skolem is retired (mt-047); buckets={:?}",
        report.count_buckets
    );
    assert!(
        report.count_mismatches.is_empty(),
        "no count mismatch expected: {:?}",
        report.count_mismatches
    );
    assert!(report.self_check_failures.is_empty());
    assert!(report.panics.is_empty());
}

/// mt-076: temporal counting posture, **inverted**. `skip_temporal_trace` is
/// retired — `leader.als`'s two real cached jar counts (probe T-26 reproduced
/// the jar's own SB-0 `count:1` for commands 1 and 3 live) are now *compared*,
/// and mettle's own trace enumeration reproduces them. This is the single
/// sharpest live check that `als_core`'s [`TraceEnumerator`] walks the same set
/// the jar's `next()`-until-UNSAT loop does: the number is 1, and 1 is only
/// right if the configuration-hold and the across-length de-duplication are
/// both right.
///
/// Jar-free (cached committed baselines, no live JVM). What it pins, in order:
/// nothing lands in the retired bucket; the two comparable commands match; the
/// third is the *existing* typed `skip_enum_budget`, not a new bucket and not a
/// fabricated count; no mismatch is manufactured.
#[test]
fn leader_als_counts_match_its_real_jar_baseline() {
    let root = workspace_root();
    let leader = root.join("corpus/alloytools-models/models/examples/temporal/leader.als");
    // Same posture as every corpus-driven test (corpus/ is git-ignored, so CI
    // never has it): skip cleanly with a note, never fail.
    if !leader.is_file() {
        eprintln!(
            "SKIP leader_als_counts_match_its_real_jar_baseline: {} not present \
             (expected for a fresh checkout; run the corpus fetch script to enable)",
            leader.display()
        );
        return;
    }
    let cfg = GaugeConfig {
        roots: vec![leader],
        workspace_root: root.clone(),
        baselines_dir: root.join("baselines"),
        conflict_budget: 10_000,
        encode_budget: 4_000_000,
        primary_var_cap: 20_000,
        allow_overflow: false,
        symmetry: 20,
        count_symmetry: 0,
        count: true,
        count_cap: 10_000,
        // The sweep's own default, deliberately: measured, a smaller budget
        // pushes commands 1 and 3 into `skip_enum_budget` too (their counts are
        // 1, but reaching that answer still means sweeping every length in a
        // `10 steps` range), which would gut the test. This is the slowest test
        // in the workspace as a result — a couple of minutes in a debug build —
        // and it earns it: it is the only live check that mettle's trace
        // enumeration walks the same set the jar's does.
        enum_budget: 250_000_000,
        enumerate_all: false,
        jar_path: jar_path(),
        shim_source: PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/shim/OracleShim.java")),
        jar_timeout: Duration::from_mins(5),
        // Four workers, one per command: the gauge's stdout and JSON are
        // byte-identical at any `--jobs` for a FULL run, and this is the
        // slowest test in the workspace (mt-076's enumeration runs on top of
        // the verdict sweep), so there is no reason to serialize it.
        jobs: 4,
        // Cached committed baselines only — this test must not need a JDK.
        live_jar: false,
        fail_fast: false,
        only: Vec::new(),
        from_report: None,
        from_buckets: Vec::new(),
        delta: false,
        capture_sweep: None,
        capture_commit: None,
    };

    let report =
        run_gauge(&cfg, None, &mut |_| {}).unwrap_or_else(|e| panic!("run_gauge failed: {e}"));

    assert_eq!(report.commands, 4, "leader.als has four commands");
    // Three commands solve SAT at default budgets (run$1, example, liveness);
    // `safety` is a known over_budget row (mt-069 workstream 4).
    assert_eq!(
        report.verdict_buckets.get("agree_sat"),
        Some(&3),
        "buckets={:?}",
        report.verdict_buckets
    );
    assert_eq!(
        report.count_buckets.get("skip_temporal_trace"),
        None,
        "mt-076 retired the bucket outright; buckets={:?}",
        report.count_buckets
    );
    assert_eq!(
        report.count_buckets.get("count_match"),
        Some(&2),
        "commands 1 and 3 have real cached jar counts (both 1) and mettle's \
         trace enumeration reproduces them; buckets={:?}",
        report.count_buckets
    );
    assert_eq!(
        report.count_buckets.get("skip_enum_budget"),
        Some(&1),
        "command 0's space is past the enumeration budget — the EXISTING typed \
         skip, never a new bucket and never a truncated count; buckets={:?}",
        report.count_buckets
    );
    assert!(
        report.count_mismatches.is_empty(),
        "the real count baseline entry must never surface as a mismatch: {:?}",
        report.count_mismatches
    );
}

/// mt-054 (b): `--refresh-counts` writes a valid count baseline for a single
/// small file, and `--resume` on the already-complete output re-runs nothing.
#[test]
fn refresh_counts_resume_smoke() {
    if !jar_path().is_file() {
        eprintln!(
            "SKIP {}: reference jar not found at {} (expected for CI)",
            module_path!(),
            jar_path().display()
        );
        return;
    }

    let out = std::env::temp_dir().join(format!(
        "als-refresh-resume-{}-count-sb0.json",
        std::process::id()
    ));
    let _ = std::fs::remove_file(&out);

    // A fast, single-file corpus: the crate fixture test1.als.
    let cfg = test1_config();

    // First pass populates the baseline.
    refresh_counts(&cfg, &out, false, &mut |_| {}).unwrap_or_else(|e| panic!("refresh: {e}"));
    let first = std::fs::read_to_string(&out).expect("baseline written");
    let value: serde_json::Value = serde_json::from_str(&first).expect("valid json");
    assert_eq!(
        value["config"]["count_cap"], 10_000,
        "config header pins count_cap"
    );
    assert!(
        value["entries"]
            .as_object()
            .is_some_and(|m| m.contains_key("crates/als-conform/fixtures/test1.als")),
        "test1.als recorded: {value}"
    );

    // Second pass with --resume: the file is already present, so nothing re-runs
    // and the output is byte-identical.
    refresh_counts(&cfg, &out, true, &mut |_| {}).unwrap_or_else(|e| panic!("resume: {e}"));
    let second = std::fs::read_to_string(&out).expect("baseline still there");
    assert_eq!(first, second, "resume must not change a complete baseline");

    std::fs::remove_file(&out).ok();
}

// ---------------------------------------------------------------------------
// mt-057: the sweep-baseline artifact. These need no jar — stage 1 only, with
// an empty baselines dir (every command is `no_baseline`), over the crate's own
// `fixtures/` corpus.
// ---------------------------------------------------------------------------

fn scratch_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("als-sweep-it-{tag}-{}", std::process::id()));
    std::fs::remove_dir_all(&dir).ok();
    std::fs::create_dir_all(&dir).expect("scratch dir");
    dir
}

/// Stage-1-only config over the crate fixtures, with `baselines_dir` pointed at
/// a scratch directory the test owns.
fn fixtures_config(baselines_dir: &Path, jobs: usize) -> GaugeConfig {
    let root = workspace_root();
    GaugeConfig {
        roots: vec![root.join("crates/als-conform/fixtures")],
        workspace_root: root,
        baselines_dir: baselines_dir.to_path_buf(),
        conflict_budget: 10_000,
        encode_budget: 4_000_000,
        primary_var_cap: 20_000,
        allow_overflow: false,
        symmetry: 20,
        count_symmetry: 0,
        count: false,
        count_cap: 10_000,
        enum_budget: 250_000_000,
        enumerate_all: false,
        jar_path: jar_path(),
        shim_source: PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/shim/OracleShim.java")),
        jar_timeout: Duration::from_mins(5),
        jobs,
        live_jar: false,
        fail_fast: false,
        only: Vec::new(),
        from_report: None,
        from_buckets: Vec::new(),
        delta: false,
        capture_sweep: None,
        capture_commit: None,
    }
}

/// The header a `fixtures_config` run pins, so a hand-built artifact loads.
fn fixtures_header() -> SweepConfig {
    SweepConfig {
        symmetry: 20,
        conflict_budget: 10_000,
        encode_budget: 4_000_000,
        primary_var_cap: 20_000,
        no_overflow: true,
        solver: "sat4j".to_owned(),
        count_enabled: false,
        count_symmetry: 0,
        count_cap: 10_000,
        enum_budget: 250_000_000,
        enumerate_all: false,
        capture_commit: None,
    }
}

fn write_artifact(dir: &Path, entries: BTreeMap<String, SweepEntry>) {
    SweepBaselineFile {
        config: fixtures_header(),
        entries,
    }
    .write_atomic(&dir.join("fixtures-sweep-sb20.json"))
    .expect("artifact written");
}

/// The central mt-057 contract: **the artifact never changes what the gauge
/// reports.** Even an artifact that claims a command is a hopeless capacity
/// defer buys it nothing — the command is still swept and still lands in its
/// real bucket. This is what makes the canonical sweep hash in
/// `docs/MIGRATION.md` reproduce with an artifact committed, and it is the
/// property an earlier revision of this bead traded away for 6% and got back.
#[test]
fn an_artifact_never_changes_the_report() {
    let dir = scratch_dir("inert");

    // No artifact yet — the canonical report.
    let canonical = run_gauge(&fixtures_config(&dir, 1), None, &mut |_| {}).expect("canonical run");
    assert!(canonical.commands >= 2, "fixtures have commands to sweep");
    let canonical_text = canonical.render_text();
    let canonical_json = canonical.to_json().expect("json");

    // Record every command as a capacity defer — the strongest claim the
    // artifact can make, and the one the deleted skip lane acted on.
    let entries: BTreeMap<String, SweepEntry> = canonical
        .per_command
        .iter()
        .enumerate()
        .map(|(i, pc)| {
            (
                pc.key.clone(),
                SweepEntry {
                    verdict_bucket: "mettle_defer:capacity".to_owned(),
                    count_bucket: None,
                    ms: 1_000 * (i as u64 + 1),
                    ms_by_mode: BTreeMap::new(),
                },
            )
        })
        .collect();
    write_artifact(&dir, entries);

    let with_artifact =
        run_gauge(&fixtures_config(&dir, 1), None, &mut |_| {}).expect("run w/ artifact");
    assert_eq!(
        with_artifact.commands, canonical.commands,
        "no command disappears"
    );
    assert_eq!(
        with_artifact.render_text(),
        canonical_text,
        "an artifact must not move a byte of the report"
    );
    assert_eq!(
        with_artifact.to_json().expect("json"),
        canonical_json,
        "nor a byte of the JSON"
    );
    assert!(
        !with_artifact
            .verdict_buckets
            .keys()
            .any(|b| b.starts_with("skip_known")),
        "no skip bucket exists any more: {:?}",
        with_artifact.verdict_buckets
    );
    // STYLE I1: the partition holds.
    let sum: usize = with_artifact.verdict_buckets.values().sum();
    assert_eq!(sum, with_artifact.commands);

    // `--full` / `--recheck-capacity` survive only as no-op aliases, so a run
    // that passes them is the same run.
    std::fs::remove_dir_all(&dir).ok();
}

/// mt-057: LPT reordering is driven by the recorded times, and the report stays
/// byte-identical at any `--jobs`.
#[test]
fn lpt_scheduling_never_moves_a_byte_at_any_job_count() {
    let dir = scratch_dir("lpt");
    let seed = run_gauge(&fixtures_config(&dir, 1), None, &mut |_| {}).expect("seed run");

    // Deliberately inverted costs, so LPT schedules the queue backwards.
    let n = seed.per_command.len() as u64;
    let entries: BTreeMap<String, SweepEntry> = seed
        .per_command
        .iter()
        .enumerate()
        .map(|(i, pc)| {
            (
                pc.key.clone(),
                SweepEntry {
                    verdict_bucket: pc.verdict_bucket.clone(),
                    count_bucket: None,
                    ms: (n - i as u64) * 10_000,
                    ms_by_mode: BTreeMap::new(),
                },
            )
        })
        .collect();
    write_artifact(&dir, entries);

    let baseline_text = seed.render_text();
    for jobs in [1, 2, 4] {
        let cfg = fixtures_config(&dir, jobs);
        let r = run_gauge(&cfg, None, &mut |_| {}).expect("lpt run");
        assert_eq!(
            r.render_text(),
            baseline_text,
            "LPT dispatch at --jobs {jobs} must not move a byte"
        );
        assert_eq!(
            r.to_json().expect("json"),
            seed.to_json().expect("json"),
            "the JSON report must be byte-identical too"
        );
    }

    std::fs::remove_dir_all(&dir).ok();
}

/// mt-057 (3): capture writes the artifact; re-running against it reports a
/// clean delta; a fast-lane capture is refused rather than written as a lie.
#[test]
fn capture_then_delta_reports_no_change() {
    let dir = scratch_dir("delta");
    let out = dir.join("fixtures-sweep-sb20.json");

    let mut capture_cfg = fixtures_config(&dir, 2);
    capture_cfg.capture_sweep = Some(out.clone());
    let captured = run_gauge(&capture_cfg, None, &mut |_| {}).expect("capture run");
    assert!(out.is_file(), "the artifact was written");

    let text = std::fs::read_to_string(&out).expect("artifact readable");
    let file: SweepBaselineFile = serde_json::from_str(&text).expect("artifact parses");
    assert_eq!(file.entries.len(), captured.commands);
    assert_eq!(file.config.symmetry, 20);
    assert!(!file.config.count_enabled);

    // Re-run with --delta against what we just captured: nothing moved.
    let mut delta_cfg = fixtures_config(&dir, 1);
    delta_cfg.delta = true;
    let rerun = run_gauge(&delta_cfg, None, &mut |_| {}).expect("delta run");
    let delta = rerun.delta.as_ref().expect("delta computed");
    assert!(
        delta.is_clean(),
        "an unchanged tree must report no change: {delta:?}"
    );
    assert_eq!(delta.unchanged, rerun.commands);
    assert!(rerun.render_text().contains("NO CHANGE vs the recorded"));

    std::fs::remove_dir_all(&dir).ok();
}

/// A capture from a run that did not observe every command is refused, whatever
/// narrowed it. The artifact is committed, so a narrow capture is not merely
/// slow next time — it is indistinguishable from a deliberate one forever after.
#[test]
fn capture_is_refused_for_every_kind_of_incomplete_run() {
    let dir = scratch_dir("refuse");
    let out = dir.join("must-not-exist-sweep-sb20.json");

    // A prior report to point --from-report at (its contents do not matter; the
    // refusal fires before any of it is used).
    let prior = dir.join("prior.json");
    std::fs::write(&prior, r#"{"per_command":[]}"#).expect("prior report");

    let mut narrowed = fixtures_config(&dir, 1);
    narrowed.capture_sweep = Some(out.clone());

    // --only, --from-report and --from-buckets each bar a capture on their own.
    let mut only = narrowed.clone();
    only.only = vec!["test1".to_owned()];
    let mut from_report = narrowed.clone();
    from_report.from_report = Some(prior);
    let mut from_buckets = narrowed.clone();
    from_buckets.from_buckets = vec!["DISAGREE".to_owned()];
    // And so does a fail-fast run that stopped early — asserted here only for
    // the filters, since a clean fixtures sweep never trips fail-fast.
    for (label, cfg) in [
        ("--only", &only),
        ("--from-report", &from_report),
        ("--from-buckets", &from_buckets),
    ] {
        let err = run_gauge(cfg, None, &mut |_| {}).expect_err("capture must be refused");
        match err {
            als_conform::ConformError::SweepCaptureRefused { reason } => {
                assert!(
                    reason.contains("filtered"),
                    "{label}: unexpected reason {reason}"
                );
            }
            other => panic!("{label}: expected a refusal, got {other:?}"),
        }
        assert!(!out.exists(), "{label}: nothing may be written");
    }

    // The same config without a filter writes normally — the refusal is about
    // the filter, not about capture being broken.
    let ok = run_gauge(&narrowed, None, &mut |_| {}).expect("unfiltered capture");
    assert!(out.is_file());
    assert!(ok.commands > 0);

    std::fs::remove_dir_all(&dir).ok();
}

// ---------------------------------------------------------------------------
// mt-059: the count baseline is consulted BEFORE the enumeration. Jar-free —
// the scratch baselines dir *is* the count baseline.
// ---------------------------------------------------------------------------

/// A counting config over the fixtures with `count_cap: 0`, which makes the two
/// worlds trivially distinguishable: any command that is actually enumerated
/// produces one instance, exceeds the cap, and lands `skip_mettle_cap`; a
/// command whose bucket the baseline already settles is never enumerated at all
/// and keeps the settled bucket.
fn counting_config(baselines_dir: &Path, enumerate_all: bool) -> GaugeConfig {
    GaugeConfig {
        count: true,
        count_cap: 0,
        enumerate_all,
        ..fixtures_config(baselines_dir, 1)
    }
}

/// The heart of mt-059: with no count to compare against, the enumerator is
/// never constructed, and the command lands in the bucket the baseline implies
/// rather than in whatever the enumeration would have run out of.
#[test]
fn a_command_the_baseline_cannot_compare_is_never_enumerated() {
    let dir = scratch_dir("presettled");

    // No count baseline at all → every command is a miss.
    let skipped =
        run_gauge(&counting_config(&dir, false), None, &mut |_| {}).expect("skipping run");
    let counted =
        run_gauge(&counting_config(&dir, true), None, &mut |_| {}).expect("enumerating run");

    // Stage 1 is untouched by the stage-2 reordering.
    assert_eq!(skipped.verdict_buckets, counted.verdict_buckets);
    assert_eq!(skipped.commands, counted.commands);
    assert!(skipped.disagreements.is_empty() && skipped.panics.is_empty());

    // The same commands reach the net either way — a settled command keeps its
    // slot and its count bucket, it just does not pay for one.
    let total = |r: &als_conform::SolveGaugeReport| -> usize { r.count_buckets.values().sum() };
    assert!(total(&skipped) > 0, "fixtures reach the counting net");
    assert_eq!(total(&skipped), total(&counted));

    // Skipping: nothing was enumerated, so no enumeration-shaped bucket exists.
    assert_eq!(
        skipped.count_buckets.get("skip_mettle_cap"),
        None,
        "a settled command must not construct an enumerator: {:?}",
        skipped.count_buckets
    );
    assert_eq!(
        skipped.count_buckets.get("skip_enum_budget"),
        None,
        "nor exhaust an enumeration budget: {:?}",
        skipped.count_buckets
    );
    assert!(
        skipped.count_buckets["skip_no_count_baseline"] > 0,
        "they land in the baseline's own bucket instead: {:?}",
        skipped.count_buckets
    );

    // `--enumerate-all` restores the old behavior exactly: the enumerator runs
    // and the command is bucketed by what the enumeration found.
    assert_eq!(
        counted.count_buckets.get("skip_no_count_baseline"),
        None,
        "--enumerate-all must not pre-settle anything: {:?}",
        counted.count_buckets
    );
    assert!(
        counted.count_buckets["skip_mettle_cap"] > 0,
        "--enumerate-all must actually enumerate: {:?}",
        counted.count_buckets
    );

    // STYLE I1: the verdict partition still holds in both worlds.
    for r in [&skipped, &counted] {
        let sum: usize = r.verdict_buckets.values().sum();
        assert_eq!(
            sum, r.commands,
            "verdict buckets must partition the commands"
        );
    }

    std::fs::remove_dir_all(&dir).ok();
}

/// The negative space: a command the baseline *does* hold a count for is still
/// enumerated and still compared, in the very same run that skips its
/// neighbours. This is the acceptance criterion in miniature — the reordering
/// may re-partition skips, never a comparison.
#[test]
fn a_recorded_count_is_still_enumerated_and_compared() {
    use als_conform::solve_gauge::count_baseline::{
        CountBaselineFile, CountConfig, CountEntry, FileCounts,
    };

    let dir = scratch_dir("compare");
    let mut cmds = BTreeMap::new();
    // test1.als's two jar-pinned SB-0 counts (see this file's header comment).
    cmds.insert("0".to_owned(), CountEntry::Count { count: 1129 });
    cmds.insert("1".to_owned(), CountEntry::Count { count: 561 });
    let mut entries = BTreeMap::new();
    entries.insert(
        "crates/als-conform/fixtures/test1.als".to_owned(),
        FileCounts::Commands(cmds),
    );
    let json = CountBaselineFile {
        config: CountConfig {
            count_symmetry: 0,
            count_cap: 10_000,
            jar_timeout_secs: 300,
            no_overflow: true,
            solver: "sat4j".to_owned(),
        },
        entries,
    }
    .to_json()
    .expect("count baseline serializes");
    std::fs::write(dir.join("fixtures-count-sb0.json"), json).expect("count baseline written");

    let cfg = GaugeConfig {
        count: true,
        count_cap: 10_000,
        enum_budget: 2_000_000,
        only: vec!["test1.als".to_owned()],
        ..fixtures_config(&dir, 1)
    };
    let report = run_gauge(&cfg, None, &mut |_| {}).expect("comparing run");

    assert_eq!(
        report.count_buckets.get("count_match"),
        Some(&2),
        "both recorded counts must still be enumerated and matched: {:?}",
        report.count_buckets
    );
    assert!(report.count_mismatches.is_empty());

    std::fs::remove_dir_all(&dir).ok();
}

/// A stale artifact must never silently license a skip or a delta — but it must
/// also not fail a run that was never going to consult it.
#[test]
fn stale_artifact_is_fatal_only_when_it_could_reach_the_answer() {
    let dir = scratch_dir("stale");
    let mut header = fixtures_header();
    header.conflict_budget = 999_999; // captured at a far larger budget
    SweepBaselineFile {
        config: header,
        entries: BTreeMap::new(),
    }
    .write_atomic(&dir.join("stale-sweep-sb20.json"))
    .expect("artifact written");

    // --delta is the sole consumer whose answer depends on artifact content.
    let mut delta_cfg = fixtures_config(&dir, 1);
    delta_cfg.delta = true;
    let err = run_gauge(&delta_cfg, None, &mut |_| {}).expect_err("must hard-error under --delta");
    match err {
        als_conform::ConformError::SweepBaselineConfigMismatch { field, .. } => {
            assert_eq!(field, "conflict_budget");
        }
        other => panic!("expected a config mismatch, got {other:?}"),
    }

    // Any other run can only have used it for scheduling hints: warn, carry on.
    let mut warnings = Vec::new();
    let report = run_gauge(&fixtures_config(&dir, 1), None, &mut |line: &str| {
        warnings.push(line.to_owned());
    })
    .expect("a plain run must not be failed by an artifact it cannot use");
    assert!(report.commands > 0);
    assert!(
        warnings.iter().any(|w| w.contains("conflict_budget")),
        "the mismatch must still be surfaced: {warnings:?}"
    );

    std::fs::remove_dir_all(&dir).ok();
}

/// mt-094: attaching a `--progress-jsonl` telemetry sink is an observability
/// side channel and must not move a single byte of the deterministic report
/// -- with or without a sink, and at any `--jobs` count, the rendered text
/// and JSON stay byte-identical.
#[test]
fn telemetry_sink_does_not_move_the_report() {
    let dir = scratch_dir("telemetry");
    let bare = run_gauge(&fixtures_config(&dir, 1), None, &mut |_| {}).expect("bare run");
    let bare_text = bare.render_text();
    let bare_json = bare.to_json().expect("bare json");

    for jobs in [1, 4] {
        let jsonl_path = dir.join(format!("progress-{jobs}.jsonl"));
        let sink = TelemetrySink::create(&jsonl_path).expect("open telemetry sink");
        let report = run_gauge(&fixtures_config(&dir, jobs), Some(&sink), &mut |_| {})
            .expect("telemetry run");
        assert_eq!(
            report.render_text(),
            bare_text,
            "a telemetry sink must not change the text report (jobs={jobs})"
        );
        assert_eq!(
            report.to_json().expect("telemetry json"),
            bare_json,
            "a telemetry sink must not change the JSON report (jobs={jobs})"
        );

        // The sink actually wrote something real: a run_start, at least one
        // row_done per command, and a run_done.
        drop(sink);
        let lines: Vec<String> = std::fs::read_to_string(&jsonl_path)
            .expect("read jsonl")
            .lines()
            .map(str::to_owned)
            .collect();
        assert!(lines.iter().any(|l| l.contains("\"run_start\"")));
        assert!(lines.iter().any(|l| l.contains("\"run_done\"")));
        let row_done_count = lines.iter().filter(|l| l.contains("\"row_done\"")).count();
        assert_eq!(
            row_done_count, report.commands,
            "one row_done per swept command (jobs={jobs})"
        );
    }

    std::fs::remove_dir_all(&dir).ok();
}
