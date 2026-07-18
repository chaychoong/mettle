//! Integration smoke for the mt-037 solve gauge + SB-0 counting net, driving
//! the *real* reference jar. Skips cleanly (not fails) when the jar is absent
//! (CI has no JDK), matching `oracle_integration.rs`.
//!
//! Pins the golden from the task spec on `oracle/test1.als` at `--count`:
//! - `run show` (`run { some r } for 3`) has no skolemizable existential and no
//!   ordered-abstract partition, so it reaches the net and its SB-0 count
//!   matches the jar exactly (1129 = 1129) → `count_match`;
//! - `check NoEmpty` (`all b: B | some b.r`, negated) is a first-order top-level
//!   existential the jar skolemizes at depth 0, so mettle's raw count diverges
//!   and the command is a typed `skip_fo_skolem`.

use std::path::PathBuf;
use std::time::Duration;

use als_conform::{run_gauge, GaugeConfig};

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn jar_path() -> PathBuf {
    workspace_root().join("oracle/org.alloytools.alloy.dist.jar")
}

fn test1_config() -> GaugeConfig {
    let root = workspace_root();
    GaugeConfig {
        roots: vec![root.join("oracle/test1.als")],
        workspace_root: root.clone(),
        baselines_dir: root.join("baselines"),
        conflict_budget: 200_000,
        encode_budget: 50_000_000,
        primary_var_cap: 200_000,
        allow_overflow: false,
        count: true,
        count_cap: 10_000,
        jar_path: jar_path(),
        shim_source: PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/shim/OracleShim.java")),
        jar_timeout: Duration::from_mins(5),
    }
}

#[test]
fn test1_count_smoke_matches_jar_and_skips_fo_skolem() {
    if !jar_path().is_file() {
        eprintln!(
            "SKIP {}: reference jar not found at {} (expected for CI)",
            module_path!(),
            jar_path().display()
        );
        return;
    }

    let report =
        run_gauge(&test1_config(), &mut |_| {}).unwrap_or_else(|e| panic!("run_gauge failed: {e}"));

    assert_eq!(report.commands, 2, "test1.als has two commands");
    // `run show` reaches the net and matches the jar's SB-0 count (1129).
    assert_eq!(
        report.count_buckets.get("count_match"),
        Some(&1),
        "run show must land count_match (1129=1129); buckets={:?}",
        report.count_buckets
    );
    // `check NoEmpty` is a skolemizable first-order existential.
    assert_eq!(
        report.count_buckets.get("skip_fo_skolem"),
        Some(&1),
        "check NoEmpty must land skip_fo_skolem; buckets={:?}",
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
