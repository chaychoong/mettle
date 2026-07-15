//! Integration test: drives the *real* reference jar via `OracleShim`.
//!
//! Skips cleanly (with an `eprintln!` note, not a failure) when the jar
//! isn't present, because CI has no JDK/jar -- this bead's requirement.
//! Verifies the empirically-known facts recorded in
//! docs/reference/alloy6-reference.md sec 3(b)/(c) and sec 5:
//! test1.als's `show` command is SAT; exhaustive enumeration gives 87
//! instances at symmetry=20 and 1129 at symmetry=0; test2/test3 exercise
//! `expect` matching (Net 0).

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use als_conform::{EnumerationCap, FileOutcome, OracleConfig, Outcome};

fn oracle_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../oracle")
}

fn jar_path() -> PathBuf {
    oracle_dir().join("org.alloytools.alloy.dist.jar")
}

fn shim_source() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("shim/OracleShim.java")
}

fn oracle_file(name: &str) -> PathBuf {
    oracle_dir().join(name)
}

fn jar_present() -> bool {
    jar_path().is_file()
}

/// Skip (not fail) when the pinned jar isn't available -- CI has no JDK.
macro_rules! require_jar_or_skip {
    () => {
        if !jar_present() {
            eprintln!(
                "SKIP {}: reference jar not found at {} (expected for CI; run \
                 docs/reference/alloy6-reference.md's download step locally to enable this test)",
                module_path!(),
                jar_path().display()
            );
            return;
        }
    };
}

fn base_config() -> OracleConfig {
    OracleConfig::new(jar_path(), shim_source())
}

/// Compiles the shim exactly once for the whole test binary (tests run on
/// multiple threads by default; sharing one compile avoids two `javac`
/// invocations racing on the same output `.class` file).
fn shim_classes() -> &'static Path {
    static CLASSES: OnceLock<PathBuf> = OnceLock::new();
    CLASSES.get_or_init(|| {
        let cfg = base_config();
        #[allow(
            clippy::expect_used,
            reason = "test setup: a compile failure here should abort the test run loudly"
        )]
        als_conform::ensure_shim_compiled(&cfg)
            .expect("failed to compile oracle shim for integration tests")
    })
}

#[test]
fn test1_show_command_is_sat() {
    require_jar_or_skip!();
    let cfg = base_config();
    let result = als_conform::run_oracle_on_file(
        &cfg,
        shim_classes(),
        &oracle_file("test1.als"),
        EnumerationCap::VerdictOnly,
    );
    let FileOutcome::Commands(commands) = result.outcome else {
        panic!("expected Commands, got {:?}", result.outcome)
    };
    assert_eq!(
        commands.len(),
        2,
        "test1.als has two commands: show, NoEmpty"
    );
    assert_eq!(commands[0].label, "show");
    assert_eq!(
        commands[0].outcome,
        Outcome::Sat {
            instance_count: None
        }
    );
}

#[test]
fn test1_enumeration_matches_known_symmetry_counts() {
    require_jar_or_skip!();

    // docs/reference/alloy6-reference.md sec 3(b)/(c): default symmetry
    // (20) enumerates 87 instances for `show`; symmetry=0 (ADR-0002's
    // canonical counting net) enumerates 1129.
    let config_with_breaking = base_config().with_symmetry(20);
    let outcome_with_breaking = als_conform::run_oracle_on_file(
        &config_with_breaking,
        shim_classes(),
        &oracle_file("test1.als"),
        EnumerationCap::Exhaustive,
    );
    let FileOutcome::Commands(found_with_breaking) = outcome_with_breaking.outcome else {
        panic!("expected Commands, got {:?}", outcome_with_breaking.outcome)
    };
    assert_eq!(
        found_with_breaking[0].outcome,
        Outcome::Sat {
            instance_count: Some(87)
        }
    );

    let config_no_breaking = base_config().with_symmetry(0);
    let outcome_no_breaking = als_conform::run_oracle_on_file(
        &config_no_breaking,
        shim_classes(),
        &oracle_file("test1.als"),
        EnumerationCap::Exhaustive,
    );
    let FileOutcome::Commands(found_no_breaking) = outcome_no_breaking.outcome else {
        panic!("expected Commands, got {:?}", outcome_no_breaking.outcome)
    };
    assert_eq!(
        found_no_breaking[0].outcome,
        Outcome::Sat {
            instance_count: Some(1129)
        }
    );
}

#[test]
fn expect_annotations_cross_check_as_net0() {
    require_jar_or_skip!();
    let cfg = base_config();
    let files = vec![oracle_file("test2.als"), oracle_file("test3.als")];
    let scorecard = als_conform::run_oracle_on_files(&cfg, &files, EnumerationCap::VerdictOnly)
        .unwrap_or_else(|e| panic!("run_oracle_on_files failed: {e}"));

    // test2.als: `impossible` expect 0 (actually UNSAT) -> match;
    // `possible` expect 1 (actually SAT) -> match; `possible` expect 0
    // (actually SAT, deliberately wrong) -> mismatch.
    // test3.als: `impossible` expect 1 (actually UNSAT) -> mismatch.
    assert_eq!(scorecard.totals.commands, 4);
    assert_eq!(scorecard.totals.with_expect, 4);
    assert_eq!(scorecard.totals.matches, 2);
    assert_eq!(scorecard.totals.mismatches, 2);
    assert_eq!(scorecard.totals.errors, 0);
    assert_eq!(scorecard.totals.timeouts, 0);
}

#[test]
fn overflow_default_forbids_per_ledger_001() {
    require_jar_or_skip!();

    // LEDGER-001 (approved): mettle's canonical default is forbid-overflow,
    // and the harness sets the oracle's noOverflow explicitly to match.
    // `OracleConfig::new` defaults to `no_overflow = true`.
    let cfg_forbid = base_config();
    assert!(
        cfg_forbid.no_overflow,
        "OracleConfig::new must default no_overflow=true per LEDGER-001"
    );
    let result = als_conform::run_oracle_on_file(
        &cfg_forbid,
        shim_classes(),
        &oracle_file("overflow.als"),
        EnumerationCap::VerdictOnly,
    );
    let FileOutcome::Commands(commands) = result.outcome else {
        panic!("expected Commands, got {:?}", result.outcome)
    };
    assert_eq!(
        commands[0].outcome,
        Outcome::Unsat {
            instance_count: None
        },
        "7+7 overflows at bitwidth 4, forbidden by default"
    );

    let cfg_allow = base_config().with_no_overflow(false);
    let result = als_conform::run_oracle_on_file(
        &cfg_allow,
        shim_classes(),
        &oracle_file("overflow.als"),
        EnumerationCap::VerdictOnly,
    );
    let FileOutcome::Commands(commands) = result.outcome else {
        panic!("expected Commands, got {:?}", result.outcome)
    };
    assert_eq!(
        commands[0].outcome,
        Outcome::Sat {
            instance_count: None
        },
        "with overflow allowed, 7+7 wraps and is satisfiable"
    );
}

#[test]
fn missing_file_reports_structured_parse_error_not_panic() {
    require_jar_or_skip!();
    let cfg = base_config();
    let result = als_conform::run_oracle_on_file(
        &cfg,
        shim_classes(),
        Path::new("/nonexistent/does-not-exist.als"),
        EnumerationCap::VerdictOnly,
    );
    let FileOutcome::Error { kind, .. } = result.outcome else {
        panic!(
            "expected a structured Error outcome, got {:?}",
            result.outcome
        )
    };
    assert_eq!(kind, als_conform::ShimErrorKind::Parse);
}
