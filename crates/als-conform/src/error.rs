//! Typed error enum for the harness's own infrastructure failures.
//!
//! These are failures of the *harness* (can't find the jar, can't compile
//! the shim, can't spawn `java`) -- not oracle *verdicts*. A file that the
//! oracle itself failed to parse/solve is not an error at this level; it is
//! recorded as [`crate::model::FileOutcome::Error`] inside a normal
//! [`crate::scorecard::Scorecard`] (STYLE E1: errors are typed values, and per
//! this bead's spec the library never panics on a recoverable condition).

use std::path::PathBuf;

/// Harness-level failures: everything short of a genuine internal
/// invariant violation is represented here rather than panicking (STYLE
/// E2/E3 -- this crate never panics or prints; only `src/bin/conform.rs`
/// renders these for a human).
#[derive(Debug, thiserror::Error)]
pub enum ConformError {
    /// The configured reference jar path does not exist.
    #[error("reference jar not found at {0}")]
    JarNotFound(PathBuf),
    /// The `OracleShim.java` source does not exist.
    #[error("oracle shim source not found at {0}")]
    ShimSourceNotFound(PathBuf),
    /// `javac` failed to compile the shim; message is javac's stderr.
    #[error("failed to compile oracle shim: {0}")]
    ShimCompile(String),
    /// Could not spawn `javac`/`java` at all (e.g. not on PATH).
    #[error("failed to spawn {program} for {file}: {source}")]
    Spawn {
        program: &'static str,
        file: PathBuf,
        #[source]
        source: std::io::Error,
    },
    /// Any other I/O failure (creating scratch dirs, writing the scorecard).
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    /// Failed to render the scorecard as JSON.
    #[error("failed to render scorecard as json: {0}")]
    Json(#[from] serde_json::Error),
    /// A JVM shim invocation (mt-024's `bench`, driving `ResolveGaugeShim`
    /// directly rather than through [`crate::shim::run_oracle_on_file`])
    /// exceeded its wall-clock budget.
    #[error("java {class_name} timed out after {timeout:?}")]
    JvmTimeout {
        class_name: String,
        timeout: std::time::Duration,
    },
    /// A JVM shim invocation exited nonzero or produced no parseable
    /// output on stdout.
    #[error("java {class_name} failed: {message}")]
    JvmFailed { class_name: String, message: String },
    /// A loaded count baseline's `config` header disagrees with the run's
    /// pinned config on a field that would make its counts incomparable
    /// (`count_cap`, overflow, `count_symmetry`, or `solver`). A hard tool
    /// error, never a silent skip (mt-054 (b)): comparing against counts
    /// produced at a different config is a fabricated verdict.
    #[error(
        "count baseline {file}: config field `{field}` mismatch (baseline={found}, run={expected})"
    )]
    CountBaselineConfigMismatch {
        file: String,
        field: &'static str,
        expected: String,
        found: String,
    },
    /// A loaded **sweep** baseline's `config` header disagrees with the run on a
    /// field that would make its buckets incomparable (symmetry, the
    /// conflict/encode/primary-var budgets, overflow, solver, or — for a
    /// counting run — the counting budgets). A hard tool error, never a silent
    /// skip (mt-057): skipping a "known-capped" command on the authority of a
    /// baseline captured at different budgets is a fabricated skip.
    #[error(
        "sweep baseline {file}: config field `{field}` mismatch (baseline={found}, run={expected})"
    )]
    SweepBaselineConfigMismatch {
        file: String,
        field: &'static str,
        expected: String,
        found: String,
    },
    /// `--capture-sweep` was asked to record an artifact from a run that did not
    /// observe every command — a fail-fast `partial` run, or one narrowed by
    /// `--only` / `--from-report` / `--from-buckets`. Refused loudly rather than
    /// written as a lie: the artifact is committed, so a narrow one outlives the
    /// session and reads exactly like a deliberate one.
    #[error("refusing to capture a sweep baseline: {reason}")]
    SweepCaptureRefused { reason: &'static str },
    /// A committed resolve-verdict baseline could not be read as one (mt-110):
    /// a missing header field or a malformed reject row. Half a baseline is not
    /// a usable baseline, so this fails the load rather than dropping rows.
    #[error("resolve baseline is malformed: {detail}")]
    ResolveBaselineParse { detail: String },
    /// A resolve-verdict baseline's header does not describe the corpus (or the
    /// jar) it is being used against. A hard tool error, never a warning
    /// (mt-110): the baseline keys rows by code index, so answering for a
    /// different extraction compares row `i` of one corpus with row `i` of
    /// another.
    #[error("resolve baseline: `{field}` mismatch (baseline={expected}, run={actual})")]
    ResolveBaselineMismatch {
        field: String,
        expected: String,
        actual: String,
    },
    /// A committed warning-parity baseline could not be read as one (mt-118):
    /// a missing header field or a malformed warning row. Half a baseline is
    /// not a usable baseline, so this fails the load rather than dropping
    /// rows.
    #[error("warnings baseline is malformed: {detail}")]
    WarningsBaselineParse { detail: String },
}
