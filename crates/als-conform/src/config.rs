//! Oracle configuration: everything needed to drive the reference jar
//! through `OracleShim` for one conformance run.

use std::path::PathBuf;
use std::time::Duration;

/// How many instances to enumerate per command, on top of the initial
/// verdict. Mirrors `OracleShim`'s `enumCap` argument (`PORTING_RULES` R5:
/// no in-band `-1`/`0` sentinel on the Rust side, even though the Java
/// shim's wire protocol uses one).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnumerationCap {
    /// Only the first solve's verdict; no enumeration.
    VerdictOnly,
    /// Enumerate up to `n` distinct instances.
    UpTo(u32),
    /// Enumerate every instance (stop only at UNSAT).
    Exhaustive,
}

impl EnumerationCap {
    /// The `enumCap` command-line argument `OracleShim` expects.
    pub(crate) fn shim_arg(self) -> String {
        match self {
            EnumerationCap::VerdictOnly => "0".to_string(),
            EnumerationCap::UpTo(n) => n.to_string(),
            EnumerationCap::Exhaustive => "-1".to_string(),
        }
    }
}

/// Configuration for driving the reference Alloy jar via `OracleShim`.
///
/// Defaults follow the project's decided canonical settings: `no_overflow`
/// defaults to `true` per LEDGER-001 (mettle's canonical default is
/// forbid-overflow, and the harness must set the oracle's `noOverflow`
/// explicitly to match rather than rely on the jar's own headless default
/// of `false` -- see docs/reference/alloy6-reference.md sec 3(c)).
/// `symmetry` defaults to 20 (the jar's own `A4Options` default) because
/// Net 0 (this bead) only compares verdicts, which symmetry breaking does
/// not affect; ADR-0002's `symmetry = 0` canonical counting net is an
/// explicit opt-in via [`OracleConfig::with_symmetry`] for callers that
/// need SB-off counts.
#[derive(Debug, Clone)]
pub struct OracleConfig {
    /// Path to the pinned reference jar (ADR-0002).
    pub jar_path: PathBuf,
    /// Path to the `OracleShim.java` source, compiled on demand.
    pub shim_source: PathBuf,
    /// Directory the compiled `OracleShim.class` is cached in.
    pub shim_classes_dir: PathBuf,
    /// `A4Options.symmetry`.
    pub symmetry: i32,
    /// `A4Options.noOverflow`. See LEDGER-001 above.
    pub no_overflow: bool,
    /// `A4Options.solver` factory name, e.g. `"sat4j"` (zero native deps).
    pub solver: String,
    /// Per-file wall-clock budget before the JVM is killed.
    pub timeout: Duration,
}

impl OracleConfig {
    /// Builds a config with the project's decided defaults: symmetry 20,
    /// `no_overflow = true` (LEDGER-001), solver `sat4j`, 60s timeout, and
    /// a shim-class cache under the OS temp dir.
    #[must_use]
    pub fn new(jar_path: impl Into<PathBuf>, shim_source: impl Into<PathBuf>) -> Self {
        Self {
            jar_path: jar_path.into(),
            shim_source: shim_source.into(),
            shim_classes_dir: std::env::temp_dir().join("als-conform-oracle-shim"),
            symmetry: 20,
            no_overflow: true,
            solver: "sat4j".to_string(),
            timeout: Duration::from_mins(1),
        }
    }

    /// Sets `A4Options.symmetry` (ADR-0002's counting net uses 0).
    #[must_use]
    pub fn with_symmetry(mut self, symmetry: i32) -> Self {
        self.symmetry = symmetry;
        self
    }

    /// Sets `A4Options.noOverflow` explicitly (LEDGER-001: never rely on
    /// the jar's own default).
    #[must_use]
    pub fn with_no_overflow(mut self, no_overflow: bool) -> Self {
        self.no_overflow = no_overflow;
        self
    }

    /// Sets the `A4Options.solver` factory name.
    #[must_use]
    pub fn with_solver(mut self, solver: impl Into<String>) -> Self {
        self.solver = solver.into();
        self
    }

    /// Sets the per-file JVM timeout.
    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
}
