//! Result types shared by the parser, the process runner, and the
//! scorecard. Kept separate from both so `parse` (pure) and `scorecard`
//! (pure) can be unit-tested without depending on the process-spawning
//! code in `shim`.

use serde::Serialize;
use std::path::PathBuf;

/// Coarse classification of a harness-reported failure, shared between
/// file-level and command-level errors so both render the same way.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ShimErrorKind {
    /// The `.als` file failed to parse/compile.
    Parse,
    /// A single command's translation/solve threw.
    Command,
    /// The shim was invoked incorrectly (should not happen from the Rust
    /// side; surfaced anyway rather than silently swallowed).
    Usage,
    /// The Rust side could not even talk to the shim: spawn failure,
    /// missing pipe, or output that isn't well-formed JSON Lines.
    Protocol,
}

/// One command's verdict from a single oracle run. `instance_count` is
/// `Some` only when the run requested enumeration
/// ([`crate::config::EnumerationCap`] other than `VerdictOnly`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Outcome {
    Sat {
        instance_count: Option<u32>,
    },
    Unsat {
        instance_count: Option<u32>,
    },
    Error {
        kind: ShimErrorKind,
        message: String,
    },
}

impl Outcome {
    /// Whether this outcome represents a solver verdict of SAT (as
    /// opposed to UNSAT or an error). Used by Net 0 classification.
    #[must_use]
    pub fn is_sat(&self) -> bool {
        matches!(self, Outcome::Sat { .. })
    }
}

/// One command mined from a file plus its oracle outcome.
///
/// `expects` mirrors the Alloy `Command.expects` field, translated from
/// its `-1`/`0`/`1` sentinel into a proper `Option` (`PORTING_RULES` R5):
/// `None` = no `expect` annotation, `Some(false)` = `expect 0` (asserts
/// UNSAT), `Some(true)` = `expect 1` (asserts SAT).
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CommandResult {
    pub index: usize,
    pub label: String,
    pub check: bool,
    pub expects: Option<bool>,
    pub outcome: Outcome,
}

/// The outcome of running the oracle over one whole file: either every
/// command produced a result, the JVM was killed for exceeding the
/// per-file timeout, or the shim reported a structural failure before/
/// instead of producing any command results.
// Adjacently (not internally) tagged: `Commands` wraps a `Vec`, which
// can't serialize as a JSON object, so it can't carry an internal tag
// field the way `Outcome`'s struct-only variants can.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "type", content = "data", rename_all = "snake_case")]
pub enum FileOutcome {
    Commands(Vec<CommandResult>),
    Timeout,
    Error {
        kind: ShimErrorKind,
        message: String,
    },
}

/// One file's oracle run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FileResult {
    pub file: PathBuf,
    pub outcome: FileOutcome,
}
