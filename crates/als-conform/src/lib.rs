//! Conformance harness (mt-006, v0): drives the pinned reference Alloy
//! jar through a purpose-built JVM shim (`shim/OracleShim.java`, shipped
//! inside this crate) via
//! the `A4Options` API, mines `expect 0`/`expect 1` command annotations,
//! and cross-checks the jar's own verdicts against them -- "Net 0"
//! (ADR-0002 item 3). mettle cannot parse or solve anything yet; this
//! crate's whole job at v0 is to prove the harness itself is correct and
//! to produce a deterministic scorecard artifact.
//!
//! Library surface:
//! - [`config::OracleConfig`] / [`config::EnumerationCap`]: how to invoke the oracle.
//! - [`shim::ensure_shim_compiled`] / [`shim::run_oracle_on_file`] / [`shim::run_oracle_on_files`]:
//!   drive the jar.
//! - [`model`]: typed per-command/per-file results.
//! - [`scorecard::Scorecard`]: deterministic aggregation and rendering.
//! - [`error::ConformError`]: harness-level (not oracle-verdict-level) failures.
//! - [`bench::run_bench`] / [`bench::BenchReport`] (mt-024): the one-command
//!   conformance + speed benchmark (`conform bench`) -- per-stage mettle-vs-jar
//!   agreement (parse, resolve) plus honest mettle/jar timing, reusing the
//!   mt-020 `ResolveGaugeShim` machinery.
//!
//! This crate never prints and never exits the process (STYLE E3) --
//! that is `src/bin/conform.rs`'s job alone.

#![deny(clippy::unwrap_used, clippy::expect_used)]

pub mod bench;
pub mod config;
pub mod error;
pub mod model;
mod parse;
pub mod scorecard;
pub mod shim;
pub mod solve_gauge;

pub use bench::{run_bench, BenchConfig, BenchReport, DEFAULT_CORPUS_ROOTS};
pub use config::{EnumerationCap, OracleConfig};
pub use error::ConformError;
pub use model::{CommandResult, FileOutcome, FileResult, Outcome, ShimErrorKind};
pub use scorecard::{Scorecard, Totals};
pub use shim::{ensure_shim_compiled, run_oracle_on_file, run_oracle_on_files};
pub use solve_gauge::{run_gauge, GaugeConfig, SolveGaugeReport};
