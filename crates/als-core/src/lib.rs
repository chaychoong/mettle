//! Bounds, relational IR, matrix translation, quantifier grounding,
//! skolemization, symmetry breaking, sharing, and Tseitin-to-CNF translation.
//!
//! Currently: the hand-designed type skeleton (mt-005) — [`ir`] holds the
//! three-sorted relational IR, [`bounds`] the universe/tuple-set/bounds
//! types. Translation passes land in later rungs.

#![deny(clippy::unwrap_used, clippy::expect_used)]

pub mod bounds;
pub mod bounds_builder;
mod encode;
pub mod error;
pub mod ir;
pub mod lower;
pub mod scope;
pub mod solve;

pub use bounds_builder::{compute_bounds, BoundsResult};
pub use error::TranslateError;
pub use lower::{lower_command, GoalConjunct, LoweredGoal, Provenance};
pub use scope::{compute_universe, MintedAtoms, ScopeTable, ScopedSig, ScopedUniverse};
pub use solve::{enumerate, solve_goal, Instance, InstanceEnumerator, SolveOptions, SolveVerdict};
