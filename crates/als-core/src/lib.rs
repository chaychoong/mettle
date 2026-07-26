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
pub mod eval;
mod freevars;
pub mod ir;
pub mod lower;
mod overflow_guard;
pub mod scope;
pub mod solve;
mod strings;
pub mod temporal;
pub mod temporal_lower;

pub use bounds_builder::{compute_bounds, BoundsResult};
pub use error::TranslateError;
pub use eval::{self_check, Evaluator, SelfCheckDetail, SelfCheckFailure};
pub use lower::{
    lower_command, lower_command_keeping_temporal, lower_fragment, FragmentInput, GoalConjunct,
    LoweredFragment, LoweredGoal, Provenance,
};
pub use scope::{compute_universe, MintedAtoms, ScopeTable, ScopedSig, ScopedUniverse};
pub use solve::{
    enumerate, solve_goal, solve_temporal_goal, Instance, InstanceEnumerator, SolveOptions,
    SolveVerdict,
};
pub use temporal::{unroll, LassoSelector, UnrolledBounds};
pub use temporal_lower::lower_temporal_command;
