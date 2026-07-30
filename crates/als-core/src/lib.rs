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
#[cfg(feature = "cadical-instrument")]
pub mod instrument;
pub mod ir;
pub mod lower;
mod overflow_guard;
pub mod scope;
pub mod solve;
mod strings;
pub mod temporal;
pub mod temporal_enum;
pub mod temporal_lower;
pub mod temporal_solve;

// Re-exported because `SolveOptions::backend` is a public field of this type:
// a caller that sets it (the CLI's `--solver`, the instrument) should not have to
// depend on als-solve directly to name the value.
pub use als_solve::Backend;

/// Whether THIS crate was compiled with `debug_assertions` armed. A test binary's
/// own `cfg!(debug_assertions)` reflects the test profile, not the profile this
/// library was built under — and the mt-091 per-package `opt-level` override
/// exists precisely because the two can diverge. The `solve_corpus` canary asserts
/// the two agree, so the override can never silently disarm the debug gauntlet's
/// invariant coverage.
pub const DEBUG_ASSERTIONS_ARMED: bool = cfg!(debug_assertions);
pub use bounds_builder::{compute_bounds, BoundsResult};
pub use error::TranslateError;
pub use eval::{self_check, self_check_temporal, Evaluator, SelfCheckDetail, SelfCheckFailure};
#[cfg(feature = "cadical-instrument")]
pub use instrument::{
    cross_check_goal, solve_goal_with_backend, CrossAgreement, CrossOutcome, InstrumentBackend,
    InstrumentOutcome, InstrumentVerdict,
};
pub use lower::{
    lower_command, lower_command_keeping_temporal, lower_fragment, lower_fragment_keeping_temporal,
    FragmentInput, GoalConjunct, LoweredFragment, LoweredGoal, Provenance,
};
pub use scope::{compute_universe, MintedAtoms, ScopeTable, ScopedSig, ScopedUniverse};
pub use solve::{
    enumerate, solve_goal, solve_temporal_goal, solve_temporal_goal_at,
    solve_temporal_goal_checked, Instance, InstanceEnumerator, SolveOptions, SolveVerdict,
    TemporalSolution,
};
pub use temporal::{unroll, LassoSelector, UnrolledBounds};
pub use temporal_enum::{TraceAdvance, TraceEnumerator, TraceStep};
pub use temporal_lower::{eliminate_fragment_at_state, lower_temporal_command};
pub use temporal_solve::{
    normalize_state, solve_temporal_command, TemporalSolveConfig, TemporalTrace, TemporalVerdict,
    TraceArtifacts,
};
