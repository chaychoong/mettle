//! The solve driver: bounded IR → CNF → verdict / instances (mt-033,
//! translation-ref §4).
//!
//! This is the phase-4 seam ADR-0011 names: it mints the primary variables in
//! the pinned order (decision 3), hands the goal to the [`crate::encode`]r, drives
//! the [`als_solve::CdclSolver`], and decodes an [`Assignment`](als_solve::Assignment)
//! back into an [`Instance`] over the command's [`Universe`]. It is the point
//! where mettle produces its first real **SAT/UNSAT verdicts** and instances.
//!
//! - [`solve_goal`] returns the first verdict ([`SolveVerdict`]).
//! - [`enumerate`] returns an [`InstanceEnumerator`] yielding **distinct
//!   instances** (distinct projections onto the primary variables) in a
//!   deterministic order — the SB-0 counting-net primitive (translation-ref
//!   §4.5): the enumerator blocks each found model over the **primary variables
//!   only**, never the Tseitin auxiliaries.
//!
//! Polarity (translation-ref §0/§4.3, for mt-036's CLI): the goal a `check`
//! command lowers to is the **negated** assertion, so `solve_goal` returning
//! [`SolveVerdict::Sat`] for a `check` means a **counterexample** was found, and
//! [`SolveVerdict::Unsat`] means the assertion holds within scope.

use std::collections::BTreeMap;

use als_solve::{block, Assignment, CdclSolver, Cnf, Outcome, Var};

use crate::bounds::{Bounds, Tuple, TupleSet, Universe};
use crate::bounds_builder::BoundsResult;
use crate::encode::{Bool, Encoder, PrimaryMap};
use crate::error::TranslateError;
use crate::ir::{Ir, RelId};
use crate::lower::LoweredGoal;
use crate::scope::ScopedUniverse;

/// Solver knobs (translation-ref §2.4). Currently just the LEDGER-001 overflow
/// switch; kept as a struct so mt-036/Rung-4 can extend it without churning the
/// driver signature.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct SolveOptions {
    /// Whether integer overflow **wraps** (`true`) or **excludes the instance**.
    /// The default (`false`) is mettle's canonical **forbid** per LEDGER-001 —
    /// which is exactly `bool::default()`, so `Default` is derived.
    pub allow_overflow: bool,
}

/// A solving verdict for one command.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SolveVerdict {
    /// Satisfiable, with a witnessing instance (a `run` instance or a `check`
    /// counterexample — see the module docs on polarity).
    Sat(Instance),
    /// Unsatisfiable (no `run` instance / no `check` counterexample).
    Unsat,
}

/// A decoded instance: one concrete [`TupleSet`] per relation, over the command
/// universe.
///
/// Per ADR-0002 instance tuples are **never** diffed against the jar; this is for
/// display (mt-036), the evaluator self-check (mt-034), and the bounds-respect
/// property net. Relations iterate in `RelId` order (deterministic).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Instance {
    /// The atom universe the tuples range over.
    pub universe: Universe,
    rels: BTreeMap<RelId, TupleSet>,
}

impl Instance {
    /// The decoded value of `rel`, if present.
    #[must_use]
    pub fn get(&self, rel: RelId) -> Option<&TupleSet> {
        self.rels.get(&rel)
    }

    /// Iterates `(rel, tuples)` in `RelId` order.
    pub fn iter(&self) -> impl Iterator<Item = (RelId, &TupleSet)> {
        self.rels.iter().map(|(&r, ts)| (r, ts))
    }
}

/// How to reconstruct one relation's [`TupleSet`] from an [`Assignment`]: its
/// fixed lower tuples plus each floating tuple gated by its primary variable.
#[derive(Debug)]
struct RelDecode {
    rel: RelId,
    arity: usize,
    lower: TupleSet,
    floating: Vec<(Tuple, Var)>,
}

/// The finished translation: CNF, primary variables (for blocking), the decode
/// layout, and the universe. `trivially_unsat` short-circuits an all-false goal.
#[derive(Debug)]
struct Translated {
    cnf: Cnf,
    primary_vars: Vec<Var>,
    layout: Vec<RelDecode>,
    universe: Universe,
    trivially_unsat: bool,
}

/// Mints the primary variables (ADR-0011 decision 3) and builds the decode
/// layout for every bounded relation — referenced by the goal or not (the
/// equivalent of the reference's §2.5(4) reflexive `r = r` padding: every bounded
/// relation keeps its primary variables so unreferenced relations stay free, and
/// so enumeration counts match).
fn allocate_primaries(bounds: &Bounds, cnf: &mut Cnf) -> (PrimaryMap, Vec<Var>, Vec<RelDecode>) {
    let mut prim: PrimaryMap = BTreeMap::new();
    let mut primary_vars: Vec<Var> = Vec::new();
    let mut layout: Vec<RelDecode> = Vec::new();
    for (rel, bound) in bounds.iter() {
        let mut floating: Vec<(Tuple, Var)> = Vec::new();
        for t in bound.upper().iter() {
            if bound.lower().contains(t) {
                continue;
            }
            let var = cnf.fresh_var();
            prim.insert((rel, t.clone()), var);
            primary_vars.push(var);
            floating.push((t.clone(), var));
        }
        layout.push(RelDecode {
            rel,
            arity: bound.upper().arity(),
            lower: bound.lower().clone(),
            floating,
        });
    }
    (prim, primary_vars, layout)
}

/// Translates one lowered command goal to CNF (primary allocation + encoding).
fn translate(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    opts: SolveOptions,
) -> Result<Translated, TranslateError> {
    let mut cnf = Cnf::new();
    let (prim, primary_vars, layout) = allocate_primaries(&bounds.bounds, &mut cnf);

    let encoder = Encoder::new(
        ir,
        &bounds.bounds,
        &prim,
        cnf,
        scoped.bitwidth,
        scoped.sig_atom_count,
        opts.allow_overflow,
    );
    let (goal_bool, mut cnf) = encoder.finish_goal(goal.goal)?;

    let mut trivially_unsat = false;
    match goal_bool {
        Bool::Const(true) => {}
        Bool::Const(false) => trivially_unsat = true,
        Bool::Lit(l) => cnf.add_clause(vec![l]),
    }

    Ok(Translated {
        cnf,
        primary_vars,
        layout,
        universe: bounds.bounds.universe.clone(),
        trivially_unsat,
    })
}

/// Decodes an assignment into an instance (STYLE I2 bounds-respect asserted).
fn decode(layout: &[RelDecode], universe: &Universe, assign: &Assignment) -> Instance {
    let mut rels: BTreeMap<RelId, TupleSet> = BTreeMap::new();
    for rd in layout {
        let mut ts = rd.lower.clone();
        debug_assert_eq!(ts.arity(), rd.arity, "lower/relation arity mismatch");
        for (tuple, var) in &rd.floating {
            if assign.value(*var) {
                ts.insert(tuple.clone());
            }
        }
        // Bounds-respect: lower ⊆ decoded ⊆ upper holds by construction (we start
        // from lower and only add floating tuples of the upper). Assert the lower
        // half, which the floating loop could not violate but a layout bug could.
        debug_assert!(
            rd.lower.is_subset_of(&ts),
            "decoded relation dropped a lower-bound tuple"
        );
        rels.insert(rd.rel, ts);
    }
    Instance {
        universe: universe.clone(),
        rels,
    }
}

/// Solves one lowered command, returning its first verdict (translation-ref §4).
///
/// # Errors
/// A [`TranslateError`] when the goal contains a construct outside the Rung-3
/// encoder slice (integer arithmetic / `sum` / int-`ITE`, or — as an internal
/// invariant failure — a temporal node); never a wrong verdict (STYLE E5).
pub fn solve_goal(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    opts: &SolveOptions,
) -> Result<SolveVerdict, TranslateError> {
    let t = translate(ir, scoped, goal, bounds, *opts)?;
    if t.trivially_unsat {
        return Ok(SolveVerdict::Unsat);
    }
    let mut solver = CdclSolver::new(&t.cnf);
    Ok(match solver.solve() {
        Outcome::Sat(model) => SolveVerdict::Sat(decode(&t.layout, &t.universe, &model)),
        Outcome::Unsat => SolveVerdict::Unsat,
    })
}

/// A deterministic enumerator over the **distinct instances** of one command
/// (translation-ref §4.5). Each [`InstanceEnumerator::next`] yields the next
/// instance and blocks its primary-variable projection; the sequence ends at the
/// first `Unsat`. Blocking over primary variables (never Tseitin auxiliaries)
/// makes the count the **raw / SB-0** model count (ADR-0002 counting net).
#[derive(Debug)]
pub struct InstanceEnumerator {
    solver: CdclSolver,
    primary_vars: Vec<Var>,
    layout: Vec<RelDecode>,
    universe: Universe,
    done: bool,
}

impl Iterator for InstanceEnumerator {
    type Item = Instance;

    /// The next distinct instance, or `None` when the space is exhausted.
    fn next(&mut self) -> Option<Instance> {
        if self.done {
            return None;
        }
        match self.solver.solve() {
            Outcome::Unsat => {
                self.done = true;
                None
            }
            Outcome::Sat(model) => {
                let inst = decode(&self.layout, &self.universe, &model);
                let clause = block(&model, &self.primary_vars);
                if clause.is_empty() {
                    // No primary variables ⇒ a single distinguishable instance.
                    self.done = true;
                } else {
                    self.solver.add_clause(clause);
                }
                Some(inst)
            }
        }
    }
}

/// Builds an [`InstanceEnumerator`] for one lowered command.
///
/// # Errors
/// As [`solve_goal`] — a [`TranslateError`] for a construct outside the encoder
/// slice.
pub fn enumerate(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
    opts: &SolveOptions,
) -> Result<InstanceEnumerator, TranslateError> {
    let t = translate(ir, scoped, goal, bounds, *opts)?;
    // A trivially-UNSAT goal (the encoded `Bool` folded to constant-false) gets an
    // empty clause, so the solver reports UNSAT on the first `next()` and the
    // enumerator terminates cleanly with no instances.
    let mut cnf = t.cnf;
    if t.trivially_unsat {
        cnf.add_clause(vec![]);
    }
    let solver = CdclSolver::new(&cnf);
    Ok(InstanceEnumerator {
        solver,
        primary_vars: t.primary_vars,
        layout: t.layout,
        universe: t.universe,
        done: false,
    })
}
