//! The finite universe and relation bounds handed to translation.
//!
//! Behavioral role (not structure) mirrors Kodkod's universe/bounds: solving
//! is model-finding over a fixed atom universe where every relation is boxed
//! between a lower and an upper tuple set (`PORTING_RULES` prime directive:
//! behavior pinned, shape idiomatic).
//!
//! Determinism: atom order is fixed at universe construction, and tuple sets
//! iterate in key (lexicographic) order via `BTreeSet` (STYLE C2) — nothing
//! downstream can observe hash order.

use std::collections::{BTreeMap, BTreeSet};

use als_syntax::{define_id, ArenaId};

use crate::ir::RelId;

define_id! {
    /// Index of one atom within its [`Universe`].
    pub struct AtomId;
}

/// The fixed, ordered set of atoms a solving run ranges over.
///
/// Atom order is decided once, at construction, and is part of the
/// deterministic input to everything downstream (variable numbering derives
/// from it).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Universe {
    names: Vec<String>,
}

impl Universe {
    /// Creates a universe from atom names in their canonical order.
    ///
    /// # Panics
    /// Panics if two atoms share a name — duplicate atoms are an internal
    /// invariant violation by the bounds builder.
    #[must_use]
    pub fn new(names: Vec<String>) -> Self {
        let distinct: BTreeSet<&str> = names.iter().map(String::as_str).collect();
        assert!(
            distinct.len() == names.len(),
            "duplicate atom name in universe: {} names, {} distinct",
            names.len(),
            distinct.len()
        );
        Self { names }
    }

    /// The name of `atom`.
    #[must_use]
    pub fn name(&self, atom: AtomId) -> &str {
        &self.names[atom.index()]
    }

    /// Number of atoms.
    #[must_use]
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// Whether the universe is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    /// Iterates `(id, name)` in canonical atom order.
    pub fn iter(&self) -> impl Iterator<Item = (AtomId, &str)> {
        self.names
            .iter()
            .enumerate()
            .map(|(index, name)| (AtomId::from_index(index), name.as_str()))
    }
}

/// An ordered sequence of atoms; the element of a [`TupleSet`].
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Tuple(Vec<AtomId>);

impl Tuple {
    /// Creates a tuple.
    ///
    /// # Panics
    /// Panics on an empty atom list — arity 0 does not exist in the
    /// relational logic.
    #[must_use]
    pub fn new(atoms: Vec<AtomId>) -> Self {
        assert!(!atoms.is_empty(), "tuple arity must be >= 1");
        Self(atoms)
    }

    /// Number of atoms (>= 1).
    #[must_use]
    pub fn arity(&self) -> usize {
        self.0.len()
    }

    /// The atoms, in position order.
    #[must_use]
    pub fn atoms(&self) -> &[AtomId] {
        &self.0
    }
}

/// A set of same-arity tuples with deterministic (lexicographic) iteration.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TupleSet {
    arity: usize,
    tuples: BTreeSet<Tuple>,
}

impl TupleSet {
    /// Creates an empty tuple set of the given arity.
    ///
    /// # Panics
    /// Panics if `arity == 0`.
    #[must_use]
    pub fn empty(arity: usize) -> Self {
        assert!(arity >= 1, "tuple set arity must be >= 1");
        Self {
            arity,
            tuples: BTreeSet::new(),
        }
    }

    /// Inserts a tuple; returns whether it was newly added.
    ///
    /// # Panics
    /// Panics on arity mismatch (STYLE I1: arities agree through every
    /// operation).
    pub fn insert(&mut self, tuple: Tuple) -> bool {
        assert!(
            tuple.arity() == self.arity,
            "arity mismatch: set={} tuple={}",
            self.arity,
            tuple.arity()
        );
        self.tuples.insert(tuple)
    }

    /// The common arity of all member tuples.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// Number of tuples.
    #[must_use]
    pub fn len(&self) -> usize {
        self.tuples.len()
    }

    /// Whether the set has no tuples.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.tuples.is_empty()
    }

    /// Membership test.
    #[must_use]
    pub fn contains(&self, tuple: &Tuple) -> bool {
        self.tuples.contains(tuple)
    }

    /// Whether every tuple of `self` is in `other`.
    #[must_use]
    pub fn is_subset_of(&self, other: &TupleSet) -> bool {
        self.tuples.is_subset(&other.tuples)
    }

    /// Iterates tuples in lexicographic atom order (deterministic, C2).
    pub fn iter(&self) -> impl Iterator<Item = &Tuple> {
        self.tuples.iter()
    }
}

/// Lower/upper bound pair for one relation.
///
/// Invariant (checked at construction): same arity, and `lower ⊆ upper`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RelBound {
    lower: TupleSet,
    upper: TupleSet,
}

impl RelBound {
    /// Creates a bound, checking the containment invariant.
    ///
    /// # Panics
    /// Panics if arities differ or `lower ⊄ upper` — an ill-formed bound is a
    /// bounds-builder bug, never user input.
    #[must_use]
    pub fn new(lower: TupleSet, upper: TupleSet) -> Self {
        assert!(
            lower.arity() == upper.arity(),
            "arity mismatch: lower={} upper={}",
            lower.arity(),
            upper.arity()
        );
        assert!(
            lower.is_subset_of(&upper),
            "bound invariant violated: lower not a subset of upper"
        );
        Self { lower, upper }
    }

    /// An exact bound: the relation must equal `tuples`.
    #[must_use]
    pub fn exact(tuples: TupleSet) -> Self {
        Self {
            lower: tuples.clone(),
            upper: tuples,
        }
    }

    /// Tuples the relation must contain.
    #[must_use]
    pub fn lower(&self) -> &TupleSet {
        &self.lower
    }

    /// Tuples the relation may contain.
    #[must_use]
    pub fn upper(&self) -> &TupleSet {
        &self.upper
    }
}

/// Bounds for every relation of an [`crate::ir::Ir`], over one [`Universe`].
///
/// Keyed by `BTreeMap` for deterministic iteration in `RelId` order (C2:
/// key order — `RelId` order is allocation order, which is fixed).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Bounds {
    /// The atom universe.
    pub universe: Universe,
    bounds: BTreeMap<RelId, RelBound>,
}

impl Bounds {
    /// Creates an empty bounds table over `universe`.
    #[must_use]
    pub fn new(universe: Universe) -> Self {
        Self {
            universe,
            bounds: BTreeMap::new(),
        }
    }

    /// Binds `rel`.
    ///
    /// # Panics
    /// Panics if `rel` is already bound — double-binding is a bounds-builder
    /// bug. (Arity against the declared `Relation` is asserted by the
    /// translator, which owns both the `Ir` and the `Bounds`.)
    pub fn bind(&mut self, rel: RelId, bound: RelBound) {
        let previous = self.bounds.insert(rel, bound);
        assert!(previous.is_none(), "relation bound twice: {rel:?}");
    }

    /// Replaces the bound of an **already-bound** `rel` (mt-035): the
    /// `util/ordering` pinning tightens `First`/`Next` from their ordinary
    /// field bounds to exact constants after `alloc_fields` bound them.
    ///
    /// # Panics
    /// Panics if `rel` is not already bound — the pinning targets a field
    /// relation the bounds builder allocated.
    pub fn rebind(&mut self, rel: RelId, bound: RelBound) {
        let previous = self.bounds.insert(rel, bound);
        assert!(previous.is_some(), "rebind of an unbound relation: {rel:?}");
    }

    /// The bound for `rel`, if bound.
    #[must_use]
    pub fn get(&self, rel: RelId) -> Option<&RelBound> {
        self.bounds.get(&rel)
    }

    /// Iterates `(rel, bound)` in `RelId` order (deterministic).
    pub fn iter(&self) -> impl Iterator<Item = (RelId, &RelBound)> {
        self.bounds.iter().map(|(&rel, bound)| (rel, bound))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use als_syntax::ArenaId;

    fn atom(index: usize) -> AtomId {
        AtomId::from_index(index)
    }

    #[test]
    fn tuple_set_iterates_in_lexicographic_order() {
        let mut set = TupleSet::empty(2);
        set.insert(Tuple::new(vec![atom(1), atom(0)]));
        set.insert(Tuple::new(vec![atom(0), atom(1)]));
        set.insert(Tuple::new(vec![atom(0), atom(0)]));
        let order: Vec<Vec<AtomId>> = set.iter().map(|t| t.atoms().to_vec()).collect();
        assert_eq!(
            order,
            vec![
                vec![atom(0), atom(0)],
                vec![atom(0), atom(1)],
                vec![atom(1), atom(0)],
            ]
        );
    }

    #[test]
    #[should_panic(expected = "arity mismatch")]
    fn tuple_set_rejects_arity_mismatch() {
        let mut set = TupleSet::empty(2);
        set.insert(Tuple::new(vec![atom(0)]));
    }

    #[test]
    #[should_panic(expected = "lower not a subset of upper")]
    fn rel_bound_rejects_lower_outside_upper() {
        let mut lower = TupleSet::empty(1);
        lower.insert(Tuple::new(vec![atom(0)]));
        let upper = TupleSet::empty(1);
        let _ = RelBound::new(lower, upper);
    }

    #[test]
    fn universe_rejects_duplicate_atoms() {
        let result =
            std::panic::catch_unwind(|| Universe::new(vec!["A$0".to_owned(), "A$0".to_owned()]));
        assert!(result.is_err());
    }
}
