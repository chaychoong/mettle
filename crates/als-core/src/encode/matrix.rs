//! The **boolean matrix** — the value every [`crate::ir::RelExpr`] encodes to.
//!
//! Behaviorally a Kodkod boolean matrix: an `arity`-dimensional relation over
//! the universe where each candidate tuple carries a [`Bool`] saying whether it
//! is present. The representation is **sparse** — only tuples that *can* be true
//! (the computed upper bound of the sub-expression) are stored; any absent tuple
//! is [`Bool::FALSE`]. This keeps the dense `|universe|^arity` grid from ever
//! being materialised while staying exact.
//!
//! Determinism (STYLE D2): cells live in a [`BTreeMap`] keyed by [`Tuple`], so
//! every traversal is in lexicographic tuple order — the same order the
//! variable allocator uses, so Tseitin numbering is stable.

use std::collections::BTreeMap;

use crate::bounds::Tuple;

use super::circuit::Bool;

/// A sparse boolean matrix: the encoded value of a relation expression.
#[derive(Clone, Debug)]
pub struct Matrix {
    arity: usize,
    /// Present-cell formulas, keyed by tuple (lexicographic iteration).
    /// A tuple absent from the map is [`Bool::FALSE`] by convention.
    cells: BTreeMap<Tuple, Bool>,
}

impl Matrix {
    /// An empty matrix of the given arity (every tuple false).
    #[must_use]
    pub fn empty(arity: usize) -> Self {
        debug_assert!(arity >= 1, "matrix arity must be >= 1");
        Self {
            arity,
            cells: BTreeMap::new(),
        }
    }

    /// The common arity of every tuple.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// Sets `tuple`'s cell, unless it is a constant false (kept sparse).
    ///
    /// # Panics
    /// Panics (debug) on an arity mismatch — a translator invariant (STYLE I1).
    pub fn set(&mut self, tuple: Tuple, value: Bool) {
        debug_assert!(
            tuple.arity() == self.arity,
            "matrix arity mismatch: matrix={} tuple={}",
            self.arity,
            tuple.arity()
        );
        if matches!(value, Bool::Const(false)) {
            return;
        }
        self.cells.insert(tuple, value);
    }

    /// The formula for `tuple` (false when absent — the sparse convention).
    #[must_use]
    pub fn get(&self, tuple: &Tuple) -> Bool {
        self.cells.get(tuple).copied().unwrap_or(Bool::FALSE)
    }

    /// Whether `tuple` has a stored (possibly-true) cell.
    #[must_use]
    pub fn contains_key(&self, tuple: &Tuple) -> bool {
        self.cells.contains_key(tuple)
    }

    /// Iterates `(tuple, cell)` in lexicographic tuple order.
    pub fn iter(&self) -> impl Iterator<Item = (&Tuple, Bool)> {
        self.cells.iter().map(|(t, &b)| (t, b))
    }

    /// The stored (candidate) tuples, in lexicographic order.
    pub fn tuples(&self) -> impl Iterator<Item = &Tuple> {
        self.cells.keys()
    }

    /// Number of stored candidate cells.
    #[must_use]
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether no candidate cells are stored (the matrix is constantly empty).
    #[must_use]
    #[allow(
        dead_code,
        reason = "paired with `len` for clippy::len_without_is_empty"
    )]
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Mutable access to a cell slot, inserting `Bool::FALSE` if absent — used by
    /// the encoder's or-accumulating merges.
    pub fn entry_or_false(&mut self, tuple: Tuple) -> &mut Bool {
        self.cells.entry(tuple).or_insert(Bool::FALSE)
    }
}
