//! The type representation (resolution-doc §4.1, ADR-0008 decision 5).
//!
//! A [`Type`] is a value: a boolean/small-int flag plus a **union of products
//! of prim [`SigId`]s**, kept maximal per arity by subsumption on `add`. This
//! mirrors `ast/Type.java` *behaviorally* (STYLE M1) without porting its shape.
//!
//! Hierarchy-dependent operations (`join`, `intersect`, subtype, `is_int`) take
//! a `&ResolvedWorld` because product columns are prim sigs whose descendant
//! relation lives in the sig arena — the `Type` value itself stays pure.

use crate::world::{ResolvedWorld, SigId};

/// One product entry: a tuple of prim-sig columns. Arity = column count.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Product(pub Vec<SigId>);

impl Product {
    /// Arity (column count) of this product.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.0.len()
    }
}

/// A relational / boolean / integer type (resolution-doc §4.1).
///
/// - `EMPTY` (`entries` empty, not bool, not small-int) is the **ill-typed**
///   sentinel; the invariant `type == EMPTY iff errors nonempty` is asserted at
///   the resolver boundary (STYLE I1).
/// - `FORMULA` (`entries` empty, `is_bool`) is the boolean type.
/// - `smallIntType` (`is_small_int`, `entries == [[Int]]`) is the primitive-int
///   type, distinct from the `Int` sig relation (resolution-doc §4.5).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Type {
    /// Boolean/formula flag.
    pub is_bool: bool,
    /// Primitive-int marker (`#e`, `sum`, `fun/add`, …).
    pub is_small_int: bool,
    /// Maximal product entries (subsumption-reduced per arity).
    pub entries: Vec<Product>,
}

impl Type {
    /// The ill-typed sentinel (`EMPTY`).
    #[must_use]
    pub fn empty() -> Self {
        Self {
            is_bool: false,
            is_small_int: false,
            entries: Vec::new(),
        }
    }

    /// The boolean/formula type (`FORMULA`).
    #[must_use]
    pub fn formula() -> Self {
        Self {
            is_bool: true,
            is_small_int: false,
            entries: Vec::new(),
        }
    }

    /// The primitive-int type (`smallIntType`): `{Int}` with the small-int
    /// marker.
    #[must_use]
    pub fn small_int(int_sig: SigId) -> Self {
        Self {
            is_bool: false,
            is_small_int: true,
            entries: vec![Product(vec![int_sig])],
        }
    }

    /// A single unary product `{sig}` (a prim-sig reference's bounding type).
    #[must_use]
    pub fn unary(sig: SigId) -> Self {
        Self {
            is_bool: false,
            is_small_int: false,
            entries: vec![Product(vec![sig])],
        }
    }

    /// A single product from an explicit column list.
    #[must_use]
    pub fn product_of(cols: Vec<SigId>) -> Self {
        Self {
            is_bool: false,
            is_small_int: false,
            entries: vec![Product(cols)],
        }
    }

    /// The ill-typed sentinel test (`type == EMPTY`).
    #[must_use]
    pub fn is_error(&self) -> bool {
        !self.is_bool && !self.is_small_int && self.entries.is_empty()
    }

    /// Whether this type carries at least one relational product.
    #[must_use]
    pub fn has_entries(&self) -> bool {
        !self.entries.is_empty()
    }

    /// The set of arities present (as a small sorted vec; arities are tiny).
    #[must_use]
    pub fn arities(&self) -> Vec<usize> {
        let mut a: Vec<usize> = self.entries.iter().map(Product::arity).collect();
        a.sort_unstable();
        a.dedup();
        a
    }

    /// Whether some product has arity `k`.
    #[must_use]
    pub fn has_arity(&self, k: usize) -> bool {
        self.entries.iter().any(|p| p.arity() == k)
    }

    /// Whether `self` and `other` share any product arity (resolution-doc §4.2
    /// `hasCommonArity`).
    #[must_use]
    pub fn has_common_arity(&self, other: &Type) -> bool {
        self.entries.iter().any(|p| other.has_arity(p.arity()))
    }

    /// Whether this type is an integer relation (`is_int`): some **unary**
    /// product whose column is `Int` or a descendant (resolution-doc §4.1/§4.5).
    #[must_use]
    pub fn is_int(&self, w: &ResolvedWorld) -> bool {
        self.entries
            .iter()
            .any(|p| p.arity() == 1 && w.is_same_or_descendent(p.0[0], w.builtins.int))
    }

    /// Adds a product with subsumption (resolution-doc §4.1 `Type.add`): drop
    /// existing entries subsumed by `prod`, skip `prod` if already subsumed.
    fn add(&mut self, w: &ResolvedWorld, prod: Product) {
        if self.entries.iter().any(|e| product_subtype(w, &prod, e)) {
            return; // subsumed by an existing (more general) entry
        }
        self.entries.retain(|e| !product_subtype(w, e, &prod));
        self.entries.push(prod);
    }

    /// Union / merge (`+`, resolution-doc §4.2): all entries of both, subsumed.
    /// The `+` operator additionally requires a common arity (checked by the
    /// caller); `Type` merge itself just unions.
    #[must_use]
    pub fn union(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type::empty();
        for p in self.entries.iter().chain(&other.entries) {
            out.add(w, p.clone());
        }
        out
    }

    /// Intersection (`&`, resolution-doc §4.2): pointwise column meet over
    /// products of equal arity.
    #[must_use]
    pub fn intersect(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type::empty();
        for pa in &self.entries {
            for pb in &other.entries {
                if pa.arity() != pb.arity() {
                    continue;
                }
                if let Some(cols) = meet_columns(w, pa, pb) {
                    out.add(w, Product(cols));
                }
            }
        }
        out
    }

    /// Relational join (`.`, resolution-doc §4.2): drop the touching columns
    /// when they intersect; arity `a + b - 2`. Result may be `EMPTY` (then the
    /// node becomes a deferred `ExprBadJoin`, resolution-doc §4.4).
    #[must_use]
    pub fn join(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type::empty();
        for pa in &self.entries {
            for pb in &other.entries {
                if pa.arity() < 1 || pb.arity() < 1 {
                    continue;
                }
                let last = pa.0[pa.arity() - 1];
                let first = pb.0[0];
                if !columns_intersect(w, last, first) {
                    continue;
                }
                let arity = pa.arity() + pb.arity() - 2;
                if arity == 0 {
                    continue; // join of two unaries has no relational result
                }
                let mut cols = Vec::with_capacity(arity);
                cols.extend_from_slice(&pa.0[..pa.arity() - 1]);
                cols.extend_from_slice(&pb.0[1..]);
                out.add(w, Product(cols));
            }
        }
        out
    }

    /// Product (`->`, resolution-doc §4.2): every left entry concatenated with
    /// every right entry; arities add.
    #[must_use]
    pub fn product(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type::empty();
        for pa in &self.entries {
            for pb in &other.entries {
                let mut cols = pa.0.clone();
                cols.extend_from_slice(&pb.0);
                out.add(w, Product(cols));
            }
        }
        out
    }

    /// Transpose (`~`, binary only): reverse each binary product's columns.
    #[must_use]
    pub fn transpose(&self) -> Type {
        Type {
            is_bool: false,
            is_small_int: false,
            entries: self
                .entries
                .iter()
                .filter(|p| p.arity() == 2)
                .map(|p| Product(vec![p.0[1], p.0[0]]))
                .collect(),
        }
    }

    /// Whether `self` and `other` have a non-empty intersection *as types*
    /// (resolution-doc §4.4 `intersects`): both boolean, or a shared product.
    #[must_use]
    pub fn intersects(&self, w: &ResolvedWorld, other: &Type) -> bool {
        if self.is_bool && other.is_bool {
            return true;
        }
        if (self.is_small_int || self.is_int(w)) && (other.is_small_int || other.is_int(w)) {
            return true;
        }
        !self.intersect(w, other).entries.is_empty()
    }

    /// The relevant-type projection for `resolve_as_set` (`removesBoolAndInt`):
    /// drop the boolean flag; a `smallIntType` becomes the `Int` sig relation.
    #[must_use]
    pub fn as_set(&self, int_sig: SigId) -> Type {
        if self.is_small_int && self.entries.is_empty() {
            return Type::unary(int_sig);
        }
        Type {
            is_bool: false,
            is_small_int: false,
            entries: self.entries.clone(),
        }
    }
}

/// Whether product `sub` is a subtype of product `sup`: equal arity and every
/// column of `sub` is the same as or a descendant of `sup`'s.
fn product_subtype(w: &ResolvedWorld, sub: &Product, sup: &Product) -> bool {
    sub.arity() == sup.arity()
        && sub
            .0
            .iter()
            .zip(&sup.0)
            .all(|(&a, &b)| w.is_same_or_descendent(a, b))
}

/// Whether two prim-sig columns intersect (share a common subtype).
fn columns_intersect(w: &ResolvedWorld, a: SigId, b: SigId) -> bool {
    w.is_same_or_descendent(a, b) || w.is_same_or_descendent(b, a)
}

/// The pointwise meet of two equal-arity products, or `None` if any column
/// pair is disjoint. Each column meet is the more specific of the two.
fn meet_columns(w: &ResolvedWorld, a: &Product, b: &Product) -> Option<Vec<SigId>> {
    let mut cols = Vec::with_capacity(a.arity());
    for (&x, &y) in a.0.iter().zip(&b.0) {
        if w.is_same_or_descendent(x, y) {
            cols.push(x);
        } else if w.is_same_or_descendent(y, x) {
            cols.push(y);
        } else {
            return None;
        }
    }
    Some(cols)
}
