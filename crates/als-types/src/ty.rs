//! The type representation (resolution-doc §4.1, ADR-0008 decision 5).
//!
//! A [`Type`] is a value: a boolean/small-int flag plus a **union of products
//! of prim [`SigId`]s**, kept maximal per arity by subsumption on `add`. This
//! is a faithful port of `ast/Type.java` (STYLE M1) — including the reference's
//! crucial behavior of **keeping empty (`NONE->..->NONE`) products with their
//! arity** rather than collapsing them (mt-022). A product whose first column
//! is `none` is an *empty product of a known arity*; only an **arity-0** product
//! is dropped (`add`). This distinguishes "empty because the columns are
//! disjoint" (a legal-arity relation that happens to be empty — a relevance
//! warning) from "no product at all" (`EMPTY`, the ill-typed / illegal-join
//! sentinel). The previous representation dropped both, which is the coarseness
//! ADR-0009 identified as the blocker.
//!
//! Hierarchy-dependent operations (`join`, `intersect`, subtype, `is_int`) take
//! a `&ResolvedWorld` because product columns are prim sigs whose descendant
//! relation lives in the sig arena — the `Type` value itself stays pure.

use crate::world::{ResolvedWorld, SigId};

/// One product entry: a tuple of prim-sig columns. Arity = column count.
///
/// A product is **empty** (`is_empty`) iff arity 0 or its first column is
/// `none` — the reference's `ProductType.isEmpty` (`NONE` in any column makes
/// the whole tuple `NONE->..->NONE`, so column 0 suffices).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Product(pub Vec<SigId>);

impl Product {
    /// Arity (column count) of this product.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.0.len()
    }

    /// Whether this is an empty product (`arity 0` or a `NONE`-headed tuple).
    #[must_use]
    pub fn is_empty(&self, w: &ResolvedWorld) -> bool {
        self.0.is_empty() || self.0[0] == w.builtins.none
    }
}

/// A relational / boolean / integer type (resolution-doc §4.1).
///
/// - `EMPTY` (`entries` empty, not bool, not small-int) is the **ill-typed**
///   sentinel — the reference's `Type.EMPTY`. It is what a make-time error
///   produces (illegal join, arity mismatch, non-binary closure, …).
/// - `FORMULA` (`entries` empty, `is_bool`) is the boolean type.
/// - `smallIntType` (`is_small_int`, `entries == [[Int]]`) is the primitive-int
///   type, distinct from the `Int` sig relation (resolution-doc §4.5).
///
/// Note: a type may have entries that are all empty products (e.g.
/// `{NONE->NONE}`) — that is NOT `EMPTY`; it is a legal arity-2 relation that
/// is statically empty (`has_no_tuple`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Type {
    /// Boolean/formula flag.
    pub is_bool: bool,
    /// Primitive-int marker (`#e`, `sum`, `fun/add`, …).
    pub is_small_int: bool,
    /// Product entries (subsumption-reduced per arity; empty products kept).
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

    /// The ill-typed sentinel test (`type == EMPTY`): zero entries and neither
    /// bool nor small-int.
    #[must_use]
    pub fn is_error(&self) -> bool {
        !self.is_bool && !self.is_small_int && self.entries.is_empty()
    }

    /// Whether this type carries at least one product entry (empty or not).
    #[must_use]
    pub fn has_entries(&self) -> bool {
        !self.entries.is_empty()
    }

    /// Number of product entries (`Type.size`).
    #[must_use]
    pub fn size(&self) -> usize {
        self.entries.len()
    }

    /// Whether some entry is a non-empty tuple (`Type.hasTuple`).
    #[must_use]
    pub fn has_tuple(&self, w: &ResolvedWorld) -> bool {
        self.entries.iter().any(|p| !p.is_empty(w))
    }

    /// Whether no entry is a non-empty tuple (`Type.hasNoTuple`): every entry is
    /// `NONE`-headed (or there are none).
    #[must_use]
    pub fn has_no_tuple(&self, w: &ResolvedWorld) -> bool {
        !self.has_tuple(w)
    }

    /// The set of arities present (as a small sorted vec; arities are tiny).
    #[must_use]
    pub fn arities(&self) -> Vec<usize> {
        let mut a: Vec<usize> = self.entries.iter().map(Product::arity).collect();
        a.sort_unstable();
        a.dedup();
        a
    }

    /// Whether some product has arity `k` (`Type.hasArity`).
    #[must_use]
    pub fn has_arity(&self, k: usize) -> bool {
        k > 0 && self.entries.iter().any(|p| p.arity() == k)
    }

    /// If every entry has the same arity, return it; if entries differ in
    /// arity, return `None` (the reference's `arity()` returning `-1`); if no
    /// entries, `Some(0)`. (`Type.arity`.)
    #[must_use]
    pub fn arity(&self) -> Option<usize> {
        let mut ans: Option<usize> = None;
        for p in &self.entries {
            match ans {
                None => ans = Some(p.arity()),
                Some(a) if a != p.arity() => return None,
                Some(_) => {}
            }
        }
        Some(ans.unwrap_or(0))
    }

    /// Whether `self` and `other` share any product arity (`Type.hasCommonArity`).
    #[must_use]
    pub fn has_common_arity(&self, other: &Type) -> bool {
        self.entries
            .iter()
            .any(|p| other.entries.iter().any(|q| p.arity() == q.arity()))
    }

    /// Whether this type is an integer relation (`is_int`): some **unary**
    /// product whose column is `Int` (exactly `SIGINT`, resolution-doc §4.1).
    /// The reference checks `e.get(0) == Sig.SIGINT` (not a descendant).
    #[must_use]
    pub fn is_int(&self, w: &ResolvedWorld) -> bool {
        self.entries
            .iter()
            .any(|p| p.arity() == 1 && p.0[0] == w.builtins.int)
    }

    /// Adds a product with subsumption + arity-0 drop (`Type.add`): an arity-0
    /// product is dropped; otherwise drop existing entries subsumed by `prod`,
    /// skip `prod` if already subsumed by an existing (more general) entry.
    fn add(&mut self, w: &ResolvedWorld, prod: Product) {
        if prod.arity() == 0 {
            return; // the reference drops arity-0 products (its `zero`).
        }
        if self.entries.iter().any(|e| product_subtype(w, &prod, e)) {
            return;
        }
        self.entries.retain(|e| !product_subtype(w, e, &prod));
        self.entries.push(prod);
    }

    /// Merge (`Type.merge` for products of a peer type): union of entries,
    /// preserving `is_bool` as the OR (`is_small_int` follows `self`). Used for
    /// `+` bottom-up union and gathering candidate types.
    #[must_use]
    pub fn merge(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type {
            is_bool: self.is_bool || other.is_bool,
            is_small_int: false,
            entries: self.entries.clone(),
        };
        for p in &other.entries {
            out.add(w, p.clone());
        }
        out
    }

    /// Plain relational union (`+`): all entries of both, subsumed, never bool.
    #[must_use]
    pub fn union(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type::empty();
        for p in self.entries.iter().chain(&other.entries) {
            out.add(w, p.clone());
        }
        out
    }

    /// `unionWithCommonArity`: `{A | A in this, A.arity in that} ∪ {B | B in
    /// that, B.arity in this}`. `EMPTY` if no common arity.
    #[must_use]
    pub fn union_with_common_arity(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type::empty();
        for p in &self.entries {
            if other.has_arity(p.arity()) {
                out.add(w, p.clone());
            }
        }
        for q in &other.entries {
            if self.has_arity(q.arity()) {
                out.add(w, q.clone());
            }
        }
        out
    }

    /// `pickCommonArity`: `{A in this | A.arity in that}`. `EMPTY` if none.
    #[must_use]
    pub fn pick_common_arity(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type::empty();
        for p in &self.entries {
            if other.has_arity(p.arity()) {
                out.add(w, p.clone());
            }
        }
        out
    }

    /// `extract(k)`: `{A in this | A.arity == k}`.
    #[must_use]
    pub fn extract(&self, w: &ResolvedWorld, k: usize) -> Type {
        let mut out = Type::empty();
        for p in &self.entries {
            if p.arity() == k {
                out.add(w, p.clone());
            }
        }
        out
    }

    /// Intersection (`Type.intersect`): pointwise column meet over products of
    /// equal arity, **keeping** `NONE`-headed empty products (they carry arity).
    #[must_use]
    pub fn intersect(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type::empty();
        for pa in &self.entries {
            for pb in &other.entries {
                if pa.arity() != pb.arity() {
                    continue;
                }
                out.add(w, meet_columns(w, pa, pb));
            }
        }
        out
    }

    /// Relational join (`Type.join`): joins each product pair whose combined
    /// arity `> 0` (skips unary·unary), keeping `NONE`-headed results. Result is
    /// `EMPTY` iff no pair had combined arity `> 0` — i.e. both sides are
    /// entirely unary (the illegal-join / `ExprBadJoin` case, resolution-doc
    /// §4.2/§4.4).
    #[must_use]
    pub fn join(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type::empty();
        if self.entries.is_empty() || other.entries.is_empty() {
            return out;
        }
        for pa in &self.entries {
            for pb in &other.entries {
                if pa.arity() > 1 || pb.arity() > 1 {
                    out.add(w, join_products(w, pa, pb));
                }
            }
        }
        out
    }

    /// Product (`Type.product`): every left entry concatenated with every right
    /// entry; arities add. A product touching an empty operand is `NONE`-filled.
    #[must_use]
    pub fn product(&self, w: &ResolvedWorld, other: &Type) -> Type {
        let mut out = Type::empty();
        for pa in &self.entries {
            for pb in &other.entries {
                out.add(w, product_products(w, pa, pb));
            }
        }
        out
    }

    /// Transpose (`~`, binary only): reverse each binary product's columns;
    /// non-binary products dropped. `EMPTY` if there is no binary product.
    #[must_use]
    pub fn transpose(&self, w: &ResolvedWorld) -> Type {
        let mut out = Type::empty();
        for p in &self.entries {
            if p.arity() == 2 {
                out.add(w, Product(vec![p.0[1], p.0[0]]));
            }
        }
        out
    }

    /// Transitive closure (`^`): `u + u.u + u.u.u + …` over the binary entries
    /// (`Type.closure`). `EMPTY` if there is no binary entry.
    #[must_use]
    pub fn closure(&self, w: &ResolvedWorld) -> Type {
        let mut ans = self.extract(w, 2);
        let u = ans.clone();
        let mut uu = u.clone();
        loop {
            uu = uu.join(w, &u);
            let old = ans.clone();
            ans = ans.union_with_common_arity(w, &uu);
            if ans == old {
                break;
            }
        }
        ans
    }

    /// Domain restriction `A <: r` (`right.domainRestrict(left)` in the
    /// reference): for each unary product `b` of `A` and each product `a` of
    /// `r`, restrict `a`'s first column by `b`. `EMPTY` if `A` has no unary
    /// product or `r` is empty.
    #[must_use]
    pub fn domain_restrict(&self, w: &ResolvedWorld, dom: &Type) -> Type {
        let mut out = Type::empty();
        if self.entries.is_empty() || !dom.has_arity(1) {
            return out;
        }
        for b in &dom.entries {
            if b.arity() != 1 {
                continue;
            }
            for a in &self.entries {
                out.add(w, column_restrict(w, a, b.0[0], 0));
            }
        }
        out
    }

    /// Range restriction `r :> A` (`left.rangeRestrict(right)`): restrict each
    /// product's **last** column by each unary product of `A`.
    #[must_use]
    pub fn range_restrict(&self, w: &ResolvedWorld, ran: &Type) -> Type {
        let mut out = Type::empty();
        if self.entries.is_empty() || !ran.has_arity(1) {
            return out;
        }
        for b in &ran.entries {
            if b.arity() != 1 {
                continue;
            }
            for a in &self.entries {
                let last = a.arity().saturating_sub(1);
                out.add(w, column_restrict(w, a, b.0[0], last));
            }
        }
        out
    }

    /// Whether `self` and `other` have a non-empty intersection *as types*
    /// (`Type.intersects` — the boolean): some pair of equal-arity **non-empty**
    /// products whose columns pairwise intersect. Bool/int handled by the
    /// caller (`resolveHelper`), not here.
    #[must_use]
    pub fn intersects(&self, w: &ResolvedWorld, other: &Type) -> bool {
        for pa in &self.entries {
            if pa.is_empty(w) {
                continue;
            }
            for pb in &other.entries {
                if pa.arity() == pb.arity() && !pb.is_empty(w) && products_intersect(w, pa, pb) {
                    return true;
                }
            }
        }
        false
    }

    /// `removesBoolAndInt`: drop the boolean flag and small-int marker, keeping
    /// the product entries. A pure `smallIntType` (no product but the marker,
    /// or `{Int}` marked small-int) becomes the `Int` sig relation.
    #[must_use]
    pub fn remove_bool_and_int(&self, int_sig: SigId) -> Type {
        if self.is_small_int && self.entries.is_empty() {
            return Type::unary(int_sig);
        }
        Type {
            is_bool: false,
            is_small_int: false,
            entries: self.entries.clone(),
        }
    }

    /// The relevant-type projection for `resolve_as_set`/decl bounds
    /// (`removesBoolAndInt`): identical to [`Self::remove_bool_and_int`]. Kept
    /// as a named alias at the resolver call sites.
    #[must_use]
    pub fn as_set(&self, int_sig: SigId) -> Type {
        self.remove_bool_and_int(int_sig)
    }
}

/// Whether product `sub` is a subtype of product `sup`: equal arity and every
/// column of `sub` is the same as or a descendant of `sup`'s
/// (`ProductType.isSubtypeOf`).
fn product_subtype(w: &ResolvedWorld, sub: &Product, sup: &Product) -> bool {
    sub.arity() == sup.arity()
        && sub
            .0
            .iter()
            .zip(&sup.0)
            .all(|(&a, &b)| w.is_same_or_descendent(a, b))
}

/// The meet of two prim-sig columns (`PrimSig.intersect`): the descendant of
/// the two, or `none` if neither descends from the other.
fn col_meet(w: &ResolvedWorld, a: SigId, b: SigId) -> SigId {
    if w.is_same_or_descendent(a, b) {
        a
    } else if w.is_same_or_descendent(b, a) {
        b
    } else {
        w.builtins.none
    }
}

/// Whether two prim-sig columns have a non-empty meet (`PrimSig.intersects`):
/// one descends from the other **and** the meet is not `none`.
fn col_intersects(w: &ResolvedWorld, a: SigId, b: SigId) -> bool {
    let none = w.builtins.none;
    if w.is_same_or_descendent(a, b) {
        a != none
    } else if w.is_same_or_descendent(b, a) {
        b != none
    } else {
        false
    }
}

/// The pointwise meet of two equal-arity products (`ProductType.intersect`): a
/// `NONE`-filled product if any column pair is disjoint.
fn meet_columns(w: &ResolvedWorld, a: &Product, b: &Product) -> Product {
    if a.is_empty(w) {
        return a.clone();
    }
    if b.is_empty(w) {
        return b.clone();
    }
    let none = w.builtins.none;
    let mut cols = Vec::with_capacity(a.arity());
    for (&x, &y) in a.0.iter().zip(&b.0) {
        let c = col_meet(w, x, y);
        if c == none {
            return Product(vec![none; a.arity()]);
        }
        cols.push(c);
    }
    Product(cols)
}

/// Whether two equal-arity non-empty products intersect (`ProductType.intersects`).
fn products_intersect(w: &ResolvedWorld, a: &Product, b: &Product) -> bool {
    a.0.iter().zip(&b.0).all(|(&x, &y)| col_intersects(w, x, y))
}

/// The relational join of two products (`ProductType.join`): drop the touching
/// columns; a `NONE`-filled result if they are disjoint. Precondition (enforced
/// by the caller): combined arity `> 0`.
fn join_products(w: &ResolvedWorld, a: &Product, b: &Product) -> Product {
    let left = a.arity();
    let right = b.arity();
    if left <= 1 && right <= 1 {
        return Product(Vec::new()); // arity-0, dropped by `add`
    }
    let arity = left + right - 2;
    let meet = col_meet(w, a.0[left - 1], b.0[0]);
    if meet == w.builtins.none {
        return Product(vec![w.builtins.none; arity]);
    }
    let mut cols = Vec::with_capacity(arity);
    cols.extend_from_slice(&a.0[..left - 1]);
    cols.extend_from_slice(&b.0[1..]);
    Product(cols)
}

/// The cross product of two products (`ProductType.product`): concatenation, or
/// a `NONE`-filled tuple of the summed arity if either is empty.
fn product_products(w: &ResolvedWorld, a: &Product, b: &Product) -> Product {
    let n = a.arity() + b.arity();
    if a.is_empty(w) || b.is_empty(w) {
        return Product(vec![w.builtins.none; n]);
    }
    let mut cols = Vec::with_capacity(n);
    cols.extend_from_slice(&a.0);
    cols.extend_from_slice(&b.0);
    Product(cols)
}

/// Restrict column `idx` of product `a` by unary sig `b` (`ProductType.columnRestrict`):
/// meet that one column; `NONE`-fill if the meet is empty.
fn column_restrict(w: &ResolvedWorld, a: &Product, b: SigId, idx: usize) -> Product {
    if a.is_empty(w) || idx >= a.arity() {
        return a.clone();
    }
    let c = col_meet(w, a.0[idx], b);
    if c == w.builtins.none {
        return Product(vec![w.builtins.none; a.arity()]);
    }
    let mut cols = a.0.clone();
    cols[idx] = c;
    Product(cols)
}
