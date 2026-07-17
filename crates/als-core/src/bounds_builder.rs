//! Bounds builder: the second translation phase (mt-030, translation-ref §1.4).
//!
//! [`compute_bounds`] is a faithful **behavioral** port of the reference's
//! `BoundsComputer` plus the `Int`/`seq`/`String` builtin bounds the
//! `A4Solution` constructor builds (behavior, not structure — PORTING prime
//! directive). Given a [`ResolvedWorld`] and mt-029's [`ScopedUniverse`] for
//! one command, it produces, over a shared [`Ir`]:
//!
//! - a [`Bounds`] — one [`RelBound`] per allocated [`RelId`];
//! - a **denotation seam** for the next bead (mt-031, expression lowering): for
//!   every sig and field, the [`RelExprId`] that denotes it. A sig is *not*
//!   always one relation (translation-ref §1.4): a leaf is a fresh relation; a
//!   non-abstract sig with children is the union of its children plus a fresh
//!   `<Sig>_remainder` relation; an abstract sig with children is just that
//!   union; an `in` subset sig is a fresh relation; an exact (`=`) subset sig
//!   *is* the union of its parents (no relation). Each such shape is prebuilt
//!   into the `Ir` as one `RelExprId` so mt-031 consumes it directly.
//! - the **constraint formulas** `BoundsComputer` adds, as [`FormulaId`]s in the
//!   same `Ir`: sibling disjointness, subset-sig containment (`r in ⋃parents`),
//!   and per-sig **size**/**multiplicity** formulas built as quantified formulas
//!   **over atoms** (never `#sig` cardinality — cardinality routes through
//!   bitwidth integer arithmetic and would wrongly interact with overflow when a
//!   scope exceeds the max int; translation-ref §1.4). When the bounds alone
//!   pin a sig (`upper.len() <= scope`) no size formula is emitted.
//!
//! Builtin bounds (translation-ref §1.4, `A4Solution` ctor): `Int` is bound
//! **exactly** to the integer atoms, `seq/Int` exactly to the first `maxseq`
//! non-negative integer atoms. `univ`/`none`/`iden` are IR **constants**
//! ([`RelConst`]), not relations — they are given constant denotations, never
//! allocated.
//!
//! **Deferred (documented, never a wrong verdict):**
//! - **String** is Rung 4 (ADR-0011): the `String` relation is bound **exactly
//!   empty** (mettle mints no string atoms yet, mt-029), and `String`
//!   references denote that empty relation, consistent with what mt-031 needs.
//! - The `Int/min`/`Int/max`/`Int/next`/`Int/zero` integer-ordering relations
//!   the jar's `A4Solution` also builds are **not** allocated here — they belong
//!   to Rung-4 integer fidelity (translation-ref §9); Rung-3 models do not need
//!   them for a correct verdict.
//! - **`var` (temporal) sigs** get the same *static* sibling disjointness as
//!   static sigs this rung; the `[electrum]` temporal disjointness variant is
//!   Rung 6 (translation-ref §1.4). Recorded in LIMITATIONS.
//! - **`util/ordering` exact-bound pinning** of `first`/`next` is mt-035
//!   (LEDGER-004): the ordering module's sigs/fields get ordinary bounds here.
//!
//! Determinism (STYLE D1/D2): [`RelId`] allocation order is fixed — the `Int`,
//! `seq/Int`, `String` builtins, then prim sig relations in `SigId` order, then
//! subset sig relations in `SigId` order, then field relations in `FieldId`
//! order — and every set iterates in key order (`BTreeSet`/`BTreeMap`).

use std::collections::{BTreeMap, BTreeSet};

use als_syntax::ast::SigMult;
use als_syntax::{ArenaId, Span};
use als_types::{FieldId, ResolvedWorld, SigId, SigKind};

use crate::bounds::{AtomId, Bounds, RelBound, Tuple, TupleSet, Universe};
use crate::ir::{
    Formula, FormulaId, FormulaKind, Ir, MultTest, QuantKind, RelBinOp, RelCmpOp, RelConst,
    RelExpr, RelExprId, RelExprKind, RelId, Relation, Var,
};
use crate::scope::ScopedUniverse;

/// The whole output of the bounds phase (translation-ref §1.4) and mt-031's
/// input: the [`Bounds`], the per-sig/field denotation seam, and the constraint
/// formulas allocated into the shared [`Ir`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BoundsResult {
    /// One [`RelBound`] per allocated [`RelId`], over the command's universe.
    pub bounds: Bounds,
    /// How to denote each sig as a relational expression (translation-ref
    /// §1.4). Total over every sig mt-031 can reference: user prim sigs, subset
    /// sigs, and the builtins (`Int`/`seq/Int`/`String` as relations;
    /// `univ`/`none` as constants).
    pub sig_denote: BTreeMap<SigId, RelExprId>,
    /// How to denote each field as a relational expression. For an ordinary
    /// field this is the field relation; for a **`one`-sig** field (whose stored
    /// relation drops the singleton owner column) it is `owner -> stored`, so
    /// the denotation always has the field's full arity (translation-ref §1.4).
    pub field_denote: BTreeMap<FieldId, RelExprId>,
    /// The sig-hierarchy / subset / size / multiplicity constraint formulas, in
    /// deterministic emission order. mt-031 conjoins these into the goal (§2.5).
    pub constraints: Vec<FormulaId>,
}

/// Computes the relation bounds, denotation seam, and constraint formulas for
/// one command (translation-ref §1.4), allocating relations, expressions, and
/// formulas into `ir`. A faithful behavioral port of `BoundsComputer` plus the
/// `A4Solution` builtin bounds; see the module docs for what defers.
#[must_use]
pub fn compute_bounds(world: &ResolvedWorld, scoped: &ScopedUniverse, ir: &mut Ir) -> BoundsResult {
    let mut builder = BoundsBuilder::new(world, scoped, ir);
    builder.compute_atom_bounds();
    builder.alloc_builtins();
    builder.alloc_prim_relations();
    builder.build_prim_denotations();
    builder.alloc_subset_sigs();
    builder.alloc_fields();
    builder.pin_ordering();
    builder.emit_prim_constraints();
    builder.finish()
}

/// The mutable working state of the bounds build. Atom bounds are `BTreeSet`s
/// of [`AtomId`] (never a hash set — they feed relation bounds and thus CNF
/// numbering, STYLE D2).
struct BoundsBuilder<'a> {
    world: &'a ResolvedWorld,
    scoped: &'a ScopedUniverse,
    ir: &'a mut Ir,
    /// Scopable prim children of each sig, in `SigId` (declaration) order.
    children: BTreeMap<SigId, Vec<SigId>>,
    /// Per-sig lower atom set (bottom-up): tuples the sig *must* contain.
    lower: BTreeMap<SigId, BTreeSet<AtomId>>,
    /// Per-sig upper atom set (top-down): tuples the sig *may* contain.
    upper: BTreeMap<SigId, BTreeSet<AtomId>>,
    /// The relation allocated for a *leaf* prim sig (its own tuples).
    leaf_rel: BTreeMap<SigId, RelId>,
    /// The `<Sig>_remainder` relation of a non-abstract sig with children.
    remainder_rel: BTreeMap<SigId, RelId>,
    /// The **stored** relation of each field (the arity-stripped one for a
    /// `one`-sig owner) — mt-035 rebinds `util/ordering`'s `First`/`Next` here.
    field_rel: BTreeMap<FieldId, RelId>,
    // --- outputs being assembled ---
    bounds: Bounds,
    sig_denote: BTreeMap<SigId, RelExprId>,
    field_denote: BTreeMap<FieldId, RelExprId>,
    constraints: Vec<FormulaId>,
}

impl<'a> BoundsBuilder<'a> {
    fn new(world: &'a ResolvedWorld, scoped: &'a ScopedUniverse, ir: &'a mut Ir) -> Self {
        let mut children: BTreeMap<SigId, Vec<SigId>> = BTreeMap::new();
        for (id, sig) in world.sigs.iter() {
            if let SigKind::Prim { parent: Some(p) } = &sig.kind {
                if is_scopable(world, id) {
                    children.entry(*p).or_default().push(id);
                }
            }
        }
        let bounds = Bounds::new(scoped.universe.clone());
        Self {
            world,
            scoped,
            ir,
            children,
            lower: BTreeMap::new(),
            upper: BTreeMap::new(),
            leaf_rel: BTreeMap::new(),
            remainder_rel: BTreeMap::new(),
            field_rel: BTreeMap::new(),
            bounds,
            sig_denote: BTreeMap::new(),
            field_denote: BTreeMap::new(),
            constraints: Vec::new(),
        }
    }

    fn finish(self) -> BoundsResult {
        BoundsResult {
            bounds: self.bounds,
            sig_denote: self.sig_denote,
            field_denote: self.field_denote,
            constraints: self.constraints,
        }
    }

    /// The scopable prim children of `sig`, in declaration order.
    fn kids(&self, sig: SigId) -> Vec<SigId> {
        self.children.get(&sig).cloned().unwrap_or_default()
    }

    // ============================ atom bounds ============================

    /// Fills [`Self::lower`]/[`Self::upper`] for every scopable prim sig
    /// (translation-ref §1.4): lower bottom-up (children's lowers + own minted
    /// atoms when exact), upper top-down (each still-growable child absorbs the
    /// parent's floating atoms).
    fn compute_atom_bounds(&mut self) {
        // Bottom-up lower + upper-initialised-to (lower ∪ minted).
        for (id, _) in self.world.sigs.iter() {
            if is_scopable(self.world, id) && self.is_top_level(id) {
                self.lower_of(id);
            }
        }
        // Top-down growth from each top-level sig.
        for (id, _) in self.world.sigs.iter() {
            if is_scopable(self.world, id) && self.is_top_level(id) {
                self.grow_children(id);
            }
        }
    }

    /// Recursively computes `lower[sig]` (children's lowers plus `sig`'s minted
    /// atoms when exact) and seeds `upper[sig] = lower[sig] ∪ minted[sig]`
    /// (minted atoms always join the upper). Returns `lower[sig]`.
    fn lower_of(&mut self, sig: SigId) -> BTreeSet<AtomId> {
        let mut lower = BTreeSet::new();
        for kid in self.kids(sig) {
            lower.extend(self.lower_of(kid));
        }
        let minted = self.minted_atoms(sig);
        let mut upper = lower.clone();
        upper.extend(minted.iter().copied());
        if self.is_exact(sig) {
            lower.extend(minted);
        }
        self.lower.insert(sig, lower.clone());
        self.upper.insert(sig, upper);
        lower
    }

    /// Adds the parent's floating atoms (its upper minus every child's lower) to
    /// each child that can still grow (`scope(child) > lower(child).len()`,
    /// translation-ref §1.4), then recurses. Idempotent per sig.
    fn grow_children(&mut self, sig: SigId) {
        let kids = self.kids(sig);
        let mut floating = self.upper[&sig].clone();
        for kid in &kids {
            for a in &self.lower[kid] {
                floating.remove(a);
            }
        }
        for kid in &kids {
            let scope = self.scope_of(*kid);
            if usize::try_from(scope).unwrap_or(usize::MAX) > self.lower[kid].len() {
                if let Some(child_upper) = self.upper.get_mut(kid) {
                    child_upper.extend(floating.iter().copied());
                }
            }
        }
        for kid in kids {
            self.grow_children(kid);
        }
    }

    // ======================= relation allocation =======================

    /// Allocates and binds the builtin `Int`/`seq/Int`/`String` relations and
    /// records the `univ`/`none`/`Int`/`seq/Int`/`String` denotations
    /// (translation-ref §1.4).
    fn alloc_builtins(&mut self) {
        let b = self.world.builtins;
        // `univ`/`none` are relational constants, never allocated.
        let univ = self.mk_rel_expr(RelExprKind::Const(RelConst::Univ), self.sig_span(b.univ));
        self.sig_denote.insert(b.univ, univ);
        let none = self.mk_rel_expr(RelExprKind::Const(RelConst::None), self.sig_span(b.none));
        self.sig_denote.insert(b.none, none);

        let int_atoms = self.int_atoms();
        self.bind_builtin(b.int, "Int", &int_atoms);
        let seq_atoms = self.seq_atoms();
        self.bind_builtin(b.seq_int, "seq/Int", &seq_atoms);
        // String: no string atoms yet (Rung 4) — bound exactly empty.
        self.bind_builtin(b.string, "String", &BTreeSet::new());
    }

    /// Allocates a builtin relation, binds it exactly to `atoms`, and records
    /// its `Relation` denotation.
    fn bind_builtin(&mut self, sig: SigId, name: &str, atoms: &BTreeSet<AtomId>) {
        let span = self.sig_span(sig);
        let rel = self.ir.relations.alloc(Relation {
            name: name.to_owned(),
            arity: 1,
            span,
        });
        self.bounds
            .bind(rel, RelBound::exact(unary_tupleset(atoms)));
        let denote = self.mk_rel_expr(RelExprKind::Relation(rel), span);
        self.sig_denote.insert(sig, denote);
    }

    /// Allocates and binds the prim-sig relations in `SigId` order
    /// (translation-ref §1.4): a leaf sig → one `[lower, upper]` relation; a
    /// non-abstract sig with children → a `<Sig>_remainder` relation holding the
    /// parent's floating atoms; an abstract sig with children → no own relation.
    fn alloc_prim_relations(&mut self) {
        for (id, sig) in self.world.sigs.iter() {
            if !is_scopable(self.world, id) {
                continue;
            }
            let kids = self.kids(id);
            if kids.is_empty() {
                let rel = self.alloc_named(&sig.qualified_name, 1, sig.span);
                let bound = RelBound::new(
                    unary_tupleset(&self.lower[&id]),
                    unary_tupleset(&self.upper[&id]),
                );
                self.bounds.bind(rel, bound);
                self.leaf_rel.insert(id, rel);
            } else if !sig.is_abstract {
                let name = format!("{}_remainder", sig.qualified_name);
                let rel = self.alloc_named(&name, 1, sig.span);
                let floating = unary_tupleset(&self.floating(id));
                // An **exact** non-abstract parent pins its remainder to *all*
                // its floating atoms (lower == upper), so `#sig` equals its exact
                // scope — the children only re-tag those atoms, they cannot shrink
                // the parent (translation-ref §1.4; the reference binds
                // `A_remainder` exactly, jar-verified probe T14a). A non-exact
                // parent keeps the ordinary `[{}, floating]` bound, so its
                // population may float below scope (probe B6). Without this an
                // `exactly N`/`util/ordering` parent with a subsig under-counts
                // (its remainder could go empty).
                let bound = if self.is_exact(id) {
                    RelBound::exact(floating)
                } else {
                    RelBound::new(TupleSet::empty(1), floating)
                };
                self.bounds.bind(rel, bound);
                self.remainder_rel.insert(id, rel);
            }
        }
    }

    /// The parent's floating atoms (its upper minus every child's lower) — the
    /// remainder relation's upper bound (translation-ref §1.4).
    fn floating(&self, sig: SigId) -> BTreeSet<AtomId> {
        let mut floating = self.upper[&sig].clone();
        for kid in self.kids(sig) {
            for a in &self.lower[&kid] {
                floating.remove(a);
            }
        }
        floating
    }

    /// Builds the denotation `RelExprId` of every prim sig (translation-ref
    /// §1.4). Post-order so a parent's union references its children's already
    /// built denotations.
    fn build_prim_denotations(&mut self) {
        for (id, _) in self.world.sigs.iter() {
            if is_scopable(self.world, id) {
                self.denote_prim(id);
            }
        }
    }

    /// The denotation of a prim sig, memoised: a leaf is its relation; a
    /// non-abstract parent is `⋃children + remainder`; an abstract parent is
    /// `⋃children` (translation-ref §1.4).
    fn denote_prim(&mut self, sig: SigId) -> RelExprId {
        if let Some(&d) = self.sig_denote.get(&sig) {
            return d;
        }
        let kids = self.kids(sig);
        let span = self.sig_span(sig);
        let denote = if kids.is_empty() {
            let rel = self.leaf_rel[&sig];
            self.mk_rel_expr(RelExprKind::Relation(rel), span)
        } else {
            let mut parts: Vec<RelExprId> = kids.iter().map(|&k| self.denote_prim(k)).collect();
            if let Some(&rem) = self.remainder_rel.get(&sig) {
                parts.push(self.mk_rel_expr(RelExprKind::Relation(rem), span));
            }
            self.union_of(&parts, span)
        };
        self.sig_denote.insert(sig, denote);
        denote
    }

    /// Allocates and binds the subset sigs in `SigId` order (translation-ref
    /// §1.4): an exact (`=`) subset sig *is* the union of its parents (no
    /// relation, no formula); an `in` subset sig gets a fresh relation bounded
    /// by that union with an `r in ⋃parents` containment formula.
    fn alloc_subset_sigs(&mut self) {
        for (id, _) in self.world.sigs.iter() {
            if matches!(self.world.sigs[id].kind, SigKind::Subset { .. }) {
                self.denote_subset(id);
            }
        }
    }

    /// The denotation of a subset sig, memoised (translation-ref §1.4).
    fn denote_subset(&mut self, sig: SigId) -> RelExprId {
        if let Some(&d) = self.sig_denote.get(&sig) {
            return d;
        }
        let SigKind::Subset { parents, exact } = self.world.sigs[sig].kind.clone() else {
            unreachable!("denote_subset called on a non-subset sig");
        };
        let span = self.sig_span(sig);
        let parent_denotes: Vec<RelExprId> = parents.iter().map(|&p| self.denote_sig(p)).collect();
        let union = self.union_of(&parent_denotes, span);
        let denote = if exact {
            // An exact `=` subset sig *is* the parents' union — no relation.
            union
        } else {
            let rel = self.alloc_named(&self.world.sigs[sig].qualified_name.clone(), 1, span);
            let upper = self.upper_atoms(sig);
            self.bounds.bind(
                rel,
                RelBound::new(TupleSet::empty(1), unary_tupleset(&upper)),
            );
            let r = self.mk_rel_expr(RelExprKind::Relation(rel), span);
            // r in (⋃ parents).
            let f = self.mk_formula(
                FormulaKind::RelCompare {
                    op: RelCmpOp::Subset,
                    lhs: r,
                    rhs: union,
                },
                span,
            );
            self.constraints.push(f);
            r
        };
        self.sig_denote.insert(sig, denote);
        denote
    }

    /// The denotation of any sig (prim, subset, or builtin), dispatching to the
    /// memoised builders.
    fn denote_sig(&mut self, sig: SigId) -> RelExprId {
        if let Some(&d) = self.sig_denote.get(&sig) {
            return d;
        }
        match self.world.sigs[sig].kind {
            SigKind::Prim { .. } => self.denote_prim(sig),
            SigKind::Subset { .. } => self.denote_subset(sig),
        }
    }

    // ============================== fields ==============================

    /// Allocates and binds every field relation in `FieldId` order
    /// (translation-ref §1.4): a relation whose upper bound is the product of
    /// the per-column sig uppers of the field type; a **`one`-sig** field drops
    /// the singleton owner column from the stored relation and denotes the field
    /// as `owner -> stored`.
    fn alloc_fields(&mut self) {
        for (fid, field) in self.world.fields.iter() {
            let full_arity = field.ty.arity().filter(|&a| a >= 2);
            let Some(full_arity) = full_arity else {
                // A well-typed field is always arity >= 2 (owner + value); a
                // degenerate type cannot arise from an accepted world.
                debug_assert!(false, "field {} has a non-relational type", field.name);
                continue;
            };
            let one_sig = self.is_one_sig(field.owner);
            let stored_arity = if one_sig { full_arity - 1 } else { full_arity };
            let upper = self.field_upper(fid, one_sig);
            let name = format!(
                "{}.{}",
                self.world.sigs[field.owner].qualified_name, field.name
            );
            let rel = self.alloc_named(&name, stored_arity, field.span);
            self.bounds
                .bind(rel, RelBound::new(TupleSet::empty(stored_arity), upper));
            self.field_rel.insert(fid, rel);
            let stored = self.mk_rel_expr(RelExprKind::Relation(rel), field.span);
            let denote = if one_sig {
                // The stored relation is the value columns; the field is the
                // singleton owner re-multiplied: `owner -> stored`.
                let owner = self.denote_sig(field.owner);
                self.mk_rel_expr(
                    RelExprKind::Binary {
                        op: RelBinOp::Product,
                        lhs: owner,
                        rhs: stored,
                    },
                    field.span,
                )
            } else {
                stored
            };
            self.field_denote.insert(fid, denote);
        }
    }

    // ========================= util/ordering =========================

    /// Pins `util/ordering`'s `First`/`Next` field relations to exact constants
    /// over the ordered sig's atoms in universe order (mt-035, LEDGER-004 part
    /// (b), translation-ref §5). This reproduces the reference `Simplifier`'s
    /// exact-bounds shrink on the native total-order relations — the source of
    /// `count = 1` for a childless / enum ordered sig at *every* symmetry setting
    /// (probes T10/T11/T12/T13, jar-verified sym0 = 1).
    ///
    /// **Eligibility (jar-verified sym0, translation-ref §10.1).** The shrink
    /// engages only when the ordered sig `S`'s atom set is fully determined with
    /// no interchangeable atoms: `S` has **no proper subsig** (a leaf — its own
    /// exact atoms `S$0..`), OR `S` is an **`enum`** (its members are `one`
    /// singletons, each atom in its own named sig). A sig with a genuine subsig
    /// partition choice — a proper subsig whose atoms are freely interchangeable
    /// — is left unpinned even when the child fills all of `S` (probe T14e:
    /// `for 3 A, exactly 3 B` is sym0 count **6**, not 1; the jar's sym20 = 1 is
    /// pure symmetry breaking, which mettle does not do). There `first`/`next`
    /// are governed only by the `pred/totalOrder` fact formula (`lower.rs`), and
    /// the enumerated count is the full `n!` set of linear orders. The `enum`
    /// case is the one parent-with-children that pins (probe T13): a non-enum
    /// parent with all-`one` children does **not** (jar-verified sym0 = 6).
    fn pin_ordering(&mut self) {
        for inst in self.world.ordering.clone() {
            let elem = inst.elem;
            // Eligibility: leaf sig, or an enum (all-`one`-singleton children).
            let eligible = self.kids(elem).is_empty() || self.world.sigs[elem].is_enum;
            if !eligible {
                continue;
            }
            // `S`'s determined atoms in universe order (== lower == upper: part
            // (a) forces `S` exact, and an enum's members are `one` sigs).
            let atoms: Vec<AtomId> = self
                .upper
                .get(&elem)
                .map(|s| s.iter().copied().collect())
                .unwrap_or_default();
            let (Some(&first_rel), Some(&next_rel)) = (
                self.field_rel.get(&inst.first),
                self.field_rel.get(&inst.next),
            ) else {
                continue;
            };
            // Only the `one`-sig-`Ord` stored shape (arity 1 `First`, arity 2
            // `Next`) is pinnable to a plain atom order; anything else falls back
            // to the `pred/totalOrder` formula.
            if self.ir.relations[first_rel].arity != 1 || self.ir.relations[next_rel].arity != 2 {
                continue;
            }
            // first = { S$0 } (empty for a degenerate empty ordered sig).
            let mut first_set = TupleSet::empty(1);
            if let Some(&a0) = atoms.first() {
                first_set.insert(Tuple::new(vec![a0]));
            }
            self.bounds.rebind(first_rel, RelBound::exact(first_set));
            // next = { S$0->S$1, S$1->S$2, ... } — the consecutive-atom chain.
            let mut next_set = TupleSet::empty(2);
            for pair in atoms.windows(2) {
                next_set.insert(Tuple::new(vec![pair[0], pair[1]]));
            }
            self.bounds.rebind(next_rel, RelBound::exact(next_set));
        }
    }

    /// The upper bound of a field relation: the union, over each product of the
    /// field type, of the cartesian product of each column sig's upper atoms;
    /// the owner column (column 0) is dropped for a `one`-sig field.
    fn field_upper(&self, fid: FieldId, one_sig: bool) -> TupleSet {
        let field = &self.world.fields[fid];
        let skip = usize::from(one_sig);
        let arity = field.ty.arity().unwrap_or(0).saturating_sub(skip);
        let mut set = TupleSet::empty(arity.max(1));
        for product in &field.ty.entries {
            let cols = &product.0[skip.min(product.0.len())..];
            let col_atoms: Vec<BTreeSet<AtomId>> =
                cols.iter().map(|&c| self.column_atoms(c)).collect();
            insert_product(&mut set, &col_atoms);
        }
        set
    }

    // ========================= sig constraints =========================

    /// Emits the sibling-disjointness, size, and multiplicity constraint
    /// formulas for every prim sig in `SigId` order (translation-ref §1.4).
    fn emit_prim_constraints(&mut self) {
        for (id, _) in self.world.sigs.iter() {
            if !is_scopable(self.world, id) {
                continue;
            }
            self.emit_disjointness(id);
            self.emit_size(id);
            self.emit_multiplicity(id);
        }
    }

    /// Pairwise `no (child_i & child_j)` over `sig`'s children (translation-ref
    /// §1.4). Emitted for every sibling pair (jar-verified: emitted even when the
    /// children's uppers are already disjoint — probe B7). The `var` temporal
    /// variant is Rung 6; static disjointness is used for all sigs this rung.
    fn emit_disjointness(&mut self, sig: SigId) {
        let kids = self.kids(sig);
        for i in 0..kids.len() {
            for j in (i + 1)..kids.len() {
                let a = self.denote_sig(kids[i]);
                let b = self.denote_sig(kids[j]);
                let span = self.sig_span(sig);
                let inter = self.mk_rel_expr(
                    RelExprKind::Binary {
                        op: RelBinOp::Intersect,
                        lhs: a,
                        rhs: b,
                    },
                    span,
                );
                let f = self.mk_formula(
                    FormulaKind::MultTest {
                        test: MultTest::No,
                        expr: inter,
                    },
                    span,
                );
                self.constraints.push(f);
            }
        }
    }

    /// The per-sig size constraint (translation-ref §1.4). Emitted only when the
    /// upper bound is looser than the scope (`upper.len() > scope`); otherwise
    /// the bound alone caps `#sig`, so no formula (jar-verified: probe B1 — a
    /// leaf whose upper equals its scope gets no size formula). Exact sigs are
    /// always bound-pinned (`upper.len() == scope`), so this is always the
    /// inexact `#sig <= scope` case.
    fn emit_size(&mut self, sig: SigId) {
        let scope = usize::try_from(self.scope_of(sig)).unwrap_or(usize::MAX);
        // Exact sig whose atoms are **not** already bound-pinned to `scope`: an
        // **abstract** parent with non-exact children (probe T14d) — its own
        // population has no relation of its own and no exact remainder to pin it,
        // so `A = ⋃children` could float below `scope`. Force `#sig = scope` with
        // `scope` disjoint element-witnesses covering it (translation-ref §1.4,
        // the reference's exact-abstract-parent constraint). Leaf and
        // non-abstract-parent exact sigs are already pinned (their leaf bound /
        // exact remainder), and a fully-`exactly`-childed abstract parent has its
        // lower already at `scope`, so this fires only for the genuine gap.
        // The children's *enforced* lower atoms (each child relation's own lower
        // bound) — for an abstract parent this is all that pins `A = ⋃children`,
        // since `A` has no relation of its own. `self.lower[&sig]` cannot be used:
        // it folds in `sig`'s minted atoms, which for an abstract parent are not
        // bound to any relation.
        let child_lower: BTreeSet<AtomId> = self
            .kids(sig)
            .iter()
            .flat_map(|k| self.lower[k].iter().copied())
            .collect();
        if self.is_exact(sig)
            && self.world.sigs[sig].is_abstract
            && !self.kids(sig).is_empty()
            && child_lower.len() < scope
        {
            let denote = self.denote_sig(sig);
            let span = self.sig_span(sig);
            let f = match scope {
                0 => self.mk_formula(mult_test(MultTest::No, denote), span),
                n => self.build_size_witness_exact(sig, denote, n, span),
            };
            self.constraints.push(f);
            return;
        }
        if self.upper[&sig].len() <= scope {
            return;
        }
        debug_assert!(
            !self.is_exact(sig),
            "an exact sig is bound-pinned (upper == scope), never over-approximated"
        );
        let denote = self.denote_sig(sig);
        let span = self.sig_span(sig);
        let f = match scope {
            0 => self.mk_formula(mult_test(MultTest::No, denote), span),
            1 => self.mk_formula(mult_test(MultTest::Lone, denote), span),
            n => {
                // `no sig or (some v0..v_{n-1}: sig | v0 + .. + v_{n-1} = sig)`:
                // the (non-disjoint) witnesses let the union be 1..n atoms, so
                // `#sig <= n` — a quantified-over-atoms cap that never routes
                // through bitwidth cardinality (translation-ref §1.4).
                let empty = self.mk_formula(mult_test(MultTest::No, denote), span);
                let exists = self.build_size_witness(sig, denote, n, span);
                self.mk_formula(FormulaKind::Or(vec![empty, exists]), span)
            }
        };
        self.constraints.push(f);
    }

    /// Builds `some v0..v_{n-1}: sig | (v0 + .. + v_{n-1}) = sig` — `n` nested
    /// existentials over the sig's own denotation whose (freely overlapping)
    /// union equals the sig (translation-ref §1.4).
    fn build_size_witness(
        &mut self,
        sig: SigId,
        denote: RelExprId,
        n: usize,
        span: Span,
    ) -> FormulaId {
        let name = self.world.sigs[sig].name.clone();
        let mut vars = Vec::with_capacity(n);
        for k in 0..n {
            vars.push(self.ir.vars.alloc(Var {
                name: format!("{name}_sz{k}"),
                arity: 1,
                span,
            }));
        }
        let var_exprs: Vec<RelExprId> = vars
            .iter()
            .map(|&v| self.mk_rel_expr(RelExprKind::Var(v), span))
            .collect();
        let union = self.union_of(&var_exprs, span);
        let mut body = self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Equal,
                lhs: union,
                rhs: denote,
            },
            span,
        );
        // Wrap innermost-first so v0 is the outermost quantifier.
        for &v in vars.iter().rev() {
            body = self.mk_formula(
                FormulaKind::Quant {
                    kind: QuantKind::Some,
                    var: v,
                    bound: denote,
                    body,
                },
                span,
            );
        }
        body
    }

    /// Builds `some v0..v_{n-1}: sig | (v0 + .. + v_{n-1}) = sig and
    /// pairwise-disjoint` — `n` **distinct** element-witnesses covering the sig,
    /// so `#sig = n` exactly (translation-ref §1.4). Unlike
    /// [`Self::build_size_witness`] (a `<= n` cap with freely-overlapping
    /// witnesses), the staged disjointness makes it an equality, matching the
    /// reference's exact-abstract-parent form (probe T14d).
    fn build_size_witness_exact(
        &mut self,
        sig: SigId,
        denote: RelExprId,
        n: usize,
        span: Span,
    ) -> FormulaId {
        let name = self.world.sigs[sig].name.clone();
        let vars: Vec<_> = (0..n)
            .map(|k| {
                self.ir.vars.alloc(Var {
                    name: format!("{name}_ex{k}"),
                    arity: 1,
                    span,
                })
            })
            .collect();
        let var_exprs: Vec<RelExprId> = vars
            .iter()
            .map(|&v| self.mk_rel_expr(RelExprKind::Var(v), span))
            .collect();
        let union = self.union_of(&var_exprs, span);
        let mut parts = vec![self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Equal,
                lhs: union,
                rhs: denote,
            },
            span,
        )];
        // Staged pairwise disjointness: `no (v_k & (v_0 + .. + v_{k-1}))`.
        for k in 1..n {
            let prev = self.union_of(&var_exprs[..k], span);
            let inter = self.mk_rel_expr(
                RelExprKind::Binary {
                    op: RelBinOp::Intersect,
                    lhs: var_exprs[k],
                    rhs: prev,
                },
                span,
            );
            parts.push(self.mk_formula(mult_test(MultTest::No, inter), span));
        }
        // `parts` always holds at least the equality; a lone part needs no `And`.
        let mut body = match parts.pop() {
            Some(only) if parts.is_empty() => only,
            Some(last) => {
                parts.push(last);
                self.mk_formula(FormulaKind::And(parts), span)
            }
            None => unreachable!("witness parts always include the equality"),
        };
        // Wrap innermost-first so v0 is the outermost quantifier.
        for &v in vars.iter().rev() {
            body = self.mk_formula(
                FormulaKind::Quant {
                    kind: QuantKind::Some,
                    var: v,
                    bound: denote,
                    body,
                },
                span,
            );
        }
        body
    }

    /// The sig multiplicity constraint (translation-ref §1.4), when the bounds
    /// do not already guarantee it: `some sig` for a `some` sig with an empty
    /// lower bound; `one sig` for a `one` sig not pinned to a singleton. `lone`
    /// is subsumed by the size cap (scope 1) and needs no separate formula.
    fn emit_multiplicity(&mut self, sig: SigId) {
        let denote = self.denote_sig(sig);
        let span = self.sig_span(sig);
        match self.world.sigs[sig].mult {
            Some(SigMult::Some) if self.lower[&sig].is_empty() => {
                let f = self.mk_formula(mult_test(MultTest::Some, denote), span);
                self.constraints.push(f);
            }
            Some(SigMult::One) if !(self.lower[&sig].len() == 1 && self.upper[&sig].len() == 1) => {
                // Defensive: a non-var `one` sig is always exact-scoped 1 and so
                // bound-pinned; this fires only if that invariant is broken.
                let f = self.mk_formula(mult_test(MultTest::One, denote), span);
                self.constraints.push(f);
            }
            Some(SigMult::One | SigMult::Some | SigMult::Lone) | None => {}
        }
    }

    // ============================== helpers ==============================

    /// Whether `sig` is a top-level user sig (a prim child of `univ`).
    fn is_top_level(&self, sig: SigId) -> bool {
        matches!(self.world.sigs[sig].kind, SigKind::Prim { parent: Some(p) } if p == self.world.builtins.univ)
    }

    /// `sig`'s resolved scope (0 if absent — a subset/builtin, never queried for
    /// its own scope here).
    fn scope_of(&self, sig: SigId) -> u32 {
        self.scoped.scopes.get(sig).map_or(0, |s| s.scope)
    }

    /// Whether `sig`'s scope is exact.
    fn is_exact(&self, sig: SigId) -> bool {
        self.scoped.scopes.get(sig).is_some_and(|s| s.is_exact)
    }

    /// The universe atoms `sig` minted (mt-029), as a set.
    fn minted_atoms(&self, sig: SigId) -> BTreeSet<AtomId> {
        let mut set = BTreeSet::new();
        if let Some(m) = self.scoped.scopes.get(sig).and_then(|s| s.minted) {
            for k in 0..m.count {
                set.insert(AtomId::from_index(m.first.index() + k as usize));
            }
        }
        set
    }

    /// Whether `sig` is a non-`var` `one` sig (the field owner-column strip
    /// applies, translation-ref §1.4).
    fn is_one_sig(&self, sig: SigId) -> bool {
        let s = &self.world.sigs[sig];
        !s.is_var && matches!(s.mult, Some(SigMult::One))
    }

    /// The upper atom set of any sig: a scopable prim sig's computed upper, a
    /// builtin's atom range, or a subset sig's parents' union.
    fn upper_atoms(&self, sig: SigId) -> BTreeSet<AtomId> {
        if let Some(u) = self.upper.get(&sig) {
            return u.clone();
        }
        match &self.world.sigs[sig].kind {
            SigKind::Subset { parents, .. } => {
                let mut set = BTreeSet::new();
                for &p in parents {
                    set.extend(self.upper_atoms(p));
                }
                set
            }
            SigKind::Prim { .. } => self.column_atoms(sig),
        }
    }

    /// The atoms a *column* sig contributes to a field product: a builtin's
    /// atom range or a prim sig's upper (translation-ref §1.4). Type columns are
    /// always prim sigs (resolution §4.1).
    fn column_atoms(&self, sig: SigId) -> BTreeSet<AtomId> {
        let b = self.world.builtins;
        if sig == b.int {
            return self.int_atoms();
        }
        if sig == b.seq_int {
            return self.seq_atoms();
        }
        if sig == b.univ {
            return (0..self.universe().len()).map(AtomId::from_index).collect();
        }
        if sig == b.string || sig == b.none {
            return BTreeSet::new();
        }
        self.upper.get(&sig).cloned().unwrap_or_default()
    }

    /// The integer atoms (the whole `int_atom_range`, ascending).
    fn int_atoms(&self) -> BTreeSet<AtomId> {
        self.scoped
            .int_atom_range()
            .map(AtomId::from_index)
            .collect()
    }

    /// The first `maxseq` **non-negative** integer atoms (`seq/Int`,
    /// translation-ref §1.4): the atoms for values `0 .. maxseq`.
    fn seq_atoms(&self) -> BTreeSet<AtomId> {
        let range = self.scoped.int_atom_range();
        let bw = self.scoped.bitwidth;
        // Value v maps to universe index (range.start + v + 2^(bw-1)); value 0
        // is the first non-negative atom.
        let half = if bw >= 1 { 1usize << (bw - 1) } else { 0 };
        let zero_index = range.start + half;
        let count = usize::try_from(self.scoped.maxseq).unwrap_or(usize::MAX);
        (0..count)
            .map(|v| AtomId::from_index(zero_index + v))
            .filter(|a| a.index() < range.end)
            .collect()
    }

    fn universe(&self) -> &Universe {
        &self.scoped.universe
    }

    fn sig_span(&self, sig: SigId) -> Span {
        self.world.sigs[sig].span
    }

    /// Allocates a fresh `arity`-ary relation named `name`.
    fn alloc_named(&mut self, name: &str, arity: usize, span: Span) -> RelId {
        self.ir.relations.alloc(Relation {
            name: name.to_owned(),
            arity,
            span,
        })
    }

    fn mk_rel_expr(&mut self, kind: RelExprKind, span: Span) -> RelExprId {
        self.ir.rel_exprs.alloc(RelExpr { kind, span })
    }

    fn mk_formula(&mut self, kind: FormulaKind, span: Span) -> FormulaId {
        self.ir.formulas.alloc(Formula { kind, span })
    }

    /// Left-folds `parts` into a union expression (`a + b + ...`). A single part
    /// is returned as-is; the caller guarantees `parts` is non-empty.
    fn union_of(&mut self, parts: &[RelExprId], span: Span) -> RelExprId {
        let Some((&first, rest)) = parts.split_first() else {
            // Callers pass a non-empty slice (a sig's children/parents); a union
            // of nothing is an internal invariant violation, not user input.
            debug_assert!(false, "union of zero relations");
            return self.mk_rel_expr(RelExprKind::Const(RelConst::None), span);
        };
        let mut acc = first;
        for &next in rest {
            acc = self.mk_rel_expr(
                RelExprKind::Binary {
                    op: RelBinOp::Union,
                    lhs: acc,
                    rhs: next,
                },
                span,
            );
        }
        acc
    }
}

/// Whether `sig` is a scopable prim sig — a non-builtin primitive sig (subset
/// sigs and builtins mint no atoms of their own; matches mt-029).
fn is_scopable(world: &ResolvedWorld, sig: SigId) -> bool {
    let s = &world.sigs[sig];
    !s.is_builtin && matches!(s.kind, SigKind::Prim { .. })
}

/// A unary `TupleSet` over `atoms`, in atom order.
fn unary_tupleset(atoms: &BTreeSet<AtomId>) -> TupleSet {
    let mut set = TupleSet::empty(1);
    for &a in atoms {
        set.insert(Tuple::new(vec![a]));
    }
    set
}

/// Inserts the cartesian product of `columns` (one atom set per column) into
/// `set`. An empty column (e.g. `none`, or a sig with no atoms) yields no
/// tuples.
fn insert_product(set: &mut TupleSet, columns: &[BTreeSet<AtomId>]) {
    if columns.is_empty() || columns.iter().any(BTreeSet::is_empty) {
        return;
    }
    let mut rows: Vec<Vec<AtomId>> = vec![Vec::new()];
    for col in columns {
        let mut next = Vec::with_capacity(rows.len() * col.len());
        for row in &rows {
            for &a in col {
                let mut extended = row.clone();
                extended.push(a);
                next.push(extended);
            }
        }
        rows = next;
    }
    for row in rows {
        set.insert(Tuple::new(row));
    }
}

/// A `MultTest` formula kind over `expr`.
fn mult_test(test: MultTest, expr: RelExprId) -> FormulaKind {
    FormulaKind::MultTest { test, expr }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atoms(indices: &[usize]) -> BTreeSet<AtomId> {
        indices.iter().map(|&i| AtomId::from_index(i)).collect()
    }

    #[test]
    fn unary_tupleset_is_in_atom_order() {
        let ts = unary_tupleset(&atoms(&[2, 0, 1]));
        let got: Vec<usize> = ts.iter().map(|t| t.atoms()[0].index()).collect();
        assert_eq!(got, vec![0, 1, 2], "BTreeSet order");
    }

    #[test]
    fn insert_product_is_cartesian() {
        // {0,1} × {2} = {<0,2>, <1,2>} (translation-ref §1.4 field product).
        let mut ts = TupleSet::empty(2);
        insert_product(&mut ts, &[atoms(&[0, 1]), atoms(&[2])]);
        let got: Vec<Vec<usize>> = ts
            .iter()
            .map(|t| t.atoms().iter().map(|a| a.index()).collect())
            .collect();
        assert_eq!(got, vec![vec![0, 2], vec![1, 2]]);
    }

    #[test]
    fn insert_product_with_empty_column_is_empty() {
        // A `none` column (or an empty sig) yields no tuples — a statically
        // empty relation of a known arity (translation-ref §1.4).
        let mut ts = TupleSet::empty(2);
        insert_product(&mut ts, &[atoms(&[0, 1]), BTreeSet::new()]);
        assert!(ts.is_empty());
    }
}
