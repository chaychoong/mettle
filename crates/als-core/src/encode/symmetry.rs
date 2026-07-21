//! Symmetry breaking — the Kodkod lex-leader predicate, bit-exactly (mt-048,
//! translation-ref §16).
//!
//! Two pieces, matching the jar's `SymmetryDetector` + `SymmetryBreaker`:
//!
//! 1. [`build_plan`] computes the **coarsest partition** of the universe's atoms
//!    into symmetry classes (§16.2) from the goal's relation bounds, and the
//!    **relation order** for SBP generation (§16.3): every post-skolem
//!    non-constant relation, sorted by `(arity asc, name asc byte-wise)`.
//! 2. [`Encoder::generate_sbp`](super::Encoder::generate_sbp) turns that plan into
//!    a single [`Bool`] — the conjunction of lex-leq circuits over every adjacent
//!    atom pair of every class (§16.3) — conjoined with the goal circuit by
//!    [`super::Encoder::finish_goal`] (unless the goal folded to a constant,
//!    §16.1.5).
//!
//! **Determinism (STYLE D1/D2).** The partition is computed by an exact-signature
//! grouping (see [`build_plan`]) that is a pure function of the bounds; classes
//! are ordered canonically by ascending minimum atom index; relations are sorted
//! by `(arity, name)`; every tuple traversal is in `BTreeSet`/`BTreeMap` key
//! order. No hash iteration anywhere near the SBP.
//!
//! **What never changes.** The SBP adds only Tseitin auxiliary variables and
//! extra clauses; the **primary-variable set is untouched**, so enumeration still
//! blocks over exactly the primary variables and instance decoding is unchanged.
//! A lex-leader predicate is verdict-neutral (§16, §10.12).

use std::collections::{BTreeMap, BTreeSet};

use crate::bounds::{AtomId, Bounds, Tuple};
use crate::ir::{Ir, RelId};

use als_syntax::ArenaId;

/// One atom's continuation tuple within an input tupleset (a tuple with one
/// column removed), the value the partition signature groups on.
type Continuation = Vec<AtomId>;
/// An atom's full symmetry signature: for each `(tupleset ordinal, column)`, the
/// set of continuation tuples it appears with. Two atoms are in the same class iff
/// their signatures are equal (see [`detect_partition`]).
type Signature = BTreeMap<(usize, usize), BTreeSet<Continuation>>;

/// The precomputed symmetry-breaking plan for one command (translation-ref §16).
///
/// `classes` are the atom-symmetry classes in canonical order (ascending
/// minimum). `relparts` are the post-skolem **non-constant** relations, sorted by
/// `(arity asc, name asc byte-wise)` — the exact order the jar's `relParts()`
/// produces (SymmetryBreaker.java:284).
#[derive(Clone, Debug)]
pub(crate) struct SbpPlan {
    /// Symmetry classes, each a sorted (ascending) list of atoms; classes
    /// themselves ordered by ascending minimum atom index.
    classes: Vec<Vec<AtomId>>,
    /// Relations that contribute SBP bits, in `(arity, name)` order.
    relparts: Vec<RelId>,
}

impl SbpPlan {
    /// Whether the plan can generate any SBP bits at all: at least one class with
    /// an adjacent pair (≥ 2 atoms) and at least one contributing relation.
    pub(crate) fn is_trivial(&self) -> bool {
        self.relparts.is_empty() || self.classes.iter().all(|c| c.len() < 2)
    }

    /// The classes, in canonical order.
    pub(crate) fn classes(&self) -> &[Vec<AtomId>] {
        &self.classes
    }

    /// The relation order for SBP generation.
    pub(crate) fn relparts(&self) -> &[RelId] {
        &self.relparts
    }
}

/// Computes the [`SbpPlan`] for a goal over `bounds` (translation-ref §16.2/§16.3).
///
/// Every atom in `[int_start, universe.len())` — the int run **and** the string
/// tail that follows it — refines the partition as its own singleton,
/// **unconditionally**: the jar's per-integer exact bounds and per-string-atom
/// `s2k` singletons (A4Solution.java:391–400) are always present on its solve
/// path, which never mention-gates them (§16.1.1, probes Y6/uf1-SB20/fmrun).
/// `bounds` is the **post-skolem** augmented bounds (base + skolem relations),
/// so `relparts` sees the skolems that eat SBP slots first among their arity
/// (§16.3).
pub(crate) fn build_plan(ir: &Ir, bounds: &Bounds, int_start: usize) -> SbpPlan {
    let usize_n = bounds.universe.len();
    let classes = detect_partition(ir, bounds, int_start, usize_n);
    let relparts = rel_parts(ir, bounds);
    SbpPlan { classes, relparts }
}

/// Whether a relation is a **skolem** (name begins with `$`) — user identifiers
/// cannot start with `$`, so this is unambiguous (translation-ref §16.1/§16.3).
fn is_skolem(ir: &Ir, rel: RelId) -> bool {
    ir.relations[rel].name.starts_with('$')
}

/// Whether a relation is one of the three **builtin sig relations** (`Int`,
/// `seq/Int`, `String`), excluded from partition refinement. `Int` is not a
/// bounds relation on the jar side at all (the Alloy `Int` sig translates to
/// `Expression.INTS`); `seq/Int` and `String` are, but their exact uppers can
/// only ever split int/string atoms — which the unconditional per-atom
/// singletons (§16.1.1, [`build_plan`]) already reduce to singleton classes —
/// so excluding them is exactly refinement-neutral. Identified by name (the
/// bounds builder mints exactly these three spellings).
fn is_builtin_sig(ir: &Ir, rel: RelId) -> bool {
    matches!(
        ir.relations[rel].name.as_str(),
        "Int" | "seq/Int" | "String"
    )
}

/// Detects the coarsest symmetry partition (translation-ref §16.2).
///
/// # Algorithm
/// The coarsest partition `P` such that every input tupleset is a union of
/// cross-products of `P`-classes has an exact, non-iterative characterization:
/// two atoms `a`, `b` are in the same class **iff** for every input tupleset `T`
/// and every column position `i`, the set of *continuation tuples*
/// `{ t with column i removed : t ∈ T, t[i] = a }` is identical for `a` and `b`.
///
/// *Necessity:* if the continuations differ, some `t ∈ T` with `t[i]=a` has
/// `t[i:=b] ∉ T`, so the block containing `t` is not a full class-product unless
/// `a`, `b` are separated. *Sufficiency:* if all continuations agree, transform
/// any `t ∈ T` into any same-class-profile tuple one column at a time — each step
/// stays in `T` because that column's continuation set matches — so every
/// class-product block is contained in `T`. Hence grouping atoms by their full
/// signature profile (over all `T`, all `i`) is exactly the coarsest sound
/// partition. Atoms mentioned by no tupleset share the empty profile and form one
/// class (the jar's "everything else").
///
/// **Scope of the equivalence (mt-048 review).** Kodkod's `refinePartitions`
/// carries one deliberate departure from the union-of-products spec: atoms whose
/// slice of a tupleset is *exactly* the full-diagonal tuple `(a, a, …, a)` are
/// grouped together (`idenPartition`, SymmetryDetector.java:210–221), where this
/// grouping splits them into singletons. The two coincide on every bounds shape
/// mettle's builder can emit — unary sets, cross-products (owner-stripped or
/// not), consecutive-pair chains (`Int/next`, ordering), and singletons — none of
/// which has a diagonal-only slice; `iden` itself is a relational *constant*,
/// never a bounded relation. If a future bounds shape can put `(a, a, …, a)` as
/// some atom's only slice of a bound, this function must grow the jar's
/// diagonal special-case.
///
/// The inputs are the same tuplesets the jar's `SymmetryDetector` refines on
/// (§16.2): an unconditional singleton per int and per string atom (the jar's
/// per-integer exact bounds + per-string-atom `s2k` singletons, never
/// mention-gated on its solve path — §16.1.1) and, for each **non-skolem,
/// non-builtin** relation, its lower bound (iff non-empty and strictly smaller
/// than upper) and its upper bound (iff non-empty).
fn detect_partition(
    ir: &Ir,
    bounds: &Bounds,
    int_start: usize,
    usize_n: usize,
) -> Vec<Vec<AtomId>> {
    // Each tupleset is fed as an (index, &[Tuple]) pair; the signature keys on the
    // tupleset's ordinal so different tuplesets never alias. We collect the raw
    // tuple lists first (owned singletons for int/string atoms, borrowed for
    // relations).
    let mut tuplesets: Vec<Vec<&Tuple>> = Vec::new();
    let mut atom_singletons: Vec<Tuple> = Vec::new();

    // Per-int and per-string-atom exact singletons, unconditionally (§16.1.1):
    // the universe lays out sig atoms, then the int run, then the string tail,
    // so `[int_start, usize_n)` is exactly the ints + strings.
    for i in int_start..usize_n {
        atom_singletons.push(Tuple::new(vec![AtomId::from_index(i)]));
    }
    for t in &atom_singletons {
        tuplesets.push(vec![t]);
    }

    // Retained relation bounds (§16.2): non-skolem, non-builtin. Lower iff
    // non-empty and strictly smaller than upper; upper iff non-empty.
    for (rel, bound) in bounds.iter() {
        if is_skolem(ir, rel) || is_builtin_sig(ir, rel) {
            continue;
        }
        let lower = bound.lower();
        let upper = bound.upper();
        if !lower.is_empty() && lower.len() < upper.len() {
            tuplesets.push(lower.iter().collect());
        }
        if !upper.is_empty() {
            tuplesets.push(upper.iter().collect());
        }
    }

    // Signature of each atom: map (tupleset ordinal, column) → set of continuation
    // tuples (the other columns, in order). Two atoms are in the same class iff
    // their whole signature maps are equal.
    let mut sigs: BTreeMap<AtomId, Signature> = BTreeMap::new();
    // Seed every atom with an empty signature so unmentioned atoms group together.
    for i in 0..usize_n {
        sigs.insert(AtomId::from_index(i), Signature::new());
    }
    for (ts_idx, tuples) in tuplesets.iter().enumerate() {
        for t in tuples {
            let atoms = t.atoms();
            for i in 0..atoms.len() {
                let mut cont: Continuation = Vec::with_capacity(atoms.len() - 1);
                cont.extend_from_slice(&atoms[..i]);
                cont.extend_from_slice(&atoms[i + 1..]);
                sigs.entry(atoms[i])
                    .or_default()
                    .entry((ts_idx, i))
                    .or_default()
                    .insert(cont);
            }
        }
    }

    // Group atoms by identical signature. `BTreeMap` keyed by the signature keeps
    // this deterministic; classes then sorted by ascending minimum atom.
    let mut by_sig: BTreeMap<Signature, Vec<AtomId>> = BTreeMap::new();
    for (atom, sig) in sigs {
        by_sig.entry(sig).or_default().push(atom);
    }
    let mut classes: Vec<Vec<AtomId>> = by_sig.into_values().collect();
    for c in &mut classes {
        c.sort_unstable();
    }
    classes.sort_unstable_by_key(|c| c[0].index());
    classes
}

/// The relation order for SBP generation (translation-ref §16.3,
/// SymmetryBreaker.java:284 `relParts`): every relation in the post-skolem bounds
/// whose `lower.size() != upper.size()` (constants skipped), sorted by **arity
/// ascending, then name ascending byte-wise** (Java `String.compareTo` = UTF-16
/// code-unit order; ASCII in practice, which byte-wise `str` ordering matches).
/// `$`-prefixed skolems sort before `this/…` at the same arity, so they eat SBP
/// slots first — truncation-visible.
fn rel_parts(ir: &Ir, bounds: &Bounds) -> Vec<RelId> {
    let mut parts: Vec<RelId> = bounds
        .iter()
        .filter(|(_, bound)| bound.lower().len() != bound.upper().len())
        .map(|(rel, _)| rel)
        .collect();
    parts.sort_by(|&a, &b| {
        let ra = &ir.relations[a];
        let rb = &ir.relations[b];
        ra.arity
            .cmp(&rb.arity)
            .then_with(|| ra.name.as_bytes().cmp(rb.name.as_bytes()))
    });
    parts
}
