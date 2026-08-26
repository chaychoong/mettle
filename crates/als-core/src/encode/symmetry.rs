//! Symmetry breaking — the Kodkod lex-leader predicate, bit-exactly (mt-048,
//! translation-ref §16).
//!
//! Two pieces, matching the jar's `SymmetryDetector` + `SymmetryBreaker`:
//!
//! 1. [`build_plan`] computes the **coarsest partition** of the universe's atoms
//!    into symmetry classes (§16.2) from the goal's relation bounds, and the
//!    **relation order** for SBP generation (§16.3): every post-skolem
//!    non-constant relation, sorted by `(arity asc, name asc byte-wise)`.
//!    Both range over the relations the *reference* bounds, which is not quite
//!    the set mettle bounds — see [`is_reference_bounded`] (§16.3.1, mt-134).
//! 2. [`Encoder::generate_sbp`](super::Encoder::generate_sbp) turns that plan into
//!    a single [`Bool`] — the conjunction of lex-leq circuits over every adjacent
//!    atom pair of every class (§16.3) — conjoined with the goal circuit by
//!    [`super::Encoder::finish_goal`].
//!
//! A goal whose circuit folds to constant TRUE gets a **second** plan instead:
//! [`build_trivial_plan`], the partition of the reference's *residual*
//! translation (§16.5, mt-136). See its docs for why that partition is coarser
//! than [`build_plan`]'s.
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
/// (§16.3) — *unless* `temporal` is set, which drops them unconditionally (see
/// [`rel_parts`]).
///
/// # Per-state symmetry breaking (mt-067, alloy6-temporal.md §(d))
///
/// The jar's `SymmetryBreaker.generateSBP` (`:207-259`) special-cases temporal
/// bounds twice: it re-applies the lex-leader constraint **independently at
/// every state** rather than once over the flattened trace, and it skips skolem
/// relations outright (`if (r.isSkolem() && options.temporal()) continue;`,
/// `:231-232`). mettle's unrolled representation makes the first one fall out
/// and needs an explicit gate only for the second:
///
/// - **Atoms are rigid**, so there is one partition for the whole trace. Every
///   per-state copy inherits its original's bound verbatim
///   ([`crate::temporal::unroll`]), so feeding the unrolled bounds to
///   [`detect_partition`] adds `k` identical tuplesets per variable relation —
///   refinement-neutral, i.e. exactly the partition the un-unrolled bounds give.
/// - **Each per-state copy is an ordinary relation** for SBP purposes: it gets
///   the same lex-leader treatment a static relation of the same arity would.
///   The unrolled problem *is* a static problem, so the predicate is as sound
///   and as verdict-neutral here as on the static path.
/// - **Skolems are excluded** when `temporal` — the one thing that does not
///   fall out.
///
/// The bit order within the lex chain is mettle's own (relation-major: a
/// relation's `k` state copies are adjacent, the jar's outer loop is
/// state-major). Any fixed bit order yields a sound lex-leader, and the SBP is
/// Tseitin-only, so this is a disclosed perf/enumeration-order choice, never a
/// verdict one — see [`rel_parts`] for how the `name@s` copies sort.
pub(crate) fn build_plan(ir: &Ir, bounds: &Bounds, int_start: usize, temporal: bool) -> SbpPlan {
    let usize_n = bounds.universe.len();
    let classes = detect_partition(ir, bounds, int_start, usize_n);
    let relparts = rel_parts(ir, bounds, temporal);
    SbpPlan { classes, relparts }
}

/// Computes the [`SbpPlan`] the reference uses to enumerate a **trivially true**
/// goal — the plan of its *residual* translation (translation-ref §16.5,
/// `ExtendedSolver.java:212-260`, mt-136).
///
/// When the goal circuit folds to constant TRUE every assignment within bounds
/// satisfies it, so plain iteration would return one instance forever. The
/// reference instead answers with the trivial instance (every relation at its
/// lower bound) and then re-translates, **from scratch**, the question "which
/// assignment differs from that one": a disjunction over the free relations of
/// `r.some()` (empty lower) or `r != <exact constant = lower>`. That fresh
/// translation keeps only the relations its formula mentions — the free ones,
/// plus the exact constants holding their lowers — and clears the int bounds, so
/// the partition it detects is **strictly coarser** than [`build_plan`]'s:
///
/// - no unconditional per-int / per-string singletons (§16.1.1's tuplesets are
///   not in these bounds at all),
/// - no exact relation refines anything, so a pinned `util/ordering` `Next`
///   chain no longer splits its sig's atoms into singletons,
/// - skolems participate like any other relation (the residual bounds hold no
///   `isSkolem` marks to skip on — the temporal exclusion in [`rel_parts`] is
///   the *other* path's rule).
///
/// The exact constants are bound to the free relations' own lowers, which
/// [`trivial_partition`] already feeds, so re-feeding them would be
/// refinement-neutral; they are simply not modelled. `relparts` needs no
/// residual variant either: [`rel_parts`] already selects exactly the free
/// reference-bounded relations, in the same `(arity, name)` order.
pub(crate) fn build_trivial_plan(ir: &Ir, bounds: &Bounds) -> SbpPlan {
    let classes = trivial_partition(ir, bounds, bounds.universe.len());
    let relparts = rel_parts(ir, bounds, false);
    SbpPlan { classes, relparts }
}

/// Whether a relation is a **skolem** (name begins with `$`) — user identifiers
/// cannot start with `$`, so this is unambiguous (translation-ref §16.1/§16.3).
fn is_skolem(ir: &Ir, rel: RelId) -> bool {
    ir.relations[rel].name.starts_with('$')
}

/// Whether the reference bounds `rel` at all — i.e. whether it would appear in
/// the jar's `bounds.relations()`, the set both [`detect_partition`] and
/// [`rel_parts`] range over (translation-ref §16.2/§16.3).
///
/// The one relation mettle holds that the jar does not is a `$`-metamodel field
/// (mt-107): `BoundsComputer` binds a defined field of a `one` sig to a plain
/// expression and allocates no Kodkod relation for it
/// (`BoundsComputer.java:426-431`), and every metamodel field is built that way
/// (`CompModule.resolveMeta`, `:2170`-`:2228`). mettle keeps a placeholder
/// relation pinned by the defined-field fact, so it must be filtered here or it
/// eats SBP slots the reference spends on real relations (mt-134, §16.3.1).
///
/// Dropping these tuplesets from the partition is **refinement-neutral**, not
/// just faithful: a field's upper bound is a union of products of its columns'
/// sig atom sets ([`crate::bounds_builder`]'s `field_upper`), every sig atom set
/// is itself a union of classes of the partition the remaining relations induce,
/// and a union of class-products never splits a class.
pub(crate) fn is_reference_bounded(ir: &Ir, rel: RelId) -> bool {
    !ir.relations[rel].is_meta_field
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
/// non-builtin, reference-bounded** relation ([`is_reference_bounded`]), its
/// lower bound (iff non-empty and strictly smaller than upper) and its upper
/// bound (iff non-empty).
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

    // Retained relation bounds (§16.2): non-skolem, non-builtin, and one the
    // reference actually bounds. Lower iff non-empty and strictly smaller than
    // upper; upper iff non-empty.
    for (rel, bound) in bounds.iter() {
        if is_skolem(ir, rel) || is_builtin_sig(ir, rel) || !is_reference_bounded(ir, rel) {
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

    partition_by_signature(&tuplesets, usize_n)
}

/// The partition of the reference's **residual** translation (see
/// [`build_trivial_plan`]): the same grouping over a strictly smaller input set —
/// only the free reference-bounded relations' own bounds, with no int/string
/// singletons and no exact relation in sight.
fn trivial_partition(ir: &Ir, bounds: &Bounds, usize_n: usize) -> Vec<Vec<AtomId>> {
    let mut tuplesets: Vec<Vec<&Tuple>> = Vec::new();
    for (rel, bound) in bounds.iter() {
        let (lower, upper) = (bound.lower(), bound.upper());
        if lower.len() == upper.len() || !is_reference_bounded(ir, rel) {
            continue;
        }
        // A free relation's upper strictly contains its lower, so only the
        // lower can be the empty tupleset the jar's non-emptiness check drops.
        if !lower.is_empty() {
            tuplesets.push(lower.iter().collect());
        }
        tuplesets.push(upper.iter().collect());
    }
    partition_by_signature(&tuplesets, usize_n)
}

/// Groups `[0, usize_n)`'s atoms into the coarsest partition `tuplesets` admits —
/// the shared core of [`detect_partition`] and [`trivial_partition`], which
/// differ only in which tuplesets they feed it (see [`detect_partition`] for the
/// correctness argument).
fn partition_by_signature(tuplesets: &[Vec<&Tuple>], usize_n: usize) -> Vec<Vec<AtomId>> {
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
/// SymmetryBreaker.java:284 `relParts`): every **reference-bounded** relation
/// ([`is_reference_bounded`]) in the post-skolem bounds whose
/// `lower.size() != upper.size()` (constants skipped), sorted by **arity
/// ascending, then name ascending byte-wise** (Java `String.compareTo` = UTF-16
/// code-unit order; ASCII in practice, which byte-wise `str` ordering matches).
/// `$`-prefixed skolems sort before `this/…` at the same arity, so they eat SBP
/// slots first — truncation-visible. Under `temporal` they are dropped entirely
/// (`SymmetryBreaker.java:231-232`, alloy6-temporal.md §(d)), so the slots go to
/// the real relations instead.
///
/// **Where the `name@s` per-state copies land.** [`crate::temporal::unroll`]
/// names a copy `<original>@<state>`, and `@` (`0x40`) sorts after every digit
/// (`0x30-0x39`) and before every ASCII letter (`0x41+`), while `/` (`0x2F`) —
/// the module separator every user relation name carries — sorts before all of
/// them. So byte-wise `(arity, name)` ordering puts one original's copies in a
/// contiguous, state-ascending block within its arity group, immediately after
/// any relation whose name is a strict prefix of the original's. The state
/// index is written in decimal without padding, so "ascending" is *decimal*
/// order only while `k <= 10` (states `0..9`); at a wider `steps` bound
/// (`leader.als`'s `15 steps`) the copies order lexicographically
/// (`@0, @1, @10, …, @14, @2, …`). That is deliberate rather than fixed with
/// zero padding: the order is a pure function of the input either way (STYLE
/// D1), it is invisible to verdicts (the SBP is Tseitin-only and truncation
/// only weakens it), and padding would make the copy names depend on `k`, so a
/// relation's name would change between two lengths of the *same* command.
/// Pinned by `per_state_copies_sort_adjacent_and_state_ascending` in
/// `tests/temporal_solve_conformance.rs`.
fn rel_parts(ir: &Ir, bounds: &Bounds, temporal: bool) -> Vec<RelId> {
    let mut parts: Vec<RelId> = bounds
        .iter()
        .filter(|(_, bound)| bound.lower().len() != bound.upper().len())
        .filter(|&(rel, _)| is_reference_bounded(ir, rel))
        .filter(|&(rel, _)| !(temporal && is_skolem(ir, rel)))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bounds::{RelBound, Tuple, TupleSet, Universe};
    use crate::ir::{Mutability, Relation};
    use als_syntax::{FileId, Span};

    fn span() -> Span {
        Span::new(FileId::from_index(0), 0, 1)
    }

    fn unary(atoms: &[usize]) -> TupleSet {
        let mut set = TupleSet::empty(1);
        for &a in atoms {
            set.insert(Tuple::new(vec![AtomId::from_index(a)]));
        }
        set
    }

    /// Allocates `name` with the given unary bounds.
    fn bound(
        ir: &mut Ir,
        bounds: &mut Bounds,
        name: &str,
        lower: &[usize],
        upper: &[usize],
    ) -> RelId {
        let rel = ir.relations.alloc(Relation {
            name: name.to_owned(),
            arity: 1,
            span: span(),
            mutability: Mutability::Static,
            is_meta_field: false,
        });
        bounds.bind(rel, RelBound::new(unary(lower), unary(upper)));
        rel
    }

    /// Allocates `name` with a free unary bound (so it contributes SBP bits).
    fn free(ir: &mut Ir, bounds: &mut Bounds, name: &str) -> RelId {
        bound(ir, bounds, name, &[], &[0, 1])
    }

    /// The classes as plain atom indices, for readable assertions.
    fn class_indices(plan: &SbpPlan) -> Vec<Vec<usize>> {
        plan.classes()
            .iter()
            .map(|c| c.iter().map(|a| a.index()).collect())
            .collect()
    }

    /// Same, but marked as a `$`-metamodel field placeholder — a relation the
    /// reference never bounds (see [`is_reference_bounded`]).
    fn free_meta_field(ir: &mut Ir, bounds: &mut Bounds, name: &str) -> RelId {
        let rel = free(ir, bounds, name);
        ir.relations[rel].is_meta_field = true;
        rel
    }

    fn names(ir: &Ir, parts: &[RelId]) -> Vec<String> {
        parts
            .iter()
            .map(|&r| ir.relations[r].name.clone())
            .collect()
    }

    /// The per-state copies of one original sort **adjacent** and
    /// **state-ascending** within their arity group: `@` (0x40) sorts after every
    /// digit and before every ASCII letter, and `/` (0x2F, in every user
    /// relation name) sorts before both. Pins the ordering claim in
    /// [`rel_parts`]'s docs (mt-067, alloy6-temporal.md §(d)).
    #[test]
    fn per_state_copies_sort_adjacent_and_state_ascending() {
        let mut ir = Ir::default();
        let mut bounds = Bounds::new(Universe::new(vec!["A$0".to_owned(), "A$1".to_owned()]));
        // Deliberately allocated out of order, so only the sort can produce the
        // expected sequence.
        for name in [
            "this/B@1", "this/A@2", "this/A@0", "this/B@0", "this/A@1", "this/AB",
        ] {
            let _ = free(&mut ir, &mut bounds, name);
        }
        assert_eq!(
            names(&ir, &rel_parts(&ir, &bounds, true)),
            vec!["this/A@0", "this/A@1", "this/A@2", "this/AB", "this/B@0", "this/B@1"]
        );
    }

    /// Past ten states the decimal index is no longer byte-ascending — recorded
    /// deliberately rather than papered over with zero padding (see
    /// [`rel_parts`]'s docs): the order stays a pure function of the input and
    /// the SBP stays verdict-neutral either way.
    #[test]
    fn beyond_ten_states_copies_order_lexicographically() {
        let mut ir = Ir::default();
        let mut bounds = Bounds::new(Universe::new(vec!["A$0".to_owned(), "A$1".to_owned()]));
        for name in ["this/A@2", "this/A@10", "this/A@1"] {
            let _ = free(&mut ir, &mut bounds, name);
        }
        assert_eq!(
            names(&ir, &rel_parts(&ir, &bounds, true)),
            vec!["this/A@1", "this/A@10", "this/A@2"]
        );
    }

    /// `SymmetryBreaker.java:231-232` — skolem relations are excluded from SBP
    /// generation **unconditionally** in temporal mode, and only there: the
    /// static path still lets them eat the first slots of their arity.
    #[test]
    fn skolems_are_excluded_from_the_sbp_only_in_temporal_mode() {
        let mut ir = Ir::default();
        let mut bounds = Bounds::new(Universe::new(vec!["A$0".to_owned(), "A$1".to_owned()]));
        for name in ["$cmd_x", "this/A@0", "this/A@1"] {
            let _ = free(&mut ir, &mut bounds, name);
        }
        assert_eq!(
            names(&ir, &rel_parts(&ir, &bounds, false)),
            vec!["$cmd_x", "this/A@0", "this/A@1"],
            "static: skolems sort first and keep their slots"
        );
        assert_eq!(
            names(&ir, &rel_parts(&ir, &bounds, true)),
            vec!["this/A@0", "this/A@1"],
            "temporal: skolems are dropped outright"
        );
    }

    /// The atom partition is computed once for the whole trace: every per-state
    /// copy inherits its original's bound, so unrolling adds only duplicate
    /// tuplesets — refinement-neutral (atoms are rigid, alloy6-temporal.md §(d)).
    #[test]
    fn unrolling_does_not_refine_the_atom_partition() {
        let universe = Universe::new(vec!["A$0".to_owned(), "A$1".to_owned()]);
        let mut ir = Ir::default();

        let mut base = Bounds::new(universe.clone());
        let _ = free(&mut ir, &mut base, "this/A");
        let flat = build_plan(&ir, &base, universe.len(), false);

        let mut unrolled = Bounds::new(universe.clone());
        for state in 0..3 {
            let _ = free(&mut ir, &mut unrolled, &format!("this/A@{state}"));
        }
        let per_state = build_plan(&ir, &unrolled, universe.len(), true);

        assert_eq!(flat.classes(), per_state.classes());
        assert_eq!(per_state.relparts().len(), 3);
    }

    /// `$`-metamodel field placeholders are invisible to **both** halves of the
    /// plan (translation-ref §16.3.1, mt-134): the reference binds those fields
    /// to expressions and has no bounds relation for them
    /// (`BoundsComputer.java:426-431`), so they neither join `relparts` — where
    /// they would eat the soft cap ahead of real relations — nor refine the
    /// partition. Here `so/Ord$.subfields` sorts first at arity 1, and its
    /// universe-wide upper bound would otherwise take the leading SBP slot.
    #[test]
    fn meta_field_placeholders_are_invisible_to_the_plan() {
        let universe = Universe::new(vec!["A$0".to_owned(), "A$1".to_owned()]);
        let mut ir = Ir::default();
        let mut bounds = Bounds::new(universe.clone());
        let _ = free_meta_field(&mut ir, &mut bounds, "so/Ord$.subfields");
        let _ = free(&mut ir, &mut bounds, "this/A");

        let plan = build_plan(&ir, &bounds, universe.len(), false);
        assert_eq!(names(&ir, plan.relparts()), vec!["this/A"]);

        // And the partition is the one the reference-bounded relations alone
        // give: both atoms stay interchangeable.
        let mut without = Bounds::new(universe.clone());
        let mut only_real = Ir::default();
        let _ = free(&mut only_real, &mut without, "this/A");
        assert_eq!(
            plan.classes(),
            build_plan(&only_real, &without, universe.len(), false).classes()
        );
    }

    /// The residual partition refines on the **free** relations only
    /// (translation-ref §16.5, mt-136): the reference's re-translation keeps
    /// only the relations its "differ from the trivial instance" formula
    /// mentions, so an exact relation — a pinned `util/ordering` chain, in the
    /// cells that motivated this — no longer splits the atoms it names. Here
    /// `this/P` pins `A$0`, which the goal's own plan sees and the residual's
    /// does not.
    #[test]
    fn the_residual_partition_ignores_exact_relations() {
        let universe = Universe::new(vec!["A$0".to_owned(), "A$1".to_owned(), "A$2".to_owned()]);
        let mut ir = Ir::default();
        let mut bounds = Bounds::new(universe.clone());
        let _ = bound(&mut ir, &mut bounds, "this/P", &[0], &[0]);
        let _ = bound(&mut ir, &mut bounds, "this/A", &[], &[0, 1, 2]);

        let goal_plan = build_plan(&ir, &bounds, universe.len(), false);
        assert_eq!(class_indices(&goal_plan), vec![vec![0], vec![1, 2]]);

        let residual = build_trivial_plan(&ir, &bounds);
        assert_eq!(class_indices(&residual), vec![vec![0, 1, 2]]);
        assert_eq!(
            names(&ir, residual.relparts()),
            vec!["this/A"],
            "an exact relation contributes no SBP bits either way"
        );
    }

    /// Skolems **refine** the residual partition, unlike the goal's own
    /// (`detect_partition` skips them there). The reference's residual bounds
    /// are freshly built and carry no skolem marks to skip on: `$x` is an
    /// ordinary free relation in that translation.
    #[test]
    fn skolems_refine_the_residual_partition() {
        let universe = Universe::new(vec!["A$0".to_owned(), "A$1".to_owned()]);
        let mut ir = Ir::default();
        let mut bounds = Bounds::new(universe.clone());
        let _ = bound(&mut ir, &mut bounds, "$x", &[], &[0]);

        assert_eq!(
            class_indices(&build_plan(&ir, &bounds, universe.len(), false)),
            vec![vec![0, 1]],
            "the goal's own partition skips skolem bounds"
        );
        assert_eq!(
            class_indices(&build_trivial_plan(&ir, &bounds)),
            vec![vec![0], vec![1]]
        );
    }

    /// Atoms no free relation mentions fuse into one class — including the int
    /// run, which [`build_plan`] splits into unconditional singletons (§16.1.1)
    /// and the residual translation does not see at all (its bounds carry no
    /// ints). This is the other half of why the residual partition is coarser.
    #[test]
    fn unmentioned_atoms_fuse_in_the_residual_partition() {
        let universe = Universe::new(
            ["A$0", "A$1", "0", "1"]
                .iter()
                .map(|&s| s.to_owned())
                .collect(),
        );
        let mut ir = Ir::default();
        let mut bounds = Bounds::new(universe.clone());
        let _ = bound(&mut ir, &mut bounds, "this/A", &[], &[0, 1]);

        // `int_start = 2`: the two trailing atoms are the int run.
        assert_eq!(
            class_indices(&build_plan(&ir, &bounds, 2, false)),
            vec![vec![0, 1], vec![2], vec![3]]
        );
        assert_eq!(
            class_indices(&build_trivial_plan(&ir, &bounds)),
            vec![vec![0, 1], vec![2, 3]]
        );
    }

    /// The exclusion is **field**-scoped, not `$`-scoped: a metamodel *sig*
    /// relation (`this/A$`) is a real Kodkod relation on the reference side, so
    /// it keeps refining the partition and keeps its `relparts` slot.
    #[test]
    fn meta_sig_relations_are_still_reference_bounded() {
        let universe = Universe::new(vec!["A$0".to_owned(), "A$1".to_owned()]);
        let mut ir = Ir::default();
        let mut bounds = Bounds::new(universe.clone());
        let _ = free(&mut ir, &mut bounds, "this/A$");
        let plan = build_plan(&ir, &bounds, universe.len(), false);
        assert_eq!(names(&ir, plan.relparts()), vec!["this/A$"]);
    }
}
