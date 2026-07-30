//! The CDCL solver's **flat clause arena** (mt-092 stage 1a).
//!
//! Every clause's literals live in **one contiguous `Vec<Lit>`**, addressed by
//! an `(offset, len)` pair in a small fixed-size header. The alternative — a
//! `Vec<Lit>` per clause — is what this replaces, and the reason is measured
//! rather than assumed: the mt-092 stage-0 profile
//! ([ADR-0020](../../../docs/adr/0020-cdcl-clause-db-reduction.md) stage-0
//! addendum) attributed **68.7–72.7% of solve wall to `propagate`**, and the
//! cost was memory-bound arena round-trips — 3.3k–44k watch visits per conflict
//! at 12–24 ns each, with ns-per-visit tracking arena *size*. A per-clause `Vec`
//! makes every visit pay two dependent random loads into a 32-byte header array
//! plus a separate heap allocation, with the literal storage fragmented across
//! hundreds of thousands of allocations. This layout halves the header array
//! (32 → 16 bytes per clause) and makes the literals of live clauses contiguous.
//!
//! # `ClauseRef` stability (the load-bearing invariant)
//! A [`ClauseRef`] is an index into [`ClauseArena::headers`], **not** into the
//! literal store. Headers are append-only and are never removed, so a
//! `ClauseRef` handed out once stays valid for the solver's whole lifetime —
//! which is what `reason`, the watch lists, and the `block`/`add_clause`
//! enumeration seam all rely on. Only the `offset` *inside* a header ever moves
//! (see [`ClauseArena::compact`]), and callers never see an offset.
//!
//! # Deletion and the memory story
//! [`ClauseArena::tombstone`] marks a clause deleted and sets its `len` to 0, so
//! its literals become unreachable but their storage is still held.
//! [`ClauseArena::compact`] is the reclaim step: it slides every live clause's
//! literals down over the holes and rewrites the offsets. The tradeoff, stated
//! explicitly because mt-049's contract depends on it:
//!
//! - **What is reclaimed:** the literal storage of deleted clauses, so a long
//!   run's literal store stays proportional to the *live* set (plus one
//!   reduction interval of fresh learned clauses) instead of to every clause
//!   ever learned. On the mt-092 ertms row that is ~29 MB instead of ~200 MB.
//!   mt-049's "its `lits` are freed" claim therefore stays literally true.
//! - **What is not:** the `Vec`'s *capacity* is kept (`truncate`, no
//!   `shrink_to_fit`), so the store holds its high-water mark rather than
//!   returning pages to the allocator on every reduction. That is deliberate:
//!   the peak is bounded and small, and giving it back would mean a realloc +
//!   full copy on every reduction to buy memory nobody is short of.
//! - **Header slots are never reclaimed at all** — that is the price of
//!   `ClauseRef` stability, and it is the same price the pre-mt-092 tombstone
//!   scheme paid.

use crate::Lit;

/// Index of a clause in the [`ClauseArena`] — specifically, an index into its
/// header array.
///
/// Stable for the solver's whole lifetime: headers are only ever appended, so a
/// `ClauseRef` never dangles and `reason`/watch entries stay valid without
/// relocation (STYLE A1 — index-based arena). [`ClauseArena::compact`] moves
/// literals, never headers.
pub(crate) type ClauseRef = usize;

/// A clause's fixed-size record: where its literals are, plus the reduction
/// bookkeeping mt-049 ranks by.
///
/// Kept to 16 bytes because `propagate` indexes this array randomly, once per
/// watch visit, billions of times per hard row — its size *is* the miss rate.
#[derive(Debug)]
struct ClauseHeader {
    /// Start of this clause's literals in [`ClauseArena::lits`].
    offset: u32,
    /// Number of literals. `0` exactly when the clause is a tombstone (a live
    /// clause always has ≥ 2 — units are enqueued, never installed).
    len: u32,
    /// Integer glue (distinct decision levels at learning time; lower = more
    /// useful) — the mt-049 reduction ranking key. `0` for permanent clauses.
    lbd: u32,
    /// A solver-learned resolvent (deletable) rather than an original problem
    /// clause or an enumeration blocking clause (both permanent).
    learnt: bool,
    /// A tombstone: unwatched, literals unreachable, slot retained so every
    /// `ClauseRef` stays valid.
    deleted: bool,
}

/// The clause store: one contiguous literal buffer plus one header per clause.
///
/// See the module docs for the `ClauseRef`-stability and memory contracts.
#[derive(Debug)]
pub(crate) struct ClauseArena {
    /// Every clause's literals, back to back in `ClauseRef` order. Holes left
    /// by tombstones are reclaimed by [`Self::compact`].
    lits: Vec<Lit>,
    /// One header per clause, indexed by [`ClauseRef`]; append-only.
    headers: Vec<ClauseHeader>,
}

impl ClauseArena {
    /// An empty arena.
    pub(crate) fn new() -> Self {
        Self {
            lits: Vec::new(),
            headers: Vec::new(),
        }
    }

    /// Number of clause slots, live and tombstoned — the exclusive upper bound
    /// on any valid [`ClauseRef`].
    pub(crate) fn len(&self) -> usize {
        self.headers.len()
    }

    /// Appends a clause, returning its (permanently stable) [`ClauseRef`].
    #[allow(
        clippy::cast_possible_truncation,
        reason = "the debug_assert above pins offset + len inside u32; the encode budget \
                  caps a real CNF orders of magnitude below it"
    )]
    pub(crate) fn push(&mut self, lits: &[Lit], learnt: bool, lbd: u32) -> ClauseRef {
        debug_assert!(lits.len() >= 2, "only size >= 2 clauses are installed");
        let offset = self.lits.len();
        debug_assert!(
            u32::try_from(offset + lits.len()).is_ok(),
            "clause literal store outgrew a u32 offset"
        );
        self.lits.extend_from_slice(lits);
        self.headers.push(ClauseHeader {
            offset: offset as u32,
            len: lits.len() as u32,
            lbd,
            learnt,
            deleted: false,
        });
        self.headers.len() - 1
    }

    /// The clause's literals.
    ///
    /// Empty for a tombstone, matching the pre-mt-092 behaviour of freeing the
    /// per-clause `Vec` (a tombstone's literals are never read: it is unwatched,
    /// and a locked clause is never deleted, so no `reason` points at one).
    pub(crate) fn lits(&self, cref: ClauseRef) -> &[Lit] {
        let h = &self.headers[cref];
        let start = h.offset as usize;
        &self.lits[start..start + h.len as usize]
    }

    /// The clause's literal count.
    pub(crate) fn len_of(&self, cref: ClauseRef) -> usize {
        self.headers[cref].len as usize
    }

    /// The clause's `k`th literal.
    ///
    /// The scalar accessor, not [`Self::lits`], is what `propagate` and
    /// `analyze` use: they interleave literal reads with `&mut self` calls on
    /// the solver, so holding a borrowed slice across them would not compile.
    pub(crate) fn lit(&self, cref: ClauseRef, k: usize) -> Lit {
        let h = &self.headers[cref];
        debug_assert!(k < h.len as usize, "clause literal index out of range");
        self.lits[h.offset as usize + k]
    }

    /// Overwrites the clause's `k`th literal.
    pub(crate) fn set_lit(&mut self, cref: ClauseRef, k: usize, lit: Lit) {
        let h = &self.headers[cref];
        debug_assert!(k < h.len as usize, "clause literal index out of range");
        let at = h.offset as usize + k;
        self.lits[at] = lit;
    }

    /// Brings `false_lit` to index 1 (its partner to index 0) and returns that
    /// partner — the "other watch" `propagate` then tests.
    ///
    /// One fused operation rather than a read / conditional swap / re-read
    /// because it sits on the hottest path in the solver and each of those steps
    /// would refetch the header: **65–67% of all watch visits** (mt-092 stage 0)
    /// go no further than the value of the literal this returns. Semantically it
    /// is exactly the read-swap-read it replaces, including performing the swap
    /// — the watched pair's *positions* are load-bearing downstream (a reason
    /// clause's `lits[0]` must be the literal it implied, which `analyze` skips
    /// and `reduce_db`'s locked check reads), so this must not become a
    /// swap-only-when-needed shortcut.
    pub(crate) fn watch_partner(&mut self, cref: ClauseRef, false_lit: Lit) -> Lit {
        let offset = self.headers[cref].offset as usize;
        debug_assert!(self.headers[cref].len >= 2, "watched pair needs 2 literals");
        if self.lits[offset] == false_lit {
            self.lits.swap(offset, offset + 1);
        }
        self.lits[offset]
    }

    /// The clause's integer LBD (mt-049 reduction key).
    pub(crate) fn lbd(&self, cref: ClauseRef) -> u32 {
        self.headers[cref].lbd
    }

    /// Whether the clause is a solver-learned resolvent (deletable).
    pub(crate) fn is_learnt(&self, cref: ClauseRef) -> bool {
        self.headers[cref].learnt
    }

    /// Whether the clause is a tombstone.
    pub(crate) fn is_deleted(&self, cref: ClauseRef) -> bool {
        self.headers[cref].deleted
    }

    /// Tombstones a clause: it keeps its slot (so every [`ClauseRef`] stays
    /// valid) but loses its literals.
    ///
    /// The storage is reclaimed by the following [`Self::compact`]; zeroing
    /// `len` first is what makes the clause's literals unreachable immediately,
    /// so a compaction is a pure reclaim step and never has to reason about
    /// half-deleted state.
    ///
    /// The `offset` is zeroed too, and that is load-bearing rather than tidy: a
    /// compaction leaves tombstoned headers alone, so a retained offset would
    /// point past the truncated store and [`Self::lits`] would panic slicing
    /// `[stale..stale]` (an empty range still has to start inside the slice).
    /// Offset 0 is a valid empty-slice start for every store, including an empty
    /// one.
    pub(crate) fn tombstone(&mut self, cref: ClauseRef) {
        let h = &mut self.headers[cref];
        debug_assert!(h.learnt, "only learned clauses may be tombstoned");
        h.deleted = true;
        h.len = 0;
        h.offset = 0;
    }

    /// Slides every live clause's literals down over the tombstoned holes and
    /// rewrites the offsets.
    ///
    /// **Trajectory-neutral by construction.** Each live clause's literal
    /// *sequence* is copied unchanged, in ascending [`ClauseRef`] order, so
    /// every subsequent read returns exactly the literal it would have returned
    /// without the compaction. Offsets are internal and never observed by the
    /// search. The result is a pure function of the live set (STYLE D1/D2) —
    /// no allocation addresses, no iteration-order dependence.
    #[allow(
        clippy::cast_possible_truncation,
        reason = "compaction only ever lowers an offset that already fitted u32"
    )]
    pub(crate) fn compact(&mut self) {
        let mut write = 0usize;
        for h in &mut self.headers {
            if h.deleted {
                continue;
            }
            let read = h.offset as usize;
            let len = h.len as usize;
            // Offsets ascend with `ClauseRef` (headers are pushed after their
            // literals, and compaction preserves the order), so the write
            // cursor never passes the read cursor and a forward copy is safe.
            debug_assert!(
                write <= read,
                "compaction write cursor overran the read cursor"
            );
            if write != read {
                self.lits.copy_within(read..read + len, write);
                h.offset = write as u32;
            }
            write += len;
        }
        // Capacity is deliberately retained — see the module docs' memory story.
        self.lits.truncate(write);
    }

    /// Live literal count — the compacted size of the store. Test/assertion
    /// support for the memory contract.
    #[cfg(test)]
    pub(crate) fn live_lits(&self) -> usize {
        self.lits.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Var;

    fn lit(i: u32) -> Lit {
        Lit::positive(Var::from_index(i as usize))
    }

    fn clause(range: std::ops::Range<u32>) -> Vec<Lit> {
        range.map(lit).collect()
    }

    #[test]
    fn push_then_read_round_trips() {
        let mut a = ClauseArena::new();
        let c0 = a.push(&clause(0..3), false, 0);
        let c1 = a.push(&clause(10..15), true, 7);
        assert_eq!(a.len(), 2);
        assert_eq!(a.lits(c0), clause(0..3).as_slice());
        assert_eq!(a.lits(c1), clause(10..15).as_slice());
        assert_eq!(a.len_of(c1), 5);
        assert_eq!(a.lit(c1, 2), lit(12));
        assert!(!a.is_learnt(c0));
        assert!(a.is_learnt(c1));
        assert_eq!(a.lbd(c1), 7);
    }

    #[test]
    fn set_lit_and_watch_partner_touch_only_that_clause() {
        let mut a = ClauseArena::new();
        let c0 = a.push(&clause(0..3), false, 0);
        let c1 = a.push(&clause(10..13), false, 0);
        // lits[0] IS the false literal, so the pair is swapped and its partner
        // returned; the neighbouring clause must be untouched.
        assert_eq!(a.watch_partner(c1, lit(10)), lit(11));
        a.set_lit(c1, 2, lit(99));
        assert_eq!(a.lits(c0), clause(0..3).as_slice(), "neighbour untouched");
        assert_eq!(a.lits(c1), &[lit(11), lit(10), lit(99)]);
    }

    #[test]
    fn watch_partner_leaves_an_already_normalized_pair_alone() {
        let mut a = ClauseArena::new();
        let c = a.push(&clause(10..13), false, 0);
        // lits[1] is the false literal already: no swap, same partner.
        assert_eq!(a.watch_partner(c, lit(11)), lit(10));
        assert_eq!(a.lits(c), clause(10..13).as_slice(), "no needless swap");
        // Idempotent under repetition, which is how propagate calls it.
        assert_eq!(a.watch_partner(c, lit(11)), lit(10));
        assert_eq!(a.lits(c), clause(10..13).as_slice());
    }

    #[test]
    fn tombstone_empties_the_clause_and_keeps_the_slot() {
        let mut a = ClauseArena::new();
        let c0 = a.push(&clause(0..3), true, 1);
        let c1 = a.push(&clause(10..13), true, 2);
        a.tombstone(c0);
        assert!(a.is_deleted(c0));
        assert_eq!(a.len_of(c0), 0);
        assert!(a.lits(c0).is_empty());
        // The slot count is unchanged — that is what keeps every ClauseRef valid.
        assert_eq!(a.len(), 2);
        assert_eq!(a.lits(c1), clause(10..13).as_slice(), "survivor intact");
    }

    #[test]
    fn compact_reclaims_holes_and_preserves_every_live_clause() {
        let mut a = ClauseArena::new();
        let refs: Vec<ClauseRef> = (0..6)
            .map(|i| a.push(&clause(i * 10..i * 10 + 4), true, i))
            .collect();
        assert_eq!(a.live_lits(), 24);
        // Delete a leading, a middle and a trailing clause: every hole shape.
        a.tombstone(refs[0]);
        a.tombstone(refs[3]);
        a.tombstone(refs[5]);
        let survivors: Vec<Vec<Lit>> = [1usize, 2, 4]
            .iter()
            .map(|&i| a.lits(refs[i]).to_vec())
            .collect();
        a.compact();
        assert_eq!(a.live_lits(), 12, "holes reclaimed");
        for (slot, expected) in [1usize, 2, 4].iter().zip(&survivors) {
            assert_eq!(
                a.lits(refs[*slot]),
                expected.as_slice(),
                "a live clause's literals survive compaction byte-for-byte"
            );
        }
        for slot in [0usize, 3, 5] {
            assert!(a.is_deleted(refs[slot]));
            assert!(a.lits(refs[slot]).is_empty());
        }
        assert_eq!(a.len(), 6, "ClauseRefs are still in range after compaction");
    }

    #[test]
    fn compact_is_idempotent_and_survives_an_all_or_nothing_arena() {
        let mut a = ClauseArena::new();
        let c0 = a.push(&clause(0..3), true, 0);
        a.compact();
        assert_eq!(a.lits(c0), clause(0..3).as_slice());
        a.compact();
        assert_eq!(a.lits(c0), clause(0..3).as_slice(), "idempotent");
        a.tombstone(c0);
        a.compact();
        assert_eq!(a.live_lits(), 0, "an all-dead arena compacts to nothing");
        assert_eq!(a.len(), 1);
        // And it still grows correctly afterwards, from offset 0.
        let c1 = a.push(&clause(7..10), false, 0);
        assert_eq!(a.lits(c1), clause(7..10).as_slice());
    }

    #[test]
    fn push_after_compact_appends_past_the_live_set() {
        let mut a = ClauseArena::new();
        let c0 = a.push(&clause(0..3), true, 0);
        let c1 = a.push(&clause(10..13), true, 0);
        a.tombstone(c0);
        a.compact();
        let c2 = a.push(&clause(20..23), true, 0);
        assert_eq!(a.lits(c1), clause(10..13).as_slice());
        assert_eq!(a.lits(c2), clause(20..23).as_slice());
        assert_eq!(a.live_lits(), 6);
    }
}
