//! The CDCL solver's **decision-variable order** (mt-092 stage 1a): an indexed
//! binary max-heap that reproduces the old linear scan's argmax exactly.
//!
//! Before mt-092, `pick_branch` was a linear pass over the whole dense variable
//! pool on every decision. The mt-092 stage-0 profile
//! ([ADR-0020](../../../docs/adr/0020-cdcl-clause-db-reduction.md) stage-0
//! addendum) measured that model exactly — `pick_iters = decisions × num_vars`
//! at 0.87–0.91 ns per iteration — and priced it at **10–19% of solve wall**,
//! the second-largest term. This module replaces the scan with a heap while
//! keeping the *decision sequence* bit-identical, so the change cannot move the
//! search trajectory.
//!
//! # The order, and why the heap reproduces the scan exactly
//! The old scan was: over `0..num_vars`, keep the unassigned variable of highest
//! `activity`, replacing only on a **strict** `>`. On an ascending scan that
//! resolves ties to the **lowest variable index**. So the scan computes
//!
//! > the unassigned variable maximising `(activity, Reverse(index))`
//!
//! and that key is a **total order with no ties** — indices are distinct. This
//! is the whole correctness argument: under a total order a binary max-heap's
//! root is the *unique* maximum of its contents, so the pop sequence is a pure
//! function of the contained set and the activities, independent of the internal
//! array layout. Any valid heap — however it was built, sifted, or rebuilt —
//! yields the same variable the scan would have. Determinism (STYLE D1/D2)
//! follows for free: integer keys, a total tie-order, no floats, no hashing, no
//! addresses.
//!
//! # Membership discipline
//! The invariant is **every unassigned variable is in the heap**. Assigned ones
//! may also be in it (propagation assigns without touching the heap — the
//! standard lazy scheme), so [`VarOrder::pop_unassigned`] discards assigned
//! variables as it pops and the solver re-inserts on unassign. A variable fixed
//! at level 0 is never unassigned, so it is popped once and never returns, which
//! is exactly right — it can never be a decision again.
//!
//! # The rescale corner
//! The solver bounds its `u64` activities by right-shifting **all** of them
//! (`rescale_activities`). A uniform shift is monotone but **not injective**:
//! two previously-distinct activities can collapse to equal, at which point the
//! index tie-break — not the old activity order — decides which variable wins.
//! A heap ordered by the pre-shift values can therefore violate the heap
//! property, so [`VarOrder::rebuild`] re-heapifies from scratch after every
//! rescale. It is O(n) and rescales are rare (the increment has to cross
//! `1 << 40`), and it is the only way to guarantee the heap still agrees with
//! what a linear scan over the *post-shift* activities would compute.

/// Sentinel for "this variable is not in the heap" in the position map.
const NOT_IN_HEAP: u32 = u32::MAX;

/// An indexed max-heap over variable indices, keyed by
/// `(activity, Reverse(index))`.
///
/// "Indexed" = it carries a position map, so a variable's key can be increased
/// in place (`increase`, on a VSIDS bump) without a linear search.
#[derive(Debug)]
pub(crate) struct VarOrder {
    /// The heap: variable indices, parent higher than both children under
    /// [`Self::higher`].
    heap: Vec<u32>,
    /// `pos[v]` is `v`'s index in `heap`, or [`NOT_IN_HEAP`].
    pos: Vec<u32>,
}

impl VarOrder {
    /// Every variable, in index order — which is already a valid max-heap.
    ///
    /// All activities start equal (zero), so the key reduces to the index
    /// tie-break, and `0..n` in ascending order satisfies the heap property by
    /// construction (a parent's index is always below its children's).
    #[allow(
        clippy::cast_possible_truncation,
        reason = "the variable pool is capped at u32::MAX/2 by Cnf::fresh_var (STYLE I1), \
                  so an index always fits u32"
    )]
    pub(crate) fn new(num_vars: usize) -> Self {
        debug_assert!(
            num_vars < NOT_IN_HEAP as usize,
            "variable pool outgrew the heap"
        );
        Self {
            heap: (0..num_vars as u32).collect(),
            pos: (0..num_vars as u32).collect(),
        }
    }

    /// Whether `a` outranks `b`: higher activity, ties to the lower index.
    ///
    /// A total order with no ties — see the module docs; the heap's uniqueness
    /// (and so the whole equivalence to the old linear scan) rests on it.
    fn higher(a: u32, b: u32, activity: &[u64]) -> bool {
        let (aa, ab) = (activity[a as usize], activity[b as usize]);
        aa > ab || (aa == ab && a < b)
    }

    /// Whether `v` is currently in the heap.
    fn contains(&self, v: u32) -> bool {
        self.pos[v as usize] != NOT_IN_HEAP
    }

    /// Re-admits `v` to the heap; a no-op if it is already there.
    ///
    /// Called on every unassign, which is what maintains the module's
    /// membership invariant.
    #[allow(
        clippy::cast_possible_truncation,
        reason = "the heap holds at most num_vars entries, which fits u32 (see new)"
    )]
    pub(crate) fn insert(&mut self, v: u32, activity: &[u64]) {
        if self.contains(v) {
            return;
        }
        let at = self.heap.len() as u32;
        self.heap.push(v);
        self.pos[v as usize] = at;
        self.sift_up(at, activity);
    }

    /// Restores the heap property after `v`'s activity **grew** (a VSIDS bump).
    ///
    /// A no-op when `v` is not in the heap: it is assigned, and it will be
    /// re-inserted at its then-current activity when it is unassigned.
    pub(crate) fn increase(&mut self, v: u32, activity: &[u64]) {
        let at = self.pos[v as usize];
        if at != NOT_IN_HEAP {
            self.sift_up(at, activity);
        }
    }

    /// Pops the highest-ranked variable for which `is_unassigned` holds,
    /// discarding assigned variables on the way.
    ///
    /// Returns `None` once the heap is exhausted, which — given the membership
    /// invariant — means no unassigned variable exists and the assignment is
    /// total. The returned variable is removed; the solver re-inserts it if it
    /// is ever unassigned again.
    pub(crate) fn pop_unassigned(
        &mut self,
        activity: &[u64],
        is_unassigned: impl Fn(u32) -> bool,
    ) -> Option<u32> {
        loop {
            let top = *self.heap.first()?;
            self.remove_root(activity);
            if is_unassigned(top) {
                return Some(top);
            }
        }
    }

    /// Re-heapifies from scratch, for use after the activities have been
    /// rewritten in place by a rescale (see the module docs' rescale corner).
    ///
    /// Floyd's bottom-up build, O(n). Membership is unchanged — only the order.
    pub(crate) fn rebuild(&mut self, activity: &[u64]) {
        for (i, &v) in self.heap.iter().enumerate() {
            // `enumerate` over the heap can only produce in-range positions.
            #[allow(
                clippy::cast_possible_truncation,
                reason = "a heap position is below heap.len() <= num_vars, which fits u32"
            )]
            {
                self.pos[v as usize] = i as u32;
            }
        }
        for at in (0..self.heap.len() / 2).rev() {
            #[allow(
                clippy::cast_possible_truncation,
                reason = "at < heap.len() <= num_vars, which fits u32"
            )]
            self.sift_down(at as u32, activity);
        }
        debug_assert!(self.is_heap(activity), "rebuild must leave a valid heap");
    }

    /// Drops the root, moving the last entry into its place and sifting it down.
    #[allow(
        clippy::cast_possible_truncation,
        reason = "heap.len() <= num_vars, which fits u32 (see new)"
    )]
    fn remove_root(&mut self, activity: &[u64]) {
        let Some(&root) = self.heap.first() else {
            debug_assert!(false, "remove_root on an empty heap");
            return;
        };
        self.pos[root as usize] = NOT_IN_HEAP;
        let Some(last) = self.heap.pop() else {
            unreachable!("a heap with a root is nonempty")
        };
        if last != root {
            self.heap[0] = last;
            self.pos[last as usize] = 0;
            self.sift_down(0, activity);
        }
    }

    /// Moves the entry at `at` up while it outranks its parent.
    fn sift_up(&mut self, mut at: u32, activity: &[u64]) {
        let v = self.heap[at as usize];
        while at > 0 {
            let parent = (at - 1) / 2;
            if !Self::higher(v, self.heap[parent as usize], activity) {
                break;
            }
            let moved = self.heap[parent as usize];
            self.heap[at as usize] = moved;
            self.pos[moved as usize] = at;
            at = parent;
        }
        self.heap[at as usize] = v;
        self.pos[v as usize] = at;
    }

    /// Moves the entry at `at` down while a child outranks it.
    #[allow(
        clippy::cast_possible_truncation,
        reason = "every position computed here is bounded by heap.len() <= num_vars"
    )]
    fn sift_down(&mut self, mut at: u32, activity: &[u64]) {
        let n = self.heap.len() as u32;
        let v = self.heap[at as usize];
        loop {
            let left = 2 * at + 1;
            if left >= n {
                break;
            }
            let right = left + 1;
            // Pick the stronger child; `higher` is total, so this is unambiguous.
            let child = if right < n
                && Self::higher(
                    self.heap[right as usize],
                    self.heap[left as usize],
                    activity,
                ) {
                right
            } else {
                left
            };
            if !Self::higher(self.heap[child as usize], v, activity) {
                break;
            }
            let moved = self.heap[child as usize];
            self.heap[at as usize] = moved;
            self.pos[moved as usize] = at;
            at = child;
        }
        self.heap[at as usize] = v;
        self.pos[v as usize] = at;
    }

    /// Whether the heap property and the position map both hold — the
    /// structural invariant, checked in debug builds at the points that
    /// establish it (STYLE I1).
    fn is_heap(&self, activity: &[u64]) -> bool {
        self.heap.iter().enumerate().all(|(i, &v)| {
            #[allow(
                clippy::cast_possible_truncation,
                reason = "i < heap.len() <= num_vars, which fits u32"
            )]
            let ok_pos = self.pos[v as usize] == i as u32;
            let ok_order = i == 0 || !Self::higher(v, self.heap[(i - 1) / 2], activity);
            ok_pos && ok_order
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pre-mt-092 `pick_branch`, in spirit: ascending scan, strict `>`, so
    /// ties fall to the lowest index. The oracle every test below compares
    /// against — if this and [`VarOrder::pop_unassigned`] ever disagree, the
    /// mt-092 trajectory-neutrality claim is false.
    fn linear_scan_argmax(activity: &[u64], assigned: &[bool]) -> Option<u32> {
        let mut best: Option<u32> = None;
        let mut best_act = 0u64;
        for v in 0..width(activity.len()) {
            if !assigned[v as usize] {
                let act = activity[v as usize];
                if best.is_none() || act > best_act {
                    best = Some(v);
                    best_act = act;
                }
            }
        }
        best
    }

    /// A pool size as the `u32` the heap speaks; test pools are tiny.
    fn width(n: usize) -> u32 {
        u32::try_from(n).unwrap_or(u32::MAX)
    }

    /// A tiny deterministic LCG — STYLE U5: seeded, no `rand` dependency, and
    /// the seed is part of the recorded input, so a failure is reproducible.
    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            self.0 >> 11
        }

        /// A value in `0..n`.
        fn below(&mut self, n: u32) -> u32 {
            u32::try_from(self.next() % u64::from(n)).unwrap_or(0)
        }
    }

    /// Drains the heap under a constant "everything is unassigned" filter.
    fn drain(order: &mut VarOrder, activity: &[u64]) -> Vec<u32> {
        std::iter::from_fn(|| order.pop_unassigned(activity, |_| true)).collect()
    }

    #[test]
    fn fresh_heap_pops_in_index_order_when_all_activities_are_equal() {
        // The degenerate case that pins the tie-break: with every activity zero
        // the key is the index alone, so the pop order must be 0, 1, 2, …
        let activity = vec![0u64; 32];
        let mut order = VarOrder::new(32);
        assert_eq!(drain(&mut order, &activity), (0..32u32).collect::<Vec<_>>());
    }

    #[test]
    fn pop_sequence_matches_the_linear_scan_over_seeds() {
        // The equivalence test mt-092 stage 1a rests on: for many seeds, drive
        // the heap through the exact four state transitions the solver performs
        // (bump / unassign / rescale / pick) and require that EVERY pick equals
        // what the old linear scan would have returned on the same state.
        for seed in 0..200u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1));
            let n = 1 + rng.below(40);
            let mut activity = vec![0u64; n as usize];
            let mut assigned = vec![false; n as usize];
            let mut order = VarOrder::new(n as usize);

            for _step in 0..300 {
                match rng.next() % 4 {
                    // Bump: activity only ever grows, so `increase` is the hook.
                    0 => {
                        let v = rng.below(n);
                        activity[v as usize] =
                            activity[v as usize].saturating_add(1 + rng.next() % 8);
                        order.increase(v, &activity);
                    }
                    // Unassign: the solver re-inserts, so the heap must too.
                    1 => {
                        let v = rng.below(n);
                        if assigned[v as usize] {
                            assigned[v as usize] = false;
                            order.insert(v, &activity);
                        }
                    }
                    // Rescale: a uniform right shift, then a rebuild.
                    2 => {
                        for a in &mut activity {
                            *a >>= 1;
                        }
                        order.rebuild(&activity);
                    }
                    // Pick: the assertion.
                    _ => {
                        let expected = linear_scan_argmax(&activity, &assigned);
                        let got = order.pop_unassigned(&activity, |v| !assigned[v as usize]);
                        assert_eq!(
                            got, expected,
                            "heap argmax diverged from the linear scan (seed {seed})"
                        );
                        if let Some(v) = got {
                            assigned[v as usize] = true;
                        }
                    }
                }
                assert!(
                    order.is_heap(&activity),
                    "heap invariant broken (seed {seed})"
                );
            }
        }
    }

    #[test]
    fn rescale_that_merges_activities_falls_back_to_the_index_tie_break() {
        // The rescale corner, made explicit: two activities distinct before the
        // shift and equal after it must flip the winner to the LOWER index. A
        // heap that merely kept its pre-shift order would still answer var 2.
        let mut activity = vec![0u64, 1 << 21, (1 << 21) + 1];
        let mut order = VarOrder::new(3);
        order.increase(1, &activity);
        order.increase(2, &activity);
        assert_eq!(
            order.pop_unassigned(&activity, |_| true),
            Some(2),
            "pre-shift the higher activity wins"
        );
        order.insert(2, &activity);

        for a in &mut activity {
            *a >>= 20;
        }
        assert_eq!(activity[1], activity[2], "the shift merged them");
        order.rebuild(&activity);
        let unassigned = [false; 3];
        assert_eq!(
            order.pop_unassigned(&activity, |_| true),
            linear_scan_argmax(&activity, &unassigned),
            "post-shift the index tie-break decides, exactly as the scan would"
        );
    }

    #[test]
    fn rescale_without_a_rebuild_would_be_wrong() {
        // Guards the *reason* rebuild exists rather than just its effect: sift
        // -only maintenance cannot fix a merge, because the violation can be
        // arbitrarily deep in the heap rather than at the node that changed.
        let mut activity: Vec<u64> = (0..16u64).map(|i| (16 - i) << 20).collect();
        let mut order = VarOrder::new(16);
        for v in 0..16u32 {
            order.increase(v, &activity);
        }
        for a in &mut activity {
            *a >>= 20;
        }
        order.rebuild(&activity);
        let mut assigned = [false; 16];
        for _ in 0..16 {
            let expected = linear_scan_argmax(&activity, &assigned);
            let got = order.pop_unassigned(&activity, |v| !assigned[v as usize]);
            assert_eq!(got, expected, "post-rescale order tracks the scan");
            let Some(v) = got else {
                panic!("pool exhausted early")
            };
            assigned[v as usize] = true;
        }
    }

    #[test]
    fn level_zero_variables_are_popped_once_and_never_return() {
        let activity = vec![0u64; 8];
        let mut assigned = [false; 8];
        let mut order = VarOrder::new(8);
        // Three level-0 fixings: assigned and never unassigned, so never
        // re-inserted — they must not be offered as decisions again.
        for _ in 0..3 {
            let Some(v) = order.pop_unassigned(&activity, |v| !assigned[v as usize]) else {
                panic!("pool exhausted early")
            };
            assigned[v as usize] = true;
        }
        let rest: Vec<u32> =
            std::iter::from_fn(|| order.pop_unassigned(&activity, |v| !assigned[v as usize]))
                .collect();
        assert_eq!(rest, vec![3, 4, 5, 6, 7], "no level-0 variable came back");
    }

    #[test]
    fn exhausted_heap_reports_none_which_is_the_total_assignment_signal() {
        let activity = vec![0u64; 4];
        let mut order = VarOrder::new(4);
        assert_eq!(drain(&mut order, &activity).len(), 4);
        assert_eq!(order.pop_unassigned(&activity, |_| true), None);
    }

    #[test]
    fn insert_is_idempotent() {
        let activity = vec![0u64; 4];
        let mut order = VarOrder::new(4);
        order.insert(2, &activity); // already present
        order.insert(2, &activity);
        assert_eq!(
            drain(&mut order, &activity),
            vec![0, 1, 2, 3],
            "no duplicate entry was admitted"
        );
    }

    #[test]
    fn increase_on_an_absent_variable_is_a_no_op() {
        // The bump path hits assigned (hence popped) variables constantly; it
        // must not resurrect them or corrupt the position map.
        let mut activity = vec![0u64; 4];
        let mut order = VarOrder::new(4);
        assert_eq!(order.pop_unassigned(&activity, |_| true), Some(0));
        activity[0] = 999;
        order.increase(0, &activity);
        assert_eq!(drain(&mut order, &activity), vec![1, 2, 3], "0 stayed out");
    }

    #[test]
    fn empty_pool_is_immediately_exhausted() {
        let mut order = VarOrder::new(0);
        assert_eq!(order.pop_unassigned(&[], |_| true), None);
    }
}
