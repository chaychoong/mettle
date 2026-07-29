// util/sequniv — sequences represented directly as `Int -> univ` relations;
// this is the module backing Alloy's native `seq` keyword sugar.
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.7) and standard
// sequence semantics (0-based, contiguous-from-0 index sets), never from
// upstream Alloy's util/*.als text.

module util/sequniv

open util/integer as ui

pred isSeq [s: Int -> univ] {
    all i: Int | lone i.s
    all i: Int | some i.s implies ui/nonneg[i]
    all i: Int | (some i.s and ui/pos[i]) implies some (ui/prev[i]).s
}

pred isEmpty [s: Int -> univ] { no s }

pred hasDups [s: Int -> univ] {
    some disj i, j: inds[s] | i.s = j.s
}

fun inds [s: Int -> univ]: set Int { s.univ }
fun elems [s: Int -> univ]: set (Int.s) { Int.s }

fun first [s: Int -> univ]: lone (Int.s) { 0.s }
// The last used index is the one in `inds` that no larger used index precedes:
// removing every index reachable by repeatedly stepping *down* (`^prev`) from a
// used index leaves the maximum (jar-verified: `lastIdx` of a 3-seq is 2).
fun lastIdx [s: Int -> univ]: lone Int { inds[s] - inds[s].^(ui/prev) }
// The smallest UNUSED index — not `lastIdx.next` (jar-verified, probes
// mt046-afterLast/-noncontig/-full): `0` for the empty sequence, one past the
// last for a contiguous prefix, the first gap for a non-contiguous relation
// (`afterLastIdx[{1->e}] = 0`), and `none` when every `seq/Int` index is used.
// Same min-extraction idiom as `idxOf`, over the unused set.
fun afterLastIdx [s: Int -> univ]: lone Int {
    (seq/Int - inds[s]) - (seq/Int - inds[s]).^(ui/next)
}
fun last [s: Int -> univ]: lone (Int.s) { (lastIdx[s]).s }

// Declared results below are dependent bounds on the caller's own `s`
// (§7.7): each body computes a definite value that is provably a subset of
// its declared bound.
//
// SHIFTING FUNS AND `seq/Int` (mt-084, jar-verified). Where a fun's body is an
// index *comprehension*, the index binder is `seq/Int`, not `Int`: the jar
// drops any result tuple whose index falls outside the seq index domain. The
// clamp is per-fun, NOT a uniform post-intersection — the decisive pair is
// `rest[{0->A,1->B,2->C,3->A,4->B}] = {0->B,1->C,2->A}` (index 3 dropped)
// against `delete[<same>,0] = {0->B,1->C,2->A,3->B}` (index 3 kept), with
// `setAt[{0..2},5,A]` keeping `5->A` as a second witness. So `rest`, `insert`,
// `append` and `subseq` clamp; `delete` and `setAt` do not; `add`/`butlast`
// take their index from `afterLastIdx`/`lastIdx` and are already bounded.
fun rest [s: Int -> univ]: s {
    { i: seq/Int, x: univ | (i.(ui/next)).s = x }
}

fun butlast [s: Int -> univ]: s {
    s - (lastIdx[s] -> last[s])
}

fun indsOf [s: Int -> univ, e: univ]: set Int { s.e }
// `idxOf` = the *first* (smallest) index of `e`: remove every index reachable by
// stepping *up* (`^next`) from an occurrence, leaving the minimum. `lastIdxOf` =
// the *last* (largest): remove the `^prev`-reachable ones, leaving the maximum.
// (jar-verified: for `e` at indices {0,2}, `idxOf = 0`, `lastIdxOf = 2`.)
fun idxOf [s: Int -> univ, e: univ]: lone Int { indsOf[s, e] - indsOf[s, e].^(ui/next) }
fun lastIdxOf [s: Int -> univ, e: univ]: lone Int { indsOf[s, e] - indsOf[s, e].^(ui/prev) }

fun add [s: Int -> univ, e: univ]: s + (seq/Int -> e) { s + (afterLastIdx[s] -> e) }

fun setAt [s: Int -> univ, i: Int, e: univ]: s + (seq/Int -> e) {
    (s - (i -> univ)) + (i -> e)
}

// Everything at or past `i` shifts up by one, so the shifted term is keyed on
// `gt` (strictly), not `gte` — at `gte` index `i` would carry both `e` and the
// old `s[i-1]`, making the result non-functional (jar: `insert[0->A+1->B,1,C]`
// = `{0->A, 1->C, 2->B}`). `i` itself is clamped like every other result index,
// so an out-of-range `i` contributes nothing (jar: `insert[0->A+1->B,3,C]` =
// `{0->A, 1->B}`), while a negative `i` still shifts (`insert[..,-1,C]` =
// `{1->A, 2->B}`) — the clamp is on the index domain, not a guard on `i`.
fun insert [s: Int -> univ, i: Int, e: univ]: s + (seq/Int -> e) {
    { j: seq/Int, x: univ | ui/lt[j, i] and j -> x in s }
    + ((i & seq/Int) -> e)
    + { j: seq/Int, x: univ | ui/gt[j, i] and (ui/prev[j]).s = x }
}

// No `seq/Int` clamp here — jar-verified negative space: `delete` keeps
// out-of-domain result indices (`delete[0->A+1->B+2->C,-1]` = `{-1->A, 0->B,
// 1->C}`), unlike its mirror image `rest`.
fun delete [s: Int -> univ, i: Int]: s {
    { j: Int, x: univ | ui/lt[j, i] and j -> x in s }
    + { j: Int, x: univ | ui/gte[j, i] and (ui/next[j]).s = x }
}

fun append [s1, s2: Int -> univ]: s1 + s2 {
    s1 + { i: seq/Int, x: univ |
        some j: inds[s2] | j -> x in s2 and i = ui/add[afterLastIdx[s1], j] }
}

fun subseq [s: Int -> univ, from: Int, to: Int]: s {
    { k: seq/Int, x: univ |
        some m: Int | ui/lte[from, m] and ui/lte[m, to] and m -> x in s and k = ui/sub[m, from] }
}
