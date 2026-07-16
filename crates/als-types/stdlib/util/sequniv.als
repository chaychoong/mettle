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
fun lastIdx [s: Int -> univ]: lone Int { inds[s] - inds[s].^(ui/prev) }
fun afterLastIdx [s: Int -> univ]: lone Int { (lastIdx[s]).(ui/next) }
fun last [s: Int -> univ]: lone (Int.s) { (lastIdx[s]).s }

// Declared results below are dependent bounds on the caller's own `s`
// (§7.7): each body computes a definite value that is provably a subset of
// its declared bound.
fun rest [s: Int -> univ]: s {
    { i: Int, x: univ | (i.(ui/next)).s = x }
}

fun butlast [s: Int -> univ]: s {
    s - (lastIdx[s] -> last[s])
}

fun indsOf [s: Int -> univ, e: univ]: set Int { s.e }
fun idxOf [s: Int -> univ, e: univ]: lone Int { indsOf[s, e] - indsOf[s, e].^(ui/prev) }
fun lastIdxOf [s: Int -> univ, e: univ]: lone Int { indsOf[s, e] - indsOf[s, e].^(ui/next) }

fun add [s: Int -> univ, e: univ]: s + (seq/Int -> e) { s + (afterLastIdx[s] -> e) }

fun setAt [s: Int -> univ, i: Int, e: univ]: s + (seq/Int -> e) {
    (s - (i -> univ)) + (i -> e)
}

fun insert [s: Int -> univ, i: Int, e: univ]: s + (seq/Int -> e) {
    { j: Int, x: univ | ui/lt[j, i] and j -> x in s }
    + (i -> e)
    + { j: Int, x: univ | ui/gte[j, i] and (ui/prev[j]).s = x }
}

fun delete [s: Int -> univ, i: Int]: s {
    { j: Int, x: univ | ui/lt[j, i] and j -> x in s }
    + { j: Int, x: univ | ui/gte[j, i] and (ui/next[j]).s = x }
}

fun append [s1, s2: Int -> univ]: s1 + s2 {
    s1 + { i: Int, x: univ |
        some j: inds[s2] | j -> x in s2 and i = ui/add[afterLastIdx[s1], j] }
}

fun subseq [s: Int -> univ, from: Int, to: Int]: s {
    { k: Int, x: univ |
        some m: Int | ui/lte[from, m] and ui/lte[m, to] and m -> x in s and k = ui/sub[m, from] }
}
