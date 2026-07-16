// util/seqrel — finite sequences represented as bare `SeqIdx -> elem`
// relations (no wrapping sig, contrast util/sequence): every mutator here
// is a *func* returning the new relation, not a relating pred.
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.6) and standard
// sequence semantics, never from upstream Alloy's util/*.als text.

module util/seqrel[elem]

open util/integer
open util/ordering[SeqIdx] as ord

sig SeqIdx {}

// Global bounds of the whole `SeqIdx` order.
fun firstIdx: SeqIdx { ord/first }
fun finalIdx: SeqIdx { ord/last }

pred isSeq [s: SeqIdx -> elem] {
    all i: SeqIdx | lone i.s
    no s or inds[s] = firstIdx.*(ord/next) & lastIdx[s].*(~(ord/next))
}

fun inds [s: SeqIdx -> elem]: set SeqIdx { s.elem }
fun elems [s: SeqIdx -> elem]: set elem { SeqIdx.s }
fun at [s: SeqIdx -> elem, i: SeqIdx]: lone elem { i.s }

fun lastIdx [s: SeqIdx -> elem]: lone SeqIdx { inds[s] - inds[s].^(ord/prev) }
fun afterLastIdx [s: SeqIdx -> elem]: lone SeqIdx { (lastIdx[s]).(ord/next) }

fun first [s: SeqIdx -> elem]: lone elem { at[s, firstIdx] }
fun last [s: SeqIdx -> elem]: lone elem { at[s, lastIdx[s]] }

fun indsOf [s: SeqIdx -> elem, e: elem]: set SeqIdx { s.e }
fun idxOf [s: SeqIdx -> elem, e: elem]: lone SeqIdx { indsOf[s, e] - indsOf[s, e].^(ord/prev) }
fun lastIdxOf [s: SeqIdx -> elem, e: elem]: lone SeqIdx { indsOf[s, e] - indsOf[s, e].^(ord/next) }

pred isEmpty [s: SeqIdx -> elem] { no s }
pred hasDups [s: SeqIdx -> elem] { some e: elems[s] | not lone indsOf[s, e] }

fun rest [s: SeqIdx -> elem]: SeqIdx -> elem {
    { i: SeqIdx, x: elem | i.(ord/next) -> x in s }
}

fun butlast [s: SeqIdx -> elem]: SeqIdx -> elem {
    s - (lastIdx[s] -> last[s])
}

fun add [s: SeqIdx -> elem, e: elem]: SeqIdx -> elem { s + (afterLastIdx[s] -> e) }

fun setAt [s: SeqIdx -> elem, i: SeqIdx, e: elem]: SeqIdx -> elem {
    (s - (i -> elem)) + (i -> e)
}

fun insert [s: SeqIdx -> elem, i: SeqIdx, e: elem]: SeqIdx -> elem {
    { j: SeqIdx, x: elem | ord/lt[j, i] and j -> x in s }
    + (i -> e)
    + { j: SeqIdx, x: elem | ord/gte[j, i] and j.(ord/prev) -> x in s }
}

fun delete [s: SeqIdx -> elem, i: SeqIdx]: SeqIdx -> elem {
    { j: SeqIdx, x: elem | ord/lt[j, i] and j -> x in s }
    + { j: SeqIdx, x: elem | ord/gte[j, i] and j.(ord/next) -> x in s }
}

fun append [s1: SeqIdx -> elem, s2: SeqIdx -> elem]: SeqIdx -> elem {
    s1 + { i: SeqIdx, x: elem |
        some j: inds[s2] | j -> x in s2
            and integer/eq[integer/elem2int[i, ord/next],
                            integer/add[integer/elem2int[afterLastIdx[s1], ord/next],
                                        integer/elem2int[j, ord/next]]] }
}

fun subseq [s: SeqIdx -> elem, from: SeqIdx, to: SeqIdx]: SeqIdx -> elem {
    { k: SeqIdx, x: elem |
        some m: SeqIdx | ord/lte[from, m] and ord/lte[m, to] and m -> x in s
            and integer/eq[integer/elem2int[k, ord/next],
                            integer/sub[integer/elem2int[m, ord/next],
                                        integer/elem2int[from, ord/next]]] }
}
