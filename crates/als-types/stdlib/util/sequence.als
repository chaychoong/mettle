// util/sequence — finite sequences of `elem`, reified as `Seq` atoms and
// indexed by an opaque ordered `SeqIdx` sig (contrast util/seqrel's bare
// `SeqIdx -> elem` relations and util/sequniv's native-`Int` indexing).
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.5) and standard
// sequence semantics, never from upstream Alloy's util/*.als text.

module util/sequence[elem]

open util/ordering[SeqIdx] as ord

sig SeqIdx {}

// Every `Seq` atom's occupied indices are, by construction, a contiguous
// prefix of the `SeqIdx` order starting at the global first index.
sig Seq {
    seqElems: SeqIdx -> lone elem
} {
    no seqElems
    or
    inds[this] = firstIdx.*(ord/next) & lastIdx[this].*(~(ord/next))
}

// No two `Seq` atoms carry the same contents (canonical representation).
fact canonicalizeSeqs {
    all disj s1, s2: Seq | s1.seqElems != s2.seqElems
}

fun inds [s: Seq]: set SeqIdx { s.seqElems.elem }
fun elems [s: Seq]: set elem { SeqIdx.(s.seqElems) }
fun at [s: Seq, i: SeqIdx]: lone elem { i.(s.seqElems) }

// Global bounds of the whole `SeqIdx` order (not specific to any one `Seq`).
fun firstIdx: SeqIdx { ord/first }
fun finalIdx: SeqIdx { ord/last }

fun lastIdx [s: Seq]: lone SeqIdx { inds[s] - inds[s].^(ord/prev) }
fun afterLastIdx [s: Seq]: lone SeqIdx { lastIdx[s].(ord/next) }

fun first [s: Seq]: lone elem { at[s, firstIdx] }
fun last [s: Seq]: lone elem { at[s, lastIdx[s]] }

fun indsOf [s: Seq, e: elem]: set SeqIdx { (s.seqElems).e }
fun idxOf [s: Seq, e: elem]: lone SeqIdx { indsOf[s, e] - indsOf[s, e].^(ord/prev) }
fun lastIdxOf [s: Seq, e: elem]: lone SeqIdx { indsOf[s, e] - indsOf[s, e].^(ord/next) }

pred isEmpty [s: Seq] { no s.seqElems }
pred hasDups [s: Seq] { not s.noDuplicates }

pred Seq.noDuplicates () { all e: elems[this] | lone seqElems.e }

pred Seq.allExist () {
    no seqElems or inds[this] = firstIdx.*(ord/next) & lastIdx[this].*(~(ord/next))
}

pred Seq.allExistNoDuplicates () { this.allExist and this.noDuplicates }

pred startsWith [s: Seq, prefix: Seq] {
    isEmpty[prefix]
    or
    (prefix.allExist and (inds[prefix] <: prefix.seqElems) = (inds[prefix] <: s.seqElems))
}

// `r` is `s` with its first element dropped and every remaining index
// shifted one step earlier.
pred rest [s: Seq, r: Seq] {
    isEmpty[s] => isEmpty[r]
    else (s.allExist and r.seqElems = { i: SeqIdx, e: elem | i.(ord/next) -> e in s.seqElems })
}

pred copy [source: Seq, dest: Seq, destStart: SeqIdx] {
    dest.seqElems = { j: SeqIdx, x: elem |
        some k: inds[source] | k -> x in source.seqElems
            and #(ord/prevs[j]) = (#(ord/prevs[destStart]) fun/add #(ord/prevs[k])) }
}

pred add [s: Seq, e: elem, added: Seq] {
    added.seqElems = s.seqElems + (afterLastIdx[s] -> e)
}

pred setAt [s: Seq, idx: SeqIdx, e: elem, setted: Seq] {
    idx in inds[s]
    setted.seqElems = (s.seqElems - (idx -> elem)) + (idx -> e)
}

pred insert [s: Seq, idx: SeqIdx, e: elem, inserted: Seq] {
    idx in inds[s] + afterLastIdx[s]
    inserted.seqElems =
        { j: SeqIdx, x: elem | ord/lt[j, idx] and j -> x in s.seqElems }
        + (idx -> e)
        + { j: SeqIdx, x: elem | ord/gte[j, idx] and j.(ord/prev) -> x in s.seqElems }
}

pred append [s1: Seq, s2: Seq, appended: Seq] {
    s1.allExist and s2.allExist
    appended.seqElems = s1.seqElems
        + { i: SeqIdx, x: elem |
              some j: inds[s2] | j -> x in s2.seqElems
                and #(ord/prevs[i]) = (#(ord/prevs[afterLastIdx[s1]]) fun/add #(ord/prevs[j])) }
}

pred subseq [s: Seq, sub: Seq, from: SeqIdx, to: SeqIdx] {
    sub.seqElems = { k: SeqIdx, x: elem |
        some m: SeqIdx | ord/lte[from, m] and ord/lte[m, to] and m -> x in s.seqElems
            and #(ord/prevs[k]) = (#(ord/prevs[m]) fun/sub #(ord/prevs[from])) }
}
