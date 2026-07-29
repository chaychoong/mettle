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
// The smallest UNUSED index (jar-pinned semantics, probes mt046-afterLast/
// -seqrel-gap): `firstIdx` for an empty sequence, one past the last otherwise,
// `none` when every `SeqIdx` is used. `Seq`'s sig fact keeps `inds` a
// contiguous prefix, so on this domain it equals `lastIdx.next` + the empty
// case — the min-unused form is used for uniformity with seqrel/sequniv.
fun afterLastIdx [s: Seq]: lone SeqIdx {
    (SeqIdx - inds[s]) - (SeqIdx - inds[s]).^(ord/next)
}

fun first [s: Seq]: lone elem { at[s, firstIdx] }
fun last [s: Seq]: lone elem { at[s, lastIdx[s]] }

fun indsOf [s: Seq, e: elem]: set SeqIdx { (s.seqElems).e }
// `idxOf` = the *first* (order-least) index of `e`: remove the `^next`-reachable
// occurrences, leaving the minimum. `lastIdxOf` = the *last* (order-greatest):
// remove the `^prev`-reachable ones, leaving the maximum. (jar-verified: for `e`
// at both ends of a 3-seq, `idxOf = firstIdx`, `lastIdxOf = finalIdx`.)
fun idxOf [s: Seq, e: elem]: lone SeqIdx { indsOf[s, e] - indsOf[s, e].^(ord/next) }
fun lastIdxOf [s: Seq, e: elem]: lone SeqIdx { indsOf[s, e] - indsOf[s, e].^(ord/prev) }

pred isEmpty [s: Seq] { no s.seqElems }
pred hasDups [s: Seq] { some e: elems[s] | not lone indsOf[s, e] }

// `noDuplicates` / `allExist` / `allExistNoDuplicates` are **0-ary** (§7.5),
// not receiver preds on `Seq`: the jar rejects every receiver-style call —
// `x.noDuplicates`, `(x).noDuplicates`, `x.noDuplicates[]`, `noDuplicates[x]`
// all fail to type-check ("This must be a set or relation … {PrimitiveBoolean}")
// and only the bare `noDuplicates` resolves (probes mt085-p3 rows 0/3/4 and the
// bisect table in mt085/NOTES.md §"receiver-call rejection"). They are global
// statements about the whole `Seq` sig.
//
// `noDuplicates` — no `Seq` atom repeats an element. Global, and it makes no
// existence claim of its own: mt085-p5 row 15 (`exactly 1 Seq`) is SAT while
// rows 13/14 pin the count ceiling at the 5 duplicate-free contents available
// for 2 indices × 2 elems.
pred noDuplicates () { all s: Seq | not hasDups[s] }

// `allExist` — with `canonicalizeSeqs` supplying uniqueness, this supplies
// EXISTENCE: every sequence over (`SeqIdx`, `elem`) is realised by some `Seq`
// atom, so `Seq` becomes isomorphic to the set of all sequences. Stated
// inductively (empty exists; every non-full sequence extends by every element),
// which is first-order and generates exactly that closure.
//
// Pinned by the exact-scope counting probe mt085-p5, whose rows are UNSAT one
// atom below the predicted count and SAT at it — `exactly 7/6 Seq` at 2 idx ×
// 2 elem (rows 0/1), `exactly 3/2` at 2 idx × 1 elem (rows 2/3), `exactly
// 15/14` at 3 idx × 2 elem (rows 4/5), `exactly 13` at 2 idx × 3 elem (row 6).
// The non-exact scopes of round 4 prove nothing here: `util/ordering` pins
// `SeqIdx` to exactly its scope, but the solver is free to shrink `elem`.
pred allExist () {
    (some s: Seq | isEmpty[s])
    and (all s: Seq, e: elem |
            some afterLastIdx[s] =>
                (some t: Seq | t.seqElems = s.seqElems + (afterLastIdx[s] -> e)))
}

// `allExistNoDuplicates` — the same closure restricted to duplicate-free
// sequences, PLUS `noDuplicates`. The second conjunct is not redundant: without
// it, 5 duplicate-free atoms plus one duplicate-carrying atom would satisfy
// `exactly 6 Seq` at 2 idx × 2 elem, which the jar reports UNSAT (mt085-p5 row
// 9; rows 7/8 pin the count at exactly 5, rows 10/11 confirm at other shapes).
pred allExistNoDuplicates () {
    (some s: Seq | isEmpty[s])
    and (all s: Seq, e: elem - elems[s] |
            some afterLastIdx[s] =>
                (some t: Seq | t.seqElems = s.seqElems + (afterLastIdx[s] -> e)))
    and noDuplicates
}

pred startsWith [s: Seq, prefix: Seq] {
    isEmpty[prefix]
    or
    (inds[prefix] <: prefix.seqElems) = (inds[prefix] <: s.seqElems)
}

// `r` is `s` with its first element dropped and every remaining index shifted
// one step earlier. `s` must be non-empty — the jar makes `rest` FALSE rather
// than a no-op there (probe mt085-p1 row 3 UNSAT), unlike util/sequniv's `rest`
// which is total.
//
// The shifted lookup is a join equality, NOT `i.(ord/next) -> e in s.seqElems`:
// at `ord/last` the step is empty, `none -> e` is the empty relation, and
// `{} in s.seqElems` is VACUOUSLY TRUE, which would put every element at the
// last index at once — impossible for a `lone` column, so the whole pred went
// spuriously UNSAT (mt085-p1 rows 0/1/2, mettle-before UNSAT vs jar SAT). This
// is the util/seqrel defect of mt-084 (`09243ba`-era P4) in its second home.
pred rest [s: Seq, r: Seq] {
    some s.seqElems
    r.seqElems = { i: SeqIdx, e: elem | (i.(ord/next)).(s.seqElems) = e }
}

// `copy` is a ONE-WAY constraint, not an equality: it pins `dest` only at the
// indices the copy lands on, and leaves the rest of `dest` free. Jar-pinned —
// `copy[{i0->A}, dest, i0]` admits `dest = {i0->A, i1->B}` (mt085-p2 row 13),
// two distinct `dest`s satisfy one `copy` (row 14, SAT), and `copy` into `i2`
// from a length-1 source leaves `i0`/`i1` arbitrary (row 16, jar instance
// `{i0->C, i1->C, i2->A}`). An equality body made all three spuriously UNSAT.
// The copy must land entirely inside `SeqIdx`: mt085-p1 row 28 (a full source
// copied to `i1`) is UNSAT rather than truncated, which the `all k … some j`
// shape gives for free.
pred copy [source: Seq, dest: Seq, destStart: SeqIdx] {
    all k: inds[source] | some j: SeqIdx |
        #(ord/prevs[j]) = (#(ord/prevs[destStart]) fun/add #(ord/prevs[k]))
        and j -> k.(source.seqElems) in dest.seqElems
}

// `add` needs room: on a full sequence the jar is UNSAT (mt085-p1 row 14), not
// the no-op that dropping `none -> e` would silently produce.
pred add [s: Seq, e: elem, added: Seq] {
    some afterLastIdx[s]
    added.seqElems = s.seqElems + (afterLastIdx[s] -> e)
}

// `setAt` accepts the first FREE index as well as an occupied one, extending
// the sequence by one: `setAt[{i0->A, i1->B}, i2, C]` = `{i0->A, i1->B, i2->C}`
// (mt085-p2 row 18) and `setAt[{}, i0, A]` = `{i0->A}` (row 19). Anything past
// that is UNSAT (mt085-p1 row 16). So the guard is `inds + afterLastIdx`, the
// same one `insert` carries — an `idx in inds[s]` guard rejected both extending
// rows.
pred setAt [s: Seq, idx: SeqIdx, e: elem, setted: Seq] {
    idx in inds[s] + afterLastIdx[s]
    setted.seqElems = (s.seqElems - (idx -> elem)) + (idx -> e)
}

// `insert` needs room (`some afterLastIdx[s]`): inserting anywhere into a full
// sequence is UNSAT, not truncated — mt085-p1 row 7 and mt085-p2 rows 0/1 cover
// `idx` = first / middle / last. Contrast util/sequniv, whose `insert` truncates
// (mt-084 P2/P3).
//
// The tail shift is strictly `ord/gt`, and spelled as a join equality for the
// same reason `rest` is. `ord/gte` put both `idx -> e` and `idx -> s[idx.prev]`
// at `idx` (two values in a `lone` column → spurious UNSAT, mt085-p1 row 5 /
// mt085-p2 rows 2/3), and at `idx = ord/first` the `-> x in` spelling was
// additionally vacuous (mt085-p1 rows 4 and 9).
pred insert [s: Seq, idx: SeqIdx, e: elem, inserted: Seq] {
    idx in inds[s] + afterLastIdx[s]
    some afterLastIdx[s]
    inserted.seqElems =
        { j: SeqIdx, x: elem | ord/lt[j, idx] and j -> x in s.seqElems }
        + (idx -> e)
        + { j: SeqIdx, x: elem | ord/gt[j, idx] and (j.(ord/prev)).(s.seqElems) = x }
}

// `append` must fit end to end — `#s1 + #s2 <= #SeqIdx`, expressed as "every
// index of `s2` lands somewhere". Overflow is UNSAT, not truncation: 2+2 and
// 3+1 into 3 indices are both UNSAT (mt085-p1 rows 19/20) while 1+2 and 2+1 are
// SAT (rows 18, mt085-p2 row 5).
//
// The offset is `#(inds[s1])`, not `#(ord/prevs[afterLastIdx[s1]])`: for a full
// `s1` there is no after-index, and `#(ord/prevs[none])` is 0, which silently
// restarted `s2` at index 0 on top of `s1`.
pred append [s1: Seq, s2: Seq, appended: Seq] {
    all j: inds[s2] | some i: SeqIdx |
        #(ord/prevs[i]) = (#(inds[s1]) fun/add #(ord/prevs[j]))
    appended.seqElems = s1.seqElems
        + { i: SeqIdx, x: elem |
              some j: inds[s2] | j -> x in s2.seqElems
                and #(ord/prevs[i]) = (#(inds[s1]) fun/add #(ord/prevs[j])) }
}

// `subseq` is defined only on a non-empty, in-range, non-inverted window: both
// bounds must be occupied indices of `s` and `from <= to`. A reversed window is
// UNSAT rather than the empty sequence (mt085-p1 row 24), a `to` past the end is
// UNSAT rather than a clamped copy (mt085-p2 row 9), and `subseq` of an empty
// sequence is UNSAT (mt085-p2 row 11). `from in inds[s]` is implied by the other
// two (`inds` is a prefix) and is kept only as documentation.
pred subseq [s: Seq, sub: Seq, from: SeqIdx, to: SeqIdx] {
    from in inds[s]
    to in inds[s]
    ord/lte[from, to]
    sub.seqElems = { k: SeqIdx, x: elem |
        some m: SeqIdx | ord/lte[from, m] and ord/lte[m, to] and m -> x in s.seqElems
            and #(ord/prevs[k]) = (#(ord/prevs[m]) fun/sub #(ord/prevs[from])) }
}

// Negative space — deliberately NOT changed, each with the probe row that says
// so. Do not "fix" these:
//   * Every func (`inds` `elems` `at` `first` `last` `firstIdx` `finalIdx`
//     `lastIdx` `afterLastIdx` `idxOf` `lastIdxOf` `indsOf`) already matches the
//     jar value-for-value on all three of `{i0->A, i1->B, i2->A}`, `{i0->A}` and
//     the empty sequence — 36/36 rows, probe mt085-p6.
//   * The `Seq` sig fact and `canonicalizeSeqs` are right as written: a
//     non-prefix `{i1->A}` and a gapped `{i0->A, i2->B}` are both UNSAT
//     (mt085-p1 rows 10/11), and two atoms with equal contents are UNSAT (row
//     12).
//   * `isEmpty` and `startsWith` were already faithful (mt085-p1 rows 29/30,
//     mt085-p2 rows 20/21/22, 27/28). `startsWith` lost only its
//     `prefix.allExist` conjunct, which the sig fact already guarantees and
//     which no longer parses now that `allExist` is 0-ary.
//   * `rest`, `insert`, `add`, `append`, `subseq` and `copy` all have a UNIQUE
//     output where the jar has one — the "two distinct outputs" probes are UNSAT
//     for `rest` (mt085-p1 row 31, mt085-p2 row 23), `insert` (mt085-p1 row 32),
//     `append` (mt085-p2 row 7) and `subseq` (mt085-p2 row 12). `copy` is the
//     lone exception and is deliberately non-functional (mt085-p2 row 14, SAT).
//   * `insert`/`setAt` keep the `idx in inds[s] + afterLastIdx[s]` guard rather
//     than a `lte[idx, afterLastIdx[s]]` rewrite: mt085-p1 rows 8/16 pin the
//     rejection, and on this domain `inds` is a prefix so the two agree.
//   * mt-084's OTHER defect — a shifting result escaping the index domain — is
//     structurally impossible here and was not guarded against: every
//     comprehension binder is `j: SeqIdx`, and `SeqIdx` is a sig, so no result
//     tuple can carry an out-of-domain index the way util/sequniv's `Int`-ranged
//     ones could.
