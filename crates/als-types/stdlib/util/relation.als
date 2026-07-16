// util/relation — generic properties of binary relations (functionality,
// injectivity, the standard order-theoretic hierarchy).
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.8) and standard
// relation-theory semantics, never from upstream Alloy's util/*.als text.
//
// §7.8's arities are deliberately non-uniform; `s` plays domain-and-
// codomain for the (r, s: set univ) group (an endorelation reading), while
// `irreflexive`/`symmetric`/`antisymmetric`/`transitive` need no domain set
// at all (self-contained relational-algebra tests via `iden`/converse/
// composition). `complete`'s `s: univ` is a single atom (§7 preamble: a
// bare unary param is `one`), so it gets its own, different reading:
// "every atom is reachable from `s` via `r`" (a distinguished-root
// completeness), not "the order over s is total" — that job now falls to
// `totalOrder`, which spells out its own comparability clause since it can
// no longer delegate to `complete`.

module util/relation

fun dom [r: univ -> univ]: set (r.univ) { r.univ }
fun ran [r: univ -> univ]: set (univ.r) { univ.r }

pred total [r: univ -> univ, s: set univ] { all x: s | some x.r }
pred functional [r: univ -> univ, s: set univ] { all x: s | lone x.r }
pred function [r: univ -> univ, s: set univ] { total[r, s] and functional[r, s] }

pred surjective [r: univ -> univ, s: set univ] { ran[s <: r] = s }
pred injective [r: univ -> univ, s: set univ] {
    all x, y: s | (some x.r and x.r = y.r) implies x = y
}
pred bijective [r: univ -> univ, s: set univ] {
    function[r, s] and surjective[r, s] and injective[r, s]
}

// `r` is a bijection specifically from `d` to `c` (distinct domain and
// codomain sets, unlike the endorelation-flavored `bijective` above).
pred bijection [r: univ -> univ, d: set univ, c: set univ] {
    all x: d | one x.r
    all y: c | one r.y
    ran[d <: r] = c
}

pred reflexive [r: univ -> univ, s: set univ] { all x: s | x -> x in r }
pred irreflexive [r: univ -> univ] { no (r & iden) }
pred symmetric [r: univ -> univ] { r = ~r }
pred antisymmetric [r: univ -> univ] { (r & ~r) in iden }
pred transitive [r: univ -> univ] { r.r in r }

pred acyclic [r: univ -> univ, s: set univ] { all x: s | x not in x.^(s <: r :> s) }

// Distinguished-root completeness: every atom is reachable from `s`.
pred complete [r: univ -> univ, s: univ] { univ in s.*r }

pred preorder [r: univ -> univ, s: set univ] { reflexive[r, s] and transitive[r] }
pred equivalence [r: univ -> univ, s: set univ] { preorder[r, s] and symmetric[r] }
pred partialOrder [r: univ -> univ, s: set univ] { preorder[r, s] and antisymmetric[r] }
pred totalOrder [r: univ -> univ, s: set univ] {
    partialOrder[r, s]
    all x, y: s | x = y or x -> y in r or y -> x in r
}
