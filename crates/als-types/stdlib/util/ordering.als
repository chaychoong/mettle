// util/ordering — a total order over a parameter set `elem`.
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.1) and standard
// order-theory semantics, never from upstream Alloy's util/*.als text.
//
// The analyzer's exact-bounds / symmetry-breaking special-casing for
// ordered sigs is Java-side behavior (not expressed here); see the
// SEMANTICS_LEDGER entries filed alongside beads mt-015/mt-017.

module util/ordering[exactly elem]

private one sig Ord {
    private First: set elem,
    private Next: elem -> elem
} {
    pred/totalOrder[elem, First, Next]
}

// Declaration order `first, last, prev, next` is load-bearing: the XML
// writer's `m<i>` fun-skolem indices number reachable zero-arg funs in
// declaration order per module, and the jar's util/ordering declares in
// this order (mt-132 probe `Macros.als`, jar `m2 first m3 last m4 prev
// m5 next`). Forward references between funs are legal, so bodies may
// mention `next` before its declaration.
fun first: one elem { Ord.First }
fun last: one elem { elem - next.elem }
// `~next` is ambiguous: `util/integer` is auto-opened into every module and
// also exports a 0-ary `next(): Int -> Int`; under transpose there is no join
// context to filter it out by type, so a bare `next` here has two live
// candidates. `this/next` scopes the lookup to this module's own
// declarations only (resolution-doc §2.4/§4.4), which is unambiguous.
fun prev: elem -> elem { ~this/next }
fun next: elem -> elem { Ord.Next }

fun prevs [e: elem]: set elem { e.^prev }
fun nexts [e: elem]: set elem { e.^next }

pred lt [e1, e2: elem] { e1 in prevs[e2] }
pred gt [e1, e2: elem] { e2 in prevs[e1] }
pred lte [e1, e2: elem] { e1 = e2 or lt[e1, e2] }
pred gte [e1, e2: elem] { e1 = e2 or gt[e1, e2] }

fun larger [e1, e2: elem]: elem { lte[e1, e2] => e2 else e1 }
fun smaller [e1, e2: elem]: elem { lte[e1, e2] => e1 else e2 }

fun max [es: set elem]: lone elem { es - es.^prev }
fun min [es: set elem]: lone elem { es - es.^next }

assert correct {
    pred/totalOrder[elem, first, next]
}

run {} for 4
check correct for 4
