// util/natural — the natural numbers as an ordered sig (an alternative to
// `Int` for models that want unbounded-looking, non-negative, non-wrapping
// arithmetic within whatever scope is given).
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.4) and standard
// Peano-style semantics (arithmetic derived from rank in the total order),
// never from upstream Alloy's util/*.als text.

module util/natural

private open util/ordering[Natural] as ord
private open util/integer as integer

sig Natural {}

one sig Zero in Natural {}
lone sig One in Natural {}

fact {
    Zero = ord/first
    One = Zero.(ord/next)
}

fun inc [n: Natural]: lone Natural { n.(ord/next) }
fun dec [n: Natural]: lone Natural { n.(ord/prev) }

// Arithmetic is defined via rank (the count of strictly-smaller elements in
// the order, computed through the privately opened `util/integer`): a
// result exists only if some `Natural` atom in the current scope has the
// matching rank, which is exactly the partiality `lone` promises
// (out-of-scope results are simply absent, not wrapped).
fun add [n1, n2: Natural]: lone Natural {
    { n3: Natural | integer/eq[#(ord/prevs[n3]), integer/add[#(ord/prevs[n1]), #(ord/prevs[n2])]] }
}

fun sub [n1, n2: Natural]: lone Natural {
    { n3: Natural | integer/eq[#(ord/prevs[n3]), integer/sub[#(ord/prevs[n1]), #(ord/prevs[n2])]] }
}

fun mul [n1, n2: Natural]: lone Natural {
    { n3: Natural | integer/eq[#(ord/prevs[n3]), integer/mul[#(ord/prevs[n1]), #(ord/prevs[n2])]] }
}

fun div [n1, n2: Natural]: lone Natural {
    { n3: Natural | integer/eq[#(ord/prevs[n3]), integer/div[#(ord/prevs[n1]), #(ord/prevs[n2])]] }
}

pred gt [n1, n2: Natural] { ord/gt[n1, n2] }
pred lt [n1, n2: Natural] { ord/lt[n1, n2] }
pred gte [n1, n2: Natural] { ord/gte[n1, n2] }
pred lte [n1, n2: Natural] { ord/lte[n1, n2] }

fun max [ns: set Natural]: lone Natural { ord/max[ns] }
fun min [ns: set Natural]: lone Natural { ord/min[ns] }
