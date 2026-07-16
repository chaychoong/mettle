// util/integer — arithmetic, comparison, and ordering helpers over Alloy's
// built-in `Int` atoms.
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.2) and the
// language's own built-in integer operators (`fun/add` et al., `fun/min`,
// `fun/max`, `fun/next`), never from upstream Alloy's util/*.als text.
//
// The analyzer name-checks "util/integer" and inlines/excludes its funcs
// from meta-model reflection (per the resolution doc); that special-casing
// is Java-side and out of scope here — this file only needs to describe the
// same public surface with standard semantics.

module util/integer

fun add [n1, n2: Int]: Int { n1 fun/add n2 }
fun plus [n1, n2: Int]: Int { n1 fun/add n2 }
fun sub [n1, n2: Int]: Int { n1 fun/sub n2 }
fun minus [n1, n2: Int]: Int { n1 fun/sub n2 }
fun mul [n1, n2: Int]: Int { n1 fun/mul n2 }
fun div [n1, n2: Int]: Int { n1 fun/div n2 }
fun rem [n1, n2: Int]: Int { n1 fun/rem n2 }
fun negate [n: Int]: Int { 0 fun/sub n }

pred eq [n1, n2: Int] { n1 = n2 }
pred gt [n1, n2: Int] { n1 > n2 }
pred lt [n1, n2: Int] { n1 < n2 }
pred gte [n1, n2: Int] { n1 >= n2 }
pred lte [n1, n2: Int] { n1 <= n2 }
pred zero [n: Int] { n = 0 }
pred pos [n: Int] { n > 0 }
pred neg [n: Int] { n < 0 }
pred nonpos [n: Int] { n <= 0 }
pred nonneg [n: Int] { n >= 0 }

fun signum [n: Int]: Int { pos[n] => 1 else (neg[n] => -1 else 0) }

fun max: one Int { fun/max }
fun min: one Int { fun/min }
fun next: Int -> Int { fun/next }
fun prev: Int -> Int { ~(fun/next) }

fun prevs [e: Int]: set Int { e.^prev }
fun nexts [e: Int]: set Int { e.^next }

fun larger [n1, n2: Int]: Int { lte[n1, n2] => n2 else n1 }
fun smaller [n1, n2: Int]: Int { lte[n1, n2] => n1 else n2 }

fun max [es: set Int]: lone Int { es - es.^next }
fun min [es: set Int]: lone Int { es - es.^prev }

// Converts between `Int` and elements ordered by an externally supplied
// `next` relation (e.g. some `util/ordering` instance's `next`): `int2elem`
// maps a zero-based rank to the element of that rank within `s`;
// `elem2int` maps an element to its zero-based rank (count of strict
// predecessors reachable backwards along `next`). Standard rank<->element
// correspondence for a totally ordered set; signature pinned by §7.2
// (int2elem's result is `lone s` — a lone member of the supplied set).
fun int2elem [i: Int, next: univ -> univ, s: set univ]: lone s {
    { e: s | #(s & e.^(~next)) = i }
}

fun elem2int [e: univ, next: univ -> univ]: lone Int {
    #(e.^(~next))
}
