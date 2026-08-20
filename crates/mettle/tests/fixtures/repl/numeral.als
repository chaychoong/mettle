// mt-099 — the numeral-rendering surface (evaluator contract §3, E-59..E-79).
//
// Scopes are exact so the solved instance is pinned by the model rather than by
// which satisfying assignment the search reaches first: exactly one `A` atom,
// `B.v` fixed to 3, and bitwidth 4 so the wrap edges (-8..7) are reachable.
sig A {}
one sig B { v: one Int }
fact { B.v = 3 }
run { some A } for 1 but 4 int
