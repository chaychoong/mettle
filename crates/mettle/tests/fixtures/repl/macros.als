// mt-100 — module-level macros in integer position, evaluator side.
//
// The scope is exact so the solved instance is pinned by the model, not by
// which satisfying assignment the search reaches first: `A` is saturated at
// two atoms, `B.v` is fixed to 3, and the bitwidth is 4 so the `0-(max+1)`
// fold's trigger literal is `0-8`.
//
// `cardm`'s parameter deliberately shadows the module-level macro `s`.
sig A {}
one sig B { v: one Int }
fact { #A = 2 and B.v = 3 }

let k = #A
let n = 3
let m = 0-8
let j = plus[1, 2]
let deep = plus[k, 1]
let f[x] = plus[x, 1]
let cardm[s] = #s
let s = A

run { } for 2 but 4 int
