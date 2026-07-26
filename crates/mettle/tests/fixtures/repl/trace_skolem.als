// mt-068: a temporal command whose top-level existential still skolemizes.
// Skolemization is off *under* a temporal operator but a top-level one keeps
// its rigid witness (alloy6-temporal.md §(l), probes P-F1/F2), so `$witness_n`
// is an ordinary evaluator global whose value is the same at every state —
// while the `var` sig it talks about is not.
//
// The facts force the trace (`no A`, then alternate with `A = Q`) and therefore
// the witness: `Q` is in `A` at the odd states, so the only atom that is never
// in `A` is `P`.
abstract sig Node {}
one sig P, Q extends Node {}
var sig A in Node {}
fact {
  no A
  always (some A => after no A)
  always (no A => after (A = Q))
}

run witness { some n: Node | always (n not in A) } for 3 steps
