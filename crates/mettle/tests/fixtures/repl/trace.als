// mt-068 per-state evaluator: the wave-2 probe fixture (`scratchpad/probe/
// mt064/fixtures/TraceDemo.als`) with a `run` in place of its `check`, so the
// REPL attaches to a plain SAT. The facts pin every state, so every cell in
// `repl.rs` is a function of the model — not of which trace the solver found:
//
//   state 0: no A,   no B
//   state 1: A,      no B
//   state 2: no A,   B      <- the loop state (T-13: traceLength=3, loopState=2)
//
// The eval cells reproduce T-22/T-23/T-24 (wrap/clamp, temporal operators as
// evaluator input) against this exact trace, jar-free.
one sig Counter {}
var sig A, B in Counter {}
fact {
  no A
  no B
  always (no A and no B => after (some A and no B))
  always (some A and no B => after (no A and some B))
  always (no A and some B => after (no A and some B))
}

run Show {} for 3 steps
