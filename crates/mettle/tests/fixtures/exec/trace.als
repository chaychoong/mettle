-- mt-068 trace rendering: the wave-2 probe fixture `scratchpad/probe/mt064/
-- fixtures/TraceDemo.als`, verbatim (alloy6-temporal.md §(f), probe T-13), so
-- the rendered trace is checkable against a jar-captured one.
--
-- The facts force every state: state0=(no A, no B), state1=(A, no B),
-- state2=(no A, some B) — and state2's rule re-triggers its own guard, so the
-- minimal trace is 3 states looping back onto state 2 (T-13 live: `traceLength=3
-- loopState=2`). That makes it the "loop at the last state" case as well.
one sig Counter {}
var sig A, B in Counter {}
fact {
  no A
  no B
  always (no A and no B => after (some A and no B))
  always (some A and no B => after (no A and some B))
  always (no A and some B => after (no A and some B))
}
assert NeverB { always no B }
check NeverB for 3 steps
