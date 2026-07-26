-- mt-068 trace rendering, the loop-*not*-at-the-last-state case: the mt-066/067
-- alternation gadget forces exactly 2 states looping back to state 0 (k=1 would
-- need `no A` and `some A` at the same state; a loop onto state 1 would need
-- state 1 to alternate with itself).
--
-- `Rigid` is a static sig with a forced population: its line must appear
-- byte-identically in every state block — rigid content is re-emitted, never
-- factored out (alloy6-temporal.md §(f), probe T-13).
sig Rigid {}
var sig A {}
fact { no A }
fact { always (some A => after no A) }
fact { always (no A => after some A) }
run { } for exactly 2 Rigid, 1 A, 3 steps
