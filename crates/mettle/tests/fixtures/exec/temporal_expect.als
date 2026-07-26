-- mt-069 probe T-12: `expect` on a temporal command reports the same way it
-- does on a static one -- no special-casing at the execute_command layer
-- (alloy6-temporal.md §(c), jar-verified against ExpectTemporal.als). Both
-- commands solve identically (SAT); the first's `expect 1` matches, the
-- second's `expect 0` (declaring UNSAT expected) does not.
var sig A {}
pred p { A' = A }
run p expect 1
run p expect 0
