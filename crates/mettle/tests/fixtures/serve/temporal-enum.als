-- mt-076 serve fixture: a temporal command with BOTH a real path space and a
-- real configuration space, so every one of the four exploration verbs has
-- something to do. `X` may hold 1 or 2 atoms (two non-isomorphic
-- configurations) and `A` is free at each state (four per-state combinations
-- times two loop targets inside a configuration).
--
-- Its shape is `scratchpad/probe/mt076/fixtures/StaticMultiConfig.als`, the
-- fixture probes P-076-1/P-076-5 were run against, so the numbers this fixture
-- produces are the jar-pinned ones.
sig X {}
var sig A in X {}
run { some X } for 2 but exactly 2 steps
