-- Rung-6 `mettle exec` fixtures (mt-067): a bound-relative temporal `check`,
-- the one typed defer the driver raises before any solving, and (mt-077) a
-- `check` at a one-state bound, which is answered like any other length.
var sig A {}

-- Always true (the universe is never empty), so the check finds no
-- counterexample and reports it *relative to the steps bound*.
assert UnivIsNeverEmpty { always (some univ) }
check UnivIsNeverEmpty for 2 but 4 steps

-- [1] an unbounded range: the reference's bounded engine refuses it (T-08b).
check UnivIsNeverEmpty for 2 but 1.. steps

-- [2] a `check` at a one-state bound (mt-077, probe P-077-5): answered, not
--     refused. `some univ` holds in the single state, so this is VALID within
--     the bound.
check UnivIsNeverEmpty for 2 but 1 steps

-- [3] a `check` at a one-state bound with a real counterexample (P-077-1): the
--     single-state lasso in which `A` is empty falsifies it.
assert AlwaysSomeA { always (some A) }
check AlwaysSomeA for 2 but 1 steps
