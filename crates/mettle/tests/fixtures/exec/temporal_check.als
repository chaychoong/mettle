-- Rung-6 `mettle exec` fixtures (mt-067): a bound-relative temporal `check`,
-- plus the two typed defers the driver raises before any solving.
var sig A {}

-- Always true (the universe is never empty), so the check finds no
-- counterexample and reports it *relative to the steps bound*.
assert UnivIsNeverEmpty { always (some univ) }
check UnivIsNeverEmpty for 2 but 4 steps

-- [1] an unbounded range: the reference's bounded engine refuses it (T-08b).
check UnivIsNeverEmpty for 2 but 1.. steps

-- [2] a `check` at a one-state bound: the pinned jar NullPointerException
--     (T-10a/T-11), an open owner fork.
check UnivIsNeverEmpty for 2 but 1 steps
