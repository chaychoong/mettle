-- mt-072 serve fixture: one command with exactly two instances, so a `next`
-- click has somewhere to go and a second one runs the enumeration out.
--
-- `Red`/`Green` are distinguishable `one sig`s, so symmetry breaking cannot
-- fold the two colourings into one: the space is exactly {Node -> Red} and
-- {Node -> Green}.
abstract sig Color {}
one sig Red extends Color {}
one sig Green extends Color {}
sig Node { color: one Color }
run { some Node } for exactly 1 Node
