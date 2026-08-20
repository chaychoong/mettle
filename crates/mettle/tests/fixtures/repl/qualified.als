-- mt-098: a solved instance whose universe carries MODULE-QUALIFIED atom
-- labels (`so/Ord$0`), the shape the evaluator used to print but could not
-- read back. Two aliased `util/ordering` instances plus the un-aliased one
-- `enum` opens implicitly, an enum, and a String atom, so one fixture covers
-- every atom-label kind the round-trip has to survive.
open util/ordering[A] as so
open util/ordering[B] as tw
sig A {}
sig B {}
enum Color { Red, Green, Blue }
one sig S { s: one String }
fact { S.s = "hi" }
run { some A and some B } for exactly 2 A, exactly 2 B
