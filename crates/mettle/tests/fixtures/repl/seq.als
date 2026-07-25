// mt-062: a `seq` value is an ordinary index->element binary relation, with no
// special syntax (E-42). One element and length 2 pin it exactly.
sig A {}
one sig Holder { xs: seq A }

fact { #Holder.xs = 2 }

run Show {} for exactly 1 A, 3 seq
