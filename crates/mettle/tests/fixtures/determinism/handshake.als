// Integer arithmetic in the search loop: pair up people so that every person's
// count of acquaintances is even, with a summed total. Forces the int encoding
// to participate rather than pure relational structure.
sig Person {
  knows: set Person
}
fact Symmetric {
  knows = ~knows
  no p: Person | p in p.knows
}
pred evenDegrees {
  all p: Person | rem[#p.knows, 2] = 0
  some p: Person | #p.knows > 0
}
run evenDegrees for exactly 6 Person, 5 int expect 1
