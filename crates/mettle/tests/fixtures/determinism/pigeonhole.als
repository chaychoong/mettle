// Pigeonhole: 5 pigeons into 4 holes, injectively. UNSAT, and not by
// propagation -- the solver has to analyze conflicts to prove it.
sig Pigeon {}
sig Hole {}
sig Nest {
  where: Pigeon -> one Hole
}
pred injective {
  some n: Nest |
    all disj p1, p2: Pigeon | p1.(n.where) != p2.(n.where)
}
run injective for exactly 5 Pigeon, exactly 4 Hole, exactly 1 Nest expect 0
