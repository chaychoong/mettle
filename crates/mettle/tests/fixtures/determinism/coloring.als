// A proper 3-colouring of a 6-node cycle: symmetry-rich, many solutions, and
// the symmetry-breaking predicate and the search interact.
sig Color {}
sig Node {
  adj: set Node,
  color: one Color
}
fact Cycle {
  // A single 6-cycle: every node has exactly two neighbours, symmetric,
  // irreflexive, and connected.
  all n: Node | #n.adj = 2
  adj = ~adj
  no n: Node | n in n.adj
  all n: Node | Node in n.*adj
}
pred proper {
  all n: Node, m: n.adj | n.color != m.color
}
run proper for exactly 6 Node, exactly 3 Color expect 1
