// util/graph — standard graph-theoretic properties (connectivity,
// acyclicity, tree-ness) over an edge relation on a parameter set `node`.
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.9) and standard
// graph-theory semantics, never from upstream Alloy's util/*.als text.

module util/graph[node]

open util/relation as rel

pred undirected [r: node -> node] { rel/symmetric[r] }
pred noSelfLoops [r: node -> node] { rel/irreflexive[r] }

pred weaklyConnected [r: node -> node] {
    all disj n1, n2: node | n2 in n1.^(r + ~r)
}

pred stronglyConnected [r: node -> node] {
    all disj n1, n2: node | n2 in n1.^r
}

pred rootedAt [r: node -> node, root: node] { node in root.*r }

fun roots [r: node -> node]: set node { node - node.r }
fun leaves [r: node -> node]: set node { node - r.node }
fun innerNodes [r: node -> node]: set node { node - roots[r] - leaves[r] }

pred dag [r: node -> node] { rel/acyclic[r, node] }

pred forest [r: node -> node] {
    dag[r]
    all n: node | lone n.~r
}

pred tree [r: node -> node] {
    forest[r]
    one roots[r]
}

pred treeRootedAt [r: node -> node, root: node] {
    tree[r] and rootedAt[r, root]
}

pred ring [r: node -> node] {
    rel/function[r, node]
    rel/injective[r, node]
    weaklyConnected[r]
}
