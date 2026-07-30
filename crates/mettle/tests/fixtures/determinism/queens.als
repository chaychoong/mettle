// Non-attacking rooks on a 6x6 board with a diagonal ban: a placement search
// with many solutions, so which one is reported is a heuristic choice.
open util/ordering[Row] as ro
open util/ordering[Col] as co
sig Row {}
sig Col {}
sig Board {
  at: Row -> one Col
}
pred distinctCols[b: Board] {
  all disj r1, r2: Row | r1.(b.at) != r2.(b.at)
}
pred noAdjacentDiagonal[b: Board] {
  all r: Row | some r.ro/next implies {
    (r.(b.at)).co/next != (r.ro/next).(b.at)
    (r.ro/next.(b.at)).co/next != r.(b.at)
  }
}
run { some b: Board | distinctCols[b] and noAdjacentDiagonal[b] }
  for exactly 6 Row, exactly 6 Col, exactly 1 Board expect 1
