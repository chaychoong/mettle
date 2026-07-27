-- mt-072 serve fixture: a lasso trace, for the per-state evaluator and the
-- typed defers that stand in for trace enumeration until mt-076.
one sig Counter {}
var sig A in Counter {}
fact {
  no A
  always (no A => after some A)
  always (some A => after some A)
}
run { eventually some A } for 3 but 3 steps
