// mt-107 P3: the `$` metamodel at the evaluator prompt (P0 probe wave,
// `scratchpad/probe/mt107/out/m5_eval.txt`). The probe ran against the
// unconstrained `m1_01` cell and the jar happened to land on an all-empty
// instance; the fact pins that here, so the cells test the evaluator rather
// than which satisfying assignment mettle's SAT search reaches first.
abstract sig V { f: lone V, g: lone V }
sig W extends V { h: lone W }
sig Z {}
fact { no f and no g and no h }
run meta { some V$ } for 3
