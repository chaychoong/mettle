-- A `steps` scope on a model with no `var` and no temporal operator: the
-- reference rejects it (probe T-03, ScopeComputer.java:479/:487).
sig A {}
run { some A } for 2 but 3 steps
