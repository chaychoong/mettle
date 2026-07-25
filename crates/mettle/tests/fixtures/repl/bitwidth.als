// mt-062: bitwidth is inherited from the *solved command* (E-25, E-26) — the
// same expression wraps differently under the two `int` scopes.
sig A {}

run Wide { some A } for 3 but 4 int
run Narrow { some A } for 3 but 3 int
