// mt-062: a command with no instance is nothing to evaluate against
// (E-34, E-35).
sig A {}

run Impossible { some A and no A } for 3
