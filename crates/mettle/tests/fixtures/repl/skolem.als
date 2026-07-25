// mt-062: a skolem name is an ordinary global (E-24).
sig A {}

run foo { some x: A | x = x } for exactly 1 A
