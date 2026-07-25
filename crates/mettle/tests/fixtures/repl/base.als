// mt-062 evaluator battery: the shapes probed against the reference jar as
// E-01..E-20, E-37..E-39, E-43/E-44 and E-49 (docs/reference/alloy6-evaluator.md
// §6). Scopes and the `g` fact pin the instance exactly, so every rendered
// value below is a function of the model, not of which model the solver
// happened to find first.
sig A {}
sig B { f: one A }
sig C { g: A -> B }

fact { g = C -> A -> B }

run Show {} for exactly 1 A, exactly 3 B, exactly 3 C
