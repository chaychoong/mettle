// mt-062: string atoms render with their quotes (E-40, E-41).
sig A { label: one String }

fact { A.label = "hello" }

run Show {} for exactly 1 A
