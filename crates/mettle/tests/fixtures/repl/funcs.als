// mt-062: calling a model pred/fun from the prompt (E-21, E-22, E-23).
sig A {}

pred isEmpty[s: set A] { no s }
fun double[x: Int]: Int { plus[x, x] }

run Show {} for exactly 1 A
