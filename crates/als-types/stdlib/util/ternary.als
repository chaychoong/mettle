// util/ternary — projection and column-permutation helpers for ternary
// relations (`univ -> univ -> univ`).
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.10) and standard
// relational-algebra semantics (dot-join column projection), never from
// upstream Alloy's util/*.als text. Result types are the exact dependent
// projections §7.10 pins; each body computes precisely that value.

module util/ternary

fun dom [r: univ -> univ -> univ]: set ((r.univ).univ) { (r.univ).univ }
fun ran [r: univ -> univ -> univ]: set (univ.(univ.r)) { univ.(univ.r) }
fun mid [r: univ -> univ -> univ]: set (univ.(r.univ)) { univ.(r.univ) }

fun select12 [r: univ -> univ -> univ]: r.univ { r.univ }
fun select23 [r: univ -> univ -> univ]: univ.r { univ.r }
fun select13 [r: univ -> univ -> univ]: ((r.univ).univ) -> (univ.(univ.r)) {
    { a: dom[r], c: ran[r] | some b: mid[r] | a -> b -> c in r }
}

fun flip12 [r: univ -> univ -> univ]:
    (univ.(r.univ)) -> ((r.univ).univ) -> (univ.(univ.r))
{
    { b: mid[r], a: dom[r], c: ran[r] | a -> b -> c in r }
}

fun flip13 [r: univ -> univ -> univ]:
    (univ.(univ.r)) -> (univ.(r.univ)) -> ((r.univ).univ)
{
    { c: ran[r], b: mid[r], a: dom[r] | a -> b -> c in r }
}

fun flip23 [r: univ -> univ -> univ]:
    ((r.univ).univ) -> (univ.(univ.r)) -> (univ.(r.univ))
{
    { a: dom[r], c: ran[r], b: mid[r] | a -> b -> c in r }
}
