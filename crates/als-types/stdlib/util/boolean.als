// util/boolean — a two-valued boolean sig with the standard logical
// connectives, for models that want boolean *values* (as opposed to
// Alloy's native formulas).
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.3) and standard
// Boolean-algebra semantics, never from upstream Alloy's util/*.als text.

module util/boolean

abstract sig Bool {}
one sig True, False extends Bool {}

pred isTrue [b: Bool] { b = True }
pred isFalse [b: Bool] { b = False }

fun Not [b: Bool]: Bool { b = True => False else True }
fun And [b1, b2: Bool]: Bool { (b1 = True and b2 = True) => True else False }
fun Or [b1, b2: Bool]: Bool { (b1 = True or b2 = True) => True else False }
fun Xor [b1, b2: Bool]: Bool { b1 = b2 => False else True }
fun Nand [b1, b2: Bool]: Bool { Not[And[b1, b2]] }
fun Nor [b1, b2: Bool]: Bool { Not[Or[b1, b2]] }

// Private helper: true iff every element of `s1` is, under the natural
// True-as-member reading, also present in `s2` (i.e. `s1 in s2`).
private fun subset_ [s1: set Bool, s2: set Bool]: Bool { s1 in s2 => True else False }
