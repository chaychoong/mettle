// util/time — a totally ordered set of time steps, plus a family of
// textual `let` macros for writing "explicit-time" (pre-`var`) temporal
// idioms over it. Deliberately has no `module` header (§7.11 pins this as
// a legal, header-less module).
//
// This file is part of mettle, MPL-2.0.
// Clean-room implementation per ADR-0006: written from the documented
// module interface (docs/reference/alloy6-resolution.md §7.11), never from
// upstream Alloy's util/*.als text.
//
// Judgment call (flagged for the Ledger, see mt-015 report): macro BODIES
// are not pinned by §7.11 (only names/arity/param-names are), and macros
// expand by textual substitution (§3.7) rather than true recursion, so a
// literally recursive definition isn't available. `then` is read as a
// simple two-step sequencing helper. `whileN` is read as a manually
// unrolled bounded while loop: each `whileN` composes the *lower-numbered*
// macro (a legal acyclic macro-dependency chain, not self-recursion),
// allowing at most one more iteration of `body` than `whileN-1`. This
// captures the shape of a bounded loop; the operational fidelity of the
// per-step `cond`/`body` substitution against real traces is exactly the
// kind of thing mt-020's differential run should stress.

open util/ordering[Time]

sig Time {}

let dynamic [x] = some t1, t2: Time | t1 != t2 and x.t1 != x.t2
let dynamicSet [x] = some t1, t2: Time | t1 != t2 and x.t1 != x.t2

let then [a, b, t, t"] = a implies (ordering/lt[t, t"] and b)

let while0 [cond, body, t, t"] = not cond and t" = t
let while1 [cond, body, t, t"] =
    while0[cond, body, t, t"] or (cond and body and t" = t)
let while2 [cond, body, t, t"] =
    while1[cond, body, t, t"] or (cond and body and some tm: Time | while1[cond, body, tm, t"])
let while3 [cond, body, t, t"] =
    while2[cond, body, t, t"] or (cond and body and some tm: Time | while2[cond, body, tm, t"])
let while4 [cond, body, t, t"] =
    while3[cond, body, t, t"] or (cond and body and some tm: Time | while3[cond, body, tm, t"])
let while5 [cond, body, t, t"] =
    while4[cond, body, t, t"] or (cond and body and some tm: Time | while4[cond, body, tm, t"])
let while6 [cond, body, t, t"] =
    while5[cond, body, t, t"] or (cond and body and some tm: Time | while5[cond, body, tm, t"])
let while7 [cond, body, t, t"] =
    while6[cond, body, t, t"] or (cond and body and some tm: Time | while6[cond, body, tm, t"])
let while8 [cond, body, t, t"] =
    while7[cond, body, t, t"] or (cond and body and some tm: Time | while7[cond, body, tm, t"])
let while9 [cond, body, t, t"] =
    while8[cond, body, t, t"] or (cond and body and some tm: Time | while8[cond, body, tm, t"])

let while = while3
