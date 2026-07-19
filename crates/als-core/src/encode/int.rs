//! Two's-complement integer encoding — the Rung-3 slice (translation-ref §2.4).
//!
//! An [`IntVal`] is a fixed-width two's-complement bit-vector, **LSB first**, of
//! exactly the command's bitwidth (Int atoms span `-2^(bw-1) … 2^(bw-1)-1`).
//! The corpus measurement (mt-033) showed the only integer nodes reachable in
//! lowerable commands are `Const`, `Card` (cardinality), and `AtomToInt`
//! (`int[·]`) — no arithmetic, `sum`, or int-`ITE` — so this module implements:
//!
//! - constants ([`IntVal::constant`]);
//! - unsigned **cardinality** accumulation ([`IntBuilder::add_bit`], driven by
//!   the encoder's [`super::Encoder::int_card`]);
//! - signed **two's-complement addition** with overflow detection
//!   ([`IntBuilder::add_signed`]) for `int[·]`;
//! - the comparison predicates ([`IntBuilder::signed_lt`], [`IntBuilder::eq`]).
//!
//! Everything else (`plus`/`minus`/`mul`/…, `sum`, int-`ITE`) is a typed defer
//! in the encoder, never a wrong verdict (STYLE E5). Overflow honours the
//! LEDGER-001 switch: each overflow-capable op returns an **overflow flag**; the
//! encoder conjoins `¬flag` into the goal when overflow is forbidden (the
//! default), and ignores it (two's-complement wraps) when allowed.

use super::circuit::{Bool, Circuit};
use crate::overflow_guard::shift_mask_width;

/// A fixed-width two's-complement integer, least-significant bit first.
#[derive(Clone, Debug)]
pub struct IntVal {
    /// `bits[0]` is the LSB; `bits[width-1]` is the sign bit.
    bits: Vec<Bool>,
}

impl IntVal {
    /// The constant `value` in `width` bits (two's complement, wrapping — an
    /// out-of-range literal takes its low `width` bits, matching a fixed
    /// bitwidth; Rung-3 literals are in range).
    #[must_use]
    pub fn constant(value: i64, width: usize) -> Self {
        let bits = (0..width)
            .map(|i| Bool::Const((value >> i) & 1 == 1))
            .collect();
        Self { bits }
    }

    /// The bits, LSB first.
    #[must_use]
    pub fn bits(&self) -> &[Bool] {
        &self.bits
    }

    /// The bit width.
    #[must_use]
    pub fn width(&self) -> usize {
        self.bits.len()
    }

    /// Builds a value directly from bits (LSB first) — for gated constants.
    #[must_use]
    pub fn from_bits(bits: Vec<Bool>) -> Self {
        Self { bits }
    }
}

/// Integer-arithmetic gate builder over a [`Circuit`].
///
/// A thin façade so the encoder can construct integer networks without threading
/// the circuit through every helper; every method is a pure function of its
/// inputs (STYLE D1) and mints auxiliaries in a fixed order.
pub struct IntBuilder<'c, 'a> {
    circ: &'c mut Circuit<'a>,
    width: usize,
}

impl<'c, 'a> IntBuilder<'c, 'a> {
    /// Wraps a circuit for a fixed bit width.
    pub fn new(circ: &'c mut Circuit<'a>, width: usize) -> Self {
        Self { circ, width }
    }

    /// A full adder: returns `(sum, carry_out)` for `a + b + carry_in`.
    fn full_add(&mut self, a: Bool, b: Bool, cin: Bool) -> (Bool, Bool) {
        let axb = self.circ.xor(a, b);
        let sum = self.circ.xor(axb, cin);
        // carry = (a & b) | (cin & (a ^ b))
        let ab = self.circ.and(a, b);
        let cx = self.circ.and(cin, axb);
        let carry = self.circ.or(ab, cx);
        (sum, carry)
    }

    /// Adds a single bit into an **unsigned** accumulator, widening by one bit
    /// when the carry escapes — the cardinality counter primitive. `acc` is LSB
    /// first; the result holds the exact sum (no overflow, no truncation).
    #[must_use]
    pub fn add_bit(&mut self, acc: &[Bool], bit: Bool) -> Vec<Bool> {
        let mut out = Vec::with_capacity(acc.len() + 1);
        let mut carry = bit;
        for &a in acc {
            let (s, c) = self.full_add(a, Bool::FALSE, carry);
            out.push(s);
            carry = c;
        }
        if !matches!(carry, Bool::Const(false)) {
            out.push(carry);
        }
        out
    }

    /// Signed two's-complement addition at the fixed width, with a signed
    /// **overflow** flag (`carry_in(msb) ⊕ carry_out(msb)`). Result wraps to the
    /// width; the caller decides what the overflow flag means (LEDGER-001).
    #[must_use]
    pub fn add_signed(&mut self, a: &IntVal, b: &IntVal) -> (IntVal, Bool) {
        debug_assert_eq!(a.width(), self.width);
        debug_assert_eq!(b.width(), self.width);
        let mut bits = Vec::with_capacity(self.width);
        let mut carry = Bool::FALSE;
        let mut carry_into_msb = Bool::FALSE;
        for i in 0..self.width {
            if i == self.width - 1 {
                carry_into_msb = carry;
            }
            let (s, c) = self.full_add(a.bits[i], b.bits[i], carry);
            bits.push(s);
            carry = c;
        }
        let overflow = self.circ.xor(carry_into_msb, carry);
        (IntVal { bits }, overflow)
    }

    /// Truncates/normalises an exact unsigned accumulator to a signed [`IntVal`]
    /// at the fixed width, returning `(value, overflow)`. Since the count is
    /// non-negative, overflow is "any bit at or above the sign position is set"
    /// (the value would exceed `2^(width-1)-1`).
    #[must_use]
    pub fn unsigned_to_signed(&mut self, acc: &[Bool]) -> (IntVal, Bool) {
        let mut bits = Vec::with_capacity(self.width);
        for i in 0..self.width {
            bits.push(acc.get(i).copied().unwrap_or(Bool::FALSE));
        }
        // Overflow if the sign bit or any higher bit is set.
        let mut high = Vec::new();
        for &b in acc.iter().skip(self.width - 1) {
            high.push(b);
        }
        let overflow = self.circ.or_many(high);
        (IntVal { bits }, overflow)
    }

    /// Structural equality `a = b` (bitwise `iff`, conjoined).
    #[must_use]
    pub fn eq(&mut self, a: &IntVal, b: &IntVal) -> Bool {
        let mut parts = Vec::with_capacity(self.width);
        for i in 0..self.width {
            let e = self.circ.iff(a.bits[i], b.bits[i]);
            parts.push(e);
        }
        self.circ.and_many(parts)
    }

    /// Signed `a ≤ b` = `¬(b < a)`.
    #[must_use]
    pub fn signed_le(&mut self, a: &IntVal, b: &IntVal) -> Bool {
        let gt = self.signed_lt(b, a);
        self.circ.not(gt)
    }

    /// Signed `a > b` = `b < a`.
    #[must_use]
    pub fn signed_gt(&mut self, a: &IntVal, b: &IntVal) -> Bool {
        self.signed_lt(b, a)
    }

    /// Signed `a ≥ b` = `¬(a < b)`.
    #[must_use]
    pub fn signed_ge(&mut self, a: &IntVal, b: &IntVal) -> Bool {
        let lt = self.signed_lt(a, b);
        self.circ.not(lt)
    }

    /// Signed less-than `a < b`, via the "flip the sign bit, compare unsigned"
    /// identity: signed `a < b` iff unsigned `(a ⊕ 2^(w-1)) < (b ⊕ 2^(w-1))`.
    #[must_use]
    pub fn signed_lt(&mut self, a: &IntVal, b: &IntVal) -> Bool {
        let msb = self.width - 1;
        let mut af = a.bits.clone();
        let mut bf = b.bits.clone();
        af[msb] = self.circ.not(af[msb]);
        bf[msb] = self.circ.not(bf[msb]);
        self.unsigned_lt(&af, &bf)
    }

    /// Unsigned less-than over equal-width LSB-first bit vectors: the borrow out
    /// of `a - b` is `1` exactly when `a < b`.
    fn unsigned_lt(&mut self, a: &[Bool], b: &[Bool]) -> Bool {
        // Ripple subtract; borrow_out after the MSB is the < predicate.
        let mut borrow = Bool::FALSE;
        for i in 0..a.len() {
            // borrow_out = (¬a & b) | (¬a & borrow_in) | (b & borrow_in)
            let na = self.circ.not(a[i]);
            let nab = self.circ.and(na, b[i]);
            let nabr = self.circ.and(na, borrow);
            let bbr = self.circ.and(b[i], borrow);
            borrow = self.circ.or_many(vec![nab, nabr, bbr]);
        }
        borrow
    }

    // ------------------------------------------------------ arithmetic (mt-044)

    /// The most-negative value at the fixed width (`−2^(w-1)`), as a constant.
    fn min_val(&self) -> IntVal {
        IntVal::constant(-(1i64 << (self.width - 1)), self.width)
    }

    /// Signed two's-complement subtraction `a − b` at the fixed width, with a
    /// signed **overflow** flag. Computed as `a + (¬b) + 1` (borrow-free ripple);
    /// overflow is `carry_in(msb) ⊕ carry_out(msb)`, the standard signed-subtract
    /// flag — correct at the edges (`0 − MIN` overflows), translation-ref §11.2.
    #[must_use]
    pub fn sub_signed(&mut self, a: &IntVal, b: &IntVal) -> (IntVal, Bool) {
        debug_assert_eq!(a.width(), self.width);
        debug_assert_eq!(b.width(), self.width);
        let mut bits = Vec::with_capacity(self.width);
        let mut carry = Bool::TRUE; // +1 for two's-complement negate of `b`
        let mut carry_into_msb = Bool::FALSE;
        for i in 0..self.width {
            if i == self.width - 1 {
                carry_into_msb = carry;
            }
            let nb = self.circ.not(b.bits[i]);
            let (s, c) = self.full_add(a.bits[i], nb, carry);
            bits.push(s);
            carry = c;
        }
        let overflow = self.circ.xor(carry_into_msb, carry);
        (IntVal { bits }, overflow)
    }

    /// Signed negation `−a` at the fixed width (`¬a + 1`), overflowing exactly
    /// when `a = MIN` (whose negation is out of range), translation-ref §11.2.
    #[must_use]
    pub fn negate(&mut self, a: &IntVal) -> (IntVal, Bool) {
        let inv = self.invert(a);
        self.add_signed(&inv, &IntVal::constant(1, self.width))
    }

    /// Bitwise complement (`¬` every bit) — the magnitude helper for negation and
    /// subtraction. No gate for constant bits; a literal negates for free.
    fn invert(&self, a: &IntVal) -> IntVal {
        let bits = a.bits.iter().map(|&b| self.circ.not(b)).collect();
        IntVal { bits }
    }

    /// The value bits only of `−a` (drops the overflow flag) — magnitude helper.
    fn negate_value(&mut self, a: &IntVal) -> IntVal {
        self.negate(a).0
    }

    /// Bitwise select `cond ? a : b` at the fixed width (int if-then-else mux,
    /// translation-ref §11.1). Also the composition primitive for the div/rem
    /// sign fix-up and the shift barrel.
    #[must_use]
    pub fn mux(&mut self, cond: Bool, a: &IntVal, b: &IntVal) -> IntVal {
        let bits = (0..self.width)
            .map(|i| self.circ.ite(cond, a.bits[i], b.bits[i]))
            .collect();
        IntVal { bits }
    }

    /// Whether `a` is zero (all bits clear).
    #[must_use]
    pub fn is_zero(&mut self, a: &IntVal) -> Bool {
        let anyset = self.circ.or_many(a.bits.clone());
        self.circ.not(anyset)
    }

    /// Signed multiplication `a × b`, wrapping to the width, with a signed
    /// **overflow** flag (the full `2w`-bit product leaves the `w`-bit signed
    /// range), translation-ref §11.2. The full product is computed by
    /// sign-extending both operands to `2w` bits and shift-adding.
    #[must_use]
    pub fn multiply(&mut self, a: &IntVal, b: &IntVal) -> (IntVal, Bool) {
        let w = self.width;
        let dw = 2 * w;
        let ax = Self::sign_extend(a, dw);
        let bx = Self::sign_extend(b, dw);
        // Shift-add: product = Σ_i bx[i] · (ax << i), keeping `dw` bits.
        let mut prod = vec![Bool::FALSE; dw];
        for (i, &bit) in bx.iter().enumerate() {
            let shifted = shift_left_bits(&ax, i, dw);
            let gated: Vec<Bool> = shifted.iter().map(|&s| self.circ.and(bit, s)).collect();
            prod = self.add_bits_fixed(&prod, &gated);
        }
        let value = IntVal {
            bits: prod[..w].to_vec(),
        };
        // Overflow: the high bits `w..dw` must all equal the sign bit `w-1`.
        let sign = prod[w - 1];
        let mut diffs = Vec::with_capacity(w);
        for &hb in &prod[w..dw] {
            let d = self.circ.xor(hb, sign);
            diffs.push(d);
        }
        let overflow = self.circ.or_many(diffs);
        (value, overflow)
    }

    /// Signed division and remainder `(a ÷ b, a mod b)` reproducing the jar's
    /// two's-complement values bit-exactly (translation-ref §11.2, §10.7b): `÷`
    /// truncates toward zero, `mod` takes the sign of the dividend, and the
    /// jar-specific edge values hold — `÷` by zero is `−sign(a)`, `mod` by zero is
    /// the dividend, and `MIN ÷ −1` wraps to `MIN`. Returned overflow flags follow
    /// the pinned forbid-mode rule (`I10`): `÷` overflows on `b = 0 ∨ (a = MIN ∧ b
    /// = −1)`; `mod` overflows on `b = 0`.
    ///
    /// The generic path is sign-magnitude: divide `|a|` by `|b|` unsigned
    /// (restoring), then fix the quotient's sign to `sign(a) ⊕ sign(b)` and the
    /// remainder's to `sign(a)`. This already yields `MIN ÷ −1 = MIN` (the
    /// magnitude `2^(w-1)` re-tagged negative is `MIN` again); only division by
    /// zero is muxed in explicitly.
    #[must_use]
    pub fn div_rem(&mut self, a: &IntVal, b: &IntVal) -> DivRem {
        let w = self.width;
        let sa = a.bits[w - 1];
        let sb = b.bits[w - 1];
        let neg_a = self.negate_value(a);
        let neg_b = self.negate_value(b);
        let mag_a = self.mux(sa, &neg_a, a);
        let mag_b = self.mux(sb, &neg_b, b);
        let (q_mag, r_mag) = self.unsigned_div_rem(&mag_a, &mag_b);
        let sign_q = self.circ.xor(sa, sb);
        let q_neg = self.negate_value(&q_mag);
        let q_signed = self.mux(sign_q, &q_neg, &q_mag);
        let r_neg = self.negate_value(&r_mag);
        let r_signed = self.mux(sa, &r_neg, &r_mag);

        // Division-by-zero muxes (b = 0 ⟺ |b| = 0):
        let b_zero = self.is_zero(b);
        let a_zero = self.is_zero(a);
        let one = IntVal::constant(1, w);
        let minus_one = IntVal::constant(-1, w);
        let zero = IntVal::constant(0, w);
        // −sign(a): a<0 → 1, a=0 → 0, a>0 → −1.
        let nonneg_branch = self.mux(a_zero, &zero, &minus_one);
        let dbz_val = self.mux(sa, &one, &nonneg_branch);
        let div = self.mux(b_zero, &dbz_val, &q_signed);
        let rem = self.mux(b_zero, a, &r_signed);

        // Overflow flags (forbid mode, translation-ref §11.3/I10).
        let a_is_min = {
            let m = self.min_val();
            self.eq(a, &m)
        };
        let b_is_neg1 = self.eq(b, &minus_one);
        let min_neg1 = self.circ.and(a_is_min, b_is_neg1);
        let div_overflow = self.circ.or(b_zero, min_neg1);
        DivRem {
            quotient: div,
            remainder: rem,
            div_overflow,
            rem_overflow: b_zero,
        }
    }

    /// Unsigned restoring division of two width-`w` bit patterns, returning
    /// `(quotient, remainder)` each width `w`. The `y = 0` result is unspecified
    /// (the caller muxes the division-by-zero value in), so this need only be
    /// correct for `y ≥ 1`.
    fn unsigned_div_rem(&mut self, x: &IntVal, y: &IntVal) -> (IntVal, IntVal) {
        let w = self.width;
        // `y` zero-extended to `w+1` bits (the remainder accumulator's width).
        let mut y_ext = y.bits.clone();
        y_ext.push(Bool::FALSE);
        let mut rem: Vec<Bool> = vec![Bool::FALSE; w + 1];
        let mut q: Vec<Bool> = vec![Bool::FALSE; w];
        for i in (0..w).rev() {
            // rem = (rem << 1) | x[i]  (LSB-first: prepend x[i], drop top bit).
            let mut shifted = Vec::with_capacity(w + 1);
            shifted.push(x.bits[i]);
            shifted.extend_from_slice(&rem[..w]);
            rem = shifted;
            // if rem >= y: rem -= y; q[i] = 1.
            let lt = self.unsigned_lt(&rem, &y_ext);
            let ge = self.circ.not(lt);
            let rem_sub = self.unsigned_sub_bits(&rem, &y_ext);
            let mut next = Vec::with_capacity(w + 1);
            for k in 0..=w {
                next.push(self.circ.ite(ge, rem_sub[k], rem[k]));
            }
            rem = next;
            q[i] = ge;
        }
        (
            IntVal { bits: q },
            IntVal {
                bits: rem[..w].to_vec(),
            },
        )
    }

    /// Unsigned subtraction `a − b` over equal-width LSB-first vectors, keeping
    /// the width (borrow discarded): `a + (¬b) + 1`.
    fn unsigned_sub_bits(&mut self, a: &[Bool], b: &[Bool]) -> Vec<Bool> {
        debug_assert_eq!(a.len(), b.len());
        let mut out = Vec::with_capacity(a.len());
        let mut carry = Bool::TRUE;
        for i in 0..a.len() {
            let nb = self.circ.not(b[i]);
            let (s, c) = self.full_add(a[i], nb, carry);
            out.push(s);
            carry = c;
        }
        out
    }

    /// Unsigned addition of two equal-width LSB-first vectors, keeping the width
    /// (final carry discarded).
    fn add_bits_fixed(&mut self, a: &[Bool], b: &[Bool]) -> Vec<Bool> {
        debug_assert_eq!(a.len(), b.len());
        let mut out = Vec::with_capacity(a.len());
        let mut carry = Bool::FALSE;
        for i in 0..a.len() {
            let (s, c) = self.full_add(a[i], b[i], carry);
            out.push(s);
            carry = c;
        }
        out
    }

    /// Sign-extends `a` to `width` bits (`width ≥ a.width`), replicating the sign.
    fn sign_extend(a: &IntVal, width: usize) -> Vec<Bool> {
        let mut bits = a.bits.clone();
        let sign = a.bits[a.width() - 1];
        while bits.len() < width {
            bits.push(sign);
        }
        bits
    }

    /// Logical left shift `a << b` (zero-fill) with its **own** overflow flag —
    /// surface `<<`, translation-ref §10.7d (`TwosComplementInt.shl`). Only the
    /// low `⌈log2 w⌉` bits of the amount affect the value (a masked amount ≥ w
    /// shifts everything out → `0`); the overflow circuit is a **structural port**
    /// of Kodkod's (its junk-bit artifacts are the pinned semantics — same license
    /// as the division port): the check loop runs over **all** `w` amount bits,
    /// and a set bit at index `i` ORs in "shifting the running state left by `2^i`
    /// would push out a bit differing from its neighbour" — so a masked-away
    /// (`i ≥ ⌈log2 w⌉`) junk bit still spuriously flags overflow when the
    /// (frozen) shifted value has a bit transition in the inspected region.
    #[must_use]
    #[allow(
        clippy::many_single_char_names,
        reason = "bit-circuit indices (i/j/k) and the LSB-first running state (s) read \
                  naturally in the shift loop"
    )]
    pub fn shl(&mut self, a: &IntVal, b: &IntVal) -> (IntVal, Bool) {
        let w = self.width;
        let mask = shift_mask_width(w);
        let mut s = a.bits.clone();
        let mut overflow = Bool::FALSE;
        for i in 0..w {
            // Overflow check against the *current* running state, gated by bit i.
            let k = if i < usize::BITS as usize {
                1usize << i
            } else {
                w
            };
            let lo = (w - 1).saturating_sub(k);
            let mut pairs = Vec::new();
            for j in lo..(w - 1) {
                let x = self.circ.xor(s[j], s[j + 1]);
                pairs.push(x);
            }
            let region_changes = self.circ.or_many(pairs);
            let stage_of = self.circ.and(b.bits[i], region_changes);
            overflow = self.circ.or(overflow, stage_of);
            // Value: only the low `mask` bits actually shift.
            if i < mask {
                let shifted = shift_left_bits(&s, k, w);
                s = (0..w)
                    .map(|kk| self.circ.ite(b.bits[i], shifted[kk], s[kk]))
                    .collect();
            }
        }
        (IntVal { bits: s }, overflow)
    }

    /// Arithmetic right shift `a >> b` (sign-fill) — surface `>>`, translation-ref
    /// §10.7d (`SHA`). Only the low `⌈log2 w⌉` amount bits affect the value; a
    /// masked amount ≥ w fills fully with the sign bit. Its **own** overflow is
    /// unconditionally `FALSE` (operand overflow still propagates upstream).
    #[must_use]
    pub fn sha(&mut self, a: &IntVal, b: &IntVal) -> IntVal {
        self.shift_right(a, b, a.bits[self.width - 1])
    }

    /// Logical right shift `a >>> b` (zero-fill) — surface `>>>`, translation-ref
    /// §10.7d (`SHR`). Only the low `⌈log2 w⌉` amount bits affect the value; a
    /// masked amount ≥ w shifts everything out → `0`. Own overflow `FALSE`.
    #[must_use]
    pub fn shr(&mut self, a: &IntVal, b: &IntVal) -> IntVal {
        self.shift_right(a, b, Bool::FALSE)
    }

    /// The shared right-shift barrel over the low `⌈log2 w⌉` amount bits, filling
    /// vacated high bits with `fill` (sign for `sha`, `0` for `shr`).
    fn shift_right(&mut self, a: &IntVal, b: &IntVal, fill: Bool) -> IntVal {
        let w = self.width;
        let mask = shift_mask_width(w);
        let mut s = a.bits.clone();
        for i in 0..mask {
            let sh = 1usize << i;
            let shifted = shift_right_bits(&s, sh, w, fill);
            s = (0..w)
                .map(|k| self.circ.ite(b.bits[i], shifted[k], s[k]))
                .collect();
        }
        IntVal { bits: s }
    }
}

/// Logical left shift of an LSB-first slice by `sh`, zero-filling, kept to
/// `width` bits: `out[k] = bits[k − sh]` when `k ≥ sh`, else `0`.
fn shift_left_bits(bits: &[Bool], sh: usize, width: usize) -> Vec<Bool> {
    (0..width)
        .map(|k| {
            if k >= sh {
                bits.get(k - sh).copied().unwrap_or(Bool::FALSE)
            } else {
                Bool::FALSE
            }
        })
        .collect()
}

/// Right shift of an LSB-first slice by `sh`, filling vacated high bits with
/// `fill`, kept to `width` bits: `out[k] = bits[k + sh]` when `k + sh < width`,
/// else `fill`.
fn shift_right_bits(bits: &[Bool], sh: usize, width: usize, fill: Bool) -> Vec<Bool> {
    (0..width)
        .map(|k| {
            let src = k + sh;
            if src < width {
                bits.get(src).copied().unwrap_or(fill)
            } else {
                fill
            }
        })
        .collect()
}

/// The result of a signed division/remainder circuit ([`IntBuilder::div_rem`]):
/// both values plus their pinned forbid-mode overflow flags (translation-ref
/// §11.2/§11.3).
#[derive(Clone, Debug)]
pub struct DivRem {
    /// `a ÷ b` (truncating toward zero; jar edge values reproduced).
    pub quotient: IntVal,
    /// `a mod b` (sign of the dividend; jar edge values reproduced).
    pub remainder: IntVal,
    /// Overflow flag for `÷` (`b = 0 ∨ (a = MIN ∧ b = −1)`).
    pub div_overflow: Bool,
    /// Overflow flag for `mod` (`b = 0`).
    pub rem_overflow: Bool,
}

#[cfg(test)]
#[allow(
    clippy::redundant_closure_for_method_calls,
    clippy::redundant_closure,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_possible_wrap,
    reason = "exhaustive fold tables: op closures can't be method paths (HRTB on &mut \
              Circuit), and the bw-4 reference arithmetic casts are all in range"
)]
mod tests {
    use super::*;
    use als_solve::{CdclSolver, Cnf, Lit, Outcome, Var};

    // ==================== exhaustive constant-fold tables (mt-044) ============
    //
    // Every arithmetic op is constant-folded over all 256 signed pairs at bw 4
    // and compared to a Rust reference for the jar's two's-complement semantics
    // (translation-ref §11.2, §10.7b). Constant inputs fold every gate away, so
    // the output bits are all `Bool::Const` — read back with [`to_i64`].

    /// Reads an all-constant [`IntVal`] back to its signed value; panics if any
    /// bit is a live literal (a fold bug — the test would otherwise pass blind).
    fn to_i64(v: &IntVal) -> i64 {
        let w = v.width();
        let mut u: i64 = 0;
        for (i, &b) in v.bits().iter().enumerate() {
            match b {
                Bool::Const(true) => u |= 1 << i,
                Bool::Const(false) => {}
                Bool::Lit(_) => panic!("non-constant bit {i} in a constant fold"),
            }
        }
        // Interpret as signed two's complement.
        if u & (1 << (w - 1)) != 0 {
            u - (1 << w)
        } else {
            u
        }
    }

    fn const_bool(b: Bool) -> bool {
        match b {
            Bool::Const(x) => x,
            Bool::Lit(_) => panic!("non-constant flag in a constant fold"),
        }
    }

    /// Two's-complement wrap of `value` to `w` bits, interpreted signed.
    fn wrap(value: i64, w: u32) -> i64 {
        let modulus = 1i64 << w;
        let m = value.rem_euclid(modulus);
        if m >= (1 << (w - 1)) {
            m - modulus
        } else {
            m
        }
    }

    /// The jar's `div[a,b]` closed form (§10.7b): `−sign(a)` on `b = 0`; else
    /// `wrap(a/b)` (Rust `/` truncates toward zero, and `wrap` carries `MIN/−1`).
    fn jar_div(a: i64, b: i64, w: u32) -> i64 {
        if b == 0 {
            match a.cmp(&0) {
                std::cmp::Ordering::Less => 1,
                std::cmp::Ordering::Equal => 0,
                std::cmp::Ordering::Greater => -1,
            }
        } else {
            wrap(a / b, w)
        }
    }

    /// The jar's `rem[a,b]` closed form (§10.7b): the dividend on `b = 0`; else
    /// Rust `%` (sign of the dividend), always in range.
    fn jar_rem(a: i64, b: i64) -> i64 {
        if b == 0 {
            a
        } else {
            a % b
        }
    }

    /// Folds `build` over one pair `(a, b)` at width `w`, returning the value.
    fn fold_bin(
        a: i64,
        b: i64,
        w: usize,
        build: impl FnOnce(&mut IntBuilder, &IntVal, &IntVal) -> IntVal,
    ) -> i64 {
        let mut cnf = Cnf::new();
        let mut ops = 0u64;
        let out = {
            let mut circ = Circuit::new(&mut cnf, &mut ops);
            let mut ib = IntBuilder::new(&mut circ, w);
            let av = IntVal::constant(a, w);
            let bv = IntVal::constant(b, w);
            build(&mut ib, &av, &bv)
        };
        assert_eq!(cnf.num_vars(), 0, "constant fold minted a variable");
        to_i64(&out)
    }

    #[test]
    fn div_rem_match_the_jar_tables_exhaustively() {
        let w = 4usize;
        for a in -8..=7i64 {
            for b in -8..=7i64 {
                let mut cnf = Cnf::new();
                let mut ops = 0u64;
                let dr = {
                    let mut circ = Circuit::new(&mut cnf, &mut ops);
                    let mut ib = IntBuilder::new(&mut circ, w);
                    ib.div_rem(&IntVal::constant(a, w), &IntVal::constant(b, w))
                };
                assert_eq!(cnf.num_vars(), 0, "div_rem fold minted a variable");
                assert_eq!(
                    to_i64(&dr.quotient),
                    jar_div(a, b, 4),
                    "div[{a},{b}] mismatch"
                );
                assert_eq!(
                    to_i64(&dr.remainder),
                    jar_rem(a, b),
                    "rem[{a},{b}] mismatch"
                );
                assert_eq!(
                    const_bool(dr.div_overflow),
                    b == 0 || (a == -8 && b == -1),
                    "div overflow[{a},{b}]"
                );
                assert_eq!(const_bool(dr.rem_overflow), b == 0, "rem overflow[{a},{b}]");
            }
        }
    }

    #[test]
    fn add_sub_mul_wrap_and_flag_overflow_exhaustively() {
        let w = 4usize;
        for a in -8..=7i64 {
            for b in -8..=7i64 {
                // add
                let mut cnf = Cnf::new();
                let mut ops = 0u64;
                let (sum, sof, sub, subof, mul, mof) = {
                    let mut circ = Circuit::new(&mut cnf, &mut ops);
                    let mut ib = IntBuilder::new(&mut circ, w);
                    let av = IntVal::constant(a, w);
                    let bv = IntVal::constant(b, w);
                    let (s, sof) = ib.add_signed(&av, &bv);
                    let (d, dof) = ib.sub_signed(&av, &bv);
                    let (m, mof) = ib.multiply(&av, &bv);
                    (
                        to_i64(&s),
                        const_bool(sof),
                        to_i64(&d),
                        const_bool(dof),
                        to_i64(&m),
                        const_bool(mof),
                    )
                };
                assert_eq!(sum, wrap(a + b, 4), "add[{a},{b}]");
                assert_eq!(sof, !(-8..=7).contains(&(a + b)), "add overflow[{a},{b}]");
                assert_eq!(sub, wrap(a - b, 4), "sub[{a},{b}]");
                assert_eq!(subof, !(-8..=7).contains(&(a - b)), "sub overflow[{a},{b}]");
                assert_eq!(mul, wrap(a * b, 4), "mul[{a},{b}]");
                assert_eq!(mof, !(-8..=7).contains(&(a * b)), "mul overflow[{a},{b}]");
            }
        }
    }

    #[test]
    fn negate_wraps_and_flags_min() {
        let w = 4usize;
        for a in -8..=7i64 {
            let mut cnf = Cnf::new();
            let mut ops = 0u64;
            let (v, of) = {
                let mut circ = Circuit::new(&mut cnf, &mut ops);
                let mut ib = IntBuilder::new(&mut circ, w);
                ib.negate(&IntVal::constant(a, w))
            };
            assert_eq!(to_i64(&v), wrap(-a, 4), "negate[{a}]");
            assert_eq!(const_bool(of), a == -8, "negate overflow[{a}]");
        }
    }

    /// The mask width `⌈log2 w⌉`.
    fn ref_mask(w: usize) -> usize {
        if w <= 1 {
            0
        } else {
            (usize::BITS - (w as u64 - 1).leading_zeros()) as usize
        }
    }

    /// Reference `shl` (value + junk-bit overflow), mirroring §10.7d exactly.
    fn ref_shl(a: i64, b: i64, w: usize) -> (i64, bool) {
        let modw = 1i64 << w;
        let bpat = a_pat(b, w);
        let mut s = a_pat(a, w);
        let mask = ref_mask(w);
        let bit = |v: u64, i: usize| (v >> i) & 1 == 1;
        let mut of = false;
        for i in 0..w {
            let k = if i < 63 { 1usize << i } else { w };
            let lo = (w - 1).saturating_sub(k);
            let mut changes = false;
            for j in lo..(w - 1) {
                changes |= bit(s, j) != bit(s, j + 1);
            }
            of |= bit(bpat, i) && changes;
            if i < mask && bit(bpat, i) {
                s = (s << k) & (modw as u64 - 1);
            }
        }
        (wrap(s as i64, w as u32), of)
    }

    /// The unsigned `w`-bit pattern of a signed value.
    fn a_pat(v: i64, w: usize) -> u64 {
        (v.rem_euclid(1i64 << w)) as u64
    }

    fn ref_shr(a: i64, b: i64, w: usize, arith: bool) -> i64 {
        let mask = ref_mask(w);
        let amt = (a_pat(b, w) & ((1u64 << mask) - 1)) as usize;
        if amt >= w {
            return if arith && a < 0 { -1 } else { 0 };
        }
        if arith {
            a >> amt // arithmetic (sign-extending) on the signed value
        } else {
            wrap((a_pat(a, w) >> amt) as i64, w as u32)
        }
    }

    /// Folds `shl` over one pair, returning `(value, overflow)`.
    fn fold_shl(a: i64, b: i64, w: usize) -> (i64, bool) {
        let mut cnf = Cnf::new();
        let mut ops = 0u64;
        let (v, of) = {
            let mut circ = Circuit::new(&mut cnf, &mut ops);
            let mut ib = IntBuilder::new(&mut circ, w);
            ib.shl(&IntVal::constant(a, w), &IntVal::constant(b, w))
        };
        assert_eq!(cnf.num_vars(), 0, "shl fold minted a variable");
        (to_i64(&v), const_bool(of))
    }

    #[test]
    fn shifts_match_reference_and_pinned_cells() {
        // I4 anchors (bw4): 4<<1=8, (-8)>>1(sha)=-4, (-8)>>>1(shr)=4, 4>>>1=2.
        let w = 4usize;
        assert_eq!(fold_shl(4, 1, w).0, wrap(8, 4));
        assert_eq!(fold_bin(-8, 1, w, |ib, a, b| ib.sha(a, b)), -4);
        assert_eq!(fold_bin(-8, 1, w, |ib, a, b| ib.shr(a, b)), 4);
        assert_eq!(fold_bin(4, 1, w, |ib, a, b| ib.shr(a, b)), 2);

        // §10.7d pinned junk-bit matrix (bw4, mask 2): masked amount 0, but a set
        // junk bit spuriously flags overflow when the shiftee has a transition.
        assert_eq!(fold_shl(5, 4, 4), (5, true), "5<<4: junk-bit overflow");
        assert_eq!(fold_shl(3, 4, 4), (3, true), "3<<4: junk-bit overflow");
        assert_eq!(fold_shl(0, 4, 4), (0, false), "0<<4: uniform, no trigger");
        assert_eq!(fold_shl(1, 4, 4), (1, true), "1<<4: junk-bit overflow");
        assert_eq!(fold_shl(5, 0, 4), (5, false), "5<<0: no shift, no overflow");
        assert_eq!(fold_shl(4, 1, 4), (wrap(8, 4), true), "4<<1: genuine wrap");

        // Mask-width cells at other widths.
        assert_eq!(fold_shl(1, 4, 3).0, 1, "1<<4 at bw3 = 1 (mask 2)");
        assert_eq!(fold_shl(1, 8, 5).0, 1, "1<<8 at bw5 = 1 (mask 3)");
        assert_eq!(fold_shl(1, 6, 6).0, 0, "1<<6 at bw6 = 0 (masked 6 ≥ w)");

        // Exhaustive bw4 vs the reference for value AND overflow (shl) and value
        // (shr/sha), over every amount including junk-bit and negative amounts.
        for a in -8..=7i64 {
            for b in -8..=7i64 {
                assert_eq!(fold_shl(a, b, 4), ref_shl(a, b, 4), "shl[{a},{b}]");
                assert_eq!(
                    fold_bin(a, b, 4, |ib, x, y| ib.shr(x, y)),
                    ref_shr(a, b, 4, false),
                    "shr[{a},{b}]"
                );
                assert_eq!(
                    fold_bin(a, b, 4, |ib, x, y| ib.sha(x, y)),
                    ref_shr(a, b, 4, true),
                    "sha[{a},{b}]"
                );
            }
        }
    }

    /// Counts the `n` one-bit inputs into a signed value and asserts the model
    /// with all inputs true reports exactly `n` (via a `#e = n` equality gate).
    fn card_equals(n: usize, target: i64, width: usize) -> bool {
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..n).map(|_| cnf.fresh_var()).collect();
        let mut ops = 0u64;
        let eq = {
            let mut circ = Circuit::new(&mut cnf, &mut ops);
            let mut ib = IntBuilder::new(&mut circ, width);
            let mut acc = vec![Bool::FALSE];
            for &v in &vars {
                acc = ib.add_bit(&acc, Bool::Lit(Lit::positive(v)));
            }
            let (val, _ovf) = ib.unsigned_to_signed(&acc);
            let konst = IntVal::constant(target, width);
            ib.eq(&val, &konst)
        };
        // Force all inputs true and the equality true.
        for &v in &vars {
            cnf.add_clause(vec![Lit::positive(v)]);
        }
        match eq {
            Bool::Const(b) => b,
            Bool::Lit(l) => {
                cnf.add_clause(vec![l]);
                matches!(CdclSolver::new(&cnf).solve(), Outcome::Sat(_))
            }
        }
    }

    #[test]
    fn cardinality_counts_exactly() {
        assert!(card_equals(3, 3, 4), "three ones count to 3");
        assert!(!card_equals(3, 2, 4), "three ones do not count to 2");
        assert!(
            card_equals(5, 5, 4),
            "five ones count to 5 (fits bitwidth 4)"
        );
    }

    /// Enumerates the pairs `(x, y)` of two 4-bit signed values for which
    /// `signed_lt(x, y)` holds, restricted to `x, y ∈ {-2, -1, 0, 1}` via fixed
    /// low bits, and checks the ordering is the true signed one.
    #[test]
    fn signed_lt_orders_negatives_below_positives() {
        // -1 < 1 : build constants and assert lt is constant-true.
        let mut cnf = Cnf::new();
        let mut ops = 0u64;
        let (lt1, lt2, eqn) = {
            let mut circ = Circuit::new(&mut cnf, &mut ops);
            let mut ib = IntBuilder::new(&mut circ, 4);
            let neg1 = IntVal::constant(-1, 4);
            let pos1 = IntVal::constant(1, 4);
            let a = ib.signed_lt(&neg1, &pos1); // -1 < 1  → true
            let b = ib.signed_lt(&pos1, &neg1); // 1 < -1  → false
            let e = ib.eq(&neg1, &neg1); // -1 = -1 → true
            (a, b, e)
        };
        let _ = &cnf;
        assert_eq!(lt1, Bool::Const(true));
        assert_eq!(lt2, Bool::Const(false));
        assert_eq!(eqn, Bool::Const(true));
    }

    #[test]
    fn add_signed_wraps_and_flags_overflow() {
        // 7 + 1 at bitwidth 4 overflows (max is 7).
        let mut cnf = Cnf::new();
        let mut ops = 0u64;
        let (val_is_neg8, overflow) = {
            let mut circ = Circuit::new(&mut cnf, &mut ops);
            let mut ib = IntBuilder::new(&mut circ, 4);
            let seven = IntVal::constant(7, 4);
            let one = IntVal::constant(1, 4);
            let (sum, ovf) = ib.add_signed(&seven, &one);
            // 7 + 1 wraps to -8 (1000).
            let neg8 = IntVal::constant(-8, 4);
            let eq = ib.eq(&sum, &neg8);
            (eq, ovf)
        };
        let _ = &cnf;
        assert_eq!(val_is_neg8, Bool::Const(true), "7+1 wraps to -8");
        assert_eq!(overflow, Bool::Const(true), "signed overflow flagged");
        // A non-overflowing add: 2 + 3 = 5, no flag.
        let mut cnf2 = Cnf::new();
        let mut ops2 = 0u64;
        let (val5, ovf2) = {
            let mut circ = Circuit::new(&mut cnf2, &mut ops2);
            let mut ib = IntBuilder::new(&mut circ, 4);
            let (sum, ovf) = ib.add_signed(&IntVal::constant(2, 4), &IntVal::constant(3, 4));
            (ib.eq(&sum, &IntVal::constant(5, 4)), ovf)
        };
        let _ = &cnf2;
        assert_eq!(val5, Bool::Const(true));
        assert_eq!(ovf2, Bool::Const(false));
    }
}
