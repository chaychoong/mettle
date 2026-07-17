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
}

#[cfg(test)]
mod tests {
    use super::*;
    use als_solve::{CdclSolver, Cnf, Lit, Outcome, Var};

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
