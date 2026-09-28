//! Bounded binary integers over characteristic-two fields.
//!
//! Bits are low-first and Boolean. Widths are circuit-shape constants, at most
//! 64; arithmetic is modulo `2^width`, with discarded information returned
//! separately. Selectors must be checked Boolean masks supplied by the caller.

use crate::{Error, context::Context};

#[derive(Clone)]
pub(crate) struct Uint<F> {
    bits: Vec<F>,
}

impl<F: Copy> Uint<F> {
    pub(crate) fn constant<C: Context<F = F>>(ctx: &C, value: u64, width: usize) -> Self {
        assert!(width <= 64, "integer width exceeds 64");
        assert!(width == 64 || value >> width == 0, "integer constant exceeds width");
        Self {
            bits: (0..width).map(|i| ctx.base((value >> i) & 1)).collect(),
        }
    }

    pub(crate) fn from_field<C: Context<F = F>>(ctx: &C, value: F, width: usize) -> Result<Self, Error> {
        if width > 64 {
            return Err(Error::InvalidInput);
        }
        Ok(Self {
            bits: ctx.bits(value, width)?,
        })
    }

    pub(crate) fn from_bits<C: Context<F = F>>(ctx: &C, bits: Vec<F>) -> Result<Self, Error> {
        if bits.len() > 64 {
            return Err(Error::InvalidInput);
        }
        for &bit in &bits {
            ctx.assert_bool(bit)?;
        }
        Ok(Self { bits })
    }

    pub(crate) fn bits(&self) -> &[F] {
        &self.bits
    }

    pub(crate) fn width(&self) -> usize {
        self.bits.len()
    }

    pub(crate) fn value<C: Context<F = F>>(&self, ctx: &C) -> F {
        self.bits.iter().enumerate().fold(ctx.zero(), |value, (i, &bit)| {
            ctx.add(value, ctx.mul(bit, ctx.base(1u64 << i)))
        })
    }

    pub(crate) fn add<C: Context<F = F>>(&self, ctx: &C, rhs: &Self) -> (Self, F) {
        assert_eq!(self.width(), rhs.width(), "integer widths differ");
        let mut carry = ctx.zero();
        let mut bits = Vec::with_capacity(self.width());
        for (&a, &b) in self.bits.iter().zip(&rhs.bits) {
            let parity = ctx.add(a, b);
            bits.push(ctx.add(parity, carry));
            // The two carry terms are mutually exclusive for Boolean inputs.
            carry = ctx.add(ctx.mul(a, b), ctx.mul(parity, carry));
        }
        (Self { bits }, carry)
    }

    pub(crate) fn sub<C: Context<F = F>>(&self, ctx: &C, rhs: &Self) -> (Self, F) {
        assert_eq!(self.width(), rhs.width(), "integer widths differ");
        let mut borrow = ctx.zero();
        let mut bits = Vec::with_capacity(self.width());
        for (&a, &b) in self.bits.iter().zip(&rhs.bits) {
            let parity = ctx.add(a, b);
            bits.push(ctx.add(parity, borrow));
            borrow = ctx.add(ctx.mul(ctx.not(a), b), ctx.mul(ctx.not(parity), borrow));
        }
        (Self { bits }, borrow)
    }

    pub(crate) fn lt<C: Context<F = F>>(&self, ctx: &C, rhs: &Self) -> F {
        assert_eq!(self.width(), rhs.width(), "integer widths differ");
        self.bits.iter().zip(&rhs.bits).fold(ctx.zero(), |borrow, (&a, &b)| {
            ctx.add(ctx.mul(ctx.not(a), b), ctx.mul(ctx.not(ctx.add(a, b)), borrow))
        })
    }

    pub(crate) fn eq_const<C: Context<F = F>>(&self, ctx: &C, value: u64) -> F {
        if self.width() < 64 && value >> self.width() != 0 {
            return ctx.zero();
        }
        self.bits.iter().enumerate().fold(ctx.one(), |equal, (i, &bit)| {
            ctx.mul(equal, if value >> i & 1 == 1 { bit } else { ctx.not(bit) })
        })
    }

    pub(crate) fn select<C: Context<F = F>>(ctx: &C, enabled: F, yes: &Self, no: &Self) -> Self {
        assert_eq!(yes.width(), no.width(), "integer widths differ");
        Self {
            bits: yes
                .bits
                .iter()
                .zip(&no.bits)
                .map(|(&a, &b)| ctx.select(enabled, a, b))
                .collect(),
        }
    }

    fn any<C: Context<F = F>>(ctx: &C, bits: &[F]) -> F {
        bits.iter().fold(ctx.zero(), |any, &bit| ctx.or(any, bit))
    }

    pub(crate) fn shl<C: Context<F = F>>(&self, ctx: &C, amount: &Self) -> (Self, F) {
        if self.width() == 0 || amount.width() == 0 {
            return (self.clone(), ctx.zero());
        }
        let mut value = self.clone();
        let mut overflow = ctx.zero();
        // The width determines the barrel's shape. At most six stages are
        // needed, so host shifts remain safe even with a 64-bit amount.
        let stages = amount
            .width()
            .min((usize::BITS - (self.width() - 1).leading_zeros()) as usize);
        for (i, &enabled) in amount.bits[..stages].iter().enumerate() {
            let shift = 1usize << i;
            let lost = Self::any(ctx, &value.bits[self.width() - shift..]);
            overflow = ctx.or(overflow, ctx.mul(enabled, lost));
            for j in (0..self.width()).rev() {
                let shifted = if j >= shift { value.bits[j - shift] } else { ctx.zero() };
                value.bits[j] = ctx.select(enabled, shifted, value.bits[j]);
            }
        }
        if stages < amount.width() {
            // Any higher amount bit clears the result, without erasing loss
            // already accumulated by the preceding stages.
            let high = Self::any(ctx, &amount.bits[stages..]);
            overflow = ctx.or(overflow, ctx.mul(high, Self::any(ctx, &value.bits)));
            let keep = ctx.not(high);
            for bit in &mut value.bits {
                *bit = ctx.mul(keep, *bit);
            }
        }
        (value, overflow)
    }

    pub(crate) fn shr<C: Context<F = F>>(&self, ctx: &C, amount: &Self) -> Self {
        if self.width() == 0 || amount.width() == 0 {
            return self.clone();
        }
        let mut value = self.clone();
        let stages = amount
            .width()
            .min((usize::BITS - (self.width() - 1).leading_zeros()) as usize);
        for (i, &enabled) in amount.bits[..stages].iter().enumerate() {
            let shift = 1usize << i;
            for j in 0..self.width() {
                let shifted = if j + shift < self.width() {
                    value.bits[j + shift]
                } else {
                    ctx.zero()
                };
                value.bits[j] = ctx.select(enabled, shifted, value.bits[j]);
            }
        }
        if stages < amount.width() {
            let keep = ctx.not(Self::any(ctx, &amount.bits[stages..]));
            for bit in &mut value.bits {
                *bit = ctx.mul(keep, *bit);
            }
        }
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::Witness;
    use leanvm_guest::Field;

    fn check(ctx: &Witness<'_>, value: &Uint<Field>, expected: u64) {
        assert_eq!(value.value(ctx), Field::from(expected));
    }

    #[test]
    fn bounded_inputs_reject_truncation_and_non_boolean_bits() {
        let ctx = Witness::new(&[], vec![]);
        assert!(Uint::from_field(&ctx, Field::from(16), 4).is_err());
        assert!(Uint::from_field(&ctx, Field::ONE, 0).is_err());
        assert!(Uint::from_field(&ctx, Field::new(0, 1, 0), 64).is_err());
        assert!(Uint::from_bits(&ctx, vec![Field::from(2)]).is_err());
        assert!(Uint::from_bits(&ctx, vec![Field::ZERO; 65]).is_err());
        check(&ctx, &Uint::from_field(&ctx, Field::ZERO, 0).unwrap(), 0);
        check(
            &ctx,
            &Uint::from_field(&ctx, Field::from(u64::MAX), 64).unwrap(),
            u64::MAX,
        );
        check(
            &ctx,
            &Uint::from_bits(&ctx, vec![Field::ONE, Field::ZERO, Field::ONE]).unwrap(),
            5,
        );
    }

    #[test]
    fn arithmetic_tracks_carries_borrows_and_unsigned_order() {
        let ctx = Witness::new(&[], vec![]);
        for width in [0, 1, 4, 63, 64] {
            let modulus = 1u128 << width;
            let mask = (modulus - 1) as u64;
            let mut values = vec![0, mask / 2, mask / 2 + u64::from(width != 0), mask];
            values.sort_unstable();
            values.dedup();
            for &a in &values {
                for &b in &values {
                    let lhs = Uint::constant(&ctx, a, width);
                    let rhs = Uint::constant(&ctx, b, width);
                    let (sum, carry) = lhs.add(&ctx, &rhs);
                    check(&ctx, &sum, a.wrapping_add(b) & mask);
                    assert_eq!(carry, Field::from(u64::from(a as u128 + b as u128 >= modulus)));
                    let (difference, borrow) = lhs.sub(&ctx, &rhs);
                    check(&ctx, &difference, a.wrapping_sub(b) & mask);
                    assert_eq!(borrow, Field::from(u64::from(a < b)));
                    assert_eq!(lhs.lt(&ctx, &rhs), borrow);
                    assert_eq!(lhs.eq_const(&ctx, b), Field::from(u64::from(a == b)));
                    check(
                        &ctx,
                        &Uint::select(&ctx, carry, &lhs, &rhs),
                        if a as u128 + b as u128 >= modulus { a } else { b },
                    );
                }
            }
            if width < 64 {
                assert_eq!(
                    Uint::constant(&ctx, 0, width).eq_const(&ctx, modulus as u64),
                    Field::ZERO
                );
            }
        }
    }

    #[test]
    fn barrel_shifts_saturate_and_preserve_earlier_lost_bits() {
        let ctx = Witness::new(&[], vec![]);
        // Width three also exercises a combined shift >= width without an
        // individually saturating stage. Bit 63 must never mask a host shift.
        for (width, input, shift) in [
            (0, 0, u64::MAX),
            (1, 1, 0),
            (1, 1, 1),
            (3, 5, 3),
            (4, 8, 3),
            (4, 1, 3),
            (4, 1, 4),
            (4, 0, u64::MAX),
            (64, 1, 63),
            (64, 1u64 << 63, 1),
            (64, u64::MAX, 64),
            (64, 1, 1u64 << 63),
            (64, u64::MAX, 0),
        ] {
            let input_uint = Uint::constant(&ctx, input, width);
            let amount = Uint::constant(&ctx, shift, 64);
            let mask = ((1u128 << width) - 1) as u64;
            let expected_left = if shift >= 64 { 0 } else { (input << shift) & mask };
            let expected_right = if shift >= 64 { 0 } else { input >> shift };
            let expected_overflow = if shift == 0 {
                false
            } else if shift >= width as u64 {
                input != 0
            } else {
                input >> (width as u64 - shift) != 0
            };
            let (left, overflow) = input_uint.shl(&ctx, &amount);
            check(&ctx, &left, expected_left);
            check(&ctx, &input_uint.shr(&ctx, &amount), expected_right);
            assert_eq!(overflow, Field::from(u64::from(expected_overflow)));
        }
        let input = Uint::constant(&ctx, u64::MAX, 64);
        let empty_amount = Uint::constant(&ctx, 0, 0);
        let (left, overflow) = input.shl(&ctx, &empty_amount);
        check(&ctx, &left, u64::MAX);
        check(&ctx, &input.shr(&ctx, &empty_amount), u64::MAX);
        assert_eq!(overflow, Field::ZERO);
    }

    #[test]
    #[should_panic(expected = "integer constant exceeds width")]
    fn constants_cannot_silently_truncate() {
        Uint::constant(&Witness::new(&[], vec![]), 1, 0);
    }
}
