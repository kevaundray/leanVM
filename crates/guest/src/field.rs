//! `F192 = GF(2^64)[y]/(y^3+y+1)`, with base modulus `x^64+x^4+x^3+x+1`.
//! Limbs are the coefficients of 1, y and y², not a polynomial's 192 raw bits.

use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul, MulAssign, Neg, Sub, SubAssign};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct Field(pub [u64; 3]);

impl Field {
    pub const ZERO: Self = Self([0, 0, 0]);
    pub const ONE: Self = Self([1, 0, 0]);
    pub const Y: Self = Self([0, 1, 0]);

    pub const fn new(c0: u64, c1: u64, c2: u64) -> Self {
        Self([c0, c1, c2])
    }

    pub const fn is_zero(self) -> bool {
        self.0[0] == 0 && self.0[1] == 0 && self.0[2] == 0
    }

    pub fn from_le_bytes(bytes: [u8; 24]) -> Self {
        Self(core::array::from_fn(|i| {
            u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap())
        }))
    }

    pub fn to_le_bytes(self) -> [u8; 24] {
        let mut bytes = [0; 24];
        for (chunk, limb) in bytes.chunks_exact_mut(8).zip(self.0) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        bytes
    }

    #[inline]
    pub fn square(self) -> Self {
        self * self
    }

    /// Multiply by the base-field generator x, reducing x^64 = x^4+x^3+x+1.
    #[inline]
    pub fn mul_base_generator(self) -> Self {
        Self(self.0.map(|limb| (limb << 1) ^ (0x1b & 0u64.wrapping_sub(limb >> 63))))
    }

    /// The 2^64-power Frobenius automorphism fixes the base field.
    pub const fn frobenius(self) -> Self {
        Self([self.0[0], self.0[2], self.0[1] ^ self.0[2]])
    }

    pub fn pow(self, mut exponent: u64) -> Self {
        let mut base = self;
        let mut result = Self::ONE;
        while exponent != 0 {
            if exponent & 1 != 0 {
                result *= base;
            }
            exponent >>= 1;
            if exponent != 0 {
                base = base.square();
            }
        }
        result
    }

    /// Exponentiation by an unsigned 192-bit integer, least-significant limb
    /// first. As usual, x^0 = 1, including when x = 0.
    pub fn pow_words(self, exponent: [u64; 3]) -> Self {
        let mut result = Self::ONE;
        let Some(high) = exponent.iter().rposition(|&word| word != 0) else {
            return result;
        };
        let bits = high * 64 + (64 - exponent[high].leading_zeros() as usize);
        let mut base = self;
        for bit in 0..bits {
            if (exponent[bit / 64] >> (bit % 64)) & 1 != 0 {
                result *= base;
            }
            if bit + 1 != bits {
                base = base.square();
            }
        }
        result
    }

    /// Multiplicative inverse, or `None` for zero. The norm reduces inversion
    /// to GF(2^64); an Itoh–Tsujii chain uses 63 squares and 10 multiplies there.
    pub fn inverse(self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        let conjugate = self.frobenius();
        let product = conjugate * conjugate.frobenius();
        let norm = self * product;
        let square_n = |mut value: Self, count| {
            for _ in 0..count {
                value = value.square();
            }
            value
        };
        let t1 = norm;
        let t2 = square_n(t1, 1) * t1;
        let t3 = square_n(t2, 1) * t1;
        let t6 = square_n(t3, 3) * t3;
        let t7 = square_n(t6, 1) * t1;
        let t14 = square_n(t7, 7) * t7;
        let t15 = square_n(t14, 1) * t1;
        let t30 = square_n(t15, 15) * t15;
        let t31 = square_n(t30, 1) * t1;
        let t62 = square_n(t31, 31) * t31;
        let t63 = square_n(t62, 1) * t1;
        Some(product * t63.square())
    }
}

/// Multiply through a proof-checked guest ECALL or the selected host field kernel.
#[inline]
pub fn field_mul(lhs: Field, rhs: Field) -> Field {
    #[cfg(all(feature = "native", not(target_arch = "riscv64")))]
    {
        use primitives::field::F192;
        let product = F192::new(lhs.0[0], lhs.0[1], lhs.0[2]) * F192::new(rhs.0[0], rhs.0[1], rhs.0[2]);
        Field([product.c0, product.c1, product.c2])
    }
    #[cfg(target_arch = "riscv64")]
    {
        if lhs.is_zero() || rhs.is_zero() {
            return Field::ZERO;
        }
        if lhs == Field::ONE {
            return rhs;
        }
        if rhs == Field::ONE {
            return lhs;
        }
        let (c0, c1, c2);
        // SAFETY: this pure ECALL consumes and returns only integer registers.
        unsafe {
            core::arch::asm!(
                "ecall",
                in("a7") crate::ECALL_F192_MUL,
                inlateout("a0") lhs.0[0] => c0,
                inlateout("a1") lhs.0[1] => c1,
                inlateout("a2") lhs.0[2] => c2,
                in("a3") rhs.0[0],
                in("a4") rhs.0[1],
                in("a5") rhs.0[2],
                options(pure, nomem, nostack),
            );
        }
        Field([c0, c1, c2])
    }
    #[cfg(all(not(feature = "native"), not(target_arch = "riscv64")))]
    {
        // Six base products via Karatsuba, then y³ = y+1 and y⁴ = y²+y.
        let [a0, a1, a2] = lhs.0;
        let [b0, b1, b2] = rhs.0;
        let p0 = base_mul(a0, b0);
        let p1 = base_mul(a1, b1);
        let p2 = base_mul(a2, b2);
        let c1 = base_mul(a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
        let c2 = base_mul(a0 ^ a2, b0 ^ b2) ^ p0 ^ p2 ^ p1;
        let c3 = base_mul(a1 ^ a2, b1 ^ b2) ^ p1 ^ p2;
        Field([p0 ^ c3, c1 ^ c3 ^ p2, c2 ^ p2])
    }
}

#[cfg(all(not(feature = "native"), not(target_arch = "riscv64")))]
fn base_mul(mut lhs: u64, mut rhs: u64) -> u64 {
    let mut product = 0;
    for _ in 0..64 {
        product ^= lhs & 0u64.wrapping_sub(rhs & 1);
        let carry = lhs >> 63;
        lhs = (lhs << 1) ^ (0x1b & 0u64.wrapping_sub(carry));
        rhs >>= 1;
    }
    product
}

impl From<u64> for Field {
    fn from(value: u64) -> Self {
        Self([value, 0, 0])
    }
}

impl BitXor for Field {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self {
        Self([self.0[0] ^ rhs.0[0], self.0[1] ^ rhs.0[1], self.0[2] ^ rhs.0[2]])
    }
}
impl BitXorAssign for Field {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}
#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for Field {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        self ^ rhs
    }
}
#[allow(clippy::suspicious_op_assign_impl)]
impl AddAssign for Field {
    fn add_assign(&mut self, rhs: Self) {
        *self ^= rhs;
    }
}
#[allow(clippy::suspicious_arithmetic_impl)]
impl Sub for Field {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        self ^ rhs
    }
}
#[allow(clippy::suspicious_op_assign_impl)]
impl SubAssign for Field {
    fn sub_assign(&mut self, rhs: Self) {
        *self ^= rhs;
    }
}
impl Neg for Field {
    type Output = Self;
    fn neg(self) -> Self {
        self
    }
}
impl Mul for Field {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        field_mul(self, rhs)
    }
}
impl MulAssign for Field {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

#[cfg(test)]
mod tests {
    use super::Field;

    #[test]
    fn defining_polynomials_reduce_at_both_tower_boundaries() {
        assert_eq!(Field::from(1 << 63) * Field::from(2), Field::from(0x1b));
        assert_eq!(Field::Y.pow(3), Field::Y + Field::ONE);
        assert_eq!(Field::Y.pow(4), Field::Y.square() + Field::Y);
        assert_eq!(Field::Y.pow_words([0, 1, 0]), Field::Y.square());
        for value in [Field::ZERO, Field::ONE, Field([u64::MAX; 3]), Field([1 << 63, 7, 19])] {
            assert_eq!(value.mul_base_generator(), value * Field::from(2));
        }
    }

    #[test]
    fn inversion_rejects_zero_and_handles_dense_coefficients() {
        assert_eq!(Field::ZERO.inverse(), None);
        for value in [Field::ONE, Field::Y, Field([u64::MAX; 3]), Field([1 << 63, 7, 19])] {
            assert_eq!(value * value.inverse().unwrap(), Field::ONE);
            assert_eq!(value.pow_words([u64::MAX; 3]), Field::ONE);
        }
    }
}
