//! The base field `K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`.
//!
//! The executable functions are the portable paths of `crates/primitives/src/field/gf2_64.rs`, copied
//! with the same bodies; `tests/equivalence.rs` checks the two agree.
//!
//! Specification: an element is a polynomial over GF(2) of degree below 64, bit `i` its coefficient of
//! `x^i`. The product [`k_mul`] is the carry-less product ([`clmul`]) reduced modulo
//! `M = x^64 + x^4 + x^3 + x + 1`, where "reduced" is the definition of a remainder ([`is_remainder`]).
use crate::clmul::*;
use core::ops::{Add, AddAssign, Mul, MulAssign};
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// The modulus `M = x^64 + x^4 + x^3 + x + 1`, as a 65-bit polynomial.
pub open spec fn modulus() -> u128 {
    0x1_0000_0000_0000_001Bu128
}

/// `r` is the remainder of `p` modulo `M`: `p = q * M + r` for some polynomial `q`, and `deg r < 64`.
///
/// A `p` of degree below 128 has a quotient of degree below 64, so `q: u64` loses nothing.
pub open spec fn is_remainder(p: u128, r: u64) -> bool {
    exists|q: u64| p == clmul(q, modulus()) ^ (r as u128)
}

/// `p mod M`, the unique remainder (unique by [`lemma_remainder_unique`]).
pub open spec fn k_mod(p: u128) -> u64 {
    choose|r: u64| is_remainder(p, r)
}

/// The product in `K`: `a * b mod M`.
pub open spec fn k_mul(a: u64, b: u64) -> u64 {
    k_mod(clmul(a, b as u128))
}

/// `a^n` in `K`.
pub open spec fn k_pow(a: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        1
    } else {
        k_mul(k_pow(a, (n - 1) as nat), a)
    }
}

/// `a` squared `n` times, `a^(2^n)` by [`lemma_k_sq_iter_pow`].
pub open spec fn k_sq_iter(a: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        a
    } else {
        let v = k_sq_iter(a, (n - 1) as nat);
        k_mul(v, v)
    }
}

// ---------------------------------------------------------------------------------------------
// The reduction
// ---------------------------------------------------------------------------------------------
/// The closed form of the production `reduce`, as a spec function.
pub open spec fn reduce_formula(p: u128) -> u64 {
    let (lo, hi) = (p as u64, (p >> 64u128) as u64);
    let spill = (hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64);
    let v = hi ^ spill;
    lo ^ v ^ (v << 1u64) ^ (v << 3u64) ^ (v << 4u64)
}

/// Multiplication by `x` in `K`: shift, and fold `x^64` back as `x^4 + x^3 + x + 1`.
pub open spec fn mulx(a: u64) -> u64 {
    (a << 1u64) ^ (if a >> 63u64 == 1 {
        0x1Bu64
    } else {
        0u64
    })
}

/// `a * x^k` in `K`.
pub open spec fn mulx_pow(a: u64, k: nat) -> u64
    decreases k,
{
    if k == 0 {
        a
    } else {
        mulx(mulx_pow(a, (k - 1) as nat))
    }
}

/// `q * (x^4 + x^3 + x + 1) = q ^ q<<1 ^ q<<3 ^ q<<4`, the product by the reduction constant `0x1B`.
pub open spec fn times_r64(q: u64) -> u128 {
    let w = q as u128;
    w ^ (w << 1u128) ^ (w << 3u128) ^ (w << 4u128)
}

pub proof fn lemma_clmul_r64(q: u64)
    ensures
        clmul(q, 0x1Bu128) == times_r64(q),
{
    assert(0x1Bu128 == (1u128 << 0u128) ^ (1u128 << 1u128) ^ (1u128 << 3u128) ^ (1u128 << 4u128))
        by (bit_vector);
    let (e0, e1, e3, e4) = (1u128 << 0u128, 1u128 << 1u128, 1u128 << 3u128, 1u128 << 4u128);
    lemma_clmul_xor_right(q, e0 ^ e1 ^ e3, e4);
    lemma_clmul_xor_right(q, e0 ^ e1, e3);
    lemma_clmul_xor_right(q, e0, e1);
    lemma_clmul_monomial(q, 0);
    lemma_clmul_monomial(q, 1);
    lemma_clmul_monomial(q, 3);
    lemma_clmul_monomial(q, 4);
    let w = q as u128;
    assert(w << 0u128 == w) by (bit_vector);
}

/// `q * M = q x^64 + q * 0x1B`.
pub proof fn lemma_clmul_modulus(q: u64)
    ensures
        clmul(q, modulus()) == ((q as u128) << 64u128) ^ times_r64(q),
{
    assert(modulus() == 0x1Bu128 ^ (1u128 << 64u128)) by (bit_vector);
    lemma_clmul_xor_right(q, 0x1Bu128, 1u128 << 64u128);
    lemma_clmul_r64(q);
    lemma_clmul_monomial(q, 64);
    let (a, b) = (times_r64(q), (q as u128) << 64u128);
    assert(a ^ b == b ^ a) by (bit_vector);
}

/// The production reduction returns a remainder of `p` modulo `M`, with quotient `hi ^ spill`.
pub proof fn lemma_reduce_formula_is_remainder(p: u128)
    ensures
        is_remainder(p, reduce_formula(p)),
{
    let hi = (p >> 64u128) as u64;
    let q = hi ^ ((hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64));
    lemma_clmul_modulus(q);
    assert({
        let hi = (p >> 64u128) as u64;
        let q = hi ^ ((hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64));
        let w = q as u128;
        p == ((w << 64u128) ^ (w ^ (w << 1u128) ^ (w << 3u128) ^ (w << 4u128))) ^ (reduce_formula(p) as u128)
    }) by (bit_vector);
}

/// The remainder modulo `M` is unique.
pub proof fn lemma_remainder_unique(p: u128, r1: u64, r2: u64)
    requires
        is_remainder(p, r1),
        is_remainder(p, r2),
    ensures
        r1 == r2,
{
    let q1 = choose|q: u64| p == clmul(q, modulus()) ^ (r1 as u128);
    let q2 = choose|q: u64| p == clmul(q, modulus()) ^ (r2 as u128);
    lemma_clmul_modulus(q1);
    lemma_clmul_modulus(q2);
    assert({
        let (w1, w2) = (q1 as u128, q2 as u128);
        ((w1 << 64u128) ^ (w1 ^ (w1 << 1u128) ^ (w1 << 3u128) ^ (w1 << 4u128))) ^ (r1 as u128) == ((w2
            << 64u128) ^ (w2 ^ (w2 << 1u128) ^ (w2 << 3u128) ^ (w2 << 4u128))) ^ (r2 as u128) ==> r1 == r2
    }) by (bit_vector);
}

/// `p mod M` is the production reduction's closed form.
pub proof fn lemma_k_mod(p: u128)
    ensures
        k_mod(p) == reduce_formula(p),
        is_remainder(p, k_mod(p)),
{
    lemma_reduce_formula_is_remainder(p);
    lemma_remainder_unique(p, k_mod(p), reduce_formula(p));
}

/// Reduction is GF(2)-linear.
pub proof fn lemma_k_mod_xor(p1: u128, p2: u128)
    ensures
        k_mod(p1 ^ p2) == k_mod(p1) ^ k_mod(p2),
{
    lemma_k_mod(p1);
    lemma_k_mod(p2);
    lemma_k_mod(p1 ^ p2);
    assert(reduce_formula(p1 ^ p2) == reduce_formula(p1) ^ reduce_formula(p2)) by (bit_vector);
}

/// A polynomial of degree below 64 is its own remainder.
pub proof fn lemma_k_mod_small(p: u128)
    requires
        p >> 64u128 == 0,
    ensures
        k_mod(p) == p as u64,
{
    lemma_k_mod(p);
    assert(p >> 64u128 == 0 ==> reduce_formula(p) == p as u64) by (bit_vector);
}

/// `(p x) mod M = (p mod M) x mod M`.
pub proof fn lemma_k_mod_shl1(p: u128)
    requires
        p >> 127u128 == 0,
    ensures
        k_mod(p << 1u128) == mulx(k_mod(p)),
{
    lemma_k_mod(p);
    lemma_k_mod(p << 1u128);
    assert(p >> 127u128 == 0 ==> reduce_formula(p << 1u128) == mulx(reduce_formula(p))) by (bit_vector);
}

/// A multiple of `M` reduces to zero.
pub proof fn lemma_k_mod_multiple(q: u64)
    ensures
        k_mod(clmul(q, modulus())) == 0,
{
    lemma_clmul_modulus(q);
    lemma_k_mod(clmul(q, modulus()));
    assert({
        let w = q as u128;
        reduce_formula((w << 64u128) ^ (w ^ (w << 1u128) ^ (w << 3u128) ^ (w << 4u128))) == 0
    }) by (bit_vector);
}

// ---------------------------------------------------------------------------------------------
// K is a commutative ring
// ---------------------------------------------------------------------------------------------
pub proof fn lemma_k_mul_comm(a: u64, b: u64)
    ensures
        k_mul(a, b) == k_mul(b, a),
{
    lemma_clmul_comm(a, b);
}

pub proof fn lemma_k_mul_xor_right(a: u64, b: u64, c: u64)
    ensures
        k_mul(a, b ^ c) == k_mul(a, b) ^ k_mul(a, c),
{
    assert((b ^ c) as u128 == (b as u128) ^ (c as u128)) by (bit_vector);
    lemma_clmul_xor_right(a, b as u128, c as u128);
    lemma_k_mod_xor(clmul(a, b as u128), clmul(a, c as u128));
}

pub proof fn lemma_k_mul_xor_left(a: u64, b: u64, c: u64)
    ensures
        k_mul(a ^ b, c) == k_mul(a, c) ^ k_mul(b, c),
{
    lemma_k_mul_comm(a ^ b, c);
    lemma_k_mul_comm(a, c);
    lemma_k_mul_comm(b, c);
    lemma_k_mul_xor_right(c, a, b);
}

pub proof fn lemma_k_mul_one(a: u64)
    ensures
        k_mul(a, 1) == a,
        k_mul(1, a) == a,
{
    assert(1u64 as u128 == 1u128 << 0u128) by (bit_vector);
    lemma_clmul_monomial(a, 0);
    assert((a as u128) << 0u128 == (a as u128) && (a as u128) >> 64u128 == 0) by (bit_vector);
    lemma_k_mod_small(a as u128);
    lemma_k_mul_comm(a, 1);
}

pub proof fn lemma_k_mul_zero(a: u64)
    ensures
        k_mul(a, 0) == 0,
        k_mul(0, a) == 0,
{
    lemma_clmul_zero(a);
    assert(0u128 >> 64u128 == 0) by (bit_vector);
    lemma_k_mod_small(0);
    lemma_k_mul_comm(a, 0);
}

/// `a * (x b) = x (a * b)`.
pub proof fn lemma_k_mul_mulx(a: u64, b: u64)
    ensures
        k_mul(a, mulx(b)) == mulx(k_mul(a, b)),
{
    let m: u128 = if b >> 63u64 == 1 {
        modulus()
    } else {
        0
    };
    // b x = mulx(b) + [b_63] M, as polynomials.
    assert((b as u128) << 1u128 == (mulx(b) as u128) ^ (if b >> 63u64 == 1 {
        0x1_0000_0000_0000_001Bu128
    } else {
        0u128
    })) by (bit_vector);
    lemma_clmul_shl1(a, b as u128);
    lemma_clmul_xor_right(a, mulx(b) as u128, m);
    lemma_clmul_bound(a, b);
    lemma_k_mod_shl1(clmul(a, b as u128));
    lemma_k_mod_xor(clmul(a, mulx(b) as u128), clmul(a, m));
    if b >> 63u64 == 1 {
        lemma_k_mod_multiple(a);
    } else {
        lemma_clmul_zero(a);
        assert(0u128 >> 64u128 == 0) by (bit_vector);
        lemma_k_mod_small(0);
    }
    let r = k_mod(clmul(a, mulx(b) as u128));
    assert(r ^ 0 == r) by (bit_vector);
}

pub proof fn lemma_k_mul_mulx_pow(a: u64, b: u64, k: nat)
    ensures
        k_mul(a, mulx_pow(b, k)) == mulx_pow(k_mul(a, b), k),
    decreases k,
{
    if k > 0 {
        lemma_k_mul_mulx_pow(a, b, (k - 1) as nat);
        lemma_k_mul_mulx(a, mulx_pow(b, (k - 1) as nat));
    }
}

/// `x^k` is `1 << k` for `k < 64`.
pub proof fn lemma_mulx_pow_one(k: nat)
    requires
        k < 64,
    ensures
        mulx_pow(1, k) == 1u64 << (k as u64),
    decreases k,
{
    if k == 0 {
        assert(1u64 << 0u64 == 1) by (bit_vector);
    } else {
        lemma_mulx_pow_one((k - 1) as nat);
        let s = (k - 1) as u64;
        assert(s < 63 ==> mulx(1u64 << s) == 1u64 << (s + 1)) by (bit_vector);
    }
}

/// `t * x^k = mulx^k(t)`.
pub proof fn lemma_k_mul_monomial(t: u64, k: nat)
    requires
        k < 64,
    ensures
        k_mul(t, 1u64 << (k as u64)) == mulx_pow(t, k),
{
    lemma_mulx_pow_one(k);
    lemma_k_mul_mulx_pow(t, 1, k);
    lemma_k_mul_one(t);
}

/// Associativity, by linearity in `c` and the monomial case `(a b) x^k = a (b x^k)`.
pub proof fn lemma_k_mul_assoc_upto(a: u64, b: u64, c: u64, n: nat)
    requires
        n <= 64,
    ensures
        k_mul(k_mul(a, b), low(c, n)) == k_mul(a, k_mul(b, low(c, n))),
    decreases n,
{
    if n == 0 {
        assert(low(c, 0) == 0) by {
            assert(c & ((1u64 << 0u64) - 1) as u64 == 0) by (bit_vector);
        }
        lemma_k_mul_zero(k_mul(a, b));
        lemma_k_mul_zero(b);
        lemma_k_mul_zero(a);
    } else {
        let i = (n - 1) as nat;
        lemma_k_mul_assoc_upto(a, b, c, i);
        lemma_low_step(c, i);
        let e: u64 = if bit(c, i) {
            1u64 << (i as u64)
        } else {
            0
        };
        let lo = low(c, i);
        lemma_k_mul_xor_right(k_mul(a, b), lo, e);
        lemma_k_mul_xor_right(b, lo, e);
        lemma_k_mul_xor_right(a, k_mul(b, lo), k_mul(b, e));
        if bit(c, i) {
            lemma_k_mul_monomial(k_mul(a, b), i);
            lemma_k_mul_monomial(b, i);
            lemma_k_mul_mulx_pow(a, b, i);
        } else {
            lemma_k_mul_zero(k_mul(a, b));
            lemma_k_mul_zero(b);
            lemma_k_mul_zero(a);
        }
    }
}

pub proof fn lemma_k_mul_assoc(a: u64, b: u64, c: u64)
    ensures
        k_mul(k_mul(a, b), c) == k_mul(a, k_mul(b, c)),
{
    lemma_k_mul_assoc_upto(a, b, c, 64);
}

// ---------------------------------------------------------------------------------------------
// Powers
// ---------------------------------------------------------------------------------------------
pub proof fn lemma_k_pow_add(a: u64, m: nat, n: nat)
    ensures
        k_mul(k_pow(a, m), k_pow(a, n)) == k_pow(a, m + n),
    decreases n,
{
    if n == 0 {
        lemma_k_mul_one(k_pow(a, m));
    } else {
        lemma_k_pow_add(a, m, (n - 1) as nat);
        lemma_k_mul_assoc(k_pow(a, m), k_pow(a, (n - 1) as nat), a);
        assert((m + n - 1) as nat + 1 == m + n);
    }
}

/// Squaring `n` times raises to the power `2^n`: `(a^m)^(2^n) = a^(m 2^n)`.
pub proof fn lemma_k_sq_iter_pow(a: u64, m: nat, n: nat)
    ensures
        k_sq_iter(k_pow(a, m), n) == k_pow(a, m * pow2(n)),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
        assert(m * pow2(0) == m) by (nonlinear_arith)
            requires
                pow2(0) == 1,
        ;
    } else {
        lemma_k_sq_iter_pow(a, m, (n - 1) as nat);
        let e = m * pow2((n - 1) as nat);
        lemma_k_pow_add(a, e, e);
        lemma_pow2_unfold(n);
        assert(e + e == m * pow2(n)) by (nonlinear_arith)
            requires
                e == m * pow2((n - 1) as nat),
                pow2(n) == 2 * pow2((n - 1) as nat),
        ;
    }
}

pub proof fn lemma_k_sq_iter_add(a: u64, m: nat, n: nat)
    ensures
        k_sq_iter(k_sq_iter(a, m), n) == k_sq_iter(a, m + n),
    decreases n,
{
    if n > 0 {
        lemma_k_sq_iter_add(a, m, (n - 1) as nat);
    }
}

// ---------------------------------------------------------------------------------------------
// Executable code: the portable paths of `crates/primitives/src/field/gf2_64.rs`
// ---------------------------------------------------------------------------------------------
/// Reduction constant of the base field: `x^64 = x^4 + x^3 + x + 1 = 0x1B`.
pub const R64: u64 = 0x1B;

/// A GF(2^64) element; bit i = coefficient of x^i.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct F64(pub u64);

impl F64 {
    /// Degree over GF(2), the number of binary coefficients in one element.
    pub const DEGREE: usize = 64;

    pub const ZERO: Self = Self(0);

    pub const ONE: Self = Self(1);

    /// `x`, with `ord(x) = 2^64 - 1`.
    pub const G: Self = Self(2);

    #[inline]
    pub const fn is_zero(self) -> (r: bool)
        ensures
            r == (self.0 == 0),
    {
        self.0 == 0
    }

    /// Squaring, as a bit spread followed by one reduction.
    #[inline]
    pub fn square(self) -> (r: Self)
        ensures
            r.0 == k_mul(self.0, self.0),
    {
        Self(reduce(square_wide(self.0)))
    }

    /// Multiplicative inverse `x^(2^64 - 2)`, mapping zero to zero.
    ///
    /// Itoh-Tsujii: with `t_k = x^(2^k - 1)`, the inverse is `t_63^2`.
    pub fn inv(self) -> (r: Self)
        ensures
            r.0 == k_pow(self.0, (pow2(64) - 2) as nat),
    {
        // Square `v` a total of `n` times.
        let sq = |v: Self, n: u32| -> (r: Self)
            ensures
                r.0 == k_sq_iter(v.0, n as nat),
            {
                let ghost v0 = v;
                let mut v = v;
                for i in 0..n
                    invariant
                        v.0 == k_sq_iter(v0.0, i as nat),
                {
                    v = v.square();
                }
                v
            };
        let ghost a = self.0;
        proof {
            lemma2_to64();
            lemma2_to64_rest();
            assert(k_pow(a, 1) == a) by {
                assert(k_pow(a, 0) == 1);
                lemma_k_mul_one(a);
                lemma_k_mul_comm(1, a);
            }
        }
        // Each step reads t_k = x^(2^k - 1).
        let t1 = self;
        let t2 = sq(t1, 1) * t1;
        proof { step(a, 1, 1, 1) }
        let t3 = sq(t2, 1) * t1;
        proof { step(a, 2, 1, 1) }
        let t6 = sq(t3, 3) * t3;
        proof { step(a, 3, 3, 3) }
        let t12 = sq(t6, 6) * t6;
        proof { step(a, 6, 6, 6) }
        let t24 = sq(t12, 12) * t12;
        proof { step(a, 12, 12, 12) }
        let t48 = sq(t24, 24) * t24;
        proof { step(a, 24, 24, 24) }
        let t60 = sq(t48, 12) * t12;
        proof { step(a, 48, 12, 12) }
        let t63 = sq(t60, 3) * t3;
        proof { step(a, 60, 3, 3) }
        // (x^(2^63 - 1))^2 = x^(2^64 - 2).
        proof {
            lemma_k_sq_iter_pow(a, (pow2(63) - 1) as nat, 1);
        }
        sq(t63, 1)
    }
}

/// One Itoh-Tsujii step: `t_k^(2^n) * t_n = t_(k + n)` with `t_k = a^(2^k - 1)`.
proof fn step(a: u64, k: nat, n: nat, n2: nat)
    requires
        n == n2,
        k + n <= 64,
    ensures
        k_mul(k_sq_iter(k_pow(a, (pow2(k) - 1) as nat), n), k_pow(a, (pow2(n2) - 1) as nat)) == k_pow(
            a,
            (pow2(k + n) - 1) as nat,
        ),
{
    lemma_k_sq_iter_pow(a, (pow2(k) - 1) as nat, n);
    lemma_pow2_pos(k);
    lemma_pow2_pos(n);
    lemma_pow2_adds(k, n);
    let e1 = ((pow2(k) - 1) as nat) * pow2(n);
    let e2 = (pow2(n) - 1) as nat;
    lemma_k_pow_add(a, e1, e2);
    assert(e1 + e2 == (pow2(k + n) - 1) as nat) by (nonlinear_arith)
        requires
            e1 == ((pow2(k) - 1) as nat) * pow2(n),
            e2 == (pow2(n) - 1) as nat,
            pow2(k) * pow2(n) == pow2(k + n),
            pow2(k) > 0,
            pow2(n) > 0,
    ;
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl for F64 {
    open spec fn obeys_add_spec() -> bool {
        true
    }

    open spec fn add_req(self, rhs: F64) -> bool {
        true
    }

    open spec fn add_spec(self, rhs: F64) -> F64 {
        F64(self.0 ^ rhs.0)
    }
}

impl Add for F64 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> (r: Self)
        ensures
            r.0 == self.0 ^ rhs.0,
    {
        Self(self.0 ^ rhs.0)
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl for F64 {
    open spec fn obeys_mul_spec() -> bool {
        true
    }

    open spec fn mul_req(self, rhs: F64) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: F64) -> F64 {
        F64(k_mul(self.0, rhs.0))
    }
}

impl Mul for F64 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> (r: Self)
        ensures
            r.0 == k_mul(self.0, rhs.0),
    {
        Self(reduce(mul_wide(self.0, rhs.0)))
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddAssignSpecImpl for F64 {
    open spec fn obeys_add_assign_spec() -> bool {
        true
    }

    open spec fn add_assign_req(&self, rhs: F64) -> bool {
        true
    }

    open spec fn add_assign_spec(&self, rhs: F64) -> &F64 {
        &F64(self.0 ^ rhs.0)
    }
}

impl AddAssign for F64 {
    #[inline]
    fn add_assign(&mut self, rhs: Self)
        ensures
            final(self).0 == old(self).0 ^ rhs.0,
    {
        self.0 ^= rhs.0;
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulAssignSpecImpl for F64 {
    open spec fn obeys_mul_assign_spec() -> bool {
        true
    }

    open spec fn mul_assign_req(&self, rhs: F64) -> bool {
        true
    }

    open spec fn mul_assign_spec(&self, rhs: F64) -> &F64 {
        &F64(k_mul(self.0, rhs.0))
    }
}

impl MulAssign for F64 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self)
        ensures
            final(self).0 == k_mul(old(self).0, rhs.0),
    {
        *self = *self * rhs;
    }
}

/// The carry-less product of two 64-bit polynomials, as a 128-bit polynomial.
#[inline]
pub fn mul_wide(a: u64, b: u64) -> (r: u128)
    ensures
        r == clmul(a, b as u128),
{
    software::clmul(a, b)
}

/// The carry-less square of a 64-bit polynomial: bit `i` moves to bit `2i`.
#[inline]
pub fn square_wide(a: u64) -> (r: u128)
    ensures
        r == clmul(a, a as u128),
{
    mul_wide(a, a)
}

/// Reduce a 128-bit carry-less product modulo `x^64 + x^4 + x^3 + x + 1`.
#[inline]
pub const fn reduce(p: u128) -> (r: u64)
    ensures
        r == k_mod(p),
        is_remainder(p, r),
{
    proof {
        lemma_k_mod(p);
    }
    // Split the product into its low and high words.
    let (lo, hi) = (p as u64, (p >> 64) as u64);
    // The bits of `hi * 0x1B` shifted past x^63, which wrap around as `spill * 0x1B`.
    let spill = (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
    // Fold `hi` and `spill` together: both are multiplied by the same constant.
    let v = hi ^ spill;
    lo ^ v ^ (v << 1) ^ (v << 3) ^ (v << 4)
}

pub mod software {
    use super::*;

    /// Portable 64x64 carry-less product, used by fallback paths and as the reference.
    pub const fn clmul(a: u64, b: u64) -> (r: u128)
        ensures
            r == crate::clmul::clmul(a, b as u128),
    {
        let mut acc = 0u128;
        let mut i = 0;
        // Schoolbook: XOR in `b * x^i` for every set bit `i` of `a`.
        while i < 64
            invariant
                0 <= i <= 64,
                acc == clmul_upto(a, b as u128, i as nat),
            decreases 64 - i,
        {
            proof {
                let s = i as u64;
                let bb = b as u128;
                assert(((a >> s) & 1 != 0) == ((a >> s) & 1 == 1)) by (bit_vector);
                assert(acc ^ 0 == acc) by (bit_vector);
            }
            if (a >> i) & 1 != 0 {
                acc ^= (b as u128) << i;
            }
            i += 1;
        }
        acc
    }
}

// ---------------------------------------------------------------------------------------------
// The scalar SIMD products: their reduction, given the semantics of the carry-less multiply
// ---------------------------------------------------------------------------------------------
/// The reduction of `x86_64::mul` (PCLMULQDQ) and `aarch64::mul_shift_tail` / `reduce_pair_pmull4` (PMULL):
///
/// ```text
///     t = hi(p) * 0x1B,  u = hi(t) * 0x1B,  result = lo(p ^ t ^ u)
/// ```
///
/// equals [`reduce`], so with the instruction computing [`clmul`] those kernels compute [`k_mul`].
pub proof fn lemma_clmul_fold_reduction(p: u128)
    ensures
        ({
            let t = clmul((p >> 64u128) as u64, 0x1Bu128);
            let u = clmul((t >> 64u128) as u64, 0x1Bu128);
            (p ^ t ^ u) as u64 == k_mod(p)
        }),
{
    let t = clmul((p >> 64u128) as u64, 0x1Bu128);
    lemma_clmul_r64((p >> 64u128) as u64);
    lemma_clmul_r64((t >> 64u128) as u64);
    lemma_k_mod(p);
    assert({
        let h = ((p >> 64u128) as u64) as u128;
        let t = h ^ (h << 1u128) ^ (h << 3u128) ^ (h << 4u128);
        let h2 = ((t >> 64u128) as u64) as u128;
        let u = h2 ^ (h2 << 1u128) ^ (h2 << 3u128) ^ (h2 << 4u128);
        (p ^ t ^ u) as u64 == reduce_formula(p)
    }) by (bit_vector);
}

} // verus!
