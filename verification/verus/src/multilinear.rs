//! The equality polynomial and its tables over the Boolean cube.
//!
//! The executable functions are the portable paths of `crates/primitives/src/multilinear.rs`, copied with the same
//! bodies where Verus accepts them; `tests/equivalence/multilinear.rs` checks the two agree. Where Verus rejects the
//! production form (iterator chains and `fold`, `as_chunks_mut`, `split_at_mut`, `MaybeUninit` and `set_len`,
//! `[x; N]`, the parallel pass), the copy spells out the same arithmetic in `while`/`for` loops over indices; each
//! such spot says what it replaces.
//!
//! Specification: over `E` ([`e_mul`], [`e_add`]; `1 - a = 1 + a` in characteristic 2),
//!
//! ```text
//!     eq(r, x) = prod_i (r_i x_i + (1 + r_i)(1 + x_i))        ([`eq_poly`], [`eq_factor`])
//! ```
//!
//! and a table over `n` variables holds at index `x` the value at the cube point whose coordinate `i` is bit `i`
//! of `x` (LSB first, [`cube_point`], [`eq_at`]).
use crate::gf2_64::*;
use crate::gf2_64x3::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// One coordinate's factor of `eq`: `r x + (1 + r)(1 + x)`.
pub open spec fn eq_factor(r: F192, x: F192) -> F192 {
    e_add(e_mul(r, x), e_mul(e_add(F192::ONE, r), e_add(F192::ONE, x)))
}

/// `eq(r, x) = prod_i eq_factor(r_i, x_i)`, the product taken from the first coordinate up.
pub open spec fn eq_poly(r: Seq<F192>, x: Seq<F192>) -> F192
    decreases r.len(),
{
    if r.len() == 0 {
        F192::ONE
    } else {
        e_mul(eq_poly(r.drop_last(), x.drop_last()), eq_factor(r.last(), x.last()))
    }
}

/// Bit `i` of an index.
pub open spec fn bit(x: usize, i: int) -> bool {
    (x >> (i as usize)) & 1 == 1
}

/// A bit as an element of `E`.
pub open spec fn e_bool(b: bool) -> F192 {
    if b {
        F192::ONE
    } else {
        F192::ZERO
    }
}

/// The point of the cube `{0, 1}^n` at index `x`: coordinate `i` is bit `i` of `x`.
pub open spec fn cube_point(n: nat, x: usize) -> Seq<F192> {
    Seq::new(n, |i: int| e_bool(bit(x, i)))
}

/// `eq(r, x)` at the cube point of index `x`.
pub open spec fn eq_at(r: Seq<F192>, x: usize) -> F192 {
    eq_poly(r, cube_point(r.len(), x))
}

/// `t` is `seed * eq(r, .)`: `2^n` entries, entry `x` being `seed * eq(r, x)`.
pub open spec fn is_eq_table(t: Seq<F192>, r: Seq<F192>, seed: F192) -> bool {
    &&& r.len() < 64
    &&& t.len() == (1usize << r.len())
    &&& forall|x: int| 0 <= x < t.len() ==> #[trigger] t[x] == e_mul(seed, eq_at(r, x as usize))
}

// ---------------------------------------------------------------------------------------------
// Algebra of E used below
// ---------------------------------------------------------------------------------------------
proof fn lemma_xor_ring(a: u64, b: u64, c: u64)
    ensures
        a ^ b == b ^ a,
        (a ^ b) ^ c == a ^ (b ^ c),
        a ^ 0 == a,
        0 ^ a == a,
        a ^ a == 0,
        a ^ (b ^ (c ^ a)) == b ^ c,
{
    assert(a ^ b == b ^ a && (a ^ b) ^ c == a ^ (b ^ c) && a ^ 0 == a && 0 ^ a == a && a ^ a == 0 && a ^ (b ^ (c
        ^ a)) == b ^ c) by (bit_vector);
}

/// `E` under `+`: commutative, associative, zero, every element its own negative.
pub proof fn lemma_e_add(a: F192, b: F192, c: F192)
    ensures
        e_add(a, b) == e_add(b, a),
        e_add(e_add(a, b), c) == e_add(a, e_add(b, c)),
        e_add(a, F192::ZERO) == a,
        e_add(F192::ZERO, a) == a,
        e_add(a, a) == F192::ZERO,
        e_add(a, e_add(b, e_add(c, a))) == e_add(b, c),
{
    lemma_xor_ring(a.c0, b.c0, c.c0);
    lemma_xor_ring(a.c1, b.c1, c.c1);
    lemma_xor_ring(a.c2, b.c2, c.c2);
}

pub proof fn lemma_e_mul_zero(a: F192)
    ensures
        e_mul(a, F192::ZERO) == F192::ZERO,
        e_mul(F192::ZERO, a) == F192::ZERO,
{
    lemma_k_mul_zero(a.c0);
    lemma_k_mul_zero(a.c1);
    lemma_k_mul_zero(a.c2);
    assert(0u64 ^ (0u64 ^ 0u64) == 0u64 && (0u64 ^ 0u64) ^ (0u64 ^ 0u64) ^ 0u64 == 0u64 && (0u64 ^ 0u64 ^ 0u64)
        ^ 0u64 == 0u64) by (bit_vector);
}

proof fn lemma_xor_distrib(
    b00: u64, b01: u64, b02: u64, b10: u64, b11: u64, b12: u64, b20: u64, b21: u64, b22: u64,
    c00: u64, c01: u64, c02: u64, c10: u64, c11: u64, c12: u64, c20: u64, c21: u64, c22: u64,
)
    ensures
        (b00 ^ c00) ^ ((b12 ^ c12) ^ (b21 ^ c21)) == (b00 ^ (b12 ^ b21)) ^ (c00 ^ (c12 ^ c21)),
        ((b01 ^ c01) ^ (b10 ^ c10)) ^ ((b12 ^ c12) ^ (b21 ^ c21)) ^ (b22 ^ c22) == ((b01 ^ b10) ^ (b12 ^ b21) ^ b22)
            ^ ((c01 ^ c10) ^ (c12 ^ c21) ^ c22),
        ((b02 ^ c02) ^ (b11 ^ c11) ^ (b20 ^ c20)) ^ (b22 ^ c22) == ((b02 ^ b11 ^ b20) ^ b22) ^ ((c02 ^ c11 ^ c20)
            ^ c22),
{
    assert((b00 ^ c00) ^ ((b12 ^ c12) ^ (b21 ^ c21)) == (b00 ^ (b12 ^ b21)) ^ (c00 ^ (c12 ^ c21))) by (bit_vector);
    assert(((b01 ^ c01) ^ (b10 ^ c10)) ^ ((b12 ^ c12) ^ (b21 ^ c21)) ^ (b22 ^ c22) == ((b01 ^ b10) ^ (b12 ^ b21)
        ^ b22) ^ ((c01 ^ c10) ^ (c12 ^ c21) ^ c22)) by (bit_vector);
    assert(((b02 ^ c02) ^ (b11 ^ c11) ^ (b20 ^ c20)) ^ (b22 ^ c22) == ((b02 ^ b11 ^ b20) ^ b22) ^ ((c02 ^ c11
        ^ c20) ^ c22)) by (bit_vector);
}

/// The product distributes over the sum.
pub proof fn lemma_e_mul_distrib(a: F192, b: F192, c: F192)
    ensures
        e_mul(a, e_add(b, c)) == e_add(e_mul(a, b), e_mul(a, c)),
        e_mul(e_add(b, c), a) == e_add(e_mul(b, a), e_mul(c, a)),
{
    let s = e_add(b, c);
    lemma_k_mul_xor_right(a.c0, b.c0, c.c0);
    lemma_k_mul_xor_right(a.c0, b.c1, c.c1);
    lemma_k_mul_xor_right(a.c0, b.c2, c.c2);
    lemma_k_mul_xor_right(a.c1, b.c0, c.c0);
    lemma_k_mul_xor_right(a.c1, b.c1, c.c1);
    lemma_k_mul_xor_right(a.c1, b.c2, c.c2);
    lemma_k_mul_xor_right(a.c2, b.c0, c.c0);
    lemma_k_mul_xor_right(a.c2, b.c1, c.c1);
    lemma_k_mul_xor_right(a.c2, b.c2, c.c2);
    lemma_xor_distrib(
        k_mul(a.c0, b.c0), k_mul(a.c0, b.c1), k_mul(a.c0, b.c2),
        k_mul(a.c1, b.c0), k_mul(a.c1, b.c1), k_mul(a.c1, b.c2),
        k_mul(a.c2, b.c0), k_mul(a.c2, b.c1), k_mul(a.c2, b.c2),
        k_mul(a.c0, c.c0), k_mul(a.c0, c.c1), k_mul(a.c0, c.c2),
        k_mul(a.c1, c.c0), k_mul(a.c1, c.c1), k_mul(a.c1, c.c2),
        k_mul(a.c2, c.c0), k_mul(a.c2, c.c1), k_mul(a.c2, c.c2),
    );
    assert(e_mul(a, s) == e_add(e_mul(a, b), e_mul(a, c)));
    lemma_e_mul_comm(a, s);
    lemma_e_mul_comm(a, b);
    lemma_e_mul_comm(a, c);
}

/// `v + v r = v (1 + r)`: the doubling's low child.
proof fn lemma_times_one_plus(v: F192, r: F192)
    ensures
        e_add(v, e_mul(v, r)) == e_mul(v, e_add(F192::ONE, r)),
{
    lemma_e_mul_distrib(v, F192::ONE, r);
    lemma_e_mul_one(v);
}

// ---------------------------------------------------------------------------------------------
// The equality polynomial
// ---------------------------------------------------------------------------------------------
/// At a cube coordinate the factor selects: `eq_factor(r, 1) = r`, `eq_factor(r, 0) = 1 + r`.
pub proof fn lemma_eq_factor_bits(r: F192)
    ensures
        eq_factor(r, F192::ONE) == r,
        eq_factor(r, F192::ZERO) == e_add(F192::ONE, r),
{
    let s = e_add(F192::ONE, r);
    assert(1u64 ^ 1u64 == 0u64 && 1u64 ^ 0u64 == 1u64 && 0u64 ^ 0u64 == 0u64) by (bit_vector);
    assert(e_add(F192::ONE, F192::ONE) == F192::ZERO);
    assert(e_add(F192::ONE, F192::ZERO) == F192::ONE);
    lemma_e_mul_one(r);
    lemma_e_mul_one(s);
    lemma_e_mul_zero(r);
    lemma_e_mul_zero(s);
    lemma_e_add(r, r, r);
    lemma_e_add(s, s, s);
}

/// In characteristic 2 the factor is `1 + r + x` for every `x`, the form `eq_eval` computes.
pub proof fn lemma_eq_factor_sum(r: F192, x: F192)
    ensures
        eq_factor(r, x) == e_add(e_add(F192::ONE, r), x),
{
    let (s, t, u) = (e_add(F192::ONE, r), e_add(F192::ONE, x), e_mul(r, x));
    // (1 + r)(1 + x) = (1 + r) + (x + r x).
    lemma_e_mul_distrib(s, F192::ONE, x);
    lemma_e_mul_one(s);
    lemma_e_mul_distrib(x, F192::ONE, r);
    lemma_e_mul_one(x);
    lemma_e_mul_comm(s, x);
    lemma_e_mul_comm(x, r);
    assert(e_mul(s, t) == e_add(s, e_add(x, u)));
    lemma_e_add(u, s, x);
    lemma_e_add(s, x, u);
    lemma_e_add(x, u, s);
    assert(e_add(u, e_add(s, e_add(x, u))) == e_add(s, x));
}

/// A table entry extended by one top variable: the low half picks `1 + r_i`, the high half `r_i`.
pub proof fn lemma_eq_at_high(r: Seq<F192>, j: usize)
    requires
        1 <= r.len() <= 63,
        j < (1usize << ((r.len() - 1) as usize)),
    ensures
        eq_at(r, j) == e_mul(eq_at(r.drop_last(), j), e_add(F192::ONE, r.last())),
        eq_at(r, (j + (1usize << ((r.len() - 1) as usize))) as usize) == e_mul(eq_at(r.drop_last(), j), r.last()),
{
    let i = (r.len() - 1) as usize;
    let j2 = (j + (1usize << i)) as usize;
    lemma_bit_add_high(j, i);
    let (p, p2) = (cube_point(r.len(), j), cube_point(r.len(), j2));
    assert(p.drop_last() =~= cube_point(i as nat, j));
    assert forall|k: int| 0 <= k < i implies #[trigger] bit(j2, k) == bit(j, k) by {
        lemma_bit_add_low(j, i, k as usize);
    }
    assert(p2.drop_last() =~= cube_point(i as nat, j));
    assert(p.last() == F192::ZERO);
    assert(p2.last() == F192::ONE);
    lemma_eq_factor_bits(r.last());
}

proof fn lemma_bit_add_high(j: usize, i: usize)
    requires
        i < 63,
        j < (1usize << i),
    ensures
        (j >> i) & 1 == 0,
        ((j + (1usize << i)) as usize >> i) & 1 == 1,
{
    assert((j >> i) & 1 == 0 && ((j + (1usize << i)) as usize >> i) & 1 == 1) by (bit_vector)
        requires
            i < 63,
            j < (1usize << i),
    ;
}

proof fn lemma_bit_add_low(j: usize, i: usize, k: usize)
    requires
        i < 63,
        j < (1usize << i),
        k < i,
    ensures
        ((j + (1usize << i)) as usize >> k) & 1 == (j >> k) & 1,
{
    assert(((j + (1usize << i)) as usize >> k) & 1 == (j >> k) & 1) by (bit_vector)
        requires
            i < 63,
            j < (1usize << i),
            k < i,
    ;
}

/// `2^(i+1) = 2 * 2^i` as shifts.
proof fn lemma_shl_double(i: usize)
    requires
        i < 63,
    ensures
        (1usize << i) * 2 == (1usize << ((i + 1) as usize)),
        (1usize << i) >= 1,
        (1usize << i) <= (1usize << 62usize),
{
    assert((1usize << i) * 2 == (1usize << ((i + 1) as usize)) && (1usize << i) >= 1 && (1usize << i) <= (1usize
        << 62usize)) by (bit_vector)
        requires
            i < 63,
    ;
}

/// The bits of `(h << L) | l`, `l < 2^L`: those of `l` below `L`, those of `h` above.
proof fn lemma_bit_concat(h: usize, l: usize, low: usize, k: usize)
    requires
        low < 64,
        l < (1usize << low),
        k < 64,
    ensures
        k < low ==> (((h << low) | l) >> k) & 1 == (l >> k) & 1,
        k >= low ==> (((h << low) | l) >> k) & 1 == (h >> ((k - low) as usize)) & 1,
{
    assert(k < low ==> (((h << low) | l) >> k) & 1 == (l >> k) & 1) by (bit_vector)
        requires
            low < 64,
            l < (1usize << low),
            k < 64,
    ;
    assert(k >= low ==> (((h << low) | l) >> k) & 1 == (h >> ((k - low) as usize)) & 1) by (bit_vector)
        requires
            low < 64,
            l < (1usize << low),
            k < 64,
    ;
}

/// `eq` of a concatenation is the product of the parts' `eq`.
pub proof fn lemma_eq_poly_concat(r1: Seq<F192>, x1: Seq<F192>, r2: Seq<F192>, x2: Seq<F192>)
    requires
        r1.len() == x1.len(),
        r2.len() == x2.len(),
    ensures
        eq_poly(r1 + r2, x1 + x2) == e_mul(eq_poly(r1, x1), eq_poly(r2, x2)),
    decreases r2.len(),
{
    if r2.len() == 0 {
        assert(r1 + r2 =~= r1);
        assert(x1 + x2 =~= x1);
        lemma_e_mul_one(eq_poly(r1, x1));
    } else {
        assert((r1 + r2).drop_last() =~= r1 + r2.drop_last());
        assert((x1 + x2).drop_last() =~= x1 + x2.drop_last());
        lemma_eq_poly_concat(r1, x1, r2.drop_last(), x2.drop_last());
        lemma_e_mul_assoc(
            eq_poly(r1, x1),
            eq_poly(r2.drop_last(), x2.drop_last()),
            eq_factor(r2.last(), x2.last()),
        );
    }
}

/// The tensor structure of the table: `eq(r, (h << L) | l) = eq(r[..L], l) * eq(r[L..], h)` for `l < 2^L`.
pub proof fn lemma_eq_at_tensor(r: Seq<F192>, low: usize, h: usize, l: usize)
    requires
        low <= r.len() < 64,
        l < (1usize << low),
    ensures
        eq_at(r, (h << low) | l) == e_mul(eq_at(r.subrange(0, low as int), l), eq_at(r.subrange(low as int, r.len() as int), h)),
{
    let n = r.len();
    let x = (h << low) | l;
    let (rl, rh) = (r.subrange(0, low as int), r.subrange(low as int, n as int));
    assert forall|k: int| 0 <= k < n implies #[trigger] bit(x, k) == (if k < low {
        bit(l, k)
    } else {
        bit(h, k - low)
    }) by {
        lemma_bit_concat(h, l, low, k as usize);
    }
    assert(cube_point(n, x) =~= cube_point(low as nat, l) + cube_point((n - low) as nat, h));
    assert(r =~= rl + rh);
    lemma_eq_poly_concat(rl, cube_point(low as nat, l), rh, cube_point((n - low) as nat, h));
}

/// `h * 2^L + l = (h << L) | l` for `l < 2^L` and `h < 2^(n - L)`, and it is below `2^n`.
proof fn lemma_index_split(h: usize, l: usize, low: usize, n: usize)
    requires
        low <= n < 64,
        l < (1usize << low),
        h < (1usize << ((n - low) as usize)),
    ensures
        h * (1usize << low) + l == (h << low) | l,
        h * (1usize << low) + l < (1usize << n),
{
    lemma_usize_pow2_no_overflow(low as nat);
    lemma_usize_pow2_no_overflow((n - low) as nat);
    lemma_usize_pow2_no_overflow(n as nat);
    lemma_usize_shl_is_mul(1, low);
    lemma_usize_shl_is_mul(1, (n - low) as usize);
    lemma_usize_shl_is_mul(1, n);
    lemma_pow2_adds((n - low) as nat, low as nat);
    lemma_pow2_pos(low as nat);
    assert(h * pow2(low as nat) + l < pow2(n as nat)) by (nonlinear_arith)
        requires
            h + 1 <= pow2((n - low) as nat),
            l < pow2(low as nat),
            pow2((n - low) as nat) * pow2(low as nat) == pow2(n as nat),
    ;
    lemma_usize_pow2_no_overflow(n as nat);
    lemma_usize_shl_is_mul(h, low);
    let hs = h << low;
    assert(hs + l == hs | l) by (bit_vector)
        requires
            hs == h << low,
            l < (1usize << low),
            low < 64,
    ;
}

/// An index splits as `((x >> L) << L) | (x & (2^L - 1))`, its high part below `2^(n - L)`.
proof fn lemma_index_parts(x: usize, low: usize, n: usize)
    requires
        low <= n < 64,
        x < (1usize << n),
    ensures
        x == ((x >> low) << low) | (x & sub(1usize << low, 1)),
        (x & sub(1usize << low, 1)) < (1usize << low),
        (x >> low) < (1usize << ((n - low) as usize)),
        (1usize << low) >= 1,
{
    assert(x == ((x >> low) << low) | (x & sub(1usize << low, 1)) && (x & sub(1usize << low, 1)) < (1usize << low)
        && (x >> low) < (1usize << ((n - low) as usize)) && (1usize << low) >= 1) by (bit_vector)
        requires
            low <= n < 64,
            x < (1usize << n),
    ;
}

// ---------------------------------------------------------------------------------------------
// Executable code: the portable paths
// ---------------------------------------------------------------------------------------------
/// Multilinear interpolation in one variable over `E`: `lo + t·(lo+hi)`, the
/// char-2 form of `(1−t)·lo + t·hi`.
#[inline]
pub fn interp(lo: F192, hi: F192, t: F192) -> (r: F192)
    ensures
        r == e_add(e_mul(e_add(F192::ONE, t), lo), e_mul(t, hi)),
{
    proof {
        lemma_e_mul_distrib(t, lo, hi);
        lemma_e_mul_distrib(lo, F192::ONE, t);
        lemma_e_mul_one(lo);
        lemma_e_mul_comm(lo, e_add(F192::ONE, t));
        lemma_e_mul_comm(lo, t);
        lemma_e_add(lo, e_mul(t, lo), e_mul(t, hi));
    }
    lo + t * (lo + hi)
}

/// Mixed interpolation: two `K` endpoints against an `E` parameter, one
/// `mul_base` (`lo + t·(lo+hi)` with `lo, hi ∈ K`).
#[inline]
pub fn interp_k(lo: F64, hi: F64, t: F192) -> (r: F192)
    ensures
        r == e_add(e_mul(e_add(F192::ONE, t), e_from_k(lo.0)), e_mul(t, e_from_k(hi.0))),
{
    proof {
        let (l, h) = (e_from_k(lo.0), e_from_k(hi.0));
        assert(e_from_k(lo.0 ^ hi.0) == e_add(l, h)) by {
            assert(0u64 ^ 0u64 == 0u64) by (bit_vector);
        }
        lemma_e_mul_distrib(t, l, h);
        lemma_e_mul_distrib(l, F192::ONE, t);
        lemma_e_mul_one(l);
        lemma_e_mul_comm(l, e_add(F192::ONE, t));
        lemma_e_mul_comm(l, t);
        lemma_e_add(l, e_mul(t, l), e_mul(t, h));
    }
    F192::from(lo) + t.mul_base(lo + hi)
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)`. For Boolean `r`, this is the indicator
/// of `x = r`; for arbitrary `r`, it is the multilinear interpolation weight.
///
/// Production folds over `r.iter().zip(x)` after a `debug_assert_eq!` of the lengths, here a `requires`.
pub fn eq_eval(r: &[F192], x: &[F192]) -> (e: F192)
    requires
        r.len() == x.len(),
    ensures
        e == eq_poly(r@, x@),
{
    let mut acc = F192::ONE;
    for i in 0..r.len()
        invariant
            r.len() == x.len(),
            acc == eq_poly(r@.subrange(0, i as int), x@.subrange(0, i as int)),
    {
        proof {
            lemma_eq_factor_sum(r@[i as int], x@[i as int]);
            assert(r@.subrange(0, i + 1).drop_last() =~= r@.subrange(0, i as int));
            assert(x@.subrange(0, i + 1).drop_last() =~= x@.subrange(0, i as int));
        }
        acc = acc * (F192::ONE + r[i] + x[i]);
    }
    proof {
        assert(r@.subrange(0, r.len() as int) =~= r@);
        assert(x@.subrange(0, x.len() as int) =~= x@);
    }
    acc
}

/// The `eq(r, ·)` table over `n = r.len()` variables. See [`fill_eq_table_uninit`].
pub fn eq_table(r: &[F192]) -> (t: Vec<F192>)
    requires
        r.len() < 64,
    ensures
        is_eq_table(t@, r@, F192::ONE),
    decreases r.len(), 2nat,
{
    eq_table_seeded(r, F192::ONE)
}

/// The table of `seed * eq(r, .)` over `n = r.len()` variables, in LSB-first order.
///
/// Production fills the spare capacity of `Vec::with_capacity(len)` and then sets the length; the copy fills a
/// vector of zeros. The length `1 << r.len()` needs `r.len() < 64`, a `requires`.
pub fn eq_table_seeded(r: &[F192], seed: F192) -> (t: Vec<F192>)
    requires
        r.len() < 64,
    ensures
        is_eq_table(t@, r@, seed),
    decreases r.len(), 1nat,
{
    // One entry per point of the cube: 2^n.
    let len = 1usize << r.len();

    let mut eq = vec![F192::ZERO; len];
    fill_eq_table_uninit(r, seed, eq.as_mut_slice());
    eq
}

/// Fill `out` with `seed * eq(r, .)`, in LSB-first order. Every entry is written before it is read.
///
/// A small table doubles a level at a time on the calling thread.
///
/// A large one is a tensor product, written in one parallel pass:
///
/// ```text
///     out[h * 2^L + l] = high[h] * low[l],    low = eq(r[..L]),  high = seed * eq(r[L..])
/// ```
///
/// Production writes `MaybeUninit` slots; the copy writes initialized ones. Its `assert_eq!` on the length is a
/// `requires`. The parallel pass (`parallel::chunks_mut` over chunks of whole rows, each row zipped with its
/// weight `high[h]` and cut `as_chunks_mut::<4>`) becomes a loop over the rows in order: each entry is written
/// once, from `high[h]` and `low` alone, so the order of the rows does not change the table.
pub fn fill_eq_table_uninit(r: &[F192], seed: F192, out: &mut [F192])
    requires
        r.len() < 64,
        old(out).len() == (1usize << r.len()),
    ensures
        is_eq_table(final(out)@, r@, seed),
    decreases r.len(), 0nat,
{
    if out.len() < EQ_PAR_LEN {
        return fill_eq_doubling(r, seed, out);
    }
    proof {
        let nn = r.len();
        assert(EQ_PAR_LEN == 65536) by (compute_only);
        assert((1usize << nn) >= 65536usize ==> nn >= 16) by (bit_vector)
            requires
                nn < 64,
        ;
    }
    let r_low = &r[..EQ_LOW_VARS];
    let r_high = &r[EQ_LOW_VARS..];
    let low = eq_table(r_low);
    let high = eq_table_seeded(r_high, seed);
    let ghost n = r.len();
    let ghost hl = (n - EQ_LOW_VARS) as usize;
    proof {
        assert(r_low@ == r@.subrange(0, EQ_LOW_VARS as int));
        assert(r_high@ == r@.subrange(EQ_LOW_VARS as int, n as int));
        assert(low.len() == 1024) by {
            assert((1usize << 10usize) == 1024) by (bit_vector);
        }
    }
    let mut h = 0;
    while h < high.len()
        invariant
            n == r.len(),
            n < 64,
            hl == n - EQ_LOW_VARS,
            out.len() == (1usize << n),
            low.len() == 1024,
            low.len() == (1usize << EQ_LOW_VARS),
            high.len() == (1usize << hl),
            is_eq_table(low@, r_low@, F192::ONE),
            is_eq_table(high@, r_high@, seed),
            r_low@ == r@.subrange(0, EQ_LOW_VARS as int),
            r_high@ == r@.subrange(EQ_LOW_VARS as int, n as int),
            h <= high.len(),
            forall|x: int| 0 <= x < h * 1024 ==> #[trigger] out@[x] == e_mul(seed, eq_at(r@, x as usize)),
        decreases high.len() - h,
    {
        let w = high[h];
        let mut c = 0;
        while c < low.len() / 4
            invariant
                n == r.len(),
                n < 64,
                hl == n - EQ_LOW_VARS,
                out.len() == (1usize << n),
                low.len() == 1024,
                low.len() == (1usize << EQ_LOW_VARS),
                high.len() == (1usize << hl),
                is_eq_table(low@, r_low@, F192::ONE),
                is_eq_table(high@, r_high@, seed),
                r_low@ == r@.subrange(0, EQ_LOW_VARS as int),
                r_high@ == r@.subrange(EQ_LOW_VARS as int, n as int),
                h < high.len(),
                w == high@[h as int],
                c <= 256,
                forall|x: int| 0 <= x < h * 1024 + 4 * c ==> #[trigger] out@[x] == e_mul(seed, eq_at(r@, x as usize)),
            decreases 256 - c,
        {
            let src = [low[4 * c], low[4 * c + 1], low[4 * c + 2], low[4 * c + 3]];
            let p = mul4([w, w, w, w], src);
            for k in 0..4
                invariant
                    n == r.len(),
                    n < 64,
                    hl == n - EQ_LOW_VARS,
                    out.len() == (1usize << n),
                    low.len() == 1024,
                    low.len() == (1usize << EQ_LOW_VARS),
                    high.len() == (1usize << hl),
                    is_eq_table(low@, r_low@, F192::ONE),
                    is_eq_table(high@, r_high@, seed),
                    r_low@ == r@.subrange(0, EQ_LOW_VARS as int),
                    r_high@ == r@.subrange(EQ_LOW_VARS as int, n as int),
                    h < high.len(),
                    w == high@[h as int],
                    c < 256,
                    forall|kk: int| 0 <= kk < 4 ==> #[trigger] p[kk] == e_mul(w, low@[4 * c + kk]),
                    forall|x: int| 0 <= x < h * 1024 + 4 * c + k ==> #[trigger] out@[x] == e_mul(seed, eq_at(r@, x as usize)),
            {
                let l = 4 * c + k;
                proof {
                    lemma_index_split(h, l, EQ_LOW_VARS, n as usize);
                    lemma_tensor_entry(r@, seed, h, l);
                    lemma_e_mul_one(eq_at(r_low@, l));
                }
                out[h * low.len() + l] = p[k];
            }
            c += 1;
        }
        h += 1;
    }
    proof {
        lemma_shl_sum(hl, EQ_LOW_VARS);
    }
}

/// `2^a * 2^b = 2^(a + b)` as shifts.
proof fn lemma_shl_sum(a: usize, b: usize)
    requires
        a + b < 64,
    ensures
        (1usize << a) * (1usize << b) == (1usize << ((a + b) as usize)),
{
    lemma_usize_pow2_no_overflow((a + b) as nat);
    lemma_usize_pow2_no_overflow(a as nat);
    lemma_usize_pow2_no_overflow(b as nat);
    lemma_usize_shl_is_mul(1, a);
    lemma_usize_shl_is_mul(1, b);
    lemma_usize_shl_is_mul(1, (a + b) as usize);
    lemma_pow2_adds(a as nat, b as nat);
}

/// One entry of the tensor pass: `seed eq(r_high, h) * eq(r_low, l) = seed eq(r, h 2^L + l)`.
proof fn lemma_tensor_entry(r: Seq<F192>, seed: F192, h: usize, l: usize)
    requires
        EQ_LOW_VARS <= r.len() < 64,
        l < 1024,
        h < (1usize << ((r.len() - EQ_LOW_VARS) as usize)),
    ensures
        h * 1024 + l < (1usize << r.len()),
        e_mul(e_mul(seed, eq_at(r.subrange(EQ_LOW_VARS as int, r.len() as int), h)), eq_at(r.subrange(0, EQ_LOW_VARS as int), l))
            == e_mul(seed, eq_at(r, (h * 1024 + l) as usize)),
{
    assert((1usize << 10usize) == 1024) by (bit_vector);
    lemma_index_split(h, l, EQ_LOW_VARS, r.len() as usize);
    lemma_eq_at_tensor(r, EQ_LOW_VARS, h, l);
    let (a, b) = (eq_at(r.subrange(0, EQ_LOW_VARS as int), l), eq_at(r.subrange(EQ_LOW_VARS as int, r.len() as int), h));
    lemma_e_mul_assoc(seed, b, a);
    lemma_e_mul_comm(b, a);
}

/// Tables below this size are built on the calling thread.
pub const EQ_PAR_LEN: usize = 1 << 16;

/// The variables of the L1-resident factor of a large `eq` table.
pub const EQ_LOW_VARS: usize = 10;

/// One doubling step on entry `j` of level `i`: the high child `v r_i` and the low child `v + v r_i`.
proof fn lemma_doubling_entry(r: Seq<F192>, seed: F192, j: usize)
    requires
        1 <= r.len() <= 63,
        j < (1usize << ((r.len() - 1) as usize)),
    ensures
        ({
            let v = e_mul(seed, eq_at(r.drop_last(), j));
            &&& e_mul(r.last(), v) == e_mul(seed, eq_at(r, (j + (1usize << ((r.len() - 1) as usize))) as usize))
            &&& e_mul(v, r.last()) == e_mul(seed, eq_at(r, (j + (1usize << ((r.len() - 1) as usize))) as usize))
            &&& e_add(v, e_mul(r.last(), v)) == e_mul(seed, eq_at(r, j))
            &&& e_add(v, e_mul(v, r.last())) == e_mul(seed, eq_at(r, j))
        }),
{
    let e = eq_at(r.drop_last(), j);
    let v = e_mul(seed, e);
    let rk = r.last();
    lemma_eq_at_high(r, j);
    lemma_e_mul_comm(rk, v);
    lemma_e_mul_assoc(seed, e, rk);
    lemma_times_one_plus(v, rk);
    lemma_e_mul_assoc(seed, e, e_add(F192::ONE, rk));
}

/// The level-by-level `eq` build: each level writes the high half from the low half, then rewrites the low half.
///
/// In characteristic 2 the low child is the high child plus the parent, so each pair costs one product.
///
/// Production enumerates `r.iter()`, splits `out[..2 * half]` with `split_at_mut` (and casts the initialized low
/// half from `MaybeUninit`), and walks both halves `as_chunks_mut::<4>` then their tails; the copy indexes
/// `lo[j] = out[j]`, `hi[j] = out[half + j]`, and `l[k] += p[k]` is `out[..] = out[..] + p[k]`.
fn fill_eq_doubling(r: &[F192], seed: F192, out: &mut [F192])
    requires
        r.len() < 64,
        old(out).len() == (1usize << r.len()),
    ensures
        is_eq_table(final(out)@, r@, seed),
{
    let ghost n = r.len();
    proof {
        assert((1usize << n) >= 1) by (bit_vector)
            requires
                n < 64,
        ;
    }
    out[0] = seed;
    proof {
        assert((1usize << 0usize) == 1) by (bit_vector);
        assert(eq_at(r@.subrange(0, 0), 0) == F192::ONE);
        lemma_e_mul_one(seed);
    }
    for i in 0..r.len()
        invariant
            n == r.len(),
            n < 64,
            out.len() == (1usize << n),
            forall|j: int| 0 <= j < (1usize << i) ==> #[trigger] out@[j] == e_mul(seed, eq_at(r@.subrange(0, i as int), j as usize)),
    {
        let rk = r[i];
        let half = 1usize << i;
        let ghost lvl = r@.subrange(0, i as int);
        let ghost nxt = r@.subrange(0, i + 1);
        let ghost before = out@;
        proof {
            lemma_shl_double(i);
            assert((1usize << ((i + 1) as usize)) <= (1usize << n)) by (bit_vector)
                requires
                    i < n,
                    n < 64,
            ;
            assert(nxt.drop_last() =~= lvl);
            assert(nxt.last() == rk);
        }
        let n4 = half / 4;
        let mut c = 0;
        while c < n4
            invariant
                n == r.len(),
                n < 64,
                i < n,
                out.len() == (1usize << n),
                half == (1usize << i),
                2 * half <= out.len(),
                before.len() == out.len(),
                n4 == half / 4,
                c <= n4,
                rk == r@[i as int],
                lvl == r@.subrange(0, i as int),
                nxt == r@.subrange(0, i + 1),
                nxt.drop_last() == lvl,
                nxt.last() == rk,
                forall|j: int| 0 <= j < half ==> #[trigger] before[j] == e_mul(seed, eq_at(lvl, j as usize)),
                forall|j: int| 0 <= j < 4 * c ==> #[trigger] out@[j] == e_mul(seed, eq_at(nxt, j as usize)),
                forall|j: int| 0 <= j < 4 * c ==> #[trigger] out@[half + j] == e_mul(seed, eq_at(nxt, (half + j) as usize)),
                forall|j: int| 4 * c <= j < half ==> #[trigger] out@[j] == before[j],
            decreases n4 - c,
        {
            let l = [out[4 * c], out[4 * c + 1], out[4 * c + 2], out[4 * c + 3]];
            let p = mul4([rk, rk, rk, rk], l);
            for k in 0..4
                invariant
                    n == r.len(),
                    n < 64,
                    i < n,
                    out.len() == (1usize << n),
                    half == (1usize << i),
                    2 * half <= out.len(),
                    before.len() == out.len(),
                    n4 == half / 4,
                    c < n4,
                    rk == r@[i as int],
                    lvl == r@.subrange(0, i as int),
                    nxt == r@.subrange(0, i + 1),
                    nxt.drop_last() == lvl,
                    nxt.last() == rk,
                    forall|kk: int| 0 <= kk < 4 ==> #[trigger] l[kk] == before[4 * c + kk],
                    forall|kk: int| 0 <= kk < 4 ==> #[trigger] p[kk] == e_mul(rk, l[kk]),
                    forall|j: int| 0 <= j < half ==> #[trigger] before[j] == e_mul(seed, eq_at(lvl, j as usize)),
                    forall|j: int| 0 <= j < 4 * c + k ==> #[trigger] out@[j] == e_mul(seed, eq_at(nxt, j as usize)),
                    forall|j: int| 0 <= j < 4 * c + k ==> #[trigger] out@[half + j] == e_mul(seed, eq_at(nxt, (half + j) as usize)),
                    forall|j: int| 4 * c + k <= j < half ==> #[trigger] out@[j] == before[j],
            {
                let j = 4 * c + k;
                proof {
                    lemma_doubling_entry(nxt, seed, j);
                }
                out[half + j] = p[k];
                out[j] = out[j] + p[k];
            }
            c += 1;
        }
        let mut j = 4 * n4;
        while j < half
            invariant
                n == r.len(),
                n < 64,
                i < n,
                out.len() == (1usize << n),
                half == (1usize << i),
                2 * half <= out.len(),
                before.len() == out.len(),
                4 * n4 <= j <= half,
                rk == r@[i as int],
                lvl == r@.subrange(0, i as int),
                nxt == r@.subrange(0, i + 1),
                nxt.drop_last() == lvl,
                nxt.last() == rk,
                forall|jj: int| 0 <= jj < half ==> #[trigger] before[jj] == e_mul(seed, eq_at(lvl, jj as usize)),
                forall|jj: int| 0 <= jj < j ==> #[trigger] out@[jj] == e_mul(seed, eq_at(nxt, jj as usize)),
                forall|jj: int| 0 <= jj < j ==> #[trigger] out@[half + jj] == e_mul(seed, eq_at(nxt, (half + jj) as usize)),
                forall|jj: int| j <= jj < half ==> #[trigger] out@[jj] == before[jj],
            decreases half - j,
        {
            proof {
                lemma_doubling_entry(nxt, seed, j);
            }
            let p = out[j] * rk;
            out[half + j] = p;
            out[j] = out[j] + p;
            j += 1;
        }
        proof {
            assert forall|jj: int| 0 <= jj < (1usize << ((i + 1) as usize)) implies #[trigger] out@[jj] == e_mul(
                seed,
                eq_at(nxt, jj as usize),
            ) by {
                if jj >= half {
                    assert(out@[half + (jj - half)] == e_mul(seed, eq_at(nxt, (half + (jj - half)) as usize)));
                }
            }
        }
    }
    proof {
        assert(r@.subrange(0, n as int) =~= r@);
    }
}

} // verus!
