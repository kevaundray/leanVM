//! The x86-64 kernels of `E = GF(2^192)`: a copy of `crates/primitives/src/field/gf2_64x3/x86_64.rs`.
//!
//! Every kernel is proven to compute what the portable path computes, given the intrinsic specifications of
//! `crate::intrinsics::x86` and `crate::intrinsics::x86_gfx86`: a product's three 128-bit coefficients are the
//! schoolbook's ([`prod_coeffs`]), so they reduce to [`e_mul`]; a lane-wise reduction is [`k_mod`] of each
//! coefficient; a sum of products in registers reduces to the sum of the products.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
use super::Weights8;
use super::{F192, F192Unreduced};
#[cfg(verus_keep_ghost)]
use super::{
    dot_spec, e_add, e_from_k, e_mul, e_value, lemma_e_value_xor, lemma_karatsuba_fold, lemma_mul_base_spec,
    lemma_mul_unreduced_value, lemma_u_from_wide, lemma_u_zero, lemma_wide_split, sched, u_from_wide, u_xor, w8_get,
    wide,
};
#[cfg(verus_keep_ghost)]
use crate::clmul::clmul;
#[cfg(verus_keep_ghost)]
use crate::gf2_64::{k_mod, k_mul, lemma_k_mod, lemma_k_mod_xor, reduce_formula};
use crate::gf2_64::F64;
use core::arch::x86_64::*;
use core::mem::MaybeUninit;
use core::mem::transmute;
use core::ops::{Add, BitXor, BitXorAssign, Mul};
#[cfg(verus_keep_ghost)]
use crate::intrinsics::x86::*;
#[cfg(verus_keep_ghost)]
use crate::intrinsics::x86_gfx86::*;
#[cfg(verus_keep_ghost)]
use vstd::raw_ptr::MemContents;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::maybe_uninit::MaybeUninitAdditionalSpecFns;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specifications
// ---------------------------------------------------------------------------------------------
/// A 128-bit coefficient as its `[low, high]` words.
pub open spec fn split(c: u128) -> [u64; 2] {
    [c as u64, (c >> 64u128) as u64]
}

/// The three y-folded 128-bit coefficients of `a * b`: what the schoolbook `software::mul_unreduced` builds.
pub open spec fn prod_coeffs(a: F192, b: F192) -> [u128; 3] {
    let e = sched(seq![a.c0, a.c1, a.c2], seq![b.c0, b.c1, b.c2], 9);
    [e[0] ^ e[3], e[1] ^ e[3] ^ e[4], e[2] ^ e[4]]
}

/// The unreduced product as [`F192Unreduced`] holds it.
pub open spec fn prod_unreduced(a: F192, b: F192) -> F192Unreduced {
    u_from_wide(prod_coeffs(a, b)[0], prod_coeffs(a, b)[1], prod_coeffs(a, b)[2])
}

/// The unreduced mixed product by `k`: the three coefficients times `k`.
pub open spec fn base_unreduced(a: F192, k: u64) -> F192Unreduced {
    u_from_wide(clmul(a.c0, k as u128), clmul(a.c1, k as u128), clmul(a.c2, k as u128))
}

/// The base-field reduction of `hi * x^64 + lo`.
pub open spec fn reduce_word(lo: u64, hi: u64) -> u64 {
    k_mod(wide([lo, hi]))
}

/// The kernels' shift network on one word pair, with the shifts as the intrinsics specify them:
/// `lo ^ f(hi ^ spill)`, `spill = hi >> 63 ^ hi >> 61 ^ hi >> 60`, `f(v) = v ^ v << 1 ^ v << 3 ^ v << 4`.
pub open spec fn reduce_net(lo: u64, hi: u64) -> u64 {
    let spill = shr_imm(hi, 63) ^ shr_imm(hi, 61) ^ shr_imm(hi, 60);
    let v = hi ^ spill;
    lo ^ ((v ^ shl_imm(v, 1)) ^ (shl_imm(v, 3) ^ shl_imm(v, 4)))
}

// ---------------------------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------------------------
pub proof fn lemma_i64_round_trip(a: u64)
    ensures
        (a as i64) as u64 == a,
{
    assert((a as i64) as u64 == a) by (bit_vector);
}

/// The words of a XOR are the XORs of the words.
pub proof fn lemma_split_xor(x: u128, y: u128)
    ensures
        split(x ^ y)[0] == split(x)[0] ^ split(y)[0],
        split(x ^ y)[1] == split(x)[1] ^ split(y)[1],
{
    assert((x ^ y) as u64 == (x as u64) ^ (y as u64) && ((x ^ y) >> 64u128) as u64 == ((x >> 64u128) as u64) ^ ((y
        >> 64u128) as u64)) by (bit_vector);
}

/// The shift network is the reduction.
pub proof fn lemma_reduce_net(lo: u64, hi: u64)
    ensures
        reduce_net(lo, hi) == reduce_word(lo, hi),
{
    let p = wide([lo, hi]);
    lemma_k_mod(p);
    assert(p == ((hi as u128) << 64u128) | (lo as u128));
    assert(p == ((hi as u128) << 64u128) | (lo as u128) ==> {
        let spill = (hi >> 63u64) ^ (hi >> 61u64) ^ (hi >> 60u64);
        let v = hi ^ spill;
        reduce_formula(p) == lo ^ ((v ^ (v << 1u64)) ^ ((v << 3u64) ^ (v << 4u64)))
    }) by (bit_vector);
}

/// The schoolbook coefficients reduce to the product.
pub proof fn lemma_prod_unreduced(a: F192, b: F192)
    ensures
        e_value(prod_unreduced(a, b)) == e_mul(a, b),
{
    lemma_mul_unreduced_value(a, b);
}

/// The mixed product's coefficients reduce to the product by `k`.
pub proof fn lemma_base_unreduced(a: F192, k: u64)
    ensures
        e_value(base_unreduced(a, k)) == e_mul(a, e_from_k(k)),
{
    lemma_u_from_wide(clmul(a.c0, k as u128), clmul(a.c1, k as u128), clmul(a.c2, k as u128));
    lemma_mul_base_spec(a, k);
}

/// Word `w` of the carry-less product `x * y`.
pub open spec fn cw(x: u64, y: u64, w: int) -> u64 {
    split(clmul(x, y as u128))[w]
}

/// Word `w` of coefficient `k` as Karatsuba's six products and `fold` give it.
pub open spec fn kara_word(a: F192, b: F192, k: int, w: int) -> u64 {
    let p0 = cw(a.c0, b.c0, w);
    let p1 = cw(a.c1, b.c1, w);
    let p2 = cw(a.c2, b.c2, w);
    let p01 = cw(a.c0 ^ a.c1, b.c0 ^ b.c1, w);
    let p02 = cw(a.c0 ^ a.c2, b.c0 ^ b.c2, w);
    let p12 = cw(a.c1 ^ a.c2, b.c1 ^ b.c2, w);
    if k == 0 {
        p0 ^ p12 ^ p1 ^ p2
    } else if k == 1 {
        p0 ^ p12 ^ p01
    } else {
        p0 ^ p1 ^ p02
    }
}

/// Karatsuba's six products give the schoolbook coefficients, word by word.
pub proof fn lemma_karatsuba_words(a: F192, b: F192)
    ensures
        forall|k: int, w: int|
            0 <= k < 3 && 0 <= w < 2 ==> #[trigger] split(prod_coeffs(a, b)[k])[w] == kara_word(a, b, k, w),
{
    lemma_karatsuba_fold(a, b);
    let c = |x: u64, y: u64| clmul(x, y as u128);
    let (p0, p1, p2) = (c(a.c0, b.c0), c(a.c1, b.c1), c(a.c2, b.c2));
    let p01 = c(a.c0 ^ a.c1, b.c0 ^ b.c1);
    let p02 = c(a.c0 ^ a.c2, b.c0 ^ b.c2);
    let p12 = c(a.c1 ^ a.c2, b.c1 ^ b.c2);
    lemma_split_xor(p0, p12);
    lemma_split_xor(p0 ^ p12, p1);
    lemma_split_xor(p0 ^ p12 ^ p1, p2);
    lemma_split_xor(p0 ^ p12, p01);
    lemma_split_xor(p0, p1);
    lemma_split_xor(p0 ^ p1, p02);
}

/// `clmul_words` is the split of the product.
pub proof fn lemma_clmul_words(a: u64, b: u64)
    ensures
        clmul_words(a, b) == split(clmul(a, b as u128)),
{
}

// ---------------------------------------------------------------------------------------------
// The kernels
// ---------------------------------------------------------------------------------------------
/// Two 64-bit words as one register, `lo` in the low qword.
#[inline(always)]
fn pair(lo: u64, hi: u64) -> (r: __m128i)
    ensures
        m128(r)[0] == lo,
        m128(r)[1] == hi,
{
    proof {
        lemma_i64_round_trip(lo);
        lemma_i64_round_trip(hi);
    }
    // SAFETY: SSE2 is part of the x86-64 baseline.
    unsafe { _mm_set_epi64x(hi as i64, lo as i64) }
}

/// The y-folded Karatsuba product of one pair.
///
/// # Safety
///
/// Requires the `pclmulqdq` target feature.
#[inline]
#[target_feature(enable = "pclmulqdq")]
unsafe fn karatsuba(a: F192, b: F192) -> (r: [__m128i; 3])
    ensures
        forall|k: int, w: int| 0 <= k < 3 && 0 <= w < 2 ==> #[trigger] m128(r[k])[w] == split(prod_coeffs(a, b)[k])[w],
{
    proof {
        lemma_clmul_sel();
    }
    // Operand registers, as in the module table.
    let (a01, b01) = (pair(a.c0, a.c1), pair(b.c0, b.c1));
    let (at, bt) = (pair(a.c2, a.c0 ^ a.c1), pair(b.c2, b.c0 ^ b.c1));
    // XOR the broadcast c2 into both qwords of r01.
    let a_s = _mm_xor_si128(a01, _mm_unpacklo_epi64(at, at));
    let b_s = _mm_xor_si128(b01, _mm_unpacklo_epi64(bt, bt));
    // The six base products, two per register pair.
    let p0 = _mm_clmulepi64_si128::<0x00>(a01, b01);
    let p1 = _mm_clmulepi64_si128::<0x11>(a01, b01);
    let p02 = _mm_clmulepi64_si128::<0x00>(a_s, b_s);
    let p12 = _mm_clmulepi64_si128::<0x11>(a_s, b_s);
    let p2 = _mm_clmulepi64_si128::<0x00>(at, bt);
    let p01 = _mm_clmulepi64_si128::<0x11>(at, bt);
    proof {
        lemma_karatsuba_words(a, b);
        assert(m128(a_s)[0] == a.c0 ^ a.c2 && m128(a_s)[1] == a.c1 ^ a.c2);
        assert(m128(b_s)[0] == b.c0 ^ b.c2 && m128(b_s)[1] == b.c1 ^ b.c2);
        lemma_clmul_words(a.c0, b.c0);
        lemma_clmul_words(a.c1, b.c1);
        lemma_clmul_words(a.c2, b.c2);
        lemma_clmul_words(a.c0 ^ a.c1, b.c0 ^ b.c1);
        lemma_clmul_words(a.c0 ^ a.c2, b.c0 ^ b.c2);
        lemma_clmul_words(a.c1 ^ a.c2, b.c1 ^ b.c2);
    }
    let xor = |x: __m128i, y: __m128i| -> (z: __m128i)
        ensures
            forall|i: int| 0 <= i < 2 ==> #[trigger] m128(z)[i] == m128(x)[i] ^ m128(y)[i],
        { _mm_xor_si128(x, y) };
    let r = fold(p0, p1, p2, p01, p02, p12, xor);
    proof {
        lemma_fold(xor, |v: __m128i| m128(v)@, 2, p0, p1, p2, p01, p02, p12, r);
        assert forall|k: int, w: int| 0 <= k < 3 && 0 <= w < 2 implies #[trigger] m128(r[k])[w] == split(
            prod_coeffs(a, b)[k],
        )[w] by {
            assert(m128(p0)[w] == cw(a.c0, b.c0, w));
            assert(m128(p1)[w] == cw(a.c1, b.c1, w));
            assert(m128(p2)[w] == cw(a.c2, b.c2, w));
            assert(m128(p01)[w] == cw(a.c0 ^ a.c1, b.c0 ^ b.c1, w));
            assert(m128(p02)[w] == cw(a.c0 ^ a.c2, b.c0 ^ b.c2, w));
            assert(m128(p12)[w] == cw(a.c1 ^ a.c2, b.c1 ^ b.c2, w));
            assert(m128(r[k])[w] == kara_word(a, b, k, w));
        }
    }
    r
}

/// Karatsuba recombination and y-fold in one step, for any register width.
///
/// Composing the two linear maps leaves a short XOR network:
///
/// ```text
///     d0 = p0 ^ p1 ^ p2 ^ p12
///     d1 = p0 ^ p01 ^ p12
///     d2 = p0 ^ p1 ^ p02
/// ```
///
/// Rewritten for Verus: the two inner XORs are bound to names (`t`, `u`), which the specification quantifies over.
#[inline(always)]
fn fold<V: Copy>(p0: V, p1: V, p2: V, p01: V, p02: V, p12: V, xor: impl Fn(V, V) -> V) -> (r: [V; 3])
    requires
        forall|x: V, y: V| #[trigger] xor.requires((x, y)),
    ensures
        fold_post(xor, p0, p1, p2, p01, p02, p12, r),
{
    // Shared by d0 and d1.
    let q = xor(p0, p12);
    let t = xor(q, p1);
    let u = xor(p0, p1);
    [xor(t, p2), xor(q, p01), xor(u, p02)]
}

/// [`fold`]'s result: its six XORs, as `xor` specifies them.
pub open spec fn fold_post<V, F: Fn(V, V) -> V>(xor: F, p0: V, p1: V, p2: V, p01: V, p02: V, p12: V, r: [V; 3]) -> bool {
    exists|q: V, t: V, u: V|
        {
            &&& #[trigger] xor.ensures((p0, p12), q)
            &&& #[trigger] xor.ensures((q, p1), t)
            &&& xor.ensures((t, p2), r[0])
            &&& xor.ensures((q, p01), r[1])
            &&& #[trigger] xor.ensures((p0, p1), u)
            &&& xor.ensures((u, p02), r[2])
        }
}

/// `xor` XORs the first `n` words of the `view` of its operands.
pub open spec fn xors_words<V, F: Fn(V, V) -> V>(xor: F, view: spec_fn(V) -> Seq<u64>, n: int) -> bool {
    forall|x: V, y: V, z: V, i: int|
        #![trigger xor.ensures((x, y), z), view(z)[i]]
        xor.ensures((x, y), z) && 0 <= i < n ==> view(z)[i] == view(x)[i] ^ view(y)[i]
}

/// [`fold`] word by word, for a word-wise XOR.
pub proof fn lemma_fold<V, F: Fn(V, V) -> V>(
    xor: F,
    view: spec_fn(V) -> Seq<u64>,
    n: int,
    p0: V,
    p1: V,
    p2: V,
    p01: V,
    p02: V,
    p12: V,
    r: [V; 3],
)
    requires
        xors_words(xor, view, n),
        fold_post(xor, p0, p1, p2, p01, p02, p12, r),
    ensures
        forall|i: int| 0 <= i < n ==> #[trigger] view(r[0])[i] == view(p0)[i] ^ view(p12)[i] ^ view(p1)[i] ^ view(p2)[i],
        forall|i: int| 0 <= i < n ==> #[trigger] view(r[1])[i] == view(p0)[i] ^ view(p12)[i] ^ view(p01)[i],
        forall|i: int| 0 <= i < n ==> #[trigger] view(r[2])[i] == view(p0)[i] ^ view(p1)[i] ^ view(p02)[i],
{
    let (q, t, u) = choose|q: V, t: V, u: V|
        {
            &&& #[trigger] xor.ensures((p0, p12), q)
            &&& #[trigger] xor.ensures((q, p1), t)
            &&& xor.ensures((t, p2), r[0])
            &&& xor.ensures((q, p01), r[1])
            &&& #[trigger] xor.ensures((p0, p1), u)
            &&& xor.ensures((u, p02), r[2])
        };
    assert forall|i: int| 0 <= i < n implies {
        &&& #[trigger] view(r[0])[i] == view(p0)[i] ^ view(p12)[i] ^ view(p1)[i] ^ view(p2)[i]
        &&& view(r[1])[i] == view(p0)[i] ^ view(p12)[i] ^ view(p01)[i]
        &&& view(r[2])[i] == view(p0)[i] ^ view(p1)[i] ^ view(p02)[i]
    } by {
        assert(view(q)[i] == view(p0)[i] ^ view(p12)[i]);
        assert(view(t)[i] == view(q)[i] ^ view(p1)[i]);
        assert(view(u)[i] == view(p0)[i] ^ view(p1)[i]);
    }
}

/// One unreduced product.
///
/// Rewritten for Verus: production maps the reinterpret over the three registers.
///
/// # Safety
///
/// Requires the `pclmulqdq` target feature.
#[inline]
#[target_feature(enable = "pclmulqdq")]
pub unsafe fn mul_unreduced(a: F192, b: F192) -> (r: F192Unreduced)
    ensures
        r == prod_unreduced(a, b),
        e_value(r) == e_mul(a, b),
{
    // SAFETY: the function carries pclmulqdq; the reinterprets are between 128-bit values.
    unsafe {
        let d = karatsuba(a, b);
        let r = F192Unreduced {
            coeffs: [
                transmute::<__m128i, [u64; 2]>(d[0]),
                transmute::<__m128i, [u64; 2]>(d[1]),
                transmute::<__m128i, [u64; 2]>(d[2]),
            ],
        };
        proof {
            assert(r == regs128(d));
            lemma_regs128(d, prod_coeffs(a, b));
            lemma_prod_unreduced(a, b);
        }
        r
    }
}

/// The unreduced value three 128-bit registers hold, one coefficient each.
pub open spec fn regs128(d: [__m128i; 3]) -> F192Unreduced {
    F192Unreduced { coeffs: [m128(d[0]), m128(d[1]), m128(d[2])] }
}

/// Registers holding the words of three coefficients hold their unreduced value.
pub proof fn lemma_regs128(d: [__m128i; 3], c: [u128; 3])
    requires
        forall|k: int, w: int| 0 <= k < 3 && 0 <= w < 2 ==> #[trigger] m128(d[k])[w] == split(c[k])[w],
    ensures
        regs128(d) == u_from_wide(c[0], c[1], c[2]),
{
    let u = u_from_wide(c[0], c[1], c[2]);
    assert forall|k: int| 0 <= k < 3 implies #[trigger] regs128(d).coeffs[k] == u.coeffs[k] by {
        assert(m128(d[k])[0] == split(c[k])[0]);
        assert(m128(d[k])[1] == split(c[k])[1]);
        assert(regs128(d).coeffs[k] =~= u.coeffs[k]);
    }
    assert(regs128(d).coeffs =~= u.coeffs);
}

/// One unreduced mixed product: three base products from two operand registers.
///
/// Rewritten for Verus: production maps the reinterpret over the three registers.
///
/// # Safety
///
/// Requires the `pclmulqdq` target feature.
#[inline]
#[target_feature(enable = "pclmulqdq")]
pub unsafe fn mul_base_unreduced(a: F192, k: F64) -> (r: F192Unreduced)
    ensures
        r == base_unreduced(a, k.0),
        e_value(r) == e_mul(a, e_from_k(k.0)),
{
    let ghost k0 = k.0;
    proof {
        lemma_clmul_sel();
        lemma_i64_round_trip(a.c2);
        lemma_i64_round_trip(k.0);
    }
    // [c0, c1] and [c2, 0] against [k, 0].
    let a01 = pair(a.c0, a.c1);
    let a2 = _mm_cvtsi64_si128(a.c2 as i64);
    let k = _mm_cvtsi64_si128(k.0 as i64);
    // Immediate 0x01 multiplies the high qword of the first operand by the low qword of the second.
    let products = [
        _mm_clmulepi64_si128::<0x00>(a01, k),
        _mm_clmulepi64_si128::<0x01>(a01, k),
        _mm_clmulepi64_si128::<0x00>(a2, k),
    ];
    // SAFETY: the reinterprets are between 128-bit values.
    unsafe {
        let r = F192Unreduced {
            coeffs: [
                transmute::<__m128i, [u64; 2]>(products[0]),
                transmute::<__m128i, [u64; 2]>(products[1]),
                transmute::<__m128i, [u64; 2]>(products[2]),
            ],
        };
        proof {
            lemma_clmul_words(a.c0, k0);
            lemma_clmul_words(a.c1, k0);
            lemma_clmul_words(a.c2, k0);
            let c = [clmul(a.c0, k0 as u128), clmul(a.c1, k0 as u128), clmul(a.c2, k0 as u128)];
            assert forall|j: int, w: int| 0 <= j < 3 && 0 <= w < 2 implies #[trigger] m128(products[j])[w] == split(
                c[j],
            )[w] by {}
            assert(r == regs128(products));
            lemma_regs128(products, c);
            lemma_base_unreduced(a, k0);
        }
        r
    }
}

/// The batched kernels' lane-wise reduction on one register: qword `i` of the result is the
/// reduction of `hi[i] * x^64 + lo[i]`.
#[inline(always)]
fn reduce_lanes128(lo: __m128i, hi: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] m128(r)[i] == reduce_word(m128(lo)[i], m128(hi)[i]),
{
    // SAFETY: SSE2 is part of the x86-64 baseline.
    unsafe {
        let spill = _mm_xor_si128(
            _mm_xor_si128(_mm_srli_epi64::<63>(hi), _mm_srli_epi64::<61>(hi)),
            _mm_srli_epi64::<60>(hi),
        );
        let v = _mm_xor_si128(hi, spill);
        let f = _mm_xor_si128(
            _mm_xor_si128(v, _mm_slli_epi64::<1>(v)),
            _mm_xor_si128(_mm_slli_epi64::<3>(v), _mm_slli_epi64::<4>(v)),
        );
        let r = _mm_xor_si128(lo, f);
        proof {
            assert forall|i: int| 0 <= i < 2 implies #[trigger] m128(r)[i] == reduce_word(m128(lo)[i], m128(hi)[i]) by {
                lemma_reduce_net(m128(lo)[i], m128(hi)[i]);
            }
        }
        r
    }
}

/// `_mm*_shuffle_epi32::<0x4E>` swaps the two words of every 128-bit lane.
pub proof fn lemma_swap_words(a: Seq<u64>, i: int)
    requires
        0 <= i < a.len(),
        a.len() % 2 == 0,
    ensures
        shuffle_epi32_lane(a, 0x4Ei32 as u8, i) == if i % 2 == 0 {
            a[i + 1]
        } else {
            a[i - 1]
        },
{
    assert(((0x4Eu8 >> 0u8) & 3) == 2 && ((0x4Eu8 >> 2u8) & 3) == 3 && ((0x4Eu8 >> 4u8) & 3) == 0 && ((0x4Eu8 >> 6u8)
        & 3) == 1) by (bit_vector);
    let (x, y) = (a[2 * (i / 2)], a[2 * (i / 2) + 1]);
    assert(((x >> 0u64) & 0xFFFF_FFFFu64) | (((x >> 32u64) & 0xFFFF_FFFFu64) << 32u64) == x) by (bit_vector);
    assert(((y >> 0u64) & 0xFFFF_FFFFu64) | (((y >> 32u64) & 0xFFFF_FFFFu64) << 32u64) == y) by (bit_vector);
}

/// One element in two registers, `[c0, c1]` and `[c2, c2]`, for a kernel whose values stay
/// there from load to store, as the aarch64 kernels' `F192x1`; for x86 without the wide
/// CLMUL, where the batched products leave no lanes to fill.
///
/// An [`F192`] is three integer words: its sums run on the integer side, and every product
/// moves its operands over and reduces its result there. These sums, products and reductions
/// stay in vector registers.
#[derive(Clone, Copy)]
pub struct F192x1 {
    c01: __m128i,
    c22: __m128i,
}

/// An unreduced product of [`F192x1`] values, or a sum of them: its three 128-bit coefficients
/// in registers.
#[derive(Clone, Copy)]
pub struct F192x1Unreduced([__m128i; 3]);

impl F192x1 {
    /// The two words of `c22` are both `c2`.
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        m128(self.c22)[0] == m128(self.c22)[1]
    }

    /// The element held.
    pub closed spec fn elem(self) -> F192 {
        F192 { c0: m128(self.c01)[0], c1: m128(self.c01)[1], c2: m128(self.c22)[0] }
    }

    #[inline(always)]
    pub fn new(e: F192) -> (r: Self)
        ensures
            r.elem() == e,
    {
        proof {
            lemma_i64_round_trip(e.c2);
        }
        // SAFETY: SSE2 is part of the x86-64 baseline.
        Self { c01: pair(e.c0, e.c1), c22: unsafe { _mm_set1_epi64x(e.c2 as i64) } }
    }

    /// The element at `e`, loaded into its registers.
    ///
    /// Rewritten for Verus: the loads through the cast pointer are the helpers [`load_c01`] and [`load_c2`].
    #[inline(always)]
    pub fn load(e: &F192) -> (r: Self)
        ensures
            r.elem() == *e,
    {
        let w2 = load_c2(e);
        proof {
            lemma_i64_round_trip(w2);
        }
        // SAFETY: `e` is three words, `c0` and `c1` adjacent under `repr(C)`.
        unsafe { Self { c01: load_c01(e), c22: _mm_set1_epi64x(w2 as i64) } }
    }

    /// Write the element to `out`, which need not be initialized.
    ///
    /// Rewritten for Verus: the two stores through the cast pointer are the helper [`store_c01_c2`].
    #[inline(always)]
    pub fn store(self, out: &mut MaybeUninit<F192>)
        ensures
            final(out).mem_contents() == MemContents::Init(self.elem()),
    {
        store_c01_c2(self.c01, self.c22, out);
    }

    /// The product without the reduction, Karatsuba's six from the registers.
    ///
    /// Rewritten for Verus: the six products and the XOR closure are bound to names before `fold`.
    #[inline(always)]
    pub fn mul_unreduced(self, rhs: Self) -> (r: F192x1Unreduced)
        ensures
            r.unreduced() == prod_unreduced(self.elem(), rhs.elem()),
            e_value(r.unreduced()) == e_mul(self.elem(), rhs.elem()),
    {
        proof {
            use_type_invariant(&self);
            use_type_invariant(&rhs);
            lemma_clmul_sel();
        }
        let ((a01, a22), (b01, b22)) = ((self.c01, self.c22), (rhs.c01, rhs.c22));
        // SAFETY: the module's cfg enables pclmulqdq; the rest is SSE2.
        unsafe {
            // `[c0 + c2, c1 + c2]`, and `c0 + c1` in both qwords.
            let (a_s, b_s) = (_mm_xor_si128(a01, a22), _mm_xor_si128(b01, b22));
            let a_x = _mm_xor_si128(a01, _mm_shuffle_epi32::<0x4E>(a01));
            let b_x = _mm_xor_si128(b01, _mm_shuffle_epi32::<0x4E>(b01));
            let p0 = _mm_clmulepi64_si128::<0x00>(a01, b01);
            let p1 = _mm_clmulepi64_si128::<0x11>(a01, b01);
            let p2 = _mm_clmulepi64_si128::<0x00>(a22, b22);
            let p01 = _mm_clmulepi64_si128::<0x00>(a_x, b_x);
            let p02 = _mm_clmulepi64_si128::<0x00>(a_s, b_s);
            let p12 = _mm_clmulepi64_si128::<0x11>(a_s, b_s);
            let xor = |x: __m128i, y: __m128i| -> (z: __m128i)
                ensures
                    forall|i: int| 0 <= i < 2 ==> #[trigger] m128(z)[i] == m128(x)[i] ^ m128(y)[i],
                { _mm_xor_si128(x, y) };
            let d = fold(p0, p1, p2, p01, p02, p12, xor);
            proof {
                let (a, b) = (self.elem(), rhs.elem());
                lemma_swap_words(m128(a01)@, 0);
                lemma_swap_words(m128(b01)@, 0);
                assert(m128(a_x)[0] == a.c0 ^ a.c1 && m128(b_x)[0] == b.c0 ^ b.c1);
                lemma_fold(xor, |v: __m128i| m128(v)@, 2, p0, p1, p2, p01, p02, p12, d);
                lemma_karatsuba_words(a, b);
                lemma_clmul_words(a.c0, b.c0);
                lemma_clmul_words(a.c1, b.c1);
                lemma_clmul_words(a.c2, b.c2);
                lemma_clmul_words(a.c0 ^ a.c1, b.c0 ^ b.c1);
                lemma_clmul_words(a.c0 ^ a.c2, b.c0 ^ b.c2);
                lemma_clmul_words(a.c1 ^ a.c2, b.c1 ^ b.c2);
                assert forall|k: int, w: int| 0 <= k < 3 && 0 <= w < 2 implies #[trigger] m128(d[k])[w] == split(
                    prod_coeffs(a, b)[k],
                )[w] by {
                    assert(m128(p0)[w] == cw(a.c0, b.c0, w));
                    assert(m128(p1)[w] == cw(a.c1, b.c1, w));
                    assert(m128(p2)[w] == cw(a.c2, b.c2, w));
                    assert(m128(p01)[w] == cw(a.c0 ^ a.c1, b.c0 ^ b.c1, w));
                    assert(m128(p02)[w] == cw(a.c0 ^ a.c2, b.c0 ^ b.c2, w));
                    assert(m128(p12)[w] == cw(a.c1 ^ a.c2, b.c1 ^ b.c2, w));
                    assert(m128(d[k])[w] == kara_word(a, b, k, w));
                }
                lemma_regs128(d, prod_coeffs(a, b));
                lemma_prod_unreduced(a, b);
            }
            F192x1Unreduced(d)
        }
    }

    /// The mixed product by a base-field scalar, without the reduction.
    #[inline(always)]
    pub fn mul_base_unreduced(self, k: F64) -> (r: F192x1Unreduced)
        ensures
            r.unreduced() == base_unreduced(self.elem(), k.0),
            e_value(r.unreduced()) == e_mul(self.elem(), e_from_k(k.0)),
    {
        let ghost k0 = k.0;
        proof {
            use_type_invariant(&self);
            lemma_clmul_sel();
            lemma_i64_round_trip(k.0);
        }
        // SAFETY: the module's cfg enables pclmulqdq; the rest is SSE2.
        unsafe {
            let k = _mm_cvtsi64_si128(k.0 as i64);
            let r = F192x1Unreduced([
                _mm_clmulepi64_si128::<0x00>(self.c01, k),
                _mm_clmulepi64_si128::<0x01>(self.c01, k),
                _mm_clmulepi64_si128::<0x00>(self.c22, k),
            ]);
            proof {
                let a = self.elem();
                lemma_clmul_words(a.c0, k0);
                lemma_clmul_words(a.c1, k0);
                lemma_clmul_words(a.c2, k0);
                let c = [clmul(a.c0, k0 as u128), clmul(a.c1, k0 as u128), clmul(a.c2, k0 as u128)];
                assert forall|j: int, w: int| 0 <= j < 3 && 0 <= w < 2 implies #[trigger] m128(r.0[j])[w] == split(
                    c[j],
                )[w] by {}
                lemma_regs128(r.0, c);
                lemma_base_unreduced(a, k0);
            }
            r
        }
    }
}

/// The element at `e`'s first two words in one register.
///
/// Trusted (`external_body`): the body is production's load; `tests/equivalence/gf2_64x3.rs` checks it.
#[verifier::external_body]
#[inline(always)]
pub fn load_c01(e: &F192) -> (r: __m128i)
    ensures
        m128(r)[0] == e.c0,
        m128(r)[1] == e.c1,
{
    let words = (e as *const F192).cast::<u64>();
    // SAFETY: `e` is three words, `c0` and `c1` adjacent under `repr(C)`.
    unsafe { _mm_loadu_si128(words.cast()) }
}

/// The element at `e`'s third word.
///
/// Trusted (`external_body`): the body is production's read; `tests/equivalence/gf2_64x3.rs` checks it.
#[verifier::external_body]
#[inline(always)]
pub fn load_c2(e: &F192) -> (r: u64)
    ensures
        r == e.c2,
{
    let words = (e as *const F192).cast::<u64>();
    // SAFETY: `e` is three words.
    unsafe { *words.add(2) }
}

/// Store `[c0, c1]` and the low word of `c22` as the three words of `out`.
///
/// Trusted (`external_body`): the body is production's two stores; `tests/equivalence/gf2_64x3.rs` checks it.
#[verifier::external_body]
#[inline(always)]
pub fn store_c01_c2(c01: __m128i, c22: __m128i, out: &mut MaybeUninit<F192>)
    ensures
        final(out).mem_contents() == MemContents::Init(F192 { c0: m128(c01)[0], c1: m128(c01)[1], c2: m128(c22)[0] }),
{
    let words = out.as_mut_ptr().cast::<u64>();
    // SAFETY: `out` is three words, `c0` and `c1` adjacent under `repr(C)`.
    unsafe {
        _mm_storeu_si128(words.cast(), c01);
        _mm_storel_epi64(words.add(2).cast(), c22);
    }
}

// The operator traits' Verus specifications: no closed form for the registers' bits, so each impl's own `ensures`
// states its result (for the conversions, the value held).
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl for F192x1 {
    open spec fn obeys_add_spec() -> bool {
        false
    }

    open spec fn add_req(self, rhs: F192x1) -> bool {
        true
    }

    open spec fn add_spec(self, rhs: F192x1) -> F192x1 {
        self
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl for F192x1 {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: F192x1) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: F192x1) -> F192x1 {
        self
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::BitXorSpecImpl for F192x1Unreduced {
    open spec fn obeys_bitxor_spec() -> bool {
        false
    }

    open spec fn bitxor_req(self, rhs: F192x1Unreduced) -> bool {
        true
    }

    open spec fn bitxor_spec(self, rhs: F192x1Unreduced) -> F192x1Unreduced {
        self
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::BitXorAssignSpecImpl for F192x1Unreduced {
    open spec fn obeys_bitxor_assign_spec() -> bool {
        false
    }

    open spec fn bitxor_assign_req(&self, rhs: F192x1Unreduced) -> bool {
        true
    }

    open spec fn bitxor_assign_spec(&self, rhs: F192x1Unreduced) -> &F192x1Unreduced {
        self
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<F192x1Unreduced> for F192Unreduced {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(u: F192x1Unreduced) -> F192Unreduced {
        u.unreduced()
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<F192x1> for F192 {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(e: F192x1) -> F192 {
        e.elem()
    }
}

impl Add for F192x1 {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: Self) -> (r: Self)
        ensures
            r.elem() == e_add(self.elem(), rhs.elem()),
    {
        proof {
            use_type_invariant(&self);
            use_type_invariant(&rhs);
        }
        // SAFETY: SSE2 is part of the x86-64 baseline.
        unsafe { Self { c01: _mm_xor_si128(self.c01, rhs.c01), c22: _mm_xor_si128(self.c22, rhs.c22) } }
    }
}

impl Mul for F192x1 {
    type Output = Self;

    #[inline(always)]
    fn mul(self, rhs: Self) -> (r: Self)
        ensures
            r.elem() == e_mul(self.elem(), rhs.elem()),
    {
        self.mul_unreduced(rhs).reduce()
    }
}

impl F192x1Unreduced {
    /// The unreduced value held.
    pub closed spec fn unreduced(self) -> F192Unreduced {
        regs128(self.0)
    }

    #[inline(always)]
    pub fn zero() -> (r: Self)
        ensures
            r.unreduced() == F192Unreduced::ZERO,
    {
        // SAFETY: SSE2 is part of the x86-64 baseline.
        let r = Self([unsafe { _mm_setzero_si128() }; 3]);
        proof {
            assert(r.unreduced().coeffs[0] =~= F192Unreduced::ZERO.coeffs[0]);
            assert(r.unreduced().coeffs[1] =~= F192Unreduced::ZERO.coeffs[1]);
            assert(r.unreduced().coeffs[2] =~= F192Unreduced::ZERO.coeffs[2]);
            assert(r.unreduced().coeffs =~= F192Unreduced::ZERO.coeffs);
        }
        r
    }

    /// Reduce each coefficient, into the element's two registers.
    ///
    /// Rewritten for Verus: the array pattern `let [d0, d1, d2]` becomes indexing.
    #[inline(always)]
    pub fn reduce(self) -> (r: F192x1)
        ensures
            r.elem() == e_value(self.unreduced()),
    {
        let (d0, d1, d2) = (self.0[0], self.0[1], self.0[2]);
        // SAFETY: SSE2 is part of the x86-64 baseline.
        unsafe {
            F192x1 {
                c01: reduce_lanes128(_mm_unpacklo_epi64(d0, d1), _mm_unpackhi_epi64(d0, d1)),
                c22: reduce_lanes128(_mm_unpacklo_epi64(d2, d2), _mm_unpackhi_epi64(d2, d2)),
            }
        }
    }
}

impl BitXor for F192x1Unreduced {
    type Output = Self;

    /// Rewritten for Verus: the array patterns become indexing.
    #[inline(always)]
    fn bitxor(self, rhs: Self) -> (r: Self)
        ensures
            r.unreduced() == u_xor(self.unreduced(), rhs.unreduced()),
    {
        let ((a0, a1, a2), (b0, b1, b2)) = ((self.0[0], self.0[1], self.0[2]), (rhs.0[0], rhs.0[1], rhs.0[2]));
        // SAFETY: SSE2 is part of the x86-64 baseline.
        let r = unsafe { Self([_mm_xor_si128(a0, b0), _mm_xor_si128(a1, b1), _mm_xor_si128(a2, b2)]) };
        proof {
            let (u, v) = (self.unreduced(), rhs.unreduced());
            assert(r.unreduced().coeffs[0] =~= u_xor(u, v).coeffs[0]);
            assert(r.unreduced().coeffs[1] =~= u_xor(u, v).coeffs[1]);
            assert(r.unreduced().coeffs[2] =~= u_xor(u, v).coeffs[2]);
            assert(r.unreduced().coeffs =~= u_xor(u, v).coeffs);
        }
        r
    }
}

impl BitXorAssign for F192x1Unreduced {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self)
        ensures
            final(self).unreduced() == u_xor(old(self).unreduced(), rhs.unreduced()),
    {
        *self = *self ^ rhs;
    }
}

impl From<F192x1Unreduced> for F192Unreduced {
    /// Rewritten for Verus: production maps the reinterpret over the three registers.
    #[inline(always)]
    fn from(u: F192x1Unreduced) -> (r: Self)
        ensures
            r == u.unreduced(),
    {
        Self {
            // SAFETY: the reinterprets are between 128-bit values.
            coeffs: unsafe {
                [
                    transmute::<__m128i, [u64; 2]>(u.0[0]),
                    transmute::<__m128i, [u64; 2]>(u.0[1]),
                    transmute::<__m128i, [u64; 2]>(u.0[2]),
                ]
            },
        }
    }
}

impl From<F192x1> for F192 {
    /// Rewritten for Verus: the array patterns become indexing.
    #[inline(always)]
    fn from(e: F192x1) -> (r: Self)
        ensures
            r == e.elem(),
    {
        // SAFETY: the reinterprets are between 128-bit values.
        let (w01, w22) = unsafe {
            (transmute::<__m128i, [u64; 2]>(e.c01), transmute::<__m128i, [u64; 2]>(e.c22))
        };
        let (c0, c1, c2) = (w01[0], w01[1], w22[0]);
        Self::new(c0, c1, c2)
    }
}

// ---------------------------------------------------------------------------------------------
// Batched products: one product per 128-bit lane
// ---------------------------------------------------------------------------------------------
/// The extract immediate 1 selects the upper half.
pub proof fn lemma_imm_one()
    ensures
        (1i32 as u8 & 1u8) == 1,
        (0i32 as u8 & 1u8) == 0,
{
    assert((1u8 & 1u8) == 1 && (0u8 & 1u8) == 0) by (bit_vector);
}

/// Every word of a PCLMULQDQ lane is a word of [`cw`].
pub proof fn lemma_cw_all()
    ensures
        forall|a: u64, b: u64, w: int| 0 <= w < 2 ==> #[trigger] clmul_words(a, b)[w] == cw(a, b, w),
{
}

/// The reduced product's coefficients are the reductions of the schoolbook words.
pub proof fn lemma_coeffs_reduce(a: F192, b: F192)
    ensures
        ({
            let pc = prod_coeffs(a, b);
            e_mul(a, b) == F192 {
                c0: reduce_word(split(pc[0])[0], split(pc[0])[1]),
                c1: reduce_word(split(pc[1])[0], split(pc[1])[1]),
                c2: reduce_word(split(pc[2])[0], split(pc[2])[1]),
            }
        }),
{
    lemma_prod_unreduced(a, b);
    let pc = prod_coeffs(a, b);
    assert([split(pc[0])[0], split(pc[0])[1]] =~= prod_unreduced(a, b).coeffs[0]);
    assert([split(pc[1])[0], split(pc[1])[1]] =~= prod_unreduced(a, b).coeffs[1]);
    assert([split(pc[2])[0], split(pc[2])[1]] =~= prod_unreduced(a, b).coeffs[2]);
}

/// Lane-wise base reduction: qword `i` of the result is the reduction of `hi[i] * x^64 + lo[i]`.
///
/// The same shift network as the scalar reduction, applied to every qword at once.
///
/// # Safety
///
/// Requires the `avx2` target feature.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn reduce_lanes256(lo: __m256i, hi: __m256i) -> (r: __m256i)
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == reduce_word(m256(lo)[i], m256(hi)[i]),
{
    // The bits of `hi * 0x1B` shifted past x^63.
    let spill = _mm256_xor_si256(
        _mm256_xor_si256(_mm256_srli_epi64::<63>(hi), _mm256_srli_epi64::<61>(hi)),
        _mm256_srli_epi64::<60>(hi),
    );
    // lo ^ f(hi ^ spill), with f(v) = v ^ v<<1 ^ v<<3 ^ v<<4.
    let v = _mm256_xor_si256(hi, spill);
    let f = _mm256_xor_si256(
        _mm256_xor_si256(v, _mm256_slli_epi64::<1>(v)),
        _mm256_xor_si256(_mm256_slli_epi64::<3>(v), _mm256_slli_epi64::<4>(v)),
    );
    let r = _mm256_xor_si256(lo, f);
    proof {
        assert forall|i: int| 0 <= i < 4 implies #[trigger] m256(r)[i] == reduce_word(m256(lo)[i], m256(hi)[i]) by {
            lemma_reduce_net(m256(lo)[i], m256(hi)[i]);
        }
    }
    r
}

/// Lane-wise base reduction on eight qwords; see the four-qword version.
///
/// # Safety
///
/// Requires the `avx512f` target feature.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn reduce_lanes512(lo: __m512i, hi: __m512i) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == reduce_word(m512(lo)[i], m512(hi)[i]),
{
    // The bits of `hi * 0x1B` shifted past x^63.
    let spill = _mm512_xor_si512(
        _mm512_xor_si512(_mm512_srli_epi64::<63>(hi), _mm512_srli_epi64::<61>(hi)),
        _mm512_srli_epi64::<60>(hi),
    );
    // lo ^ f(hi ^ spill), with f(v) = v ^ v<<1 ^ v<<3 ^ v<<4.
    let v = _mm512_xor_si512(hi, spill);
    let f = _mm512_xor_si512(
        _mm512_xor_si512(v, _mm512_slli_epi64::<1>(v)),
        _mm512_xor_si512(_mm512_slli_epi64::<3>(v), _mm512_slli_epi64::<4>(v)),
    );
    let r = _mm512_xor_si512(lo, f);
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] m512(r)[i] == reduce_word(m512(lo)[i], m512(hi)[i]) by {
            lemma_reduce_net(m512(lo)[i], m512(hi)[i]);
        }
    }
    r
}

/// The y-folded Karatsuba products of two pairs, one pair per 128-bit lane.
///
/// Rewritten for Verus: `a.map(|e| e.c0)` and the like become array literals; the closures carry their
/// specifications; the six products are bound to names before `fold`.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
unsafe fn karatsuba_vec2(a: [F192; 2], b: [F192; 2]) -> (r: [__m256i; 3])
    ensures
        forall|k: int, i: int|
            0 <= k < 3 && 0 <= i < 4 ==> #[trigger] m256(r[k])[i] == split(prod_coeffs(a[i / 2], b[i / 2])[k])[i % 2],
{
    // One coefficient of both elements, in the low qword of each lane.
    let pack = |c: [u64; 2]| -> (r: __m256i)
        ensures
            m256(r)[0] == c[0] && m256(r)[1] == 0 && m256(r)[2] == c[1] && m256(r)[3] == 0,
        {
            proof {
                lemma_i64_round_trip(c[0]);
                lemma_i64_round_trip(c[1]);
            }
            _mm256_set_epi64x(0, c[1] as i64, 0, c[0] as i64)
        };
    let (a0, a1, a2) = (pack([a[0].c0, a[1].c0]), pack([a[0].c1, a[1].c1]), pack([a[0].c2, a[1].c2]));
    let (b0, b1, b2) = (pack([b[0].c0, b[1].c0]), pack([b[0].c1, b[1].c1]), pack([b[0].c2, b[1].c2]));
    // One instruction per base product covers both lanes.
    let mul = |x: __m256i, y: __m256i| -> (r: __m256i)
        ensures
            forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == cw(m256(x)[2 * (i / 2)], m256(y)[2 * (i / 2)], i % 2),
        {
            proof {
                lemma_clmul_sel();
                lemma_cw_all();
            }
            _mm256_clmulepi64_epi128::<0x00>(x, y)
        };
    let xor = |x: __m256i, y: __m256i| -> (r: __m256i)
        ensures
            forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == m256(x)[i] ^ m256(y)[i],
        { _mm256_xor_si256(x, y) };
    let p0 = mul(a0, b0);
    let p1 = mul(a1, b1);
    let p2 = mul(a2, b2);
    let p01 = mul(xor(a0, a1), xor(b0, b1));
    let p02 = mul(xor(a0, a2), xor(b0, b2));
    let p12 = mul(xor(a1, a2), xor(b1, b2));
    let r = fold(p0, p1, p2, p01, p02, p12, xor);
    proof {
        lemma_fold(xor, |v: __m256i| m256(v)@, 4, p0, p1, p2, p01, p02, p12, r);
        assert forall|k: int, i: int| 0 <= k < 3 && 0 <= i < 4 implies #[trigger] m256(r[k])[i] == split(
            prod_coeffs(a[i / 2], b[i / 2])[k],
        )[i % 2] by {
            let (x, y, l, w) = (a[i / 2], b[i / 2], 2 * (i / 2), i % 2);
            lemma_karatsuba_words(x, y);
            assert(m256(p0)[i] == cw(x.c0, y.c0, w));
            assert(m256(p1)[i] == cw(x.c1, y.c1, w));
            assert(m256(p2)[i] == cw(x.c2, y.c2, w));
            assert(m256(p01)[i] == cw(x.c0 ^ x.c1, y.c0 ^ y.c1, w));
            assert(m256(p02)[i] == cw(x.c0 ^ x.c2, y.c0 ^ y.c2, w));
            assert(m256(p12)[i] == cw(x.c1 ^ x.c2, y.c1 ^ y.c2, w));
            assert(m256(r[k])[i] == kara_word(x, y, k, w));
        }
    }
    r
}

/// Two independent products in the two 128-bit lanes of a YMM register.
///
/// Rewritten for Verus: the array pattern becomes indexing; `std::array::from_fn` becomes an array literal.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
pub unsafe fn mul_vec2(a: [F192; 2], b: [F192; 2]) -> (r: [F192; 2])
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] r[i] == e_mul(a[i], b[i]),
{
    // SAFETY: the function carries both features.
    unsafe {
        let d = karatsuba_vec2(a, b);
        let (d0, d1, d2) = (d[0], d[1], d[2]);
        // Lane i of c01 is [c0_i, c1_i]; the low qword of lane i of c2 is c2_i.
        let c01 = reduce_lanes256(_mm256_unpacklo_epi64(d0, d1), _mm256_unpackhi_epi64(d0, d1));
        let c2 = reduce_lanes256(d2, _mm256_unpackhi_epi64(d2, d2));
        let (w01, w2) = (transmute::<__m256i, [u64; 4]>(c01), transmute::<__m256i, [u64; 4]>(c2));
        let r = [F192::new(w01[0], w01[1], w2[0]), F192::new(w01[2], w01[3], w2[2])];
        proof {
            assert forall|i: int| 0 <= i < 2 implies #[trigger] r[i] == e_mul(a[i], b[i]) by {
                lemma_coeffs_reduce(a[i], b[i]);
                assert(m256(d0)[2 * i] == split(prod_coeffs(a[i], b[i])[0])[0]);
                assert(m256(d0)[2 * i + 1] == split(prod_coeffs(a[i], b[i])[0])[1]);
                assert(m256(d1)[2 * i] == split(prod_coeffs(a[i], b[i])[1])[0]);
                assert(m256(d1)[2 * i + 1] == split(prod_coeffs(a[i], b[i])[1])[1]);
                assert(m256(d2)[2 * i] == split(prod_coeffs(a[i], b[i])[2])[0]);
                assert(m256(d2)[2 * i + 1] == split(prod_coeffs(a[i], b[i])[2])[1]);
                assert(m256(c01)[2 * i] == reduce_word(m256(d0)[2 * i], m256(d0)[2 * i + 1]));
                assert(m256(c01)[2 * i + 1] == reduce_word(m256(d1)[2 * i], m256(d1)[2 * i + 1]));
                assert(m256(c2)[2 * i] == reduce_word(m256(d2)[2 * i], m256(d2)[2 * i + 1]));
            }
        }
        r
    }
}

/// Two independent unreduced products, packed as for the reduced version.
///
/// Rewritten for Verus: the reinterpret map and `std::array::from_fn` become array literals.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx2` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx2")]
pub unsafe fn mul_unreduced_vec2(a: [F192; 2], b: [F192; 2]) -> (r: [F192Unreduced; 2])
    ensures
        forall|i: int| 0 <= i < 2 ==> #[trigger] r[i] == prod_unreduced(a[i], b[i]),
        forall|i: int| 0 <= i < 2 ==> #[trigger] e_value(r[i]) == e_mul(a[i], b[i]),
{
    // SAFETY: the function carries both features; lane i of each register is one coefficient.
    unsafe {
        let k = karatsuba_vec2(a, b);
        let d = [
            transmute::<__m256i, [[u64; 2]; 2]>(k[0]),
            transmute::<__m256i, [[u64; 2]; 2]>(k[1]),
            transmute::<__m256i, [[u64; 2]; 2]>(k[2]),
        ];
        let r = [
            F192Unreduced { coeffs: [d[0][0], d[1][0], d[2][0]] },
            F192Unreduced { coeffs: [d[0][1], d[1][1], d[2][1]] },
        ];
        proof {
            axiom_m256_as_pairs(k[0]);
            axiom_m256_as_pairs(k[1]);
            axiom_m256_as_pairs(k[2]);
            assert forall|i: int| 0 <= i < 2 implies #[trigger] r[i] == prod_unreduced(a[i], b[i]) && e_value(r[i])
                == e_mul(a[i], b[i]) by {
                let pu = prod_unreduced(a[i], b[i]);
                assert forall|j: int| 0 <= j < 3 implies #[trigger] r[i].coeffs[j] == pu.coeffs[j] by {
                    assert(m256(k[j])[2 * i] == split(prod_coeffs(a[i], b[i])[j])[0]);
                    assert(m256(k[j])[2 * i + 1] == split(prod_coeffs(a[i], b[i])[j])[1]);
                    assert(r[i].coeffs[j] =~= pu.coeffs[j]);
                }
                assert(r[i].coeffs =~= pu.coeffs);
                lemma_prod_unreduced(a[i], b[i]);
            }
        }
        r
    }
}

/// The y-folded Karatsuba products of four pairs, one pair per 128-bit lane.
///
/// Rewritten for Verus: `a.map(|e| e.c0)` and the like become array literals; the closures carry their
/// specifications; the six products are bound to names before `fold`.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn karatsuba_vec4(a: [F192; 4], b: [F192; 4]) -> (r: [__m512i; 3])
    ensures
        forall|k: int, i: int|
            0 <= k < 3 && 0 <= i < 8 ==> #[trigger] m512(r[k])[i] == split(prod_coeffs(a[i / 2], b[i / 2])[k])[i % 2],
{
    // One coefficient of all four elements, in the low qword of each lane.
    let pack = |c: [u64; 4]| -> (r: __m512i)
        ensures
            forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == if i % 2 == 0 {
                c[i / 2]
            } else {
                0
            },
        {
            proof {
                lemma_i64_round_trip(c[0]);
                lemma_i64_round_trip(c[1]);
                lemma_i64_round_trip(c[2]);
                lemma_i64_round_trip(c[3]);
            }
            _mm512_set_epi64(0, c[3] as i64, 0, c[2] as i64, 0, c[1] as i64, 0, c[0] as i64)
        };
    let (a0, a1, a2) = (
        pack([a[0].c0, a[1].c0, a[2].c0, a[3].c0]),
        pack([a[0].c1, a[1].c1, a[2].c1, a[3].c1]),
        pack([a[0].c2, a[1].c2, a[2].c2, a[3].c2]),
    );
    let (b0, b1, b2) = (
        pack([b[0].c0, b[1].c0, b[2].c0, b[3].c0]),
        pack([b[0].c1, b[1].c1, b[2].c1, b[3].c1]),
        pack([b[0].c2, b[1].c2, b[2].c2, b[3].c2]),
    );
    // One instruction per base product covers all four lanes.
    let mul = |x: __m512i, y: __m512i| -> (r: __m512i)
        ensures
            forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == cw(m512(x)[2 * (i / 2)], m512(y)[2 * (i / 2)], i % 2),
        {
            proof {
                lemma_clmul_sel();
                lemma_cw_all();
            }
            _mm512_clmulepi64_epi128::<0x00>(x, y)
        };
    let xor = |x: __m512i, y: __m512i| -> (r: __m512i)
        ensures
            forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == m512(x)[i] ^ m512(y)[i],
        { _mm512_xor_si512(x, y) };
    let p0 = mul(a0, b0);
    let p1 = mul(a1, b1);
    let p2 = mul(a2, b2);
    let p01 = mul(xor(a0, a1), xor(b0, b1));
    let p02 = mul(xor(a0, a2), xor(b0, b2));
    let p12 = mul(xor(a1, a2), xor(b1, b2));
    let r = fold(p0, p1, p2, p01, p02, p12, xor);
    proof {
        lemma_fold(xor, |v: __m512i| m512(v)@, 8, p0, p1, p2, p01, p02, p12, r);
        assert forall|k: int, i: int| 0 <= k < 3 && 0 <= i < 8 implies #[trigger] m512(r[k])[i] == split(
            prod_coeffs(a[i / 2], b[i / 2])[k],
        )[i % 2] by {
            let (x, y, l, w) = (a[i / 2], b[i / 2], 2 * (i / 2), i % 2);
            lemma_karatsuba_words(x, y);
            assert(m512(a0)[l] == x.c0 && m512(a1)[l] == x.c1 && m512(a2)[l] == x.c2);
            assert(m512(b0)[l] == y.c0 && m512(b1)[l] == y.c1 && m512(b2)[l] == y.c2);
            assert(m512(p0)[i] == cw(x.c0, y.c0, w));
            assert(m512(p1)[i] == cw(x.c1, y.c1, w));
            assert(m512(p2)[i] == cw(x.c2, y.c2, w));
            assert(m512(p01)[i] == cw(x.c0 ^ x.c1, y.c0 ^ y.c1, w));
            assert(m512(p02)[i] == cw(x.c0 ^ x.c2, y.c0 ^ y.c2, w));
            assert(m512(p12)[i] == cw(x.c1 ^ x.c2, y.c1 ^ y.c2, w));
            assert(m512(r[k])[i] == kara_word(x, y, k, w));
        }
    }
    r
}

/// Four independent products in the four 128-bit lanes of a ZMM register.
///
/// Rewritten for Verus: the array pattern becomes indexing; `std::array::from_fn` becomes an array literal.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_vec4(a: [F192; 4], b: [F192; 4]) -> (r: [F192; 4])
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] r[i] == e_mul(a[i], b[i]),
{
    // SAFETY: the function carries both features.
    unsafe {
        let d = karatsuba_vec4(a, b);
        let (d0, d1, d2) = (d[0], d[1], d[2]);
        // Lane i of c01 is [c0_i, c1_i]; the low qword of lane i of c2 is c2_i.
        let c01 = reduce_lanes512(_mm512_unpacklo_epi64(d0, d1), _mm512_unpackhi_epi64(d0, d1));
        let c2 = reduce_lanes512(d2, _mm512_unpackhi_epi64(d2, d2));
        let (w01, w2) = (transmute::<__m512i, [u64; 8]>(c01), transmute::<__m512i, [u64; 8]>(c2));
        let r = [
            F192::new(w01[0], w01[1], w2[0]),
            F192::new(w01[2], w01[3], w2[2]),
            F192::new(w01[4], w01[5], w2[4]),
            F192::new(w01[6], w01[7], w2[6]),
        ];
        proof {
            assert forall|i: int| 0 <= i < 4 implies #[trigger] r[i] == e_mul(a[i], b[i]) by {
                lemma_coeffs_reduce(a[i], b[i]);
                assert(m512(d0)[2 * i] == split(prod_coeffs(a[i], b[i])[0])[0]);
                assert(m512(d0)[2 * i + 1] == split(prod_coeffs(a[i], b[i])[0])[1]);
                assert(m512(d1)[2 * i] == split(prod_coeffs(a[i], b[i])[1])[0]);
                assert(m512(d1)[2 * i + 1] == split(prod_coeffs(a[i], b[i])[1])[1]);
                assert(m512(d2)[2 * i] == split(prod_coeffs(a[i], b[i])[2])[0]);
                assert(m512(d2)[2 * i + 1] == split(prod_coeffs(a[i], b[i])[2])[1]);
                assert(m512(c01)[2 * i] == reduce_word(m512(d0)[2 * i], m512(d0)[2 * i + 1]));
                assert(m512(c01)[2 * i + 1] == reduce_word(m512(d1)[2 * i], m512(d1)[2 * i + 1]));
                assert(m512(c2)[2 * i] == reduce_word(m512(d2)[2 * i], m512(d2)[2 * i + 1]));
            }
        }
        r
    }
}

/// Four independent unreduced products, packed as for the reduced version.
///
/// Rewritten for Verus: the reinterpret map and `std::array::from_fn` become array literals.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_unreduced_vec4(a: [F192; 4], b: [F192; 4]) -> (r: [F192Unreduced; 4])
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] r[i] == prod_unreduced(a[i], b[i]),
        forall|i: int| 0 <= i < 4 ==> #[trigger] e_value(r[i]) == e_mul(a[i], b[i]),
{
    // SAFETY: the function carries both features; lane i of each register is one coefficient.
    unsafe {
        let k = karatsuba_vec4(a, b);
        let d = [
            transmute::<__m512i, [[u64; 2]; 4]>(k[0]),
            transmute::<__m512i, [[u64; 2]; 4]>(k[1]),
            transmute::<__m512i, [[u64; 2]; 4]>(k[2]),
        ];
        let r = [
            F192Unreduced { coeffs: [d[0][0], d[1][0], d[2][0]] },
            F192Unreduced { coeffs: [d[0][1], d[1][1], d[2][1]] },
            F192Unreduced { coeffs: [d[0][2], d[1][2], d[2][2]] },
            F192Unreduced { coeffs: [d[0][3], d[1][3], d[2][3]] },
        ];
        proof {
            axiom_m512_as_pairs(k[0]);
            axiom_m512_as_pairs(k[1]);
            axiom_m512_as_pairs(k[2]);
            assert forall|i: int| 0 <= i < 4 implies #[trigger] r[i] == prod_unreduced(a[i], b[i]) && e_value(r[i])
                == e_mul(a[i], b[i]) by {
                let pu = prod_unreduced(a[i], b[i]);
                assert forall|j: int| 0 <= j < 3 implies #[trigger] r[i].coeffs[j] == pu.coeffs[j] by {
                    assert(m512(k[j])[2 * i] == split(prod_coeffs(a[i], b[i])[j])[0]);
                    assert(m512(k[j])[2 * i + 1] == split(prod_coeffs(a[i], b[i])[j])[1]);
                    assert(r[i].coeffs[j] =~= pu.coeffs[j]);
                }
                assert(r[i].coeffs =~= pu.coeffs);
                lemma_prod_unreduced(a[i], b[i]);
            }
        }
        r
    }
}

// ---------------------------------------------------------------------------------------------
// Mixed products: eight base scalars against shared operand registers
// ---------------------------------------------------------------------------------------------
/// Coefficient `c` of an element.
pub open spec fn coef(e: F192, c: int) -> u64 {
    if c == 0 {
        e.c0
    } else if c == 1 {
        e.c1
    } else {
        e.c2
    }
}

/// Unreduced values with the same words are equal.
pub proof fn lemma_unreduced_ext(u: F192Unreduced, v: F192Unreduced)
    requires
        forall|c: int, x: int| 0 <= c < 3 && 0 <= x < 2 ==> #[trigger] u.coeffs[c][x] == v.coeffs[c][x],
    ensures
        u == v,
{
    assert(u.coeffs[0][0] == v.coeffs[0][0] && u.coeffs[0][1] == v.coeffs[0][1]);
    assert(u.coeffs[1][0] == v.coeffs[1][0] && u.coeffs[1][1] == v.coeffs[1][1]);
    assert(u.coeffs[2][0] == v.coeffs[2][0] && u.coeffs[2][1] == v.coeffs[2][1]);
    assert(u.coeffs[0] =~= v.coeffs[0]);
    assert(u.coeffs[1] =~= v.coeffs[1]);
    assert(u.coeffs[2] =~= v.coeffs[2]);
    assert(u.coeffs =~= v.coeffs);
}

/// The words of the mixed product's coefficients.
pub proof fn lemma_base_words(a: F192, k: u64)
    ensures
        forall|c: int, x: int| 0 <= c < 3 && 0 <= x < 2 ==> #[trigger] base_unreduced(a, k).coeffs[c][x] == cw(coef(a, c), k, x),
{
}

/// `0 + e = e` in `E`.
pub proof fn lemma_e_add_zero(e: F192)
    ensures
        e_add(F192::ZERO, e) == e,
{
    let (x, y, z) = (e.c0, e.c1, e.c2);
    assert(0u64 ^ x == x && 0u64 ^ y == y && 0u64 ^ z == z) by (bit_vector);
}

/// Adding a product to zero gives the product.
pub proof fn lemma_zero_xor_base(u: F192Unreduced, a: F192, k: u64)
    requires
        forall|c: int, x: int| 0 <= c < 3 && 0 <= x < 2 ==> #[trigger] u.coeffs[c][x] == 0,
    ensures
        e_value(u_xor(u, base_unreduced(a, k))) == e_mul(a, e_from_k(k)),
{
    lemma_unreduced_ext(u, F192Unreduced::ZERO);
    lemma_u_zero();
    lemma_e_value_xor(u, base_unreduced(a, k));
    lemma_base_unreduced(a, k);
    lemma_e_add_zero(e_mul(a, e_from_k(k)));
}

/// Which of [`mul_by_pairs`]'s six registers holds coefficient `c` of row `i`: `[e0, e1, e2]` for the even rows,
/// `[o0, o1, o2]` for the odd ones, at positions `[0, 1, 4]` and `[2, 3, 5]`.
pub open spec fn acc_reg(i: int, c: int) -> int {
    if i % 2 == 0 {
        if c == 2 {
            4
        } else {
            c
        }
    } else {
        if c == 2 {
            5
        } else {
            2 + c
        }
    }
}

/// Row `i` of six product registers: lane `i / 2` of the registers [`acc_reg`] names.
pub open spec fn row512(acc: [__m512i; 6], i: int) -> F192Unreduced {
    let j = i / 2;
    F192Unreduced {
        coeffs: [
            [m512(acc[acc_reg(i, 0)])[2 * j], m512(acc[acc_reg(i, 0)])[2 * j + 1]],
            [m512(acc[acc_reg(i, 1)])[2 * j], m512(acc[acc_reg(i, 1)])[2 * j + 1]],
            [m512(acc[acc_reg(i, 2)])[2 * j], m512(acc[acc_reg(i, 2)])[2 * j + 1]],
        ],
    }
}

/// The six products of a shared pair of operand registers against eight packed scalars.
///
/// `a` lane `j` meets `k_2j` through `lo` and `k_2j+1` through `hi`.
/// Returns the products of `(a_lo, a_hi)` by `k_2j`, then by `k_2j+1`.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn mul_by_pairs(lo: __m512i, hi: __m512i, c2: __m512i, k: __m512i) -> (r: [__m512i; 6])
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r[0])[i] == cw(m512(lo)[2 * (i / 2)], m512(k)[2 * (i / 2)], i % 2),
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r[1])[i] == cw(m512(lo)[2 * (i / 2) + 1], m512(k)[2 * (i / 2)], i % 2),
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r[2])[i] == cw(m512(hi)[2 * (i / 2)], m512(k)[2 * (i / 2) + 1], i % 2),
        forall|i: int|
            0 <= i < 8 ==> #[trigger] m512(r[3])[i] == cw(m512(hi)[2 * (i / 2) + 1], m512(k)[2 * (i / 2) + 1], i % 2),
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r[4])[i] == cw(m512(c2)[2 * (i / 2)], m512(k)[2 * (i / 2)], i % 2),
        forall|i: int|
            0 <= i < 8 ==> #[trigger] m512(r[5])[i] == cw(m512(c2)[2 * (i / 2) + 1], m512(k)[2 * (i / 2) + 1], i % 2),
{
    proof {
        lemma_clmul_sel();
        lemma_cw_all();
    }
    // Immediate bit 0 picks the qword of the first operand, bit 4 that of the second.
    [
        _mm512_clmulepi64_epi128::<0x00>(lo, k),
        _mm512_clmulepi64_epi128::<0x01>(lo, k),
        _mm512_clmulepi64_epi128::<0x10>(hi, k),
        _mm512_clmulepi64_epi128::<0x11>(hi, k),
        _mm512_clmulepi64_epi128::<0x00>(c2, k),
        _mm512_clmulepi64_epi128::<0x11>(c2, k),
    ]
}

/// Eight mixed products by one scalar.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_base8(t: F192, k: [F64; 8]) -> (r: [F192; 8])
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] r[i] == e_mul(t, e_from_k(k[i].0)),
{
    // SAFETY: the function carries both features.
    unsafe {
        let mut acc = [_mm512_setzero_si512(); 6];
        let ghost zero = acc;
        mul_base8_add(&mut acc, t, k);
        proof {
            assert forall|i: int| 0 <= i < 8 implies #[trigger] e_value(row512(acc, i)) == e_mul(t, e_from_k(k[i].0)) by {
                assert forall|c: int, x: int| 0 <= c < 3 && 0 <= x < 2 implies #[trigger] row512(zero, i).coeffs[c][x]
                    == 0 by {
                    assert(m512(zero[acc_reg(i, c)])[2 * (i / 2) + x] == 0);
                }
                lemma_zero_xor_base(row512(zero, i), t, k[i].0);
            }
        }
        mul_base8_reduce(acc)
    }
}

/// The eight scalars in one register.
///
/// Trusted (`external_body`): the body is production's load; `tests/equivalence/gf2_64x3.rs` checks it.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[verifier::external_body]
#[inline(always)]
pub fn load_k8(k: &[F64; 8]) -> (r: __m512i)
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == k[i].0,
{
    // SAFETY: `k` is eight qwords.
    unsafe { _mm512_loadu_si512(k.as_ptr().cast()) }
}

/// Add the eight mixed products `t * k[i]` to the six product registers of [`mul_by_pairs`].
///
/// Rewritten for Verus: the load of `k` is the helper [`load_k8`]; the `iter_mut().zip(..)` loop is an index loop.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_base8_add(acc: &mut [__m512i; 6], t: F192, k: [F64; 8])
    ensures
        forall|i: int|
            0 <= i < 8 ==> #[trigger] row512(*final(acc), i) == u_xor(row512(*old(acc), i), base_unreduced(t, k[i].0)),
{
    proof {
        lemma_i64_round_trip(t.c2);
    }
    // SAFETY: the function carries both features; `k` is eight qwords.
    unsafe {
        // `t` in every lane: [c0, c1] for both pair registers, [c2, c2] for the last.
        let t01 = _mm512_broadcast_i32x4(pair(t.c0, t.c1));
        let t2 = _mm512_set1_epi64(t.c2 as i64);
        let kv = load_k8(&k);
        let p = mul_by_pairs(t01, t01, t2, kv);
        for c in 0..6usize
            invariant
                forall|d: int, x: int|
                    0 <= d < c && 0 <= x < 8 ==> #[trigger] m512(acc[d])[x] == m512(old(acc)[d])[x] ^ m512(p[d])[x],
                forall|d: int| c <= d < 6 ==> #[trigger] acc[d] == old(acc)[d],
        {
            acc[c] = _mm512_xor_si512(acc[c], p[c]);
        }
        proof {
            assert forall|i: int| 0 <= i < 8 implies #[trigger] row512(*acc, i) == u_xor(
                row512(*old(acc), i),
                base_unreduced(t, k[i].0),
            ) by {
                let j = i / 2;
                lemma_base_words(t, k[i].0);
                assert forall|c: int, x: int| 0 <= c < 3 && 0 <= x < 2 implies #[trigger] row512(*acc, i).coeffs[c][x]
                    == u_xor(row512(*old(acc), i), base_unreduced(t, k[i].0)).coeffs[c][x] by {
                    let r = acc_reg(i, c);
                    assert(m512(acc[r])[2 * j + x] == m512(old(acc)[r])[2 * j + x] ^ m512(p[r])[2 * j + x]);
                    assert(m512(p[r])[2 * j + x] == cw(coef(t, c), k[i].0, x));
                }
                lemma_unreduced_ext(row512(*acc, i), u_xor(row512(*old(acc), i), base_unreduced(t, k[i].0)));
            }
        }
    }
}

/// Reduce the six product registers of [`mul_base8_add`] into the eight sums.
///
/// Rewritten for Verus: the parameter pattern `[e0, e1, o0, o1, e2, o2]` is the parameter `acc`, indexed;
/// `std::array::from_fn` is its closure called on `0..8`; the closures carry their specifications.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn mul_base8_reduce(acc: [__m512i; 6]) -> (r: [F192; 8])
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] r[i] == e_value(row512(acc, i)),
{
    let (e0, e1, o0, o1, e2, o2) = (acc[0], acc[1], acc[2], acc[3], acc[4], acc[5]);
    // SAFETY: the function carries both features.
    unsafe {
        // Gather each product's low and high halves into qword-wise vectors, then reduce.
        let red = |x: __m512i, y: __m512i| -> (r: __m512i)
            ensures
                forall|i: int| 0 <= i < 4 ==> #[trigger] m512(r)[2 * i] == reduce_word(m512(x)[2 * i], m512(x)[2 * i + 1]),
                forall|i: int| 0 <= i < 4 ==> #[trigger] m512(r)[2 * i + 1] == reduce_word(m512(y)[2 * i], m512(y)[2 * i + 1]),
            { reduce_lanes512(_mm512_unpacklo_epi64(x, y), _mm512_unpackhi_epi64(x, y)) };
        let (ev, od, cv) = (red(e0, e1), red(o0, o1), red(e2, o2));
        let even = transmute::<__m512i, [u64; 8]>(ev);
        let odd = transmute::<__m512i, [u64; 8]>(od);
        let c2 = transmute::<__m512i, [u64; 8]>(cv);
        proof {
            assert(even == m512(ev) && odd == m512(od) && c2 == m512(cv));
        }
        let elem = |i: usize| -> (r: F192)
            requires
                i < 8,
            ensures
                r == (F192 {
                    c0: (if i % 2 == 0 { even } else { odd })[2 * (i / 2) as int],
                    c1: (if i % 2 == 0 { even } else { odd })[2 * (i / 2) + 1],
                    c2: c2[i as int],
                }),
            {
                let (j, w) = (i / 2, if i % 2 == 0 { &even } else { &odd });
                F192::new(w[2 * j], w[2 * j + 1], c2[i])
            };
        let r = [elem(0), elem(1), elem(2), elem(3), elem(4), elem(5), elem(6), elem(7)];
        proof {
            assert forall|i: int| 0 <= i < 8 implies #[trigger] r[i] == e_value(row512(acc, i)) by {
                let j = i / 2;
                assert(i == 0 || i == 1 || i == 2 || i == 3 || i == 4 || i == 5 || i == 6 || i == 7);
                if i % 2 == 0 {
                    assert(i == 2 * j);
                    assert(even[2 * j] == reduce_word(m512(e0)[2 * j], m512(e0)[2 * j + 1]));
                    assert(even[2 * j + 1] == reduce_word(m512(e1)[2 * j], m512(e1)[2 * j + 1]));
                    assert(c2[2 * j] == reduce_word(m512(e2)[2 * j], m512(e2)[2 * j + 1]));
                } else {
                    assert(i == 2 * j + 1);
                    assert(odd[2 * j] == reduce_word(m512(o0)[2 * j], m512(o0)[2 * j + 1]));
                    assert(odd[2 * j + 1] == reduce_word(m512(o1)[2 * j], m512(o1)[2 * j + 1]));
                    assert(c2[2 * j + 1] == reduce_word(m512(o2)[2 * j], m512(o2)[2 * j + 1]));
                }
            }
        }
        r
    }
}

/// Words `x` of the four 128-bit lanes of a register, XORed as [`sum_lanes4`] folds them: halves, then quarters.
pub open spec fn sum4(a: __m512i, x: int) -> u64 {
    (m512(a)[x] ^ m512(a)[4 + x]) ^ (m512(a)[2 + x] ^ m512(a)[6 + x])
}

/// The unreduced value of three coefficient registers whose four lanes each hold part of the coefficient.
pub open spec fn sum_lanes512(d: [__m512i; 3]) -> F192Unreduced {
    F192Unreduced {
        coeffs: [[sum4(d[0], 0), sum4(d[0], 1)], [sum4(d[1], 0), sum4(d[1], 1)], [sum4(d[2], 0), sum4(d[2], 1)]],
    }
}

/// Word `x` of coefficient `c` of the mixed product `w_m * k_m`.
pub open spec fn tw(w: Seq<super::Weights8>, k: Seq<F64>, m: int, c: int, x: int) -> u64 {
    cw(coef(w8_get(w[m / 8], m % 8), c), k[m].0, x)
}

/// Word `a`, then the words of the eight mixed products of block `b` XORed on in order.
pub open spec fn block_words(a: u64, w: Seq<super::Weights8>, k: Seq<F64>, b: int, c: int, x: int) -> u64 {
    a ^ tw(w, k, 8 * b, c, x) ^ tw(w, k, 8 * b + 1, c, x) ^ tw(w, k, 8 * b + 2, c, x) ^ tw(w, k, 8 * b + 3, c, x)
        ^ tw(w, k, 8 * b + 4, c, x) ^ tw(w, k, 8 * b + 5, c, x) ^ tw(w, k, 8 * b + 6, c, x) ^ tw(w, k, 8 * b + 7, c, x)
}

/// The mixed product `w_m * k_m`, unreduced.
pub open spec fn dot_term(w: Seq<super::Weights8>, k: Seq<F64>, m: int) -> F192Unreduced {
    base_unreduced(w8_get(w[m / 8], m % 8), k[m].0)
}

/// One step of the inner product: XORing on the unreduced product `w_m * k_m` adds it to the sum.
pub proof fn lemma_dot_term(w: Seq<super::Weights8>, k: Seq<F64>, m: int, u: F192Unreduced)
    requires
        0 <= m,
        e_value(u) == dot_spec(w, k, m as nat),
    ensures
        e_value(u_xor(u, dot_term(w, k, m))) == dot_spec(w, k, (m + 1) as nat),
{
    lemma_e_value_xor(u, dot_term(w, k, m));
    lemma_base_unreduced(w8_get(w[m / 8], m % 8), k[m].0);
}

/// A block of eight terms XORed on in order adds the block to the sum.
pub proof fn lemma_dot_block(w: Seq<super::Weights8>, k: Seq<F64>, b: int, u_old: F192Unreduced, u_new: F192Unreduced)
    requires
        0 <= b,
        e_value(u_old) == dot_spec(w, k, (8 * b) as nat),
        forall|c: int, x: int|
            0 <= c < 3 && 0 <= x < 2 ==> #[trigger] u_new.coeffs[c][x] == block_words(u_old.coeffs[c][x], w, k, b, c, x),
    ensures
        e_value(u_new) == dot_spec(w, k, (8 * b + 8) as nat),
{
    let t = |m: int| dot_term(w, k, m);
    let u1 = u_xor(u_old, t(8 * b));
    let u2 = u_xor(u1, t(8 * b + 1));
    let u3 = u_xor(u2, t(8 * b + 2));
    let u4 = u_xor(u3, t(8 * b + 3));
    let u5 = u_xor(u4, t(8 * b + 4));
    let u6 = u_xor(u5, t(8 * b + 5));
    let u7 = u_xor(u6, t(8 * b + 6));
    let u8 = u_xor(u7, t(8 * b + 7));
    lemma_dot_term(w, k, 8 * b, u_old);
    lemma_dot_term(w, k, 8 * b + 1, u1);
    lemma_dot_term(w, k, 8 * b + 2, u2);
    lemma_dot_term(w, k, 8 * b + 3, u3);
    lemma_dot_term(w, k, 8 * b + 4, u4);
    lemma_dot_term(w, k, 8 * b + 5, u5);
    lemma_dot_term(w, k, 8 * b + 6, u6);
    lemma_dot_term(w, k, 8 * b + 7, u7);
    assert forall|c: int, x: int| 0 <= c < 3 && 0 <= x < 2 implies #[trigger] u_new.coeffs[c][x] == u8.coeffs[c][x] by {
        assert forall|m: int| #![auto] 0 <= m ==> t(m).coeffs[c][x] == tw(w, k, m, c, x) by {
            lemma_base_words(w8_get(w[m / 8], m % 8), k[m].0);
        }
    }
    lemma_unreduced_ext(u_new, u8);
}

/// The mixed inner product over packed weights.
///
/// Rewritten for Verus: the `enumerate` loop is an index loop; the loads are the helpers [`load_k_at`] and
/// [`load_weights`]; the array pattern of the products becomes indexing; the lane fold mapped over `acc` is its
/// closure called on each register; the closures carry their specifications. The `Safety` condition on the lengths
/// is a `requires`.
///
/// # Safety
///
/// Requires the `vpclmulqdq` and `avx512f` target features, and `k.len() == 8 * w.len()`.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
pub unsafe fn dot_base(w: &[Weights8], k: &[F64]) -> (r: F192Unreduced)
    requires
        k.len() == 8 * w.len(),
    ensures
        e_value(r) == dot_spec(w@, k@, k.len() as nat),
{
    // SAFETY: the function carries both features; `Weights8` is 64-byte aligned, `k` holds 8 qwords per block.
    unsafe {
        let xor = |x: __m512i, y: __m512i| -> (r: __m512i)
            ensures
                forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == m512(x)[i] ^ m512(y)[i],
            { _mm512_xor_si512(x, y) };
        let mut acc = [_mm512_setzero_si512(); 3];
        proof {
            lemma_u_zero();
            let z = sum_lanes512(acc);
            assert forall|c: int, x: int| 0 <= c < 3 && 0 <= x < 2 implies #[trigger] z.coeffs[c][x]
                == F192Unreduced::ZERO.coeffs[c][x] by {
                assert(m512(acc[c])[x] == 0 && m512(acc[c])[4 + x] == 0 && m512(acc[c])[2 + x] == 0 && m512(acc[c])[6
                    + x] == 0);
                assert((0u64 ^ 0u64) ^ (0u64 ^ 0u64) == 0u64) by (bit_vector);
            }
            lemma_unreduced_ext(z, F192Unreduced::ZERO);
        }
        for b in 0..w.len()
            invariant
                k.len() == 8 * w.len(),
                e_value(sum_lanes512(acc)) == dot_spec(w@, k@, (8 * b) as nat),
                forall|x: __m512i, y: __m512i| #[trigger] xor.requires((x, y)),
                forall|x: __m512i, y: __m512i, z: __m512i, i: int|
                    #![trigger xor.ensures((x, y), z), m512(z)[i]]
                    xor.ensures((x, y), z) && 0 <= i < 8 ==> m512(z)[i] == m512(x)[i] ^ m512(y)[i],
        {
            let kv = load_k_at(k, 8 * b);
            let (lo, hi, c2) = load_weights(&w[b]);
            let p = mul_by_pairs(lo, hi, c2, kv);
            let (e0, e1, o0, o1, e2, o2) = (p[0], p[1], p[2], p[3], p[4], p[5]);
            let ghost old_acc = acc;
            acc = [xor(acc[0], xor(e0, o0)), xor(acc[1], xor(e1, o1)), xor(acc[2], xor(e2, o2))];
            proof {
                let (u_old, u_new) = (sum_lanes512(old_acc), sum_lanes512(acc));
                let ws = w[b as int];
                assert forall|c: int, x: int| 0 <= c < 3 && 0 <= x < 2 implies #[trigger] u_new.coeffs[c][x]
                    == block_words(u_old.coeffs[c][x], w@, k@, b as int, c, x) by {
                    // Lane `j` of the even and odd products: terms `8b + 2j` and `8b + 2j + 1`.
                    assert forall|j: int| 0 <= j < 4 implies {
                        &&& #[trigger] m512(p[acc_reg(0, c)])[2 * j + x] == tw(w@, k@, 8 * b + 2 * j, c, x)
                        &&& m512(p[acc_reg(1, c)])[2 * j + x] == tw(w@, k@, 8 * b + 2 * j + 1, c, x)
                    } by {
                        assert((8 * b + 2 * j) / 8 == b && (8 * b + 2 * j) % 8 == 2 * j);
                        assert((8 * b + 2 * j + 1) / 8 == b && (8 * b + 2 * j + 1) % 8 == 2 * j + 1);
                        assert((2 * j) / 2 == j && (2 * j + 1) / 2 == j && (2 * j) % 2 == 0 && (2 * j + 1) % 2 == 1);
                    }
                    let a = |l: int| m512(old_acc[c])[2 * l + x];
                    let t = |m: int| tw(w@, k@, 8 * b + m, c, x);
                    assert(m512(p[acc_reg(0, c)])[x] == t(0) && m512(p[acc_reg(1, c)])[x] == t(1));
                    assert(m512(p[acc_reg(0, c)])[2 + x] == t(2) && m512(p[acc_reg(1, c)])[2 + x] == t(3));
                    assert(m512(p[acc_reg(0, c)])[4 + x] == t(4) && m512(p[acc_reg(1, c)])[4 + x] == t(5));
                    assert(m512(p[acc_reg(0, c)])[6 + x] == t(6) && m512(p[acc_reg(1, c)])[6 + x] == t(7));
                    let (a0, a1, a2, a3) = (a(0), a(1), a(2), a(3));
                    let (t0, t1, t2, t3, t4, t5, t6, t7) = (t(0), t(1), t(2), t(3), t(4), t(5), t(6), t(7));
                    assert(((a0 ^ (t0 ^ t1)) ^ (a2 ^ (t4 ^ t5))) ^ ((a1 ^ (t2 ^ t3)) ^ (a3 ^ (t6 ^ t7))) == ((a0 ^ a2) ^ (
                    a1 ^ a3)) ^ t0 ^ t1 ^ t2 ^ t3 ^ t4 ^ t5 ^ t6 ^ t7) by (bit_vector);
                }
                lemma_dot_block(w@, k@, b as int, u_old, u_new);
            }
        }
        // Fold the four 128-bit lanes of each sum into one.
        let lane = |a: __m512i| -> (q: [u64; 2])
            ensures
                q[0] == sum4(a, 0),
                q[1] == sum4(a, 1),
            {
                let half = _mm256_xor_si256(_mm512_castsi512_si256(a), _mm512_extracti64x4_epi64::<1>(a));
                let q = _mm_xor_si128(_mm256_castsi256_si128(half), _mm256_extracti128_si256::<1>(half));
                proof {
                    lemma_imm_one();
                    assert(m128(q)[0] == sum4(a, 0) && m128(q)[1] == sum4(a, 1));
                }
                transmute::<__m128i, [u64; 2]>(q)
            };
        let lanes = [lane(acc[0]), lane(acc[1]), lane(acc[2])];
        let r = F192Unreduced { coeffs: lanes };
        proof {
            lemma_unreduced_ext(r, sum_lanes512(acc));
        }
        r
    }
}

/// Eight scalars from `k[at..]` in one register.
///
/// Trusted (`external_body`): the body is production's load; `tests/equivalence/gf2_64x3.rs` checks it.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[verifier::external_body]
#[inline(always)]
pub fn load_k_at(k: &[F64], at: usize) -> (r: __m512i)
    requires
        at + 8 <= k.len(),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r)[i] == k[at + i].0,
{
    // SAFETY: `k` holds eight qwords from `at`.
    unsafe { _mm512_loadu_si512(k.as_ptr().add(at).cast()) }
}

/// The three weight registers of a block.
///
/// Trusted (`external_body`): the body is production's three aligned loads (`Weights8` is 64-byte aligned);
/// `tests/equivalence/gf2_64x3.rs` checks it.
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[verifier::external_body]
#[inline(always)]
pub fn load_weights(w: &Weights8) -> (r: (__m512i, __m512i, __m512i))
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r.0)[i] == w.lo[i],
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r.1)[i] == w.hi[i],
        forall|i: int| 0 <= i < 8 ==> #[trigger] m512(r.2)[i] == w.c2[i],
{
    // SAFETY: the fields of `Weights8` are 64-byte aligned.
    unsafe {
        (
            _mm512_load_si512(w.lo.as_ptr().cast()),
            _mm512_load_si512(w.hi.as_ptr().cast()),
            _mm512_load_si512(w.c2.as_ptr().cast()),
        )
    }
}

} // verus!
