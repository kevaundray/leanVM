//! The additive NTT over `GF(2^8)` of flock's zerocheck, and the table that collapses the round-1 extension
//! through it.
//!
//! The executable functions are the portable paths of `crates/flock/src/zerocheck/ntt.rs` and
//! `crates/flock/src/zerocheck/ntt/inv_table.rs`, copied with the same names and bodies where Verus accepts
//! them; `tests/equivalence/flock_ntt.rs` checks the copies against production.
//!
//! Specification, over the field of `crate::gf2_8` (`f8_mul`), with the standard basis `b_i = x^i`
//! ([`basis8`], the byte with bit `i` alone):
//!
//! - [`subspace_poly8`]: the subspace polynomial `s_i`, `s_0(x) = x`, `s_i(x) = s_{i-1}(x) (s_{i-1}(x) +
//!   s_{i-1}(b_{i-1}))`, and [`normalized_poly8`], `Ŵ_i(x) = s_i(b_i)^(-1) s_i(x)`.
//! - [`novel8`]: the novel-basis polynomial `Σ_{j < 2^m} a_j X_j(x)`, `X_j = Π_{i < m} Ŵ_i(x)^(bit_i(j))`, by its
//!   split on the top bit of `j`; [`lemma_novel8_flat`] proves it equal to the flat sum [`novel8_sum`].
//! - [`fft_spec`] and [`ifft_spec`]: the recursions of `fft_rec` and `ifft_rec`, butterfly by butterfly.
//! - [`twiddles_of`]: the claim of `compute_twiddles`' documentation, entry `2^d - 1 + j` is the twiddle of
//!   block `j` at depth `d`, `Ŵ_(k-1-d)` of the block's first point.
//!
//! Main results: `compute_twiddles`' postcondition; [`lemma_fft_evaluates`] (the forward transform of an
//! NTT built with offset `β` maps the coefficients to the evaluations at `β + v`, `v < 2^k`);
//! [`lemma_ifft_after_fft`] and [`lemma_fft_after_ifft`] (the two transforms undo each other);
//! [`lemma_lde_shift`] (the columns of `M = forward_Λ ∘ inverse_S` satisfy `M[i][j] = M[i ⊕ j][0]`);
//! `InvNttTableByteSingleGf8::new`'s postcondition (row `w` of the table is the XOR of the columns `t < 8` of
//! `M` over the set bits `t` of `w`) and `apply_scalar`'s (it multiplies `M` by the row's bits).
use crate::gf2_8::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// The basis element `b_i = x^i`: the byte with bit `i` alone (`i < 8`).
pub open spec fn basis8(i: nat) -> u8 {
    1u8 << (i as u8)
}

/// The subspace polynomial `s_i` of the standard basis, evaluated at `x`:
/// `s_0(x) = x` and `s_i(x) = s_{i-1}(x) · (s_{i-1}(x) + s_{i-1}(b_{i-1}))`.
pub open spec fn subspace_poly8(i: nat, x: u8) -> u8
    decreases i,
{
    if i == 0 {
        x
    } else {
        let p = subspace_poly8((i - 1) as nat, x);
        f8_mul(p, p ^ subspace_poly8((i - 1) as nat, basis8((i - 1) as nat)))
    }
}

/// The inverse in `GF(2^8)`, `y^254` (zero for zero), as `F8::inv` computes it.
pub open spec fn f8_inv(y: u8) -> u8 {
    f8_pow(y, 254)
}

/// The normalized subspace polynomial `Ŵ_i(x) = s_i(b_i)^(-1) · s_i(x)`.
pub open spec fn normalized_poly8(i: nat, x: u8) -> u8 {
    f8_mul(f8_inv(subspace_poly8(i, basis8(i))), subspace_poly8(i, x))
}

/// The novel-basis polynomial with the `2^m` coefficients `a`, evaluated at `x`:
/// `Σ_{j < 2^m} a_j X_j(x)` with `X_j = Π_{i < m} Ŵ_i(x)^(bit_i(j))`, split on the top bit of `j`: the
/// polynomial of the low half of the coefficients, plus `Ŵ_(m-1)(x)` times the polynomial of the high half.
pub open spec fn novel8(m: nat, a: Seq<F8>, x: u8) -> u8
    decreases m,
{
    if m == 0 {
        a[0].0
    } else {
        let h = pow2((m - 1) as nat) as int;
        novel8((m - 1) as nat, a.subrange(0, h), x) ^ f8_mul(
            normalized_poly8((m - 1) as nat, x),
            novel8((m - 1) as nat, a.subrange(h, 2 * h), x),
        )
    }
}

/// `a + t b`, word by word.
pub open spec fn lincomb(a: Seq<F8>, t: u8, b: Seq<F8>) -> Seq<F8> {
    Seq::new(a.len(), |j: int| F8(a[j].0 ^ f8_mul(t, b[j].0)))
}

/// `fft_butterfly` on the halves of `v`: `(u, w) -> (u + λ w, w + (u + λ w))`.
pub open spec fn fft_butterfly_spec(v: Seq<F8>, lambda: u8) -> Seq<F8> {
    let h = v.len() / 2;
    Seq::new(
        v.len(),
        |p: int|
            if p < h {
                F8(v[p].0 ^ f8_mul(lambda, v[p + h].0))
            } else if p < 2 * h {
                F8(v[p].0 ^ (v[p - h].0 ^ f8_mul(lambda, v[p].0)))
            } else {
                v[p]
            },
    )
}

/// `ifft_butterfly` on the halves of `v`: `(u, w) -> (u + λ (w + u), w + u)`.
pub open spec fn ifft_butterfly_spec(v: Seq<F8>, lambda: u8) -> Seq<F8> {
    let h = v.len() / 2;
    Seq::new(
        v.len(),
        |p: int|
            if p < h {
                F8(v[p].0 ^ f8_mul(lambda, v[p + h].0 ^ v[p].0))
            } else if p < 2 * h {
                F8(v[p].0 ^ v[p - h].0)
            } else {
                v[p]
            },
    )
}

/// The recursion of `fft_rec(v, tw, idx)`: the butterfly with twiddle `tw[idx - 1]`, then the low half at
/// `2 idx` and the high half at `2 idx + 1`.
pub open spec fn fft_spec(v: Seq<F8>, tw: Seq<F8>, idx: int) -> Seq<F8>
    decreases v.len(),
{
    if v.len() <= 1 {
        v
    } else {
        let w = fft_butterfly_spec(v, tw[idx - 1].0);
        let h = v.len() / 2;
        fft_spec(w.subrange(0, h as int), tw, 2 * idx) + fft_spec(w.subrange(h as int, v.len() as int), tw, 2 * idx + 1)
    }
}

/// The recursion of `ifft_rec(v, tw, idx)`: the low half at `2 idx` and the high half at `2 idx + 1`, then
/// the inverse butterfly with twiddle `tw[idx - 1]`.
pub open spec fn ifft_spec(v: Seq<F8>, tw: Seq<F8>, idx: int) -> Seq<F8>
    decreases v.len(),
{
    if v.len() <= 1 {
        v
    } else {
        let h = v.len() / 2;
        ifft_butterfly_spec(
            ifft_spec(v.subrange(0, h as int), tw, 2 * idx) + ifft_spec(v.subrange(h as int, v.len() as int), tw, 2 * idx + 1),
            tw[idx - 1].0,
        )
    }
}

/// The first point of block `blk` of `2^m` points: `blk 2^m`, as a byte.
pub open spec fn block_offset(blk: nat, m: nat) -> u8 {
    (blk * pow2(m)) as u8
}

/// The twiddle table of a `2^k`-point NTT with offset `β`: entry `2^d - 1 + j`, for depth `d < k` and block
/// `j < 2^d`, is `Ŵ_(k-1-d)(β + j 2^(k-d))`, `Ŵ` of the first point of the block.
pub open spec fn twiddles_of(tw: Seq<F8>, k: nat, beta: u8) -> bool {
    &&& tw.len() + 1 == pow2(k)
    &&& forall|d: nat, j: nat|
        d < k && j < pow2(d) ==> (#[trigger] tw[pow2(d) - 1 + j]).0 == normalized_poly8(
            (k - 1 - d) as nat,
            beta ^ block_offset(j, (k - d) as nat),
        )
}

/// The twiddles of the subtree of `fft_rec` at `idx`, `2^m` points from `y` on: `tw[idx - 1] = Ŵ_(m-1)(y)`,
/// and the same for the low half from `y` and the high half from `y + b_(m-1)`.
pub open spec fn node_ok(tw: Seq<F8>, idx: int, m: nat, y: u8) -> bool
    decreases m,
{
    m == 0 || (tw[idx - 1].0 == normalized_poly8((m - 1) as nat, y) && node_ok(tw, 2 * idx, (m - 1) as nat, y)
        && node_ok(tw, 2 * idx + 1, (m - 1) as nat, y ^ basis8((m - 1) as nat)))
}

// ---------------------------------------------------------------------------------------------
// Field facts
// ---------------------------------------------------------------------------------------------
proof fn lemma_xor8(a: u8, b: u8, c: u8)
    ensures
        a ^ a == 0,
        a ^ 0 == a,
        0 ^ a == a,
        a ^ b == b ^ a,
        (a ^ b) ^ c == a ^ (b ^ c),
        (a ^ b) ^ b == a,
        a ^ (a ^ b) == b,
{
    assert(a ^ a == 0 && a ^ 0 == a && 0 ^ a == a && a ^ b == b ^ a && (a ^ b) ^ c == a ^ (b ^ c) && (a ^ b) ^ b == a
        && a ^ (a ^ b) == b) by (bit_vector);
}

/// `GF(2^8)` has no zero divisors.
pub proof fn lemma_f8_no_zero_divisors(a: u8, b: u8)
    requires
        f8_mul(a, b) == 0,
        a != 0,
    ensures
        b == 0,
{
    let ai = f8_inv(a);
    lemma_f8_inv_correct(a);
    lemma_f8_mul_comm(a, ai);
    lemma_f8_mul_assoc(ai, a, b);
    lemma_f8_mul_one(b);
    lemma_f8_mul_zero(ai);
}

/// `1^(-1) = 1`.
proof fn lemma_f8_inv_one()
    ensures
        f8_inv(1) == 1,
{
    lemma_f8_inv_correct(1);
    lemma_f8_mul_one(f8_inv(1));
}

proof fn lemma_f8_mul_xor_left(a: u8, b: u8, c: u8)
    ensures
        f8_mul(a ^ b, c) == f8_mul(a, c) ^ f8_mul(b, c),
{
    lemma_f8_mul_comm(a ^ b, c);
    lemma_f8_mul_comm(a, c);
    lemma_f8_mul_comm(b, c);
    lemma_f8_mul_xor_right(c, a, b);
}

/// `a (b c) = b (a c)`.
proof fn lemma_f8_mul_swap(a: u8, b: u8, c: u8)
    ensures
        f8_mul(a, f8_mul(b, c)) == f8_mul(b, f8_mul(a, c)),
{
    lemma_f8_mul_assoc(a, b, c);
    lemma_f8_mul_assoc(b, a, c);
    lemma_f8_mul_comm(a, b);
}

// ---------------------------------------------------------------------------------------------
// Bits of a byte
// ---------------------------------------------------------------------------------------------
/// `1 << s = 2^s` for a byte.
pub proof fn lemma_shl8(s: nat)
    requires
        s < 8,
    ensures
        basis8(s) as nat == pow2(s),
        pow2(s) <= 128,
{
    lemma2_to64();
    if s < 7 {
        lemma_pow2_strictly_increases(s, 7);
    }
    lemma_u8_shl_is_mul(1, s as u8);
}

/// Bit `s` against the comparisons with `2^s` and `2^(s+1)`.
proof fn lemma_bit8(x: u8, s: u8)
    requires
        s < 8,
    ensures
        (x >> s) == 1u8 ==> (x ^ (1u8 << s)) == sub(x, 1u8 << s) && (x ^ (1u8 << s)) < (1u8 << s),
        s < 7 ==> (x < (1u8 << s) ==> x < (1u8 << add(s, 1))),
        s < 7 ==> ((x ^ (1u8 << s)) < (1u8 << s) ==> x < (1u8 << add(s, 1))),
        s < 7 ==> (x < (1u8 << add(s, 1)) && !(x < (1u8 << s)) ==> (x ^ (1u8 << s)) < (1u8 << s)),
        s == 7 ==> (!(x < (1u8 << s)) ==> (x ^ (1u8 << s)) < (1u8 << s)),
        (x >> s) & 1u8 == 0u8 ==> (x ^ (1u8 << s)) == add(x, 1u8 << s),
{
    assert((x >> s) == 1u8 ==> (x ^ (1u8 << s)) == sub(x, 1u8 << s) && (x ^ (1u8 << s)) < (1u8 << s)) by (bit_vector)
        requires
            s < 8,
    ;
    assert(s < 7 ==> (x < (1u8 << s) ==> x < (1u8 << add(s, 1)))) by (bit_vector)
        requires
            s < 8,
    ;
    assert(s < 7 ==> ((x ^ (1u8 << s)) < (1u8 << s) ==> x < (1u8 << add(s, 1)))) by (bit_vector)
        requires
            s < 8,
    ;
    assert(s < 7 ==> (x < (1u8 << add(s, 1)) && !(x < (1u8 << s)) ==> (x ^ (1u8 << s)) < (1u8 << s))) by (bit_vector)
        requires
            s < 8,
    ;
    assert(s == 7 ==> (!(x < (1u8 << s)) ==> (x ^ (1u8 << s)) < (1u8 << s))) by (bit_vector);
    assert((x >> s) & 1u8 == 0u8 ==> (x ^ (1u8 << s)) == add(x, 1u8 << s)) by (bit_vector)
        requires
            s < 8,
    ;
}

/// An index `u` of the high half of `2^(s+1)` points: `u - 2^s = u ⊕ 2^s`, below `2^s`.
proof fn lemma_high_half(u: int, s: nat)
    requires
        s < 8,
        pow2(s) <= u < 2 * pow2(s),
    ensures
        (u - pow2(s)) as u8 == (u as u8) ^ basis8(s),
        ((u as u8) ^ basis8(s)) < basis8(s),
{
    lemma_shl8(s);
    let x = u as u8;
    assert(x as int == u);
    lemma_u8_shr_is_div(x, s as u8);
    lemma_fundamental_div_mod_converse(u, pow2(s) as int, 1, u - pow2(s));
    lemma_bit8(x, s as u8);
}

// ---------------------------------------------------------------------------------------------
// Subspace polynomials
// ---------------------------------------------------------------------------------------------
/// `s_i` is F_2-linear: `s_i(x + y) = s_i(x) + s_i(y)`.
pub proof fn lemma_subspace_poly8_additive(i: nat, x: u8, y: u8)
    ensures
        subspace_poly8(i, x ^ y) == subspace_poly8(i, x) ^ subspace_poly8(i, y),
    decreases i,
{
    if i > 0 {
        let j = (i - 1) as nat;
        lemma_subspace_poly8_additive(j, x, y);
        let a = subspace_poly8(j, x);
        let b = subspace_poly8(j, y);
        let c = subspace_poly8(j, basis8(j));
        // (a + b)(a + b + c) = a(a + c) + a b + b(b + c) + b a
        assert((a ^ b) ^ c == (a ^ c) ^ b && (a ^ b) ^ c == (b ^ c) ^ a) by (bit_vector);
        lemma_f8_mul_xor_left(a, b, (a ^ b) ^ c);
        lemma_f8_mul_xor_right(a, a ^ c, b);
        lemma_f8_mul_xor_right(b, b ^ c, a);
        lemma_f8_mul_comm(a, b);
        let (p, q, r) = (f8_mul(a, a ^ c), f8_mul(b, b ^ c), f8_mul(a, b));
        assert((p ^ r) ^ (q ^ r) == p ^ q) by (bit_vector);
    }
}

/// The normalized `Ŵ_i` is F_2-linear too.
pub proof fn lemma_normalized_poly8_additive(i: nat, x: u8, y: u8)
    ensures
        normalized_poly8(i, x ^ y) == normalized_poly8(i, x) ^ normalized_poly8(i, y),
{
    lemma_subspace_poly8_additive(i, x, y);
    lemma_f8_mul_xor_right(f8_inv(subspace_poly8(i, basis8(i))), subspace_poly8(i, x), subspace_poly8(i, y));
}

/// `s_i` vanishes on `{0, .., 2^i - 1}`, the span of `b_0 .. b_(i-1)`.
pub proof fn lemma_subspace_poly8_vanishes(i: nat, x: u8)
    requires
        i < 8,
        x < basis8(i),
    ensures
        subspace_poly8(i, x) == 0,
    decreases i,
{
    if i == 0 {
        assert(x < (1u8 << 0u8) ==> x == 0) by (bit_vector);
    } else {
        let j = (i - 1) as nat;
        let b = basis8(j);
        let p = subspace_poly8(j, x);
        let c = subspace_poly8(j, b);
        lemma_bit8(x, j as u8);
        assert(add(j as u8, 1) == i as u8);
        if x < b {
            lemma_subspace_poly8_vanishes(j, x);
            lemma_f8_mul_zero(p ^ c);
        } else {
            lemma_subspace_poly8_vanishes(j, x ^ b);
            lemma_subspace_poly8_additive(j, x ^ b, b);
            lemma_xor8(x, b, 0);
            lemma_xor8(c, 0, 0);
            lemma_f8_mul_zero(p);
        }
    }
}

/// The roots of `s_i` lie below `2^i`: `s_i(x) = 0` only on `{0, .., 2^i - 1}`.
pub proof fn lemma_subspace_poly8_roots(i: nat, x: u8)
    requires
        i < 8,
        subspace_poly8(i, x) == 0,
    ensures
        x < basis8(i),
    decreases i,
{
    if i == 0 {
        assert(0u8 < (1u8 << 0u8)) by (bit_vector);
    } else {
        let j = (i - 1) as nat;
        let b = basis8(j);
        let p = subspace_poly8(j, x);
        let c = subspace_poly8(j, b);
        lemma_bit8(x, j as u8);
        assert(add(j as u8, 1) == i as u8);
        if p == 0 {
            lemma_subspace_poly8_roots(j, x);
        } else {
            lemma_f8_no_zero_divisors(p, p ^ c);
            lemma_subspace_poly8_additive(j, x, b);
            lemma_subspace_poly8_roots(j, x ^ b);
        }
    }
}

/// Every normalizer works: `Ŵ_i(b_i) = 1` for `i < 8`.
pub proof fn lemma_normalized_poly8_at_basis(i: nat)
    requires
        i < 8,
    ensures
        normalized_poly8(i, basis8(i)) == 1,
{
    let y = subspace_poly8(i, basis8(i));
    if y == 0 {
        lemma_subspace_poly8_roots(i, basis8(i));
    }
    lemma_f8_inv_correct(y);
    lemma_f8_mul_comm(y, f8_inv(y));
}

/// `Ŵ_i` vanishes on `{0, .., 2^i - 1}`.
pub proof fn lemma_normalized_poly8_vanishes(i: nat, x: u8)
    requires
        i < 8,
        x < basis8(i),
    ensures
        normalized_poly8(i, x) == 0,
{
    lemma_subspace_poly8_vanishes(i, x);
    lemma_f8_mul_zero(f8_inv(subspace_poly8(i, basis8(i))));
}

/// `Ŵ_0(x) = x`.
proof fn lemma_normalized_poly8_zero(x: u8)
    ensures
        normalized_poly8(0, x) == x,
{
    assert(basis8(0) == 1) by {
        assert((1u8 << 0u8) == 1u8) by (bit_vector);
    }
    lemma_f8_inv_one();
    lemma_f8_mul_one(x);
}

// ---------------------------------------------------------------------------------------------
// The novel-basis polynomial is linear in its coefficients
// ---------------------------------------------------------------------------------------------
proof fn lemma_lincomb_halves(a: Seq<F8>, t: u8, b: Seq<F8>, h: int)
    requires
        a.len() == b.len() == 2 * h,
        h >= 0,
    ensures
        lincomb(a, t, b).subrange(0, h) == lincomb(a.subrange(0, h), t, b.subrange(0, h)),
        lincomb(a, t, b).subrange(h, 2 * h) == lincomb(a.subrange(h, 2 * h), t, b.subrange(h, 2 * h)),
{
    assert(lincomb(a, t, b).subrange(0, h) =~= lincomb(a.subrange(0, h), t, b.subrange(0, h)));
    assert(lincomb(a, t, b).subrange(h, 2 * h) =~= lincomb(a.subrange(h, 2 * h), t, b.subrange(h, 2 * h)));
}

/// `P_(a + t b) = P_a + t P_b`.
pub proof fn lemma_novel8_lincomb(m: nat, a: Seq<F8>, t: u8, b: Seq<F8>, x: u8)
    requires
        a.len() == pow2(m),
        b.len() == pow2(m),
    ensures
        novel8(m, lincomb(a, t, b), x) == novel8(m, a, x) ^ f8_mul(t, novel8(m, b, x)),
    decreases m,
{
    if m > 0 {
        let j = (m - 1) as nat;
        let h = pow2(j) as int;
        lemma_pow2_unfold(m);
        lemma_lincomb_halves(a, t, b, h);
        let (al, ah, bl, bh) = (a.subrange(0, h), a.subrange(h, 2 * h), b.subrange(0, h), b.subrange(h, 2 * h));
        lemma_novel8_lincomb(j, al, t, bl, x);
        lemma_novel8_lincomb(j, ah, t, bh, x);
        let w = normalized_poly8(j, x);
        let (pal, pah, pbl, pbh) = (novel8(j, al, x), novel8(j, ah, x), novel8(j, bl, x), novel8(j, bh, x));
        // (pal + t pbl) + w (pah + t pbh) = (pal + w pah) + t (pbl + w pbh)
        lemma_f8_mul_xor_right(w, pah, f8_mul(t, pbh));
        lemma_f8_mul_swap(w, t, pbh);
        lemma_f8_mul_xor_right(t, pbl, f8_mul(w, pbh));
        let (p1, p2, p3) = (f8_mul(t, pbl), f8_mul(w, pah), f8_mul(t, f8_mul(w, pbh)));
        assert((pal ^ p1) ^ (p2 ^ p3) == (pal ^ p2) ^ (p1 ^ p3)) by (bit_vector);
    } else {
        lemma2_to64();
    }
}

// ---------------------------------------------------------------------------------------------
// The forward transform evaluates, the inverse undoes it
// ---------------------------------------------------------------------------------------------
proof fn lemma_fft_spec_len(v: Seq<F8>, tw: Seq<F8>, idx: int)
    ensures
        fft_spec(v, tw, idx).len() == v.len(),
    decreases v.len(),
{
    if v.len() > 1 {
        let w = fft_butterfly_spec(v, tw[idx - 1].0);
        let h = v.len() / 2;
        lemma_fft_spec_len(w.subrange(0, h as int), tw, 2 * idx);
        lemma_fft_spec_len(w.subrange(h as int, v.len() as int), tw, 2 * idx + 1);
    }
}

proof fn lemma_ifft_spec_len(v: Seq<F8>, tw: Seq<F8>, idx: int)
    ensures
        ifft_spec(v, tw, idx).len() == v.len(),
    decreases v.len(),
{
    if v.len() > 1 {
        let h = v.len() / 2;
        lemma_ifft_spec_len(v.subrange(0, h as int), tw, 2 * idx);
        lemma_ifft_spec_len(v.subrange(h as int, v.len() as int), tw, 2 * idx + 1);
    }
}

/// The forward transform evaluates the novel-basis polynomial: on `2^m` coefficients, with the twiddles of
/// a subtree from `y` ([`node_ok`]), output word `u` is `P(y + u)`.
pub proof fn lemma_fft_evaluates_from(v: Seq<F8>, tw: Seq<F8>, idx: int, m: nat, y: u8)
    requires
        m <= 8,
        v.len() == pow2(m),
        node_ok(tw, idx, m, y),
    ensures
        fft_spec(v, tw, idx).len() == v.len(),
        forall|u: int| 0 <= u < v.len() ==> (#[trigger] fft_spec(v, tw, idx)[u]).0 == novel8(m, v, y ^ (u as u8)),
    decreases m,
{
    lemma_fft_spec_len(v, tw, idx);
    if m == 0 {
        lemma2_to64();
        assert forall|u: int| 0 <= u < v.len() implies (#[trigger] fft_spec(v, tw, idx)[u]).0 == novel8(m, v, y ^ (u as u8)) by {
            assert(u == 0);
            assert(y ^ 0u8 == y) by (bit_vector);
        }
    } else {
        let j = (m - 1) as nat;
        let h = pow2(j) as int;
        let n = v.len() as int;
        lemma_pow2_unfold(m);
        lemma_pow2_pos(j);
        lemma_shl8(j);
        let lambda = tw[idx - 1].0;
        let w = fft_butterfly_spec(v, lambda);
        let (lo, hi) = (w.subrange(0, h), w.subrange(h, n));
        let (vl, vh) = (v.subrange(0, h), v.subrange(h, n));
        let b = basis8(j);
        lemma_fft_evaluates_from(lo, tw, 2 * idx, j, y);
        lemma_fft_evaluates_from(hi, tw, 2 * idx + 1, j, y ^ b);
        // The two halves after the butterfly, as combinations of the coefficient halves.
        assert(lo =~= lincomb(vl, lambda, vh));
        assert forall|i: int| 0 <= i < h implies #[trigger] hi[i] == lincomb(vl, lambda ^ 1, vh)[i] by {
            let (p, q) = (v[i].0, v[i + h].0);
            lemma_f8_mul_xor_left(lambda, 1, q);
            lemma_f8_mul_one(q);
            let r = f8_mul(lambda, q);
            assert(q ^ (p ^ r) == p ^ (r ^ q)) by (bit_vector);
        }
        assert(hi =~= lincomb(vl, lambda ^ 1, vh));
        lemma_novel8_lincomb(j, vl, lambda, vh, y);
        assert forall|u: int| 0 <= u < n implies (#[trigger] fft_spec(v, tw, idx)[u]).0 == novel8(m, v, y ^ (u as u8)) by {
            let x = y ^ (u as u8);
            lemma_normalized_poly8_additive(j, y, u as u8);
            lemma_novel8_lincomb(j, vl, lambda, vh, x);
            lemma_novel8_lincomb(j, vl, lambda ^ 1, vh, x);
            if u < h {
                assert((u as u8) < b);
                lemma_normalized_poly8_vanishes(j, u as u8);
                lemma_xor8(lambda, 0, 0);
                assert(fft_spec(v, tw, idx)[u] == fft_spec(lo, tw, 2 * idx)[u]);
            } else {
                lemma_high_half(u, j);
                let u8l = (u - h) as u8;
                lemma_normalized_poly8_additive(j, b, u8l);
                lemma_normalized_poly8_at_basis(j);
                lemma_normalized_poly8_vanishes(j, u8l);
                lemma_xor8(1, 0, 0);
                let ux = u as u8;
                assert((y ^ b) ^ (ux ^ b) == y ^ ux) by (bit_vector);
                assert(b ^ (ux ^ b) == ux) by (bit_vector);
                assert(fft_spec(v, tw, idx)[u] == fft_spec(hi, tw, 2 * idx + 1)[u - h]);
            }
        }
    }
}

/// The inverse butterfly undoes the forward one.
proof fn lemma_butterfly8_inverse(u: u8, w: u8, t: u8)
    ensures
        ({
            let (u1, w1) = (u ^ f8_mul(t, w), w ^ (u ^ f8_mul(t, w)));
            u1 ^ f8_mul(t, w1 ^ u1) == u && w1 ^ u1 == w
        }),
        ({
            let (u1, w1) = (u ^ f8_mul(t, w ^ u), w ^ u);
            u1 ^ f8_mul(t, w1) == u && w1 ^ (u1 ^ f8_mul(t, w1)) == w
        }),
{
    let r = f8_mul(t, w);
    assert((w ^ (u ^ r)) ^ (u ^ r) == w) by (bit_vector);
    assert((u ^ r) ^ r == u) by (bit_vector);
    let s = f8_mul(t, w ^ u);
    assert((u ^ s) ^ s == u) by (bit_vector);
    assert((w ^ u) ^ ((u ^ s) ^ s) == w) by (bit_vector);
}

/// The inverse transform undoes the forward one, for every twiddle table and every buffer.
pub proof fn lemma_ifft_after_fft(v: Seq<F8>, tw: Seq<F8>, idx: int)
    ensures
        ifft_spec(fft_spec(v, tw, idx), tw, idx) == v,
    decreases v.len(),
{
    if v.len() > 1 {
        let n = v.len() as int;
        let h = n / 2;
        let lambda = tw[idx - 1].0;
        let w = fft_butterfly_spec(v, lambda);
        let (lo, hi) = (w.subrange(0, h), w.subrange(h, n));
        lemma_ifft_after_fft(lo, tw, 2 * idx);
        lemma_ifft_after_fft(hi, tw, 2 * idx + 1);
        lemma_fft_spec_len(lo, tw, 2 * idx);
        lemma_fft_spec_len(hi, tw, 2 * idx + 1);
        let f = fft_spec(v, tw, idx);
        assert(f.subrange(0, h) =~= fft_spec(lo, tw, 2 * idx));
        assert(f.subrange(h, n) =~= fft_spec(hi, tw, 2 * idx + 1));
        assert(fft_spec(lo, tw, 2 * idx) + fft_spec(hi, tw, 2 * idx + 1) == f);
        let g = ifft_spec(fft_spec(lo, tw, 2 * idx), tw, 2 * idx) + ifft_spec(fft_spec(hi, tw, 2 * idx + 1), tw, 2 * idx + 1);
        assert(g =~= w);
        assert forall|p: int| 0 <= p < n implies #[trigger] ifft_butterfly_spec(w, lambda)[p] == v[p] by {
            if p < h {
                lemma_butterfly8_inverse(v[p].0, v[p + h].0, lambda);
            } else if p < 2 * h {
                lemma_butterfly8_inverse(v[p - h].0, v[p].0, lambda);
            }
        }
        assert(ifft_butterfly_spec(w, lambda) =~= v);
    }
}

/// The forward transform undoes the inverse one, for every twiddle table and every buffer.
pub proof fn lemma_fft_after_ifft(v: Seq<F8>, tw: Seq<F8>, idx: int)
    ensures
        fft_spec(ifft_spec(v, tw, idx), tw, idx) == v,
    decreases v.len(),
{
    if v.len() > 1 {
        let n = v.len() as int;
        let h = n / 2;
        let lambda = tw[idx - 1].0;
        let (vl, vh) = (v.subrange(0, h), v.subrange(h, n));
        lemma_fft_after_ifft(vl, tw, 2 * idx);
        lemma_fft_after_ifft(vh, tw, 2 * idx + 1);
        lemma_ifft_spec_len(vl, tw, 2 * idx);
        lemma_ifft_spec_len(vh, tw, 2 * idx + 1);
        let g = ifft_spec(vl, tw, 2 * idx) + ifft_spec(vh, tw, 2 * idx + 1);
        let iv = ifft_spec(v, tw, idx);
        assert(iv == ifft_butterfly_spec(g, lambda));
        let w = fft_butterfly_spec(iv, lambda);
        assert forall|p: int| 0 <= p < n implies #[trigger] w[p] == g[p] by {
            if p < h {
                lemma_butterfly8_inverse(g[p].0, g[p + h].0, lambda);
            } else if p < 2 * h {
                lemma_butterfly8_inverse(g[p - h].0, g[p].0, lambda);
            }
        }
        assert(w =~= g);
        assert(w.subrange(0, h) =~= ifft_spec(vl, tw, 2 * idx));
        assert(w.subrange(h, n) =~= ifft_spec(vh, tw, 2 * idx + 1));
        assert(fft_spec(iv, tw, idx) =~= v);
    }
}

} // verus!
