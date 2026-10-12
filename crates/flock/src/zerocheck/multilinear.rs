// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The zerocheck's multilinear rounds, after the univariate skip.
//!
//! Past the skip, the zerocheck is a sumcheck over the `n = m - k_skip` remaining variables:
//!
//! ```text
//!     sum_x eq(r, x) * (a(x) b(x) + c(x))        a, b, c folded at the skip challenge z
//! ```
//!
//! The quadratic `a b` and the linear `c` ride the same rounds, so all three claims land at one point.
//!
//! Round `t` binds the lowest unbound variable: positions `2k` and `2k + 1` pair up as its `X = 0` and `X = 1`.
//! Each kernel returns the bare `(G(1), G(inf))` of the round's inner polynomial `G`.
//! The prover sends them, and the verifier derives `G(0)` from the running claim:
//!
//! ```text
//!     claim = (1 + r_t) G(0) + r_t G(1)
//! ```
//!
//! Every pass sends several consecutive rounds, each after the first as a polynomial in the challenges before it.
//!
//! - **Bit passes** read the packed bits, folding them on the fly, while a folded table would outweigh them.
//! - The last bit pass also stores the folded tables.
//! - **Table passes** fold the challenges pending on the stored tables, then send two rounds from the result.
//!
//! The naive fold-then-sum routes cross-check every kernel in the tests.

use std::mem::MaybeUninit;

use parallel::Chunks;
use primitives::bit_fold::{BLOCK, BitFold};
use primitives::field::{F192, F192Unreduced};
use primitives::multilinear::{SplitEq, eq_table};
use primitives::stream::Stream;

use super::Padding;
use super::round1::EQ_HIGH_VARS;

/// Eq variables in the per-task half of a bit pass's split eq table.
///
/// - `2^10` entries are 24 KiB, so the table stays in L1 beside the fold's matrices.
/// - The remaining variables index the tasks, one reduced product each.
const EQ_LO_VARS: usize = 10;

/// The blocks of `2^k` positions a bit pass takes per step: 64 positions, or eight blocks, the planar packing.
const fn unit_blocks(k: usize) -> usize {
    if BLOCK >> k > 8 { BLOCK >> k } else { 8 }
}

static TMP_TASKS: std::sync::LazyLock<usize> =
    std::sync::LazyLock::new(|| std::env::var("TMP_TASKS_LOG").map_or(6, |s| s.parse().unwrap()));
fn tmp_tasks_log() -> usize {
    *TMP_TASKS
}

/// Most rounds one pass sends.
pub(crate) const MAX_PASS_ROUNDS: usize = 4;

/// Points of the grid of a pass of [`MAX_PASS_ROUNDS`] rounds.
const MAX_GRID: usize = pow3(MAX_PASS_ROUNDS);

/// `3^k`.
const fn pow3(k: usize) -> usize {
    3usize.pow(k as u32)
}

/// The grid point of the binary point `beta`: its bits as base-3 digits.
const fn grid_of(beta: usize) -> usize {
    let (mut point, mut place, mut rest) = (0, 1, beta);
    while rest != 0 {
        point += (rest & 1) * place;
        place *= 3;
        rest >>= 1;
    }
    point
}

/// The `NE = 3^k - 2^k` steps extending values on the binary points of a `k`-variable grid to all of it.
///
/// Step `(p, p0, p1)` sets `v[p] = v[p0] + v[p1]`, where `p0` and `p1` are `p` with its last `inf` digit made 0 and 1.
/// Their own last `inf` digit is an earlier one, and the steps run digit by digit, so their values come first.
const fn extension<const NE: usize>(k: usize) -> [(u8, u8, u8); NE] {
    let mut steps = [(0u8, 0u8, 0u8); NE];
    let mut n = 0;
    let mut i = 0;
    while i < k {
        let place = pow3(i);
        let mut p = 0;
        while p < pow3(k) {
            // Digit `i` is `inf`, and every later one binary.
            let mut later = p / place / 3;
            let mut binary = true;
            while later != 0 {
                binary &= later % 3 != 2;
                later /= 3;
            }
            if (p / place) % 3 == 2 && binary {
                steps[n] = (p as u8, (p - 2 * place) as u8, (p - place) as u8);
                n += 1;
            }
            p += 1;
        }
        i += 1;
    }
    assert!(n == NE, "3^k - 2^k steps");
    steps
}

/// The extension steps of a grid of `k` variables, by `k`.
const EXTENSIONS: [&[(u8, u8, u8)]; MAX_PASS_ROUNDS + 1] = [
    &[],
    &extension::<1>(1),
    &extension::<5>(2),
    &extension::<19>(3),
    &extension::<65>(4),
];

/// Extend values given on the binary points of a `k`-variable grid to every point, `add` being the field sum.
#[inline(always)]
fn extend<T: Copy, const N: usize>(v: &mut [T; N], k: usize, add: impl Fn(T, T) -> T) {
    for &(p, p0, p1) in EXTENSIONS[k] {
        v[usize::from(p)] = add(v[usize::from(p0)], v[usize::from(p1)]);
    }
}

/// Four independent products.
///
/// A tuple keeps the scalar and NEON paths in registers, while VPCLMULQDQ batches them in one register.
#[inline(always)]
fn mul_quad(a: (F192, F192, F192, F192), b: (F192, F192, F192, F192)) -> (F192, F192, F192, F192) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    {
        let r = primitives::field::mul4([a.0, a.1, a.2, a.3], [b.0, b.1, b.2, b.3]);
        (r[0], r[1], r[2], r[3])
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    (a.0 * b.0, a.1 * b.1, a.2 * b.2, a.3 * b.3)
}

/// Four independent products, left unreduced for a caller summing them.
#[inline(always)]
fn mul_quad_unreduced(
    a: (F192, F192, F192, F192),
    b: (F192, F192, F192, F192),
) -> (F192Unreduced, F192Unreduced, F192Unreduced, F192Unreduced) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    {
        let r = primitives::field::mul_unreduced4([a.0, a.1, a.2, a.3], [b.0, b.1, b.2, b.3]);
        (r[0], r[1], r[2], r[3])
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    (
        a.0.mul_unreduced(b.0),
        a.1.mul_unreduced(b.1),
        a.2.mul_unreduced(b.2),
        a.3.mul_unreduced(b.3),
    )
}

/// The packed `a` and `b` bits, 64 skip bits per row, the row index running over the positions past the skip.
///
/// The kernels never read `c`: an honest witness has `c = a AND b`, derived from the rows already loaded.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PackedWitness<'a> {
    /// The `A z` bits.
    pub a: &'a [u8],
    /// The `B z` bits.
    pub b: &'a [u8],
}

impl<'a> PackedWitness<'a> {
    /// The two witnesses cut into rows of `CHUNKS` bytes, one per position at this level.
    fn rows<const CHUNKS: usize>(self) -> [&'a [[u8; CHUNKS]]; 2] {
        // A position at this level is `CHUNKS` bytes of each witness.
        let rows = [self.a, self.b].map(|packed| {
            let (rows, rest) = packed.as_chunks::<CHUNKS>();
            assert!(rest.is_empty(), "packed witness is whole rows");
            rows
        });
        // The passes halve the positions per round, so there is a power of two of them.
        let n_pos = rows[0].len();
        assert_eq!(rows[1].len(), n_pos, "a and b have one length");
        assert!(n_pos.is_power_of_two(), "a power-of-two number of positions");
        rows
    }

    /// The last `bytes` bytes of both witnesses.
    fn suffix(self, bytes: usize) -> Self {
        Self {
            a: &self.a[self.a.len() - bytes..],
            b: &self.b[self.b.len() - bytes..],
        }
    }
}

/// The `c = a AND b` rows of up to 64 positions, into the first `a.len()` rows of `c`.
#[inline(always)]
fn and_rows<const CHUNKS: usize>(a: &[[u8; CHUNKS]], b: &[[u8; CHUNKS]], c: &mut [[u8; CHUNKS]; BLOCK]) {
    for ((c, a), b) in c
        .as_flattened_mut()
        .iter_mut()
        .zip(a.as_flattened())
        .zip(b.as_flattened())
    {
        *c = a & b;
    }
}

/// The folded `a`, `b`, `c` values of up to 64 consecutive positions.
///
/// A task folds every block into one of these, so no block pays for zeroing or moving its tables.
struct FoldedBlock {
    a: [F192; BLOCK],
    b: [F192; BLOCK],
    c: [F192; BLOCK],
}

impl FoldedBlock {
    const ZERO: Self = Self {
        a: [F192::ZERO; BLOCK],
        b: [F192::ZERO; BLOCK],
        c: [F192::ZERO; BLOCK],
    };

    /// Fold positions `first..first + len` of each witness into the first `len` values.
    #[inline(always)]
    fn fold<const CHUNKS: usize>(&mut self, fold: &BitFold, rows: [&[[u8; CHUNKS]]; 2], first: usize, len: usize) {
        let [a, b] = rows.map(|r| &r[first..first + len]);
        let mut c = [[0u8; CHUNKS]; BLOCK];
        and_rows(a, b, &mut c);
        fold.fold_block(a, &mut self.a);
        fold.fold_block(b, &mut self.b);
        fold.fold_block(&c[..len], &mut self.c);
    }
}

/// Where the zero padding of a batched witness lets a kernel skip whole groups of positions.
///
/// A group spans `2^group_log` witness bits.
/// Group `g` lies wholly in a block's zero padding iff `(g & mask) >= live`.
///
/// - Such a group folds to zero, so it adds nothing to a message.
/// - A group straddling the boundary counts as live: its padding part is honestly zero.
/// - With no whole padding group, the mask is zero and every group is live.
#[derive(Clone, Copy, Debug)]
struct LiveGroups {
    mask: usize,
    live: usize,
}

impl LiveGroups {
    const fn new(padding: &Padding, group_log: usize) -> Self {
        let every = Self {
            mask: 0,
            live: usize::MAX,
        };
        // A group covering whole blocks holds data whenever its blocks do.
        if padding.k_log <= group_log {
            return every;
        }
        // Within a block, the groups from the first one wholly past the useful bits on are zero.
        let per_block = 1usize << (padding.k_log - group_log);
        let live = padding.useful_bits.div_ceil(1 << group_log);
        if live >= per_block {
            return every;
        }
        Self {
            mask: per_block - 1,
            live,
        }
    }

    /// Whether group `g` may hold a nonzero bit.
    #[inline(always)]
    const fn contains(self, g: usize) -> bool {
        (g & self.mask) < self.live
    }
}


/// Consecutive multilinear rounds from one pass, from one eq-weighted sum per point of a grid over its variables.
///
/// A pass of `k` rounds sees the positions in blocks of `2^k`, position `2^k q + beta` with `beta` over its variables.
/// A grid point `p` has one base-3 digit per variable, the value `0`, `1` or `inf` (digit 2) it takes:
///
/// ```text
///     A(p) = sum_q eq(r_out, q) * (a_q(p) b_q(p) + c_q(p))        c_q only at binary points
/// ```
///
/// Here `f_q(p)` is the block's multilinear extension along its variables, its leading coefficient along an `inf` digit.
///
/// Round `i` binds variable `i` once the challenges `rho` of the rounds before it are known.
/// Its polynomial has degree two in each of them, so the grid's first `i` digits interpolate it:
///
/// ```text
///     G_i(X) = sum_{p in {0, 1, inf}^i} L_p(rho) sum_beta eq(r_in, beta) A(p, X, beta)
///     L(rho) = 1 + rho, rho, rho (1 + rho)        at digits 0, 1, inf
/// ```
///
/// `beta` runs over the pass's later variables and `r_in` are their eq challenges; `c` is linear in each `rho`, so its
/// leading coefficient is zero.
/// Every point but the all-zero one serves some round, so `3^k - 1` sums send all `k` rounds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RoundBatch {
    /// The rounds of the pass.
    k: usize,
    /// `A(p)` at each point of the grid.
    grid: [F192; MAX_GRID],
    /// The eq challenges of the pass's variables after its first.
    r_in: [F192; MAX_PASS_ROUNDS - 1],
}

impl RoundBatch {
    /// The batch from its grid sums, `r_eq` the eq challenges of the variables its first round does not bind.
    fn new(sums: &[F192], r_eq: &[F192]) -> Self {
        let k = (1..=MAX_PASS_ROUNDS)
            .find(|&k| pow3(k) == sums.len())
            .expect("a grid of 3^k points");
        let mut grid = [F192::ZERO; MAX_GRID];
        // The all-zero point serves no round.
        grid[1..sums.len()].copy_from_slice(&sums[1..]);
        let mut r_in = [F192::ZERO; MAX_PASS_ROUNDS - 1];
        r_in[..k - 1].copy_from_slice(&r_eq[..k - 1]);
        Self { k, grid, r_in }
    }

    /// The rounds of the pass.
    pub(crate) const fn len(&self) -> usize {
        self.k
    }

    /// Round `i`'s `(G(1), G(inf))`, given the challenges `rhos` of the `i` rounds before it.
    pub(crate) fn round(&self, rhos: &[F192]) -> (F192, F192) {
        let i = rhos.len();
        assert!(i < self.k, "a round of the pass");
        // `L_p(rho)` for the points `p` of the bound digits.
        let mut weights = [F192::ZERO; MAX_GRID / 3];
        weights[0] = F192::ONE;
        for (l, &rho) in rhos.iter().enumerate() {
            let at_digit = [F192::ONE + rho, rho, rho * (F192::ONE + rho)];
            let place = pow3(l);
            // Digit 0 last: its weights overwrite the ones the others read.
            for d in (0..3).rev() {
                for p in 0..place {
                    weights[d * place + p] = weights[p] * at_digit[d];
                }
            }
        }
        let place = pow3(i);
        let eq = eq_table(&self.r_in[i..self.k - 1]);
        let at = |x: usize| {
            (eq.iter().enumerate()).fold(F192::ZERO, |acc, (beta, &e)| {
                let base = x * place + 3 * place * grid_of(beta);
                let row = &self.grid[base..base + place];
                acc + e * (weights.iter().zip(row)).fold(F192::ZERO, |s, (&w, &v)| s + w * v)
            })
        };
        (at(1), at(2))
    }
}

/// One quad's terms of two consecutive rounds, before its eq weight.
///
/// The quad is positions `4k + u + 2v`, `u` the first round's variable and `v` the second's.
///
/// ```text
///     position   4k     4k+1   4k+2   4k+3
///     (u, v)     (0,0)  (1,0)  (0,1)  (1,1)
/// ```
///
/// Returns the eight products of the grid's points, in the order of [`PAIR_POINTS`], `c` added at the binary ones.
#[inline(always)]
fn quad_pair_terms(
    [a0, a1, a2, a3]: [F192; 4],
    [b0, b1, b2, b3]: [F192; 4],
    [_, c1, c2, c3]: [F192; 4],
) -> [(F192, F192, F192, F192); 2] {
    // Leading coefficients along `u` (positions 0,1 and 2,3) and along `v` (0,2 and 1,3).
    let (du0, du1, dv0, dv1) = (a0 + a1, a2 + a3, a0 + a2, a1 + a3);
    let (eu0, eu1, ev0, ev1) = (b0 + b1, b2 + b3, b0 + b2, b1 + b3);
    let (p1, p2, p3, q0) = mul_quad((a1, a2, a3, du0), (b1, b2, b3, eu0));
    let (q1, r0, r1, r2) = mul_quad((du1, dv0, dv1, du0 + du1), (eu1, ev0, ev1, eu0 + eu1));
    [(p1 + c1, p3 + c3, q0, q1), (p2 + c2, r0, r1, r2)]
}

/// The grid points of [`quad_pair_terms`]'s products, `u + 3 v`.
const PAIR_POINTS: [usize; 8] = [1, 4, 2, 5, 3, 6, 7, 8];

/// Add one quad's eq-weighted terms to the grid sums, unreduced: a task reduces each sum once.
#[inline(always)]
fn add_quad<const N: usize>(acc: &mut [F192Unreduced; N], eq: F192, [lo, hi]: [(F192, F192, F192, F192); 2]) {
    let e = (eq, eq, eq, eq);
    let (s0, s1, s2, s3) = mul_quad_unreduced(e, lo);
    let (s4, s5, s6, s7) = mul_quad_unreduced(e, hi);
    for (p, s) in PAIR_POINTS.into_iter().zip([s0, s1, s2, s3, s4, s5, s6, s7]) {
        acc[p] ^= s;
    }
}

/// Add one block's eq-weighted terms to the grid sums of a pass of `K` rounds, `N = 3^K` of them, unreduced.
///
/// Past two rounds the eq weight multiplies the `a` values first, so every term is one product:
///
/// ```text
///     eq (a(p) b(p) + c(p)) = (eq a)(p) b(p) + eq c(p)
/// ```
#[inline(always)]
fn add_block<const K: usize, const N: usize>(
    acc: &mut [F192Unreduced; N],
    eq: F192,
    [a, b, c]: [&[F192]; 3],
) {
    let quad = |t: &[F192]| -> [F192; 4] { t[..4].try_into().expect("a quad") };
    // Two rounds keep the products in registers, as tuples.
    if K == 2 {
        return add_quad(acc, eq, quad_pair_terms(quad(a), quad(b), quad(c)));
    }
    let splat = (eq, eq, eq, eq);
    let (mut ea, mut eb) = ([F192::ZERO; N], [F192::ZERO; N]);
    for j in (0..1 << K).step_by(4) {
        let pa = mul_quad(splat, (a[j], a[j + 1], a[j + 2], a[j + 3]));
        let pc = mul_quad_unreduced(splat, (c[j], c[j + 1], c[j + 2], c[j + 3]));
        for (o, (x, y)) in [(pa.0, pc.0), (pa.1, pc.1), (pa.2, pc.2), (pa.3, pc.3)].into_iter().enumerate() {
            let p = grid_of(j + o);
            (ea[p], eb[p]) = (x, b[j + o]);
            // Point 0 gathers `eq c_0` too, but serves no round.
            acc[p] ^= y;
        }
    }
    extend(&mut ea, K, |x, y| x + y);
    extend(&mut eb, K, |x, y| x + y);
    let mut p = 1;
    while p + 4 <= N {
        let s = mul_quad_unreduced((ea[p], ea[p + 1], ea[p + 2], ea[p + 3]), (eb[p], eb[p + 1], eb[p + 2], eb[p + 3]));
        for (o, s) in [s.0, s.1, s.2, s.3].into_iter().enumerate() {
            acc[p + o] ^= s;
        }
        p += 4;
    }
    for p in p..N {
        acc[p] ^= ea[p].mul_unreduced(eb[p]);
    }
}

/// Rounds `t` to `t + k - 1` straight from the packed bits, the folded tables never stored.
///
/// With `rho_1..rho_t` bound, `fold` weights each position's `2^t` rows (see its level constructor).
///
/// Each round's polynomial, with `r_eq` the eq challenges of the variables round `t` does not bind:
///
/// ```text
///     G(X) = sum_x' eq(r_eq, x') * (a(X, x') * b(X, x') + c(X, x'))
/// ```
///
/// The linear `c` term reaches `G(1)` only.
pub(crate) fn bit_pass(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &Padding,
    k: usize,
) -> RoundBatch {
    bit_pass_rows(bits, fold, r_eq, padding, k, None)
}

/// The same rounds, also storing the level-`t` folded `(a, b, c)` tables for the passes that follow.
pub(crate) fn bit_pass_storing(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &Padding,
    k: usize,
) -> (RoundBatch, [Vec<F192>; 3]) {
    // Every slot is written by the kernel, padding and tail included, so the tables start uninitialized.
    let n_pos = bits.a.len() / fold.n_chunks();
    let mut out: [Box<[MaybeUninit<F192>]>; 3] = std::array::from_fn(|_| Box::new_uninit_slice(n_pos));
    let batch = bit_pass_rows(bits, fold, r_eq, padding, k, Some(out.each_mut().map(|o| &mut o[..])));
    // SAFETY: the kernel writes every slot, padding and tail included.
    let tables = out.map(|o| unsafe { o.assume_init() }.into_vec());
    (batch, tables)
}

/// The bit pass of `k` rounds, by row width: a position at level `t` is `8 * 2^t` bytes, one kernel per width.
fn bit_pass_rows(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &Padding,
    k: usize,
    out: Option<[&mut [MaybeUninit<F192>]; 3]>,
) -> RoundBatch {
    fn by_rounds<const CHUNKS: usize>(
        bits: PackedWitness<'_>,
        fold: &BitFold,
        r_eq: &[F192],
        padding: &Padding,
        k: usize,
        out: Option<[&mut [MaybeUninit<F192>]; 3]>,
    ) -> RoundBatch {
        match k {
            2 => RoundBatch::new(&bit_pass_kernel::<CHUNKS, 2, 9>(bits, fold, r_eq, padding, out), r_eq),
            3 => RoundBatch::new(&bit_pass_kernel::<CHUNKS, 3, 27>(bits, fold, r_eq, padding, out), r_eq),
            4 => RoundBatch::new(&bit_pass_kernel::<CHUNKS, 4, 81>(bits, fold, r_eq, padding, out), r_eq),
            k => panic!("no bit pass of {k} rounds"),
        }
    }
    match fold.n_chunks() {
        8 => by_rounds::<8>(bits, fold, r_eq, padding, k, out),
        16 => by_rounds::<16>(bits, fold, r_eq, padding, k, out),
        32 => by_rounds::<32>(bits, fold, r_eq, padding, k, out),
        64 => by_rounds::<64>(bits, fold, r_eq, padding, k, out),
        128 => by_rounds::<128>(bits, fold, r_eq, padding, k, out),
        n => panic!("no bit pass for {n}-byte rows"),
    }
}

/// The `K`-round pass over rows of `CHUNKS` bytes: the `N = 3^K` grid sums its rounds are read from.
///
/// `out`, when given, receives every position's folded values, one slot each.
///
/// The identical tail is summed once from its last group, whose stored values are copied over the rest of it.
fn bit_pass_kernel<const CHUNKS: usize, const K: usize, const N: usize>(
    bits: PackedWitness<'_>,
    fold: &BitFold,
    r_eq: &[F192],
    padding: &Padding,
    mut out: Option<[&mut [MaybeUninit<F192>]; 3]>,
) -> [F192; N] {
    const { assert!(N == pow3(K)) };
    let rows = bits.rows::<CHUNKS>();
    let n_blocks = rows[0].len() >> K;
    assert!(n_blocks >= 1, "a block of positions per pass");
    assert_eq!(r_eq.len(), n_blocks.trailing_zeros() as usize + K - 1);
    if let Some(out) = &out {
        assert!(out.iter().all(|o| o.len() == n_blocks << K), "one output per position");
    }

    // `r_eq[..K - 1]` weight the pass's later rounds inside a block; the rest weight the blocks.
    // The low half is at least one fold step and leaves enough tasks to keep every worker busy on a small table.
    let block_vars = r_eq.len() + 1 - K;
    let min_low = unit_blocks(K).trailing_zeros() as usize;
    let low_vars = block_vars.saturating_sub(tmp_tasks_log()).clamp(min_low, EQ_LO_VARS);
    let SplitEq {
        low: eq_lo,
        high: eq_hi,
        ..
    } = SplitEq::with_low_vars(&r_eq[K - 1..], low_vars);
    let lo_size = eq_lo.len();

    // A block covers 64 skip bits times its `2^K * 2^t` bound rows.
    let block_log = (8 * CHUNKS).trailing_zeros() as usize + K;
    let live = LiveGroups::new(padding, block_log);
    // The blocks before the tail, in whole folded blocks of 64 positions, or packings of eight blocks.
    let m = block_log + n_blocks.trailing_zeros() as usize;
    let step_log = (8 * CHUNKS).trailing_zeros() as usize + 6usize.max(K + 3);
    let tail = padding.tail(m, block_log, step_log, r_eq);
    let head_blocks = tail.map_or(n_blocks, |t| t.head >> block_log);
    let is_live = |block: usize| block < head_blocks && live.contains(block);

    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi",
        target_feature = "avx512f",
        target_feature = "vpclmulqdq"
    ))]
    let eq_planes = (out.is_none() && lo_size >= unit_blocks(K)).then(|| planar::planes(&eq_lo));

    // One task per high eq index: `lo_size` blocks, `lo_size << K` outputs of each table.
    let chunks = out.as_mut().map(|o| o.each_mut().map(|o| Chunks::new(o, lo_size << K)));
    // Blocks per folded block of 64 positions.
    let per_fold = BLOCK >> K;

    let mut sums = parallel::map_reduce(
        head_blocks.div_ceil(lo_size),
        || [F192::ZERO; N],
        |hi| {
            #[cfg(all(
                target_arch = "x86_64",
                target_feature = "gfni",
                target_feature = "avx512bw",
                target_feature = "avx512vbmi",
                target_feature = "avx512f",
                target_feature = "vpclmulqdq"
            ))]
            if let Some(eq_planes) = &eq_planes {
                // SAFETY: the target features are enabled at compile time.
                let acc = unsafe {
                    planar::block_sums::<CHUNKS, K, N>(fold, rows, hi * lo_size, eq_planes, is_live)
                };
                return acc.map(|s| eq_hi[hi] * s.reduce());
            }
            // SAFETY: task `hi` takes chunk `hi` of each output once, and the buffers outlive the dispatch.
            let mut outs = chunks.as_ref().map(|c| c.each_ref().map(|c| unsafe { c.get(hi) }));
            let stream = Stream::new();
            let mut acc = [F192Unreduced::ZERO; N];
            let mut f = FoldedBlock::ZERO;
            for lo_first in (0..lo_size).step_by(per_fold) {
                let n = (lo_size - lo_first).min(per_fold);
                let block_first = hi * lo_size + lo_first;
                // The tail is summed and stored after the dispatch.
                if block_first >= head_blocks {
                    break;
                }
                let dst = lo_first << K..(lo_first + n) << K;
                // A folded block wholly in padding folds to zero.
                if !(block_first..block_first + n).any(is_live) {
                    if let Some(outs) = &mut outs {
                        for o in outs.iter_mut() {
                            o[dst.clone()].fill(MaybeUninit::new(F192::ZERO));
                        }
                    }
                    continue;
                }
                f.fold(fold, rows, block_first << K, n << K);
                for i in 0..n {
                    let at = i << K..(i + 1) << K;
                    let block = [&f.a[at.clone()], &f.b[at.clone()], &f.c[at]];
                    add_block::<K, N>(&mut acc, eq_lo[lo_first + i], block);
                }
                // Publish the block without a read: nothing touches these tables before the next pass.
                if let Some(outs) = &mut outs {
                    for (o, t) in outs.iter_mut().zip([&f.a, &f.b, &f.c]) {
                        stream.write(&mut o[dst.clone()], &t[..n << K]);
                    }
                }
            }
            acc.map(|s| eq_hi[hi] * s.reduce())
        },
        |x, y| std::array::from_fn(|i| x[i] + y[i]),
    );

    if let Some(tail) = tail {
        // The last group is summed, and stored in place, then copied over the rest of the tail.
        let group_len = 1 << (tail.group_log - block_log + K);
        let group_sums = bit_pass_kernel::<CHUNKS, K, N>(
            bits.suffix(group_len * CHUNKS),
            fold,
            &r_eq[..tail.r_inner],
            &padding.without_tail(),
            out.as_mut()
                .map(|o| o.each_mut().map(|o| &mut o[(n_blocks << K) - group_len..])),
        );
        for (s, g) in sums.iter_mut().zip(group_sums) {
            *s += tail.weight * g;
        }
        if let Some(out) = out {
            copy_group(out, head_blocks << K, group_len);
        }
    }
    sums
}

/// One round straight from the folded tables, `(G(1), G(inf))`, for the small tables at the end.
///
/// Positions `2x` and `2x + 1` pair up as the round's `X = 0` and `X = 1`, and `r_eq` weights the pairs:
///
/// ```text
///     G(1)   = sum_x eq(r_eq, x) * (a_1 b_1 + c_1)
///     G(inf) = sum_x eq(r_eq, x) * (a_0 + a_1)(b_0 + b_1)        the leading coefficient, in characteristic 2
/// ```
pub(crate) fn single_round([a, b, c]: [&[F192]; 3], r_eq: &[F192]) -> (F192, F192) {
    let n = a.len();
    assert!(n.is_power_of_two() && n >= 2);
    assert!(b.len() == n && c.len() == n, "a, b, c have one length");
    assert_eq!(r_eq.len(), n.trailing_zeros() as usize - 1);
    // One eq weight per pair, the pairs' `X = 1` and leading terms summed under it.
    let eq = eq_table(r_eq);
    let (mut g1, mut g_inf) = (F192::ZERO, F192::ZERO);
    for (x, &e) in eq.iter().enumerate() {
        let (a0, a1, b0, b1, c1) = (a[2 * x], a[2 * x + 1], b[2 * x], b[2 * x + 1], c[2 * x + 1]);
        g1 += e * (a1 * b1 + c1);
        g_inf += e * (a0 + a1) * (b0 + b1);
    }
    (g1, g_inf)
}

/// Bind a table's low variable at `chi`, in place: `v[x] = v[2x] + chi (v[2x] + v[2x + 1])`, halving it.
pub(crate) fn bind_low(v: &mut Vec<F192>, chi: F192) {
    let half = v.len() / 2;
    assert!(
        v.len() == 2 * half && half.is_power_of_two(),
        "a table of at least two, a power of two"
    );
    // Slot `x` is written after slots `2x` and `2x + 1` are read, so the bind runs in place.
    for x in 0..half {
        let (v0, v1) = (v[2 * x], v[2 * x + 1]);
        v[x] = v0 + chi * (v0 + v1);
    }
    v.truncate(half);
}

/// Rounds `t` and `t + 1` from the stored tables, folding the challenges still pending on them first.
///
/// - `ins` are the `(a, b, c)` tables, one to four variables short of level `t`.
/// - `pending` are those variables' challenges, lowest first; each output folds `2^pending.len()` inputs.
/// - `outs` receive the level-`t` tables, every slot written.
/// - `r_eq` are the eq challenges of the variables round `t` does not bind.
/// - Each output covers `2^out_log` bits of the witness `padding` describes.
///
/// ```text
///     two pending:          read n values at level t - 2, write n / 4 at level t, send rounds t and t + 1
///     one round at a time:  n + n / 2 + n / 2 + n / 4 for the same two rounds
/// ```
///
/// The rounds are built from each quad of folded values while they are in registers, as in the bit pass.
pub(crate) fn table_pass(
    ins: [&[F192]; 3],
    outs: [&mut [MaybeUninit<F192>]; 3],
    pending: &[F192],
    r_eq: &[F192],
    padding: &Padding,
    out_log: usize,
) -> RoundBatch {
    let sums = match pending.len() {
        1 => table_pass_kernel::<1>(ins, outs, pending, r_eq, padding, out_log),
        2 => table_pass_kernel::<2>(ins, outs, pending, r_eq, padding, out_log),
        3 => table_pass_kernel::<3>(ins, outs, pending, r_eq, padding, out_log),
        4 => table_pass_kernel::<4>(ins, outs, pending, r_eq, padding, out_log),
        n => panic!("no table pass folds {n} pending challenges"),
    };
    RoundBatch::new(&sums, r_eq)
}

/// The table pass for `P` pending challenges `rhos`: the grid sums of its two rounds.
///
/// The identical tail's outputs are copies of its last group's.
fn table_pass_kernel<const P: usize>(
    ins: [&[F192]; 3],
    mut outs: [&mut [MaybeUninit<F192>]; 3],
    rhos: &[F192],
    r_eq: &[F192],
    padding: &Padding,
    out_log: usize,
) -> [F192; 9] {
    let n_out = ins[0].len() >> P;
    assert!(ins.iter().all(|t| t.len() == n_out << P), "a, b, c have one length");
    assert!(
        outs.iter().all(|t| t.len() == n_out),
        "each output is the folded length"
    );
    assert_eq!(rhos.len(), P);
    let n_quads = n_out / 4;
    assert!(n_quads >= 1, "two rounds need four positions");
    assert_eq!(r_eq.len(), n_quads.trailing_zeros() as usize + 1);

    // `r_eq[0]` weights round `t`'s split by `v`; the rest weight the quads.
    // At most `2^7` high eq indices, one task each: enough for every worker at every table size.
    let SplitEq {
        low: eq_lo,
        high: eq_hi,
        ..
    } = SplitEq::with_high_vars(&r_eq[1..], EQ_HIGH_VARS);
    let lo_size = eq_lo.len();

    // The quads before the tail, in the pairs the outputs are published in.
    let quad_log = out_log + 2;
    let m = quad_log + n_quads.trailing_zeros() as usize;
    let tail = padding.tail(m, quad_log, quad_log + 1, r_eq);
    let head_quads = tail.map_or(n_quads, |t| t.head >> quad_log);

    // One task per high eq index: `lo_size` quads, `4 * lo_size` outputs of each table.
    let (chunk_in, chunk_out) = ((4 * lo_size) << P, 4 * lo_size);
    let chunks = outs.each_mut().map(|o| Chunks::new(o, chunk_out));

    // The fold in the monomial basis: a weight per nonempty set `s` of the pending variables, their challenges' product.
    let mut weights = [F192::ONE; 16];
    for s in 1usize..1 << P {
        weights[s] = weights[s & (s - 1)] * rhos[s.trailing_zeros() as usize];
    }
    let splat = |w: F192| (w, w, w, w);

    // Four outputs of one table, each folded from its `2^P` inputs in one step:
    //
    //     z = sum_s rho^s * sum_{i in s} x_i        s over the sets of pending variables, i over their subsets
    //
    // That is the binds expanded, so its products are independent rather than a chain.
    let fold_quad = |g: &[F192]| -> [F192; 4] {
        let g = &g[..4 << P];
        // Output `j`'s subset sums, a sum of its inputs `i` per set: in characteristic 2, the inputs' Moebius transform.
        let mut x = [[F192::ZERO; 16]; 4];
        for (j, x) in x.iter_mut().enumerate() {
            x[..1 << P].copy_from_slice(&g[j << P..(j + 1) << P]);
            for v in 0..P {
                for s in (0..1 << P).filter(|s| s >> v & 1 == 1) {
                    x[s] = x[s] + x[s ^ (1 << v)];
                }
            }
        }
        let mut z = (x[0][0], x[1][0], x[2][0], x[3][0]);
        for s in 1..1 << P {
            let d = mul_quad((x[0][s], x[1][s], x[2][s], x[3][s]), splat(weights[s]));
            z = (z.0 + d.0, z.1 + d.1, z.2 + d.2, z.3 + d.3);
        }
        [z.0, z.1, z.2, z.3]
    };

    let mut sums = parallel::map_reduce(
        head_quads.div_ceil(lo_size),
        || [F192::ZERO; 9],
        |hi| {
            // SAFETY: task `hi` takes chunk `hi` of each output once, and the buffers outlive the dispatch.
            let mut outs = chunks.each_ref().map(|c| unsafe { c.get(hi) });
            let ins = ins.map(|t| &t[hi * chunk_in..(hi + 1) * chunk_in]);
            let stream = Stream::new();
            let mut acc = [F192Unreduced::ZERO; 9];
            // Two quads of a table are eight outputs, three whole cache lines, published at once.
            let mut staged = [[F192::ZERO; 8]; 3];
            let n_q = lo_size.min(head_quads - hi * lo_size);
            for q in 0..n_q {
                let [a, b, c] = ins.map(|t| fold_quad(&t[(4 * q) << P..(4 * (q + 1)) << P]));
                add_block::<2, 9>(&mut acc, eq_lo[q], [&a, &b, &c]);

                // Publish the folded values without a read: nothing touches them before the next pass.
                let half = 4 * (q % 2);
                for (stage, folded) in staged.iter_mut().zip([a, b, c]) {
                    stage[half..half + 4].copy_from_slice(&folded);
                }
                if q % 2 == 1 {
                    for (out, stage) in outs.iter_mut().zip(&staged) {
                        stream.write(&mut out[4 * (q - 1)..4 * (q + 1)], stage);
                    }
                } else if q + 1 == n_q {
                    // An odd last quad is stored alone.
                    for (out, stage) in outs.iter_mut().zip(&staged) {
                        out[4 * q..4 * q + 4].write_copy_of_slice(&stage[..4]);
                    }
                }
            }
            acc.map(|s| eq_hi[hi] * s.reduce())
        },
        |x, y| std::array::from_fn(|i| x[i] + y[i]),
    );

    if let Some(tail) = tail {
        // The last group is folded in place, then copied over the rest of the tail.
        let group_len = 1 << (tail.group_log - out_log);
        let group_ins = ins.map(|t| &t[t.len() - (group_len << P)..]);
        let group_sums = table_pass_kernel::<P>(
            group_ins,
            outs.each_mut().map(|o| &mut o[n_out - group_len..]),
            rhos,
            &r_eq[..tail.r_inner],
            &padding.without_tail(),
            out_log,
        );
        for (s, g) in sums.iter_mut().zip(group_sums) {
            *s += tail.weight * g;
        }
        copy_group(outs, head_quads * 4, group_len);
    }
    sums
}

/// Copy each table's last `group_len` values over its values from `head` on.
fn copy_group(tables: [&mut [MaybeUninit<F192>]; 3], head: usize, group_len: usize) {
    // Whole groups per copy task, about `2^12` values.
    let task = group_len.max(1 << 12);
    for t in tables {
        let tail = &mut t[head..];
        let (body, group) = tail.split_at_mut(tail.len() - group_len);
        let group = &*group;
        parallel::chunks_mut(body, task, |_, dst| {
            for d in dst.chunks_exact_mut(group_len) {
                d.copy_from_slice(group);
            }
        });
    }
}

/// The bit pass on coefficient planes, eight blocks to a packing, so no product packs or unpacks a value.
///
/// The fold leaves each table's values as three registers per block position, one per coefficient:
///
/// ```text
///     plane k, register j, word l   =   coefficient k of position j of block l of the packing
/// ```
///
/// That is exactly the field packing's own layout, eight elements a register per coefficient.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi",
    target_feature = "avx512f",
    target_feature = "vpclmulqdq"
))]
mod planar {
    use core::arch::x86_64::{__m512i, _mm512_setzero_si512, _mm512_shuffle_i64x2};

    use primitives::bit_fold::{BLOCK, BitFold};
    use primitives::field::gf2_64x3::x86_64::{F192x8, F192x8Sum};
    use primitives::field::{F192, F192Unreduced};

    use super::{extend, grid_of, unit_blocks};

    /// The eq table, eight consecutive weights a packing, one register per coefficient.
    pub(super) fn planes(values: &[F192]) -> Vec<F192x8> {
        let (groups, rest) = values.as_chunks::<8>();
        assert!(rest.is_empty(), "whole groups of eight");
        groups
            .iter()
            .map(|g| {
                // SAFETY: eight words are one register, and any bit pattern is a valid one.
                let plane =
                    |k: fn(&F192) -> u64| unsafe { core::mem::transmute::<[u64; 8], __m512i>(g.each_ref().map(k)) };
                F192x8([plane(|e| e.c0), plane(|e| e.c1), plane(|e| e.c2)])
            })
            .collect()
    }

    /// The `N = 3^K` grid sums over the blocks from `block_first`, one packing of eq weights per eight blocks.
    ///
    /// The eq weight multiplies the `a` values first, so every term is a product of two operands:
    ///
    /// ```text
    ///     eq (a(p) b(p) + c(p)) = (eq a)(p) b(p) + eq c(p)
    /// ```
    ///
    /// Per block, `2^K` products `eq a` reduced, then `3^K - 1` grid terms and `2^K - 1` `c` terms summed unreduced.
    #[inline]
    #[target_feature(
        enable = "avx512f",
        enable = "avx512bw",
        enable = "avx512vbmi",
        enable = "gfni",
        enable = "vpclmulqdq"
    )]
    pub(super) fn block_sums<const CHUNKS: usize, const K: usize, const N: usize>(
        fold: &BitFold,
        rows: [&[[u8; CHUNKS]]; 2],
        block_first: usize,
        eq: &[F192x8],
        live: impl Fn(usize) -> bool,
    ) -> [F192Unreduced; N] {
        let zero = F192x8([_mm512_setzero_si512(); 3]);
        let mut acc = [F192x8Sum::zero(); N];
        let unit = unit_blocks(K);
        // The `a`, `b` and `c = a AND b` planes of the 64 rows from `first`.
        let fold_rows = |first: usize| -> [[[__m512i; 8]; 3]; 3] {
            let [ra, rb]: [&[[u8; CHUNKS]; BLOCK]; 2] =
                rows.map(|t| t[first..first + BLOCK].try_into().expect("a block"));
            let mut rc = [[0u8; CHUNKS]; BLOCK];
            super::and_rows(ra, rb, &mut rc);
            [ra, rb, &rc].map(|t| fold.fold_planes::<CHUNKS, K>(t))
        };
        for (u, eq) in eq.chunks_exact(unit / 8).enumerate() {
            let b0 = block_first + unit * u;
            // A unit wholly in padding folds to zero.
            if !(b0..b0 + unit).any(&live) {
                continue;
            }
            let lo = fold_rows(b0 << K);
            // Blocks of 16 are two folds, their halves a block's positions 0..8 and 8..16 (see `fold_planes`).
            let hi = (K == 4).then(|| fold_rows((b0 << K) + BLOCK));

            for (g, &e) in eq.iter().enumerate() {
                // Position `j` of the packing's eight blocks, of table `t`.
                let at = |t: usize, j: usize| {
                    F192x8(std::array::from_fn(|k| match &hi {
                        None => lo[t][k][j + (g << K)],
                        Some(hi) if j < 8 => _mm512_shuffle_i64x2::<0x44>(lo[t][k][j], hi[t][k][j]),
                        Some(hi) => _mm512_shuffle_i64x2::<0xEE>(lo[t][k][j - 8], hi[t][k][j - 8]),
                    }))
                };
                let (mut ea, mut eb) = ([zero; N], [zero; N]);
                for j in 0..1 << K {
                    let p = grid_of(j);
                    (ea[p], eb[p]) = (e.mul(at(0, j)), at(1, j));
                    if j != 0 {
                        acc[p].mul_add(e, at(2, j));
                    }
                }
                extend(&mut ea, K, |x, y| x.add(y));
                extend(&mut eb, K, |x, y| x.add(y));
                for p in 1..N {
                    acc[p].mul_add(ea[p], eb[p]);
                }
            }
        }
        acc.map(|s| s.total())
    }
}

#[cfg(test)]
mod tests {
    use primitives::multilinear::skip_lagrange_weights;
    use primitives::test_util::Rng;

    use super::*;
    use crate::zerocheck::round1::tests::pack_bits;

    const K_SKIP: usize = crate::zerocheck::K_SKIP;

    /// The bits of a cube folded at `z` over the skip: one value per position past it.
    fn fold_at_z(bits: &[bool], lagrange: &[F192]) -> Vec<F192> {
        (bits.chunks(1 << K_SKIP))
            .map(|row| (row.iter().zip(lagrange)).fold(F192::ZERO, |acc, (&bit, &w)| if bit { acc + w } else { acc }))
            .collect()
    }

    /// A random honest witness over `2^m` bits, `c = a AND b`: the bits, then `a` and `b` packed.
    fn random_witness(rng: &mut Rng, m: usize) -> ([Vec<bool>; 3], [Vec<u8>; 2]) {
        let (a, b) = (rng.bits(1 << m), rng.bits(1 << m));
        let c = a.iter().zip(&b).map(|(x, y)| x & y).collect();
        let packed = [pack_bits(&a), pack_bits(&b)];
        ([a, b, c], packed)
    }

    fn packed(p: &[Vec<u8>; 2]) -> PackedWitness<'_> {
        PackedWitness { a: &p[0], b: &p[1] }
    }

    /// Bind every table's low variable at `chi`.
    fn bind_all(tables: &mut [Vec<F192>; 3], chi: F192) {
        for t in tables {
            bind_low(t, chi);
        }
    }

    /// One round of the stored tables.
    fn round_of(t: &[Vec<F192>; 3], r_eq: &[F192]) -> (F192, F192) {
        single_round([&t[0], &t[1], &t[2]], r_eq)
    }

    /// Every round of `batch` against the naive route from `tables`, binding `rho` one round at a time.
    fn check_batch(batch: &RoundBatch, tables: &[Vec<F192>; 3], r_eq: &[F192], rho: &[F192], what: &str) {
        let mut naive = tables.clone();
        for i in 0..batch.len() {
            assert_eq!(batch.round(&rho[..i]), round_of(&naive, &r_eq[i..]), "{what}, round {i}");
            bind_all(&mut naive, rho[i]);
        }
    }

    #[test]
    fn single_round_is_the_round_polynomial() {
        // Invariant: G(0), G(1) and G(inf) interpolate the round polynomial, which has degree two.
        //
        //     G(X) = sum_x eq(r_eq, x) (a(X, x) b(X, x) + c(X, x))
        //     G(X) = G(0) (1 + X) + G(1) X + G(inf) X (1 + X)          in characteristic 2
        let mut rng = Rng::new(55);
        let t: [Vec<F192>; 3] = std::array::from_fn(|_| rng.ext_vec(16));
        let r_eq = rng.ext_vec(3);
        let eq = eq_table(&r_eq);
        let at = |x: F192| {
            (eq.iter().enumerate()).fold(F192::ZERO, |acc, (i, &e)| {
                let [a, b, c] = t.each_ref().map(|v| v[2 * i] + x * (v[2 * i] + v[2 * i + 1]));
                acc + e * (a * b + c)
            })
        };
        let (g1, g_inf) = round_of(&t, &r_eq);
        let g0 = at(F192::ZERO);
        assert_eq!(g1, at(F192::ONE));
        let x = rng.ext();
        assert_eq!(at(x), g0 * (F192::ONE + x) + g1 * x + g_inf * x * (F192::ONE + x));
    }

    #[test]
    fn bit_passes_match_the_naive_route() {
        // Invariant: a bit pass of k rounds sends round t, and each later round once the challenges before it are
        // known; the storing one stores level t.
        //
        // Naive route: fold the bits at z over the skip, bind rho_1..rho_t one at a time, then sum each round.
        //
        // Fixture state: 13 variables, the smallest cube, then 19, whose first passes split their eq tables over tasks.
        for m in [13, 14, 19] {
            let mut rng = Rng::new(0xB17_0000 + m as u64);
            let (bits, packed_bits) = random_witness(&mut rng, m);
            let r_rest = rng.ext_vec(m - K_SKIP);
            let rho = rng.ext_vec(m - K_SKIP);
            let lagrange = skip_lagrange_weights(K_SKIP, rng.ext());
            let dense = Padding::dense(m);

            // Level 0 of the naive route.
            let mut tables = bits.each_ref().map(|b| fold_at_z(b, &lagrange));
            for t in 0..=4 {
                let fold = BitFold::at_level(&lagrange, &rho[..t]);
                let r_eq = &r_rest[t + 1..];
                for k in (2..=MAX_PASS_ROUNDS).filter(|&k| t + k <= m - K_SKIP) {
                    let batch = bit_pass(packed(&packed_bits), &fold, r_eq, &dense, k);
                    let (stored_batch, stored) = bit_pass_storing(packed(&packed_bits), &fold, r_eq, &dense, k);
                    assert_eq!(stored, tables, "stored tables, m={m}, t={t}, k={k}");
                    check_batch(&batch, &tables, r_eq, &rho[t..], &format!("pass, m={m}, t={t}, k={k}"));
                    let what = format!("storing pass, m={m}, t={t}, k={k}");
                    check_batch(&stored_batch, &tables, r_eq, &rho[t..], &what);
                }
                bind_all(&mut tables, rho[t]);
            }
        }
    }

    #[test]
    fn bit_passes_skip_padding_exactly() {
        // Invariant: on blocks whose bits past the useful ones are zero, skipping them changes no message or table.
        //
        // Fixture state, (m, k_log, useful): BLAKE2s, an odd boundary, and two blocks per row at level 4.
        for (m, k_log, useful) in [(17usize, 14usize, 16_000usize), (17, 14, 15_409), (18, 15, 31_401)] {
            let mut rng = Rng::new(0xFADE_F00D + (k_log * 31 + useful) as u64);
            let mut bit = |i: usize| i % (1 << k_log) < useful && rng.bit();
            let a: Vec<bool> = (0..1 << m).map(&mut bit).collect();
            let b: Vec<bool> = (0..1 << m).map(&mut bit).collect();
            let packed_bits = [pack_bits(&a), pack_bits(&b)];
            let padding = Padding {
                k_log,
                useful_bits: useful,
                live_blocks: usize::MAX,
            };
            let lagrange = skip_lagrange_weights(K_SKIP, rng.ext());
            let r_rest = rng.ext_vec(m - K_SKIP);
            let rho = rng.ext_vec(4);
            for t in 0..=4 {
                let fold = BitFold::at_level(&lagrange, &rho[..t]);
                let r_eq = &r_rest[t + 1..];
                for k in 2..=MAX_PASS_ROUNDS {
                    let run = |p: &Padding| {
                        (
                            bit_pass(packed(&packed_bits), &fold, r_eq, p, k),
                            bit_pass_storing(packed(&packed_bits), &fold, r_eq, p, k),
                        )
                    };
                    assert_eq!(run(&Padding::dense(m)), run(&padding), "m={m}, useful={useful}, t={t}, k={k}");
                }
            }
        }
    }

    #[test]
    fn a_table_pass_is_one_round_at_a_time() {
        // Invariant: folding the pending challenges and sending two rounds in one pass is the tables and messages of
        // folding and summing one round at a time.
        //
        // Fixture state: one to four pending challenges, from one quad of outputs up to 2^10 of them.
        let mut rng = Rng::new(0x7AB1E);
        for k in 1..=MAX_PASS_ROUNDS {
            for log_out in [2, 3, 6, 12] {
                let tables: [Vec<F192>; 3] = std::array::from_fn(|_| rng.ext_vec(1 << (log_out + k)));
                let pending = rng.ext_vec(k);
                let r_eq = rng.ext_vec(log_out - 1);
                let rho_t = rng.ext();

                // Reference: bind each pending challenge, sum round t, bind rho_t, sum round t + 1.
                let mut naive = tables.clone();
                for &rho in &pending {
                    bind_all(&mut naive, rho);
                }
                let level = naive.clone();
                let first = round_of(&naive, &r_eq);
                bind_all(&mut naive, rho_t);
                let second = round_of(&naive, &r_eq[1..]);

                // The pass under test.
                let mut outs: [Box<[MaybeUninit<F192>]>; 3] =
                    std::array::from_fn(|_| Box::new_uninit_slice(1 << log_out));
                let batch = table_pass(
                    tables.each_ref().map(Vec::as_slice),
                    outs.each_mut().map(|o| &mut o[..]),
                    &pending,
                    &r_eq,
                    &Padding::dense(log_out),
                    0,
                );
                // SAFETY: the pass writes every slot of its outputs.
                let outs = outs.map(|o| unsafe { o.assume_init() }.into_vec());
                assert_eq!(outs, level, "tables, k={k}, log_out={log_out}");
                assert_eq!(batch.round(&[]), first, "round t, k={k}, log_out={log_out}");
                assert_eq!(batch.round(&[rho_t]), second, "round t + 1, k={k}, log_out={log_out}");
            }
        }
    }
}
