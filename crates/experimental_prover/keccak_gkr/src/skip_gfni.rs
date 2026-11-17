//! The four bit-level rounds' sums over a block, on residues (GFNI, with AVX-512 or AVX2): per
//! [`slot`], the polynomial [`skip_row`](crate::kernels::skip_row) sums over the block.
//!
//! A row's term `w[x] e[x + 1] e[x + 2]`, a weight of 128 coefficients times two embeddings of 24,
//! has degree at most `127 + 23 + 23 = 173`, and so has a block's sum. A binary polynomial of degree
//! below 192 is fixed by its residues modulo 24 distinct irreducibles of degree 8, whose product has
//! degree 192. Its residue modulo one is its value at a root in GF(2^8), the field of GF2P8MULB: a
//! byte, where a sum is a XOR and a product a byte product. Of the 30 irreducibles of degree 8,
//! [`POWERS`] takes a root of 24, a quadword of a register each.
//!
//! So nothing is a carry-less product: affine byte maps send the witness's bytes and the weights' to
//! residues ([`EVAL`], [`WEIGHT`]), and a slot's products are byte products. Once a block, a slot's
//! residues are summed over its eight slices and affine byte maps send them back to coefficients
//! ([`CRT`], the inverse of the residue map).

use core::arch::x86_64::*;

use primitives::hash::positions::row_positions;
use verifier::keccak::{BITS, EMBED_BITS};

use crate::kernels::{GROUP, SLOTS, slot};
use crate::rmfe::RMFE;
use crate::witness::BLOCK_WORDS;

/// Points a polynomial is held at.
const POINTS: usize = 24;
const _: () = assert!(
    127 + 2 * (EMBED_BITS - 1) < 8 * POINTS,
    "a slot's sum has more coefficients than the points fix"
);
cfg_select! {
    all(target_feature = "avx512f", target_feature = "avx512bw") => {
        type Reg = __m512i;
        /// Quadwords of a register.
        const LANES: usize = 8;

        // SAFETY (every wrapper here): AVX-512F, AVX-512BW and GFNI are enabled at compile time
        // (the cfgs), and a load or store is of the words named.

        /// `x` in every quadword.
        #[inline(always)]
        fn splat(x: u64) -> Reg {
            unsafe { _mm512_set1_epi64(x as i64) }
        }

        #[inline(always)]
        fn load(words: &[u64; LANES]) -> Reg {
            unsafe { _mm512_loadu_si512(words.as_ptr().cast()) }
        }

        #[inline(always)]
        fn store(v: Reg) -> [u64; LANES] {
            let mut words = [0; LANES];
            unsafe { _mm512_storeu_si512(words.as_mut_ptr().cast(), v) };
            words
        }

        #[inline(always)]
        fn xor(a: Reg, b: Reg) -> Reg {
            unsafe { _mm512_xor_si512(a, b) }
        }

        /// Each byte of `bytes` through the affine byte map of its quadword of `matrices`.
        #[inline(always)]
        fn map(bytes: Reg, matrices: Reg) -> Reg {
            unsafe { _mm512_gf2p8affine_epi64_epi8(bytes, matrices, 0) }
        }

        /// The byte products.
        #[inline(always)]
        fn mul(a: Reg, b: Reg) -> Reg {
            unsafe { _mm512_gf2p8mul_epi8(a, b) }
        }
    }
    _ => {
        type Reg = __m256i;
        /// Quadwords of a register.
        const LANES: usize = 4;

        // SAFETY (every wrapper here): AVX2 and GFNI are enabled at compile time (the module's
        // cfg), and a load or store is of the words named.

        /// `x` in every quadword.
        #[inline(always)]
        fn splat(x: u64) -> Reg {
            unsafe { _mm256_set1_epi64x(x as i64) }
        }

        #[inline(always)]
        fn load(words: &[u64; LANES]) -> Reg {
            unsafe { _mm256_loadu_si256(words.as_ptr().cast()) }
        }

        #[inline(always)]
        fn store(v: Reg) -> [u64; LANES] {
            let mut words = [0; LANES];
            unsafe { _mm256_storeu_si256(words.as_mut_ptr().cast(), v) };
            words
        }

        #[inline(always)]
        fn xor(a: Reg, b: Reg) -> Reg {
            unsafe { _mm256_xor_si256(a, b) }
        }

        /// Each byte of `bytes` through the affine byte map of its quadword of `matrices`.
        #[inline(always)]
        fn map(bytes: Reg, matrices: Reg) -> Reg {
            unsafe { _mm256_gf2p8affine_epi64_epi8(bytes, matrices, 0) }
        }

        /// The byte products.
        #[inline(always)]
        fn mul(a: Reg, b: Reg) -> Reg {
            unsafe { _mm256_gf2p8mul_epi8(a, b) }
        }
    }
}

/// Registers of a value: a point to a quadword, a slice to a byte.
const RESIDUES: usize = POINTS / LANES;
/// Words of a block's sum at a slot, a polynomial of fewer than `8 * POINTS` coefficients.
const WORDS: usize = POINTS / 8;

/// The byte product: binary polynomials modulo `x^8 + x^4 + x^3 + x + 1`.
const fn gf_mul(a: u8, b: u8) -> u8 {
    let (mut a, mut product) = (a, 0);
    let mut i = 0;
    while i < 8 {
        if b >> i & 1 == 1 {
            product ^= a;
        }
        a = a << 1 ^ if a >> 7 == 1 { 0x1b } else { 0 };
        i += 1;
    }
    product
}

/// `POWERS[i][n]` is point `i` to the power `n`. A point is the least of its eight conjugates, the
/// roots of its irreducible, so no two share one; an element of a proper subfield has fewer.
const POWERS: [[u8; 8 * POINTS]; POINTS] = {
    let mut powers = [[1u8; 8 * POINTS]; POINTS];
    let (mut i, mut t) = (0, 0u8);
    while i < POINTS {
        t += 1;
        let (mut conjugate, mut least) = (t, true);
        let mut k = 1;
        while k < 8 {
            conjugate = gf_mul(conjugate, conjugate);
            least &= conjugate > t;
            k += 1;
        }
        if least {
            let mut n = 1;
            while n < 8 * POINTS {
                powers[i][n] = gf_mul(powers[i][n - 1], t);
                n += 1;
            }
            i += 1;
        }
    }
    powers
};

/// The matrix of the affine byte map sending bit `i` of a byte to `images[i]`: the map reads
/// output bit `t` off matrix byte `7 - t`.
const fn byte_map(images: [u8; 8]) -> u64 {
    let mut matrix = 0u64;
    let mut t = 0;
    while t < 8 {
        let mut i = 0;
        while i < 8 {
            matrix |= ((images[i] >> t & 1) as u64) << (8 * (7 - t) + i);
            i += 1;
        }
        t += 1;
    }
    matrix
}

/// A GF(2)-linear map from a byte to a byte per point (or per byte of a polynomial), as affine
/// byte maps: quadword `k` of register `m` is the matrix to byte `LANES * m + k`, which a register
/// applies to eight bytes at once.
type Maps = [[u64; LANES]; RESIDUES];

/// `EVAL[h]` sends byte `h` of a pack to the residues of its share of the pack's embedding.
const EVAL: [Maps; 2] = {
    let mut maps = [[[0u64; LANES]; RESIDUES]; 2];
    let mut h = 0;
    while h < 2 {
        let mut i = 0;
        while i < POINTS {
            let mut images = [0u8; 8];
            let mut c = 0;
            while c < 8 * EMBED_BITS {
                let (b, n) = (c / EMBED_BITS, c % EMBED_BITS);
                if RMFE.emb[8 * h + b] >> n & 1 == 1 {
                    images[b] ^= POWERS[i][n];
                }
                c += 1;
            }
            maps[h][i / LANES][i % LANES] = byte_map(images);
            i += 1;
        }
        h += 1;
    }
    maps
};

/// `WEIGHT[a]` sends byte `a` of a weight, a polynomial of 128 coefficients, to its residues.
const WEIGHT: [Maps; 16] = {
    let mut maps = [[[0u64; LANES]; RESIDUES]; 16];
    let mut a = 0;
    while a < 16 {
        let mut i = 0;
        while i < POINTS {
            let mut images = [0u8; 8];
            let mut b = 0;
            while b < 8 {
                images[b] = POWERS[i][8 * a + b];
                b += 1;
            }
            maps[a][i / LANES][i % LANES] = byte_map(images);
            i += 1;
        }
        a += 1;
    }
    maps
};

/// `CRT[i]` sends the residue at point `i` to the bytes of the polynomial of fewer than
/// `8 * POINTS` coefficients with that residue and zero at the other points: column `i` of the
/// inverse of the residue map on such polynomials, by Gauss-Jordan elimination.
const CRT: [Maps; POINTS] = {
    const N: usize = 8 * POINTS;
    // Row `8 i + t` sends a polynomial to bit `t` of its residue at point `i`, beside the row of
    // the identity that the row operations turn into the inverse's.
    let mut rows = [[0u64; 2 * WORDS]; N];
    let mut r = 0;
    while r < N {
        let mut n = 0;
        while n < N {
            rows[r][n / 64] |= ((POWERS[r / 8][n] >> (r % 8) & 1) as u64) << (n % 64);
            n += 1;
        }
        rows[r][WORDS + r / 64] |= 1 << (r % 64);
        r += 1;
    }
    let mut c = 0;
    while c < N {
        let mut p = c;
        while rows[p][c / 64] >> (c % 64) & 1 == 0 {
            p += 1;
        }
        let pivot = rows[p];
        rows.swap(p, c);
        let mut r = 0;
        while r < N {
            if r != c && rows[r][c / 64] >> (c % 64) & 1 == 1 {
                let mut k = 0;
                while k < 2 * WORDS {
                    rows[r][k] ^= pivot[k];
                    k += 1;
                }
            }
            r += 1;
        }
        c += 1;
    }
    // Row `n` sends the residues to coefficient `n`: bit `n % 8` of byte `n / 8`, which a map
    // reads off matrix byte `7 - n % 8`.
    let mut maps = [[[0u64; LANES]; RESIDUES]; POINTS];
    let mut n = 0;
    while n < N {
        let mut r = 0;
        while r < N {
            let bit = rows[n][WORDS + r / 64] >> (r % 64) & 1;
            maps[r / 8][n / 8 / LANES][n / 8 % LANES] |= bit << (8 * (7 - n % 8) + r % 8);
            r += 1;
        }
        n += 1;
    }
    maps
};

/// The bytes an affine byte map `x` sends to the transpose of `x`: byte `7 - t` of
/// `map(splat(COLUMNS), x)` holds bit `t` of each byte of `x`.
const COLUMNS: u64 = 0x0102_0408_1020_4080;

/// Eight rows of 32 bytes, transposed: byte `z` of quadword `b` is byte `b` of row `z`. Three
/// rounds of interleaving, of bytes, pairs and fours, leave each 128-bit half in its own place.
#[inline(always)]
fn transpose_bytes(rows: [[u64; 4]; 8]) -> [u64; 32] {
    // SAFETY: AVX2 is enabled at compile time (the module's cfg); each load is of a row, and each
    // store of a half register into two of the 32 words.
    unsafe {
        let rows: [__m256i; 8] = rows.map(|row| _mm256_loadu_si256(row.as_ptr().cast()));
        let a: [__m256i; 8] = std::array::from_fn(|i| {
            if i % 2 == 0 {
                _mm256_unpacklo_epi8(rows[i], rows[i + 1])
            } else {
                _mm256_unpackhi_epi8(rows[i - 1], rows[i])
            }
        });
        // `b[4 r + c]`, in lane `l`: bytes `16 l + 4 c ..` of rows `4 r ..`.
        let b: [__m256i; 8] = std::array::from_fn(|i| {
            let (r, c) = (i / 4, i % 4);
            let (x, y) = (a[4 * r + c / 2], a[4 * r + 2 + c / 2]);
            if c % 2 == 0 {
                _mm256_unpacklo_epi16(x, y)
            } else {
                _mm256_unpackhi_epi16(x, y)
            }
        });
        // Register `d` holds bytes `2 d, 2 d + 1` of the rows, then bytes `16 + 2 d, 17 + 2 d`.
        let mut out = [0u64; 32];
        for d in 0..8 {
            let (x, y) = (b[d / 2], b[4 + d / 2]);
            let v = if d % 2 == 0 {
                _mm256_unpacklo_epi32(x, y)
            } else {
                _mm256_unpackhi_epi32(x, y)
            };
            _mm256_storeu2_m128i(
                out.as_mut_ptr().add(16 + 2 * d).cast(),
                out.as_mut_ptr().add(2 * d).cast(),
                v,
            );
        }
        out
    }
}

/// `acc += maps(b)` for each byte `b` of `bytes`, kept in `b`'s byte of every quadword.
#[inline(always)]
fn add_mapped(acc: &mut [Reg; RESIDUES], bytes: u64, maps: &Maps) {
    let bytes = splat(bytes);
    for (acc, matrices) in acc.iter_mut().zip(maps) {
        *acc = xor(*acc, map(bytes, load(matrices)));
    }
}

/// The factors of a slot's three products, which [`SkipBlock`] extends together: `e[0], e[2], e[4]`
/// and their cofactors.
const FACTORS: usize = 6;

/// The points of `{0, 1, infinity}^2` of two variables, in the order
/// [`extend_group`](crate::kernels::extend_group) builds a vector's values: the four binary
/// points, the four mixed ones `0 + 1, 2 + 3, 0 + 2, 1 + 3`, then the sum of all four.
const POINTS2: usize = 9;

/// A register of residues of a group's sums per point of the low and the high two variables, both
/// of [`POINTS2`], the eight slices apart.
type Acc = [[Reg; POINTS2]; POINTS2];

/// Per [`slot`], its group and its points of the low and the high two variables, both of
/// [`POINTS2`]: [`extend_group`](crate::kernels::extend_group)'s outputs are the points where
/// they are not both binary. A padding slot is at two binary points, where nothing is summed.
const PLACE: [(usize, usize, usize); SLOTS] = {
    let mut place = [(0, 0, 0); SLOTS];
    let mut half = 0;
    while half < 2 {
        let mut low = 0;
        while low < POINTS2 {
            let mut high = 0;
            while high < POINTS2 {
                let i = match (low, high) {
                    (0..4, 0..4) => None,
                    (0..4, _) => Some(4 * (high - 4) + low),
                    (4..8, _) => Some(20 + 4 * high + (low - 4)),
                    _ => Some(56 + high),
                };
                if let Some(i) = i {
                    place[slot(half, i)] = (half, low, high);
                }
                high += 1;
            }
            low += 1;
        }
        half += 1;
    }
    place
};

/// [`skip_row`](crate::kernels::skip_row) over every row and slice of a block, eight slices at a
/// time, on residues: a register holds a value of eight slices at [`LANES`] points, so the
/// extension is a sum of registers and a product of two values is [`RESIDUES`] byte products of
/// registers.
///
/// A row's sum `sum over x of w[x] e[x + 1] e[x + 2]` is taken as
/// `e[2] (w[0] e[1] + w[1] e[3]) + e[4] (w[2] e[3] + w[3] e[0]) + e[0] (w[4] e[1])`: the three
/// cofactors are linear in the values, so they are multiplied out on the group's packs and extended
/// like them, and a slot takes three products.
pub struct SkipBlock {
    /// Per register of residues and group, the sums.
    acc: [[Acc; 2]; RESIDUES],
    /// Per slot, the block's sum.
    sums: [[u64; WORDS]; SLOTS],
    /// The [`FACTORS`] of a row.
    values: Values,
    /// The weights' residues, eight consecutive positions to an entry.
    weights: Vec<[Reg; RESIDUES]>,
}

impl SkipBlock {
    /// For blocks summed at the position weights `weights`, as polynomials.
    pub fn new(weights: &[[u64; 2]]) -> Box<Self> {
        let mut residues = vec![[splat(0); RESIDUES]; BITS / 8];
        for (residues, weights) in residues.iter_mut().zip(weights[..BITS].as_chunks::<8>().0) {
            let bytes = transpose_bytes(weights.map(|w| [w[0], w[1], 0, 0]));
            for (&bytes, maps) in bytes.iter().zip(&WEIGHT) {
                add_mapped(residues, bytes, maps);
            }
        }
        Box::new(Self {
            acc: [[[[splat(0); POINTS2]; POINTS2]; 2]; RESIDUES],
            sums: [[0; WORDS]; SLOTS],
            values: no_values(),
            weights: residues,
        })
    }

    /// Sum a block.
    pub fn run(&mut self, block: &[u64]) {
        self.acc = [[[[splat(0); POINTS2]; POINTS2]; 2]; RESIDUES];
        // A group over the whole block, then the other: one group's sums stay in cache.
        for half in 0..2 {
            for r in 0..5 {
                for z in (0..64).step_by(8) {
                    let js = row_positions(r, z);
                    // Eight positions from each `j`, each as its two groups of four words.
                    let bytes = js.map(|j| {
                        let groups = block[BLOCK_WORDS * j..][..8 * BLOCK_WORDS].as_chunks::<4>().0;
                        transpose_bytes(std::array::from_fn(|i| groups[2 * i + half]))
                    });
                    for m in 0..RESIDUES {
                        let w = js.map(|j| self.weights[j / 8][m]);
                        row(&mut self.acc[m][half], &mut self.values, m, &bytes, w);
                    }
                }
            }
        }
        self.reconstruct();
    }

    /// The block's sums as polynomials, eight slots at a time: a slot's residues are summed over its
    /// slices into a byte per point, and the eight slots' bytes share a quadword for [`CRT`].
    #[inline(always)]
    fn reconstruct(&mut self) {
        for g in 0..SLOTS / 8 {
            let mut residues = [splat(0); RESIDUES];
            for (i, &(half, low, high)) in PLACE[8 * g..][..8].iter().enumerate() {
                // Byte `i`: per quadword, the XOR of its eight bytes, the slices.
                let at = splat(0xff << (8 * i));
                for (residues, acc) in residues.iter_mut().zip(&self.acc) {
                    *residues = xor(*residues, map(at, map(splat(COLUMNS), acc[half][low][high])));
                }
            }
            let points = residues.map(store);
            let mut bytes = [splat(0); RESIDUES];
            for (&point, maps) in points.as_flattened().iter().zip(&CRT) {
                add_mapped(&mut bytes, point, maps);
            }
            // Byte `i` of quadword `b` is byte `b` of slot `i`'s polynomial: transposed, a
            // quadword is a word of a slot's.
            let bytes = bytes.map(store);
            let bytes = bytes.as_flattened();
            let words = transpose_bytes(std::array::from_fn(|z| [bytes[z], bytes[8 + z], bytes[16 + z], 0]));
            for i in 0..8 {
                self.sums[8 * g + i] = std::array::from_fn(|k| words[8 * k + i]);
            }
        }
    }

    /// The sum at slot `i`.
    pub fn get(&self, i: usize) -> [u64; 3] {
        self.sums[i]
    }
}

/// The residues of pack `q`'s embedding in each position of a row, `bytes` as [`SkipBlock::run`]
/// transposed them, `maps` the [`EVAL`] maps of a register of residues.
#[inline(always)]
fn embeddings(maps: &[Reg; 2], bytes: &[[u64; 32]; 5], q: usize) -> [Reg; 5] {
    std::array::from_fn(|x| {
        let [low, high] = [0, 1].map(|h| map(splat(bytes[x][2 * q + h]), maps[h]));
        xor(low, high)
    })
}

/// `put(f, value)` for each of the [`FACTORS`] of a pack, from its embeddings `e` in a row and the
/// row's weights `w`.
#[inline(always)]
fn factors(e: [Reg; 5], w: [Reg; 5], mut put: impl FnMut(usize, Reg)) {
    put(0, e[0]);
    put(1, e[2]);
    put(2, e[4]);
    put(3, xor(mul(e[1], w[0]), mul(e[3], w[1])));
    put(4, xor(mul(e[3], w[2]), mul(e[0], w[3])));
    put(5, mul(e[1], w[4]));
}

cfg_select! {
    all(target_feature = "avx512f", target_feature = "avx512bw") => {
        /// The [`FACTORS`] of a row's group of packs, a register each.
        type Values = [[Reg; GROUP]; FACTORS];

        fn no_values() -> Values {
            [[splat(0); GROUP]; FACTORS]
        }

        /// [`extend_group`](crate::kernels::extend_group) on registers, for [`FACTORS`] groups at
        /// once: `output(low, high, values)` takes every group's value at point `low` of the low
        /// two variables and `high` of the high two, both of [`POINTS2`]. The nine vectors of four
        /// are made one at a time and passed straight to `output`, so nothing is stored.
        #[inline(always)]
        fn extend8(v: &Values, mut output: impl FnMut(usize, usize, [Reg; FACTORS])) {
            for k in 0..9 {
                // Vector `k` of each group: one of its four, or a sum of them.
                let w: [[Reg; 4]; FACTORS] = std::array::from_fn(|f| {
                    std::array::from_fn(|l| {
                        let q = |k: usize| v[f][4 * k + l];
                        match k {
                            0..4 => q(k),
                            4 => xor(q(0), q(1)),
                            5 => xor(q(2), q(3)),
                            6 => xor(q(0), q(2)),
                            7 => xor(q(1), q(3)),
                            _ => xor(xor(q(0), q(1)), xor(q(2), q(3))),
                        }
                    })
                });
                if k >= 4 {
                    for l in 0..4 {
                        output(l, k, w.map(|w| w[l]));
                    }
                }
                let low = w.map(|w| [xor(w[0], w[1]), xor(w[2], w[3]), xor(w[0], w[2]), xor(w[1], w[3])]);
                for l in 0..4 {
                    output(4 + l, k, low.map(|low| low[l]));
                }
                output(8, k, low.map(|low| xor(low[0], low[1])));
            }
        }

        /// Adds to `acc` the products of register `m` of the residues of a row's group of packs,
        /// `bytes` as [`SkipBlock::run`] transposed them, at the row's weights `w`.
        #[inline(always)]
        fn row(acc: &mut Acc, values: &mut Values, m: usize, bytes: &[[u64; 32]; 5], w: [Reg; 5]) {
            let maps = [0, 1].map(|h| load(&EVAL[h][m]));
            for q in 0..GROUP {
                factors(embeddings(&maps, bytes, q), w, |f, value| values[f][q] = value);
            }
            extend8(values, |low, high, [e0, e2, e4, a, b, c]| {
                let acc = &mut acc[low][high];
                *acc = xor(xor(*acc, mul(e2, a)), xor(mul(e4, b), mul(e0, c)));
            });
        }
    }
    _ => {
        /// The [`FACTORS`] of each product.
        const PAIRS: [(usize, usize); 3] = [(1, 3), (2, 4), (0, 5)];

        /// The [`FACTORS`] of a row's group of packs, a register each, per vector of four packs at
        /// each low point but the last two, sums of others.
        type Values = [[[Reg; POINTS2 - 2]; 4]; FACTORS];

        fn no_values() -> Values {
            [[[splat(0); POINTS2 - 2]; 4]; FACTORS]
        }

        /// The value at each of [`POINTS2`] of four values on the binary points.
        #[inline(always)]
        fn extend4(v: [Reg; 4]) -> [Reg; POINTS2] {
            let (a, b) = (xor(v[0], v[1]), xor(v[2], v[3]));
            [v[0], v[1], v[2], v[3], a, b, xor(v[0], v[2]), xor(v[1], v[3]), xor(a, b)]
        }

        /// Adds to `acc` the products at the points of the high two variables that are not binary,
        /// of the [`FACTORS`] at a low point: `at(f, k)` is factor `f` on vector `k` there.
        #[inline(always)]
        fn mixed_high(acc: &mut [Reg; POINTS2], at: impl Fn(usize, usize) -> Reg) {
            let mut sums: [Reg; 5] = acc[4..].try_into().unwrap();
            for (f, g) in PAIRS {
                let [a, b] = [f, g].map(|f| extend4(std::array::from_fn(|k| at(f, k))));
                for (j, sum) in sums.iter_mut().enumerate() {
                    *sum = xor(*sum, mul(a[4 + j], b[4 + j]));
                }
            }
            acc[4..].copy_from_slice(&sums);
        }

        /// Adds to `acc` the products of register `m` of the residues of a row's group of packs,
        /// `bytes` as [`SkipBlock::run`] transposed them, at the row's weights `w`. With sixteen
        /// registers the [`FACTORS`] go through memory: each pack's are stored as they are made,
        /// then extended to the low points a vector at a time, taking the products at the binary
        /// points of the high two variables, then to the high points a low point at a time.
        #[inline(always)]
        fn row(acc: &mut Acc, values: &mut Values, m: usize, bytes: &[[u64; 32]; 5], w: [Reg; 5]) {
            let maps = [0, 1].map(|h| load(&EVAL[h][m]));
            for q in 0..GROUP {
                factors(embeddings(&maps, bytes, q), w, |f, value| values[f][q / 4][q % 4] = value);
            }
            for k in 0..4 {
                let mut sums = [splat(0); 5];
                for (f, g) in PAIRS {
                    let [a, b] = [f, g].map(|f| {
                        let v = &mut values[f][k];
                        let extended = extend4(v[..4].try_into().unwrap());
                        v[4..].copy_from_slice(&extended[4..POINTS2 - 2]);
                        extended
                    });
                    for (j, sum) in sums.iter_mut().enumerate() {
                        *sum = xor(*sum, mul(a[4 + j], b[4 + j]));
                    }
                }
                for (acc, sum) in acc[4..].iter_mut().zip(sums) {
                    acc[k] = xor(acc[k], sum);
                }
            }
            for (low, acc) in acc[..7].iter_mut().enumerate() {
                mixed_high(acc, |f, k| values[f][k][low]);
            }
            mixed_high(&mut acc[7], |f, k| xor(values[f][k][1], values[f][k][3]));
            mixed_high(&mut acc[8], |f, k| xor(values[f][k][4], values[f][k][5]));
        }
    }
}
