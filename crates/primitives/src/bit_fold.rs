//! Weighted sums of packed bit rows, the fold that turns witness bits into F192 values.
//!
//! A row is `8 * CHUNKS` bits and every bit carries a fixed F192 weight:
//!
//! ```text
//!     fold(row) = sum_{s : bit s of row is set} w_s
//! ```
//!
//! The map is GF(2)-linear in the row's bits, so it splits into one 8-bit piece per byte.
//!
//! - Portable: a 256-entry subset-sum table per byte, one lookup per byte.
//! - AVX-512 with GFNI: an 8x8 bit matrix per (input byte, output byte), applied to 64 rows by one instruction.
//! - AVX2: the same byte-sliced shape 32 rows wide, each map one affine instruction with GFNI, else two nibble lookups.

use crate::field::F192;

use crate::multilinear::eq_table;

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use core::arch::x86_64::__m512i;

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
use portable::{self as imp, Imp};

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use gfni::{self as imp, Imp};

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    not(all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"))
))]
use avx2::{self as imp, Imp};

/// Rows folded per call.
pub const BLOCK: usize = 64;

/// The weights of every bit of a row, prepared for folding.
#[derive(Clone, Debug)]
pub struct BitFold {
    /// Bytes per row.
    n_chunks: usize,
    /// The target's fold kernel data.
    imp: Imp,
}

impl BitFold {
    /// Prepare `weights`, one per bit of a row.
    ///
    /// # Panics
    ///
    /// Panics unless a row is 8, 16, 32, 64 or 128 bytes.
    pub fn new(weights: &[F192]) -> Self {
        let n_chunks = weights.len() / 8;
        assert!(
            weights.len() == 8 * n_chunks && n_chunks.is_power_of_two() && (8..=128).contains(&n_chunks),
            "a row is 8 to 128 bytes, a power of two"
        );
        Self {
            n_chunks,
            imp: Imp::new(weights),
        }
    }

    /// The fold of a position at multilinear level `t`, once `rho_1..rho_t` are bound.
    ///
    /// Position `q` covers the `2^t` consecutive rows `q * 2^t + u`, so its weights are a tensor:
    ///
    /// ```text
    ///     w[64 u + s] = eq(rho, u) * L_s(z)        u in 0..2^t, s in 0..64
    /// ```
    pub fn at_level(lagrange: &[F192], rho: &[F192]) -> Self {
        let weights: Vec<F192> = eq_table(rho)
            .iter()
            .flat_map(|&e| lagrange.iter().map(move |&l| e * l))
            .collect();
        Self::new(&weights)
    }

    /// Bytes per row.
    pub const fn n_chunks(&self) -> usize {
        self.n_chunks
    }

    /// Fold up to 64 consecutive rows into `out[..rows.len()]`.
    #[inline]
    pub fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK]) {
        debug_assert_eq!(CHUNKS, self.n_chunks);
        assert!(rows.len() <= BLOCK);
        self.imp.fold_block(rows, out);
    }

    /// Fold 64 consecutive rows into coefficient planes, grouped by quad.
    ///
    /// Plane `k`, register `u + 2v + 4g`, qword `l` is coefficient `k` of row `4 (8g + l) + u + 2v`.
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))]
    ///
    /// # Safety
    ///
    /// Requires AVX-512F, BW and VBMI and GFNI, which the target enables wherever this is compiled.
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
    pub fn fold_quads<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK]) -> [[__m512i; 8]; 3] {
        debug_assert_eq!(CHUNKS, self.n_chunks);
        self.imp.fold_quads(rows)
    }
}

/// A GF(2)-linear map from F192 to F192, given by the image of each of its 192 coordinate bits.
///
/// It is [`BitFold`] on the 24 bytes of an F192, whose input transpose is the inverse of the output's.
#[derive(Clone, Debug)]
pub struct F192Map {
    imp: Imp,
}

impl F192Map {
    /// The map sending coordinate bit `b` (bit `b % 64` of coefficient `b / 64`) to `weights[b]`.
    ///
    /// # Panics
    ///
    /// Panics unless there are 192 weights.
    pub fn new(weights: &[F192]) -> Self {
        assert_eq!(weights.len(), 192, "one weight per coordinate bit");
        Self {
            imp: Imp::new_f192(weights),
        }
    }

    /// Add the image of each of `xs` to `out`.
    #[inline]
    pub fn apply_add(&self, xs: &[F192; BLOCK], out: &mut [F192]) {
        assert!(out.len() <= BLOCK);
        self.imp.apply_add_f192(xs, out);
    }

    /// The map `x -> self(x * c)`, itself GF(2)-linear.
    pub fn after_mul(&self, c: F192) -> Self {
        let mut weights = [F192::ZERO; 192];
        for (chunk, w) in weights.chunks_mut(BLOCK).enumerate() {
            let xs: [F192; BLOCK] = std::array::from_fn(|i| {
                let bit = BLOCK * chunk + i;
                let mut words = [0u64; 3];
                words[bit / 64] = 1 << (bit % 64);
                F192::new(words[0], words[1], words[2]) * c
            });
            self.apply_add(&xs, w);
        }
        Self::new(&weights)
    }

    /// Add the image of each value of `xs` to `out`.
    #[inline]
    pub fn apply_sliced_add(&self, xs: &Sliced, out: &mut [F192]) {
        assert!(out.len() <= BLOCK);
        self.imp.apply_sliced_add(&xs.0, out);
    }
}

/// A block of values in the layout the map reads, so that a block mapped many times is transposed once.
#[derive(Clone, Debug)]
pub struct Sliced(imp::Sliced);

impl Sliced {
    /// The block `xs`.
    #[cfg_attr(
        not(all(target_arch = "x86_64", target_feature = "avx2")),
        expect(clippy::missing_const_for_fn, reason = "The SIMD layouts transpose the block.")
    )]
    pub fn new(xs: &[F192; BLOCK]) -> Self {
        Self(Imp::slice(xs))
    }
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
mod portable {
    use super::{BLOCK, F192};

    /// The fold of one row through the byte tables: one lookup and one XOR per byte.
    #[inline(always)]
    fn fold_row_lookup<const CHUNKS: usize>(tables: &[[F192; 256]], row: &[u8; CHUNKS]) -> F192 {
        let tables: &[[F192; 256]; CHUNKS] = tables.try_into().expect("one table per byte");
        row.iter()
            .zip(tables)
            .fold(F192::ZERO, |acc, (&v, sums)| acc + sums[usize::from(v)])
    }

    /// One 256-entry subset-sum table per byte of a row: entry `[j][v]` sums the weights of the set bits of `v` at byte `j`.
    fn lookup_tables(weights: &[F192]) -> Vec<[F192; 256]> {
        weights
            .as_chunks::<8>()
            .0
            .iter()
            .map(|w| {
                let mut sums = [F192::ZERO; 256];
                // Each entry adds its lowest set bit's weight to an entry already built.
                for v in 1..256usize {
                    let low = v.isolate_lowest_one();
                    sums[v] = sums[v ^ low] + w[low.trailing_zeros() as usize];
                }
                sums
            })
            .collect()
    }

    /// The byte tables.
    #[derive(Clone, Debug)]
    pub(super) struct Imp {
        /// One subset-sum table per byte of a row.
        tables: Vec<[F192; 256]>,
    }

    impl Imp {
        pub(super) fn new(weights: &[F192]) -> Self {
            Self {
                tables: lookup_tables(weights),
            }
        }

        pub(super) fn new_f192(weights: &[F192]) -> Self {
            Self::new(weights)
        }

        #[inline]
        pub(super) fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK]) {
            for (o, row) in out.iter_mut().zip(rows) {
                *o = fold_row_lookup(&self.tables, row);
            }
        }

        pub(super) const fn slice(xs: &[F192; BLOCK]) -> Sliced {
            *xs
        }

        #[inline]
        pub(super) fn apply_sliced_add(&self, xs: &Sliced, out: &mut [F192]) {
            self.apply_add_f192(xs, out);
        }

        #[inline]
        pub(super) fn apply_add_f192(&self, xs: &[F192; BLOCK], out: &mut [F192]) {
            for (o, x) in out.iter_mut().zip(xs) {
                let mut row = [0u8; 24];
                row[..8].copy_from_slice(&x.c0.to_le_bytes());
                row[8..16].copy_from_slice(&x.c1.to_le_bytes());
                row[16..].copy_from_slice(&x.c2.to_le_bytes());
                *o += fold_row_lookup(&self.tables, &row);
            }
        }
    }

    /// A block of values, as they are.
    pub(super) type Sliced = [F192; BLOCK];
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
pub mod gfni {
    //! The GFNI fold of 64 rows at a time.
    //!
    //! ```text
    //!     1. transpose   64 rows x CHUNKS bytes  ->  CHUNKS registers, register j = byte j of the 64 rows
    //!     2. multiply    out byte o += A[j][o] * (register j), one affine instruction for all 64 rows
    //!     3. transpose   24 registers of output bytes  ->  64 F192 values
    //! ```
    //!
    //! Both transposes are butterflies of two-register byte permutes.
    //!
    //! A stage swaps one bit of the byte offset inside a register with one bit of the register index.

    use core::arch::x86_64::*;
    use std::sync::LazyLock;

    use super::{BLOCK, F192};

    /// Bytes of an F192.
    pub const OUT_BYTES: usize = 24;

    /// One butterfly stage: registers `z` and `z | zbit` exchange bytes through two permutes.
    ///
    /// The caller passes `zbit` as a constant of its unrolled loop, so the registers never leave the register file.
    #[derive(Clone, Copy, Debug)]
    struct Stage {
        /// Byte sources of the low register of each pair; bit 6 picks the high one.
        lo: [u8; 64],
        /// Byte sources of the high register of each pair.
        hi: [u8; 64],
    }

    impl Stage {
        /// Swap byte-offset bit `fbit` with the register bit the stage is applied on, then permute each output by `sigma`.
        ///
        /// Output offset `f` takes the byte the plain swap leaves at offset `sigma(f)`.
        fn swap(fbit: usize, sigma: impl Fn(usize) -> usize) -> Self {
            // The plain swap: a byte keeps its offset except bit `fbit`, which trades places with the register bit.
            let lo = |f: usize| if f & fbit == 0 { f } else { 64 | (f ^ fbit) };
            let hi = |f: usize| if f & fbit == 0 { f | fbit } else { 64 | f };
            Self {
                lo: std::array::from_fn(|f| lo(sigma(f)) as u8),
                hi: std::array::from_fn(|f| hi(sigma(f)) as u8),
            }
        }

        /// Exchange bytes between registers `z` and `z | zbit`, for every `z` with that bit clear.
        #[inline]
        #[target_feature(enable = "avx512f", enable = "avx512vbmi")]
        fn apply<const N: usize>(&self, zbit: usize, regs: &mut [__m512i; N]) {
            // SAFETY: both index arrays are 64 bytes.
            let (lo, hi) = unsafe {
                (
                    _mm512_loadu_si512(self.lo.as_ptr().cast()),
                    _mm512_loadu_si512(self.hi.as_ptr().cast()),
                )
            };
            for k in 0..N / 2 {
                // Pair `k` with a zero inserted at bit `zbit`.
                let z = (k & (zbit - 1)) | ((k & !(zbit - 1)) << 1);
                let (u, w) = (regs[z], regs[z | zbit]);
                regs[z] = _mm512_permutex2var_epi8(u, lo, w);
                regs[z | zbit] = _mm512_permutex2var_epi8(u, hi, w);
            }
        }

        /// The stage undoing this one.
        fn inverse(&self) -> Self {
            let (mut lo, mut hi) = ([0u8; 64], [0u8; 64]);
            let mut place = |src: u8, pos: usize| {
                if src < 64 {
                    lo[usize::from(src)] = pos as u8;
                } else {
                    hi[usize::from(src) - 64] = pos as u8;
                }
            };
            for f in 0..64 {
                place(self.lo[f], f);
                place(self.hi[f], 64 | f);
            }
            Self { lo, hi }
        }
    }

    /// Stages taking eight registers of one output coefficient, register = byte `o` and offset = value `p`, to qwords.
    ///
    /// Stage `s` pairs on register bit `s`.
    ///
    /// ```text
    ///     after the stages     offset = (o, then p bits 0..3)     register = p bits 3..6
    /// ```
    ///
    /// So register `k`, qword `l` is the coefficient of value `8k + l`.
    static OUTPUT_STAGES: LazyLock<[Stage; 3]> = LazyLock::new(|| {
        let to_qwords = |f: usize| (f >> 3) | ((f & 7) << 3);
        [0, 1, 2].map(|s| Stage::swap(8 << s, |f| if s == 2 { to_qwords(f) } else { f }))
    });

    /// [`OUTPUT_STAGES`] undone: eight registers of one coefficient's qwords back to one register per byte.
    static INPUT_STAGES: LazyLock<[Stage; 3]> = LazyLock::new(|| {
        let [a, b, c] = &*OUTPUT_STAGES;
        [c.inverse(), b.inverse(), a.inverse()]
    });

    /// Stages taking eight registers of one output coefficient, register = byte `o` and offset = value `p`, to quad planes.
    ///
    /// Stage `s` pairs on register bit `s`.
    ///
    /// ```text
    ///     after the stages     offset = (o, then p bits 2..5)     register = p bits 0, 1, 5
    /// ```
    ///
    /// So register `u + 2v + 4g`, qword `l` is the coefficient of value `4 (8g + l) + u + 2v`: of quad `8g + l`, one register per `(u, v)`.
    static QUAD_STAGES: LazyLock<[Stage; 3]> = LazyLock::new(|| {
        // The plain swaps leave offset = (o0, o1, p2, p3, p4, o2).
        let to_qwords = |f: usize| (f & 3) | ((f >> 3) << 2) | (((f >> 2) & 1) << 5);
        [Stage::swap(1, |f| f), Stage::swap(2, |f| f), Stage::swap(32, to_qwords)]
    });

    /// Store 24 registers of output bytes, register `o` holding byte `o` of 64 values, as those 64 values.
    ///
    /// # Safety
    ///
    /// The CPU must have the enabled target features.
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512vbmi")]
    pub fn store_f192(acc: &[__m512i; OUT_BYTES], out: &mut [F192; BLOCK]) {
        // Per coefficient, eight registers of output bytes become eight registers of qwords.
        let [mut c0, mut c1, mut c2] = [[_mm512_setzero_si512(); 8]; 3];
        for o in 0..8 {
            (c0[o], c1[o], c2[o]) = (acc[o], acc[8 + o], acc[16 + o]);
        }
        let stages = &*OUTPUT_STAGES;
        for (s, stage) in stages.iter().enumerate() {
            stage.apply(1 << s, &mut c0);
            stage.apply(1 << s, &mut c1);
            stage.apply(1 << s, &mut c2);
        }

        // Interleave the three coefficients of values 8k..8k+8 into 24 consecutive qwords.
        //
        //     zmm 0   c0 c1 c2 | c0 c1 c2 | c0 c1        values 0, 1, 2
        //     zmm 1   c2 | c0 c1 c2 | c0 c1 c2 | c0      values 2, 3, 4, 5
        //     zmm 2   c1 c2 | c0 c1 c2 | c0 c1 c2        values 5, 6, 7
        //
        // Indices 0..8 pick c0, 8..16 pick c1; the masked permute then drops c2 into its slots.
        let idx01 = [
            _mm512_setr_epi64(0, 8, 0, 1, 9, 0, 2, 10),
            _mm512_setr_epi64(0, 3, 11, 0, 4, 12, 0, 5),
            _mm512_setr_epi64(13, 0, 6, 14, 0, 7, 15, 0),
        ];
        let idx2 = [
            _mm512_setr_epi64(0, 0, 0, 0, 0, 1, 0, 0),
            _mm512_setr_epi64(2, 0, 0, 3, 0, 0, 4, 0),
            _mm512_setr_epi64(0, 5, 0, 0, 6, 0, 0, 7),
        ];
        let mask2: [__mmask8; 3] = [0b0010_0100, 0b0100_1001, 0b1001_0010];
        let dst = out.as_mut_ptr().cast::<u8>();
        for k in 0..8 {
            for i in 0..3 {
                let v = _mm512_permutex2var_epi64(c0[k], idx01[i], c1[k]);
                let v = _mm512_mask_permutexvar_epi64(v, mask2[i], idx2[i], c2[k]);
                // SAFETY: the three stores of value group k cover out[8k..8k+8], 192 bytes.
                unsafe { _mm512_storeu_si512(dst.add(192 * k + 64 * i).cast(), v) };
            }
        }
    }

    /// Qword sources splitting 24 consecutive qwords of eight values into coefficient `i` of each value.
    ///
    /// Returns the two-register sources, the third-register sources, and the mask of lanes from the third.
    const fn split_index(i: usize) -> ([i64; 8], [i64; 8], u8) {
        let (mut lo, mut hi, mut mask) = ([0i64; 8], [0i64; 8], 0u8);
        let mut l = 0;
        while l < 8 {
            let q = 3 * l + i;
            if q < 16 {
                lo[l] = q as i64;
            } else {
                hi[l] = (q - 16) as i64;
                mask |= 1 << l;
            }
            l += 1;
        }
        (lo, hi, mask)
    }

    const SPLIT: [([i64; 8], [i64; 8], u8); 3] = [split_index(0), split_index(1), split_index(2)];

    /// Load 64 values as 24 registers of bytes, register `o` holding byte `o` of every value: [`store_f192`] undone.
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512vbmi")]
    fn load_f192(xs: &[F192; BLOCK]) -> [__m512i; OUT_BYTES] {
        let src = xs.as_ptr().cast::<u8>();
        // Coefficient `i` of values 8k..8k+8, one qword each.
        let split = |i: usize, k: usize| {
            let (lo, hi, mask) = &SPLIT[i];
            // SAFETY: values 8k..8k+8 are 192 bytes, three registers, and the index arrays are 64 bytes.
            unsafe {
                let v: [__m512i; 3] = std::array::from_fn(|r| _mm512_loadu_si512(src.add(192 * k + 64 * r).cast()));
                let q = _mm512_permutex2var_epi64(v[0], _mm512_loadu_si512(lo.as_ptr().cast()), v[1]);
                _mm512_mask_permutexvar_epi64(q, *mask, _mm512_loadu_si512(hi.as_ptr().cast()), v[2])
            }
        };
        let mut c: [[__m512i; 8]; 3] = std::array::from_fn(|i| std::array::from_fn(|k| split(i, k)));
        // The inverses run in reverse order, so stage `s` pairs on register bit `2 - s`.
        let stages = &*INPUT_STAGES;
        for (s, stage) in stages.iter().enumerate() {
            for coefficient in &mut c {
                stage.apply(4 >> s, coefficient);
            }
        }
        std::array::from_fn(|r| c[r / 8][r % 8])
    }

    /// Byte sources gathering byte `o` of eight weights into qword `o`, in reverse weight order.
    ///
    /// Output register `g`, qword `l`, byte `7 - s` takes byte `8g + l` of weight `s`, input byte `24 s + 8g + l`.
    ///
    /// Returns the two-register sources, the third-register sources, and the mask of bytes from the third.
    const fn gather_index(g: usize) -> ([u8; 64], [u8; 64], u64) {
        let (mut lo, mut hi, mut mask) = ([0u8; 64], [0u8; 64], 0u64);
        let mut p = 0;
        while p < 64 {
            let (l, s) = (p / 8, 7 - p % 8);
            let src = 24 * s + 8 * g + l;
            if src < 128 {
                lo[p] = src as u8;
            } else {
                hi[p] = (src - 128) as u8;
                mask |= 1 << p;
            }
            p += 1;
        }
        (lo, hi, mask)
    }

    /// The gathers of the three output registers.
    const GATHER: [([u8; 64], [u8; 64], u64); 3] = [gather_index(0), gather_index(1), gather_index(2)];

    /// The GFNI matrices of eight weights, one per output byte.
    ///
    /// Matrix `o` maps an input byte `x` to byte `o` of `sum_{s : bit s of x} w_s`.
    ///
    /// The affine instruction computes result bit `k` as the parity of `x` against matrix byte `7 - k`.
    /// So matrix byte `7 - k` has bit `s` set when bit `k` of byte `o` of `w_s` is set.
    ///
    /// ```text
    ///     1. gather     qword o  =  byte o of w_7, ..., w_0        (a byte transpose)
    ///     2. transpose  each qword as an 8x8 bit matrix           (an affine against the reversed identity)
    /// ```
    ///
    /// # Safety
    ///
    /// The CPU must have the enabled target features.
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
    pub fn weight_matrices(w: &[F192; 8]) -> [u64; OUT_BYTES] {
        let src = w.as_ptr().cast::<u8>();
        // SAFETY: eight weights are 192 bytes, exactly three registers.
        let v: [__m512i; 3] = std::array::from_fn(|i| unsafe { _mm512_loadu_si512(src.add(64 * i).cast()) });
        // Byte t of each qword is the unit vector 1 << (7 - t).
        let reversed_identity = _mm512_set1_epi64(0x0102_0408_1020_4080);
        let mut out = [0u64; OUT_BYTES];
        let dst = out.as_mut_ptr().cast::<u8>();
        for (g, (lo, hi, mask)) in GATHER.iter().enumerate() {
            // SAFETY: the index arrays are 64 bytes, and store g fills out[8g..8g+8].
            unsafe {
                let q = _mm512_permutex2var_epi8(v[0], _mm512_loadu_si512(lo.as_ptr().cast()), v[1]);
                let q = _mm512_mask_permutexvar_epi8(q, *mask, _mm512_loadu_si512(hi.as_ptr().cast()), v[2]);
                let a = _mm512_gf2p8affine_epi64_epi8::<0>(reversed_identity, q);
                _mm512_storeu_si512(dst.add(64 * g).cast(), a);
            }
        }
        out
    }

    /// A block of values, one register per byte.
    pub(super) type Sliced = [__m512i; OUT_BYTES];

    /// The GFNI matrices and the input transpose.
    #[derive(Clone, Debug)]
    pub(super) struct Imp {
        /// `matrices[24 r + o]` maps register `r` of the input transpose to output byte `o`.
        matrices: Vec<u64>,
        /// Stages taking row-major bytes to one register per input byte; stage `s` pairs on register bit `s + skew`.
        input: Vec<Stage>,
    }

    impl Imp {
        pub(super) fn new(weights: &[F192]) -> Self {
            let n_chunks = weights.len() / 8;
            let c = n_chunks.trailing_zeros() as usize;

            // Input address of a byte: bits 0..c are its byte j in the row, bits c..c+6 its row p.
            //
            //     in a register        offset = address bits 0..6     register = address bits 6..c+6
            //     after the stages     offset = p                     register = j, rotated when c > 6
            //
            // Stage s swaps offset bit s with register bit s + (c - 6 when c > 6).
            let n_stages = c.min(6);
            let skew = c.saturating_sub(6);
            // Without a rotation, a short row leaves offset = (p high bits, then p low bits).
            let plain = |p: usize| {
                if c >= 6 {
                    p
                } else {
                    (p >> (6 - c)) | ((p & ((1 << (6 - c)) - 1)) << c)
                }
            };
            let input = (0..n_stages)
                .map(|s| {
                    let last = s + 1 == n_stages;
                    Stage::swap(1 << s, |f| if last { plain(f) } else { f })
                })
                .collect();

            // Register `r` then holds input byte `j(r)`: its bits are register bits skew.. then 0..skew.
            let byte_of_reg = |r: usize| (r >> skew) | ((r & ((1 << skew) - 1)) << (c - skew));
            let bytes: &[[F192; 8]] = weights.as_chunks().0;
            // SAFETY: the module is compiled only with these target features enabled.
            let matrices = (0..n_chunks)
                .flat_map(|r| unsafe { weight_matrices(&bytes[byte_of_reg(r)]) })
                .collect();
            Self { matrices, input }
        }

        pub(super) fn new_f192(weights: &[F192]) -> Self {
            let bytes: &[[F192; 8]] = weights.as_chunks().0;
            // SAFETY: the module is compiled only with these target features enabled.
            let matrices = bytes.iter().flat_map(|b| unsafe { weight_matrices(b) }).collect();
            Self {
                matrices,
                input: Vec::new(),
            }
        }

        pub(super) fn slice(xs: &[F192; BLOCK]) -> Sliced {
            // SAFETY: the module is compiled only with these target features enabled.
            unsafe { load_f192(xs) }
        }

        #[inline]
        pub(super) fn apply_add_f192(&self, xs: &[F192; BLOCK], out: &mut [F192]) {
            self.apply_sliced_add(&Self::slice(xs), out);
        }

        #[inline]
        pub(super) fn apply_sliced_add(&self, regs: &Sliced, out: &mut [F192]) {
            let mut image = [F192::ZERO; BLOCK];
            // SAFETY: the module is compiled only with these target features enabled.
            unsafe { self.map_regs(regs, &mut image) };
            for (o, &y) in out.iter_mut().zip(&image) {
                *o += y;
            }
        }

        #[inline]
        #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
        fn map_regs(&self, regs: &Sliced, out: &mut [F192; BLOCK]) {
            let mut acc = [_mm512_setzero_si512(); OUT_BYTES];
            let matrices: &[[u64; OUT_BYTES]] = self.matrices.as_chunks().0;
            for (pair, m) in regs.as_chunks::<2>().0.iter().zip(matrices.as_chunks::<2>().0) {
                for o in 0..OUT_BYTES {
                    let g0 = _mm512_gf2p8affine_epi64_epi8::<0>(pair[0], _mm512_set1_epi64(m[0][o] as i64));
                    let g1 = _mm512_gf2p8affine_epi64_epi8::<0>(pair[1], _mm512_set1_epi64(m[1][o] as i64));
                    acc[o] = _mm512_ternarylogic_epi64::<0x96>(acc[o], g0, g1);
                }
            }
            store_f192(&acc, out);
        }

        #[inline]
        pub(super) fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK]) {
            // A short block folds from a zero-padded copy.
            if rows.len() < BLOCK {
                let mut padded = [[0u8; CHUNKS]; BLOCK];
                padded[..rows.len()].copy_from_slice(rows);
                // SAFETY: the module is compiled only with these target features enabled.
                return unsafe { self.fold_full::<CHUNKS>(&padded, out) };
            }
            let rows: &[[u8; CHUNKS]; BLOCK] = rows.try_into().expect("a full block");
            // SAFETY: the module is compiled only with these target features enabled.
            unsafe { self.fold_full::<CHUNKS>(rows, out) };
        }

        /// Fold a full block into quad planes, see [`QUAD_STAGES`].
        #[inline]
        #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
        pub(super) fn fold_quads<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK]) -> [[__m512i; 8]; 3] {
            let acc = self.fold_bytes::<CHUNKS>(rows);
            let mut planes = [[_mm512_setzero_si512(); 8]; 3];
            for (i, plane) in planes.iter_mut().enumerate() {
                plane.copy_from_slice(&acc[8 * i..8 * i + 8]);
            }
            let stages = &*QUAD_STAGES;
            for (s, stage) in stages.iter().enumerate() {
                for plane in &mut planes {
                    stage.apply(1 << s, plane);
                }
            }
            planes
        }

        #[inline]
        #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
        fn fold_full<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK], out: &mut [F192; BLOCK]) {
            store_f192(&self.fold_bytes::<CHUNKS>(rows), out);
        }

        /// Fold a full block into 24 registers, register `o` holding byte `o` of the 64 values.
        #[inline]
        #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
        fn fold_bytes<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK]) -> [__m512i; OUT_BYTES] {
            // Phase 1: CHUNKS registers of 64 bytes, row-major, then one register per input byte.
            let base = rows.as_ptr().cast::<u8>();
            let mut regs = [_mm512_setzero_si512(); CHUNKS];
            for (i, r) in regs.iter_mut().enumerate() {
                // SAFETY: the block is 64 * CHUNKS bytes, exactly CHUNKS registers.
                *r = unsafe { _mm512_loadu_si512(base.add(64 * i).cast()) };
            }
            // Up to three stages per pass over the registers, eight at a time, so a wide row is not
            // reloaded and stored for every stage when its registers outnumber the register file.
            let n_stages = CHUNKS.trailing_zeros().min(6) as usize;
            for first in (0..n_stages).step_by(3) {
                match n_stages - first {
                    1 => self.input_stages::<2, CHUNKS>(first, &mut regs),
                    2 => self.input_stages::<4, CHUNKS>(first, &mut regs),
                    _ => self.input_stages::<8, CHUNKS>(first, &mut regs),
                }
            }

            // Phase 2: every output byte accumulates one affine product per input register.
            let mut acc = [_mm512_setzero_si512(); OUT_BYTES];
            let matrices: &[[u64; OUT_BYTES]] = self.matrices.as_chunks().0;
            for (pair, m) in regs.as_chunks::<2>().0.iter().zip(matrices.as_chunks::<2>().0) {
                for o in 0..OUT_BYTES {
                    let g0 = _mm512_gf2p8affine_epi64_epi8::<0>(pair[0], _mm512_set1_epi64(m[0][o] as i64));
                    let g1 = _mm512_gf2p8affine_epi64_epi8::<0>(pair[1], _mm512_set1_epi64(m[1][o] as i64));
                    acc[o] = _mm512_ternarylogic_epi64::<0x96>(acc[o], g0, g1);
                }
            }
            acc
        }

        /// Input stages `first..first + log2(G)`, on each group of `G` registers they pair.
        #[inline]
        #[target_feature(enable = "avx512f", enable = "avx512vbmi")]
        fn input_stages<const G: usize, const CHUNKS: usize>(&self, first: usize, regs: &mut [__m512i; CHUNKS]) {
            // Stage `s` pairs on register bit `s + skew`.
            let low = first + (CHUNKS.trailing_zeros() as usize).saturating_sub(6);
            let group_bits = (G - 1) << low;
            for base in (0..CHUNKS).filter(|r| r & group_bits == 0) {
                let mut group = [_mm512_setzero_si512(); G];
                for (k, g) in group.iter_mut().enumerate() {
                    *g = regs[base | (k << low)];
                }
                for j in 0..G.trailing_zeros() as usize {
                    self.input[first + j].apply(1 << j, &mut group);
                }
                for (k, g) in group.iter().enumerate() {
                    regs[base | (k << low)] = *g;
                }
            }
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(
    all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"),
    allow(dead_code)
)]
pub mod avx2 {
    //! The fold of 64 rows at a time, as two halves of 32 rows, one byte per row in a 256-bit register.
    //!
    //! ```text
    //!     1. transpose   64 rows x CHUNKS bytes  ->  two halves x CHUNKS registers, register j = byte j of 32 rows
    //!     2. multiply    out byte o += map[j][o] (register j), for each half
    //!     3. transpose   24 registers of output bytes  ->  32 F192 values, for each half
    //! ```
    //!
    //! Both transposes are butterflies of byte unpacks, which work within 128-bit lanes.
    //!
    //! A round on registers `z` and `z | bit` rotates the lane's byte-offset bits 0..4 with the register bit:
    //!
    //! ```text
    //!     offset bit 0  <-  register bit,    offset bits 1..4  <-  offset bits 0..3,    register bit  <-  offset bit 3
    //! ```
    //!
    //! Loading the registers in bit-reversed order makes every transpose land rows in their natural order.

    use core::arch::x86_64::*;
    use core::fmt::Debug;

    #[cfg(target_feature = "gfni")]
    use crate::bits::bit_transpose_64bytes;

    use super::{BLOCK, F192};

    /// Bytes of an F192.
    pub const OUT_BYTES: usize = 24;

    /// Rows per register.
    pub const HALF: usize = 32;

    /// How a target applies a GF(2)-linear map of bytes to a register of 32 of them.
    pub trait Product {
        /// One map, prepared.
        type Map: Copy + Debug;
        /// One register of input bytes, prepared.
        type Input: Copy;

        /// The maps of eight weights, one per output byte.
        ///
        /// Map `o` takes an input byte `x` to byte `o` of `sum_{s : bit s of x} w_s`.
        fn maps(w: &[F192; 8]) -> [Self::Map; OUT_BYTES];

        fn input(x: __m256i) -> Self::Input;

        fn product(x: Self::Input, m: &Self::Map) -> __m256i;
    }

    /// One affine instruction per map: the 8x8 bit matrix of the AVX-512 arm, broadcast.
    #[cfg(target_feature = "gfni")]
    #[derive(Clone, Copy, Debug)]
    pub struct Gfni;

    #[cfg(target_feature = "gfni")]
    impl Product for Gfni {
        type Map = u64;
        type Input = __m256i;

        /// The affine instruction computes result bit `k` as the parity of `x` against matrix byte `7 - k`.
        /// So matrix byte `7 - k` has bit `s` set when bit `k` of byte `o` of `w_s` is set.
        ///
        /// Per coefficient, the bit transpose of the eight weights' words gives word `o`, byte `k`, bit `s` as exactly
        /// that bit: the matrix is the word with its bytes reversed.
        fn maps(w: &[F192; 8]) -> [u64; OUT_BYTES] {
            let mut out = [0u64; OUT_BYTES];
            for (i, out) in out.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                let words = w.map(|w| [w.c0, w.c1, w.c2][i].to_le_bytes());
                let mut t = [0u8; 64];
                bit_transpose_64bytes(words.as_flattened().try_into().expect("eight words"), &mut t);
                for (m, word) in out.iter_mut().zip(t.as_chunks::<8>().0) {
                    *m = u64::from_be_bytes(*word);
                }
            }
            out
        }

        #[inline(always)]
        fn input(x: __m256i) -> __m256i {
            x
        }

        #[inline(always)]
        fn product(x: __m256i, m: &u64) -> __m256i {
            // SAFETY: the impl exists only when the crate is built with AVX2 and GFNI; registers only.
            unsafe { _mm256_gf2p8affine_epi64_epi8::<0>(x, _mm256_set1_epi64x(*m as i64)) }
        }
    }

    /// Two nibble lookups per map: `vpshufb` reads a 16-entry table per 128-bit lane.
    ///
    /// On a GFNI target only the tests use it.
    #[cfg_attr(target_feature = "gfni", allow(dead_code))]
    #[derive(Clone, Copy, Debug)]
    pub struct Shuffle;

    impl Product for Shuffle {
        /// Byte `o` of the subset sums of the low nibble's four weights, then of the high nibble's.
        type Map = [u8; 32];
        /// The low nibbles, then the high ones.
        type Input = [__m256i; 2];

        fn maps(w: &[F192; 8]) -> [[u8; 32]; OUT_BYTES] {
            // Row `16 h + v`: the sum of the weights of nibble `h` that `v` selects, padded to a register.
            let mut rows = [[0u8; 32]; 32];
            for (rows, w) in rows.as_chunks_mut::<16>().0.iter_mut().zip(w.as_chunks::<4>().0) {
                let mut sum = [F192::ZERO; 16];
                for v in 1..16usize {
                    let low = v.isolate_lowest_one();
                    sum[v] = sum[v ^ low] + w[low.trailing_zeros() as usize];
                }
                for (row, s) in rows.iter_mut().zip(sum) {
                    row[..OUT_BYTES].copy_from_slice([s.c0, s.c1, s.c2].map(u64::to_le_bytes).as_flattened());
                }
            }
            // SAFETY: the impl exists only when the crate is built with AVX2.
            unsafe { leading_columns(&rows) }
        }

        #[inline(always)]
        fn input(x: __m256i) -> [__m256i; 2] {
            // SAFETY: the impl exists only when the crate is built with AVX2; registers only.
            unsafe {
                let nibble = _mm256_set1_epi8(0x0F);
                [
                    _mm256_and_si256(x, nibble),
                    _mm256_and_si256(_mm256_srli_epi16::<4>(x), nibble),
                ]
            }
        }

        #[inline(always)]
        fn product(x: [__m256i; 2], m: &[u8; 32]) -> __m256i {
            // SAFETY: the impl exists only when the crate is built with AVX2, and each load reads 16 of the map's bytes.
            unsafe {
                let lo = _mm256_broadcastsi128_si256(_mm_loadu_si128(m.as_ptr().cast()));
                let hi = _mm256_broadcastsi128_si256(_mm_loadu_si128(m.as_ptr().add(16).cast()));
                _mm256_xor_si256(_mm256_shuffle_epi8(lo, x[0]), _mm256_shuffle_epi8(hi, x[1]))
            }
        }
    }

    /// The product this target prefers.
    #[cfg(target_feature = "gfni")]
    pub type Best = Gfni;
    #[cfg(not(target_feature = "gfni"))]
    pub type Best = Shuffle;

    /// Add the products of one input register by eight consecutive maps into eight accumulators.
    #[inline(always)]
    pub fn accumulate8<P: Product>(acc: &mut [__m256i], x: P::Input, maps: &[P::Map]) {
        for (a, m) in acc[..8].iter_mut().zip(&maps[..8]) {
            // SAFETY: the module is compiled only with AVX2 enabled; registers only.
            *a = unsafe { _mm256_xor_si256(*a, P::product(x, m)) };
        }
    }

    /// `x` with its low `n` bits reversed.
    const fn rev(x: usize, n: u32) -> usize {
        x.reverse_bits() >> (usize::BITS - n)
    }

    /// One unpack round on the registers that differ in `bit`.
    #[inline]
    #[target_feature(enable = "avx2")]
    fn unpack_round(regs: &mut [__m256i], bit: usize) {
        for z in (0..regs.len()).filter(|z| z & bit == 0) {
            let (u, w) = (regs[z], regs[z | bit]);
            regs[z] = _mm256_unpacklo_epi8(u, w);
            regs[z | bit] = _mm256_unpackhi_epi8(u, w);
        }
    }

    /// Four unpack rounds: register `z` and lane offset `f` trade places, both bit-reversed.
    #[inline]
    #[target_feature(enable = "avx2")]
    fn transpose16(regs: &mut [__m256i; 16]) {
        for bit in [1, 2, 4, 8] {
            unpack_round(regs, bit);
        }
    }

    /// A register of two 16-byte lanes, `lo` then `hi`, each the first 16 bytes of its slice.
    #[inline]
    #[target_feature(enable = "avx2")]
    fn pair(lo: &[u8], hi: &[u8]) -> __m256i {
        // SAFETY: each half-load reads the 16 bytes the slicing bounds.
        unsafe { _mm256_loadu2_m128i(hi[..16].as_ptr().cast(), lo[..16].as_ptr().cast()) }
    }

    /// The registers of 64 rows: `out[h][j]` is byte `j` of rows `32h..32h+32`, in order.
    ///
    /// Sixteen registers of 16-byte lanes take one butterfly. A row of at least 16 bytes is whole lanes, rows `p` and
    /// `p + 16` sharing a register, so offset bits 0..4 are byte bits and swap with row bits 0..4. An 8-byte row puts
    /// rows `p` and `p + 32` in one lane, so offset bits 0..3 are byte bits and offset bit 3 is row bit 5, the half.
    #[inline]
    #[target_feature(enable = "avx2")]
    fn transpose_rows<const CHUNKS: usize>(rows: &[[u8; CHUNKS]; BLOCK]) -> [[__m256i; CHUNKS]; 2] {
        let mut out = [[_mm256_setzero_si256(); CHUNKS]; 2];
        if CHUNKS == 8 {
            let bytes = rows.as_flattened();
            let mut regs = [_mm256_setzero_si256(); 16];
            for p in (0..16).step_by(2) {
                // Lane l, qword q: row p + 16 l + 32 q, then the same for row p + 1.
                let x = pair(&bytes[8 * p..], &bytes[8 * (p + 16)..]);
                let y = pair(&bytes[8 * (p + 32)..], &bytes[8 * (p + 48)..]);
                regs[rev(p, 4)] = _mm256_unpacklo_epi64(x, y);
                regs[rev(p + 1, 4)] = _mm256_unpackhi_epi64(x, y);
            }
            transpose16(&mut regs);
            for (z, r) in regs.into_iter().enumerate() {
                out[z & 1][rev(z >> 1, 3)] = r;
            }
        } else {
            for g in 0..CHUNKS / 16 {
                for (h, out) in out.iter_mut().enumerate() {
                    let mut regs: [__m256i; 16] = std::array::from_fn(|z| {
                        let p = 32 * h + rev(z, 4);
                        pair(&rows[p][16 * g..], &rows[p + 16][16 * g..])
                    });
                    transpose16(&mut regs);
                    for (z, r) in regs.into_iter().enumerate() {
                        out[16 * g + rev(z, 4)] = r;
                    }
                }
            }
        }
        out
    }

    /// Byte `j` of 32 rows, in order, for each of the rows' first 24 bytes: the wide rows of [`transpose_rows`].
    #[cfg_attr(target_feature = "gfni", allow(dead_code))]
    #[inline]
    #[target_feature(enable = "avx2")]
    fn leading_columns(rows: &[[u8; 32]; 32]) -> [[u8; 32]; OUT_BYTES] {
        let mut out = [[0u8; 32]; OUT_BYTES];
        for g in 0..2 {
            let mut regs: [__m256i; 16] =
                std::array::from_fn(|z| pair(&rows[rev(z, 4)][16 * g..], &rows[rev(z, 4) + 16][16 * g..]));
            transpose16(&mut regs);
            for (z, r) in regs.into_iter().enumerate() {
                if let Some(out) = out.get_mut(16 * g + rev(z, 4)) {
                    // SAFETY: the store fills one 32-byte column.
                    unsafe { _mm256_storeu_si256(out.as_mut_ptr().cast(), r) };
                }
            }
        }
        out
    }

    /// Store 24 registers of output bytes, register `o` holding byte `o` of 32 values, as those 32 values.
    ///
    /// # Safety
    ///
    /// Requires AVX2, which the target enables wherever this is compiled.
    #[inline]
    #[target_feature(enable = "avx2")]
    pub fn store_f192(acc: &[__m256i; OUT_BYTES], out: &mut [F192; HALF]) {
        // Per coefficient, register z holding byte rev(z): three rounds leave lane l of register z with the
        // coefficient of rows 2 rev(z) + 16 l and the next.
        let [c0, c1, c2]: [[__m256i; 8]; 3] = std::array::from_fn(|i| {
            let mut regs = std::array::from_fn(|z| acc[8 * i + rev(z, 3)]);
            for bit in [1, 2, 4] {
                unpack_round(&mut regs, bit);
            }
            regs
        });
        let dst = out.as_mut_ptr().cast::<u8>();
        for z in 0..8 {
            // Two rows per lane: their six qwords in three 16-byte stores.
            let (lo, hi) = (_mm256_unpacklo_epi64(c0[z], c1[z]), _mm256_unpackhi_epi64(c0[z], c1[z]));
            let parts = [lo, _mm256_unpacklo_epi64(c2[z], hi), _mm256_unpackhi_epi64(hi, c2[z])];
            for (l, row) in [2 * rev(z, 3), 2 * rev(z, 3) + 16].into_iter().enumerate() {
                for (k, part) in parts.iter().enumerate() {
                    let half = if l == 0 {
                        _mm256_castsi256_si128(*part)
                    } else {
                        _mm256_extracti128_si256::<1>(*part)
                    };
                    // SAFETY: rows `row` and `row + 1` are the 48 bytes at `24 row`, inside the 32 values.
                    unsafe { _mm_storeu_si128(dst.add(24 * row + 16 * k).cast(), half) };
                }
            }
        }
    }

    /// The maps of every input byte.
    #[derive(Clone, Debug)]
    pub struct Fold<P: Product> {
        /// `maps[24 j + o]` maps input byte `j` to output byte `o`.
        maps: Vec<P::Map>,
    }

    pub(super) type Imp = Fold<Best>;

    /// A block of values byte-sliced: `[h][j]` is byte `j` of values `32h..32h+32`.
    pub type Sliced = [[__m256i; OUT_BYTES]; 2];

    impl<P: Product> Fold<P> {
        pub fn new(weights: &[F192]) -> Self {
            let bytes: &[[F192; 8]] = weights.as_chunks().0;
            Self {
                maps: bytes.iter().flat_map(P::maps).collect(),
            }
        }

        #[inline]
        pub fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK]) {
            // A short block folds from a zero-padded copy.
            if rows.len() < BLOCK {
                let mut padded = [[0u8; CHUNKS]; BLOCK];
                padded[..rows.len()].copy_from_slice(rows);
                // SAFETY: the module is compiled only with AVX2 enabled.
                return unsafe { self.fold_full::<CHUNKS>(&padded, out) };
            }
            let rows: &[[u8; CHUNKS]; BLOCK] = rows.try_into().expect("a full block");
            // SAFETY: the module is compiled only with AVX2 enabled.
            unsafe { self.fold_full::<CHUNKS>(rows, out) };
        }

        #[inline]
        #[target_feature(enable = "avx2")]
        fn fold_full<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK], out: &mut [F192; BLOCK]) {
            let regs = transpose_rows::<CHUNKS>(rows);
            for (regs, out) in regs.iter().zip(out.as_chunks_mut::<HALF>().0) {
                self.fold_half(regs, out);
            }
        }

        /// The values of 32 rows, from one register per input byte.
        #[inline]
        #[target_feature(enable = "avx2")]
        fn fold_half(&self, regs: &[__m256i], out: &mut [F192; HALF]) {
            let maps: &[[P::Map; OUT_BYTES]] = self.maps.as_chunks().0;
            // Eight output bytes at a time keep their accumulators in registers.
            let mut acc = [_mm256_setzero_si256(); OUT_BYTES];
            for (g, acc) in acc.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                for (&x, m) in regs.iter().zip(maps) {
                    accumulate8::<P>(acc, P::input(x), &m[8 * g..]);
                }
            }
            store_f192(&acc, out);
        }

        /// The maps of an F192's 24 bytes.
        pub fn new_f192(weights: &[F192]) -> Self {
            Self::new(weights)
        }

        /// A block of values, each padded to 32 bytes and transposed like rows.
        pub fn slice(xs: &[F192; BLOCK]) -> Sliced {
            let rows: [[u8; 32]; BLOCK] = std::array::from_fn(|i| {
                let mut row = [0u8; 32];
                row[..OUT_BYTES].copy_from_slice([xs[i].c0, xs[i].c1, xs[i].c2].map(u64::to_le_bytes).as_flattened());
                row
            });
            // SAFETY: the module is compiled only with AVX2 enabled.
            let regs = unsafe { transpose_rows::<32>(&rows) };
            regs.map(|r| std::array::from_fn(|j| r[j]))
        }

        /// Add the image of each of `xs` to `out`.
        #[inline]
        pub fn apply_add_f192(&self, xs: &[F192; BLOCK], out: &mut [F192]) {
            self.apply_sliced_add(&Self::slice(xs), out);
        }

        /// Add the image of each value of a sliced block to `out`.
        #[inline]
        pub fn apply_sliced_add(&self, xs: &Sliced, out: &mut [F192]) {
            for (regs, out) in xs.iter().zip(out.chunks_mut(HALF)) {
                let mut image = [F192::ZERO; HALF];
                // SAFETY: the module is compiled only with AVX2 enabled.
                unsafe { self.fold_half(regs, &mut image) };
                for (o, v) in out.iter_mut().zip(image) {
                    *o += v;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    #[test]
    fn fold_block_matches_definition() {
        fn check<const CHUNKS: usize>(rng: &mut Rng) {
            // Random weights, one per bit of a CHUNKS-byte row.
            let weights: Vec<F192> = (0..8 * CHUNKS).map(|_| rng.ext()).collect();
            let fold = BitFold::new(&weights);

            // Full blocks of random rows, then a short block that exercises the zero padding.
            for len in [BLOCK, BLOCK, 5] {
                let rows: Vec<[u8; CHUNKS]> = (0..len)
                    .map(|_| std::array::from_fn(|_| rng.next_u64() as u8))
                    .collect();
                let mut out = [F192::ZERO; BLOCK];
                fold.fold_block(&rows, &mut out);
                for (p, row) in rows.iter().enumerate() {
                    // Each set bit contributes its own field weight, independently of the backend's layout.
                    let expected = weights
                        .iter()
                        .enumerate()
                        .filter(|(bit, _)| row[bit / 8] >> (bit % 8) & 1 == 1)
                        .fold(F192::ZERO, |acc, (_, &weight)| acc + weight);
                    assert_eq!(out[p], expected, "CHUNKS={CHUNKS}, len={len}, row {p}");
                }
            }
        }
        let mut rng = Rng::new(0xB17_F01D);
        check::<8>(&mut rng);
        check::<16>(&mut rng);
        check::<32>(&mut rng);
        check::<64>(&mut rng);
        check::<128>(&mut rng);
    }

    #[test]
    fn f192_map_matches_definition() {
        let mut rng = Rng::new(0x0F19_23A9);
        let weights: Vec<F192> = (0..192).map(|_| rng.ext()).collect();
        let map = F192Map::new(&weights);
        for len in [BLOCK, 7] {
            let xs: [F192; BLOCK] = std::array::from_fn(|_| rng.ext());
            let before: Vec<F192> = (0..len).map(|_| rng.ext()).collect();
            let mut out = before.clone();
            map.apply_add(&xs, &mut out);
            for p in 0..len {
                let words = [xs[p].c0, xs[p].c1, xs[p].c2];
                let image = (0..192)
                    .filter(|&b| words[b / 64] >> (b % 64) & 1 == 1)
                    .fold(F192::ZERO, |acc, b| acc + weights[b]);
                assert_eq!(out[p], before[p] + image, "len={len}, value {p}");
            }
        }
    }

    #[test]
    fn composed_map_is_the_map_after_the_product() {
        let mut rng = Rng::new(0xC0_4405E);
        let weights: Vec<F192> = (0..192).map(|_| rng.ext()).collect();
        let map = F192Map::new(&weights);
        let c = rng.ext();
        let composed = map.after_mul(c);
        let xs: [F192; BLOCK] = std::array::from_fn(|_| rng.ext());
        let mut expected = [F192::ZERO; BLOCK];
        map.apply_add(&xs.map(|x| x * c), &mut expected);
        let mut got = [F192::ZERO; BLOCK];
        composed.apply_sliced_add(&Sliced::new(&xs), &mut got);
        assert_eq!(got, expected);
    }

    /// Every AVX2 product this target compiles folds and maps as the definition does, not only the dispatched one.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[test]
    fn avx2_products_match_definition() {
        fn check<P: avx2::Product, const CHUNKS: usize>(rng: &mut Rng) {
            let weights: Vec<F192> = (0..8 * CHUNKS).map(|_| rng.ext()).collect();
            let fold = avx2::Fold::<P>::new(&weights);
            for len in [BLOCK, 5] {
                let rows: Vec<[u8; CHUNKS]> = (0..len)
                    .map(|_| std::array::from_fn(|_| rng.next_u64() as u8))
                    .collect();
                let mut out = [F192::ZERO; BLOCK];
                fold.fold_block(&rows, &mut out);
                for (p, row) in rows.iter().enumerate() {
                    let expected = weights
                        .iter()
                        .enumerate()
                        .filter(|(bit, _)| row[bit / 8] >> (bit % 8) & 1 == 1)
                        .fold(F192::ZERO, |acc, (_, &weight)| acc + weight);
                    assert_eq!(out[p], expected, "CHUNKS={CHUNKS}, len={len}, row {p}");
                }
            }
        }
        fn check_map<P: avx2::Product>(rng: &mut Rng) {
            let weights: Vec<F192> = (0..192).map(|_| rng.ext()).collect();
            let map = avx2::Fold::<P>::new_f192(&weights);
            let xs: [F192; BLOCK] = std::array::from_fn(|_| rng.ext());
            let mut out = [F192::ZERO; 7];
            map.apply_add_f192(&xs, &mut out);
            for (p, &o) in out.iter().enumerate() {
                let words = [xs[p].c0, xs[p].c1, xs[p].c2];
                let image = (0..192)
                    .filter(|&b| words[b / 64] >> (b % 64) & 1 == 1)
                    .fold(F192::ZERO, |acc, b| acc + weights[b]);
                assert_eq!(o, image, "value {p}");
            }
        }
        fn check_all<P: avx2::Product>(rng: &mut Rng) {
            check::<P, 8>(rng);
            check::<P, 16>(rng);
            check::<P, 32>(rng);
            check::<P, 64>(rng);
            check::<P, 128>(rng);
            check_map::<P>(rng);
        }
        let mut rng = Rng::new(0xA7_2B17);
        check_all::<avx2::Shuffle>(&mut rng);
        #[cfg(target_feature = "gfni")]
        check_all::<avx2::Gfni>(&mut rng);
    }
}
