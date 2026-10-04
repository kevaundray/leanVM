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
//! - GFNI: an 8x8 bit matrix per (input byte, output byte), applied to 64 rows by one instruction.

use crate::field::F192;

use crate::multilinear::eq_table;

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
)))]
use portable::{self as imp, Imp};

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use gfni::{self as imp, Imp};

/// Rows folded per call.
pub const BLOCK: usize = 64;

/// Whether the fold runs on GFNI rather than the byte tables.
pub const GFNI: bool = cfg!(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
));

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
    pub fn new(xs: &[F192; BLOCK]) -> Self {
        Self(Imp::slice(xs))
    }
}

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
)))]
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

        pub(super) fn slice(xs: &[F192; BLOCK]) -> Sliced {
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
    #[derive(Clone, Copy, Debug)]
    struct Stage {
        /// The register-index bit the stage pairs on.
        zbit: usize,
        /// Byte sources of the low register of each pair; bit 6 picks the high one.
        lo: [u8; 64],
        /// Byte sources of the high register of each pair.
        hi: [u8; 64],
    }

    impl Stage {
        /// Swap byte-offset bit `fbit` with register bit `zbit`, then permute each output by `sigma`.
        ///
        /// Output offset `f` takes the byte the plain swap leaves at offset `sigma(f)`.
        fn swap(fbit: usize, zbit: usize, sigma: impl Fn(usize) -> usize) -> Self {
            // The plain swap: a byte keeps its offset except bit `fbit`, which trades places with the register bit.
            let lo = |f: usize| if f & fbit == 0 { f } else { 64 | (f ^ fbit) };
            let hi = |f: usize| if f & fbit == 0 { f | fbit } else { 64 | f };
            Self {
                zbit,
                lo: std::array::from_fn(|f| lo(sigma(f)) as u8),
                hi: std::array::from_fn(|f| hi(sigma(f)) as u8),
            }
        }

        #[inline]
        #[target_feature(enable = "avx512f", enable = "avx512vbmi")]
        fn apply(&self, regs: &mut [__m512i]) {
            // SAFETY: both index arrays are 64 bytes.
            let (lo, hi) = unsafe {
                (
                    _mm512_loadu_si512(self.lo.as_ptr().cast()),
                    _mm512_loadu_si512(self.hi.as_ptr().cast()),
                )
            };
            for z in (0..regs.len()).filter(|z| z & self.zbit == 0) {
                let (u, w) = (regs[z], regs[z | self.zbit]);
                regs[z] = _mm512_permutex2var_epi8(u, lo, w);
                regs[z | self.zbit] = _mm512_permutex2var_epi8(u, hi, w);
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
            Self {
                zbit: self.zbit,
                lo,
                hi,
            }
        }
    }

    /// Stages taking eight registers of one output coefficient, register = byte `o` and offset = value `p`, to qwords.
    ///
    /// ```text
    ///     after the stages     offset = (o, then p bits 0..3)     register = p bits 3..6
    /// ```
    ///
    /// So register `k`, qword `l` is the coefficient of value `8k + l`.
    static OUTPUT_STAGES: LazyLock<[Stage; 3]> = LazyLock::new(|| {
        let to_qwords = |f: usize| (f >> 3) | ((f & 7) << 3);
        [0, 1, 2].map(|s| Stage::swap(8 << s, 1 << s, |f| if s == 2 { to_qwords(f) } else { f }))
    });

    /// [`OUTPUT_STAGES`] undone: eight registers of one coefficient's qwords back to one register per byte.
    static INPUT_STAGES: LazyLock<[Stage; 3]> = LazyLock::new(|| {
        let [a, b, c] = &*OUTPUT_STAGES;
        [c.inverse(), b.inverse(), a.inverse()]
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
        let [mut c0, mut c1, mut c2]: [[__m512i; 8]; 3] =
            std::array::from_fn(|i| std::array::from_fn(|o| acc[8 * i + o]));
        for stage in OUTPUT_STAGES.iter() {
            stage.apply(&mut c0);
            stage.apply(&mut c1);
            stage.apply(&mut c2);
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
        for stage in INPUT_STAGES.iter() {
            for coefficient in &mut c {
                stage.apply(coefficient);
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
        /// Stages taking row-major bytes to one register per input byte.
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
                    Stage::swap(1 << s, 1 << (s + skew), |f| if last { plain(f) } else { f })
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

        #[inline]
        #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
        fn fold_full<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK], out: &mut [F192; BLOCK]) {
            // Phase 1: CHUNKS registers of 64 bytes, row-major, then one register per input byte.
            let base = rows.as_ptr().cast::<u8>();
            // SAFETY: the block is 64 * CHUNKS bytes, exactly CHUNKS registers.
            let mut regs: [__m512i; CHUNKS] =
                std::array::from_fn(|i| unsafe { _mm512_loadu_si512(base.add(64 * i).cast()) });
            for stage in &self.input {
                stage.apply(&mut regs);
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

            // Phase 3: back to one F192 per row.
            store_f192(&acc, out);
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
}
