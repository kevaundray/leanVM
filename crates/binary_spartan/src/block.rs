//! The block R1CS `(A_0, B_0, C_0)` as padded sparse GF(2) matrices, and the column layout of one instance.
//!
//! Rows and columns are padded to `2^k_log` (`k_log >= MIN_K_LOG`). The first `64 * public_words()` columns are the
//! public region: column 0 is the constant one, columns `1..=n_public` the public bits, the rest zero. Private
//! signals are renumbered to start right after it, so the public region is whole packed words of every instance.
//!
//! A linked block (`CLB2`) also places link `j`'s `out` signal at column `out_base + j`, inside the aligned
//! `2^out_log` block at `out_base` and alone in its packed words, and appends one linear row per link after the
//! constraints: `A_0 = {in_j}`, `B_0 = {constant}`, `C_0 = {}`. The batch adds `z_{i-1}[out_j]` to that row of
//! instance `i` (the shift `S_N ⊗ A_link`), and the statement's `in` boundary to instance 0's.

use crate::format::{FormatError, MAX_LOG, R1csFile, check_links};
use flock::lincheck::LincheckCircuit;
use primitives::field::F192;

/// Smallest block: `2^7` rows and columns.
pub const MIN_K_LOG: usize = 7;

/// A GF(2) matrix in compressed sparse row form: every listed entry is 1, and each row's columns are strictly
/// increasing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Csr {
    pub row_ptr: Vec<u32>,
    pub cols: Vec<u32>,
}

impl Csr {
    pub fn n_rows(&self) -> usize {
        self.row_ptr.len() - 1
    }

    pub fn nnz(&self) -> usize {
        self.cols.len()
    }

    /// The columns of row `r`.
    #[inline]
    pub fn row(&self, r: usize) -> &[u32] {
        &self.cols[self.row_ptr[r] as usize..self.row_ptr[r + 1] as usize]
    }
}

/// The padded block matrices, `2^k_log` rows and columns each.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockMatrices {
    pub k_log: usize,
    pub a: Csr,
    pub b: Csr,
    pub c: Csr,
}

/// Where a linked block's links sit in padded coordinates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Links {
    pub count: usize,
    /// Link `j`'s row is `first_row + j`.
    pub first_row: usize,
    /// Link `j`'s `out` column is `out_base + j`; `out_base` is a multiple of `2^out_log`, and `count <= 2^out_log`.
    pub out_base: usize,
    pub out_log: usize,
}

impl Links {
    /// Packed words per instance holding the `out` columns, which hold nothing else.
    pub fn words(&self) -> usize {
        self.count.div_ceil(64)
    }
}

/// Why a block R1CS was rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockError {
    /// The file's own invariants do not hold.
    Format(FormatError),
    /// The padded block would exceed `2^MAX_LOG`, or the nonzeros overflow a `u32`.
    TooLarge,
}

impl std::fmt::Display for BlockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl std::error::Error for BlockError {}

/// A run of consecutive signals laid out at consecutive columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Run {
    signal: u32,
    column: u32,
    len: u32,
}

/// A validated block R1CS: its padded matrices, its signal counts and the digest of its canonical file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockR1cs {
    pub matrices: BlockMatrices,
    pub n_signals: usize,
    pub n_public: usize,
    /// The file's constraints; a linked block's link rows follow them.
    pub n_constraints: usize,
    pub links: Option<Links>,
    /// Link `j`'s `in` and `out` signals.
    pub link_signals: Vec<(u32, u32)>,
    /// BLAKE2s of the canonical `CLB1` or `CLB2` encoding.
    pub digest: [u8; 32],
    used_columns: usize,
    runs: Vec<Run>,
}

impl BlockR1cs {
    pub fn new(file: &R1csFile) -> Result<Self, BlockError> {
        let (n_signals, n_public) = (file.n_signals, file.n_public);
        if n_signals == 0 || n_public >= n_signals || n_signals > 1 << MAX_LOG || file.links.len() > 1 << MAX_LOG {
            return Err(BlockError::Format(FormatError::BadHeader));
        }
        for (index, constraint) in file.constraints.iter().enumerate() {
            for side in [&constraint.a, &constraint.b, &constraint.c] {
                if let Some(&signal) = side.iter().find(|&&s| s as usize >= n_signals) {
                    return Err(BlockError::Format(FormatError::SignalOutOfRange {
                        constraint: index,
                        signal,
                    }));
                }
                if side.windows(2).any(|w| w[0] >= w[1]) {
                    return Err(BlockError::Format(FormatError::NotIncreasing { constraint: index }));
                }
            }
        }
        check_links(n_signals, n_public, &file.links).map_err(BlockError::Format)?;

        let public_words = (n_public + 1).div_ceil(64);
        let n_constraints = file.constraints.len();
        let (column, used_columns, links) = Self::columns(file, public_words);
        let n_rows = n_constraints + file.links.len();
        let k_log = (used_columns.max(n_rows).next_power_of_two().trailing_zeros() as usize).max(MIN_K_LOG);
        if k_log > MAX_LOG {
            return Err(BlockError::TooLarge);
        }
        let k = 1usize << k_log;

        let constant = [0u32];
        let link_rows = |side: usize, j: usize| -> &[u32] {
            match side {
                0 => std::slice::from_ref(&column[file.links[j].0 as usize]),
                1 => &constant,
                _ => &[],
            }
        };
        let build = |side: usize| -> Result<Csr, BlockError> {
            let pick = |c: &crate::format::Constraint| -> Vec<u32> {
                [&c.a, &c.b, &c.c][side].iter().map(|&s| column[s as usize]).collect()
            };
            let nnz: usize = file
                .constraints
                .iter()
                .map(|c| [&c.a, &c.b, &c.c][side].len())
                .sum::<usize>()
                + (0..file.links.len()).map(|j| link_rows(side, j).len()).sum::<usize>();
            if nnz > u32::MAX as usize {
                return Err(BlockError::TooLarge);
            }
            let mut row_ptr = Vec::with_capacity(k + 1);
            let mut cols = Vec::with_capacity(nnz);
            row_ptr.push(0);
            for constraint in &file.constraints {
                let mut row = pick(constraint);
                // A link `out` column can sit below a column it followed in signal order.
                row.sort_unstable();
                cols.extend(row);
                row_ptr.push(cols.len() as u32);
            }
            for j in 0..file.links.len() {
                cols.extend_from_slice(link_rows(side, j));
                row_ptr.push(cols.len() as u32);
            }
            row_ptr.resize(k + 1, cols.len() as u32);
            Ok(Csr { row_ptr, cols })
        };
        let matrices = BlockMatrices {
            k_log,
            a: build(0)?,
            b: build(1)?,
            c: build(2)?,
        };

        let mut runs: Vec<Run> = Vec::new();
        for (signal, &col) in column.iter().enumerate() {
            match runs.last_mut() {
                Some(run) if run.signal + run.len == signal as u32 && run.column + run.len == col => run.len += 1,
                _ => runs.push(Run {
                    signal: signal as u32,
                    column: col,
                    len: 1,
                }),
            }
        }
        Ok(Self {
            matrices,
            n_signals,
            n_public,
            n_constraints,
            links: links.map(|(out_base, out_log)| Links {
                count: file.links.len(),
                first_row: n_constraints,
                out_base,
                out_log,
            }),
            link_signals: file.links.clone(),
            digest: primitives::hash::hash(&file.encode()),
            used_columns,
            runs,
        })
    }

    /// Each signal's column, the columns that can be nonzero, and a linked block's `(out_base, out_log)`.
    ///
    /// The public region comes first. Without links the private signals follow it in order. With links, the `out`
    /// signals take the first `2^out_log`-aligned block past the public region, in link order, and the other private
    /// signals fill the columns before it and continue after the `out` words.
    #[allow(clippy::type_complexity)]
    fn columns(file: &R1csFile, public_words: usize) -> (Vec<u32>, usize, Option<(usize, usize)>) {
        let head = file.n_public + 1;
        let mut column: Vec<u32> = (0..file.n_signals as u32).collect();
        let mut next = 64 * public_words;
        if file.links.is_empty() {
            for c in &mut column[head..] {
                *c = next as u32;
                next += 1;
            }
            return (column, next, None);
        }
        let n_link = file.links.len();
        let out_log = (n_link.next_power_of_two().trailing_zeros() as usize).max(6);
        let out_base = next.next_multiple_of(1 << out_log);
        let out_end = out_base + 64 * n_link.div_ceil(64);
        let mut is_out = vec![false; file.n_signals];
        for (j, &(_, out)) in file.links.iter().enumerate() {
            is_out[out as usize] = true;
            column[out as usize] = (out_base + j) as u32;
        }
        let mut used = out_base + n_link;
        for (signal, c) in column.iter_mut().enumerate().skip(head) {
            if !is_out[signal] {
                if next == out_base {
                    next = out_end;
                }
                *c = next as u32;
                next += 1;
                used = used.max(next);
            }
        }
        (column, used, Some((out_base, out_log)))
    }

    pub fn k_log(&self) -> usize {
        self.matrices.k_log
    }

    /// Packed 64-bit words per instance in the public region.
    pub fn public_words(&self) -> usize {
        (self.n_public + 1).div_ceil(64)
    }

    /// Columns that can be nonzero.
    pub fn used_columns(&self) -> usize {
        self.used_columns
    }

    /// Rows that can be nonzero: the constraints, then the link rows.
    pub fn used_rows(&self) -> usize {
        self.n_constraints + self.link_signals.len()
    }

    /// Lay one instance's signal bytes (`ceil(n_signals / 8)` bytes, signal `j` at bit `j`) out as its block of
    /// `2^k_log / 64` packed words. `out` must be zero.
    pub fn layout_instance(&self, signals: &[u8], out: &mut [u64]) {
        debug_assert_eq!(signals.len(), self.n_signals.div_ceil(8));
        debug_assert_eq!(out.len(), (1usize << self.k_log()) / 64);
        for run in &self.runs {
            copy_bits(signals, run.signal as usize, run.len as usize, out, run.column as usize);
        }
    }

    /// The public region of one instance: the constant, the public bits and zero padding, `public_words()` words.
    pub fn layout_public(&self, signals: &[u8], out: &mut [u64]) {
        debug_assert_eq!(out.len(), self.public_words());
        copy_bits(signals, 0, self.n_public + 1, out, 0);
    }

    /// One instance's link `in` (`output = false`) or `out` signals, link `j` at bit `j` of `ceil(n_link / 64)`
    /// words.
    pub fn link_values(&self, signals: &[u8], output: bool) -> Vec<u64> {
        let mut words = vec![0u64; self.link_signals.len().div_ceil(64)];
        for (j, &(input, out)) in self.link_signals.iter().enumerate() {
            let s = if output { out } else { input } as usize;
            words[j / 64] |= u64::from(signals[s / 8] >> (s % 8) & 1) << (j % 64);
        }
        words
    }

    /// The first violated constraint of one laid-out instance, if any. Link rows are not checked: they span two
    /// instances.
    pub fn first_violation(&self, z: &[u64]) -> Option<usize> {
        let m = &self.matrices;
        let parity = |row: &[u32]| row.iter().fold(0u64, |acc, &c| acc ^ (z[c as usize >> 6] >> (c & 63)));
        (0..self.n_constraints).find(|&r| (parity(m.a.row(r)) & parity(m.b.row(r)) ^ parity(m.c.row(r))) & 1 != 0)
    }
}

/// `len` bits of `src` from bit `src_bit` onwards, OR-ed into `dst` from bit `dst_bit` onwards.
fn copy_bits(src: &[u8], src_bit: usize, len: usize, dst: &mut [u64], dst_bit: usize) {
    let mut done = 0;
    while done < len {
        let (word, offset) = ((dst_bit + done) / 64, (dst_bit + done) % 64);
        let take = (len - done).min(64 - offset);
        let bit = src_bit + done;
        let first = bit / 8;
        let mut window = [0u8; 16];
        let end = (first + 9).min(src.len());
        window[..end - first].copy_from_slice(&src[first..end]);
        let bits = (u128::from_le_bytes(window) >> (bit % 8)) as u64;
        dst[word] |= if take == 64 { bits } else { bits & ((1u64 << take) - 1) } << offset;
        done += take;
    }
}

impl LincheckCircuit for BlockMatrices {
    fn n_cols(&self) -> usize {
        1 << self.k_log
    }

    fn c_is_identity(&self) -> bool {
        false
    }

    fn const_pin_col(&self) -> usize {
        0
    }

    /// `eqᵀA_0 + α·eqᵀB_0 + α²·eqᵀC_0`, one sparse pass over the rows.
    fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192> {
        let alpha_sq = alpha.square();
        let mut out = vec![F192::ZERO; self.n_cols()];
        for (r, &e) in eq_inner.iter().enumerate() {
            for (m, weight) in [(&self.a, F192::ONE), (&self.b, alpha), (&self.c, alpha_sq)] {
                let row = m.row(r);
                if !row.is_empty() {
                    let v = weight * e;
                    for &c in row {
                        out[c as usize] += v;
                    }
                }
            }
        }
        out
    }
}
