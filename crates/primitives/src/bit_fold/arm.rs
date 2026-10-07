//! AArch64 byte tables with a power-of-two entry stride.
//!
//! Each entry holds the three field limbs and one initialized zero limb. This
//! trades a third more table storage for shift-only lookup addressing. Two
//! lookups at a time feed each EOR3 accumulator, using two NEON registers per row.
//! Two independent rows share a table walk to expose load and XOR parallelism.

use super::{BLOCK, F192};
use core::arch::aarch64::{vdupq_n_u64, veor3q_u64, veorq_u64, vgetq_lane_u64, vld1q_u64};

type Entry = [u64; 4];

#[inline(always)]
fn fold_rows<const CHUNKS: usize, const ROWS: usize>(
    tables: &[[Entry; 256]],
    rows: &[[u8; CHUNKS]; ROWS],
) -> [F192; ROWS] {
    let tables: &[[Entry; 256]; CHUNKS] = tables.try_into().expect("one table per byte");
    // SAFETY: This module requires aarch64 SHA3. Each entry contains four
    // initialized u64s, so both 16-byte loads remain inside the selected entry.
    unsafe {
        let mut lo = [vdupq_n_u64(0); ROWS];
        let mut hi = [vdupq_n_u64(0); ROWS];
        for j in 0..CHUNKS / 2 {
            for r in 0..ROWS {
                let a = tables[2 * j][usize::from(rows[r][2 * j])].as_ptr();
                let b = tables[2 * j + 1][usize::from(rows[r][2 * j + 1])].as_ptr();
                lo[r] = veor3q_u64(lo[r], vld1q_u64(a), vld1q_u64(b));
                hi[r] = veor3q_u64(hi[r], vld1q_u64(a.add(2)), vld1q_u64(b.add(2)));
            }
        }
        if CHUNKS % 2 != 0 {
            for r in 0..ROWS {
                let a = tables[CHUNKS - 1][usize::from(rows[r][CHUNKS - 1])].as_ptr();
                lo[r] = veorq_u64(lo[r], vld1q_u64(a));
                hi[r] = veorq_u64(hi[r], vld1q_u64(a.add(2)));
            }
        }
        std::array::from_fn(|r| F192 {
            c0: vgetq_lane_u64::<0>(lo[r]),
            c1: vgetq_lane_u64::<1>(lo[r]),
            c2: vgetq_lane_u64::<0>(hi[r]),
        })
    }
}

#[inline(always)]
fn row_bytes(x: F192) -> [u8; 24] {
    let mut row = [0u8; 24];
    row[..8].copy_from_slice(&x.c0.to_le_bytes());
    row[8..16].copy_from_slice(&x.c1.to_le_bytes());
    row[16..].copy_from_slice(&x.c2.to_le_bytes());
    row
}

#[derive(Clone, Debug)]
pub(super) struct Imp {
    tables: Vec<[Entry; 256]>,
}

impl Imp {
    pub(super) fn new(weights: &[F192]) -> Self {
        let tables = weights
            .as_chunks::<8>()
            .0
            .iter()
            .map(|weights| {
                let mut sums = [[0; 4]; 256];
                for v in 1..256usize {
                    let low = v.isolate_lowest_one();
                    let w = weights[low.trailing_zeros() as usize];
                    let prev = sums[v ^ low];
                    sums[v] = [prev[0] ^ w.c0, prev[1] ^ w.c1, prev[2] ^ w.c2, 0];
                }
                sums
            })
            .collect();
        Self { tables }
    }

    pub(super) fn new_f192(weights: &[F192]) -> Self {
        Self::new(weights)
    }

    #[inline]
    pub(super) fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK]) {
        let (pairs, tail) = rows.as_chunks::<2>();
        for (o, pair) in out.as_chunks_mut::<2>().0.iter_mut().zip(pairs) {
            *o = fold_rows(&self.tables, pair);
        }
        if let Some(row) = tail.first() {
            out[2 * pairs.len()] = fold_rows(&self.tables, std::array::from_ref(row))[0];
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
        let (pairs, tail) = out.as_chunks_mut::<2>();
        for (o, pair) in pairs.iter_mut().zip(xs.as_chunks::<2>().0) {
            let values = fold_rows(&self.tables, &pair.map(row_bytes));
            o[0] += values[0];
            o[1] += values[1];
        }
        if let Some(o) = tail.first_mut() {
            *o += fold_rows(&self.tables, &[row_bytes(xs[2 * pairs.len()])])[0];
        }
    }
}

pub(super) type Sliced = [F192; BLOCK];
