//! AArch64 byte tables with a power-of-two entry stride.
//!
//! Each entry holds the three field limbs and one initialized zero limb. This
//! trades a third more table storage for shift-only lookup addressing.

use super::{BLOCK, F192};

type Entry = [u64; 4];

#[inline(always)]
fn fold_row<const CHUNKS: usize>(tables: &[[Entry; 256]], row: &[u8; CHUNKS]) -> F192 {
    let tables: &[[Entry; 256]; CHUNKS] = tables.try_into().expect("one table per byte");
    let mut acc = F192::ZERO;
    for (&byte, table) in row.iter().zip(tables) {
        let v = table[usize::from(byte)];
        acc.c0 ^= v[0];
        acc.c1 ^= v[1];
        acc.c2 ^= v[2];
    }
    acc
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
        for (o, row) in out.iter_mut().zip(rows) {
            *o = fold_row(&self.tables, row);
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
            *o += fold_row(&self.tables, &row);
        }
    }
}

pub(super) type Sliced = [F192; BLOCK];
