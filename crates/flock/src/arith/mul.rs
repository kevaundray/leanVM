//! Multiplication.
//!
//! ## Partial products are free
//!
//! A schoolbook multiplier pays one product per partial product `a_i·b_j`, then
//! one per carry to sum them. Over GF(2) the first half is avoidable: with
//! `e_ij = ¬(a_i ⊕ b_j)`, `2·a_i·b_j = a_i + b_j − 1 + e_ij`. Summed, with
//! `M = 2^64 − 1` and `¬a = M − a` the 64-bit complement,
//!
//! ```text
//!   2ab = Σ_i (a_i ? b : ¬b)·2^i + ¬a + ¬b + (a + b)·2^64 + 1 − 2^128
//! ```
//!
//! Every row there is affine in the inputs. Its column 0,
//! `¬(a_0 ⊕ b_0) + ¬a_0 + ¬b_0 + 1`, is `2 + 2g` with `g = ¬a_0·¬b_0`, so after
//! that one product the identity halves: `a·b mod 2^N` is `1 + g` plus the other
//! columns shifted down a place. That is 66 rows of affine bits, with `1` and
//! `g` in the empty low bits of two of them.
//!
//! ## Compression
//!
//! A carry-save step turns three rows into their XOR and their majority shifted
//! up a place. The majority `(x ⊕ z)(y ⊕ z) ⊕ z` is one product at each position
//! where at least two rows have a bit, except where exactly two do and the carry
//! row is still free there: one of the two bits moves into it instead. Taking
//! the three rows that end lowest each time, the 64 steps cost as few products
//! as summing column by column, and a ripple-carry addition finishes the last
//! two rows. The top position's majority would carry out of the modulus, so it
//! is never a product.
//!
//! Every step is word arithmetic on `u128` rows and its products are one run of
//! slots, so an instance's witness is a few shifts and masks per step.

use super::Instance;
use crate::circuit::{Builder, Wire};

/// The rows `(a_i ? b : ¬b)` for `i < 64`, then the `a` and `b` rows.
const N_ROWS: usize = 66;
const A_ROW: usize = 64;
const B_ROW: usize = 65;

/// One carry-save step: rows `x`, `y`, `z` become the sum row, stored in `x`,
/// and the carry row, stored in `y`.
#[derive(Clone, Copy)]
struct Csa {
    x: usize,
    y: usize,
    z: usize,
    /// Positions whose majority is a product, one run of slots from `slot`.
    products: u128,
    /// Positions where the pair's `y` (or `z`) bit moves to the carry row.
    move_y: u128,
    move_z: u128,
    slot: usize,
}

/// A row's `(highest, lowest)` position.
fn ends(row: u128) -> (u32, u32) {
    (127 - row.leading_zeros(), row.trailing_zeros())
}

/// Removes from `live` the row that ends lowest, by `(highest, lowest)` position,
/// the earliest of equals, and returns it.
fn take_lowest(live: &mut Vec<usize>, present: &[u128]) -> usize {
    let mut best = 0;
    for t in 1..live.len() {
        let ((h, l), (best_h, best_l)) = (ends(present[live[t]]), ends(present[live[best]]));
        if h < best_h || (h == best_h && l < best_l) {
            best = t;
        }
    }
    live.remove(best)
}

fn is_run(mask: u128) -> bool {
    let run = mask.checked_shr(mask.trailing_zeros()).unwrap_or(0);
    run & run.wrapping_add(1) == 0
}

pub struct Multiplier {
    g_slot: usize,
    steps: Vec<Csa>,
    /// The two rows the steps leave, and where adding them makes a product.
    last: (usize, usize),
    carries: u128,
    carry_slot: usize,
    /// Positions below `N`.
    width: u128,
}

/// `¬x` for each of the 64 bits of `x`.
fn complement(c: &mut Builder, x: &[Wire]) -> Vec<Wire> {
    let one = c.one();
    let mut out = Vec::with_capacity(64);
    for i in 0..64 {
        out.push(c.xor(x[i], one));
    }
    out
}

/// Each row's wire per position, all shifted down a place: row 0's bit 0 is what `g`
/// and the constant 1 replace.
fn initial_rows(
    c: &mut Builder,
    a: &[Wire],
    b: &[Wire],
    not_a: &[Wire],
    not_b: &[Wire],
    g: Wire,
    n: usize,
) -> Vec<Vec<Wire>> {
    let mut rows = Vec::with_capacity(N_ROWS);
    for i in 0..64 {
        let mut row = vec![None; n];
        for j in 0..64 {
            if i + j >= 1 && i + j - 1 < n {
                row[i + j - 1] = c.xor(b[j], not_a[i]);
            }
        }
        rows.push(row);
    }
    rows.push(operand_row(a, not_a, n));
    rows.push(operand_row(b, not_b, n));
    let one = c.one();
    rows[2][0] = one;
    rows[3][0] = g;
    // Half of the constant `2^128`, which survives only mod `2^128`.
    if n == 128 {
        rows[A_ROW][127] = one;
    }
    rows
}

/// `(¬x ≫ 1) + x·2^63` over `n` positions.
fn operand_row(x: &[Wire], not_x: &[Wire], n: usize) -> Vec<Wire> {
    let mut row = Vec::with_capacity(n);
    for p in 0..n {
        row.push(if p < 63 {
            not_x[p + 1]
        } else if p < 127 {
            x[p - 63]
        } else {
            None
        });
    }
    row
}

/// The positions where `row` has a wire.
fn presence(row: &[Wire]) -> u128 {
    let mut mask = 0;
    for p in 0..row.len() {
        if row[p].is_some() {
            mask |= 1 << p;
        }
    }
    mask
}

/// One carry-save step on the three live rows that end lowest: the sum row replaces
/// the first, the carry row the second, and the third leaves `live`.
fn carry_save(
    c: &mut Builder,
    rows: &mut [Vec<Wire>],
    present: &mut [u128],
    live: &mut Vec<usize>,
    width: u128,
) -> Csa {
    let n = rows[0].len();
    let x = take_lowest(live, present);
    let y = take_lowest(live, present);
    let z = take_lowest(live, present);
    live.push(x);
    live.push(y);

    let (px, py, pz) = (present[x], present[y], present[z]);
    let pairs = ((px & py) | (px & pz) | (py & pz)) & (width >> 1);
    let triples = px & py & pz;
    let (mut products, mut moves) = (0u128, 0u128);
    for p in 0..n - 1 {
        // The carry row is free at `p` unless `p − 1` has a product.
        if (pairs >> p) & 1 == 1 {
            if (triples >> p) & 1 == 0 && (products << 1) >> p & 1 == 0 {
                moves |= 1 << p;
            } else {
                products |= 1 << p;
            }
        }
    }
    assert!(is_run(products), "a step's products must be one run of slots");
    let step = Csa {
        x,
        y,
        z,
        products,
        move_y: moves & !pz,
        move_z: moves & pz,
        slot: c.next_slot(),
    };

    let (mut sum, mut carry) = (vec![None; n], vec![None; n]);
    for p in 0..n {
        let (wx, wy, wz) = (rows[x][p], rows[y][p], rows[z][p]);
        if (products >> p) & 1 == 1 {
            let xz = c.xor(wx, wz);
            let yz = c.xor(wy, wz);
            let maj = c.and(xz, yz);
            carry[p + 1] = c.xor(maj, wz);
            sum[p] = c.xor(xz, wy);
        } else if (step.move_z >> p) & 1 == 1 {
            carry[p] = wz;
            sum[p] = c.xor(wx, wy);
        } else if (step.move_y >> p) & 1 == 1 {
            carry[p] = wy;
            sum[p] = wx;
        } else {
            let xz = c.xor(wx, wz);
            sum[p] = c.xor(xz, wy);
        }
    }
    rows[x] = sum;
    rows[y] = carry;
    present[x] = px | py | pz;
    present[y] = (products << 1) | moves;
    step
}

/// `x + y` by ripple carry over the rows' `n` positions, and the positions where it
/// makes a product.
fn ripple(c: &mut Builder, x: &[Wire], y: &[Wire]) -> (Vec<Wire>, u128) {
    let n = x.len();
    let mut carries = 0u128;
    let mut carry = None;
    let mut sum = Vec::with_capacity(n);
    for p in 0..n {
        let (wx, wy) = (x[p], y[p]);
        let bits = wx.is_some() as usize + wy.is_some() as usize + carry.is_some() as usize;
        let out = if p + 1 < n && bits >= 2 {
            carries |= 1 << p;
            let xc = c.xor(wx, carry);
            let yc = c.xor(wy, carry);
            let maj = c.and(xc, yc);
            carry = c.xor(maj, carry);
            c.xor(xc, wy)
        } else {
            let xy = c.xor(wx, wy);
            let out = c.xor(xy, carry);
            carry = None;
            out
        };
        sum.push(out);
    }
    (sum, carries)
}

impl Multiplier {
    /// The low `n` bits of `a·b`, as wires.
    pub fn build(c: &mut Builder, a: &[Wire], b: &[Wire], n: usize) -> (Vec<Wire>, Self) {
        let width = u128::MAX >> (128 - n);
        let not_a = complement(c, a);
        let not_b = complement(c, b);
        let g_slot = c.next_slot();
        let g = c.and(not_a[0], not_b[0]);
        let mut rows = initial_rows(c, a, b, &not_a, &not_b, g, n);
        let mut present = Vec::with_capacity(N_ROWS);
        let mut live = Vec::with_capacity(N_ROWS);
        for row in 0..N_ROWS {
            present.push(presence(&rows[row]));
            live.push(row);
        }
        let mut steps = Vec::new();
        while live.len() > 2 {
            steps.push(carry_save(c, &mut rows, &mut present, &mut live, width));
        }

        // The steps stop at two rows.
        let (x, y) = (live[0], live[1]);
        let carry_slot = c.next_slot();
        let (product, carries) = ripple(c, &rows[x], &rows[y]);
        assert!(is_run(carries), "the final carries must be one run of slots");
        let multiplier = Self {
            g_slot,
            steps,
            last: (x, y),
            carries,
            carry_slot,
            width,
        };
        (product, multiplier)
    }

    /// Writes `g`'s row and every step's products, and returns the result.
    pub(super) fn witness(&self, a: u64, b: u64, witness: &mut Instance) -> u128 {
        let (na, nb) = (!a, !b);
        let mut rows = [0u128; N_ROWS];
        for (i, row) in rows[..64].iter_mut().enumerate() {
            let v = (b ^ ((a >> i) & 1).wrapping_sub(1)) as u128;
            *row = if i == 0 { v >> 1 } else { v << (i - 1) };
        }
        rows[A_ROW] = ((na >> 1) as u128) | ((a as u128) << 63) | (1 << 127);
        rows[B_ROW] = ((nb >> 1) as u128) | ((b as u128) << 63);
        rows[2] |= 1;
        rows[3] |= (na & nb & 1) as u128;
        for row in &mut rows {
            *row &= self.width;
        }
        witness.products(self.g_slot, 1, na as u128, nb as u128);

        for s in &self.steps {
            let (rx, ry, rz) = (rows[s.x], rows[s.y], rows[s.z]);
            let (xz, yz) = (rx ^ rz, ry ^ rz);
            let moved = (ry & s.move_y) | (rz & s.move_z);
            rows[s.x] = rx ^ ry ^ rz ^ moved;
            rows[s.y] = ((((xz & yz) ^ rz) & s.products) << 1) | moved;
            witness.products(s.slot, s.products, xz, yz);
        }

        let (rx, ry) = (rows[self.last.0], rows[self.last.1]);
        let sum = rx.wrapping_add(ry) & self.width;
        let carry_in = sum ^ rx ^ ry;
        witness.products(self.carry_slot, self.carries, rx ^ carry_in, ry ^ carry_in);
        sum
    }
}
