//! Polynomial helpers over wires, each a few rows per term.

use crate::rec::circuit::{Builder, Ew};
use primitives::field::F192;

/// `Σ_i c_i·x^i`, by Horner, constant first.
pub fn poly_eval(b: &mut Builder, coeffs: &[Ew], x: Ew) -> Ew {
    let (&last, rest) = coeffs.split_last().expect("a polynomial has a coefficient");
    rest.iter().rev().fold(last, |acc, &c| b.mul_add(acc, x, c))
}

/// The line through `(0, a)` and `(1, c)` at `r`: `a + r·(a + c)`.
pub fn interp(b: &mut Builder, a: Ew, c: Ew, r: Ew) -> Ew {
    let d = b.add(a, c);
    b.mul_add(r, d, a)
}

/// `v·(1 + r)`.
pub fn times_one_plus(b: &mut Builder, v: Ew, r: Ew) -> Ew {
    b.mul_add(v, r, v)
}

/// `eq(r, x)` for every `x`, lowest coordinate first: entry `x` is `Π_j (x_j ? r_j : 1 + r_j)`.
pub fn eq_table(b: &mut Builder, point: &[Ew]) -> Vec<Ew> {
    let mut table = vec![b.one()];
    for &r in point {
        let low: Vec<Ew> = table.iter().map(|&v| times_one_plus(b, v, r)).collect();
        let high: Vec<Ew> = table.iter().map(|&v| b.mul(v, r)).collect();
        table = low;
        table.extend(high);
    }
    table
}

/// `eq(bits, point)` for public Boolean `bits`: `Π_j (bit_j ? z_j : 1 + z_j)`, `bits` lowest first.
pub fn eq_bits(b: &mut Builder, bits: usize, point: &[Ew]) -> Ew {
    let mut acc = b.one();
    for (j, &z) in point.iter().enumerate() {
        acc = if bits >> j & 1 == 1 { b.mul(acc, z) } else { times_one_plus(b, acc, z) };
    }
    acc
}

/// `eq(x, y) = Π_j (1 + x_j + y_j)`.
pub fn eq_eval(b: &mut Builder, x: &[Ew], y: &[Ew]) -> Ew {
    assert_eq!(x.len(), y.len());
    let mut acc = b.one();
    for (&u, &v) in x.iter().zip(y) {
        let s = b.add(u, v);
        acc = times_one_plus(b, acc, s);
    }
    acc
}

/// `Π_j x_j`.
pub fn product(b: &mut Builder, xs: &[Ew]) -> Ew {
    let mut acc = b.one();
    for &x in xs {
        acc = b.mul(acc, x);
    }
    acc
}

/// `[1, x, x^2, ...]`, `n` terms.
pub fn powers(b: &mut Builder, x: Ew, n: usize) -> Vec<Ew> {
    let mut out = Vec::with_capacity(n);
    let mut acc = b.one();
    for _ in 0..n {
        out.push(acc);
        acc = b.mul(acc, x);
    }
    out
}

/// The MLE of `[base ^ (z << shift)]` at `point`: `base + Σ_i point_i·2^(i+shift)`, linear in the point.
pub fn int_index_mle(b: &mut Builder, base: u64, shift: u32, point: &[Ew]) -> Ew {
    let mut acc = b.e_const(F192::new(base, 0, 0));
    for (i, &z) in point.iter().enumerate() {
        acc = b.mul_const_add(z, F192::new(1 << (i as u32 + shift), 0, 0), acc);
    }
    acc
}
