//! The link term of a linked batch, as `verifier::binary_spartan` describes it: link row `j` of instance `i` also
//! reads `z_{i-1}[out_j]`, so the zerocheck's A claim carries `T = sum_i next(i, x_out) Q(i)` with
//! `Q(i) = sum_j rho_j z_i[out_j]`. The prover sends `T`, proves it by a sumcheck over the instance bits down to
//! `next(r, x_out) Q(r)`, and `Q(r)` by one over the `out` block's word bits down to its 64 slices, which a second
//! ring-switched claim binds to the commitment.

use crate::block::Links;
use fiat_shamir::transcript::ProverState;
use flock::lincheck::{QuirkyPoint, product_sumcheck};
use flock::zerocheck::K_SKIP;
use leanvm_core::pcs::RingSwitchClaim;
use primitives::field::F192;
use primitives::multilinear::{eq_table, lagrange_weights_naive};

/// `next(i, y)` for every boolean `i` of `y.len()` bits: `eq(y, i + 1)`, and zero at the last `i` (no wrap).
pub fn next_table(y: &[F192]) -> Vec<F192> {
    let mut table = eq_table(y);
    table.rotate_left(1);
    *table.last_mut().expect("non-empty table") = F192::ZERO;
    table
}

/// The multilinear extension of `next(x, y)`, one iff `y = x + 1` on little-endian bits with no wrap, in `O(len)`.
pub fn next_eval(x: &[F192], y: &[F192]) -> F192 {
    assert_eq!(x.len(), y.len());
    let mut above = vec![F192::ONE; x.len() + 1];
    for t in (0..x.len()).rev() {
        above[t] = above[t + 1] * (F192::ONE + x[t] + y[t]);
    }
    let mut carry = F192::ONE;
    let mut total = F192::ZERO;
    for t in 0..x.len() {
        total += carry * (F192::ONE + x[t]) * y[t] * above[t + 1];
        carry *= x[t] * (F192::ONE + y[t]);
    }
    total
}

/// The quirky row weight of every link row at the zerocheck's point: the skip weight of the row's low bits times
/// `eq(x_inner_rest, row / 2^k_skip)`.
fn row_weights(links: &Links, x: &QuirkyPoint) -> Vec<F192> {
    let skip = lagrange_weights_naive(K_SKIP, x.z_skip);
    let high = eq_table(&x.x_inner_rest);
    (links.first_row..links.first_row + links.count)
        .map(|row| skip[row % (1 << K_SKIP)] * high[row >> K_SKIP])
        .collect()
}

/// Prove the link term after the zerocheck, before lincheck, and return the ring-switched claim it leaves.
///
/// `z` is the instance-major packed witness (`2^k_log / 64` words per instance) and `stripes` lincheck's byte layout
/// of it, over `2^n_log` instances.
pub fn prove(
    links: &Links,
    k_log: usize,
    n_log: usize,
    z: &[u64],
    stripes: &[u8],
    x: &QuirkyPoint,
    ps: &mut ProverState,
) -> RingSwitchClaim {
    let k = 1usize << k_log;
    let wpb = k / 64;
    let n = 1usize << n_log;
    let rho = row_weights(links, x);

    // Q(i) through one 256-entry subset-sum table per byte of the `out` words.
    let base = links.out_base / 64;
    let tables: Vec<[F192; 256]> = rho
        .chunks(8)
        .map(|weights| {
            let mut table = [F192::ZERO; 256];
            for (b, &w) in weights.iter().enumerate() {
                for low in 0..1usize << b {
                    table[1 << b | low] = table[low] + w;
                }
            }
            table
        })
        .collect();
    let q: Vec<F192> = parallel::map_collect(n, |i| {
        let words = &z[i * wpb + base..i * wpb + base + links.words()];
        tables.iter().enumerate().fold(F192::ZERO, |acc, (p, table)| {
            acc + table[(words[p / 8] >> (8 * (p % 8))) as u8 as usize]
        })
    });

    let next = next_table(&x.x_outer);
    let shifted = next.iter().zip(&q).fold(F192::ZERO, |acc, (&a, &b)| acc + a * b);
    ps.add_scalar(shifted);
    let (r_out, _) = product_sumcheck(next, q, n_log, ps);

    // Q(r) = sum_t rho_t z(out_base + t, r) over the whole aligned block, folded at r from the stripes.
    let width = 1usize << links.out_log;
    let eq_r = eq_table(&r_out);
    let folded = parallel::fold_reduce(
        n / 8,
        || vec![F192::ZERO; width],
        |acc, s| {
            let mut table = [F192::ZERO; 256];
            for (b, &w) in eq_r[8 * s..8 * s + 8].iter().enumerate() {
                for low in 0..1usize << b {
                    table[1 << b | low] = table[low] + w;
                }
            }
            let bytes = &stripes[s * k + links.out_base..s * k + links.out_base + width];
            for (v, &byte) in acc.iter_mut().zip(bytes) {
                *v += table[byte as usize];
            }
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(b) {
                *x += y;
            }
            a
        },
    );
    let scale = next_eval(&r_out, &x.x_outer);
    let mut comb = vec![F192::ZERO; width];
    for (c, &r) in comb.iter_mut().zip(&rho) {
        *c = scale * r;
    }
    let (r_sub, slices) = product_sumcheck(comb, folded, links.out_log - K_SKIP, ps);
    ps.add_scalars(&slices);

    let block = links.out_base >> links.out_log;
    let block_bits = (0..k_log - links.out_log).map(|bit| if block >> bit & 1 == 1 { F192::ONE } else { F192::ZERO });
    RingSwitchClaim {
        suffix_point: r_sub.into_iter().chain(block_bits).chain(r_out).collect(),
        s_hat_v: Some(slices),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// The prover's table and its MLE against the definition `sum_{a < 2^n - 1} eq(x, a) eq(y, a + 1)`.
    #[test]
    fn next_matches_definition() {
        let mut rng = Rng::new(11);
        for n in 1..=5 {
            let (x, y) = (rng.ext_vec(n), rng.ext_vec(n));
            let point = |a: usize| -> Vec<F192> {
                (0..n)
                    .map(|bit| if a >> bit & 1 == 1 { F192::ONE } else { F192::ZERO })
                    .collect()
            };
            let eq = |p: &[F192], q: &[F192]| {
                p.iter()
                    .zip(q)
                    .fold(F192::ONE, |acc, (&a, &b)| acc * (F192::ONE + a + b))
            };
            let expected =
                (0..(1usize << n) - 1).fold(F192::ZERO, |acc, a| acc + eq(&x, &point(a)) * eq(&y, &point(a + 1)));
            assert_eq!(next_eval(&x, &y), expected, "n = {n}");
            let table_mle = eq_table(&x)
                .iter()
                .zip(next_table(&y))
                .fold(F192::ZERO, |acc, (&e, t)| acc + e * t);
            assert_eq!(table_mle, expected, "n = {n}");
        }
    }
}
