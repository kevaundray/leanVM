// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/bcc-research/bolt-rs, MIT.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Production WHIR verification, using full-image authenticated Merkle leaves.
use alloc::{vec, vec::Vec};
use leanvm_guest::Field as F;

use super::algebra::{eq_eval, eq_kernel, mle_eval, poly_eval, powers};
use super::transcript::{Error, Transcript};

pub const SECURITY_BITS: usize = 128;
pub const INITIAL_FOLDING_FACTOR: usize = 6;
pub const SUBSEQUENT_FOLDING_FACTOR: usize = 4;
pub const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 3;
pub const RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR: usize = 1;
pub const RESIDUAL_MAX_LOG: usize = 5;
pub const QUERY_GRINDING_BITS: usize = 17;
pub const MIN_STACKED_LOG: usize = 15;
pub const MAX_STACKED_LOG: usize = 28;
pub const LOG_INV_RATE_0: usize = 1;

/// Audited 128-bit Johnson/OOD profile, indexed by rate minus one and log size minus 15.
pub const WHIR_QUERIES: [[&[usize]; 14]; 4] = [
    [
        &[223, 55],
        &[223, 56, 30],
        &[223, 56, 31],
        &[224, 56, 32],
        &[224, 56, 32],
        &[224, 56, 32, 22],
        &[224, 56, 32, 22],
        &[225, 56, 32, 23],
        &[225, 56, 32, 23],
        &[225, 56, 32, 23, 17],
        &[226, 56, 32, 23, 17],
        &[226, 56, 32, 23, 18],
        &[227, 56, 32, 23, 18],
        &[228, 56, 32, 23, 18, 14],
    ],
    [
        &[112, 45],
        &[112, 45, 27],
        &[112, 45, 28],
        &[112, 45, 28],
        &[112, 45, 28],
        &[112, 45, 28, 20],
        &[112, 45, 28, 20],
        &[112, 45, 28, 21],
        &[112, 45, 28, 21],
        &[113, 45, 28, 21, 16],
        &[113, 45, 28, 21, 16],
        &[113, 45, 28, 21, 16],
        &[113, 45, 28, 21, 16],
        &[113, 45, 28, 21, 17, 13],
    ],
    [
        &[75, 37],
        &[75, 37, 24],
        &[75, 38, 25],
        &[75, 38, 25],
        &[75, 38, 25],
        &[75, 38, 25, 18],
        &[75, 38, 25, 19],
        &[75, 38, 25, 19],
        &[75, 38, 25, 19],
        &[75, 38, 25, 19, 15],
        &[75, 38, 25, 19, 15],
        &[75, 38, 25, 19, 15],
        &[75, 38, 25, 19, 15],
        &[76, 38, 25, 19, 16, 13],
    ],
    [
        &[56, 32],
        &[56, 32, 22],
        &[56, 32, 22],
        &[56, 32, 23],
        &[56, 32, 23],
        &[56, 32, 23, 17],
        &[56, 32, 23, 17],
        &[56, 32, 23, 18],
        &[56, 32, 23, 18],
        &[57, 32, 23, 18, 14],
        &[57, 32, 23, 18, 14],
        &[57, 32, 23, 18, 15],
        &[57, 33, 23, 18, 15],
        &[57, 33, 23, 18, 15, 12],
    ],
];

#[derive(Clone, Debug)]
pub struct WhirConfig {
    pub log_inv_rates: Vec<usize>,
    pub folds: Vec<usize>,
    pub queries: &'static [usize],
}

pub fn derive_config(log_n: usize, log_inv_rate: usize) -> Result<WhirConfig, Error> {
    if !(MIN_STACKED_LOG..=MAX_STACKED_LOG).contains(&log_n) || !(1..=4).contains(&log_inv_rate) {
        return Err(Error::InvalidShape);
    }
    let mut folds = vec![INITIAL_FOLDING_FACTOR];
    let mut log_inv_rates = vec![log_inv_rate];
    let mut remaining = log_n - INITIAL_FOLDING_FACTOR;
    while remaining > RESIDUAL_MAX_LOG {
        let last = folds.len() - 1;
        let reduction = if last == 0 {
            RS_DOMAIN_INITIAL_REDUCTION_FACTOR
        } else {
            RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
        };
        log_inv_rates.push(log_inv_rates[last] + folds[last] - reduction);
        let fold = SUBSEQUENT_FOLDING_FACTOR.min(remaining);
        remaining -= fold;
        folds.push(fold);
    }
    let queries = WHIR_QUERIES[log_inv_rate - 1][log_n - MIN_STACKED_LOG];
    if queries.len() != folds.len() {
        return Err(Error::InvalidShape);
    }
    Ok(WhirConfig {
        log_inv_rates,
        folds,
        queries,
    })
}

/// Low-to-high disjoint bit chunks of each complete 192-bit challenge. Duplicates
/// remain in transcript order, including chunks crossing a limb boundary.
pub fn sample_queries(transcript: &mut Transcript<'_>, block_length: usize, count: usize) -> Result<Vec<usize>, Error> {
    if !block_length.is_power_of_two() || block_length < 2 || count > 228 {
        return Err(Error::InvalidShape);
    }
    let depth = block_length.trailing_zeros() as usize;
    if depth > MAX_STACKED_LOG + 4 {
        return Err(Error::InvalidShape);
    }
    let mut queries = Vec::with_capacity(count);
    while queries.len() < count {
        let bits = transcript.sample().0;
        for chunk in 0..(192 / depth).min(count - queries.len()) {
            let offset = chunk * depth;
            let limb = offset / 64;
            let shift = offset % 64;
            let mut value = bits[limb] >> shift;
            if shift + depth > 64 {
                value |= bits[limb + 1] << (64 - shift);
            }
            queries.push((value as usize) & (block_length - 1));
        }
    }
    Ok(queries)
}

fn induced_weight(queries: &[usize], weights: &[F], point: &[F]) -> F {
    let mut roots = Vec::with_capacity(point.len());
    let mut layer: Vec<F> = (1..=point.len()).map(|i| F([1u64 << i, 0, 0])).collect();
    let mut root = F::ONE;
    for i in 0..point.len() {
        roots.push(root);
        for value in &mut layer[i..] {
            *value = value.square() + root * *value;
        }
        root = layer[i];
    }
    let inverses: Vec<F> = roots
        .iter()
        .map(|r| r.inverse().expect("nonzero subspace root"))
        .collect();
    let mut total = F::ZERO;
    for (&query, &weight) in queries.iter().zip(weights) {
        let mut basis = F([query as u64, 0, 0]);
        let mut product = weight;
        for (i, &challenge) in point.iter().enumerate() {
            product *= F::ONE + challenge * (F::ONE + basis * inverses[i]);
            basis = basis.square() + roots[i] * basis;
        }
        total += product;
    }
    total
}

enum GluedWeight {
    Equality(Vec<F>),
    Queries { positions: Vec<usize>, weights: Vec<F> },
}

struct GluedClaim {
    scalar: F,
    fold_start: usize,
    weight: GluedWeight,
}

/// Verify an opening of the committed base-field stack. The caller's weight is
/// evaluated once, in witness-coordinate order (not fold-challenge order).
/// L0 leaves must contain all 64 lanes, including the leading zero prefix of
/// a pruned commitment. Compact transport must restore that prefix before here.
pub fn verify_whir(
    transcript: &mut Transcript<'_>,
    log_n: usize,
    log_inv_rate: usize,
    target: F,
    root: [u8; 32],
    evaluate_basis: impl Fn(&[F]) -> F,
) -> Result<(), Error> {
    let config = derive_config(log_n, log_inv_rate)?;
    let mut running_quad = transcript.sumcheck_round_poly(3, target, None)?;
    let mut folds = Vec::with_capacity(log_n);
    let mut glued = Vec::with_capacity(2 * config.folds.len());
    let mut current_root = root;
    for (level, &fold_count) in config.folds.iter().enumerate() {
        let fold_start = folds.len();
        for _ in 0..fold_count {
            let challenge = transcript.sample();
            folds.push(challenge);
            running_quad = transcript.sumcheck_round_poly(3, poly_eval(&running_quad, challenge), None)?;
        }
        let message_log = log_n - folds.len();
        let final_level = level + 1 == config.folds.len();
        let mut next_root = [0; 32];
        let mut residual = Vec::new();
        let mut ood = None;
        if final_level {
            residual = transcript.next_scalars(1 << message_log)?;
        } else {
            next_root = transcript.next_root()?;
            let point = transcript.samples(message_log);
            let value = transcript.next_scalar()?;
            ood = Some((point, transcript.sumcheck_round_poly(3, value, None)?));
        }
        transcript.grind_check(QUERY_GRINDING_BITS)?;
        let block_length = 1 << (message_log + config.log_inv_rates[level]);
        let queries = sample_queries(transcript, block_length, config.queries[level])?;
        let lambda = transcript.sample();
        let query_weights = powers(lambda, queries.len());
        let lanes = 1 << fold_count;
        let rows = transcript.merkle(
            &current_root,
            block_length,
            &queries,
            if level == 0 { lanes } else { 3 * lanes },
        )?;
        let lane_weights = eq_kernel(&folds[fold_start..]);
        let mut enforced = F::ZERO;
        for (row, &query_weight) in rows.iter().zip(&query_weights) {
            let mut value = F::ZERO;
            for (lane, &weight) in lane_weights.iter().enumerate() {
                let cell = if level == 0 {
                    F([row[lanes - 1 - lane], 0, 0])
                } else {
                    F([row[3 * lane], row[3 * lane + 1], row[3 * lane + 2]])
                };
                value += weight * cell;
            }
            enforced += query_weight * value;
        }
        let intro = transcript.sumcheck_round_poly(3, enforced, None)?;
        let mut scalar = lambda;
        if let Some((point, ood_intro)) = ood {
            for (q, i) in running_quad.iter_mut().zip(ood_intro) {
                *q += scalar * i;
            }
            glued.push(GluedClaim {
                scalar,
                fold_start: folds.len(),
                weight: GluedWeight::Equality(point),
            });
            scalar *= lambda;
        }
        for (q, i) in running_quad.iter_mut().zip(intro) {
            *q += scalar * i;
        }
        glued.push(GluedClaim {
            scalar,
            fold_start: folds.len(),
            weight: GluedWeight::Queries {
                positions: queries,
                weights: query_weights,
            },
        });
        if final_level {
            let tail_start = folds.len();
            let mut running_target = F::ZERO;
            for round in 0..message_log {
                let challenge = transcript.sample();
                running_target = poly_eval(&running_quad, challenge);
                folds.push(challenge);
                if round + 1 < message_log {
                    running_quad = transcript.sumcheck_round_poly(3, running_target, None)?;
                }
            }
            let mut witness_point = Vec::with_capacity(log_n);
            witness_point.extend_from_slice(&folds[INITIAL_FOLDING_FACTOR..]);
            witness_point.extend_from_slice(&folds[..INITIAL_FOLDING_FACTOR]);
            let mut weight = evaluate_basis(&witness_point);
            for claim in glued {
                let point = &folds[claim.fold_start..];
                let value = match claim.weight {
                    GluedWeight::Equality(z) => eq_eval(&z, point),
                    GluedWeight::Queries { positions, weights } => induced_weight(&positions, &weights, point),
                };
                weight += claim.scalar * value;
            }
            return if weight * mle_eval(&residual, &folds[tail_start..]) == running_target {
                Ok(())
            } else {
                Err(Error::ClaimMismatch)
            };
        }
        current_root = next_root;
    }
    Err(Error::InvalidShape)
}

pub struct StackClaim<'a> {
    pub weight: &'a dyn Fn(&[F]) -> F,
    pub value: F,
}

/// Batch already-bound claims with one challenge, using identical powers for
/// their targets and their terminal weight evaluations.
pub fn verify_stacked_opening(
    transcript: &mut Transcript<'_>,
    root: [u8; 32],
    stack_log: usize,
    log_inv_rate: usize,
    claims: &[StackClaim<'_>],
) -> Result<(), Error> {
    if claims.is_empty() || claims.len() > super::transcript::MAX_ELEMENTS {
        return Err(Error::InvalidShape);
    }
    let scales = powers(transcript.sample(), claims.len());
    let target = claims
        .iter()
        .zip(&scales)
        .fold(F::ZERO, |sum, (claim, &scale)| sum + scale * claim.value);
    verify_whir(transcript, stack_log, log_inv_rate, target, root, |point| {
        claims
            .iter()
            .zip(&scales)
            .fold(F::ZERO, |sum, (claim, &scale)| sum + scale * (claim.weight)(point))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn query_chunks_cross_limbs_without_discarding_challenge_bits() {
        let proof = crate::Proof {
            stream: Vec::new(),
            merkle: Vec::new(),
        };
        let mut transcript = Transcript::new(&proof, [3; 32], [5; 32]);
        let mut reference = Transcript::new(&proof, [3; 32], [5; 32]);
        let mut expected = Vec::new();
        while expected.len() < 55 {
            let sample = reference.sample().0;
            for chunk in 0..(192 / 23).min(55 - expected.len()) {
                let mut query = 0;
                for bit in 0..23 {
                    let offset = chunk * 23 + bit;
                    query |= (((sample[offset / 64] >> (offset % 64)) & 1) as usize) << bit;
                }
                expected.push(query);
            }
        }
        assert_eq!(sample_queries(&mut transcript, 1 << 23, 55).unwrap(), expected);
        assert_eq!(transcript.sample(), reference.sample());
    }
}
