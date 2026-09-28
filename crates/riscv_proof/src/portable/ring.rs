// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Rectangular GF(2)-to-GF(2^64) ring switching over GF(2^192).
use alloc::vec::Vec;
use leanvm_guest::Field as F;

use super::transcript::{Error, Transcript};

pub const RING_MAP_SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];
pub const RING_SWITCH_SOUNDNESS_DEGREE: usize =
    (1usize << 31) + (1usize << 15) + (1usize << 7) + (1usize << 3) + (1usize << 1) + 1;
pub const K_BITS: usize = 64;

fn frobenius(mut value: F, shift: usize) -> F {
    for _ in 0..shift {
        value = value.square();
    }
    value
}

fn phi(mut value: F, challenges: &[F]) -> F {
    for (&challenge, shift) in challenges.iter().zip(RING_MAP_SHIFTS) {
        value += challenge * frobenius(value, shift);
    }
    value
}

/// An authenticated slice family's challenge-derived dense claim. The private
/// coefficients bind evaluate() to exactly the map used to compute target.
pub struct RingClaim {
    pub target: F,
    point: Vec<F>,
    coefficients: [F; K_BITS],
}

impl RingClaim {
    /// Evaluate the MLE of Phi(eq(point, u)), without constructing its table.
    /// The opening caller supplies exactly point.len() suffix coordinates.
    pub fn evaluate(&self, query: &[F]) -> F {
        assert_eq!(self.point.len(), query.len(), "ring weight dimension");
        let mut point_storage = [F::ZERO; super::pcs::MAX_STACKED_LOG];
        let frobenius_point = &mut point_storage[..self.point.len()];
        frobenius_point.copy_from_slice(&self.point);
        let mut total = F::ZERO;
        for &coefficient in &self.coefficients {
            let mut product = coefficient;
            for (value, &challenge) in frobenius_point.iter_mut().zip(query) {
                product *= F::ONE + *value + challenge;
                *value = value.square();
            }
            total += product;
        }
        total
    }
}

/// One challenge-derived map shared by every slice family in an opening.
pub struct RingMap {
    challenges: [F; RING_MAP_SHIFTS.len()],
    coefficients: [F; K_BITS],
}

impl RingMap {
    /// Draw only after every reduction has bound its bit slices.
    pub fn sample(transcript: &mut Transcript<'_>) -> Self {
        let challenges = core::array::from_fn(|_| transcript.sample());
        // C_k = product_{p: k & shift_p != 0} f_p^(2^(k mod shift_p)).
        let mut coefficients = [F::ONE; K_BITS];
        for (&challenge, shift) in challenges.iter().zip(RING_MAP_SHIFTS) {
            let mut power = challenge;
            for exponent in 0..shift {
                for k in (shift + exponent..K_BITS).step_by(2 * shift) {
                    coefficients[k] *= power;
                }
                power = power.square();
            }
        }
        Self {
            challenges,
            coefficients,
        }
    }

    /// Reduce an already-bound 64 bit-slice family without drawing challenges.
    pub fn switch(&self, point: &[F], slices: &[F]) -> Result<RingClaim, Error> {
        if slices.len() != K_BITS || point.len() > super::pcs::MAX_STACKED_LOG {
            return Err(Error::InvalidShape);
        }
        let generator = F([2, 0, 0]);
        let target = slices
            .iter()
            .rev()
            .fold(F::ZERO, |acc, &value| acc * generator + phi(value, &self.challenges));
        Ok(RingClaim {
            target,
            point: point.to_vec(),
            coefficients: self.coefficients,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::algebra::{dot, eq_kernel, mle_eval};
    use super::*;

    #[test]
    fn composed_map_matches_packed_target_and_extended_weight() {
        let proof = crate::Proof {
            stream: Vec::new(),
            merkle: Vec::new(),
        };
        let mut transcript = Transcript::new(&proof, [7; 32], [11; 32]);
        let mut reference = Transcript::new(&proof, [7; 32], [11; 32]);
        let point = [F([17, 19, 23]), F([29, 31, 37]), F([41, 43, 47])];
        let query = [F([53, 59, 61]), F([67, 71, 73]), F([79, 83, 89])];
        let words = [0, 1, 2, u64::MAX, 1 << 63, 0x123456789abcdef, 9, 17];
        let equality = eq_kernel(&point);
        let mut slices = [F::ZERO; K_BITS];
        for (bit, slice) in slices.iter_mut().enumerate() {
            for (&word, &weight) in words.iter().zip(&equality) {
                if word & (1u64 << bit) != 0 {
                    *slice += weight;
                }
            }
        }
        let claim = RingMap::sample(&mut transcript).switch(&point, &slices).unwrap();
        let challenges = reference.samples(RING_MAP_SHIFTS.len());
        let dense: Vec<F> = equality.iter().map(|&value| phi(value, &challenges)).collect();
        let packed: Vec<F> = words.iter().map(|&word| F([word, 0, 0])).collect();
        assert_eq!(claim.target, dot(&dense, &packed));
        assert_eq!(claim.evaluate(&query), mle_eval(&dense, &query));
        assert_eq!(transcript.sample(), reference.sample());
    }
}
