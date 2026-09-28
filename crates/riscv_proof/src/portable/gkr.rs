//! Three RLC-batched identity-padded grand products, reduced by radix-four GKR.

use super::{
    algebra::{mle_eval, poly_eval},
    transcript::{Error, Transcript},
};
use alloc::vec::Vec;
use leanvm_guest::Field as F;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GkrResult {
    pub count: F,
    pub point: Vec<F>,
    pub values: [F; 3],
}

/// The balancing products share one transmitted root. The third is the count
/// product and must be nonzero: a zero multiplicity is not a valid bus witness.
pub fn verify(depth: usize, transcript: &mut Transcript<'_>) -> Result<GkrResult, Error> {
    // The caller must be able to represent the logical cube's size. All local
    // allocations below are bounded by this depth, not by prover messages.
    if depth >= usize::BITS as usize {
        return Err(Error::InvalidShape);
    }
    let shared = transcript.next_scalar()?;
    let count = transcript.next_scalar()?;
    if count == F::ZERO {
        return Err(Error::ZeroCount);
    }
    let mut combiner = transcript.sample();
    let mut point = Vec::with_capacity(depth);
    let mut round_point = Vec::with_capacity(depth);
    let mut values = [shared, shared, count];
    let mut layer = depth;
    while layer != 0 {
        // An odd-depth tree has a single binary root-most layer. Every
        // subsequent contraction consumes two levels and a quartic sumcheck.
        let step = if layer & 1 != 0 { 1 } else { 2 };
        let width = 1usize << step;
        let mut claim = poly_eval(&values, combiner);
        round_point.clear();
        for &equality in &point {
            let coefficients = transcript.sumcheck_round_poly(width + 1, claim, Some(equality))?;
            let challenge = transcript.sample();
            round_point.push(challenge);
            claim = poly_eval(&coefficients, challenge);
        }
        let mut children = [[F::ZERO; 4]; 3];
        let mut products = [F::ONE; 3];
        for (child, product) in children.iter_mut().zip(&mut products) {
            child[0] = transcript.next_scalar()?;
            *product = child[0];
            for value in &mut child[1..width] {
                *value = transcript.next_scalar()?;
                *product *= *value;
            }
        }
        if claim != poly_eval(&products, combiner) {
            return Err(Error::InvalidGkr);
        }
        point.clear();
        for _ in 0..step {
            point.push(transcript.sample());
        }
        for (value, child) in values.iter_mut().zip(&children) {
            *value = mle_eval(&child[..width], &point);
        }
        combiner = transcript.sample();
        point.extend_from_slice(&round_point);
        layer -= step;
    }
    Ok(GkrResult { count, point, values })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Proof;
    use alloc::vec;

    // Unit trees have constant one at every layer. Their normalized round
    // messages therefore contain only zeros, while each child value is one.
    fn unit_proof(depth: usize) -> Proof {
        let mut stream = vec![F::ONE; 2];
        let mut layer = depth;
        while layer != 0 {
            let step = if layer & 1 != 0 { 1 } else { 2 };
            let width = 1usize << step;
            stream.extend(core::iter::repeat_n(F::ZERO, (depth - layer) * width));
            stream.extend(core::iter::repeat_n(F::ONE, 3 * width));
            layer -= step;
        }
        Proof {
            stream,
            merkle: Vec::new(),
        }
    }

    #[test]
    fn binary_and_quaternary_layers_reduce_unit_trees() {
        for depth in 0..=5 {
            let p = unit_proof(depth);
            let mut t = Transcript::new(&p, [0; 32], [0; 32]);
            let result = verify(depth, &mut t).unwrap();
            assert_eq!(result.count, F::ONE);
            assert_eq!(result.values, [F::ONE; 3]);
            assert_eq!(result.point.len(), depth);
            t.finish().unwrap();
        }
    }

    #[test]
    fn zero_count_and_inconsistent_children_are_rejected() {
        let mut p = unit_proof(1);
        p.stream[1] = F::ZERO;
        assert_eq!(
            verify(1, &mut Transcript::new(&p, [0; 32], [0; 32])),
            Err(Error::ZeroCount)
        );
        p.stream[1] = F::ONE;
        p.stream[2] = F::ZERO;
        assert_eq!(
            verify(1, &mut Transcript::new(&p, [0; 32], [0; 32])),
            Err(Error::InvalidGkr)
        );
    }
}
