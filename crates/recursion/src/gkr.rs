//! Bounded radix-four GKR: one optional binary root, then quaternary layers.

use crate::{
    Error,
    algebra::{mle_eval, poly_eval},
    context::Context,
    protocol::{Dimension, MAX_STACK_VARS, MAX_VARS, Point},
    transcript::Transcript,
};

pub(crate) struct GkrResult<F: Copy> {
    pub point: Point<F>,
    pub values: [F; 3],
}

pub(crate) fn verify<C: Context>(
    depth: &Dimension<C::F>,
    enabled: C::F,
    transcript: &mut Transcript<C>,
) -> Result<GkrResult<C::F>, Error> {
    let ctx = transcript.context();
    ctx.assert_bool(enabled)?;
    ctx.assert_zero(depth.contains(MAX_STACK_VARS))?;
    let shared = transcript.scalar(enabled)?;
    let count = transcript.scalar(enabled)?;
    // The inverse is itself constrained; an inactive count is allowed to be
    // zero without imposing an impossible inverse constraint on that branch.
    ctx.inverse(ctx.select(enabled, count, ctx.one()))?;
    let mut combiner = transcript.sample(enabled)?;
    let mut point = Point::zero(ctx, depth.clone());
    let mut values = [shared, shared, count];
    let odd = depth.bits().bits()[0];
    let binary = ctx.mul(enabled, odd);
    let mut children = [[ctx.zero(); 2]; 3];
    for child in &mut children {
        for value in child {
            *value = transcript.scalar(binary)?;
        }
    }
    let products = children.map(|child| ctx.mul(child[0], child[1]));
    ctx.assert_equal_if(
        binary,
        poly_eval(ctx, &values, combiner),
        poly_eval(ctx, &products, combiner),
    )?;
    let challenge = transcript.sample(binary)?;
    for (value, child) in values.iter_mut().zip(children) {
        *value = ctx.select(binary, mle_eval(ctx, &child, &[challenge]), *value);
    }
    point.coords[0] = challenge;
    combiner = ctx.select(binary, transcript.sample(binary)?, combiner);

    for layer in 0..MAX_STACK_VARS / 2 {
        // At this point the equality point has 2*layer + odd coordinates.
        // Both parity branches share the same quartic transcript operations.
        let active = ctx.mul(enabled, depth.contains(2 * layer + 1));
        let mut claim = poly_eval(ctx, &values, combiner);
        let mut round_point = [ctx.zero(); MAX_VARS];
        for (i, slot) in round_point.iter_mut().enumerate().take(2 * layer + 1) {
            let round = if i == 2 * layer { ctx.mul(active, odd) } else { active };
            let coefficients = transcript.round_poly(round, 5, claim, Some(point.coords[i]))?;
            *slot = transcript.sample(round)?;
            claim = ctx.select(round, poly_eval(ctx, &coefficients, *slot), claim);
        }
        let mut children = [[ctx.zero(); 4]; 3];
        for child in &mut children {
            for value in child {
                *value = transcript.scalar(active)?;
            }
        }
        let products = children.map(|child| ctx.mul(ctx.mul(child[0], child[1]), ctx.mul(child[2], child[3])));
        ctx.assert_equal_if(active, claim, poly_eval(ctx, &products, combiner))?;
        let low = transcript.sample(active)?;
        let high = transcript.sample(active)?;
        for (value, child) in values.iter_mut().zip(children) {
            *value = ctx.select(active, mle_eval(ctx, &child, &[low, high]), *value);
        }
        combiner = ctx.select(active, transcript.sample(active)?, combiner);
        for i in 0..(2 * layer + 3).min(MAX_STACK_VARS) {
            let coordinate = match i {
                0 => low,
                1 => high,
                _ => round_point[i - 2],
            };
            point.coords[i] = ctx.select(active, coordinate, point.coords[i]);
        }
    }
    Ok(GkrResult { point, values })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::{Source, Symbolic, Witness};
    use fiat_shamir::transcript::{Challenger, ProverState, RawProof};
    use leanvm_guest::Field;
    use primitives::field::{F64, F192};
    use zk_alloc::ArenaVec;

    fn field(value: F192) -> Field {
        Field::new(value.c0, value.c1, value.c2)
    }

    fn program<C: Context>(ctx: &C) -> Result<Vec<C::F>, Error> {
        let depth = Dimension::new(ctx, ctx.public(0)?, MAX_STACK_VARS)?;
        let enabled = ctx.public(1)?;
        let mut transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        let result = verify(&depth, enabled, &mut transcript)?;
        let mut output = result.values.to_vec();
        output.extend(result.point.coords);
        // An unconditional continuation checks that inactive protocol slots did
        // not consume a source word or ratchet the transcript.
        output.push(transcript.sample(ctx.one())?);
        Ok(output)
    }

    #[test]
    fn one_symbolic_program_matches_production_for_odd_even_and_zero_depth() {
        let symbolic = Symbolic::new(2);
        let output = program(&symbolic).unwrap();
        let circuit = symbolic.finish();
        for depth in 0..=5 {
            let leaves: Vec<_> = (0..(1usize << depth))
                .map(|i| F192::new(7 + i as u64, 11, 13))
                .collect();
            let mut reversed = leaves.clone();
            reversed.reverse();
            // The shorter count tree exercises identity-padded children too.
            let count: Vec<_> = (0..leaves.len().div_ceil(2))
                .map(|i| F192::new(17 + i as u64, 19, 23))
                .collect();
            let mut prover = ProverState::new([F64::ZERO; 4], [F64::ZERO; 4]);
            let expected = lean_vm::gkr::prove_product_triple(
                [
                    ArenaVec::from_slice(&leaves),
                    ArenaVec::from_slice(&reversed),
                    ArenaVec::from_slice(&count),
                ],
                &mut prover,
                lean_vm::gkr::RootShape::FirstTwoShared,
            );
            let next = field(prover.sample());
            let proof = prover.into_proof();
            let raw = RawProof {
                stream: proof.stream,
                merkle: vec![],
            };
            let public = [Field::from(depth as u64), Field::ONE];
            let witness = Witness::new(&public, vec![Source::Native(&raw)]);
            let actual = program(&witness).unwrap();
            assert_eq!(&actual[..3], &expected.values.map(field));
            assert_eq!(
                &actual[3..3 + depth],
                expected.point.into_iter().map(field).collect::<Vec<_>>()
            );
            assert!(
                actual[3 + depth..3 + MAX_VARS]
                    .iter()
                    .all(|&value| value == Field::ZERO)
            );
            assert_eq!(actual[3 + MAX_VARS], next);
            let values = circuit.evaluate(&public, &witness.finish().unwrap()).unwrap();
            assert_eq!(
                output.iter().map(|wire| values[wire.index()]).collect::<Vec<_>>(),
                actual
            );
        }
        for depth in [27usize, 28] {
            let proof = unit_proof(depth);
            let mut reference = riscv_proof::portable::transcript::Transcript::new(&proof, [0; 32], [0; 32]);
            let expected = riscv_proof::portable::gkr::verify(depth, &mut reference).unwrap();
            let next = reference.sample();
            reference.finish().unwrap();
            let public = [Field::from(depth as u64), Field::ONE];
            let witness = Witness::new(&public, vec![Source::Risc(&proof)]);
            let actual = program(&witness).unwrap();
            assert_eq!(&actual[..3], &expected.values);
            assert_eq!(&actual[3..3 + depth], &expected.point);
            assert_eq!(actual[3 + MAX_VARS], next);
            let values = circuit.evaluate(&public, &witness.finish().unwrap()).unwrap();
            assert_eq!(
                output.iter().map(|wire| values[wire.index()]).collect::<Vec<_>>(),
                actual
            );
        }
        for depth in [0, 1, 2, 27, 28] {
            let public = [Field::from(depth), Field::ZERO];
            let witness = Witness::new(&public, vec![Source::Advice(&[])]);
            let actual = program(&witness).unwrap();
            assert!(actual[..3 + MAX_VARS].iter().all(|&value| value == Field::ZERO));
            let mut reference = ProverState::new([F64::ZERO; 4], [F64::ZERO; 4]);
            assert_eq!(actual[3 + MAX_VARS], field(reference.sample()));
            let private = witness.finish().unwrap();
            let values = circuit.evaluate(&public, &private).unwrap();
            assert_eq!(
                output.iter().map(|wire| values[wire.index()]).collect::<Vec<_>>(),
                actual
            );
        }
    }

    fn unit_proof(depth: usize) -> riscv_proof::Proof {
        let mut stream = vec![Field::ONE; 2];
        let mut remaining = depth;
        while remaining != 0 {
            let step = if remaining & 1 == 1 { 1 } else { 2 };
            let width = 1 << step;
            stream.extend(std::iter::repeat_n(Field::ZERO, (depth - remaining) * width));
            stream.extend(std::iter::repeat_n(Field::ONE, 3 * width));
            remaining -= step;
        }
        riscv_proof::Proof { stream, merkle: vec![] }
    }

    #[test]
    fn zero_counts_and_corrupted_binary_quartic_children_reject() {
        let symbolic = Symbolic::new(2);
        program(&symbolic).unwrap();
        let circuit = symbolic.finish();
        for depth in 0..=3 {
            let public = [Field::from(depth as u64), Field::ONE];
            let valid = unit_proof(depth);
            let witness = Witness::new(&public, vec![Source::Risc(&valid)]);
            program(&witness).unwrap();
            let mut private = witness.finish().unwrap();
            // First two scalar advice slots are the root and count. An
            // enforced inverse prevents a malicious zero-count witness.
            private[1] = Field::ZERO;
            assert!(circuit.evaluate(&public, &private).is_err());
            let mut zero_count = valid.clone();
            zero_count.stream[1] = Field::ZERO;
            assert!(program(&Witness::new(&public, vec![Source::Risc(&zero_count)])).is_err());
            if depth != 0 {
                private[1] = Field::ONE;
                let last_child = private.iter().rposition(|&value| value == Field::ONE).unwrap();
                private[last_child] = Field::ZERO;
                assert!(circuit.evaluate(&public, &private).is_err());
                let mut corrupt = valid;
                // The final three child tables occur after all sumcheck rounds.
                let last = corrupt.stream.len() - 1;
                corrupt.stream[last] = Field::ZERO;
                assert!(program(&Witness::new(&public, vec![Source::Risc(&corrupt)])).is_err());
            }
        }
        for (depth, enabled) in [(29, 1), (34, 1), (1, 2)] {
            let public = [Field::from(depth), Field::from(enabled)];
            assert!(program(&Witness::new(&public, vec![Source::Advice(&[])])).is_err());
        }
    }
}
