//! Rectangular GF(2)-to-GF(2^64) switching inside GF(2^192).

use crate::{
    Error,
    context::Context,
    protocol::{MAX_STACK_VARS, Point},
    transcript::Transcript,
};

const MAP_SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];
const K_BITS: usize = 64;

fn frobenius<C: Context>(ctx: &C, mut value: C::F, shift: usize) -> C::F {
    for _ in 0..shift {
        value = ctx.mul(value, value);
    }
    value
}

fn phi<C: Context>(ctx: &C, mut value: C::F, challenges: &[C::F; 6]) -> C::F {
    for (&challenge, shift) in challenges.iter().zip(MAP_SHIFTS) {
        value = ctx.add(value, ctx.mul(challenge, frobenius(ctx, value, shift)));
    }
    value
}

pub(crate) struct RingMap<F: Copy> {
    challenges: [F; 6],
    coefficients: [F; K_BITS],
}

pub(crate) struct RingClaim<F: Copy> {
    pub target: F,
    point: Point<F>,
    coefficients: [F; K_BITS],
}

impl<F: Copy> RingMap<F> {
    pub(crate) fn sample<C: Context<F = F>>(transcript: &mut Transcript<C>, enabled: F) -> Result<Self, Error> {
        let ctx = transcript.context();
        ctx.assert_bool(enabled)?;
        let mut challenges = [ctx.zero(); 6];
        for challenge in &mut challenges {
            *challenge = transcript.sample(enabled)?;
        }
        // C_k = product_{p: k & shift_p != 0} f_p^(2^(k mod shift_p)).
        // This is the composed linearized polynomial, not independent maps
        // applied to the original input. The extension is not a 64-bit field.
        let mut coefficients = [ctx.one(); K_BITS];
        for (&challenge, shift) in challenges.iter().zip(MAP_SHIFTS) {
            let mut power = challenge;
            for exponent in 0..shift {
                for k in (shift + exponent..K_BITS).step_by(2 * shift) {
                    coefficients[k] = ctx.mul(coefficients[k], power);
                }
                if exponent + 1 < shift {
                    power = ctx.mul(power, power);
                }
            }
        }
        Ok(Self {
            challenges,
            coefficients,
        })
    }

    pub(crate) fn switch<C: Context<F = F>>(
        &self,
        ctx: &C,
        point: &Point<F>,
        slices: &[F; K_BITS],
    ) -> Result<RingClaim<F>, Error> {
        ctx.assert_zero(point.dim.contains(MAX_STACK_VARS))?;
        // Polynomial-basis generator of GF(2^64), not the extension's Y.
        let generator = ctx.base(2);
        let target = slices.iter().rev().fold(ctx.zero(), |acc, &value| {
            ctx.add(ctx.mul(acc, generator), phi(ctx, value, &self.challenges))
        });
        Ok(RingClaim {
            target,
            point: point.clone(),
            coefficients: self.coefficients,
        })
    }
}

impl<F: Copy> RingClaim<F> {
    pub(crate) fn evaluate<C: Context<F = F>>(&self, ctx: &C, query: &[F]) -> Result<F, Error> {
        let length = query.len().min(MAX_STACK_VARS);
        ctx.assert_zero(self.point.dim.contains(length))?;
        let mut point = [ctx.zero(); MAX_STACK_VARS];
        let mut query_factor = [ctx.one(); MAX_STACK_VARS];
        for i in 0..length {
            let active = self.point.dim.contains(i);
            // Boolean masks commute with Frobenius, so mask once rather than
            // paying for the same dimension selection in all 64 powers.
            point[i] = ctx.mul(active, self.point.coords[i]);
            query_factor[i] = ctx.add(ctx.one(), ctx.mul(active, query[i]));
        }
        let mut total = ctx.zero();
        for (k, &coefficient) in self.coefficients.iter().enumerate() {
            let mut product = coefficient;
            for i in 0..length {
                let factor = ctx.add(query_factor[i], point[i]);
                product = ctx.mul(product, factor);
                if k + 1 < K_BITS {
                    point[i] = ctx.mul(point[i], point[i]);
                }
            }
            total = ctx.add(total, product);
        }
        Ok(total)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        algebra::{dot, eq_kernel, mle_eval},
        context::{Source, Symbolic, Witness},
        protocol::Dimension,
    };
    use leanvm_guest::Field;

    fn program<C: Context>(ctx: &C) -> Result<[C::F; 3], Error> {
        let dimension = Dimension::new(ctx, ctx.public(0)?, MAX_STACK_VARS)?;
        let mut point = Point::zero(ctx, dimension);
        for (i, slot) in point.coords[..MAX_STACK_VARS].iter_mut().enumerate() {
            *slot = ctx.public(2 + i)?;
        }
        let query: Vec<_> = (0..MAX_STACK_VARS)
            .map(|i| ctx.public(2 + MAX_STACK_VARS + i))
            .collect::<Result<_, _>>()?;
        let slices: Vec<_> = (0..K_BITS)
            .map(|i| ctx.public(2 + 2 * MAX_STACK_VARS + i))
            .collect::<Result<_, _>>()?;
        let mut transcript = Transcript::new(
            ctx,
            0,
            [ctx.base(0x0707_0707_0707_0707); 4],
            [ctx.base(0x0b0b_0b0b_0b0b_0b0b); 4],
        )?;
        let map = RingMap::sample(&mut transcript, ctx.public(1)?)?;
        let claim = map.switch(ctx, &point, &slices.try_into().map_err(|_| Error::InvalidInput)?)?;
        Ok([
            claim.target,
            claim.evaluate(ctx, &query)?,
            transcript.sample(ctx.one())?,
        ])
    }

    #[test]
    fn one_program_matches_production_ring_target_and_dense_weight() {
        let n_public = 2 + 2 * MAX_STACK_VARS + K_BITS;
        let symbolic = Symbolic::new(n_public);
        let output = program(&symbolic).unwrap();
        let circuit = symbolic.finish();
        let empty = riscv_proof::Proof {
            stream: vec![],
            merkle: vec![],
        };
        for dimension in 0..=3 {
            let point: Vec<_> = (0..dimension).map(|i| Field::new(17 + i as u64, 19, 23)).collect();
            let query: Vec<_> = (0..dimension).map(|i| Field::new(29 + i as u64, 31, 37)).collect();
            let words = [0, 1, 2, u64::MAX, 1 << 63, 0x0123_4567_89ab_cdef, 9, 17];
            let ctx = Witness::new(&[], vec![]);
            let equality = eq_kernel(&ctx, &point);
            let mut slices = [Field::ZERO; K_BITS];
            for (bit, slice) in slices.iter_mut().enumerate() {
                for (&word, &weight) in words.iter().zip(&equality) {
                    if word & (1u64 << bit) != 0 {
                        *slice += weight;
                    }
                }
            }
            let mut reference = riscv_proof::portable::transcript::Transcript::new(&empty, [7; 32], [11; 32]);
            let reference_claim = riscv_proof::portable::ring::RingMap::sample(&mut reference)
                .switch(&point, &slices)
                .unwrap();
            let mut challenges = riscv_proof::portable::transcript::Transcript::new(&empty, [7; 32], [11; 32]);
            let challenges: [Field; 6] = challenges.samples(6).try_into().unwrap();
            let dense: Vec<_> = equality.iter().map(|&value| phi(&ctx, value, &challenges)).collect();
            let packed: Vec<_> = words[..1 << dimension].iter().map(|&word| Field::from(word)).collect();
            let expected = [
                reference_claim.target,
                reference_claim.evaluate(&query),
                reference.sample(),
            ];
            assert_eq!(expected[0], dot(&ctx, &dense, &packed));
            assert_eq!(expected[1], mle_eval(&ctx, &dense, &query));
            let mut public = vec![Field::new(101, 103, 107); n_public];
            public[0] = Field::from(dimension as u64);
            public[1] = Field::ONE;
            public[2..2 + dimension].copy_from_slice(&point);
            public[2 + MAX_STACK_VARS..2 + MAX_STACK_VARS + dimension].copy_from_slice(&query);
            public[2 + 2 * MAX_STACK_VARS..].copy_from_slice(&slices);
            let witness = Witness::new(&public, vec![Source::Advice(&[])]);
            assert_eq!(program(&witness).unwrap(), expected);
            let private = witness.finish().unwrap();
            let values = circuit.evaluate(&public, &private).unwrap();
            assert_eq!(output.map(|wire| values[wire.index()]), expected);
            // All padding is deliberately nonzero and may change independently.
            public[2 + MAX_STACK_VARS + dimension..2 + 2 * MAX_STACK_VARS].fill(Field::new(109, 113, 127));
            let values = circuit.evaluate(&public, &private).unwrap();
            assert_eq!(output.map(|wire| values[wire.index()]), expected);
            // Corrupting a bound slice changes the target, not the weight.
            public[2 + 2 * MAX_STACK_VARS] += Field::ONE;
            let values = circuit.evaluate(&public, &private).unwrap();
            assert_ne!(values[output[0].index()], expected[0]);
            assert_eq!(values[output[1].index()], expected[1]);
        }
        let mut public = vec![Field::ZERO; n_public];
        public[0] = Field::from(28);
        let witness = Witness::new(&public, vec![Source::Advice(&[])]);
        let actual = program(&witness).unwrap();
        let mut reference = riscv_proof::portable::transcript::Transcript::new(&empty, [7; 32], [11; 32]);
        assert_eq!(actual[2], reference.sample());
        let values = circuit.evaluate(&public, &witness.finish().unwrap()).unwrap();
        assert_eq!(output.map(|wire| values[wire.index()]), actual);
        public[0] = Field::from(29);
        assert!(program(&Witness::new(&public, vec![Source::Advice(&[])])).is_err());
        assert!(circuit.evaluate(&public, &[]).is_err());
    }

    #[test]
    fn weight_rejects_a_query_shorter_than_its_claim_dimension() {
        let ctx = Witness::new(&[], vec![Source::Advice(&[])]);
        let mut transcript = Transcript::new(&ctx, 0, [Field::ZERO; 4], [Field::ZERO; 4]).unwrap();
        let map = RingMap::sample(&mut transcript, Field::ONE).unwrap();
        let point = Point::zero(&ctx, Dimension::constant(&ctx, 2));
        let claim = map.switch(&ctx, &point, &[Field::ZERO; K_BITS]).unwrap();
        assert!(claim.evaluate(&ctx, &[Field::ZERO]).is_err());
    }
}
