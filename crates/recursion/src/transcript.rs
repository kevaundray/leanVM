//! The native and symbolic verifier's identical, conditionally advancing transcript.

use crate::Error;
use crate::context::Context;
use crate::uint::Uint;

// These tags are the lanes specified by fiat_shamir::FiatShamirState. Nonces
// deliberately use their own ratchet, never the scalar/observe ratchet.
const DS_OBSERVE: u64 = 1;
const DS_SQUEEZE: u64 = 2;
const DS_POW_BASE: u64 = 3;
const DS_POW_NONCE: u64 = 4;

fn initial_state<C: Context>(ctx: &C) -> [C::F; 4] {
    let iv = primitives::hash::PARAM_IV;
    std::array::from_fn(|i| ctx.base(u64::from(iv[2 * i]) | (u64::from(iv[2 * i + 1]) << 32)))
}

fn block<C: Context>(
    ctx: &C,
    message: [C::F; 8],
    state: [C::F; 4],
    counter: C::F,
    last: C::F,
) -> Result<[C::F; 4], Error> {
    let mut input = [ctx.zero(); 14];
    input[..8].copy_from_slice(&message);
    input[8..12].copy_from_slice(&state);
    input[12] = counter;
    // The ABI packs f0 below f1; sequential BLAKE2s always has f1 = 0.
    input[13] = ctx.mul(last, ctx.base(u64::from(u32::MAX)));
    ctx.blake2s(input)
}

pub(crate) fn compress<C: Context>(ctx: &C, a: [C::F; 4], b: [C::F; 4]) -> Result<[C::F; 4], Error> {
    let message = [a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]];
    block(ctx, message, initial_state(ctx), ctx.base(64), ctx.one())
}

/// Hash a bounded prefix of LE u64 words, not the padded allocation's bytes.
/// Every potential block is present in the circuit, including the empty block.
pub(crate) fn hash_words<C: Context>(ctx: &C, words: &[C::F], word_count: C::F) -> Result<[C::F; 4], Error> {
    let maximum = u64::try_from(words.len()).map_err(|_| Error::Capacity)?;
    maximum.checked_mul(8).ok_or(Error::Capacity)?;
    let width = (u64::BITS - maximum.leading_zeros()) as usize;
    let count = Uint::from_field(ctx, word_count, width)?;
    let bound = Uint::constant(ctx, maximum, width);
    ctx.assert_zero(bound.lt(ctx, &count))?;

    // A three-bit polynomial shift is integer multiplication by eight here:
    // the constrained count is at most u64::MAX / 8, so no field reduction occurs.
    let total_bytes = ctx.mul(word_count, ctx.base(8));
    let mut state = initial_state(ctx);
    for index in 0..words.len().div_ceil(8).max(1) {
        let start = index * 8;
        let end = (start + 8).min(words.len());
        let active = if index == 0 {
            ctx.one()
        } else {
            Uint::constant(ctx, start as u64, width).lt(ctx, &count)
        };
        let last = if end == words.len() {
            ctx.one()
        } else {
            ctx.not(Uint::constant(ctx, end as u64, width).lt(ctx, &count))
        };
        let mut message = [ctx.zero(); 8];
        for i in start..end {
            let present = Uint::constant(ctx, i as u64, width).lt(ctx, &count);
            message[i - start] = ctx.mul(present, words[i]);
        }
        let counter = ctx.select(last, total_bytes, ctx.base(end as u64 * 8));
        let next = block(ctx, message, state, counter, last)?;
        state = std::array::from_fn(|i| ctx.select(active, next[i], state[i]));
    }
    Ok(state)
}

pub(crate) struct Transcript<'a, C: Context> {
    ctx: &'a C,
    source: usize,
    state: [C::F; 4],
}

impl<'a, C: Context> Transcript<'a, C> {
    pub(crate) fn new(ctx: &'a C, source: usize, iv: [C::F; 4], public_digest: [C::F; 4]) -> Result<Self, Error> {
        Ok(Self {
            ctx,
            source,
            state: compress(ctx, iv, public_digest)?,
        })
    }

    pub(crate) fn context(&self) -> &'a C {
        self.ctx
    }

    pub(crate) fn merkle(
        &self,
        enabled: C::F,
        leaf_words: C::F,
        depth: C::F,
        max_words: usize,
        max_depth: usize,
    ) -> Result<crate::context::Merkle<C::F>, Error> {
        self.ctx
            .read_merkle(self.source, enabled, leaf_words, depth, max_words, max_depth)
    }

    #[cfg(test)]
    pub(crate) fn state(&self) -> [C::F; 4] {
        self.state
    }

    fn scalar_block(&self, value: C::F, domain: u64) -> [C::F; 4] {
        [
            self.ctx.limb(value, 0),
            self.ctx.limb(value, 1),
            self.ctx.limb(value, 2),
            self.ctx.base(domain),
        ]
    }

    fn ratchet(&mut self, enabled: C::F, message: [C::F; 4]) -> Result<[C::F; 4], Error> {
        self.ctx.assert_bool(enabled)?;
        let next = compress(self.ctx, self.state, message)?;
        self.state = std::array::from_fn(|i| self.ctx.select(enabled, next[i], self.state[i]));
        Ok(next)
    }

    pub(crate) fn scalar(&mut self, enabled: C::F) -> Result<C::F, Error> {
        let value = self.ctx.read_scalar(self.source, enabled)?;
        self.ratchet(enabled, self.scalar_block(value, DS_OBSERVE))?;
        Ok(value)
    }

    pub(crate) fn root(&mut self, enabled: C::F) -> Result<[C::F; 4], Error> {
        let halves = [self.scalar(enabled)?, self.scalar(enabled)?];
        for half in halves {
            self.ctx.assert_zero(self.ctx.limb(half, 2))?;
        }
        Ok([
            self.ctx.limb(halves[0], 0),
            self.ctx.limb(halves[0], 1),
            self.ctx.limb(halves[1], 0),
            self.ctx.limb(halves[1], 1),
        ])
    }

    pub(crate) fn sample(&mut self, enabled: C::F) -> Result<C::F, Error> {
        let ctx = self.ctx;
        let next = self.ratchet(enabled, [ctx.zero(), ctx.zero(), ctx.zero(), ctx.base(DS_SQUEEZE)])?;
        Ok(ctx.mul(enabled, ctx.compose([next[0], next[1], next[2]])?))
    }

    pub(crate) fn sample_vec(&mut self, enabled: C::F, n: usize) -> Result<Vec<C::F>, Error> {
        self.ctx.assert_bool(enabled)?;
        (0..n).map(|_| self.sample(enabled)).collect()
    }

    pub(crate) fn round_poly(
        &mut self,
        enabled: C::F,
        n_coeffs: usize,
        claim: C::F,
        eq: Option<C::F>,
    ) -> Result<Vec<C::F>, Error> {
        if n_coeffs < 2 {
            return Err(Error::InvalidCircuit);
        }
        let fixed = usize::from(eq.is_none());
        let mut coefficients = vec![self.ctx.zero(); n_coeffs];
        let mut sum = self.ctx.zero();
        for (i, coefficient) in coefficients.iter_mut().enumerate() {
            if i != fixed {
                *coefficient = self.scalar(enabled)?;
            }
            if i > fixed {
                sum = self.ctx.add(sum, *coefficient);
            }
        }
        // Receiver::next_round_poly binds only transmitted coefficients in index
        // order. The derived coefficient is neither read nor absorbed.
        coefficients[fixed] = self.ctx.add(
            claim,
            match eq {
                None => sum,
                Some(weight) => self.ctx.mul(weight, sum),
            },
        );
        Ok(coefficients)
    }

    pub(crate) fn grind(&mut self, enabled: C::F, bits: C::F) -> Result<(), Error> {
        let ctx = self.ctx;
        ctx.assert_bool(enabled)?;
        let difficulty = Uint::from_field(ctx, bits, 6)?;
        // The raw read is intentional: this nonce binds exactly once under DS4.
        let nonce = ctx.read_scalar(self.source, enabled)?;
        let message = self.scalar_block(nonce, DS_POW_NONCE);
        let base = compress(
            ctx,
            self.state,
            [ctx.zero(), ctx.zero(), ctx.zero(), ctx.base(DS_POW_BASE)],
        )?;
        let digest = compress(ctx, base, message)?;
        let digest_bits = ctx.bits(digest[0], 64)?;
        ctx.assert_zero(ctx.mul(ctx.mul(enabled, difficulty.eq_const(ctx, 0)), nonce))?;
        for (i, &bit) in digest_bits.iter().take(63).enumerate() {
            let required = Uint::constant(ctx, i as u64, 6).lt(ctx, &difficulty);
            ctx.assert_zero(ctx.mul(ctx.mul(enabled, required), bit))?;
        }
        self.ratchet(enabled, message)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::{Source, Symbolic, Witness};
    use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
    use leanvm_guest::Field;
    use primitives::field::{F64, F192};

    fn field(value: F192) -> Field {
        Field::new(value.c0, value.c1, value.c2)
    }

    fn digest(hash: [u8; 32]) -> [Field; 4] {
        fiat_shamir::digest_words(&hash).map(|word| Field::from(word.0))
    }

    #[test]
    fn bounded_hash_matches_empty_partial_and_multiblock_blake() {
        let symbolic = Symbolic::new(18);
        let words: Vec<_> = (1..18).map(|i| symbolic.public(i).unwrap()).collect();
        let output = hash_words(&symbolic, &words, symbolic.public(0).unwrap()).unwrap();
        let circuit = symbolic.finish();
        let data: Vec<u64> = (0..17u64)
            .map(|i| i.wrapping_mul(0xfedc_ba98_7654_3210) ^ 0x0123_4567_89ab_cdef)
            .collect();
        for count in 0..=17 {
            let public: Vec<_> = std::iter::once(Field::from(count as u64))
                .chain(data.iter().copied().map(Field::from))
                .collect();
            let ctx = Witness::new(&public, Vec::new());
            let actual = hash_words(&ctx, &public[1..], public[0]).unwrap();
            let bytes: Vec<_> = data[..count].iter().flat_map(|word| word.to_le_bytes()).collect();
            let expected = digest(primitives::hash::hash(&bytes));
            assert_eq!(actual, expected);
            let values = circuit.evaluate(&public, &ctx.finish().unwrap()).unwrap();
            assert_eq!(output.map(|wire| values[wire.index()]), expected);
        }
        let ctx = Witness::new(&[], Vec::new());
        assert_eq!(
            hash_words(&ctx, &[], Field::ZERO).unwrap(),
            digest(primitives::hash::hash(&[]))
        );
        for invalid in [Field::from(18), Field::new(0, 1, 0)] {
            let mut public = vec![Field::ZERO; 18];
            public[0] = invalid;
            assert!(hash_words(&ctx, &public[1..], invalid).is_err());
            assert!(circuit.evaluate(&public, &[]).is_err());
        }
        let mut public = vec![Field::ZERO; 18];
        public[0] = Field::ONE;
        public[1] = Field::new(0, 1, 0);
        assert!(hash_words(&ctx, &public[1..], public[0]).is_err());
        assert!(circuit.evaluate(&public, &[]).is_err());
    }

    fn replay<C: Context>(ctx: &C, plain_claim: Field, eq_claim: Field, weight: Field) -> Result<Vec<C::F>, Error> {
        let one = ctx.one();
        let mut transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        let mut out = vec![transcript.scalar(one)?, transcript.sample(one)?];
        out.extend(transcript.root(one)?);
        out.extend(transcript.sample_vec(one, 2)?);
        out.extend(transcript.round_poly(one, 3, ctx.constant(plain_claim), None)?);
        out.push(transcript.sample(one)?);
        out.extend(transcript.round_poly(one, 3, ctx.constant(eq_claim), Some(ctx.constant(weight)))?);
        out.push(transcript.sample(one)?);
        transcript.grind(one, ctx.zero())?;
        out.push(transcript.sample(one)?);
        transcript.grind(one, ctx.base(2))?;
        out.push(transcript.sample(one)?);
        Ok(out)
    }

    #[test]
    fn transcript_matches_native_and_portable_transports() {
        let scalar = F192::new(7, 8, 9);
        let root = primitives::hash::hash(b"native transcript root");
        let coefficients = [F192::new(10, 11, 12), F192::new(13, 14, 15), F192::new(16, 17, 18)];
        let weight = F192::new(2, 3, 4);
        let plain_claim = coefficients[1] + coefficients[2];
        let eq_claim = coefficients[0] + weight * plain_claim;
        let mut prover = ProverState::new([F64::ZERO; 4], [F64::ZERO; 4]);
        prover.add_scalar(scalar);
        let mut expected = vec![field(scalar), field(prover.sample())];
        prover.add_root(&root);
        expected.extend(digest(root));
        expected.extend(prover.sample_vec(2).into_iter().map(field));
        prover.add_round_poly(&coefficients, false);
        expected.extend(coefficients.map(field));
        expected.push(field(prover.sample()));
        prover.add_round_poly(&coefficients, true);
        expected.extend(coefficients.map(field));
        expected.push(field(prover.sample()));
        prover.grind(0);
        expected.push(field(prover.sample()));
        prover.grind(2);
        expected.push(field(prover.sample()));
        let proof = prover.into_proof();
        let raw = fiat_shamir::transcript::RawProof {
            stream: proof.stream.clone(),
            merkle: Vec::new(),
        };
        let ctx = Witness::new(&[], vec![Source::Native(&raw)]);
        let actual = replay(&ctx, field(plain_claim), field(eq_claim), field(weight)).unwrap();
        assert_eq!(actual, expected);
        let private = ctx.finish().unwrap();
        let symbolic = Symbolic::new(0);
        let output = replay(&symbolic, field(plain_claim), field(eq_claim), field(weight)).unwrap();
        let values = symbolic.finish().evaluate(&[], &private).unwrap();
        assert_eq!(
            output.iter().map(|wire| values[wire.index()]).collect::<Vec<_>>(),
            expected
        );

        let portable_proof = riscv_proof::Proof {
            stream: proof.stream.iter().copied().map(field).collect(),
            merkle: Vec::new(),
        };
        let mut portable = riscv_proof::portable::transcript::Transcript::new(&portable_proof, [0; 32], [0; 32]);
        let mut portable_out = vec![portable.next_scalar().unwrap(), portable.sample()];
        portable_out.extend(digest(portable.next_root().unwrap()));
        portable_out.extend(portable.samples(2));
        portable_out.extend(portable.sumcheck_round_poly(3, field(plain_claim), None).unwrap());
        portable_out.push(portable.sample());
        portable_out.extend(
            portable
                .sumcheck_round_poly(3, field(eq_claim), Some(field(weight)))
                .unwrap(),
        );
        portable_out.push(portable.sample());
        portable.grind_check(0).unwrap();
        portable_out.push(portable.sample());
        portable.grind_check(2).unwrap();
        portable_out.push(portable.sample());
        portable.finish().unwrap();
        assert_eq!(portable_out, expected);
    }

    #[test]
    fn grinding_accepts_full_field_nonces_but_constrains_zero_work_and_difficulty() {
        let symbolic = Symbolic::new(1);
        let mut transcript = Transcript::new(&symbolic, 0, [symbolic.zero(); 4], [symbolic.zero(); 4]).unwrap();
        transcript.grind(symbolic.one(), symbolic.public(0).unwrap()).unwrap();
        let output = transcript.sample(symbolic.one()).unwrap();
        let circuit = symbolic.finish();
        let nonce = F192::new(0, 1, 1);
        let proof = fiat_shamir::transcript::Proof {
            stream: vec![nonce],
            merkle: Vec::new(),
        };
        let mut reference = VerifierState::new([F64::ZERO; 4], &proof, [F64::ZERO; 4]);
        reference.grind_check(2).unwrap();
        let expected = field(reference.sample());
        let raw = fiat_shamir::transcript::RawProof {
            stream: vec![nonce],
            merkle: Vec::new(),
        };
        let ctx = Witness::new(&[], vec![Source::Native(&raw)]);
        let mut transcript = Transcript::new(&ctx, 0, [Field::ZERO; 4], [Field::ZERO; 4]).unwrap();
        transcript.grind(Field::ONE, Field::from(2)).unwrap();
        assert_eq!(transcript.sample(Field::ONE).unwrap(), expected);
        let private = ctx.finish().unwrap();
        let values = circuit.evaluate(&[Field::from(2)], &private).unwrap();
        assert_eq!(values[output.index()], expected);
        assert!(circuit.evaluate(&[Field::ZERO], &private).is_err());
        assert!(circuit.evaluate(&[Field::from(64)], &private).is_err());
        // Raising the difficulty past this nonce's zero window must reject.
        let base = fiat_shamir::compress(
            fiat_shamir::compress([F64::ZERO; 4], [F64::ZERO; 4]),
            [F64::ZERO, F64::ZERO, F64::ZERO, F64(3)],
        );
        let low = fiat_shamir::compress(base, [F64(0), F64(1), F64(1), F64(4)])[0].0;
        let failing_bits = low.trailing_zeros() + 1;
        assert!(failing_bits < 64);
        assert!(
            circuit
                .evaluate(&[Field::from(u64::from(failing_bits))], &private)
                .is_err()
        );
    }

    #[test]
    fn roots_constrain_both_spare_limbs() {
        let symbolic = Symbolic::new(0);
        let mut transcript = Transcript::new(&symbolic, 0, [symbolic.zero(); 4], [symbolic.zero(); 4]).unwrap();
        transcript.root(symbolic.one()).unwrap();
        let circuit = symbolic.finish();
        for half in 0..2 {
            let mut stream = vec![Field::ZERO; 2];
            stream[half] = Field::new(0, 0, 1);
            assert!(circuit.evaluate(&[], &stream).is_err());
            let ctx = Witness::new(&[], vec![Source::Advice(&stream)]);
            let mut transcript = Transcript::new(&ctx, 0, [Field::ZERO; 4], [Field::ZERO; 4]).unwrap();
            assert!(transcript.root(Field::ONE).is_err());
        }
    }

    fn conditional<C: Context>(ctx: &C) -> Result<C::F, Error> {
        let enabled = ctx.public(0)?;
        let mut transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        let before = transcript.state();
        let scalar = transcript.scalar(enabled)?;
        let root = transcript.root(enabled)?;
        let challenges = transcript.sample_vec(enabled, 2)?;
        let coefficients = transcript.round_poly(enabled, 3, ctx.base(27), None)?;
        transcript.grind(enabled, ctx.zero())?;
        let disabled = ctx.not(enabled);
        for value in [
            scalar,
            root[0],
            root[1],
            root[2],
            root[3],
            challenges[0],
            challenges[1],
            coefficients[0],
            coefficients[2],
        ] {
            ctx.assert_zero(ctx.mul(disabled, value))?;
        }
        ctx.assert_equal_if(disabled, coefficients[1], ctx.base(27))?;
        for (old, new) in before.into_iter().zip(transcript.state()) {
            ctx.assert_equal_if(disabled, old, new)?;
        }
        transcript.scalar(ctx.one())?;
        transcript.sample(ctx.one())
    }

    #[test]
    fn inactive_paths_preserve_state_and_do_not_consume_source() {
        let public = [Field::ZERO];
        let scalar = F192::new(7, 8, 9);
        let raw = fiat_shamir::transcript::RawProof {
            stream: vec![scalar],
            merkle: Vec::new(),
        };
        let ctx = Witness::new(&public, vec![Source::Native(&raw)]);
        let actual = conditional(&ctx).unwrap();
        let private = ctx.finish().unwrap();
        let mut reference = fiat_shamir::FiatShamirState::new([F64::ZERO; 4], [F64::ZERO; 4]);
        reference.observe(scalar);
        let expected = field(reference.sample());
        assert_eq!(actual, expected);
        let symbolic = Symbolic::new(1);
        let output = conditional(&symbolic).unwrap();
        let circuit = symbolic.finish();
        let values = circuit.evaluate(&public, &private).unwrap();
        assert_eq!(values[output.index()], expected);
        // Even adversarial private data in inactive slots cannot change state.
        let mut adversarial = private;
        let last = adversarial.len() - 1;
        adversarial[..last].fill(Field::new(u64::MAX, u64::MAX, u64::MAX));
        let values = circuit.evaluate(&public, &adversarial).unwrap();
        assert_eq!(values[output.index()], expected);
        assert!(circuit.evaluate(&[Field::from(2)], &adversarial).is_err());

        // The very same circuit also executes the enabled branch against its
        // longer scalar stream; enable values never choose a circuit shape.
        let proof = fiat_shamir::transcript::Proof {
            stream: vec![
                scalar,
                F192::new(1, 2, 0),
                F192::new(3, 4, 0),
                scalar,
                scalar,
                F192::ZERO,
                scalar,
            ],
            merkle: Vec::new(),
        };
        let mut reference = VerifierState::new([F64::ZERO; 4], &proof, [F64::ZERO; 4]);
        reference.next_scalar().unwrap();
        reference.next_root().unwrap();
        reference.sample_vec(2);
        reference.next_round_poly(3, F192::new(27, 0, 0), None).unwrap();
        reference.grind_check(0).unwrap();
        reference.next_scalar().unwrap();
        let expected = field(reference.sample());
        reference.finish().unwrap();
        let raw = fiat_shamir::transcript::RawProof {
            stream: proof.stream,
            merkle: Vec::new(),
        };
        let public = [Field::ONE];
        let ctx = Witness::new(&public, vec![Source::Native(&raw)]);
        assert_eq!(conditional(&ctx).unwrap(), expected);
        let values = circuit.evaluate(&public, &ctx.finish().unwrap()).unwrap();
        assert_eq!(values[output.index()], expected);
    }
}
