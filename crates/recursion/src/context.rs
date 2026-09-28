//! One verifier program, compiled into constraints or run to collect its advice.

use std::cell::RefCell;

use crate::{Builder, Circuit, Error, Wire};
use leanvm_guest::Field;

pub(crate) struct Merkle<F> {
    pub leaf: Vec<F>,
    pub siblings: Vec<[F; 4]>,
}

pub(crate) trait Context {
    type F: Copy;

    fn constant(&self, value: Field) -> Self::F;
    fn add(&self, lhs: Self::F, rhs: Self::F) -> Self::F;
    fn mul(&self, lhs: Self::F, rhs: Self::F) -> Self::F;
    fn inverse(&self, value: Self::F) -> Result<Self::F, Error>;
    fn limb(&self, value: Self::F, limb: u8) -> Self::F;
    fn compose(&self, limbs: [Self::F; 3]) -> Result<Self::F, Error>;
    fn bits(&self, value: Self::F, width: usize) -> Result<Vec<Self::F>, Error>;
    fn assert_zero(&self, value: Self::F) -> Result<(), Error>;
    fn assert_bool(&self, value: Self::F) -> Result<(), Error>;
    fn blake2s(&self, input: [Self::F; 14]) -> Result<[Self::F; 4], Error>;
    fn public(&self, index: usize) -> Result<Self::F, Error>;
    fn read_scalar(&self, source: usize, enabled: Self::F) -> Result<Self::F, Error>;
    fn read_merkle(
        &self,
        source: usize,
        enabled: Self::F,
        leaf_words: Self::F,
        depth: Self::F,
        max_words: usize,
        max_depth: usize,
    ) -> Result<Merkle<Self::F>, Error>;

    fn zero(&self) -> Self::F {
        self.constant(Field::ZERO)
    }
    fn one(&self) -> Self::F {
        self.constant(Field::ONE)
    }
    fn base(&self, value: u64) -> Self::F {
        self.constant(Field::from(value))
    }
    fn not(&self, value: Self::F) -> Self::F {
        self.add(self.one(), value)
    }
    fn or(&self, lhs: Self::F, rhs: Self::F) -> Self::F {
        self.add(self.add(lhs, rhs), self.mul(lhs, rhs))
    }
    fn select(&self, enabled: Self::F, yes: Self::F, no: Self::F) -> Self::F {
        self.add(no, self.mul(enabled, self.add(yes, no)))
    }
    fn assert_equal(&self, lhs: Self::F, rhs: Self::F) -> Result<(), Error> {
        self.assert_zero(self.add(lhs, rhs))
    }
    fn assert_equal_if(&self, enabled: Self::F, lhs: Self::F, rhs: Self::F) -> Result<(), Error> {
        self.assert_zero(self.mul(enabled, self.add(lhs, rhs)))
    }
}

/// Checks an integer bound without consulting the represented value.
fn bounded<C: Context>(ctx: &C, value: C::F, maximum: usize) -> Result<Vec<C::F>, Error> {
    let width = (usize::BITS - maximum.leading_zeros()) as usize;
    let bits = ctx.bits(value, width)?;
    let mut equal = ctx.one();
    let mut greater = ctx.zero();
    for bit in (0..width).rev() {
        if (maximum >> bit) & 1 == 0 {
            greater = ctx.or(greater, ctx.mul(equal, bits[bit]));
            equal = ctx.mul(equal, ctx.not(bits[bit]));
        } else {
            equal = ctx.mul(equal, bits[bit]);
        }
    }
    ctx.assert_zero(greater)?;
    Ok(bits)
}

fn merkle_dimensions<C: Context>(
    ctx: &C,
    enabled: C::F,
    leaf_words: C::F,
    depth: C::F,
    max_words: usize,
    max_depth: usize,
) -> Result<(), Error> {
    ctx.assert_bool(enabled)?;
    let leaf_bits = bounded(ctx, leaf_words, max_words)?;
    bounded(ctx, depth, max_depth)?;
    let mut empty = ctx.one();
    for bit in leaf_bits {
        empty = ctx.mul(empty, ctx.not(bit));
    }
    ctx.assert_zero(ctx.mul(enabled, empty))
}

pub(crate) struct Symbolic {
    builder: Builder,
    public: Vec<Wire>,
}

impl Symbolic {
    pub(crate) fn new(public_count: usize) -> Self {
        let builder = Builder::new();
        let public = (0..public_count).map(|_| builder.input(true)).collect();
        Self { builder, public }
    }

    pub(crate) fn finish(self) -> Circuit {
        self.builder.finish()
    }
}

impl Context for Symbolic {
    type F = Wire;

    fn constant(&self, value: Field) -> Wire {
        self.builder.constant(value)
    }
    fn add(&self, lhs: Wire, rhs: Wire) -> Wire {
        self.builder.add(lhs, rhs)
    }
    fn mul(&self, lhs: Wire, rhs: Wire) -> Wire {
        self.builder.mul(lhs, rhs)
    }
    fn inverse(&self, value: Wire) -> Result<Wire, Error> {
        Ok(self.builder.inverse(value))
    }
    fn limb(&self, value: Wire, limb: u8) -> Wire {
        self.builder.limb(value, limb)
    }
    fn compose(&self, limbs: [Wire; 3]) -> Result<Wire, Error> {
        Ok(self.builder.compose(limbs))
    }

    fn bits(&self, value: Wire, width: usize) -> Result<Vec<Wire>, Error> {
        if width > 192 {
            return Err(Error::InvalidCircuit);
        }
        Ok(self.builder.bits(value, width))
    }

    fn assert_zero(&self, value: Wire) -> Result<(), Error> {
        self.builder.assert_equal(value, self.zero());
        Ok(())
    }

    fn assert_bool(&self, value: Wire) -> Result<(), Error> {
        self.builder.assert_bool(value);
        Ok(())
    }

    fn blake2s(&self, input: [Wire; 14]) -> Result<[Wire; 4], Error> {
        Ok(self.builder.blake2s(input))
    }

    fn public(&self, index: usize) -> Result<Wire, Error> {
        self.public.get(index).copied().ok_or(Error::InvalidInput)
    }

    fn read_scalar(&self, _source: usize, enabled: Wire) -> Result<Wire, Error> {
        self.assert_bool(enabled)?;
        Ok(self.mul(enabled, self.builder.input(false)))
    }

    fn read_merkle(
        &self,
        _source: usize,
        enabled: Wire,
        leaf_words: Wire,
        depth: Wire,
        max_words: usize,
        max_depth: usize,
    ) -> Result<Merkle<Wire>, Error> {
        merkle_dimensions(self, enabled, leaf_words, depth, max_words, max_depth)?;
        let leaf = (0..max_words)
            .map(|_| self.mul(enabled, self.builder.input(false)))
            .collect();
        let siblings = (0..max_depth)
            .map(|_| std::array::from_fn(|_| self.mul(enabled, self.builder.input(false))))
            .collect();
        Ok(Merkle { leaf, siblings })
    }
}

pub(crate) enum Source<'a> {
    Native(&'a fiat_shamir::transcript::RawProof),
    Risc(&'a riscv_proof::Proof),
    Advice(&'a [Field]),
}

struct SourceState<'a> {
    source: Source<'a>,
    scalar: usize,
    merkle: usize,
}

impl SourceState<'_> {
    fn next_scalar(&mut self) -> Result<Field, Error> {
        let value = match &self.source {
            Source::Native(proof) => proof
                .stream
                .get(self.scalar)
                .map(|value| Field([value.c0, value.c1, value.c2])),
            Source::Risc(proof) => proof.stream.get(self.scalar).copied(),
            Source::Advice(values) => values.get(self.scalar).copied(),
        }
        .ok_or(Error::InvalidInput)?;
        self.scalar += 1;
        Ok(value)
    }

    fn exhausted(&self) -> bool {
        let (scalars, merkle) = match &self.source {
            Source::Native(proof) => (proof.stream.len(), proof.merkle.len()),
            Source::Risc(proof) => (proof.stream.len(), proof.merkle.len()),
            Source::Advice(values) => (values.len(), 0),
        };
        self.scalar == scalars && self.merkle == merkle
    }
}

pub(crate) struct Witness<'a> {
    public: &'a [Field],
    sources: RefCell<Vec<SourceState<'a>>>,
    private: RefCell<Vec<Field>>,
}

impl<'a> Witness<'a> {
    pub(crate) fn new(public: &'a [Field], sources: Vec<Source<'a>>) -> Self {
        Self {
            public,
            sources: RefCell::new(
                sources
                    .into_iter()
                    .map(|source| SourceState {
                        source,
                        scalar: 0,
                        merkle: 0,
                    })
                    .collect(),
            ),
            private: RefCell::new(Vec::new()),
        }
    }

    pub(crate) fn finish(self) -> Result<Vec<Field>, Error> {
        if !self.sources.into_inner().iter().all(SourceState::exhausted) {
            return Err(Error::InvalidInput);
        }
        Ok(self.private.into_inner())
    }
}

fn base_word(value: Field) -> Result<u64, Error> {
    if value.0[1] != 0 || value.0[2] != 0 {
        return Err(Error::InvalidWitness);
    }
    Ok(value.0[0])
}

fn hash_words(hash: &[u8; 32]) -> [Field; 4] {
    std::array::from_fn(|i| Field::from(u64::from_le_bytes(hash[8 * i..8 * i + 8].try_into().unwrap())))
}

impl Context for Witness<'_> {
    type F = Field;

    fn constant(&self, value: Field) -> Field {
        value
    }
    fn add(&self, lhs: Field, rhs: Field) -> Field {
        lhs + rhs
    }
    fn mul(&self, lhs: Field, rhs: Field) -> Field {
        lhs * rhs
    }
    fn inverse(&self, value: Field) -> Result<Field, Error> {
        value.inverse().ok_or(Error::InvalidWitness)
    }

    fn limb(&self, value: Field, limb: u8) -> Field {
        assert!(limb < 3, "field limb index must be below three");
        Field::from(value.0[limb as usize])
    }

    fn compose(&self, limbs: [Field; 3]) -> Result<Field, Error> {
        let [a, b, c] = limbs.map(base_word);
        Ok(Field([a?, b?, c?]))
    }

    fn bits(&self, value: Field, width: usize) -> Result<Vec<Field>, Error> {
        if width > 192 {
            return Err(Error::InvalidCircuit);
        }
        for bit in width..192 {
            if (value.0[bit / 64] >> (bit % 64)) & 1 != 0 {
                return Err(Error::InvalidWitness);
            }
        }
        Ok((0..width)
            .map(|bit| Field::from((value.0[bit / 64] >> (bit % 64)) & 1))
            .collect())
    }

    fn assert_zero(&self, value: Field) -> Result<(), Error> {
        if value == Field::ZERO {
            Ok(())
        } else {
            Err(Error::InvalidWitness)
        }
    }

    fn assert_bool(&self, value: Field) -> Result<(), Error> {
        if value == Field::ZERO || value == Field::ONE {
            Ok(())
        } else {
            Err(Error::InvalidWitness)
        }
    }

    fn blake2s(&self, input: [Field; 14]) -> Result<[Field; 4], Error> {
        let mut words = [0u64; 14];
        for (word, value) in words.iter_mut().zip(input) {
            *word = base_word(value)?;
        }
        let mut message = [0u8; 64];
        for (bytes, word) in message.chunks_exact_mut(8).zip(&words[..8]) {
            bytes.copy_from_slice(&word.to_le_bytes());
        }
        let mut chaining = std::array::from_fn(|i| (words[8 + i / 2] >> (32 * (i % 2))) as u32);
        leanvm_guest::blake2s_compress(
            &mut chaining,
            &message,
            words[12],
            words[13] as u32,
            (words[13] >> 32) as u32,
        );
        Ok(std::array::from_fn(|i| {
            Field::from(u64::from(chaining[2 * i]) | (u64::from(chaining[2 * i + 1]) << 32))
        }))
    }

    fn public(&self, index: usize) -> Result<Field, Error> {
        self.public.get(index).copied().ok_or(Error::InvalidInput)
    }

    fn read_scalar(&self, source: usize, enabled: Field) -> Result<Field, Error> {
        self.assert_bool(enabled)?;
        let value = if enabled == Field::ZERO {
            Field::ZERO
        } else {
            self.sources
                .borrow_mut()
                .get_mut(source)
                .ok_or(Error::InvalidInput)?
                .next_scalar()?
        };
        self.private.borrow_mut().push(value);
        Ok(value)
    }

    fn read_merkle(
        &self,
        source: usize,
        enabled: Field,
        leaf_words: Field,
        depth: Field,
        max_words: usize,
        max_depth: usize,
    ) -> Result<Merkle<Field>, Error> {
        merkle_dimensions(self, enabled, leaf_words, depth, max_words, max_depth)?;
        let mut result = Merkle {
            leaf: vec![Field::ZERO; max_words],
            siblings: vec![[Field::ZERO; 4]; max_depth],
        };
        if enabled == Field::ONE {
            // The generic dimension checks above constrain these conversions.
            let words = leaf_words.0[0] as usize;
            let depth = depth.0[0] as usize;
            let mut sources = self.sources.borrow_mut();
            let state = sources.get_mut(source).ok_or(Error::InvalidInput)?;
            match &state.source {
                Source::Native(proof) => {
                    let path = proof.merkle.get(state.merkle).ok_or(Error::InvalidInput)?;
                    if path.leaf_data.len() != words || path.path.len() != depth {
                        return Err(Error::InvalidInput);
                    }
                    for (slot, word) in result.leaf.iter_mut().zip(&path.leaf_data) {
                        *slot = Field::from(word.0);
                    }
                    for (slot, hash) in result.siblings.iter_mut().zip(&path.path) {
                        *slot = hash_words(hash);
                    }
                }
                Source::Risc(proof) => {
                    let path = proof.merkle.get(state.merkle).ok_or(Error::InvalidInput)?;
                    if path.leaf.len() != words || path.siblings.len() != depth {
                        return Err(Error::InvalidInput);
                    }
                    for (slot, &word) in result.leaf.iter_mut().zip(&path.leaf) {
                        *slot = Field::from(word);
                    }
                    for (slot, hash) in result.siblings.iter_mut().zip(&path.siblings) {
                        *slot = hash_words(hash);
                    }
                }
                Source::Advice(_) => return Err(Error::InvalidInput),
            }
            state.merkle += 1;
        }
        let mut private = self.private.borrow_mut();
        private.extend_from_slice(&result.leaf);
        for sibling in &result.siblings {
            private.extend_from_slice(sibling);
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::merkle::RawMerklePath;
    use fiat_shamir::transcript::RawProof;
    use primitives::field::{F64, F192};

    fn conditional_reads<C: Context>(ctx: &C) -> Result<(), Error> {
        let inactive = ctx.public(0)?;
        ctx.assert_zero(ctx.read_scalar(0, inactive)?)?;
        let skipped = ctx.read_merkle(0, inactive, ctx.zero(), ctx.zero(), 2, 1)?;
        for value in skipped.leaf.into_iter().chain(skipped.siblings.into_iter().flatten()) {
            ctx.assert_zero(value)?;
        }
        ctx.assert_equal(ctx.read_scalar(0, ctx.one())?, ctx.base(17))?;
        let opening = ctx.read_merkle(0, ctx.one(), ctx.one(), ctx.one(), 2, 1)?;
        ctx.assert_equal(opening.leaf[0], ctx.base(23))?;
        ctx.assert_zero(opening.leaf[1])?;
        for word in opening.siblings[0] {
            ctx.assert_equal(word, ctx.base(0x0807_0605_0403_0201))?;
        }
        ctx.assert_equal(ctx.read_scalar(0, ctx.one())?, ctx.base(29))
    }

    #[test]
    fn inactive_reads_preserve_cursors_and_mask_all_private_slots() {
        let hash = std::array::from_fn(|i| (i % 8 + 1) as u8);
        let risc = riscv_proof::Proof {
            stream: vec![Field::from(17), Field::from(29)],
            merkle: vec![riscv_proof::Opening {
                leaf: vec![23],
                siblings: vec![hash],
            }],
        };
        let native = RawProof {
            stream: vec![F192::from(F64(17)), F192::from(F64(29))],
            merkle: vec![RawMerklePath {
                leaf_index: 0,
                leaf_data: vec![F64(23)],
                path: vec![hash],
            }],
        };
        let public = [Field::ZERO];
        let symbolic = Symbolic::new(public.len());
        conditional_reads(&symbolic).unwrap();
        let circuit = symbolic.finish();
        for source in [Source::Risc(&risc), Source::Native(&native)] {
            let witness = Witness::new(&public, vec![source]);
            conditional_reads(&witness).unwrap();
            let mut private = witness.finish().unwrap();
            let mut expected = vec![Field::ZERO; 7];
            expected.extend([Field::from(17), Field::from(23), Field::ZERO]);
            expected.extend([Field::from(0x0807_0605_0403_0201); 4]);
            expected.push(Field::from(29));
            assert_eq!(private, expected);
            circuit.evaluate(&public, &private).unwrap();
            // A malicious prover may fill inactive advice arbitrarily, but
            // cannot make any of those values visible to the verifier.
            private[..7].fill(Field([7, 11, 13]));
            circuit.evaluate(&public, &private).unwrap();
        }
    }

    #[test]
    fn sources_reject_truncation_and_trailing_data() {
        let native = RawProof {
            stream: vec![],
            merkle: vec![],
        };
        let risc = riscv_proof::Proof {
            stream: vec![],
            merkle: vec![],
        };
        for source in [Source::Native(&native), Source::Risc(&risc), Source::Advice(&[])] {
            let witness = Witness::new(&[], vec![source]);
            assert_eq!(witness.read_scalar(0, Field::ONE), Err(Error::InvalidInput));
            assert!(matches!(
                witness.read_merkle(0, Field::ONE, Field::ONE, Field::ZERO, 1, 0),
                Err(Error::InvalidInput)
            ));
        }
        let advice = [Field::ONE, Field::from(2)];
        let witness = Witness::new(&[], vec![Source::Advice(&advice)]);
        assert_eq!(witness.read_scalar(0, Field::ONE).unwrap(), Field::ONE);
        assert_eq!(witness.finish(), Err(Error::InvalidInput));
        let native = RawProof {
            stream: vec![],
            merkle: vec![RawMerklePath {
                leaf_index: 0,
                leaf_data: vec![F64(1)],
                path: vec![],
            }],
        };
        let risc = riscv_proof::Proof {
            stream: vec![],
            merkle: vec![riscv_proof::Opening {
                leaf: vec![1],
                siblings: vec![],
            }],
        };
        for source in [Source::Native(&native), Source::Risc(&risc)] {
            let witness = Witness::new(&[], vec![source]);
            witness
                .read_merkle(0, Field::ZERO, Field::ZERO, Field::ZERO, 1, 0)
                .unwrap();
            assert_eq!(witness.finish(), Err(Error::InvalidInput));
        }
    }

    #[test]
    fn opening_lengths_must_match_constrained_dimensions() {
        let native = RawProof {
            stream: vec![],
            merkle: vec![RawMerklePath {
                leaf_index: 0,
                leaf_data: vec![F64(1)],
                path: vec![],
            }],
        };
        let risc = riscv_proof::Proof {
            stream: vec![],
            merkle: vec![riscv_proof::Opening {
                leaf: vec![1],
                siblings: vec![],
            }],
        };
        for source in [Source::Native(&native), Source::Risc(&risc)] {
            let witness = Witness::new(&[], vec![source]);
            for (words, depth) in [(2, 0), (1, 1)] {
                assert!(matches!(
                    witness.read_merkle(0, Field::ONE, Field::from(words), Field::from(depth), 2, 1),
                    Err(Error::InvalidInput)
                ));
            }
        }
    }

    #[test]
    fn malformed_enables_and_dimensions_are_rejected_in_both_modes() {
        let symbolic = Symbolic::new(3);
        symbolic
            .read_merkle(
                0,
                symbolic.public(0).unwrap(),
                symbolic.public(1).unwrap(),
                symbolic.public(2).unwrap(),
                5,
                2,
            )
            .unwrap();
        let circuit = symbolic.finish();
        for [enabled, words, depth] in [
            [Field::from(2), Field::ONE, Field::ZERO],
            [Field([0, 1, 0]), Field::ONE, Field::ZERO],
            [Field::ONE, Field::ZERO, Field::ZERO],
            [Field::ZERO, Field::from(6), Field::ZERO],
            [Field::ZERO, Field::ONE, Field::from(3)],
            [Field::ZERO, Field([1, 1, 0]), Field::ZERO],
        ] {
            let public = [enabled, words, depth];
            let witness = Witness::new(&public, vec![]);
            assert!(matches!(
                witness.read_merkle(0, enabled, words, depth, 5, 2),
                Err(Error::InvalidWitness)
            ));
            assert_eq!(
                circuit.evaluate(&public, &[Field::ZERO; 13]),
                Err(Error::InvalidWitness)
            );
        }
        let symbolic = Symbolic::new(1);
        symbolic.read_scalar(0, symbolic.public(0).unwrap()).unwrap();
        let circuit = symbolic.finish();
        let witness = Witness::new(&[], vec![]);
        assert_eq!(witness.read_scalar(0, Field::from(2)), Err(Error::InvalidWitness));
        assert_eq!(
            circuit.evaluate(&[Field::from(2)], &[Field::ZERO]),
            Err(Error::InvalidWitness)
        );
    }

    #[test]
    fn bounded_decomposition_rejects_every_excluded_limb() {
        for width in [0, 1, 63, 64, 65, 128, 191, 192] {
            let symbolic = Symbolic::new(1);
            symbolic.bits(symbolic.public(0).unwrap(), width).unwrap();
            let circuit = symbolic.finish();
            let witness = Witness::new(&[], vec![]);
            let mut maximum = Field::ZERO;
            for bit in 0..width {
                maximum.0[bit / 64] |= 1u64 << (bit % 64);
            }
            assert_eq!(witness.bits(maximum, width).unwrap(), vec![Field::ONE; width]);
            circuit.evaluate(&[maximum], &[]).unwrap();
            for bit in width..192 {
                let mut outside = Field::ZERO;
                outside.0[bit / 64] = 1u64 << (bit % 64);
                assert_eq!(witness.bits(outside, width), Err(Error::InvalidWitness));
                assert_eq!(circuit.evaluate(&[outside], &[]), Err(Error::InvalidWitness));
            }
        }
    }

    #[test]
    fn compose_rejects_nonbase_inputs_in_both_modes() {
        let invalid = Field([3, 1, 0]);
        let symbolic = Symbolic::new(1);
        symbolic
            .compose([symbolic.public(0).unwrap(), symbolic.zero(), symbolic.zero()])
            .unwrap();
        assert_eq!(symbolic.finish().evaluate(&[invalid], &[]), Err(Error::InvalidWitness));
        let witness = Witness::new(&[], vec![]);
        assert_eq!(
            witness.compose([invalid, Field::ZERO, Field::ZERO]),
            Err(Error::InvalidWitness)
        );
    }
}
