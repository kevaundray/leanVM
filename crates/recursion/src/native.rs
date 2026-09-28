use crate::{
    Error, air, algebra,
    context::Context,
    flock_verifier, gkr,
    proof::{FIXED_LOG_INV_RATE, KEY_DOMAIN, KEY_HEADER_WORDS, KEY_TABLE_WORDS, KEY_WORDS},
    protocol::{DIM_BITS, Dimension, MAX_STACK_VARS, Point},
    stacked::{self, PointClaim, RingOpening},
    tables::{self, NativeTable, TableKind},
    transcript::{Transcript, hash_words},
    uint::Uint,
};
use leanvm_guest::deferred::PUBLIC_DOMAIN;
use riscv_proof::schema::PublicSource;

pub(crate) fn digest_words<C: Context>(ctx: &C, digest: [u8; 32]) -> [C::F; 4] {
    std::array::from_fn(|index| ctx.base(u64::from_le_bytes(digest[8 * index..8 * index + 8].try_into().unwrap())))
}

pub(crate) fn public_digest<C: Context>(ctx: &C, public: &[C::F]) -> Result<[C::F; 4], Error> {
    let mut words = Vec::with_capacity(5 + 3 * public.len());
    words.extend(digest_words(ctx, primitives::hash::hash(PUBLIC_DOMAIN)));
    words.push(ctx.base(public.len() as u64));
    for &value in public {
        words.extend((0..3).map(|limb| ctx.limb(value, limb)));
    }
    hash_words(ctx, &words, ctx.base(words.len() as u64))
}

struct TableInfo<F: Copy> {
    present: F,
    dim: Dimension<F>,
    fixed: Uint<F>,
    private: Uint<F>,
    bus: Uint<F>,
}

pub(crate) struct KeyInfo<F: Copy> {
    digest: [F; 4],
    public_count: usize,
    fixed_dim: Dimension<F>,
    fixed_lanes: Uint<F>,
    private_dim: Dimension<F>,
    private_lanes: Uint<F>,
    bus_dim: Dimension<F>,
    public_offset: Uint<F>,
    flock_offset: Uint<F>,
    fixed_root: [F; 4],
    tables: Vec<TableInfo<F>>,
}

impl<F: Copy> KeyInfo<F> {
    pub(crate) fn read<C: Context<F = F>>(
        ctx: &C,
        source: usize,
        expected_digest: [F; 4],
        public_count: usize,
    ) -> Result<Self, Error> {
        let mut words = Vec::with_capacity(KEY_WORDS);
        for _ in 0..KEY_WORDS {
            words.push(ctx.read_scalar(source, ctx.one())?);
        }
        let mut message = Vec::with_capacity(KEY_WORDS + 4);
        message.extend(digest_words(ctx, primitives::hash::hash(KEY_DOMAIN)));
        message.extend_from_slice(&words);
        let digest = hash_words(ctx, &message, ctx.base(message.len() as u64))?;
        for (&actual, &expected) in digest.iter().zip(&expected_digest) {
            ctx.assert_equal(actual, expected)?;
        }
        ctx.assert_equal(words[0], ctx.base(public_count as u64))?;
        let mut tables = Vec::with_capacity(tables::KIND_COUNT);
        for index in 0..tables::KIND_COUNT {
            let start = KEY_HEADER_WORDS + index * KEY_TABLE_WORDS;
            let present = words[start];
            ctx.assert_bool(present)?;
            let dim = Dimension::new(ctx, words[start + 1], MAX_STACK_VARS)?;
            ctx.assert_equal_if(present, dim.contains(2), ctx.one())?;
            for &value in &words[start + 1..start + KEY_TABLE_WORDS] {
                ctx.assert_equal_if(ctx.not(present), value, ctx.zero())?;
            }
            tables.push(TableInfo {
                present,
                dim,
                fixed: Uint::from_field(ctx, words[start + 2], 32)?,
                private: Uint::from_field(ctx, words[start + 3], 32)?,
                bus: Uint::from_field(ctx, words[start + 4], 32)?,
            });
        }
        Ok(Self {
            digest,
            public_count,
            fixed_dim: Dimension::new(ctx, words[1], MAX_STACK_VARS)?,
            fixed_lanes: Uint::from_field(ctx, words[2], 7)?,
            private_dim: Dimension::new(ctx, words[3], MAX_STACK_VARS)?,
            private_lanes: Uint::from_field(ctx, words[4], 7)?,
            bus_dim: Dimension::new(ctx, words[5], MAX_STACK_VARS)?,
            public_offset: Uint::from_field(ctx, words[6], 32)?,
            flock_offset: Uint::from_field(ctx, words[7], 32)?,
            fixed_root: words[8..12].try_into().map_err(|_| Error::InvalidCircuit)?,
            tables,
        })
    }
}

pub(crate) fn offset<C: Context>(
    ctx: &C,
    base: &Uint<C::F>,
    dim: &Dimension<C::F>,
    index: usize,
) -> Result<Uint<C::F>, Error> {
    let (delta, overflow) = Uint::constant(ctx, index as u64, 32).shl(ctx, dim.bits());
    ctx.assert_zero(overflow)?;
    let (result, carry) = base.add(ctx, &delta);
    ctx.assert_zero(carry)?;
    Ok(result)
}

pub(crate) fn extended_dimension<C: Context>(
    ctx: &C,
    dim: &Dimension<C::F>,
    extra: usize,
    maximum: usize,
) -> Result<Dimension<C::F>, Error> {
    let (bits, carry) = dim.bits().add(ctx, &Uint::constant(ctx, extra as u64, DIM_BITS));
    ctx.assert_zero(carry)?;
    Dimension::from_uint(ctx, bits, maximum)
}

pub(crate) fn schemas() -> [NativeTable; tables::KIND_COUNT] {
    TableKind::ALL.map(tables::schema)
}

pub(crate) fn verify<C: Context>(
    ctx: &C,
    source: usize,
    enabled: C::F,
    key: &KeyInfo<C::F>,
    public: &[C::F],
    schemas: &[NativeTable; tables::KIND_COUNT],
) -> Result<(), Error> {
    if public.len() != key.public_count {
        return Err(Error::InvalidInput);
    }
    ctx.assert_bool(enabled)?;
    let public_digest = public_digest(ctx, public)?;
    let mut transcript = Transcript::new(ctx, source, key.digest, public_digest)?;
    let rate = Uint::from_field(ctx, transcript.scalar(enabled)?, 3)?;
    let root = transcript.root(enabled)?;
    let weights = algebra::eq_kernel(ctx, &transcript.sample_vec(enabled, 4)?);
    let beta = transcript.sample(enabled)?;
    let bus = gkr::verify(&key.bus_dim, enabled, &mut transcript)?;
    let mut occupied = ctx.zero();
    let mut airs = Vec::with_capacity(tables::KIND_COUNT);
    for (schema, info) in schemas.iter().zip(&key.tables) {
        let mut forms: [air::Form<'_, C::F>; 3] = std::array::from_fn(|_| air::Form::zero(ctx));
        for (index, flush) in schema.flushes.iter().enumerate() {
            let position = offset(ctx, &info.bus, &info.dim, index)?;
            let selected = ctx.mul(info.present, stacked::selector(ctx, &position, &info.dim, &bus.point));
            occupied = ctx.add(occupied, selected);
            for (side, coordinates) in [&flush.push, &flush.pull].into_iter().enumerate() {
                forms[side].constant = ctx.add(forms[side].constant, ctx.mul(selected, beta));
                for (slot, expression) in coordinates.iter().enumerate() {
                    forms[side].terms.push((ctx.mul(selected, weights[slot]), expression));
                }
            }
            if flush.count.is_some() {
                return Err(Error::InvalidCircuit);
            }
        }
        airs.push(air::Table {
            enabled: info.present,
            dim: info.dim.clone(),
            width: schema.fixed.len() + schema.width,
            relations: &schema.relations,
            forms,
        });
    }
    let zero_dim = Dimension::constant(ctx, 0);
    let mut known = [ctx.zero(); 2];
    for (index, &value) in public.iter().enumerate() {
        let position = offset(ctx, &key.public_offset, &zero_dim, index)?;
        let selected = stacked::selector(ctx, &position, &zero_dim, &bus.point);
        occupied = ctx.add(occupied, selected);
        let tuple = [
            ctx.base(256),
            ctx.base(primitives::field::g_pow(index).0),
            ctx.limb(value, 0),
            ctx.limb(value, 1),
            ctx.limb(value, 2),
        ];
        let push = ctx.add(beta, algebra::dot(ctx, &weights[..5], &tuple));
        known[0] = ctx.add(known[0], ctx.mul(selected, push));
        known[1] = ctx.add(known[1], ctx.mul(selected, beta));
    }
    let totals = [
        ctx.add(bus.values[0], ctx.add(known[0], ctx.not(occupied))),
        ctx.add(bus.values[1], ctx.add(known[1], ctx.not(occupied))),
        ctx.not(bus.values[2]),
    ];
    let no_parameters = |_: PublicSource| Err(Error::InvalidCircuit);
    let claims = air::verify(&mut transcript, enabled, &airs, &bus.point, totals, &no_parameters)?;
    let mut fixed = Vec::new();
    let mut private = Vec::new();
    for ((schema, info), claim) in schemas.iter().zip(&key.tables).zip(&claims) {
        for (column, &value) in claim.evaluations.iter().enumerate() {
            let (destination, base, local) = if column < schema.fixed.len() {
                (&mut fixed, &info.fixed, column)
            } else {
                (&mut private, &info.private, column - schema.fixed.len())
            };
            destination.push(PointClaim {
                enabled: info.present,
                offset: offset(ctx, base, &info.dim, local)?,
                point: claim.point.clone(),
                value,
            });
        }
    }
    let blake = TableKind::Blake2s as usize;
    let info = &key.tables[blake];
    let flock_dim = extended_dimension(ctx, &info.dim, 8, MAX_STACK_VARS)?;
    for &(column, slot) in &schemas[blake].flock_slots {
        let mut point = Point::zero(ctx, flock_dim.clone());
        for index in 0..8 {
            point.coords[index] = ctx.base(((slot >> index) & 1) as u64);
        }
        point.coords[8..MAX_STACK_VARS].copy_from_slice(&claims[blake].point.coords[..MAX_STACK_VARS - 8]);
        private.push(PointClaim {
            enabled: info.present,
            offset: key.flock_offset.clone(),
            point,
            value: claims[blake].evaluations[column],
        });
    }
    let bit_dim = extended_dimension(ctx, &info.dim, 14, crate::protocol::MAX_VARS)?;
    let family = flock_verifier::verify_flock(&bit_dim, ctx.mul(enabled, info.present), &mut transcript)?;
    let rings = [RingOpening {
        offset: key.flock_offset.clone(),
        family,
    }];
    stacked::verify(
        &mut transcript,
        enabled,
        &key.private_dim,
        &rate,
        &key.private_lanes,
        root,
        &private,
        &rings,
    )?;
    let fixed_rate = Uint::constant(ctx, FIXED_LOG_INV_RATE as u64, 3);
    stacked::verify(
        &mut transcript,
        enabled,
        &key.fixed_dim,
        &fixed_rate,
        &key.fixed_lanes,
        key.fixed_root,
        &fixed,
        &[],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Builder, Key,
        context::{Source, Symbolic, Witness},
    };
    use leanvm_guest::Field;

    fn inner(hashes: bool) -> (Key, Field, Vec<Field>) {
        let builder = Builder::new();
        let input = builder.input(false);
        let output = builder.input(true);
        let multiplier = builder.constant(Field::from(2));
        let mut state = input;
        let mut value = Field::from(11);
        for _ in 0..9 {
            state = builder.mul(state, multiplier);
            value *= Field::from(2);
        }
        if hashes {
            let mut words = [state; 14];
            for index in 0..4 {
                words[8 + index] = builder.constant(Field::from(lean_vm::hash_flock::IV[index].0));
            }
            words[12] = builder.constant(Field::from(64));
            words[13] = builder.constant(Field::from(u32::MAX as u64));
            state = builder.blake2s(words)[0];
            let message: Vec<_> = (0..8).flat_map(|_| value.0[0].to_le_bytes()).collect();
            value = Field::from(u64::from_le_bytes(
                primitives::hash::hash(&message)[..8].try_into().unwrap(),
            ));
        }
        builder.assert_equal(state, output);
        (Key::new(builder.finish()).unwrap(), value, vec![Field::from(11)])
    }

    fn program<C: Context>(ctx: &C, schemas: &[NativeTable; tables::KIND_COUNT]) -> Result<(), Error> {
        let digest = [ctx.public(1)?, ctx.public(2)?, ctx.public(3)?, ctx.public(4)?];
        let key = KeyInfo::read(ctx, 1, digest, 1)?;
        verify(ctx, 0, ctx.public(5)?, &key, &[ctx.public(0)?], schemas)
    }

    fn public(key: &Key, value: Field, enabled: bool) -> Vec<Field> {
        let mut public = vec![value];
        public.extend(
            key.digest()
                .chunks_exact(8)
                .map(|word| Field::from(u64::from_le_bytes(word.try_into().unwrap()))),
        );
        public.push(Field::from(u64::from(enabled)));
        public
    }

    #[test]
    fn expected_native_key_and_all_openings_are_constrained() {
        lean_vm::init_prover_pool();
        let schemas = schemas();
        let symbolic = Symbolic::new(6);
        program(&symbolic, &schemas).unwrap();
        let circuit = symbolic.finish();
        for (hashes, rate) in [(false, 1), (true, 2)] {
            let (key, value, private) = inner(hashes);
            let proof = key.prove(&[value], &private, rate).unwrap();
            let raw = key.raw_proof(&[value], &proof).unwrap();
            let descriptor: Vec<_> = key.descriptor().iter().copied().map(Field::from).collect();
            let public = public(&key, value, true);
            let witness = Witness::new(&public, vec![Source::Native(&raw), Source::Advice(&descriptor)]);
            program(&witness, &schemas)
                .unwrap_or_else(|error| panic!("native replay (hashes={hashes}, rate={rate}): {error}"));
            let advice = witness.finish().unwrap();
            circuit.evaluate(&public, &advice).unwrap();

            let mut changed_public = public.clone();
            changed_public[0] += Field::ONE;
            assert!(
                program(
                    &Witness::new(&changed_public, vec![Source::Native(&raw), Source::Advice(&descriptor)]),
                    &schemas
                )
                .is_err()
            );
            assert!(circuit.evaluate(&changed_public, &advice).is_err());

            let mut changed = raw.clone();
            changed.stream[0] += primitives::field::F192::new(0, 1, 0);
            assert!(
                program(
                    &Witness::new(&public, vec![Source::Native(&changed), Source::Advice(&descriptor)]),
                    &schemas
                )
                .is_err()
            );
            let mut changed_descriptor = descriptor.clone();
            changed_descriptor[8] += Field::ONE;
            assert!(
                program(
                    &Witness::new(&public, vec![Source::Native(&raw), Source::Advice(&changed_descriptor)]),
                    &schemas
                )
                .is_err()
            );

            let mut disabled = public.clone();
            disabled[5] = Field::ZERO;
            let witness = Witness::new(&disabled, vec![Source::Advice(&[]), Source::Advice(&descriptor)]);
            program(&witness, &schemas).unwrap();
            circuit.evaluate(&disabled, &witness.finish().unwrap()).unwrap();
        }
    }

    #[test]
    #[ignore]
    fn prove_native_verifier_circuit() {
        lean_vm::init_prover_pool();
        let schemas = schemas();
        let (inner, value, private) = inner(true);
        let proof = inner.prove(&[value], &private, 2).unwrap();
        let raw = inner.raw_proof(&[value], &proof).unwrap();
        let descriptor: Vec<_> = inner.descriptor().iter().copied().map(Field::from).collect();
        let public = public(&inner, value, true);
        let symbolic = Symbolic::new(6);
        program(&symbolic, &schemas).unwrap();
        let circuit = symbolic.finish();
        println!(
            "native_verifier wires={} private_inputs={}",
            circuit.wire_count(),
            circuit.private_inputs()
        );
        let witness = Witness::new(&public, vec![Source::Native(&raw), Source::Advice(&descriptor)]);
        program(&witness, &schemas).unwrap();
        let advice = witness.finish().unwrap();
        let outer = Key::new(circuit).unwrap();
        println!("native_verifier {:?}", outer.summary());
        let proof = outer.prove(&public, &advice, 1).unwrap();
        outer.verify(&public, &proof).unwrap();
        let mut wrong = public.clone();
        wrong[0] += Field::ONE;
        assert!(outer.verify(&wrong, &proof).is_err());
        println!(
            "native_verifier proof_accepted=true changed_public_rejected=true scalars={}",
            proof.stream.len()
        );
    }
}
