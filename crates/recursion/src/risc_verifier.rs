use crate::{
    Error, air, algebra,
    context::Context,
    flock_verifier, gkr,
    native::{digest_words, extended_dimension, offset},
    packed_verifier,
    protocol::{Dimension, MAX_STACK_VARS, Point},
    risc_layout::{Header, Layout, Templates},
    stacked::{self, PointClaim, RingOpening},
    transcript::Transcript,
};
use riscv_proof::{
    layout::{RAM_TABLE, REG_TABLE, TABLES},
    schema::{PublicSource, SEP_CPU, SEP_ROM, SEP_SORT_RAM, SEP_SORT_REG, Space},
};

fn public_mle_fold<C: Context>(ctx: &C, values: &[u64], point: &[C::F], subsets: &[C::F; 256]) -> C::F {
    if let Some((&challenge, rest)) = point.split_last() {
        let (left, right) = values.split_at(values.len() / 2);
        let a = public_mle_fold(ctx, left, rest, subsets);
        let b = public_mle_fold(ctx, right, rest, subsets);
        return ctx.add(a, ctx.mul(challenge, ctx.add(a, b)));
    }
    let anchor = values[0];
    let mut lanes = [0u64; 8];
    let mut varying = 0;
    for (lane, &word) in lanes.iter_mut().zip(values) {
        *lane = word ^ anchor;
        varying |= *lane;
    }
    if varying == 0 {
        return ctx.base(anchor);
    }
    let bits = (u64::BITS - varying.leading_zeros()) as usize;
    let mut value = ctx.zero();
    for bit in (0..bits).rev() {
        let mut plane = 0usize;
        for (lane, &word) in lanes.iter().enumerate() {
            plane |= ((word >> bit & 1) as usize) << lane;
        }
        value = ctx.add(ctx.mul(value, ctx.base(2)), subsets[plane]);
    }
    ctx.add(ctx.base(anchor), value)
}

fn public_rom<C: Context>(ctx: &C, templates: &Templates, point: &Point<C::F>) -> [C::F; 2] {
    let low = templates.rom_log.min(3);
    let weights = algebra::eq_kernel(ctx, &point.coords[..low]);
    let mut subsets = [ctx.zero(); 256];
    for (lane, &weight) in weights.iter().enumerate() {
        for mask in 0..1usize << lane {
            subsets[mask + (1 << lane)] = ctx.add(subsets[mask], weight);
        }
    }
    [&templates.rom_keys, &templates.rom_values]
        .map(|values| public_mle_fold(ctx, values, &point.coords[low..templates.rom_log], &subsets))
}

pub(crate) fn verify<C: Context>(
    ctx: &C,
    source: usize,
    enabled: C::F,
    templates: &Templates,
    public: [C::F; 4],
) -> Result<(), Error> {
    ctx.assert_bool(enabled)?;
    let mut bytes = [ctx.zero(); 32];
    for (word, &value) in public.iter().enumerate() {
        let bits = ctx.bits(value, 64)?;
        for byte in 0..8 {
            let mut value = ctx.zero();
            for bit in 0..8 {
                value = ctx.add(value, ctx.mul(bits[8 * byte + bit], ctx.base(1 << bit)));
            }
            bytes[8 * word + byte] = value;
        }
    }
    let mut transcript = Transcript::new(ctx, source, digest_words(ctx, templates.iv), public)?;
    let header = Header::read(&mut transcript, enabled)?;
    let layout = Layout::new(ctx, templates, header)?;
    let root = transcript.root(enabled)?;
    let weights = algebra::eq_kernel(ctx, &transcript.sample_vec(enabled, 4)?);
    let beta = transcript.sample(enabled)?;
    let bus = gkr::verify(&layout.bus_dim, enabled, &mut transcript)?;
    let mut occupied = [ctx.zero(); 3];
    let mut airs = Vec::with_capacity(TABLES);
    for (logical, spec) in templates.specs.iter().enumerate() {
        let shape = &layout.header.tables[logical];
        let mut forms: [air::Form<'_, C::F>; 3] = std::array::from_fn(|_| air::Form::zero(ctx));
        let mut count_index = 0;
        for (index, flush) in spec.flushes.iter().enumerate() {
            let position = offset(ctx, &layout.bus_offsets[logical], &shape.dim, index)?;
            let selected = ctx.mul(shape.present, stacked::selector(ctx, &position, &shape.dim, &bus.point));
            for (side, coordinates) in [&flush.push, &flush.pull].into_iter().enumerate() {
                if coordinates.len() > weights.len() {
                    return Err(Error::InvalidCircuit);
                }
                occupied[side] = ctx.add(occupied[side], selected);
                forms[side].constant = ctx.add(forms[side].constant, ctx.mul(selected, beta));
                for (slot, coordinate) in coordinates.iter().enumerate() {
                    forms[side].terms.push((ctx.mul(selected, weights[slot]), coordinate));
                }
            }
            if let Some(coordinate) = &flush.count {
                let position = offset(ctx, &layout.count_offsets[logical], &shape.dim, count_index)?;
                count_index += 1;
                let selected = ctx.mul(shape.present, stacked::selector(ctx, &position, &shape.dim, &bus.point));
                occupied[2] = ctx.add(occupied[2], selected);
                forms[2].terms.push((selected, coordinate));
            }
        }
        airs.push(air::Table {
            enabled: shape.present,
            dim: shape.dim.clone(),
            width: spec.circuit.raw_columns.len(),
            relations: &spec.relations,
            forms,
        });
    }
    let rom = public_rom(ctx, templates, &bus.point);
    let rom_count = transcript.scalar(enabled)?;
    let rom_dim = Dimension::constant(ctx, templates.rom_log);
    let mut rom_point = Point::zero(ctx, rom_dim.clone());
    rom_point.coords[..templates.rom_log].copy_from_slice(&bus.point.coords[..templates.rom_log]);
    let mut points = vec![PointClaim {
        enabled: ctx.one(),
        offset: layout.rom_offset.clone(),
        point: rom_point,
        value: rom_count,
    }];
    let zero_dim = Dimension::constant(ctx, 0);
    let mut known = [ctx.zero(); 3];
    let mut boundary = |index: usize, present: C::F, dim: &Dimension<C::F>, push: &[C::F], pull: &[C::F]| {
        let selected = ctx.mul(
            present,
            stacked::selector(ctx, &layout.framework_offsets[index], dim, &bus.point),
        );
        for (side, coordinates) in [push, pull].into_iter().enumerate() {
            occupied[side] = ctx.add(occupied[side], selected);
            let value = ctx.add(beta, algebra::dot(ctx, &weights[..coordinates.len()], coordinates));
            known[side] = ctx.add(known[side], ctx.mul(selected, value));
        }
    };
    boundary(
        0,
        ctx.one(),
        &zero_dim,
        &[ctx.base(SEP_CPU), ctx.base(templates.entry), ctx.zero(), ctx.zero()],
        &[
            ctx.base(SEP_CPU),
            ctx.zero(),
            layout.header.cycles.value(ctx),
            ctx.one(),
        ],
    );
    boundary(
        1,
        ctx.one(),
        &rom_dim,
        &[ctx.base(SEP_ROM), rom[0], ctx.one(), rom[1]],
        &[ctx.base(SEP_ROM), rom[0], rom_count, rom[1]],
    );
    for (index, logical, space, separator, memory) in [
        (2, RAM_TABLE, Space::Ram, SEP_SORT_RAM, &layout.header.ram),
        (3, REG_TABLE, Space::Register, SEP_SORT_REG, &layout.header.registers),
    ] {
        let rows = layout.parameter(ctx, &bytes, PublicSource::MemoryRows(space))?;
        boundary(
            index,
            layout.header.tables[logical].present,
            &zero_dim,
            &[ctx.base(separator), ctx.zero(), ctx.zero(), ctx.zero(), ctx.zero()],
            &[
                ctx.base(separator),
                rows,
                memory.last_address.value(ctx),
                memory.last_time.value(ctx),
                memory.last_value.value(ctx),
            ],
        );
    }
    let totals = std::array::from_fn(|side| ctx.add(bus.values[side], ctx.add(known[side], ctx.not(occupied[side]))));
    let parameter = |source| layout.parameter(ctx, &bytes, source);
    let claims = air::verify(&mut transcript, enabled, &airs, &bus.point, totals, &parameter)?;
    let mut rings = Vec::with_capacity(2 * TABLES + 1);
    for (logical, (spec, claim)) in templates.specs.iter().zip(&claims).enumerate() {
        let shape = &layout.header.tables[logical];
        for (column, &value) in claim.evaluations.iter().enumerate() {
            points.push(PointClaim {
                enabled: shape.present,
                offset: offset(ctx, &layout.raw_offsets[logical], &shape.dim, column)?,
                point: claim.point.clone(),
                value,
            });
        }
        let families = packed_verifier::verify(
            spec,
            &claim.point,
            &claim.evaluations,
            ctx.mul(enabled, shape.present),
            &mut transcript,
        )?;
        for family in families {
            rings.push(RingOpening {
                offset: layout.packed_offsets[logical].clone(),
                family,
            });
        }
    }
    let blake = riscv_proof::cpu_tables::BLAKE_TABLE;
    let shape = &layout.header.tables[blake];
    let full_dim = extended_dimension(ctx, &shape.dim, 14, crate::protocol::MAX_VARS)?;
    let family = flock_verifier::verify_flock(&full_dim, ctx.mul(enabled, shape.present), &mut transcript)?;
    rings.push(RingOpening {
        offset: layout.flock_offset.clone(),
        family,
    });
    let word_dim = extended_dimension(ctx, &shape.dim, 8, MAX_STACK_VARS)?;
    for &(column, slot) in &templates.specs[blake].flock_slots {
        let mut point = Point::zero(ctx, word_dim.clone());
        for index in 0..8 {
            point.coords[index] = ctx.base(((slot >> index) & 1) as u64);
        }
        point.coords[8..MAX_STACK_VARS].copy_from_slice(&claims[blake].point.coords[..MAX_STACK_VARS - 8]);
        points.push(PointClaim {
            enabled: shape.present,
            offset: layout.flock_offset.clone(),
            point,
            value: claims[blake].evaluations[column],
        });
    }
    stacked::verify(
        &mut transcript,
        enabled,
        &layout.mu,
        &layout.header.rate,
        &layout.n_lanes,
        root,
        &points,
        &rings,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Key,
        context::{Source, Symbolic, Witness},
    };
    use leanvm_guest::Field;

    fn elf() -> Vec<u8> {
        let instructions: [u32; 15] = [
            0x00003537, 0x00100593, 0x00100893, 0x00000073, 0x000032b7, 0x0002c303, 0xfff30313, 0xfe031ee3, 0x00002537,
            0x00200893, 0x00000073, 0x00000513, 0x00000893, 0x00000073, 0x00000013,
        ];
        let mut elf = vec![0u8; 0x100 + 4 * instructions.len()];
        elf[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        for (at, value) in [(16, 2u16), (18, 243), (52, 64), (54, 56), (56, 1)] {
            elf[at..at + 2].copy_from_slice(&value.to_le_bytes());
        }
        elf[20..24].copy_from_slice(&1u32.to_le_bytes());
        for (at, value) in [
            (24, 0x1000u64),
            (32, 64),
            (72, 0x100),
            (80, 0x1000),
            (88, 0x1000),
            (96, (4 * instructions.len()) as u64),
            (104, 0x1000),
            (112, 0x100),
        ] {
            elf[at..at + 8].copy_from_slice(&value.to_le_bytes());
        }
        elf[64..68].copy_from_slice(&1u32.to_le_bytes());
        elf[68..72].copy_from_slice(&5u32.to_le_bytes());
        for (index, instruction) in instructions.iter().enumerate() {
            elf[0x100 + 4 * index..0x104 + 4 * index].copy_from_slice(&instruction.to_le_bytes());
        }
        elf
    }

    fn program<C: Context>(ctx: &C, templates: &Templates) -> Result<(), Error> {
        verify(
            ctx,
            0,
            ctx.public(4)?,
            templates,
            [ctx.public(0)?, ctx.public(1)?, ctx.public(2)?, ctx.public(3)?],
        )
    }

    #[test]
    fn actual_risc_proofs_match_one_symbolic_verifier() {
        lean_vm::init_prover_pool();
        let elf = elf();
        let machine = riscv::Program::from_elf(&elf).unwrap();
        let info = riscv_proof::ProgramInfo::from_elf(&elf).unwrap();
        let templates = Templates::new(&info).unwrap();
        let symbolic = Symbolic::new(5);
        program(&symbolic, &templates).unwrap();
        let circuit = symbolic.finish();
        println!(
            "risc_verifier wires={} private_inputs={}",
            circuit.wire_count(),
            circuit.private_inputs()
        );
        for (byte, iterations, rate) in [(7, 1, 1), (19, 9, 2)] {
            let digest = [byte; 32];
            let (proof, _) = riscv_proof::host::prove(&machine, digest, &[iterations], 1000, rate).unwrap();
            riscv_proof::verify(&info, digest, &proof).unwrap();
            let mut public: Vec<_> = digest
                .chunks_exact(8)
                .map(|word| Field::from(u64::from_le_bytes(word.try_into().unwrap())))
                .collect();
            public.push(Field::ONE);
            let witness = Witness::new(&public, vec![Source::Risc(&proof)]);
            program(&witness, &templates).unwrap_or_else(|error| {
                panic!("RISC replay (byte={byte}, iterations={iterations}, rate={rate}): {error}")
            });
            let advice = witness.finish().unwrap();
            circuit.evaluate(&public, &advice).unwrap();
            let mut wrong = public.clone();
            wrong[0] += Field::ONE;
            assert!(program(&Witness::new(&wrong, vec![Source::Risc(&proof)]), &templates).is_err());
            assert!(circuit.evaluate(&wrong, &advice).is_err());
            let mut bad = proof.clone();
            bad.stream[0] = Field::ZERO;
            assert!(program(&Witness::new(&public, vec![Source::Risc(&bad)]), &templates).is_err());
            public[4] = Field::ZERO;
            let witness = Witness::new(&public, vec![Source::Advice(&[])]);
            program(&witness, &templates).unwrap();
            circuit.evaluate(&public, &witness.finish().unwrap()).unwrap();
        }
    }

    #[test]
    #[ignore]
    fn prove_risc_verifier_circuit() {
        lean_vm::init_prover_pool();
        let elf = elf();
        let machine = riscv::Program::from_elf(&elf).unwrap();
        let templates = Templates::new(&riscv_proof::ProgramInfo::from_elf(&elf).unwrap()).unwrap();
        let digest = [23u8; 32];
        let (proof, _) = riscv_proof::host::prove(&machine, digest, &[9], 1000, 2).unwrap();
        let mut public: Vec<_> = digest
            .chunks_exact(8)
            .map(|word| Field::from(u64::from_le_bytes(word.try_into().unwrap())))
            .collect();
        public.push(Field::ONE);
        let symbolic = Symbolic::new(5);
        program(&symbolic, &templates).unwrap();
        let circuit = symbolic.finish();
        println!(
            "risc_verifier wires={} private_inputs={}",
            circuit.wire_count(),
            circuit.private_inputs()
        );
        let witness = Witness::new(&public, vec![Source::Risc(&proof)]);
        program(&witness, &templates).unwrap();
        let advice = witness.finish().unwrap();
        let key = Key::new(circuit).unwrap();
        println!("risc_verifier {:?}", key.summary());
        let proof = key.prove(&public, &advice, 1).unwrap();
        key.verify(&public, &proof).unwrap();
        let mut wrong = public.clone();
        wrong[0] += Field::ONE;
        assert!(key.verify(&wrong, &proof).is_err());
        println!(
            "risc_verifier proof_accepted=true changed_public_rejected=true scalars={}",
            proof.stream.len()
        );
    }
}
