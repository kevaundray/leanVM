//! Public packed Boolean wiring and physical-column projection reductions.
//!
//! Both reductions end in 64 low-wire slices of the committed packed-word
//! cube. Only transcript messages are advice; matrices, pins and projection
//! coefficients are evaluated from the trusted circuit template.
use riscv_proof::packed::{PackedCircuit, PackedGate, PackedSpec};

use crate::Error;
use crate::algebra::{dot, eq_kernel, poly_eval};
use crate::context::Context;
use crate::flock_verifier::{verify_flock_zerocheck, verify_lincheck};
use crate::protocol::{DIM_BITS, Dimension, MAX_STACK_VARS, MAX_VARS, Point, SliceFamily};
use crate::transcript::Transcript;
use crate::uint::Uint;

const SKIP: usize = 6;
const SLICES: usize = 1 << SKIP;

fn shape(spec: &PackedSpec, values_len: usize) -> Result<(), Error> {
    let circuit = &spec.circuit;
    // At least three row bits are required, even for the smallest template.
    if !(10..=MAX_STACK_VARS).contains(&circuit.k_log)
        || circuit.gates.len() != 1usize << circuit.k_log
        || circuit.zero_pin >= circuit.gates.len()
        || values_len != circuit.aliases.len()
        || values_len != circuit.raw_columns.len()
    {
        return Err(Error::InvalidInput);
    }
    let width = circuit.gates.len();
    for gate in &circuit.gates {
        if let PackedGate::Xor(a, b) | PackedGate::And(a, b) = *gate
            && (a >= width || b >= width)
        {
            return Err(Error::InvalidInput);
        }
    }
    if circuit.aliases.iter().flatten().any(|&(wire, _)| wire >= width) {
        return Err(Error::InvalidInput);
    }
    Ok(())
}

/// row^T (A + alpha B) column. Duplicate XOR inputs cancel in the field;
/// zero rows are the only gates omitted, based on public circuit topology.
fn bilinear<C: Context>(
    ctx: &C,
    circuit: &PackedCircuit,
    alpha: C::F,
    rows: &[C::F],
    columns: &[C::F],
) -> Result<C::F, Error> {
    if rows.len() != circuit.gates.len() || columns.len() != rows.len() {
        return Err(Error::InvalidInput);
    }
    let mut result = ctx.zero();
    let alpha_one = ctx.mul(alpha, columns[1]);
    for (output, gate) in circuit.gates.iter().enumerate() {
        let value = match *gate {
            PackedGate::Zero => continue,
            PackedGate::Input => ctx.add(columns[output], alpha_one),
            PackedGate::One => ctx.add(columns[1], alpha_one),
            PackedGate::Xor(a, b) => ctx.add(ctx.add(columns[a], columns[b]), alpha_one),
            PackedGate::And(a, b) => ctx.add(columns[a], ctx.mul(alpha, columns[b])),
        };
        result = ctx.add(result, ctx.mul(rows[output], value));
    }
    Ok(result)
}

/// Fold aliases without materializing a wire-by-physical-column matrix.
/// Adjacent aliases sharing a high wire reuse gamma^column * eq(high).
fn projection_terminal<C: Context>(
    ctx: &C,
    circuit: &PackedCircuit,
    gamma: C::F,
    point: &[C::F],
    slices: &[C::F; SLICES],
) -> C::F {
    let weights = eq_kernel(ctx, point);
    let mut coefficients = [ctx.zero(); SLICES];
    let mut scaled = [ctx.zero(); 64];
    let mut power = ctx.one();
    let generator = ctx.base(2);
    for (column, aliases) in circuit.aliases.iter().enumerate() {
        if column != 0 {
            power = ctx.mul(power, gamma);
        }
        let mut high = usize::MAX;
        let mut scaled_len = 0;
        for &(wire, mut coefficient) in aliases {
            if coefficient == 0 {
                continue;
            }
            let next_high = wire / SLICES;
            if next_high != high {
                high = next_high;
                scaled[0] = ctx.mul(power, weights[high]);
                scaled_len = 1;
            }
            // Coefficients are public polynomial-basis GF(2^64) words.
            // Multiplication by the base generator is not integer shifting
            // or multiplication by an extension-tower generator.
            while coefficient != 0 {
                let bit = coefficient.trailing_zeros() as usize;
                while scaled_len <= bit {
                    scaled[scaled_len] = ctx.mul(scaled[scaled_len - 1], generator);
                    scaled_len += 1;
                }
                let low = wire % SLICES;
                coefficients[low] = ctx.add(coefficients[low], scaled[bit]);
                coefficient &= coefficient - 1;
            }
        }
    }
    dot(ctx, &coefficients, slices)
}

pub(crate) fn verify<C: Context>(
    spec: &PackedSpec,
    row_point: &Point<C::F>,
    column_values: &[C::F],
    enabled: C::F,
    transcript: &mut Transcript<C>,
) -> Result<[SliceFamily<C::F>; 2], Error> {
    shape(spec, column_values.len())?;
    let ctx = transcript.context();
    ctx.assert_bool(enabled)?;
    ctx.assert_equal_if(enabled, row_point.dim.contains(2), ctx.one())?;
    let k_log = spec.circuit.k_log;
    let rows = Uint::select(ctx, enabled, row_point.dim.bits(), &Uint::constant(ctx, 0, DIM_BITS));
    let (bits, carry) = rows.add(ctx, &Uint::constant(ctx, k_log as u64, DIM_BITS));
    ctx.assert_zero(carry)?;
    let bit_dim = Dimension::from_uint(ctx, bits, MAX_VARS)?;
    let zc = verify_flock_zerocheck(&bit_dim, enabled, transcript)?;
    let first = verify_lincheck(
        zc,
        enabled,
        k_log,
        1,
        Some(spec.circuit.zero_pin),
        |ctx, alpha, rows, columns| bilinear(ctx, &spec.circuit, alpha, rows, columns),
        transcript,
    )?;

    let gamma = transcript.sample(enabled)?;
    let mut running = ctx.mul(enabled, poly_eval(ctx, column_values, gamma));
    let rounds = k_log - SKIP;
    let mut point = Point::zero(ctx, first.point.dim.clone());
    for i in 0..rounds {
        let message = transcript.round_poly(enabled, 3, running, None)?;
        let challenge = transcript.sample(enabled)?;
        point.coords[rounds - 1 - i] = challenge;
        running = ctx.select(enabled, poly_eval(ctx, &message, challenge), running);
    }
    let mut slices = [ctx.zero(); SLICES];
    for slice in &mut slices {
        *slice = transcript.scalar(enabled)?;
    }
    let terminal = projection_terminal(ctx, &spec.circuit, gamma, &point.coords[..rounds], &slices);
    ctx.assert_equal_if(enabled, terminal, running)?;
    // Projection is at the caller's actual physical-column row point, not
    // the zerocheck's independent row point or an advised replacement.
    for i in rounds..MAX_STACK_VARS {
        point.coords[i] = ctx.mul(
            ctx.mul(enabled, row_point.dim.contains(i - rounds)),
            row_point.coords[i - rounds],
        );
    }
    let second = SliceFamily { enabled, point, slices };
    Ok([first, second])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::{Source, Symbolic, Witness};
    use fiat_shamir::transcript::{Challenger, ProverState, RawProof, Receiver, Transmitter, VerifierState};
    use leanvm_guest::Field;
    use primitives::field::{F64, F192};
    use riscv_proof::schema::{Access, RomCounter, Space, TableRows};

    const SENTINEL: Field = Field::new(0xfedc, 0xba98, 0x7654);
    const FAMILY_LEN: usize = 2 + MAX_VARS + SLICES;
    const COLUMN_START: usize = 2 + MAX_VARS;

    fn field(value: F192) -> Field {
        Field::new(value.c0, value.c1, value.c2)
    }
    fn native(value: Field) -> F192 {
        F192::new(value.0[0], value.0[1], value.0[2])
    }

    fn program_info() -> riscv_proof::ProgramInfo {
        // A real RV64 ELF with one executable ECALL; memory fixtures access
        // zero-initialized RAM outside its read-only text segment.
        let mut elf = vec![0u8; 0x104];
        elf[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        for (at, value) in [(16, 2u16), (18, 243), (52, 64), (54, 56), (56, 1)] {
            elf[at..at + 2].copy_from_slice(&value.to_le_bytes());
        }
        elf[20..24].copy_from_slice(&1u32.to_le_bytes());
        elf[24..32].copy_from_slice(&0x10000u64.to_le_bytes());
        elf[32..40].copy_from_slice(&64u64.to_le_bytes());
        elf[64..68].copy_from_slice(&1u32.to_le_bytes());
        elf[68..72].copy_from_slice(&5u32.to_le_bytes());
        for (at, value) in [(72, 0x100u64), (80, 0x10000), (96, 4), (104, 4), (112, 4)] {
            elf[at..at + 8].copy_from_slice(&value.to_le_bytes());
        }
        elf[0x100..].copy_from_slice(&0x73u32.to_le_bytes());
        riscv_proof::ProgramInfo::from_elf(&elf).unwrap()
    }

    fn memory_rows(space: Space, count: usize) -> TableRows {
        let program = program_info();
        let mut rom = RomCounter::new(&program);
        let events: Vec<_> = (0..count)
            .map(|i| Access {
                space,
                address: if space == Space::Ram { 0x20000 } else { 1 },
                time: i as u64 + 1,
                before: i as u64,
                after: i as u64 + 1,
                write: true,
            })
            .collect();
        riscv_proof::memory::build_rows(&program, space, &events, &mut rom)
            .unwrap()
            .0
    }

    fn cpu_rows(tau: usize) -> TableRows {
        use riscv_proof::instruction::{InstructionCircuit, Opcode};
        let spec = riscv_proof::cpu_tables::build_spec([0; 32], 1, riscv_proof::cpu_tables::EXIT_TABLE);
        let packing = PackedSpec::new(&spec);
        // Canonical production CPU padding rows: legal ECALL instruction,
        // disabled CPU/bus effects, and zero auxiliary inputs.
        let instruction = InstructionCircuit::build(Opcode::Ecall);
        let mut inputs = instruction.canonical_inputs();
        inputs.resize(spec.circuit.inputs(), false);
        let row = packing
            .circuit
            .pack_row(&spec.circuit.witness(&inputs).unwrap())
            .unwrap();
        let mut rows = vec![row; 1 << tau];
        // One real exit at the fixture ELF's entry, then production padding.
        // Auxiliary inputs are enabled, cycle, cycle bound, ROM count, a0.
        let mut active = riscv_proof::schema::InputValues(instruction.inputs(0x73, 0x10000, 0, 0, &[]).unwrap());
        for (value, width) in [(1, 1), (0, 32), (1, 32), (1, 64), (0, 64)] {
            active.word(value, width);
        }
        rows[0] = packing
            .circuit
            .pack_row(&spec.circuit.witness(&active.0).unwrap())
            .unwrap();
        TableRows { spec, packing, rows }
    }

    fn program<C: Context>(ctx: &C, spec: &PackedSpec) -> Result<Vec<C::F>, Error> {
        let enabled = ctx.public(0)?;
        let dim = Dimension::new(ctx, ctx.public(1)?, MAX_VARS)?;
        let mut point = Point::zero(ctx, dim);
        for (i, coord) in point.coords.iter_mut().enumerate() {
            *coord = ctx.public(2 + i)?;
        }
        let columns = (0..spec.circuit.aliases.len())
            .map(|i| ctx.public(COLUMN_START + i))
            .collect::<Result<Vec<_>, _>>()?;
        let mut transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        let families = verify(spec, &point, &columns, enabled, &mut transcript)?;
        let mut output = Vec::new();
        for family in families {
            output.extend([family.enabled, family.point.dim.value(ctx)]);
            output.extend(family.point.coords);
            output.extend(family.slices);
        }
        output.extend(transcript.state());
        output.push(transcript.sample(ctx.one())?);
        output.push(transcript.scalar(ctx.one())?);
        Ok(output)
    }

    struct Fixture {
        public: Vec<Field>,
        proof: RawProof,
        claims: Vec<riscv_proof::packed_reduction::BitClaim>,
        next_challenge: Field,
    }

    fn fixture(table: &TableRows) -> Fixture {
        let tau = table.rows.len().ilog2() as usize;
        let point: Vec<_> = (0..tau).map(|i| F192::new(17 + i as u64, 29, 43)).collect();
        let weights = primitives::multilinear::eq_table(&point);
        let mut columns = vec![F192::ZERO; table.packing.circuit.aliases.len()];
        for (row, weight) in table.rows.iter().zip(weights) {
            for (value, &word) in columns.iter_mut().zip(&row.values) {
                *value += weight.mul_base(F64(word));
            }
        }
        let mut prover = ProverState::new([F64::ZERO; 4], [F64::ZERO; 4]);
        let claims =
            riscv_proof::packed_reduction::prove(&table.packing, tau, &table.rows, &point, &columns, &mut prover)
                .unwrap();
        let next_challenge = field(prover.sample());
        prover.add_scalar(native(SENTINEL));
        let proof = prover.into_proof();
        let mut reference = VerifierState::new([F64::ZERO; 4], &proof, [F64::ZERO; 4]);
        let checked =
            riscv_proof::packed_reduction::verify_native(&table.packing, tau, &point, &columns, &mut reference)
                .unwrap();
        for (expected, actual) in claims.iter().zip(checked) {
            assert_eq!(expected.point, actual.point);
            assert_eq!(expected.slices, actual.slices);
        }
        assert_eq!(field(reference.sample()), next_challenge);
        assert_eq!(field(reference.next_scalar().unwrap()), SENTINEL);
        let mut public = vec![Field::ZERO; COLUMN_START + columns.len()];
        public[0] = Field::ONE;
        public[1] = Field::from(tau as u64);
        for (dst, src) in public[2..2 + tau].iter_mut().zip(point) {
            *dst = field(src);
        }
        for (dst, src) in public[COLUMN_START..].iter_mut().zip(columns) {
            *dst = field(src);
        }
        Fixture {
            public,
            proof: RawProof {
                stream: proof.stream,
                merkle: Vec::new(),
            },
            claims,
            next_challenge,
        }
    }

    #[test]
    fn production_cpu_and_memory_proofs_share_bounded_circuits_across_heights_and_absence() {
        for tables in [
            [cpu_rows(3), cpu_rows(4)],
            [memory_rows(Space::Ram, 1), memory_rows(Space::Ram, 9)],
            [memory_rows(Space::Register, 1), memory_rows(Space::Register, 9)],
        ] {
            let spec = &tables[0].packing;
            let symbolic = Symbolic::new(COLUMN_START + spec.circuit.aliases.len());
            let output = program(&symbolic, spec).unwrap();
            let circuit = symbolic.finish();
            for table in &tables {
                let fixture = fixture(table);
                let witness = Witness::new(&fixture.public, vec![Source::Native(&fixture.proof)]);
                let actual = program(&witness, spec).unwrap();
                for (i, expected) in fixture.claims.iter().enumerate() {
                    let start = i * FAMILY_LEN;
                    assert_eq!(actual[start], Field::ONE);
                    assert_eq!(actual[start + 1], Field::from(expected.point.len() as u64));
                    assert_eq!(&actual[start + 2..start + 2 + expected.point.len()], &expected.point);
                    assert!(
                        actual[start + 2 + expected.point.len()..start + 2 + MAX_VARS]
                            .iter()
                            .all(|&value| value == Field::ZERO)
                    );
                    assert_eq!(&actual[start + 2 + MAX_VARS..start + FAMILY_LEN], &expected.slices);
                }
                assert_eq!(actual[2 * FAMILY_LEN + 4], fixture.next_challenge);
                assert_eq!(actual[2 * FAMILY_LEN + 5], SENTINEL);
                let private = witness.finish().unwrap();
                let values = circuit.evaluate(&fixture.public, &private).unwrap();
                for (wire, expected) in output.iter().zip(actual) {
                    assert_eq!(values[wire.index()], expected);
                }
                // The raw column target participates in constrained algebra,
                // independently of transcript transport and advice checks.
                let mut false_columns = fixture.public.clone();
                false_columns[COLUMN_START] += Field::ONE;
                assert!(circuit.evaluate(&false_columns, &private).is_err());
                let bad = Witness::new(&false_columns, vec![Source::Native(&fixture.proof)]);
                assert!(program(&bad, spec).is_err());
            }
            for tau in [0, MAX_VARS] {
                let mut public = vec![Field::from(91); COLUMN_START + spec.circuit.aliases.len()];
                public[0] = Field::ZERO;
                public[1] = Field::from(tau as u64);
                let advice = [SENTINEL];
                let witness = Witness::new(&public, vec![Source::Advice(&advice)]);
                let actual = program(&witness, spec).unwrap();
                assert!(actual[..2 * FAMILY_LEN].iter().all(|&value| value == Field::ZERO));
                let initial_ctx = Witness::new(&[], Vec::new());
                let mut initial = Transcript::new(&initial_ctx, 0, [Field::ZERO; 4], [Field::ZERO; 4]).unwrap();
                assert_eq!(&actual[2 * FAMILY_LEN..2 * FAMILY_LEN + 4], &initial.state());
                assert_eq!(actual[2 * FAMILY_LEN + 4], initial.sample(Field::ONE).unwrap());
                assert_eq!(actual[2 * FAMILY_LEN + 5], SENTINEL);
                let values = circuit.evaluate(&public, &witness.finish().unwrap()).unwrap();
                for (wire, expected) in output.iter().zip(actual) {
                    assert_eq!(values[wire.index()], expected);
                }
            }
        }
    }

    #[test]
    fn malformed_dimensions_and_gate_pin_projection_claims_are_rejected() {
        let table = memory_rows(Space::Ram, 1);
        let spec = &table.packing;
        let fixture = fixture(&table);
        let symbolic = Symbolic::new(fixture.public.len());
        program(&symbolic, spec).unwrap();
        let circuit = symbolic.finish();
        let good = Witness::new(&fixture.public, vec![Source::Native(&fixture.proof)]);
        program(&good, spec).unwrap();
        let private = good.finish().unwrap();
        for (enabled, tau) in [
            (Field::ONE, 2),
            (Field::ONE, MAX_VARS - spec.circuit.k_log + 1),
            (Field::from(2), 3),
        ] {
            let mut public = fixture.public.clone();
            public[0] = enabled;
            public[1] = Field::from(tau as u64);
            let bad = Witness::new(&public, vec![Source::Native(&fixture.proof)]);
            assert!(program(&bad, spec).is_err());
            assert!(circuit.evaluate(&public, &private).is_err());
        }
        let mut wrong_pin = spec.clone();
        wrong_pin.circuit.zero_pin = 1;
        let mut wrong_gate = spec.clone();
        wrong_gate.circuit.gates[1] = PackedGate::Zero;
        let mut wrong_projection = spec.clone();
        wrong_projection.circuit.aliases[0] = vec![(1, 0x8000_0000_0000_001b)];
        for forged in [&wrong_pin, &wrong_gate, &wrong_projection] {
            let bad = Witness::new(&fixture.public, vec![Source::Native(&fixture.proof)]);
            assert!(program(&bad, forged).is_err());
        }
        // The last projection slice block precedes only the sentinel. Choose
        // an actually projected low wire rather than an unconstrained padding
        // slice, which is bound by the later commitment opening instead.
        let low = spec
            .circuit
            .aliases
            .iter()
            .flatten()
            .find(|&&(_, coefficient)| coefficient != 0)
            .unwrap()
            .0
            % SLICES;
        let mut forged = fixture.proof.clone();
        let index = forged.stream.len() - 1 - SLICES + low;
        forged.stream[index] += F192::ONE;
        let bad = Witness::new(&fixture.public, vec![Source::Native(&forged)]);
        assert!(program(&bad, spec).is_err());
        let mut forged_advice = private.clone();
        let index = forged_advice.len() - 1 - SLICES + low;
        forged_advice[index] += Field::ONE;
        assert!(circuit.evaluate(&fixture.public, &forged_advice).is_err());
        // Change the validity reduction's one-pin slice, not just the
        // projection's copy of that wire.
        let rounds = spec.circuit.k_log - SKIP;
        let validity_end = SLICES + 2 * (spec.circuit.k_log + 3 - SKIP) + 2 + 2 * rounds + SLICES;
        let mut forged = fixture.proof.clone();
        forged.stream[validity_end - SLICES + 1] += F192::ONE;
        let bad = Witness::new(&fixture.public, vec![Source::Native(&forged)]);
        assert!(program(&bad, spec).is_err());

        let mut malformed = spec.clone();
        malformed.circuit.k_log = 9;
        assert!(shape(&malformed, fixture.public.len() - COLUMN_START).is_err());
        malformed = spec.clone();
        malformed.circuit.gates.pop();
        assert!(shape(&malformed, fixture.public.len() - COLUMN_START).is_err());
        malformed = spec.clone();
        malformed.circuit.zero_pin = malformed.circuit.gates.len();
        assert!(shape(&malformed, fixture.public.len() - COLUMN_START).is_err());
        assert!(shape(spec, fixture.public.len() - COLUMN_START - 1).is_err());
    }

    fn projection_program<C: Context>(ctx: &C, circuit: &PackedCircuit) -> Result<C::F, Error> {
        let gamma = ctx.public(0)?;
        let rounds = circuit.k_log - SKIP;
        let point = (0..rounds).map(|i| ctx.public(1 + i)).collect::<Result<Vec<_>, _>>()?;
        let mut slices = [ctx.zero(); SLICES];
        for (i, slice) in slices.iter_mut().enumerate() {
            *slice = ctx.public(1 + rounds + i)?;
        }
        Ok(projection_terminal(ctx, circuit, gamma, &point, &slices))
    }

    #[test]
    fn projection_preserves_base_field_folding_at_zero_weights_and_gamma() {
        let mut packed = cpu_rows(3).packing.circuit;
        packed.aliases = vec![
            vec![(63, 1), (64, 1 << 63), (65, 0x8000_0000_0000_001b), (63, 1)],
            vec![(130, 3), (131, 1 << 62), (130, 3), (66, 0), (66, 7)],
            Vec::new(),
            vec![(1023, u64::MAX), (1, 1), (1023, 1 << 63)],
        ];
        let rounds = packed.k_log - SKIP;
        let symbolic = Symbolic::new(1 + rounds + SLICES);
        let output = projection_program(&symbolic, &packed).unwrap();
        let circuit = symbolic.finish();
        for gamma in [Field::ZERO, Field::ONE, Field::new(0x8000_0000_0000_0000, u64::MAX, 29)] {
            for boolean_point in [false, true] {
                let point: Vec<_> = (0..rounds)
                    .map(|i| {
                        if boolean_point {
                            Field::from((i % 2) as u64)
                        } else {
                            Field::new(i as u64 + 17, 19, 23)
                        }
                    })
                    .collect();
                let slices: Vec<_> = (0..SLICES)
                    .map(|i| {
                        if i % 7 == 0 {
                            Field::ZERO
                        } else {
                            Field::new(i as u64, u64::MAX - i as u64, 1 << (i % 64))
                        }
                    })
                    .collect();
                let weights = riscv_proof::portable::algebra::eq_kernel(&point);
                let mut power = Field::ONE;
                let mut expected = Field::ZERO;
                for aliases in &packed.aliases {
                    for &(wire, coefficient) in aliases {
                        expected += power * weights[wire / SLICES] * Field::from(coefficient) * slices[wire % SLICES];
                    }
                    power *= gamma;
                }
                let public: Vec<_> = [gamma].into_iter().chain(point).chain(slices).collect();
                let witness = Witness::new(&public, Vec::new());
                assert_eq!(projection_program(&witness, &packed).unwrap(), expected);
                let values = circuit.evaluate(&public, &witness.finish().unwrap()).unwrap();
                assert_eq!(values[output.index()], expected);
            }
        }
    }
}
