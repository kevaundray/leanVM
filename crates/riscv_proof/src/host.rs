//! Native witness generation and the shared SNARK protocol.
//!
//! Execution is used only to construct columns. Acceptance is the bus, local
//! polynomial identities, Flock reduction, and one mixed WHIR opening.
use crate::{
    Error, Opening, ProgramInfo, Proof, VerifySummary, cpu_tables,
    layout::{ABSENT, Coordinate, Header, Layout, ROM_COUNTS},
    memory,
    packed_reduction::{self, BitClaim},
    schema::{Coord, RomCounter, Space},
};
use alloc::{boxed::Box, sync::Arc, vec, vec::Vec};
use lean_vm::colval::ColVal;
use lean_vm::{
    constraints, hash_flock, leaf, pcs,
    transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState},
    witness::{self, Placement, StackShape},
};
use primitives::field::{F64, F192};

type Owners = [Vec<Option<(usize, usize)>>; 3];

fn digest_words(bytes: [u8; 32]) -> [F64; 4] {
    core::array::from_fn(|i| F64(u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap())))
}

fn shape(layout: &Layout) -> StackShape {
    StackShape {
        mu: layout.mu,
        n_lanes: layout.n_lanes,
    }
}

fn summary(layout: &Layout) -> Result<VerifySummary, Error> {
    Ok(VerifySummary {
        cycles: layout.header.cycles,
        memory_events: layout
            .header
            .ram
            .count
            .checked_add(layout.header.registers.count)
            .ok_or(Error::InvalidShape)?,
        committed_words: layout.committed_len() as u64,
        log_inv_rate: layout.header.log_inv_rate as u8,
    })
}

fn coordinate(coord: &Coordinate, public: &[Arc<Vec<F64>>]) -> leaf::Coord {
    match coord {
        Coordinate::Constant(value) => leaf::Coord::Const(F64(*value)),
        Coordinate::Column(column) => leaf::Coord::Col(*column),
        // g=x, so each set bit is exactly one monomial in the K basis.
        Coordinate::Scaled(column, coefficient) => leaf::Coord::Sum(
            (0..64)
                .filter(|bit| coefficient >> bit & 1 != 0)
                .map(|bit| leaf::Coord::GCol(*column, bit))
                .collect(),
        ),
        Coordinate::Product(a, b, coefficient) => leaf::Coord::Sum(
            (0..64)
                .filter(|bit| coefficient >> bit & 1 != 0)
                .map(|bit| leaf::Coord::Prod(*a, *b, bit))
                .collect(),
        ),
        Coordinate::Sum(terms) => leaf::Coord::Sum(terms.iter().map(|term| coordinate(term, public)).collect()),
        Coordinate::Public(index) => leaf::Coord::Public(public[*index].clone()),
    }
}

struct Wiring {
    blocks: [Vec<leaf::Block>; 3],
    owners: Owners,
    spans: Vec<(usize, usize)>,
}

impl Wiring {
    fn new(layout: &Layout) -> Self {
        let public: Vec<Arc<Vec<F64>>> = layout
            .public_columns
            .iter()
            .map(|column| Arc::new(column.iter().copied().map(F64).collect()))
            .collect();
        Self {
            blocks: core::array::from_fn(|side| {
                layout.blocks[side]
                    .iter()
                    .map(|block| leaf::Block {
                        kappa: block.log_rows,
                        coords: block
                            .coordinates
                            .iter()
                            .map(|coord| coordinate(coord, &public))
                            .collect(),
                    })
                    .collect()
            }),
            owners: core::array::from_fn(|side| {
                layout.blocks[side]
                    .iter()
                    .map(|block| block.owner.map(|table| (table, layout.bases[table])))
                    .collect()
            }),
            spans: layout
                .tables
                .iter()
                .enumerate()
                .map(|(table, spec)| (layout.bases[table], spec.circuit.raw_columns.len()))
                .collect(),
        }
    }
}

fn power(mut value: F192, mut exponent: usize) -> F192 {
    let mut result = F192::ONE;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result *= value;
        }
        exponent >>= 1;
        if exponent != 0 {
            value *= value;
        }
    }
    result
}

fn form_powers(layout: &Layout, eta: F192) -> [F192; 3] {
    let first = power(eta, layout.tables.iter().map(|table| table.relations.len()).sum());
    let second = first * eta;
    [first, second, second * eta]
}

// Compile the random linear combination once, rather than allocating converted
// SDK field rows or interpreting every identity at every sumcheck node. K rows
// stay in K; extension rows retain all three limbs. Sorting products also merges
// the repeated monomials introduced by bus coefficient expansion.
fn airs(
    layout: &Layout,
    forms: &[Vec<leaf::BusForm>; 3],
    eta: F192,
    shared: [F192; 3],
) -> Vec<constraints::Air<'static>> {
    let mut weight = F192::ONE;
    layout
        .tables
        .iter()
        .enumerate()
        .map(|(table, spec)| {
            let mut form = leaf::BusForm {
                coeffs: vec![F192::ZERO; spec.circuit.raw_columns.len()],
                prods: Vec::new(),
                constant: F192::ZERO,
            };
            for relation in &spec.relations {
                relation.accumulate(&mut form, weight);
                weight *= eta;
            }
            for side in 0..3 {
                let bus = &forms[side][table];
                for (coefficient, &value) in form.coeffs.iter_mut().zip(&bus.coeffs) {
                    *coefficient += shared[side] * value;
                }
                form.constant += shared[side] * bus.constant;
                form.prods
                    .extend(bus.prods.iter().map(|&(a, b, value)| (a, b, shared[side] * value)));
            }
            for (a, b, _) in &mut form.prods {
                if *a > *b {
                    core::mem::swap(a, b);
                }
            }
            form.prods.sort_unstable_by_key(|&(a, b, _)| (a, b));
            let mut length = 0;
            for index in 0..form.prods.len() {
                let (a, b, coefficient) = form.prods[index];
                if length != 0 && (form.prods[length - 1].0, form.prods[length - 1].1) == (a, b) {
                    form.prods[length - 1].2 += coefficient;
                } else {
                    form.prods[length] = (a, b, coefficient);
                    length += 1;
                }
            }
            form.prods.truncate(length);
            form.prods.retain(|&(_, _, coefficient)| coefficient != F192::ZERO);
            let form = Arc::new(form);
            let form_k = form.clone();
            constraints::Air {
                tau: layout.table_tau(table),
                n_cols: spec.circuit.raw_columns.len(),
                n_constraints: spec.relations.len(),
                eval: Box::new(move |_, values, quadratic| {
                    <F192 as ColVal>::reduce(form.eval_unreduced(values, quadratic))
                }),
                eval_k: Box::new(move |_, values, quadratic| {
                    <F64 as ColVal>::reduce(form_k.eval_unreduced(values, quadratic))
                }),
            }
        })
        .collect()
}

fn finish_claims(layout: &Layout, bus: Vec<leaf::ColumnClaim>, tables: &[constraints::Claims]) -> Vec<pcs::SlotClaim> {
    let locate = |column: usize, point, value| pcs::SlotClaim::Point {
        offset: layout.placements[column].offset,
        low_point: point,
        value,
    };
    let mut claims = Vec::with_capacity(
        bus.len()
            + layout
                .tables
                .iter()
                .map(|table| table.circuit.raw_columns.len())
                .sum::<usize>(),
    );
    claims.extend(bus.into_iter().map(|claim| locate(claim.col, claim.point, claim.value)));
    for (table, claim) in tables.iter().enumerate() {
        claims.extend(
            claim
                .evals
                .iter()
                .enumerate()
                .map(|(column, &value)| locate(layout.bases[table] + column, claim.chi.clone(), value)),
        );
    }
    if let Some(column) = layout.flock_column {
        let table = layout
            .table_ids
            .iter()
            .position(|&id| id == cpu_tables::BLAKE_TABLE)
            .unwrap();
        let claim = &tables[table];
        for &(dense, slot) in &layout.tables[table].flock_slots {
            claims.push(pcs::SlotClaim::Strided {
                offset: layout.placements[column].offset,
                slot,
                stride_log: hash_flock::SLOT_STRIDE_LOG,
                point: claim.chi.clone(),
                value: claim.evals[dense],
            });
        }
    }
    claims
}

fn packed_ring(layout: &Layout, table: usize, claims: Vec<BitClaim>) -> Result<pcs::RingSwitchOpen, Error> {
    let placement = layout.placements[layout.packed_columns[table]];
    let qflock_vars = placement.log_rows.ok_or(Error::InvalidShape)?;
    let mut converted = Vec::with_capacity(claims.len());
    for claim in claims {
        if claim.point.len() != qflock_vars || claim.slices.len() != 64 {
            return Err(Error::InvalidProof);
        }
        let field = |v: leanvm_guest::Field| F192::new(v.0[0], v.0[1], v.0[2]);
        converted.push(pcs::RingSwitchClaim {
            suffix_point: claim.point.into_iter().map(field).collect(),
            s_hat_v: Some(claim.slices.into_iter().map(field).collect()),
        });
    }
    Ok(pcs::RingSwitchOpen {
        offset: placement.offset,
        qflock_vars,
        claims: converted,
    })
}

fn ring_verifiers(rings: &[pcs::RingSwitchOpen]) -> Vec<pcs::RingSwitchVerify<'_>> {
    rings
        .iter()
        .map(|ring| pcs::RingSwitchVerify {
            offset: ring.offset,
            qflock_vars: ring.qflock_vars,
            claims: ring
                .claims
                .iter()
                .map(|claim| pcs::RingSwitchVerifyClaim {
                    suffix_point: &claim.suffix_point,
                    s_hat_v: claim.s_hat_v.as_deref().unwrap().try_into().unwrap(),
                })
                .collect(),
        })
        .collect()
}

struct ExecutionCounts {
    tables: [u64; cpu_tables::TABLE_COUNT],
    ram: u64,
    error: Option<Error>,
}

impl Default for ExecutionCounts {
    fn default() -> Self {
        Self {
            tables: [0; cpu_tables::TABLE_COUNT],
            ram: 0,
            error: None,
        }
    }
}

impl ExecutionCounts {
    fn record(&mut self, step: &riscv::Step) -> Result<(), Error> {
        use crate::instruction::Opcode;
        let table = match step.ecall {
            Some(riscv::Ecall::Exit) => cpu_tables::EXIT_TABLE,
            Some(riscv::Ecall::ReadWitness { length, .. }) => {
                self.tables[cpu_tables::WITNESS_BYTE_TABLE] = self.tables[cpu_tables::WITNESS_BYTE_TABLE]
                    .checked_add(length)
                    .ok_or(Error::InvalidShape)?;
                cpu_tables::WITNESS_TABLE
            }
            Some(riscv::Ecall::ReadPublic) => cpu_tables::PUBLIC_TABLE,
            Some(riscv::Ecall::Blake2s) => cpu_tables::BLAKE_TABLE,
            Some(riscv::Ecall::F192Mul) => cpu_tables::FIELD_TABLE,
            None => Opcode::decode(step.instruction).ok_or(Error::InvalidExecution)? as usize,
        };
        let count = self.tables.get_mut(table).ok_or(Error::InvalidExecution)?;
        *count = count.checked_add(1).ok_or(Error::InvalidShape)?;
        self.ram = self
            .ram
            .checked_add(step.memory.len() as u64)
            .ok_or(Error::InvalidShape)?;
        Ok(())
    }
}

impl Extend<riscv::Step> for ExecutionCounts {
    fn extend<I: IntoIterator<Item = riscv::Step>>(&mut self, steps: I) {
        for step in steps {
            if self.error.is_none()
                && let Err(error) = self.record(&step)
            {
                self.error = Some(error);
            }
        }
    }
}

fn check_capacity(
    program: &ProgramInfo,
    public: [u8; 32],
    execution: &riscv::Execution<ExecutionCounts>,
) -> Result<(), Error> {
    use crate::{packed::PackedSpec, schema::SEP_REG};
    if let Some(error) = execution.steps.error {
        return Err(error);
    }
    let counts = execution.steps.tables;
    let ram_count = execution.steps.ram;
    let row_height = |count: u64| count.max(8).checked_next_power_of_two().ok_or(Error::InvalidShape);
    let table_words = |spec: &crate::schema::TableSpec, count: u64| -> Result<u64, Error> {
        let circuit = PackedSpec::new(spec).circuit;
        let width = circuit.raw_columns.len() as u64 + (1u64 << (circuit.k_log - 6));
        row_height(count)?.checked_mul(width).ok_or(Error::InvalidShape)
    };
    let rom_entries = program.rom_entries().len() as u64;
    let mut words = rom_entries
        .max(1)
        .checked_next_power_of_two()
        .ok_or(Error::InvalidShape)?;
    let mut register_count = 0u64;
    for (table, count) in counts.into_iter().enumerate().filter(|(_, count)| *count != 0) {
        let spec = cpu_tables::build_spec(public, execution.cycles, table);
        let registers = spec
            .flushes
            .iter()
            .filter(|flush| matches!(flush.push.first(), Some(Coord::Scaled(_, SEP_REG))))
            .count() as u64;
        register_count = register_count
            .checked_add(count.checked_mul(registers).ok_or(Error::InvalidShape)?)
            .ok_or(Error::InvalidShape)?;
        words = words
            .checked_add(table_words(&spec, count)?)
            .ok_or(Error::InvalidShape)?;
    }
    for (space, count) in [(Space::Ram, ram_count), (Space::Register, register_count)] {
        if count == 0 {
            continue;
        }
        let log = row_height(count)?.trailing_zeros() as usize;
        let (spec, _) = memory::build_spec(program, space, count, log)?;
        words = words
            .checked_add(table_words(&spec, count)?)
            .ok_or(Error::InvalidShape)?;
    }
    if counts[cpu_tables::BLAKE_TABLE] != 0 {
        words = words
            .checked_add(row_height(counts[cpu_tables::BLAKE_TABLE])? << hash_flock::SLOT_STRIDE_LOG)
            .ok_or(Error::InvalidShape)?;
    }
    let required_log = (64 - (words - 1).leading_zeros()).max(pcs::MIN_MU as u32);
    if required_log > pcs::MAX_MU as u32 {
        return Err(Error::Capacity {
            cycles: execution.cycles,
            required_log,
            max_log: pcs::MAX_MU as u32,
        });
    }
    Ok(())
}

/// Produce a native RV64IM SNARK and its public, verifier-derived dimensions.
/// The returned transport owns ordinary vectors and survives the arena phase.
pub fn prove(
    program: &riscv::Program,
    public: [u8; 32],
    witness: &[u8],
    max_cycles: u64,
    log_inv_rate: u8,
) -> Result<(Proof, VerifySummary), Error> {
    if max_cycles == 0 || !(1..=4).contains(&log_inv_rate) {
        return Err(Error::InvalidShape);
    }
    let program_info = ProgramInfo::from_elf(program.elf_bytes())?;
    let planned_cycles = {
        let plan = program
            .execute_with_trace(
                public,
                witness,
                max_cycles.min((1u64 << 32) - 1),
                ExecutionCounts::default(),
            )
            .map_err(|_| Error::InvalidExecution)?;
        if plan.cycles == 0 || plan.cycles >= 1u64 << 32 {
            return Err(Error::InvalidShape);
        }
        check_capacity(&program_info, public, &plan)?;
        plan.cycles
    };
    let execution = program
        .execute(public, witness, planned_cycles)
        .map_err(|_| Error::InvalidExecution)?;
    let mut rom = RomCounter::new(&program_info);
    let mut cpu = cpu_tables::build_rows(public, &execution, &mut rom)?;
    let cycles = execution.cycles;
    drop(execution);
    let mut ram_accesses = Vec::new();
    let mut register_accesses = Vec::new();
    for access in cpu.accesses.drain(..) {
        match access.space {
            Space::Ram => ram_accesses.push(access),
            Space::Register => register_accesses.push(access),
        }
    }
    if ram_accesses.len() as u64 > 1u64 << 32 || register_accesses.len() as u64 > 1u64 << 36 {
        return Err(Error::InvalidShape);
    }
    let (ram, ram_header, _) = memory::build_rows(&program_info, Space::Ram, &ram_accesses, &mut rom)?;
    drop(ram_accesses);
    let (registers, register_header, _) =
        memory::build_rows(&program_info, Space::Register, &register_accesses, &mut rom)?;
    drop(register_accesses);
    cpu.tables.extend([
        (!ram.rows.is_empty()).then_some(ram),
        (!registers.rows.is_empty()).then_some(registers),
    ]);
    let taus = cpu
        .tables
        .iter()
        .map(|table| {
            let Some(table) = table else {
                return Ok(ABSENT);
            };
            if table.rows.len() < 8 || !table.rows.len().is_power_of_two() {
                return Err(Error::InvalidShape);
            }
            Ok(table.rows.len().trailing_zeros() as usize)
        })
        .collect::<Result<Vec<_>, Error>>()?;
    let header = Header {
        cycles,
        log_inv_rate: log_inv_rate as usize,
        taus,
        ram: ram_header,
        registers: register_header,
    };
    let layout = Layout::new(&program_info, public, header)?;
    let result_summary = summary(&layout)?;
    let wiring = Wiring::new(&layout);
    let placements: Vec<Placement> = layout
        .placements
        .iter()
        .map(|placement| Placement {
            n_vars: placement.log_rows.unwrap(),
            offset: placement.offset,
        })
        .collect();
    let compressions: Vec<_> = cpu.blake.iter().map(cpu_tables::BlakeInput::compression).collect();
    let expected_blake = layout
        .flock_column
        .map_or(0, |_| 1usize << layout.header.taus[cpu_tables::BLAKE_TABLE]);
    if compressions.len() != expected_blake {
        return Err(Error::InvalidShape);
    }
    drop(cpu.blake);

    // Bind the guard before every arena-backed object. No nested phase is
    // entered by the native verifier below; raw proof storage is system-owned.
    let _phase = zk_alloc::enter_phase();
    // SAFETY: split_stack zeros the pad tail, and every committed window below
    // is filled in full before any reader (including the committer) sees q.
    let mut q = unsafe { witness::alloc_stack(shape(&layout)) };
    let prepared = {
        let mut windows = witness::split_stack(&mut q, &placements);
        for (output, &key) in windows[ROM_COUNTS].iter_mut().zip(&layout.public_columns[0]) {
            *output = F64(rom.final_count(key));
        }
        let prepared = layout
            .flock_column
            .map(|column| hash_flock::build_qflock_prepared(&compressions, windows[column]));
        for (table, &logical) in layout.table_ids.iter().enumerate() {
            let rows = cpu.tables[logical].as_ref().ok_or(Error::InvalidShape)?;
            let spec = &layout.tables[table];
            let columns = spec.circuit.raw_columns.len();
            let words = 1usize << (spec.circuit.k_log - 6);
            if rows.rows.len() != 1usize << layout.table_tau(table)
                || rows
                    .rows
                    .iter()
                    .any(|row| row.values.len() != columns || row.bits.len() != words)
            {
                return Err(Error::InvalidShape);
            }
            for column in 0..columns {
                let global = layout.bases[table] + column;
                for (output, row) in windows[global].iter_mut().zip(&rows.rows) {
                    *output = F64(row.values[column]);
                }
            }
            for (output, row) in windows[layout.packed_columns[table]]
                .chunks_exact_mut(words)
                .zip(&rows.rows)
            {
                for (word, &bits) in output.iter_mut().zip(&row.bits) {
                    *word = F64(bits);
                }
            }
        }
        prepared
    };
    drop(compressions);
    let mut ps = ProverState::new(digest_words(program_info.iv()), digest_words(public));
    for value in layout.header.values() {
        ps.add_scalar(F192::from(F64(value)));
    }
    let committed = pcs::commit(&mut ps, &q, shape(&layout), layout.header.log_inv_rate);
    let columns: Vec<&[F64]> = placements
        .iter()
        .map(|placement| &q[placement.offset..placement.offset + (1usize << placement.n_vars)])
        .collect();
    let bus = leaf::prove_balance(
        &wiring.blocks[0],
        &wiring.blocks[1],
        &wiring.blocks[2],
        &columns,
        &wiring.owners,
        &wiring.spans,
        &mut ps,
    );
    let eta = ps.sample();
    let shared = form_powers(&layout, eta);
    let sigma: Vec<F192> = (0..layout.tables.len())
        .map(|table| (0..3).fold(F192::ZERO, |sum, side| sum + shared[side] * bus.sigmas[side][table]))
        .collect();
    let table_columns: Vec<Vec<&[F64]>> = wiring
        .spans
        .iter()
        .map(|&(base, length)| columns[base..base + length].to_vec())
        .collect();
    let table_claims = constraints::prove(
        &airs(&layout, &bus.forms, eta, shared),
        &table_columns,
        eta,
        &bus.point,
        &sigma,
        &mut ps,
    );
    let slots = finish_claims(&layout, bus.claims, &table_claims);
    let mut rings = Vec::with_capacity(layout.tables.len() + usize::from(prepared.is_some()));
    for (table, claim) in table_claims.iter().enumerate() {
        let rows = cpu.tables[layout.table_ids[table]].take().ok_or(Error::InvalidShape)?;
        let reduced = packed_reduction::prove(
            &layout.tables[table],
            layout.table_tau(table),
            &rows.rows,
            &claim.chi,
            &claim.evals,
            &mut ps,
        )?;
        rings.push(packed_ring(&layout, table, reduced)?);
    }
    if let Some(prepared) = prepared {
        let reduced = prepared.prove(&mut ps);
        rings.push(hash_flock::ring_switch_open(
            prepared.n_blocks(),
            layout.placements[layout.flock_column.unwrap()].offset,
            &reduced,
        ));
    }
    pcs::open(&mut ps, &committed, &q, &slots, &rings);
    let compact = ps.into_proof();
    drop(table_columns);
    drop(columns);
    drop(q);
    drop(committed);
    let proof = native_verify(&program_info, public, &layout, &wiring, &compact)?;
    Ok((proof, result_summary))
}

/// Replay only public protocol data, both to reject any invalid local/bus/Flock
/// claim and to expand authenticated compact Merkle openings. The layout came
/// from the public program and announced header; no trace enters this function.
fn native_verify(
    program: &ProgramInfo,
    public: [u8; 32],
    layout: &Layout,
    wiring: &Wiring,
    proof: &lean_vm::transcript::Proof,
) -> Result<Proof, Error> {
    let mut vs = VerifierState::new(digest_words(program.iv()), proof, digest_words(public));
    for expected in layout.header.values() {
        if vs.next_scalar().map_err(|_| Error::InvalidProof)? != F192::from(F64(expected)) {
            return Err(Error::InvalidProof);
        }
    }
    let root = pcs::read_commitment(&mut vs).map_err(|_| Error::InvalidProof)?;
    let bus = leaf::verify_balance(
        &wiring.blocks[0],
        &wiring.blocks[1],
        &wiring.blocks[2],
        &wiring.owners,
        &wiring.spans,
        &mut vs,
    )
    .map_err(|_| Error::InvalidProof)?;
    let eta = vs.sample();
    let shared = form_powers(layout, eta);
    let target = (0..3).fold(F192::ZERO, |sum, side| sum + shared[side] * bus.totals[side]);
    let table_claims = constraints::verify(&airs(layout, &bus.forms, eta, shared), eta, &bus.point, target, &mut vs)
        .map_err(|_| Error::InvalidProof)?;
    let slots = finish_claims(layout, bus.claims, &table_claims);
    let mut rings = Vec::with_capacity(layout.tables.len() + usize::from(layout.flock_column.is_some()));
    for (table, claim) in table_claims.iter().enumerate() {
        let reduced = packed_reduction::verify_native(
            &layout.tables[table],
            layout.table_tau(table),
            &claim.chi,
            &claim.evals,
            &mut vs,
        )?;
        rings.push(packed_ring(layout, table, reduced)?);
    }
    let blake_replay = if layout.flock_column.is_some() {
        let n_blocks = 1usize << layout.header.taus[cpu_tables::BLAKE_TABLE];
        Some(hash_flock::verify_reduction(n_blocks, &mut vs).map_err(|_| Error::InvalidProof)?)
    } else {
        None
    };
    let mut verify_rings = ring_verifiers(&rings);
    if let Some(replay) = &blake_replay {
        let n_blocks = 1usize << layout.header.taus[cpu_tables::BLAKE_TABLE];
        verify_rings.push(hash_flock::ring_switch_verify(
            n_blocks,
            layout.placements[layout.flock_column.unwrap()].offset,
            &replay.claim,
        ));
    }
    pcs::verify(
        &mut vs,
        &slots,
        &verify_rings,
        shape(layout),
        layout.header.log_inv_rate,
        &root,
    )
    .map_err(|_| Error::InvalidProof)?;
    vs.finish().map_err(|_| Error::InvalidProof)?;
    let raw = vs.into_raw_proof();
    Ok(Proof {
        stream: raw
            .stream
            .into_iter()
            .map(|value| leanvm_guest::Field::new(value.c0, value.c1, value.c2))
            .collect(),
        merkle: raw
            .merkle
            .into_iter()
            .map(|opening| Opening {
                leaf: opening.leaf_data.into_iter().map(|word| word.0).collect(),
                siblings: opening.path,
            })
            .collect(),
    })
}
