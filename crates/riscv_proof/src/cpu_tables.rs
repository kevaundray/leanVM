//! Native instruction, syscall, and variable-length witness-copy tables.
//! All architectural effects are emitted on the chronological state buses.
#[cfg(feature = "host")]
use crate::{
    Error,
    schema::{Access, InputValues, RomCounter, Space, TableRows},
};
use crate::{
    circuit::{Bit, Circuit},
    instruction::{InstructionCircuit, Opcode},
    schema::{Coord, Flush, PublicSource, SEP_CPU, SEP_RAM, SEP_REG, SEP_ROM, SEP_SYSCALL, TableSpec},
};
use alloc::{vec, vec::Vec};

pub const EXIT_TABLE: usize = 63;
pub const WITNESS_TABLE: usize = 64;
pub const PUBLIC_TABLE: usize = 65;
pub const BLAKE_TABLE: usize = 66;
pub const FIELD_TABLE: usize = 67;
pub const WITNESS_BYTE_TABLE: usize = 68;
pub const TABLE_COUNT: usize = 69;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableKind {
    Instruction(Opcode),
    Exit,
    ReadWitness,
    ReadPublic,
    Blake2s,
    F192Mul,
    WitnessByte,
}

pub fn table_kinds() -> Vec<TableKind> {
    let mut kinds: Vec<_> = Opcode::ALL
        .into_iter()
        .filter(|&op| op != Opcode::Ecall)
        .map(TableKind::Instruction)
        .collect();
    kinds.extend([
        TableKind::Exit,
        TableKind::ReadWitness,
        TableKind::ReadPublic,
        TableKind::Blake2s,
        TableKind::F192Mul,
        TableKind::WitnessByte,
    ]);
    kinds
}

#[derive(Clone, Copy)]
enum Source {
    Enabled,
    Cycle,
    Public(u64),
    Rom,
    Register(usize),
    OldDestination,
    Before(usize),
    After(usize),
    FieldProduct(usize),
    Index,
    Length,
    Destination,
}
struct Input {
    source: Source,
    width: usize,
}
struct Event {
    ram: bool,
    address: Coord,
    time: usize,
    before: usize,
    after: usize,
    write: bool,
}
struct Template {
    kind: TableKind,
    instruction: Option<InstructionCircuit>,
    spec: TableSpec,
    inputs: Vec<Input>,
    events: Vec<Event>,
    enabled: Bit,
}

fn input(t: &mut Template, source: Source, width: usize) -> Vec<Bit> {
    t.inputs.push(Input { source, width });
    t.spec.circuit.input_word(width)
}
fn packed_input(t: &mut Template, source: Source, width: usize) -> (Vec<Bit>, usize) {
    let bits = input(t, source, width);
    let packed = t.spec.circuit.pack(&bits);
    (bits, packed)
}
fn enabled_assert(c: &mut Circuit, enabled: Bit, predicate: Bit) {
    let bad = c.not(predicate);
    let bad = c.and(enabled, bad);
    c.assert_equal(bad, Circuit::ZERO);
}
fn enabled_zero(c: &mut Circuit, enabled: Bit, bits: &[Bit]) {
    for &bit in bits {
        let bad = c.and(enabled, bit);
        c.assert_equal(bad, Circuit::ZERO);
    }
}
fn gated(e: Bit, value: Coord) -> Coord {
    match value {
        Coord::Constant(k) => Coord::Scaled(e.index(), k),
        Coord::Column(i) => Coord::Product(e.index(), i, 1),
        _ => unreachable!("gate only affine coordinates"),
    }
}
fn tuple(e: Bit, values: Vec<Coord>) -> Vec<Coord> {
    values.into_iter().map(|v| gated(e, v)).collect()
}
fn state(t: &mut Template, push: Vec<Coord>, pull: Vec<Coord>) {
    t.spec.flushes.push(Flush {
        push: tuple(t.enabled, push),
        pull: tuple(t.enabled, pull),
        count: None,
    });
}
fn constant(c: &mut Circuit, value: u64, width: usize) -> usize {
    c.pack(&c.constant(value, width))
}
fn timestamp(c: &mut Circuit, cycle: &[Bit], slot: &[Bit]) -> usize {
    let mut bits = slot.to_vec();
    bits.extend_from_slice(cycle);
    c.pack(&bits)
}
// Addresses are already enabled and may be quadratic; never gate them twice.
fn event(t: &mut Template, ram: bool, address: Coord, time: usize, before: usize, after: usize, write: bool) {
    let push = vec![
        gated(t.enabled, Coord::Constant(if ram { SEP_RAM } else { SEP_REG })),
        address.clone(),
        gated(t.enabled, Coord::Column(time)),
        gated(t.enabled, Coord::Column(before)),
        gated(t.enabled, Coord::Column(after)),
        gated(t.enabled, Coord::Constant(write as u64)),
    ];
    t.spec.flushes.push(Flush {
        push,
        pull: vec![Coord::Constant(0); 6],
        count: None,
    });
    t.events.push(Event {
        ram,
        address,
        time,
        before,
        after,
        write,
    });
}
fn register(t: &mut Template, cycle: &[Bit], slot: u64, address: usize, before: usize, after: usize, write: bool) {
    let slot = t.spec.circuit.constant(slot, 4);
    let time = timestamp(&mut t.spec.circuit, cycle, &slot);
    event(
        t,
        false,
        gated(t.enabled, Coord::Column(address)),
        time,
        before,
        after,
        write,
    );
}
fn ram(t: &mut Template, cycle: &[Bit], slot: &[Bit], address: &[Bit], before: usize, after: usize, write: bool) {
    enabled_zero(&mut t.spec.circuit, t.enabled, &address[32..]);
    let address = t.spec.circuit.pack(address);
    ram_at(
        t,
        cycle,
        slot,
        gated(t.enabled, Coord::Column(address)),
        before,
        after,
        write,
    );
}
fn ram_at(t: &mut Template, cycle: &[Bit], slot: &[Bit], address: Coord, before: usize, after: usize, write: bool) {
    let time = timestamp(&mut t.spec.circuit, cycle, slot);
    event(t, true, address, time, before, after, write);
}
fn address_region(t: &mut Template, address: &[Bit], width: usize) -> Vec<Coord> {
    let c = &mut t.spec.circuit;
    let e = t.enabled;
    enabled_zero(c, e, &address[32..]);
    if width == 1 {
        return vec![gated(e, Coord::Column(c.pack(address)))];
    }
    let k = (usize::BITS - (width - 1).leading_zeros()) as usize;
    let low = &address[..k];
    let high = &address[k..32];
    let (next_high, overflow) = c.add_carry(high, &c.constant(1, high.len()), Circuit::ZERO);
    let delta: Vec<_> = high.iter().zip(&next_high).map(|(&a, &b)| c.xor(a, b)).collect();
    let high = c.pack(high);
    let delta = c.pack(&delta);
    (0..width)
        .map(|offset| {
            let (sum, carry) = c.add_carry(low, &c.constant(offset as u64, k), Circuit::ZERO);
            if offset == width - 1 {
                // The region crosses RAM_END exactly when both halves carry.
                let overflow = c.and(carry, overflow);
                enabled_zero(c, e, &[overflow]);
            }
            let low = c.pack(&sum);
            let masked_carry = c.and(e, carry);
            Coord::Sum(vec![
                Coord::Product(e.index(), low, 1),
                Coord::Product(e.index(), high, 1 << k),
                Coord::Product(masked_carry.index(), delta, 1 << k),
            ])
        })
        .collect()
}
fn cycle(t: &mut Template, total: u64) -> (Vec<Bit>, usize, usize) {
    t.enabled = input(t, Source::Enabled, 1)[0];
    let (bits, packed) = packed_input(t, Source::Cycle, 32);
    // Public values enter only the enabled field relation, never Boolean
    // constant folding; packing retains the alias to these input bits.
    let (bound, bound_col) = packed_input(t, Source::Public(total), 32);
    t.spec.relations.push(Coord::Sum(vec![
        gated(t.enabled, Coord::Column(bound_col)),
        Coord::PublicScaled(t.enabled.index(), PublicSource::Cycles, total),
    ]));
    let wide = t.spec.circuit.extend(&bits, 64, false);
    let bound = t.spec.circuit.extend(&bound, 64, false);
    let valid = t.spec.circuit.less_than(&wide, &bound, false);
    enabled_assert(&mut t.spec.circuit, t.enabled, valid);
    let one = t.spec.circuit.constant(1, 64);
    let next = t.spec.circuit.add(&wide, &one);
    let next = t.spec.circuit.pack(&next);
    (bits, packed, next)
}
fn fetch(t: &mut Template, ins: &InstructionCircuit) {
    let (_, count) = packed_input(t, Source::Rom, 64);
    // InstructionCircuit bounds PC to 32 bits before this field-scaled tag.
    let prefix = vec![
        Coord::Scaled(t.enabled.index(), SEP_ROM),
        Coord::Sum(vec![
            Coord::Product(t.enabled.index(), ins.pc, 2),
            Coord::Scaled(t.enabled.index(), 1),
        ]),
    ];
    let mut push = prefix.clone();
    let mut pull = prefix;
    // Disabled lookups preserve their nonzero count on both sides.
    push.push(Coord::Sum(vec![
        Coord::Column(count),
        Coord::Product(t.enabled.index(), count, 3),
    ]));
    pull.push(Coord::Column(count));
    push.push(gated(t.enabled, Coord::Column(ins.raw)));
    pull.push(gated(t.enabled, Coord::Column(ins.raw)));
    t.spec.flushes.push(Flush {
        push,
        pull,
        count: Some(Coord::Column(count)),
    });
}

fn instruction_template(public: [u8; 32], total: u64, kind: TableKind) -> Template {
    let op = if let TableKind::Instruction(op) = kind {
        op
    } else {
        Opcode::Ecall
    };
    let ins = InstructionCircuit::build(op);
    let mut t = Template {
        kind,
        instruction: None,
        spec: TableSpec::new(ins.circuit.clone()),
        inputs: Vec::new(),
        events: Vec::new(),
        enabled: Circuit::ZERO,
    };
    let (cycle_bits, cycle_col, next_cycle) = cycle(&mut t, total);
    fetch(&mut t, &ins);
    let exit = kind == TableKind::Exit;
    state(
        &mut t,
        vec![
            Coord::Constant(SEP_CPU),
            if exit {
                Coord::Constant(0)
            } else {
                Coord::Column(ins.next_pc)
            },
            Coord::Column(next_cycle),
            Coord::Constant(exit as u64),
        ],
        vec![
            Coord::Constant(SEP_CPU),
            Coord::Column(ins.pc),
            Coord::Column(cycle_col),
            Coord::Constant(0),
        ],
    );
    if matches!(kind, TableKind::Instruction(_)) {
        register(&mut t, &cycle_bits, 0, ins.rs1, ins.rs1_value, ins.rs1_value, false);
        register(&mut t, &cycle_bits, 1, ins.rs2, ins.rs2_value, ins.rs2_value, false);
        if let Some(value) = ins.rd_value {
            let (_, old) = packed_input(&mut t, Source::OldDestination, 64);
            register(&mut t, &cycle_bits, 2, ins.rd, old, value, true);
        }
        if let Some(base) = ins.memory_address_bits.as_ref() {
            let addresses = address_region(&mut t, base, ins.memory_bytes.len());
            for (i, (&byte, address)) in ins.memory_bytes.iter().zip(addresses).enumerate() {
                let before = if ins.memory_write {
                    packed_input(&mut t, Source::Before(i), 8).1
                } else {
                    byte
                };
                let slot = t.spec.circuit.constant(i as u64, 32);
                ram_at(&mut t, &cycle_bits, &slot, address, before, byte, ins.memory_write);
            }
        }
    } else {
        syscall(&mut t, public, &cycle_bits, cycle_col);
    }
    t.instruction = Some(ins);
    t
}

fn syscall(t: &mut Template, public: [u8; 32], cycle: &[Bit], cycle_col: usize) {
    let (number, argc) = match t.kind {
        TableKind::Exit => (0, 1),
        TableKind::ReadWitness => (1, 2),
        TableKind::ReadPublic => (2, 1),
        TableKind::Blake2s => (0x100, 4),
        TableKind::F192Mul => (0x101, 6),
        _ => unreachable!(),
    };
    let a7 = constant(&mut t.spec.circuit, 17, 5);
    let number = constant(&mut t.spec.circuit, number, 64);
    register(t, cycle, 0, a7, number, number, false);
    let mut args = Vec::new();
    let mut argcols = Vec::new();
    for i in 0..argc {
        let (bits, value) = packed_input(t, Source::Register(10 + i), 64);
        let address = constant(&mut t.spec.circuit, 10 + i as u64, 5);
        register(t, cycle, 1 + i as u64, address, value, value, false);
        args.push(bits);
        argcols.push(value);
    }
    if t.kind == TableKind::F192Mul {
        let terms: [&[(usize, usize)]; 3] = [
            &[(0, 0), (1, 2), (2, 1)],
            &[(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
            &[(0, 2), (1, 1), (2, 0), (2, 2)],
        ];
        for i in 0..3 {
            let output = packed_input(t, Source::FieldProduct(i), 64).1;
            let address = constant(&mut t.spec.circuit, 10 + i as u64, 5);
            register(t, cycle, 7 + i as u64, address, argcols[i], output, true);
            let mut equation = vec![Coord::Column(output)];
            equation.extend(
                terms[i]
                    .iter()
                    .map(|&(j, k)| Coord::Product(argcols[j], argcols[3 + k], 1)),
            );
            t.spec.relations.push(Coord::Sum(equation));
        }
        return;
    }
    let result = match t.kind {
        TableKind::Exit => {
            enabled_zero(&mut t.spec.circuit, t.enabled, &args[0]);
            constant(&mut t.spec.circuit, 0, 64)
        }
        TableKind::ReadWitness => {
            // A 64-bit length is retained; the byte loop supports every RAM-sized
            // copy, including length 2^32, without a smaller syscall cap.
            let (end, carry) = t.spec.circuit.add_carry(&args[0], &args[1], Circuit::ZERO);
            enabled_zero(&mut t.spec.circuit, t.enabled, &[carry]);
            let beyond_ram = t.spec.circuit.constant((1u64 << 32) + 1, 64);
            let valid = t.spec.circuit.less_than(&end, &beyond_ram, false);
            enabled_assert(&mut t.spec.circuit, t.enabled, valid);
            let state_at = |index| {
                vec![
                    Coord::Constant(SEP_SYSCALL),
                    Coord::Column(cycle_col),
                    index,
                    Coord::Column(argcols[1]),
                    Coord::Column(argcols[0]),
                ]
            };
            state(t, state_at(Coord::Constant(0)), state_at(Coord::Column(argcols[1])));
            argcols[1]
        }
        TableKind::ReadPublic => {
            let addresses = address_region(t, &args[0], public.len());
            for (i, (byte, address)) in public.into_iter().zip(addresses).enumerate() {
                let before = packed_input(t, Source::Before(i), 8).1;
                let after = packed_input(t, Source::Public(byte as u64), 8).1;
                t.spec.relations.push(Coord::Sum(vec![
                    gated(t.enabled, Coord::Column(after)),
                    Coord::PublicScaled(t.enabled.index(), PublicSource::Byte(i), byte as u64),
                ]));
                let slot = t.spec.circuit.constant(i as u64, 32);
                ram_at(t, cycle, &slot, address, before, after, true);
            }
            constant(&mut t.spec.circuit, 32, 64)
        }
        TableKind::Blake2s => {
            let ranges = &[(0, 64, false), (1, 32, false), (2, 16, false), (3, 32, true)];
            let mut groups = Vec::new();
            let mut slot_index = 0;
            for &(arg, size, write) in ranges {
                let mut bits = Vec::with_capacity(size * 8);
                let addresses = address_region(t, &args[arg], size);
                for address in addresses {
                    let (byte_bits, value) = packed_input(
                        t,
                        if write {
                            Source::After(slot_index)
                        } else {
                            Source::Before(slot_index)
                        },
                        8,
                    );
                    bits.extend_from_slice(&byte_bits);
                    let before = if write {
                        packed_input(t, Source::Before(slot_index), 8).1
                    } else {
                        value
                    };
                    let slot = t.spec.circuit.constant(slot_index as u64, 32);
                    ram_at(t, cycle, &slot, address, before, value, write);
                    slot_index += 1;
                }
                groups.push(
                    bits.chunks_exact(64)
                        .map(|word| t.spec.circuit.pack(word))
                        .collect::<Vec<_>>(),
                );
            }
            for (words, start) in groups.iter().zip([10, 0, 18, 4]) {
                t.spec
                    .flock_slots
                    .extend(words.iter().enumerate().map(|(i, &column)| (column, start + i)));
            }
            constant(&mut t.spec.circuit, 0, 64)
        }
        _ => unreachable!(),
    };
    let a0 = constant(&mut t.spec.circuit, 10, 5);
    register(t, cycle, 5, a0, argcols[0], result, true);
}

fn witness_byte_template(total: u64) -> Template {
    let mut t = Template {
        kind: TableKind::WitnessByte,
        instruction: None,
        spec: TableSpec::new(Circuit::default()),
        inputs: Vec::new(),
        events: Vec::new(),
        enabled: Circuit::ZERO,
    };
    let (cycle, cycle_col, _) = cycle(&mut t, total);
    let (index, index_col) = packed_input(&mut t, Source::Index, 32);
    let (length, length_col) = packed_input(&mut t, Source::Length, 64);
    let (destination, destination_col) = packed_input(&mut t, Source::Destination, 64);
    let wide_index = t.spec.circuit.extend(&index, 64, false);
    let valid = t.spec.circuit.less_than(&wide_index, &length, false);
    enabled_assert(&mut t.spec.circuit, t.enabled, valid);
    let one = t.spec.circuit.constant(1, 64);
    let next = t.spec.circuit.add(&wide_index, &one);
    let next_col = t.spec.circuit.pack(&next);
    let state_at = |i| {
        vec![
            Coord::Constant(SEP_SYSCALL),
            Coord::Column(cycle_col),
            Coord::Column(i),
            Coord::Column(length_col),
            Coord::Column(destination_col),
        ]
    };
    state(&mut t, state_at(next_col), state_at(index_col));
    let (address, carry) = t.spec.circuit.add_carry(&destination, &wide_index, Circuit::ZERO);
    enabled_zero(&mut t.spec.circuit, t.enabled, &[carry]);
    let before = packed_input(&mut t, Source::Before(0), 8).1;
    let after = packed_input(&mut t, Source::After(0), 8).1;
    ram(&mut t, &cycle, &index, &address, before, after, true);
    t
}
fn template(public: [u8; 32], cycles: u64, kind: TableKind) -> Template {
    if kind == TableKind::WitnessByte {
        witness_byte_template(cycles)
    } else {
        instruction_template(public, cycles, kind)
    }
}
fn templates(public: [u8; 32], cycles: u64) -> Vec<Template> {
    table_kinds()
        .into_iter()
        .map(|kind| template(public, cycles, kind))
        .collect()
}
/// Stable order is `table_kinds()`, independent of the private execution.
pub fn build_specs(public: [u8; 32], cycles: u64) -> Vec<TableSpec> {
    templates(public, cycles).into_iter().map(|t| t.spec).collect()
}

pub fn build_spec(public: [u8; 32], cycles: u64, table: usize) -> TableSpec {
    template(public, cycles, table_kinds()[table]).spec
}

#[cfg(feature = "host")]
#[derive(Clone, Debug)]
pub struct BlakeInput {
    pub message: [u8; 64],
    pub chaining_value: [u8; 32],
    pub metadata: [u8; 16],
}
#[cfg(feature = "host")]
impl BlakeInput {
    pub fn compression(&self) -> flock::hash::Compression {
        (
            core::array::from_fn(|i| u32::from_le_bytes(self.chaining_value[4 * i..4 * i + 4].try_into().unwrap())),
            core::array::from_fn(|i| u32::from_le_bytes(self.message[4 * i..4 * i + 4].try_into().unwrap())),
            u64::from_le_bytes(self.metadata[..8].try_into().unwrap()),
            u32::from_le_bytes(self.metadata[8..12].try_into().unwrap()),
            u32::from_le_bytes(self.metadata[12..].try_into().unwrap()),
        )
    }
    fn padding() -> Self {
        let (cv, msg, counter, f0, f1) = flock::hash::padding_block();
        let mut value = Self {
            message: [0; 64],
            chaining_value: [0; 32],
            metadata: [0; 16],
        };
        for (chunk, word) in value.message.chunks_exact_mut(4).zip(msg) {
            chunk.copy_from_slice(&word.to_le_bytes());
        }
        for (chunk, word) in value.chaining_value.chunks_exact_mut(4).zip(cv) {
            chunk.copy_from_slice(&word.to_le_bytes());
        }
        value.metadata[..8].copy_from_slice(&counter.to_le_bytes());
        value.metadata[8..12].copy_from_slice(&f0.to_le_bytes());
        value.metadata[12..].copy_from_slice(&f1.to_le_bytes());
        value
    }
    fn output(&self) -> [u8; 32] {
        let (cv, msg, counter, f0, f1) = self.compression();
        let words = flock::hash::blake2s_compress(&cv, &msg, counter, f0, f1);
        core::array::from_fn(|i| words[i / 4].to_le_bytes()[i % 4])
    }
}
#[cfg(feature = "host")]
pub struct CpuRows {
    pub tables: Vec<Option<TableRows>>,
    pub accesses: Vec<Access>,
    pub blake: Vec<BlakeInput>,
}

#[cfg(feature = "host")]
fn source_value(
    source: Source,
    step: Option<&riscv::Step>,
    cycle: u64,
    index: usize,
    rom_count: u64,
    padding: Option<&[u8]>,
    field_product: &[u64; 3],
) -> Result<u64, Error> {
    let byte = |i: usize, after: bool| -> Result<u64, Error> {
        if let Some(step) = step {
            let event = step.memory.get(index + i).ok_or(Error::InvalidExecution)?;
            Ok(if after { event.after } else { event.before } as u64)
        } else {
            Ok(padding.and_then(|p| p.get(i)).copied().unwrap_or(0) as u64)
        }
    };
    let register = |i: usize| -> Result<u64, Error> {
        match step {
            Some(step) => step.register_before(i).ok_or(Error::InvalidExecution),
            None => Ok(0),
        }
    };
    Ok(match source {
        Source::Enabled => step.is_some() as u64,
        Source::Cycle => cycle,
        Source::Public(value) => {
            if step.is_some() {
                value
            } else {
                0
            }
        }
        Source::Rom => rom_count,
        Source::Register(i) => register(i)?,
        Source::OldDestination => register(step.map_or(0, |s| ((s.instruction >> 7) & 31) as usize))?,
        Source::Before(i) => byte(i, false)?,
        Source::After(i) => byte(i, true)?,
        Source::FieldProduct(i) => field_product[i],
        Source::Index => index as u64,
        Source::Length => register(11)?,
        Source::Destination => register(10)?,
    })
}
#[cfg(feature = "host")]
fn row(
    t: &Template,
    step: Option<&riscv::Step>,
    cycle: u64,
    index: usize,
    rom_count: u64,
    padding: Option<&[u8]>,
) -> Result<Vec<u64>, Error> {
    let mut inputs = InputValues(if let Some(ins) = &t.instruction {
        if let Some(step) = step {
            let mut load = [0; 8];
            let length = if ins.memory_write { 0 } else { ins.op.memory_width() };
            for (byte, event) in load[..length].iter_mut().zip(&step.memory) {
                *byte = event.before;
            }
            if step.memory.len() < length {
                return Err(Error::InvalidExecution);
            }
            let rs1 = step
                .register_before(((step.instruction >> 15) & 31) as usize)
                .ok_or(Error::InvalidExecution)?;
            let rs2 = step
                .register_before(((step.instruction >> 20) & 31) as usize)
                .ok_or(Error::InvalidExecution)?;
            ins.inputs(step.instruction, step.pc, rs1, rs2, &load[..length])
                .ok_or(Error::InvalidExecution)?
        } else {
            ins.canonical_inputs()
        }
    } else {
        Vec::new()
    });
    let field_product = if let (TableKind::F192Mul, Some(step)) = (t.kind, step) {
        use primitives::field::F192;
        let register = |i| step.register_before(i).ok_or(Error::InvalidExecution);
        let lhs = F192::new(register(10)?, register(11)?, register(12)?);
        let rhs = F192::new(register(13)?, register(14)?, register(15)?);
        let result = lhs * rhs;
        [result.c0, result.c1, result.c2]
    } else {
        [0; 3]
    };
    for input in &t.inputs {
        inputs.word(
            source_value(input.source, step, cycle, index, rom_count, padding, &field_product)?,
            input.width,
        );
    }
    t.spec.circuit.witness(&inputs.0).ok_or(Error::InvalidShape)
}
#[cfg(feature = "host")]
fn accesses(t: &Template, row: &[u64], out: &mut Vec<Access>) {
    if row[t.enabled.index()] == 0 {
        return;
    }
    out.extend(t.events.iter().map(|e| Access {
        space: if e.ram { Space::Ram } else { Space::Register },
        address: e.address.eval_raw(row).0[0],
        time: row[e.time],
        before: row[e.before],
        after: row[e.after],
        write: e.write,
    }));
}

/// Build witnesses, never verify by replay. The polynomials and buses remain
/// authoritative even when a caller supplies a fabricated interpreter trace.
#[cfg(feature = "host")]
pub fn build_rows(public: [u8; 32], execution: &riscv::Execution, rom: &mut RomCounter) -> Result<CpuRows, Error> {
    if execution.steps.is_empty()
        || execution.cycles != execution.steps.len() as u64
        || execution.cycles > (1u64 << 32)
        || execution.public != public
    {
        return Err(Error::InvalidExecution);
    }
    use crate::packed::{PackedRow, PackedSpec};
    let kinds = table_kinds();
    let mut builders: Vec<Option<(Template, PackedSpec, Vec<PackedRow>)>> = (0..TABLE_COUNT).map(|_| None).collect();
    let mut result = CpuRows {
        tables: Vec::new(),
        accesses: Vec::new(),
        blake: Vec::new(),
    };
    let mut exited = false;
    for (cycle, step) in execution.steps.iter().enumerate() {
        if exited {
            return Err(Error::InvalidExecution);
        }
        let op = Opcode::decode(step.instruction).ok_or(Error::Unsupported)?;
        let table = if op == Opcode::Ecall {
            match step.register_before(17).ok_or(Error::InvalidExecution)? {
                0 => {
                    exited = true;
                    EXIT_TABLE
                }
                1 => WITNESS_TABLE,
                2 => PUBLIC_TABLE,
                0x100 => BLAKE_TABLE,
                0x101 => FIELD_TABLE,
                _ => return Err(Error::Unsupported),
            }
        } else {
            Opcode::ALL
                .iter()
                .position(|&candidate| candidate == op)
                .ok_or(Error::Unsupported)?
        };
        let expected = match table {
            EXIT_TABLE | FIELD_TABLE => 0,
            WITNESS_TABLE => usize::try_from(step.register_before(11).ok_or(Error::InvalidExecution)?)
                .map_err(|_| Error::InvalidShape)?,
            PUBLIC_TABLE => 32,
            BLAKE_TABLE => 144,
            _ => op.memory_width(),
        };
        if step.memory.len() != expected || expected as u64 > (1u64 << 32) {
            return Err(Error::InvalidExecution);
        }
        if step.pc >= (1u64 << 32) || step.pc & 3 != 0 {
            return Err(Error::InvalidExecution);
        }
        let rom_count = rom.take((step.pc << 1) | 1)?;
        let (t, packing, rows) = builders[table].get_or_insert_with(|| {
            let t = template(public, execution.cycles, kinds[table]);
            let packing = PackedSpec::new(&t.spec);
            (t, packing, Vec::new())
        });
        let witness = row(t, Some(step), cycle as u64, 0, rom_count, None)?;
        accesses(t, &witness, &mut result.accesses);
        rows.push(packing.circuit.pack_row(&witness)?);
        if table == WITNESS_TABLE {
            for index in 0..expected {
                let (t, packing, rows) = builders[WITNESS_BYTE_TABLE].get_or_insert_with(|| {
                    let t = template(public, execution.cycles, TableKind::WitnessByte);
                    let packing = PackedSpec::new(&t.spec);
                    (t, packing, Vec::new())
                });
                let witness = row(t, Some(step), cycle as u64, index, 1, None)?;
                accesses(t, &witness, &mut result.accesses);
                rows.push(packing.circuit.pack_row(&witness)?);
            }
        }
        if table == BLAKE_TABLE {
            result.blake.push(BlakeInput {
                message: core::array::from_fn(|i| step.memory[i].before),
                chaining_value: core::array::from_fn(|i| step.memory[64 + i].before),
                metadata: core::array::from_fn(|i| step.memory[96 + i].before),
            });
        }
    }
    if !exited {
        return Err(Error::InvalidExecution);
    }
    let padding = BlakeInput::padding();
    let mut padding_bytes = Vec::with_capacity(144);
    padding_bytes.extend_from_slice(&padding.message);
    padding_bytes.extend_from_slice(&padding.chaining_value);
    padding_bytes.extend_from_slice(&padding.metadata);
    padding_bytes.extend_from_slice(&padding.output());
    for (table, builder) in builders.into_iter().enumerate() {
        let Some((t, packing, mut values)) = builder else {
            result.tables.push(None);
            continue;
        };
        let height = values.len().max(8).next_power_of_two();
        let dummy = row(
            &t,
            None,
            0,
            0,
            1,
            if table == BLAKE_TABLE {
                Some(&padding_bytes)
            } else {
                None
            },
        )?;
        values.resize(height, packing.circuit.pack_row(&dummy)?);
        if table == BLAKE_TABLE {
            result.blake.resize(height, padding.clone());
        }
        result.tables.push(Some(TableRows {
            spec: t.spec,
            packing,
            rows: values,
        }));
    }
    Ok(result)
}

#[cfg(all(test, feature = "host"))]
mod tests {
    use super::*;
    use crate::ProgramInfo;
    use leanvm_guest::Field;

    fn program_file_size(file_size: u64) -> ProgramInfo {
        let mut elf = vec![0u8; 0x110];
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
            (96, file_size),
            (104, 16),
            (112, 1),
        ] {
            elf[at..at + 8].copy_from_slice(&value.to_le_bytes());
        }
        elf[64..68].copy_from_slice(&1u32.to_le_bytes());
        elf[68..72].copy_from_slice(&5u32.to_le_bytes());
        elf[0x100] = 0x13;
        elf[0x10d] = 0x13;
        ProgramInfo::from_elf(&elf).unwrap()
    }
    fn step(raw: u32, number: u64, bytes: usize) -> riscv::Step {
        let operands = if raw == 0x73 {
            riscv::OperandValues::Ecall {
                a0: 0,
                a1: 0,
                a2: 0,
                a3: 0,
                a4: 0,
                a5: 0,
                number,
            }
        } else {
            riscv::OperandValues::Instruction { rs1: 0, rs2: 0, rd: 0 }
        };
        riscv::Step {
            pc: 0x1000,
            instruction: raw,
            next_pc: 0x1004,
            operands,
            memory: (0..bytes)
                .map(|i| riscv::MemoryEvent {
                    address: i as u64,
                    before: 0,
                    after: 0,
                    kind: riscv::AccessKind::Write,
                })
                .collect(),
            ecall: None,
            witness_offset_before: 0,
            witness_offset_after: 0,
        }
    }
    fn valid(t: &Template, row: &[u64]) -> bool {
        let fields: Vec<_> = row.iter().copied().map(Field::from).collect();
        (0..t.spec.constraints()).all(|i| t.spec.constraint(i, &fields, false) == Field::ZERO)
    }
    fn active(t: &Template, step: &riscv::Step, index: usize) -> Vec<u64> {
        row(t, Some(step), 0, index, 1, None).unwrap()
    }
    #[test]
    fn every_table_has_bus_disabled_valid_padding() {
        let padding = BlakeInput::padding();
        let bytes: Vec<_> = padding
            .message
            .into_iter()
            .chain(padding.chaining_value)
            .chain(padding.metadata)
            .chain(padding.output())
            .collect();
        for t in templates([0xa5; 32], u32::MAX as u64) {
            let values = row(
                &t,
                None,
                0,
                0,
                1,
                if t.kind == TableKind::Blake2s {
                    Some(&bytes)
                } else {
                    None
                },
            )
            .unwrap();
            assert!(valid(&t, &values), "{:?}", t.kind);
            let fields: Vec<_> = values.iter().copied().map(Field::from).collect();
            for flush in &t.spec.flushes {
                let push: Vec<_> = flush.push.iter().map(|v| v.eval(&fields, false)).collect();
                let pull: Vec<_> = flush.pull.iter().map(|v| v.eval(&fields, false)).collect();
                assert_eq!(push, pull, "{:?}", t.kind);
            }
        }
    }
    #[test]
    fn raw_opcode_destination_and_zero_register_are_bound() {
        let t = instruction_template([0; 32], 1, TableKind::Instruction(Opcode::Add));
        let raw = Opcode::Add.encoding().1 | (1 << 7) | (2 << 15) | (3 << 20);
        let mut s = step(raw, 0, 0);
        s.operands = riscv::OperandValues::Instruction { rs1: 11, rs2: 7, rd: 0 };
        let values = active(&t, &s, 0);
        assert!(valid(&t, &values));
        let mut events = Vec::new();
        accesses(&t, &values, &mut events);
        assert_eq!((events[2].address, events[2].after), (1, 18));
        let mut changed = values.clone();
        changed[t.instruction.as_ref().unwrap().rd] = 4;
        assert!(!valid(&t, &changed));
        s.instruction ^= 0x7000; // AND cannot inhabit an ADD row.
        assert!(!valid(&t, &active(&t, &s, 0)));
        s.instruction = raw & !(31 << 15);
        s.operands = riscv::OperandValues::Instruction { rs1: 1, rs2: 7, rd: 0 };
        assert!(!valid(&t, &active(&t, &s, 0)));
        s.operands = riscv::OperandValues::Instruction { rs1: 11, rs2: 7, rd: 0 };
        s.instruction = raw & !(31 << 7);
        let values = active(&t, &s, 0);
        assert!(valid(&t, &values));
        events.clear();
        accesses(&t, &values, &mut events);
        assert_eq!((events[2].address, events[2].after), (0, 0));
    }
    #[test]
    fn unavailable_syscall_arguments_reject_the_trace() {
        let t = instruction_template([0; 32], 1, TableKind::Exit);
        let mut s = step(0x73, 0, 0);
        s.operands = riscv::OperandValues::Instruction { rs1: 0, rs2: 0, rd: 0 };
        assert!(matches!(row(&t, Some(&s), 0, 0, 1, None), Err(Error::InvalidExecution)));
    }
    #[test]
    fn public_bytes_are_public_constraints_not_private_output_witnesses() {
        use crate::packed::PackedSpec;
        let t = instruction_template([0x91; 32], 1, TableKind::ReadPublic);
        let s = step(0x73, 2, 32);
        let values = active(&t, &s, 0);
        assert!(valid(&t, &values));
        let mut events = Vec::new();
        accesses(&t, &values, &mut events);
        let ram: Vec<_> = events
            .iter()
            .filter(|e| e.space == Space::Ram)
            .map(|e| (e.address, e.time, e.before, e.after, e.write))
            .collect();
        assert_eq!(ram, (0..32).map(|i| (i, i, 0, 0x91, true)).collect::<Vec<_>>());
        let other = instruction_template([0x90; 32], 1, TableKind::ReadPublic);
        assert!(!valid(&other, &values));
        let packing = PackedSpec::new(&other.spec);
        let packed = packing.circuit.pack_row(&values).unwrap();
        let fields: Vec<_> = packed.values.into_iter().map(Field::from).collect();
        assert!(
            packing
                .relations
                .iter()
                .any(|relation| relation.eval(&fields, false) != Field::ZERO)
        );
    }
    #[test]
    fn packed_boolean_topology_is_independent_of_public_values() {
        use crate::packed::PackedSpec;
        for kind in table_kinds() {
            let expected = PackedSpec::new(&template([0; 32], 1, kind).spec);
            for (public, cycles) in [([u8::MAX; 32], 1), ([0; 32], u32::MAX as u64)] {
                let actual = PackedSpec::new(&template(public, cycles, kind).spec);
                assert_eq!(actual.circuit.gates, expected.circuit.gates, "{kind:?}");
                assert_eq!(actual.circuit.aliases, expected.circuit.aliases, "{kind:?}");
                assert_eq!(actual.circuit.zero_pin, expected.circuit.zero_pin, "{kind:?}");
            }
        }
    }
    #[test]
    fn pinned_cycle_bound_rejects_forged_metadata() {
        use crate::packed::PackedSpec;
        let t = instruction_template([0; 32], 2, TableKind::ReadPublic);
        let s = step(0x73, 2, 32);
        assert!(valid(&t, &row(&t, Some(&s), 1, 0, 1, None).unwrap()));
        assert!(!valid(&t, &row(&t, Some(&s), 2, 0, 1, None).unwrap()));
        let forged = instruction_template([0; 32], 3, TableKind::ReadPublic);
        let values = row(&forged, Some(&s), 2, 0, 1, None).unwrap();
        assert!(valid(&forged, &values));
        // Raising the private bound repairs the comparison but cannot change
        // the verifier-derived expectation in the external relation.
        assert!(!valid(&t, &values));
        let packing = PackedSpec::new(&t.spec);
        let packed = packing.circuit.pack_row(&values).unwrap();
        let fields: Vec<_> = packed.values.into_iter().map(Field::from).collect();
        assert!(
            packing
                .relations
                .iter()
                .any(|relation| relation.eval(&fields, false) != Field::ZERO)
        );
    }
    #[test]
    fn contiguous_regions_preserve_misalignment_and_ram_boundaries() {
        const END: u64 = 1 << 32;
        for width in [1, 2, 3, 4, 8, 16, 32, 64] {
            let mut t = Template {
                kind: TableKind::ReadPublic,
                instruction: None,
                spec: TableSpec::new(Circuit::default()),
                inputs: Vec::new(),
                events: Vec::new(),
                enabled: Circuit::ZERO,
            };
            t.enabled = input(&mut t, Source::Enabled, 1)[0];
            let base = input(&mut t, Source::Destination, 64);
            let addresses = address_region(&mut t, &base, width);
            let make = |enabled: bool, base: u64| {
                let mut inputs = InputValues::default();
                inputs.bit(enabled);
                inputs.word(base, 64);
                t.spec.circuit.witness(&inputs.0).unwrap()
            };
            let alignment = width.next_power_of_two() as u64;
            let last = END - width as u64;
            for offset in 0..alignment {
                for base in [3 * alignment + offset, last - offset] {
                    let values = make(true, base);
                    assert!(valid(&t, &values), "{width} bytes at {base:#x}");
                    let fields: Vec<_> = values.iter().copied().map(Field::from).collect();
                    for (i, address) in addresses.iter().enumerate() {
                        let expected = Field::from(base + i as u64);
                        assert_eq!(address.eval(&fields, false), expected);
                        assert_eq!(address.eval_raw(&values), expected);
                    }
                }
            }
            for base in [last + 1, END, u64::MAX] {
                assert!(!valid(&t, &make(true, base)), "{width} bytes at {base:#x}");
                let disabled = make(false, base);
                assert!(valid(&t, &disabled));
                assert!(
                    addresses
                        .iter()
                        .all(|address| address.eval_raw(&disabled) == Field::ZERO)
                );
            }
        }
    }

    #[test]
    fn blake_overlapping_regions_keep_source_order() {
        let t = instruction_template([0; 32], 1, TableKind::Blake2s);
        let mut s = step(0x73, 0x100, 144);
        s.operands = riscv::OperandValues::Ecall {
            a0: 63,
            a1: 66,
            a2: 70,
            a3: 64,
            a4: 0,
            a5: 0,
            number: 0x100,
        };
        let mut slot = 0;
        for (base, width, write) in [(63, 64, false), (66, 32, false), (70, 16, false), (64, 32, true)] {
            for offset in 0..width {
                let address = base + offset;
                s.memory[slot] = riscv::MemoryEvent {
                    address,
                    before: address as u8,
                    after: if write { 255 - address as u8 } else { address as u8 },
                    kind: if write {
                        riscv::AccessKind::Write
                    } else {
                        riscv::AccessKind::Read
                    },
                };
                slot += 1;
            }
        }
        let values = active(&t, &s, 0);
        assert!(valid(&t, &values));
        let mut events = Vec::new();
        accesses(&t, &values, &mut events);
        let ram: Vec<_> = events.iter().filter(|event| event.space == Space::Ram).collect();
        assert_eq!(ram.len(), s.memory.len());
        for (slot, (actual, expected)) in ram.iter().zip(&s.memory).enumerate() {
            assert_eq!(
                (actual.address, actual.time, actual.before, actual.after, actual.write),
                (
                    expected.address,
                    slot as u64,
                    expected.before as u64,
                    expected.after as u64,
                    slot >= 112
                )
            );
        }
    }

    #[test]
    fn field_product_rejects_forged_output_and_integer_multiplication() {
        let t = instruction_template([0; 32], 1, TableKind::F192Mul);
        let mut s = step(0x73, 0x101, 0);
        let a = Field::new(u64::MAX, 7, 9);
        let b = Field::new(3, 11, 13);
        let product = a * b;
        s.operands = riscv::OperandValues::Ecall {
            a0: a.0[0],
            a1: a.0[1],
            a2: a.0[2],
            a3: b.0[0],
            a4: b.0[1],
            a5: b.0[2],
            number: 0x101,
        };
        let with_product = |result: Field| {
            let mut inputs = InputValues(
                t.instruction
                    .as_ref()
                    .unwrap()
                    .inputs(s.instruction, s.pc, 0, 0, &[])
                    .unwrap(),
            );
            for input in &t.inputs {
                inputs.word(
                    source_value(input.source, Some(&s), 0, 0, 1, None, &result.0).unwrap(),
                    input.width,
                );
            }
            t.spec.circuit.witness(&inputs.0).unwrap()
        };
        assert!(valid(&t, &with_product(product)));
        let mut forged = product;
        forged.0[0] ^= 1;
        assert!(!valid(&t, &with_product(forged)));
        forged.0[0] = u64::MAX.wrapping_mul(3);
        assert!(!valid(&t, &with_product(forged)));
    }
    #[test]
    fn witness_loop_allows_full_ram_length_but_not_terminal_or_wrapped_writes() {
        let t = witness_byte_template(1);
        // Avoid allocating a RAM-sized trace: provide loop inputs directly.
        let make = |index: u64, length: u64, dst: u64| {
            let mut inputs = InputValues::default();
            for (value, width) in [
                (1, 1),
                (0, 32),
                (1, 32),
                (index, 32),
                (length, 64),
                (dst, 64),
                (0, 8),
                (0x98, 8),
            ] {
                inputs.word(value, width);
            }
            t.spec.circuit.witness(&inputs.0).unwrap()
        };
        let values = make(u32::MAX as u64, 1 << 32, 0);
        assert!(valid(&t, &values));
        let fields: Vec<_> = values.iter().copied().map(Field::from).collect();
        assert_eq!(t.spec.flushes[0].push[2].eval(&fields, false), Field::from(1 << 32));
        assert!(!valid(&t, &make(0, 0, 0)));
        assert!(!valid(&t, &make(4, 4, 0)));
        assert!(!valid(&t, &make(u32::MAX as u64, 1 << 32, 1)));
        assert!(!valid(&t, &make(1, 2, u64::MAX)));
        let header = instruction_template([0; 32], 1, TableKind::ReadWitness);
        let s = step(0x73, 1, 0);
        let values = active(&header, &s, 0);
        assert!(valid(&header, &values));
        let fields: Vec<_> = values.iter().copied().map(Field::from).collect();
        let call = header.spec.flushes.iter().find(|f| f.push.len() == 5).unwrap();
        assert_eq!(
            call.push.iter().map(|v| v.eval(&fields, false)).collect::<Vec<_>>(),
            call.pull.iter().map(|v| v.eval(&fields, false)).collect::<Vec<_>>()
        );
        let mut out_of_bounds = s;
        out_of_bounds.operands = riscv::OperandValues::Ecall {
            a0: (1 << 32) + 1,
            a1: 0,
            a2: 0,
            a3: 0,
            a4: 0,
            a5: 0,
            number: 1,
        };
        assert!(!valid(&header, &active(&header, &out_of_bounds, 0)));
        out_of_bounds.operands = riscv::OperandValues::Ecall {
            a0: 1 << 32,
            a1: 0,
            a2: 0,
            a3: 0,
            a4: 0,
            a5: 0,
            number: 1,
        };
        assert!(valid(&header, &active(&header, &out_of_bounds, 0)));
    }
    #[test]
    fn executable_word_authenticates_partial_bss() {
        let program = program_file_size(1);
        let t = instruction_template([0; 32], 1, TableKind::Instruction(Opcode::Addi));
        let mut s = step(0x13, 0, 0);
        let values = active(&t, &s, 0);
        assert!(valid(&t, &values) && fetch_matches_rom(&program, &t, &values));
        s.instruction |= 1 << 20;
        let forged = active(&t, &s, 0);
        assert!(valid(&t, &forged));
        assert!(!fetch_matches_rom(&program, &t, &forged));
    }
    fn fetch_matches_rom(program: &ProgramInfo, t: &Template, row: &[u64]) -> bool {
        let fields: Vec<_> = row.iter().copied().map(Field::from).collect();
        let pull: Vec<_> = t.spec.flushes[0]
            .pull
            .iter()
            .map(|coord| coord.eval(&fields, false))
            .collect();
        program.rom_entries().into_iter().any(|(key, value)| {
            pull == [SEP_ROM, key, 1, value]
                .into_iter()
                .map(Field::from)
                .collect::<Vec<_>>()
        })
    }
    #[test]
    fn upper_pc_cannot_alias_an_authenticated_data_byte() {
        let program = program_file_size(16);
        let t = instruction_template([0; 32], 1, TableKind::Instruction(Opcode::Addi));
        let mut s = step(0x13, 0, 0);
        let values = active(&t, &s, 0);
        assert!(valid(&t, &values) && fetch_matches_rom(&program, &t, &values));
        s.pc |= 1 << 63;
        let forged = active(&t, &s, 0);
        // Reduction of the high PC bit makes its tagged key equal byte 0x100d.
        assert!(fetch_matches_rom(&program, &t, &forged));
        assert!(!valid(&t, &forged));
    }
}
