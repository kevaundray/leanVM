//! Immutable native-field table schemas and their witness columns.
//!
//! Every port has three private coefficient columns. Fixed column zero is the
//! row enable, followed by `(wire, push_counter, pull_counter)` for each port.
//! Outputs precede reads. Constants append three fixed coefficients; public
//! inputs append their fixed boundary index. Padding has zero fixed metadata.

use leanvm_guest::Field;
use primitives::field::F64;
use riscv_proof::schema::{Coord, Flush};

use crate::Error;
use crate::circuit::{Circuit, Operation, Wire};

const DATAFLOW_SEPARATOR: u64 = 128;
const PUBLIC_SEPARATOR: u64 = 256;
pub(crate) const KIND_COUNT: usize = 13;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(usize)]
pub(crate) enum TableKind {
    Constant,
    PublicInput,
    PrivateInput,
    Add,
    Mul,
    Inverse,
    Limb0,
    Limb1,
    Limb2,
    Compose,
    AssertEqual,
    AssertBool,
    Blake2s,
}

impl TableKind {
    pub(crate) const ALL: [Self; KIND_COUNT] = [
        Self::Constant,
        Self::PublicInput,
        Self::PrivateInput,
        Self::Add,
        Self::Mul,
        Self::Inverse,
        Self::Limb0,
        Self::Limb1,
        Self::Limb2,
        Self::Compose,
        Self::AssertEqual,
        Self::AssertBool,
        Self::Blake2s,
    ];

    fn ports(self) -> usize {
        match self {
            Self::Constant | Self::PublicInput | Self::PrivateInput | Self::AssertBool => 1,
            Self::Inverse | Self::Limb0 | Self::Limb1 | Self::Limb2 | Self::AssertEqual => 2,
            Self::Add | Self::Mul => 3,
            Self::Compose => 4,
            Self::Blake2s => 18,
        }
    }

    fn extra_fixed(self) -> usize {
        match self {
            Self::Constant => 3,
            Self::PublicInput => 1,
            _ => 0,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct NativeTable {
    pub kind: TableKind,
    pub log_rows: usize,
    pub fixed: Vec<Vec<F64>>,
    pub width: usize,
    pub relations: Vec<Coord>,
    pub flushes: Vec<Flush>,
    /// Absolute columns in `[fixed columns, private columns]` and Flock slots.
    pub flock_slots: Vec<(usize, usize)>,
    /// Circuit operation indices, in their original order within this kind.
    rows: Vec<usize>,
}

impl NativeTable {
    pub(crate) fn row_count(&self) -> usize {
        self.rows.len()
    }
}

fn kind(operation: &Operation) -> Result<TableKind, Error> {
    Ok(match operation {
        Operation::Input { public: true, .. } => TableKind::PublicInput,
        Operation::Input { public: false, .. } | Operation::HintBit { .. } => TableKind::PrivateInput,
        Operation::Constant { .. } => TableKind::Constant,
        Operation::Add { .. } => TableKind::Add,
        Operation::Mul { .. } => TableKind::Mul,
        Operation::Inverse { .. } => TableKind::Inverse,
        Operation::Limb { limb: 0, .. } => TableKind::Limb0,
        Operation::Limb { limb: 1, .. } => TableKind::Limb1,
        Operation::Limb { limb: 2, .. } => TableKind::Limb2,
        Operation::Limb { .. } => return Err(Error::InvalidCircuit),
        Operation::Compose { .. } => TableKind::Compose,
        Operation::AssertEqual { .. } => TableKind::AssertEqual,
        Operation::AssertBool { .. } => TableKind::AssertBool,
        Operation::Blake2s { .. } => TableKind::Blake2s,
    })
}

fn outputs(operation: &Operation, mut visit: impl FnMut(Wire)) {
    match operation {
        Operation::Input { output, .. }
        | Operation::Constant { output, .. }
        | Operation::Add { output, .. }
        | Operation::Mul { output, .. }
        | Operation::Inverse { output, .. }
        | Operation::Limb { output, .. }
        | Operation::Compose { output, .. }
        | Operation::HintBit { output, .. } => visit(*output),
        Operation::Blake2s { output, .. } => output.iter().copied().for_each(visit),
        Operation::AssertEqual { .. } | Operation::AssertBool { .. } => {}
    }
}

fn reads(operation: &Operation, mut visit: impl FnMut(Wire)) {
    match operation {
        Operation::Add { lhs, rhs, .. } | Operation::Mul { lhs, rhs, .. } | Operation::AssertEqual { lhs, rhs } => {
            visit(*lhs);
            visit(*rhs);
        }
        Operation::Inverse { input, .. } | Operation::Limb { input, .. } | Operation::AssertBool { input } => {
            visit(*input)
        }
        Operation::Compose { limbs, .. } => limbs.iter().copied().for_each(visit),
        Operation::Blake2s { input, .. } => input.iter().copied().for_each(visit),
        // A hint is free advice. Its source is authenticated by the builder's
        // recombination assertion, not by an unconstrained read on this row.
        Operation::Input { .. } | Operation::Constant { .. } | Operation::HintBit { .. } => {}
    }
}

fn ports(operation: &Operation, mut visit: impl FnMut(usize, Wire, bool)) {
    let mut port = 0;
    outputs(operation, |wire| {
        visit(port, wire, true);
        port += 1;
    });
    reads(operation, |wire| {
        visit(port, wire, false);
        port += 1;
    });
}

// Reduction modulo Y^3 + Y + 1, in the same tower basis as Field/F192.
const MUL_TERMS: [&[(usize, usize)]; 3] = [
    &[(0, 0), (1, 2), (2, 1)],
    &[(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
    &[(0, 2), (1, 1), (2, 0), (2, 2)],
];

fn product_terms(lhs: usize, rhs: usize, limb: usize) -> Vec<Coord> {
    MUL_TERMS[limb]
        .iter()
        .map(|&(i, j)| Coord::Product(lhs + i, rhs + j, 1))
        .collect()
}

pub(crate) fn schema(kind: TableKind) -> NativeTable {
    let port_count = kind.ports();
    let extra = 1 + 3 * port_count;
    let fixed_count = extra + kind.extra_fixed();
    let column = |port: usize, limb: usize| fixed_count + 3 * port + limb;
    let mut table = NativeTable {
        kind,
        log_rows: 0,
        fixed: (0..fixed_count).map(|_| Vec::new()).collect(),
        width: 3 * port_count,
        relations: Vec::new(),
        flushes: Vec::with_capacity(port_count + usize::from(kind == TableKind::PublicInput)),
        flock_slots: Vec::new(),
        rows: Vec::new(),
    };
    for port in 0..port_count {
        let metadata = 1 + 3 * port;
        let tuple = |counter| {
            let mut coordinates = vec![
                Coord::Scaled(0, DATAFLOW_SEPARATOR),
                Coord::Column(metadata),
                Coord::Column(counter),
            ];
            coordinates.extend((0..3).map(|limb| Coord::Product(0, column(port, limb), 1)));
            coordinates
        };
        table.flushes.push(Flush {
            push: tuple(metadata + 1),
            pull: tuple(metadata + 2),
            count: None,
        });
    }
    match kind {
        TableKind::Constant => {
            for limb in 0..3 {
                table.relations.push(Coord::Sum(vec![
                    Coord::Column(column(0, limb)),
                    Coord::Column(extra + limb),
                ]));
            }
        }
        TableKind::PublicInput => {
            let mut pull = vec![Coord::Scaled(0, PUBLIC_SEPARATOR), Coord::Column(extra)];
            pull.extend((0..3).map(|limb| Coord::Product(0, column(0, limb), 1)));
            table.flushes.push(Flush {
                push: vec![Coord::Constant(0); 5],
                pull,
                count: None,
            });
        }
        TableKind::PrivateInput => {}
        TableKind::Add => {
            for limb in 0..3 {
                table.relations.push(Coord::Sum(
                    (0..3).map(|port| Coord::Column(column(port, limb))).collect(),
                ));
            }
        }
        TableKind::Mul | TableKind::Inverse => {
            let (lhs, rhs) = if kind == TableKind::Mul { (1, 2) } else { (0, 1) };
            for limb in 0..3 {
                let mut terms = product_terms(column(lhs, 0), column(rhs, 0), limb);
                if kind == TableKind::Mul {
                    terms.push(Coord::Column(column(0, limb)));
                } else if limb == 0 {
                    // Padding has no inverse obligation; the active equation
                    // is a*b=1. No enable*a*b cubic gate is introduced.
                    terms.push(Coord::Column(0));
                }
                table.relations.push(Coord::Sum(terms));
            }
        }
        TableKind::Limb0 | TableKind::Limb1 | TableKind::Limb2 => {
            let limb = kind as usize - TableKind::Limb0 as usize;
            table.relations.push(Coord::Sum(vec![
                Coord::Column(column(0, 0)),
                Coord::Column(column(1, limb)),
            ]));
            table
                .relations
                .extend([Coord::Column(column(0, 1)), Coord::Column(column(0, 2))]);
        }
        TableKind::Compose => {
            for limb in 0..3 {
                table.relations.push(Coord::Sum(vec![
                    Coord::Column(column(0, limb)),
                    Coord::Column(column(limb + 1, 0)),
                ]));
                table
                    .relations
                    .extend([Coord::Column(column(limb + 1, 1)), Coord::Column(column(limb + 1, 2))]);
            }
        }
        TableKind::AssertEqual => {
            for limb in 0..3 {
                table.relations.push(Coord::Sum(vec![
                    Coord::Column(column(0, limb)),
                    Coord::Column(column(1, limb)),
                ]));
            }
        }
        TableKind::AssertBool => {
            // In characteristic two, (a0+a1*Y+a2*Y^2)^2+a reduces
            // to these three equations; cross terms cancel identically.
            let a = column(0, 0);
            table.relations.extend([
                Coord::Sum(vec![Coord::Product(a, a, 1), Coord::Column(a)]),
                Coord::Sum(vec![Coord::Product(a + 2, a + 2, 1), Coord::Column(a + 1)]),
                Coord::Sum(vec![
                    Coord::Product(a + 1, a + 1, 1),
                    Coord::Product(a + 2, a + 2, 1),
                    Coord::Column(a + 2),
                ]),
            ]);
        }
        TableKind::Blake2s => {
            for port in 0..18 {
                table
                    .relations
                    .extend([Coord::Column(column(port, 1)), Coord::Column(column(port, 2))]);
                let slot = match port {
                    0..=3 => 4 + port,
                    4..=11 => 10 + port - 4,
                    12..=15 => port - 12,
                    16..=17 => 18 + port - 16,
                    _ => unreachable!(),
                };
                table.flock_slots.push((column(port, 0), slot));
            }
        }
    }
    table
}

/// Compile only trusted circuit structure. Counters are powers of the primitive
/// base-field generator, assigned before grouping rows by their operation kind.
pub(crate) fn compile(circuit: &Circuit) -> Result<Vec<NativeTable>, Error> {
    // Even the conservative bound must stay strictly below ord(g)=2^64-1.
    // This also bounds every individual wire's read count and public index.
    let occurrences = circuit.operations().len().checked_mul(18).ok_or(Error::Capacity)?;
    if u64::try_from(occurrences).map_err(|_| Error::Capacity)? == u64::MAX {
        return Err(Error::Capacity);
    }
    let mut final_counters = vec![F64::ONE; circuit.wire_count()];
    let mut counts = [0usize; KIND_COUNT];
    let mut defined = 0;
    let mut public_inputs = 0;
    let mut private_inputs = 0;
    for operation in circuit.operations() {
        counts[kind(operation)? as usize] += 1;
        let mut valid = true;
        reads(operation, |wire| {
            if wire.index() >= defined {
                valid = false;
            } else {
                final_counters[wire.index()] *= F64::G;
            }
        });
        if let Operation::HintBit { input, bit, .. } = operation {
            valid &= input.index() < defined && *bit < 192;
        }
        if let Operation::Input { index, public, .. } = operation {
            let next = if *public {
                &mut public_inputs
            } else {
                &mut private_inputs
            };
            valid &= *index == *next;
            *next += 1;
        }
        outputs(operation, |wire| {
            valid &= wire.index() == defined && defined < circuit.wire_count();
            defined += 1;
        });
        if !valid {
            return Err(Error::InvalidCircuit);
        }
    }
    if defined != circuit.wire_count()
        || public_inputs != circuit.public_inputs()
        || private_inputs != circuit.private_inputs()
    {
        return Err(Error::InvalidCircuit);
    }

    let mut tables = Vec::with_capacity(KIND_COUNT);
    let mut indexes = [usize::MAX; KIND_COUNT];
    for kind in TableKind::ALL {
        if counts[kind as usize] != 0 {
            indexes[kind as usize] = tables.len();
            let count = counts[kind as usize];
            let size = count.max(8).checked_next_power_of_two().ok_or(Error::Capacity)?;
            let mut table = schema(kind);
            table.log_rows = size.trailing_zeros() as usize;
            table.rows = Vec::with_capacity(count);
            for column in &mut table.fixed {
                column.resize(size, F64::ZERO);
            }
            tables.push(table);
        }
    }
    let mut read_counters = vec![F64::ONE; circuit.wire_count()];
    let mut public_counter = F64::ONE;
    for (operation_index, operation) in circuit.operations().iter().enumerate() {
        let table = &mut tables[indexes[kind(operation)? as usize]];
        let row = table.rows.len();
        table.rows.push(operation_index);
        table.fixed[0][row] = F64::ONE;
        ports(operation, |port, wire, output| {
            let index = wire.index();
            let metadata = 1 + 3 * port;
            table.fixed[metadata][row] = F64(index as u64);
            if output {
                table.fixed[metadata + 1][row] = F64::ONE;
                table.fixed[metadata + 2][row] = final_counters[index];
            } else {
                let previous = read_counters[index];
                read_counters[index] *= F64::G;
                table.fixed[metadata + 1][row] = read_counters[index];
                table.fixed[metadata + 2][row] = previous;
            }
        });
        let extra = 1 + 3 * table.kind.ports();
        match operation {
            Operation::Constant { value, .. } => {
                for limb in 0..3 {
                    table.fixed[extra + limb][row] = F64(value.0[limb]);
                }
            }
            Operation::Input { public: true, .. } => {
                table.fixed[extra][row] = public_counter;
                public_counter *= F64::G;
            }
            _ => {}
        }
    }
    Ok(tables)
}

/// Materialize evaluated values verbatim, including incorrect outputs supplied
/// by adversarial callers. Only inactive BLAKE rows use a canonical Flock block.
pub(crate) fn witness(
    tables: &[NativeTable],
    circuit: &Circuit,
    values: &[Field],
    windows: &mut [Vec<&mut [F64]>],
) -> Result<(), Error> {
    if values.len() != circuit.wire_count() || windows.len() != tables.len() {
        return Err(Error::InvalidWitness);
    }
    for (table, columns) in tables.iter().zip(windows) {
        let size = 1usize.checked_shl(table.log_rows as u32).ok_or(Error::Capacity)?;
        if table.rows.len() > size
            || table.width != table.kind.ports() * 3
            || columns.len() != table.width
            || columns.iter().any(|column| column.len() != size)
        {
            return Err(Error::InvalidCircuit);
        }
        for column in columns.iter_mut() {
            column[table.rows.len()..].fill(F64::ZERO);
        }
        for (row, &operation_index) in table.rows.iter().enumerate() {
            let operation = circuit.operations().get(operation_index).ok_or(Error::InvalidCircuit)?;
            if kind(operation)? != table.kind {
                return Err(Error::InvalidCircuit);
            }
            ports(operation, |port, wire, _| {
                for limb in 0..3 {
                    columns[3 * port + limb][row] = F64(values[wire.index()].0[limb]);
                }
            });
        }
        if table.kind == TableKind::Blake2s && table.rows.len() < size {
            let block = flock::hash::padding_block();
            let output = flock::hash::blake2s_compress(&block.0, &block.1, block.2, block.3, block.4);
            let pack = |lo: u32, hi: u32| F64(u64::from(lo) | (u64::from(hi) << 32));
            for port in 0..18 {
                let word = match port {
                    0..=3 => pack(output[2 * port], output[2 * port + 1]),
                    4..=11 => pack(block.1[2 * (port - 4)], block.1[2 * (port - 4) + 1]),
                    12..=15 => pack(block.0[2 * (port - 12)], block.0[2 * (port - 12) + 1]),
                    16 => F64(block.2),
                    17 => pack(block.3, block.4),
                    _ => unreachable!(),
                };
                columns[3 * port][table.rows.len()..].fill(word);
            }
        }
    }
    Ok(())
}
