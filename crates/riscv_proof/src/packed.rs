//! Boolean circuits packed into GF(2) wires, with only bus-facing words kept
//! as physical base-field columns.

use crate::{
    Error,
    circuit::{Circuit, Gate},
    schema::{Coord, Flush, TableSpec},
};
use alloc::{vec, vec::Vec};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackedGate {
    Input,
    Zero,
    One,
    Xor(usize, usize),
    And(usize, usize),
}

#[derive(Clone, Debug)]
pub struct PackedRow {
    /// Consecutive wire bits, little-endian within each word.
    pub bits: Vec<u64>,
    /// Physical columns in `PackedCircuit::raw_columns` order.
    pub values: Vec<u64>,
}

#[derive(Clone, Debug)]
pub struct PackedCircuit {
    pub k_log: usize,
    /// The equality-failure accumulator, constrained to zero by lincheck.
    pub zero_pin: usize,
    /// The output wire of a gate is its index. Includes zero padding.
    pub gates: Vec<PackedGate>,
    /// Sorted dense-column to original-column mapping.
    pub raw_columns: Vec<usize>,
    /// Each physical column's GF(2)-linear projection of the packed wires.
    pub aliases: Vec<Vec<(usize, u64)>>,
    // Pack columns do not occupy a wire, and have the sentinel usize::MAX.
    raw_wires: Vec<usize>,
    raw_packs: Vec<(usize, Vec<usize>)>,
    original_wires: usize,
    unpadded_wires: usize,
}

impl PackedCircuit {
    fn new(circuit: &Circuit, raw_columns: Vec<usize>) -> Self {
        let mut gates = Vec::with_capacity(circuit.gates.len());
        let mut raw_wires = vec![usize::MAX; circuit.gates.len()];
        let mut raw_packs = Vec::new();
        for (raw, gate) in circuit.gates.iter().enumerate() {
            let packed = match gate {
                Gate::Input => PackedGate::Input,
                Gate::Constant(false) => PackedGate::Zero,
                Gate::Constant(true) => PackedGate::One,
                Gate::Xor(a, b) => PackedGate::Xor(wire(&raw_wires, a.index()), wire(&raw_wires, b.index())),
                Gate::And(a, b) => PackedGate::And(wire(&raw_wires, a.index()), wire(&raw_wires, b.index())),
                Gate::Pack(bits) => {
                    raw_packs.push((raw, bits.iter().map(|bit| wire(&raw_wires, bit.index())).collect()));
                    continue;
                }
            };
            raw_wires[raw] = gates.len();
            gates.push(packed);
        }
        // Circuit reserves these two columns before creating any other gates.
        assert_eq!(gates[0], PackedGate::Zero);
        assert_eq!(gates[1], PackedGate::One);
        let original_wires = gates.len();
        let mut zero_pin = 0;
        for (a, b) in &circuit.equalities {
            let difference = gates.len();
            gates.push(PackedGate::Xor(
                wire(&raw_wires, a.index()),
                wire(&raw_wires, b.index()),
            ));
            if zero_pin == 0 {
                zero_pin = difference;
            } else {
                // OR(x, y) = x + y + xy over GF(2). Unlike an XOR fold,
                // simultaneous assertion failures cannot cancel each other.
                let sum = gates.len();
                gates.push(PackedGate::Xor(zero_pin, difference));
                let product = gates.len();
                gates.push(PackedGate::And(zero_pin, difference));
                zero_pin = gates.len();
                gates.push(PackedGate::Xor(sum, product));
            }
        }
        let unpadded_wires = gates.len();
        let padded_wires = unpadded_wires.max(1 << 10).next_power_of_two();
        let k_log = padded_wires.trailing_zeros() as usize;
        gates.resize(padded_wires, PackedGate::Zero);
        let aliases = raw_columns
            .iter()
            .map(|&raw| match &circuit.gates[raw] {
                Gate::Pack(bits) => bits
                    .iter()
                    .enumerate()
                    .map(|(i, bit)| (wire(&raw_wires, bit.index()), 1u64 << i))
                    .collect(),
                _ => vec![(wire(&raw_wires, raw), 1)],
            })
            .collect();
        Self {
            k_log,
            zero_pin,
            gates,
            raw_columns,
            aliases,
            raw_wires,
            raw_packs,
            original_wires,
            unpadded_wires,
        }
    }

    /// Consume one raw witness row without retaining its unpacked gate values.
    /// Existing gate values and physical words are preserved, not repaired:
    /// the R1CS and projection proofs enforce their consistency.
    pub fn pack_row(&self, raw: &[u64]) -> Result<PackedRow, Error> {
        if raw.len() != self.raw_wires.len() {
            return Err(Error::InvalidShape);
        }
        let mut bits = vec![0u64; self.gates.len() / 64];
        for (&value, &wire) in raw.iter().zip(&self.raw_wires) {
            if wire == usize::MAX {
                continue;
            }
            if value > 1 {
                return Err(Error::InvalidShape);
            }
            bits[wire / 64] |= value << (wire % 64);
        }
        for index in self.original_wires..self.unpadded_wires {
            let value = match self.gates[index] {
                PackedGate::Xor(a, b) => bit(&bits, a) ^ bit(&bits, b),
                PackedGate::And(a, b) => bit(&bits, a) & bit(&bits, b),
                _ => unreachable!("assertion accumulation uses only XOR and AND"),
            };
            bits[index / 64] |= value << (index % 64);
        }
        let values = self.raw_columns.iter().map(|&column| raw[column]).collect();
        Ok(PackedRow { bits, values })
    }

    /// Reconstruct original gate columns for raw-circuit regression checks.
    /// Pack nodes are recomputed from their bits, not from physical columns.
    pub fn unpack_row(&self, row: &PackedRow) -> Vec<u64> {
        assert_eq!(row.bits.len(), self.gates.len() / 64);
        let mut raw = vec![0; self.raw_wires.len()];
        for (value, &wire) in raw.iter_mut().zip(&self.raw_wires) {
            if wire != usize::MAX {
                *value = bit(&row.bits, wire);
            }
        }
        for (column, wires) in &self.raw_packs {
            raw[*column] = wires
                .iter()
                .enumerate()
                .fold(0, |word, (i, &wire)| word ^ (bit(&row.bits, wire) << i));
        }
        raw
    }
}

fn wire(raw_wires: &[usize], raw: usize) -> usize {
    let wire = raw_wires[raw];
    assert_ne!(wire, usize::MAX, "a Boolean gate cannot reference a Pack node");
    wire
}

fn bit(bits: &[u64], wire: usize) -> u64 {
    bits[wire / 64] >> (wire % 64) & 1
}

#[derive(Clone, Debug)]
pub struct PackedSpec {
    pub circuit: PackedCircuit,
    pub relations: Vec<Coord>,
    pub flushes: Vec<Flush>,
    pub flock_slots: Vec<(usize, usize)>,
}

impl PackedSpec {
    pub fn new(spec: &TableSpec) -> Self {
        let mut raw_columns = Vec::new();
        for relation in &spec.relations {
            collect_columns(relation, &mut raw_columns);
        }
        for flush in &spec.flushes {
            for coordinate in flush.push.iter().chain(&flush.pull).chain(flush.count.iter()) {
                collect_columns(coordinate, &mut raw_columns);
            }
        }
        raw_columns.extend(spec.flock_slots.iter().map(|&(column, _)| column));
        raw_columns.sort_unstable();
        raw_columns.dedup();
        let relations = spec.relations.iter().map(|coord| remap(coord, &raw_columns)).collect();
        let flushes = spec
            .flushes
            .iter()
            .map(|flush| Flush {
                push: flush.push.iter().map(|coord| remap(coord, &raw_columns)).collect(),
                pull: flush.pull.iter().map(|coord| remap(coord, &raw_columns)).collect(),
                count: flush.count.as_ref().map(|coord| remap(coord, &raw_columns)),
            })
            .collect();
        let flock_slots = spec
            .flock_slots
            .iter()
            .map(|&(column, slot)| (dense(&raw_columns, column), slot))
            .collect();
        let circuit = PackedCircuit::new(&spec.circuit, raw_columns);
        Self {
            circuit,
            relations,
            flushes,
            flock_slots,
        }
    }
}

fn collect_columns(coord: &Coord, columns: &mut Vec<usize>) {
    match coord {
        Coord::Constant(_) => {}
        Coord::Column(column) | Coord::Scaled(column, _) | Coord::PublicScaled(column, _, _) => columns.push(*column),
        Coord::Product(a, b, _) => {
            columns.push(*a);
            columns.push(*b);
        }
        Coord::Sum(terms) => {
            for term in terms {
                collect_columns(term, columns);
            }
        }
    }
}

fn dense(raw_columns: &[usize], raw: usize) -> usize {
    raw_columns.binary_search(&raw).expect("physical column was collected")
}

fn remap(coord: &Coord, raw_columns: &[usize]) -> Coord {
    match coord {
        Coord::Constant(value) => Coord::Constant(*value),
        Coord::Column(column) => Coord::Column(dense(raw_columns, *column)),
        Coord::Scaled(column, coefficient) => Coord::Scaled(dense(raw_columns, *column), *coefficient),
        Coord::PublicScaled(column, source, coefficient) => {
            Coord::PublicScaled(dense(raw_columns, *column), *source, *coefficient)
        }
        Coord::Product(a, b, coefficient) => {
            Coord::Product(dense(raw_columns, *a), dense(raw_columns, *b), *coefficient)
        }
        Coord::Sum(terms) => Coord::Sum(terms.iter().map(|term| remap(term, raw_columns)).collect()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanvm_guest::Field;

    fn r1cs_holds(circuit: &PackedCircuit, row: &PackedRow) -> bool {
        let one = bit(&row.bits, 1);
        one == 1
            && bit(&row.bits, circuit.zero_pin) == 0
            && circuit.gates.iter().enumerate().all(|(i, gate)| {
                let z = bit(&row.bits, i);
                let (a, b) = match *gate {
                    PackedGate::Input => (z, one),
                    PackedGate::Zero => (0, 0),
                    PackedGate::One => (one, one),
                    PackedGate::Xor(a, b) => (bit(&row.bits, a) ^ bit(&row.bits, b), one),
                    PackedGate::And(a, b) => (bit(&row.bits, a), bit(&row.bits, b)),
                };
                a & b == z
            })
    }

    fn aliases_hold(circuit: &PackedCircuit, row: &PackedRow) -> bool {
        circuit.aliases.iter().zip(&row.values).all(|(alias, &value)| {
            alias.iter().fold(0, |sum, &(wire, coefficient)| {
                sum ^ (bit(&row.bits, wire) * coefficient)
            }) == value
        })
    }

    #[test]
    fn assertions_cannot_cancel_or_be_hidden_by_tampering_with_the_flag() {
        let mut raw = Circuit::default();
        let a = raw.input();
        let b = raw.input();
        // Put a Pack node before later Boolean nodes to exercise index remapping.
        raw.pack(&[a, b]);
        let xor = raw.xor(a, b);
        let and = raw.and(a, b);
        raw.assert_equal(xor, Circuit::ZERO);
        raw.assert_equal(and, Circuit::ZERO);
        let packed = PackedSpec::new(&TableSpec::new(raw.clone())).circuit;
        for assignment in 0..4 {
            let values = raw.witness(&[assignment & 1 != 0, assignment & 2 != 0]).unwrap();
            let row = packed.pack_row(&values).unwrap();
            let fields: Vec<_> = values.iter().copied().map(Field::from).collect();
            let original_holds = (0..raw.constraints()).all(|i| raw.constraint(i, &fields, false) == Field::ZERO);
            assert_eq!(r1cs_holds(&packed, &row), original_holds);
            assert_eq!(packed.unpack_row(&row), values);
            if !original_holds {
                let mut forged = row.clone();
                forged.bits[packed.zero_pin / 64] &= !(1u64 << (packed.zero_pin % 64));
                assert!(!r1cs_holds(&packed, &forged));
            }
        }
        // Two equalities fail at once: XOR-only accumulation would accept.
        let mut raw = Circuit::default();
        let a = raw.input();
        raw.assert_equal(a, Circuit::ZERO);
        raw.assert_equal(a, Circuit::ZERO);
        let packed = PackedSpec::new(&TableSpec::new(raw.clone())).circuit;
        let invalid = packed.pack_row(&raw.witness(&[true]).unwrap()).unwrap();
        assert_eq!(bit(&invalid.bits, packed.zero_pin), 1);
        assert!(!r1cs_holds(&packed, &invalid));
        let valid = packed.pack_row(&raw.witness(&[false]).unwrap()).unwrap();
        assert!(r1cs_holds(&packed, &valid));
        for wire in [0, 1, packed.gates.len() - 1] {
            let mut forged = valid.clone();
            forged.bits[wire / 64] ^= 1u64 << (wire % 64);
            assert!(!r1cs_holds(&packed, &forged));
        }
    }

    #[test]
    fn physical_columns_bind_nested_coordinates_and_flock_slots_to_bits() {
        let mut raw = Circuit::default();
        let inputs = raw.input_word(3);
        let unused = raw.pack(&inputs);
        let word = raw.pack(&[inputs[2], inputs[0], inputs[2], Circuit::ONE]);
        let mut wide = vec![Circuit::ZERO; 64];
        wide[63] = inputs[1];
        let high = raw.pack(&wide);
        let mut spec = TableSpec::new(raw);
        spec.relations.push(Coord::Sum(vec![
            Coord::Constant(9),
            Coord::Sum(vec![Coord::Scaled(word, 7), Coord::Product(inputs[0].index(), word, 3)]),
        ]));
        spec.flushes.push(Flush {
            push: vec![Coord::Column(word)],
            pull: vec![Coord::Sum(vec![Coord::Column(inputs[1].index()), Coord::Constant(4)])],
            count: Some(Coord::Scaled(Circuit::ONE.index(), 5)),
        });
        spec.flock_slots.push((high, 17));
        let packed = PackedSpec::new(&spec);
        assert_eq!(
            packed.circuit.raw_columns,
            vec![1, inputs[0].index(), inputs[1].index(), word, high]
        );
        assert!(!packed.circuit.raw_columns.contains(&unused));
        assert_eq!(packed.flock_slots, vec![(4, 17)]);
        let raw = spec.circuit.witness(&[true, true, false]).unwrap();
        let row = packed.circuit.pack_row(&raw).unwrap();
        assert_eq!(row.values, vec![1, 1, 1, 10, 1u64 << 63]);
        assert!(aliases_hold(&packed.circuit, &row));
        assert_eq!(packed.circuit.unpack_row(&row), raw);
        let original: Vec<_> = raw.iter().copied().map(Field::from).collect();
        let physical: Vec<_> = row.values.iter().copied().map(Field::from).collect();
        let before = spec
            .relations
            .iter()
            .chain(&spec.flushes[0].push)
            .chain(&spec.flushes[0].pull)
            .chain(spec.flushes[0].count.iter());
        let after = packed
            .relations
            .iter()
            .chain(&packed.flushes[0].push)
            .chain(&packed.flushes[0].pull)
            .chain(packed.flushes[0].count.iter());
        for (before, after) in before.zip(after) {
            for quadratic in [false, true] {
                assert_eq!(before.eval(&original, quadratic), after.eval(&physical, quadratic));
            }
        }
        let mut forged = row;
        forged.values[3] ^= 1;
        assert!(!aliases_hold(&packed.circuit, &forged));
        assert!(r1cs_holds(&packed.circuit, &forged));
    }

    #[test]
    fn malformed_rows_and_non_boolean_gate_values_are_not_truncated() {
        let mut raw = Circuit::default();
        let a = raw.input();
        raw.pack(&[a, Circuit::ONE]);
        let packed = PackedSpec::new(&TableSpec::new(raw.clone())).circuit;
        let valid = raw.witness(&[true]).unwrap();
        assert!(matches!(
            packed.pack_row(&valid[..valid.len() - 1]),
            Err(Error::InvalidShape)
        ));
        let mut long = valid.clone();
        long.push(0);
        assert!(matches!(packed.pack_row(&long), Err(Error::InvalidShape)));
        let mut non_boolean = valid;
        non_boolean[a.index()] = 2;
        assert!(matches!(packed.pack_row(&non_boolean), Err(Error::InvalidShape)));
    }
}
