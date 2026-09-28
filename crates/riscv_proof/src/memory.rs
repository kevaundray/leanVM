//! Sorted, bus-linked RAM and register histories. The previous state is a
//! permutation-bus input, never a trusted host snapshot.

use crate::{
    Error, ProgramInfo,
    circuit::{Bit, Circuit},
    schema::{
        Access, Coord, Flush, InputValues, PublicSource, RomCounter, SEP_RAM, SEP_REG, SEP_ROM, SEP_SORT_RAM,
        SEP_SORT_REG, Space, TableRows, TableSpec,
    },
};
use alloc::{vec, vec::Vec};

const RAM_END: u64 = 1 << 32;
const REGISTER_TIME_END: u64 = 1 << 36;

/// Transcript-announced terminal state; validate before allocating a layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Header {
    pub count: u64,
    pub logrows: usize,
    pub last_address: u64,
    pub last_time: u64,
    pub last_value: u64,
}

impl Header {
    pub fn validate(&self, space: Space) -> Result<(), Error> {
        validate_shape(space, self.count, self.logrows)?;
        if self.last_address >= address_end(space)
            || (space == Space::Ram && self.last_value > 255)
            || (space == Space::Register && self.last_time >= REGISTER_TIME_END)
            || (space == Space::Register && self.last_address == 0 && self.last_value != 0)
            || (self.count == 0 && (self.last_address != 0 || self.last_time != 0 || self.last_value != 0))
        {
            return Err(Error::InvalidShape);
        }
        Ok(())
    }
}

/// The framework closes the chain with exactly one seed and one terminal pull.
#[derive(Clone, Copy, Debug)]
pub struct Boundary {
    pub separator: u64,
    pub terminal_index: u64,
    count: u64,
    space: Space,
}

impl Boundary {
    pub fn flush(&self, header: &Header) -> Result<Flush, Error> {
        header.validate(self.space)?;
        if header.count != self.count || (1u64 << header.logrows) != self.terminal_index {
            return Err(Error::InvalidShape);
        }
        Ok(Flush {
            push: [self.separator, 0, 0, 0, 0].into_iter().map(Coord::Constant).collect(),
            pull: [
                self.separator,
                self.terminal_index,
                header.last_address,
                header.last_time,
                header.last_value,
            ]
            .into_iter()
            .map(Coord::Constant)
            .collect(),
            count: None,
        })
    }
}

fn address_end(space: Space) -> u64 {
    match space {
        Space::Ram => RAM_END,
        Space::Register => 32,
    }
}

fn widths(space: Space) -> (usize, usize, usize) {
    match space {
        Space::Ram => (32, 64, 8),
        Space::Register => (5, 36, 64),
    }
}

fn index_width(space: Space) -> usize {
    match space {
        Space::Ram => 33,
        Space::Register => 37,
    }
}

fn row_log(count: u64) -> usize {
    if count == 0 {
        0
    } else {
        (64 - (count.max(8) - 1).leading_zeros()) as usize
    }
}

fn validate_shape(space: Space, count: u64, logrows: usize) -> Result<(), Error> {
    let limit = match space {
        Space::Ram => RAM_END,
        Space::Register => REGISTER_TIME_END,
    };
    if count > limit || logrows != row_log(count) || logrows >= usize::BITS as usize {
        return Err(Error::InvalidShape);
    }
    Ok(())
}

fn require_when(c: &mut Circuit, enabled: Bit, predicate: Bit) {
    let invalid = c.not(predicate);
    let violation = c.and(enabled, invalid);
    c.assert_equal(violation, Circuit::ZERO);
}

fn equal_when(c: &mut Circuit, enabled: Bit, a: &[Bit], b: &[Bit]) {
    for (&a, &b) in a.iter().zip(b) {
        let difference = c.xor(a, b);
        let violation = c.and(enabled, difference);
        c.assert_equal(violation, Circuit::ZERO);
    }
}

// Input and pin order: count, row limit, then range endpoints per segment.
fn metadata_values(
    program: &ProgramInfo,
    space: Space,
    count: u64,
    logrows: usize,
) -> Result<Vec<(u64, usize)>, Error> {
    let width = index_width(space);
    let mut values = vec![(count, width), (1u64 << logrows, width)];
    if space == Space::Ram {
        for segment in program.segments() {
            let memory_end = segment
                .address()
                .checked_add(segment.memory_size())
                .ok_or(Error::InvalidProgram)?;
            let file_end = segment
                .address()
                .checked_add(segment.bytes().len() as u64)
                .ok_or(Error::InvalidProgram)?;
            if memory_end > RAM_END || file_end > memory_end {
                return Err(Error::InvalidProgram);
            }
            values.extend([(segment.address(), 33), (memory_end, 33), (file_end, 33)]);
        }
    }
    Ok(values)
}

fn in_range(c: &mut Circuit, address: &[Bit], start: &[Bit], end: &[Bit]) -> Bit {
    let below = c.less_than(address, start, false);
    let above = c.not(below);
    let below_end = c.less_than(address, end, false);
    c.and(above, below_end)
}

/// Both spaces use the same sorted-index chain. Each index lies in [0,M),
/// advances by one without wrapping, and therefore cannot form an orphan cycle.
pub fn build_spec(
    program: &ProgramInfo,
    space: Space,
    realcount: u64,
    logrows: usize,
) -> Result<(TableSpec, Boundary), Error> {
    validate_shape(space, realcount, logrows)?;
    let (address_width, time_width, value_width) = widths(space);
    let mut c = Circuit::default();
    // Keep this input order synchronized with row_inputs.
    let index = c.input_word(index_width(space));
    let previous_address = c.input_word(address_width);
    let previous_time = c.input_word(time_width);
    let previous_value = c.input_word(value_width);
    let address = c.input_word(address_width);
    let time = c.input_word(time_width);
    let before = c.input_word(value_width);
    let after = c.input_word(value_width);
    let write = c.input();
    let rom_count = if space == Space::Ram {
        Some(c.input_word(64))
    } else {
        None
    };
    let metadata = metadata_values(program, space, realcount, logrows)?;
    let metadata_bits: Vec<_> = metadata.iter().map(|&(_, width)| c.input_word(width)).collect();

    let in_rows = c.less_than(&index, &metadata_bits[1], false);
    require_when(&mut c, Circuit::ONE, in_rows);
    let one = c.constant(1, index.len());
    let (successor, overflow) = c.add_carry(&index, &one, Circuit::ZERO);
    c.assert_equal(overflow, Circuit::ZERO);
    let active = c.less_than(&index, &metadata_bits[0], false);
    let zero_index = c.constant(0, index.len());
    let first_row = c.equals(&index, &zero_index);
    let has_previous = c.not(first_row);
    let same_address = c.equals(&previous_address, &address);
    let higher_address = c.less_than(&previous_address, &address, false);
    let higher_time = c.less_than(&previous_time, &time, false);
    let same_and_later = c.and(same_address, higher_time);
    let sorted = c.or(higher_address, same_and_later);
    let compare_previous = c.and(active, has_previous);
    require_when(&mut c, compare_previous, sorted);
    let continuing = c.and(compare_previous, same_address);
    equal_when(&mut c, continuing, &before, &previous_value);
    let changed_address = c.not(same_address);
    let starts_address = c.or(first_row, changed_address);
    let initialize = c.and(active, starts_address);
    let read = c.not(write);
    let reading = c.and(active, read);
    equal_when(&mut c, reading, &before, &after);

    let zero_value = c.constant(0, value_width);
    let mut lookup = Circuit::ZERO;
    match space {
        Space::Register => {
            let two = c.constant(2, address_width);
            let stack_pointer = c.equals(&address, &two);
            let stack_initial = c.constant(RAM_END, value_width);
            let initial = c.select(stack_pointer, &stack_initial, &zero_value);
            equal_when(&mut c, initialize, &before, &initial);
            let zero_address = c.constant(0, address_width);
            let is_zero = c.equals(&address, &zero_address);
            let zero_register = c.and(active, is_zero);
            equal_when(&mut c, zero_register, &before, &zero_value);
            equal_when(&mut c, zero_register, &after, &zero_value);
        }
        Space::Ram => {
            // A 33-bit comparison represents the exclusive endpoint 2^32.
            let wide_address = c.extend(&address, 33, false);
            let mut file_backed = Circuit::ZERO;
            for (segment, bounds) in program.segments().iter().zip(metadata_bits[2..].chunks_exact(3)) {
                let mapped = in_range(&mut c, &wide_address, &bounds[0], &bounds[1]);
                let mapped_active = c.and(active, mapped);
                if !segment.readable() {
                    let denied = c.and(mapped_active, read);
                    c.assert_equal(denied, Circuit::ZERO);
                }
                if !segment.writable() {
                    let denied = c.and(mapped_active, write);
                    c.assert_equal(denied, Circuit::ZERO);
                }
                let file = in_range(&mut c, &wide_address, &bounds[0], &bounds[2]);
                file_backed = c.or(file_backed, file);
            }
            lookup = c.and(initialize, file_backed);
            let not_file = c.not(file_backed);
            let zero_initialize = c.and(initialize, not_file);
            equal_when(&mut c, zero_initialize, &before, &zero_value);
        }
    }

    let next_address = c.select(active, &address, &previous_address);
    let next_time = c.select(active, &time, &previous_time);
    let next_value = c.select(active, &after, &previous_value);
    let index_column = c.pack(&index);
    let successor_column = c.pack(&successor);
    let previous_address_column = c.pack(&previous_address);
    let previous_time_column = c.pack(&previous_time);
    let previous_value_column = c.pack(&previous_value);
    let next_address_column = c.pack(&next_address);
    let next_time_column = c.pack(&next_time);
    let next_value_column = c.pack(&next_value);
    let address_column = c.pack(&address);
    let time_column = c.pack(&time);
    let before_column = c.pack(&before);
    let after_column = c.pack(&after);
    let rom_column = rom_count.as_ref().map(|bits| c.pack(bits));
    let metadata_columns: Vec<_> = metadata_bits.iter().map(|bits| c.pack(bits)).collect();
    let separator = match space {
        Space::Ram => SEP_SORT_RAM,
        Space::Register => SEP_SORT_REG,
    };
    let event_separator = match space {
        Space::Ram => SEP_RAM,
        Space::Register => SEP_REG,
    };
    let mut spec = TableSpec::new(c);
    for (index, (column, &(expected, _))) in metadata_columns.into_iter().zip(&metadata).enumerate() {
        // ONE is the packed row enable; zero extension rows must remain valid.
        let e = Circuit::ONE.index();
        let value = match index {
            0 => Coord::PublicScaled(e, PublicSource::MemoryCount(space), expected),
            1 => Coord::PublicScaled(e, PublicSource::MemoryRows(space), expected),
            _ => Coord::Scaled(e, expected),
        };
        spec.relations
            .push(Coord::Sum(vec![Coord::Product(e, column, 1), value]));
    }
    spec.flushes.push(Flush {
        push: vec![
            Coord::Constant(separator),
            Coord::Column(successor_column),
            Coord::Column(next_address_column),
            Coord::Column(next_time_column),
            Coord::Column(next_value_column),
        ],
        pull: vec![
            Coord::Constant(separator),
            Coord::Column(index_column),
            Coord::Column(previous_address_column),
            Coord::Column(previous_time_column),
            Coord::Column(previous_value_column),
        ],
        count: None,
    });
    spec.flushes.push(Flush {
        push: vec![Coord::Constant(0); 6],
        pull: vec![
            Coord::Scaled(active.index(), event_separator),
            Coord::Product(active.index(), address_column, 1),
            Coord::Product(active.index(), time_column, 1),
            Coord::Product(active.index(), before_column, 1),
            Coord::Product(active.index(), after_column, 1),
            Coord::Product(active.index(), write.index(), 1),
        ],
        count: None,
    });
    if let Some(r) = rom_column {
        // g=2 in the polynomial basis; addition is XOR, hence g+1=3.
        // Inactive lookups have the identical nonzero counter on both sides.
        let prefix = Coord::Scaled(lookup.index(), SEP_ROM);
        let key = Coord::Product(lookup.index(), address_column, 2);
        let value = Coord::Product(lookup.index(), before_column, 1);
        spec.flushes.push(Flush {
            push: vec![
                prefix.clone(),
                key.clone(),
                Coord::Sum(vec![Coord::Column(r), Coord::Product(lookup.index(), r, 3)]),
                value.clone(),
            ],
            pull: vec![prefix, key, Coord::Column(r), value],
            count: Some(Coord::Column(r)),
        });
    }
    Ok((
        spec,
        Boundary {
            separator,
            terminal_index: 1u64 << logrows,
            count: realcount,
            space,
        },
    ))
}

fn row_inputs(
    space: Space,
    index: u64,
    previous: (u64, u64, u64),
    event: Option<&Access>,
    rom_count: u64,
    metadata: &[(u64, usize)],
) -> InputValues {
    let (address_width, time_width, value_width) = widths(space);
    let mut inputs = InputValues::default();
    inputs.word(index, index_width(space));
    inputs.word(previous.0, address_width);
    inputs.word(previous.1, time_width);
    inputs.word(previous.2, value_width);
    inputs.word(event.map_or(0, |event| event.address), address_width);
    inputs.word(event.map_or(0, |event| event.time), time_width);
    inputs.word(event.map_or(0, |event| event.before), value_width);
    inputs.word(event.map_or(0, |event| event.after), value_width);
    inputs.bit(event.is_some_and(|event| event.write));
    if space == Space::Ram {
        inputs.word(rom_count, 64);
    }
    for &(value, width) in metadata {
        inputs.word(value, width);
    }
    inputs
}

fn initialized_byte(program: &ProgramInfo, address: u64) -> Option<u8> {
    program.segments().iter().find_map(|segment| {
        let offset = address.checked_sub(segment.address())?;
        segment.bytes().get(usize::try_from(offset).ok()?).copied()
    })
}

/// Construct one space's witness; callers supply only events from that space.
/// Host checks reject malformed traces early; acceptance is enforced by the
/// circuit identities, event permutation, sorted chain, and public ROM lookup.
pub fn build_rows(
    program: &ProgramInfo,
    space: Space,
    events: &[Access],
    rom: &mut RomCounter,
) -> Result<(TableRows, Header, Boundary), Error> {
    let count = u64::try_from(events.len()).map_err(|_| Error::InvalidShape)?;
    let logrows = row_log(count);
    let (spec, boundary) = build_spec(program, space, count, logrows)?;
    let metadata = metadata_values(program, space, count, logrows)?;
    let mut events = events.to_vec();
    events.sort_unstable_by_key(|event| (event.address, event.time));
    let mut previous = (0, 0, 0);
    // Validate before mutating shared ROM counters.
    for (index, event) in events.iter().enumerate() {
        if event.space != space
            || event.address >= address_end(space)
            || (space == Space::Ram && (event.before > 255 || event.after > 255))
            || (space == Space::Register && event.time >= REGISTER_TIME_END)
            || (!event.write && event.before != event.after)
        {
            return Err(Error::InvalidExecution);
        }
        let first = index == 0 || previous.0 != event.address;
        if !first && (event.time <= previous.1 || event.before != previous.2) {
            return Err(Error::InvalidExecution);
        }
        match space {
            Space::Register => {
                let initial = if event.address == 2 { RAM_END } else { 0 };
                if (first && event.before != initial) || (event.address == 0 && (event.before != 0 || event.after != 0))
                {
                    return Err(Error::InvalidExecution);
                }
            }
            Space::Ram => {
                if first && event.before != initialized_byte(program, event.address).unwrap_or(0) as u64 {
                    return Err(Error::InvalidExecution);
                }
                for segment in program.segments() {
                    if event.address >= segment.address()
                        && event.address - segment.address() < segment.memory_size()
                        && ((event.write && !segment.writable()) || (!event.write && !segment.readable()))
                    {
                        return Err(Error::InvalidExecution);
                    }
                }
            }
        }
        previous = (event.address, event.time, event.after);
    }
    let header = Header {
        count,
        logrows,
        last_address: previous.0,
        last_time: previous.1,
        last_value: previous.2,
    };
    header.validate(space)?;
    let packing = crate::packed::PackedSpec::new(&spec);
    let padded = if count == 0 { 0 } else { 1usize << logrows };
    let mut rows = Vec::with_capacity(padded);
    previous = (0, 0, 0);
    for index in 0..padded {
        let event = events.get(index);
        let mut r = 1;
        if let Some(event) = event
            && space == Space::Ram
            && (index == 0 || event.address != previous.0)
            && initialized_byte(program, event.address).is_some()
        {
            r = rom.take(event.address << 1)?;
        }
        let inputs = row_inputs(space, index as u64, previous, event, r, &metadata);
        let row = spec.circuit.witness(&inputs.0).ok_or(Error::InvalidShape)?;
        rows.push(packing.circuit.pack_row(&row)?);
        if let Some(event) = event {
            previous = (event.address, event.time, event.after);
        }
    }
    Ok((TableRows { spec, packing, rows }, header, boundary))
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::collections::BTreeMap;
    use leanvm_guest::Field;

    const CODE: u64 = 0x10000;
    const DATA: u64 = 0x20000;

    fn program() -> ProgramInfo {
        program_with_data(DATA, 4, 6, &[0x5a])
    }

    fn program_with_data(data: u64, memory_size: u64, flags: u32, bytes: &[u8]) -> ProgramInfo {
        let mut elf = vec![0u8; 0x104 + bytes.len()];
        elf[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        for (at, value) in [(16, 2u16), (18, 243), (52, 64), (54, 56), (56, 2)] {
            elf[at..at + 2].copy_from_slice(&value.to_le_bytes());
        }
        elf[20..24].copy_from_slice(&1u32.to_le_bytes());
        elf[24..32].copy_from_slice(&CODE.to_le_bytes());
        elf[32..40].copy_from_slice(&64u64.to_le_bytes());
        for (p, address, offset, size, memory_size, flags) in [
            (64, CODE, 0x100u64, 4u64, 4u64, 5u32),
            (120, data, 0x104, bytes.len() as u64, memory_size, flags),
        ] {
            elf[p..p + 4].copy_from_slice(&1u32.to_le_bytes());
            elf[p + 4..p + 8].copy_from_slice(&flags.to_le_bytes());
            for (at, value) in [(8, offset), (16, address), (32, size), (40, memory_size), (48, 4)] {
                elf[p + at..p + at + 8].copy_from_slice(&value.to_le_bytes());
            }
        }
        elf[0x100..0x104].copy_from_slice(&0x73u32.to_le_bytes());
        elf[0x104..].copy_from_slice(bytes);
        ProgramInfo::from_elf(&elf).unwrap()
    }

    fn access(address: u64, time: u64, before: u64, after: u64, write: bool) -> Access {
        Access {
            space: Space::Ram,
            address,
            time,
            before,
            after,
            write,
        }
    }

    fn local_valid(table: &TableRows) -> bool {
        table.rows.iter().all(|row| {
            let row: Vec<_> = table
                .packing
                .circuit
                .unpack_row(row)
                .into_iter()
                .map(Field::from)
                .collect();
            (0..table.spec.constraints()).all(|i| table.spec.constraint(i, &row, false) == Field::ZERO)
        })
    }

    // Exact multiset equality models the permutation argument, independently
    // of the host constructor. Forged rows below regenerate every gate column.
    fn accepts(
        program: &ProgramInfo,
        table: &TableRows,
        header: &Header,
        boundary: Boundary,
        events: &[Access],
        rom: &RomCounter,
    ) -> bool {
        if !local_valid(table) {
            return false;
        }
        let Ok(boundary) = boundary.flush(header) else {
            return false;
        };
        let mut balances = BTreeMap::<Vec<[u64; 3]>, i64>::new();
        let mut add = |tuple: Vec<Field>, sign: i64| {
            *balances.entry(tuple.into_iter().map(|x| x.0).collect()).or_default() += sign;
        };
        for row in &table.rows {
            let columns: Vec<_> = table
                .packing
                .circuit
                .unpack_row(row)
                .into_iter()
                .map(Field::from)
                .collect();
            for flush in &table.spec.flushes {
                if flush
                    .count
                    .as_ref()
                    .is_some_and(|count| count.eval(&columns, false) == Field::ZERO)
                {
                    return false;
                }
                add(flush.push.iter().map(|coord| coord.eval(&columns, false)).collect(), 1);
                add(flush.pull.iter().map(|coord| coord.eval(&columns, false)).collect(), -1);
            }
        }
        if header.count != 0 {
            add(boundary.push.iter().map(|coord| coord.eval(&[], false)).collect(), 1);
            add(boundary.pull.iter().map(|coord| coord.eval(&[], false)).collect(), -1);
        }
        for event in events {
            let separator = if event.space == Space::Ram { SEP_RAM } else { SEP_REG };
            add(
                [
                    separator,
                    event.address,
                    event.time,
                    event.before,
                    event.after,
                    u64::from(event.write),
                ]
                .into_iter()
                .map(Field::from)
                .collect(),
                1,
            );
            add(vec![Field::ZERO; 6], -1);
        }
        for (key, value) in program.rom_entries() {
            add([SEP_ROM, key, 1, value].into_iter().map(Field::from).collect(), 1);
            add(
                [SEP_ROM, key, rom.final_count(key), value]
                    .into_iter()
                    .map(Field::from)
                    .collect(),
                -1,
            );
        }
        balances.values().all(|&balance| balance == 0)
    }

    fn replace_row(
        table: &mut TableRows,
        program: &ProgramInfo,
        count: u64,
        index: usize,
        previous: (u64, u64, u64),
        event: &Access,
    ) {
        let logrows = row_log(table.rows.len() as u64);
        let metadata = metadata_values(program, event.space, count, logrows).unwrap();
        let inputs = row_inputs(event.space, index as u64, previous, Some(event), 1, &metadata);
        let row = table.spec.circuit.witness(&inputs.0).unwrap();
        table.rows[index] = table.packing.circuit.pack_row(&row).unwrap();
    }

    #[test]
    fn packed_matrices_depend_on_shape_not_public_metadata() {
        let programs = [
            program(),
            program_with_data(DATA + 16, 8, 6, &[0x5a, 0x6b]),
            program_with_data(RAM_END - 4, 4, 6, &[]),
        ];
        for space in [Space::Ram, Space::Register] {
            let (reference, _) = build_spec(&programs[0], space, 1, 3).unwrap();
            let reference = crate::packed::PackedSpec::new(&reference).circuit;
            for program in &programs {
                for count in [1, 7, 8, 9, 255, 256, 257, 1 << 20] {
                    let (spec, _) = build_spec(program, space, count, row_log(count)).unwrap();
                    let actual = crate::packed::PackedSpec::new(&spec).circuit;
                    assert_eq!(actual.gates, reference.gates);
                    assert_eq!(actual.zero_pin, reference.zero_pin);
                    assert_eq!(actual.raw_columns, reference.raw_columns);
                    assert_eq!(actual.aliases, reference.aliases);
                }
            }
        }
    }

    #[test]
    fn public_metadata_pins_reject_forged_inputs() {
        let program = program();
        for space in [Space::Ram, Space::Register] {
            let (spec, _) = build_spec(&program, space, 1, 3).unwrap();
            let packing = crate::packed::PackedSpec::new(&spec);
            let metadata = metadata_values(&program, space, 1, 3).unwrap();
            let event = Access {
                space,
                ..access(7, 0, 0, 0, false)
            };
            for index in 0..metadata.len() {
                let mut forged = metadata.clone();
                forged[index].0 ^= 1;
                let inputs = row_inputs(space, 0, (0, 0, 0), Some(&event), 1, &forged);
                let raw = spec.circuit.witness(&inputs.0).unwrap();
                let columns: Vec<_> = raw.iter().copied().map(Field::from).collect();
                assert!(
                    (0..spec.circuit.constraints()).all(|i| spec.circuit.constraint(i, &columns, false) == Field::ZERO),
                    "the public pin, not a Boolean gate, must reject this forgery"
                );
                let packed = packing.circuit.pack_row(&raw).unwrap();
                let physical: Vec<_> = packed.values.into_iter().map(Field::from).collect();
                assert!(
                    packing
                        .relations
                        .iter()
                        .any(|pin| pin.eval(&physical, false) != Field::ZERO)
                );
            }
        }
    }

    #[test]
    fn maximum_counts_and_register_time_do_not_truncate() {
        let program = program();
        for (space, count, logrows, time) in [
            (Space::Ram, RAM_END, 32, u64::MAX),
            (Space::Register, REGISTER_TIME_END, 36, REGISTER_TIME_END - 1),
        ] {
            let (spec, _) = build_spec(&program, space, count, logrows).unwrap();
            let metadata = metadata_values(&program, space, count, logrows).unwrap();
            let event = Access {
                space,
                ..access(7, time, 0, 0, false)
            };
            let inputs = row_inputs(space, count - 1, (7, time - 1, 0), Some(&event), 1, &metadata);
            let row: Vec<_> = spec
                .circuit
                .witness(&inputs.0)
                .unwrap()
                .into_iter()
                .map(Field::from)
                .collect();
            assert!((0..spec.constraints()).all(|i| spec.constraint(i, &row, false) == Field::ZERO));
            assert_eq!(spec.flushes[0].push[1].eval(&row, false), Field::from(count));
            let separator = match space {
                Space::Ram => SEP_RAM,
                Space::Register => SEP_REG,
            };
            assert_eq!(spec.flushes[1].pull[0].eval(&row, false), Field::from(separator));
        }
    }

    #[test]
    fn exclusive_ram_end_preserves_file_initialization_and_read_only_bss() {
        for bytes in [&[0x5a, 1, 2, 0x6b][..], &[0x5a][..]] {
            let program = program_with_data(RAM_END - 4, 4, 4, bytes);
            let value = bytes.get(3).copied().unwrap_or(0) as u64;
            let event = access(RAM_END - 1, 0, value, value, false);
            let mut rom = RomCounter::new(&program);
            let (mut table, header, boundary) = build_rows(&program, Space::Ram, &[event], &mut rom).unwrap();
            assert!(accepts(&program, &table, &header, boundary, &[event], &rom));
            let forbidden = Access {
                after: value ^ 1,
                write: true,
                ..event
            };
            replace_row(&mut table, &program, 1, 0, (0, 0, 0), &forbidden);
            assert!(!local_valid(&table));
            assert!(build_rows(&program, Space::Ram, &[access(RAM_END, 0, 0, 0, false)], &mut rom).is_err());
        }
        let program = program_with_data(DATA, 4, 4, &[0x5a]);
        let events = [access(DATA + 1, 0, 0, 0, false), access(DATA + 4, 1, 0, 9, true)];
        let mut rom = RomCounter::new(&program);
        let (table, header, boundary) = build_rows(&program, Space::Ram, &events, &mut rom).unwrap();
        assert!(accepts(&program, &table, &header, boundary, &events, &rom));
    }

    #[test]
    fn duplicate_initialization_cannot_forge_previous_state() {
        let program = program();
        let mut rom = RomCounter::new(&program);
        let mut events = [access(7, 1, 0, 9, true), access(7, 2, 9, 9, false)];
        let (mut table, mut header, boundary) = build_rows(&program, Space::Ram, &events, &mut rom).unwrap();
        assert!(accepts(&program, &table, &header, boundary, &events, &rom));
        events[1] = access(7, 2, 0, 0, false);
        replace_row(&mut table, &program, header.count, 1, (0, 0, 0), &events[1]);
        header.last_value = 0;
        assert!(local_valid(&table), "the attack specifically targets the adjacency bus");
        assert!(!accepts(&program, &table, &header, boundary, &events, &rom));
    }

    #[test]
    fn stale_read_after_write_violates_value_continuity() {
        let program = program();
        let mut rom = RomCounter::new(&program);
        let events = [access(7, 1, 0, 9, true), access(7, 2, 9, 9, false)];
        let (mut table, _, _) = build_rows(&program, Space::Ram, &events, &mut rom).unwrap();
        replace_row(&mut table, &program, 2, 1, (7, 1, 9), &access(7, 2, 0, 0, false));
        assert!(!local_valid(&table));
    }

    #[test]
    fn reordered_or_duplicate_timestamps_violate_strict_order() {
        let program = program();
        let mut rom = RomCounter::new(&program);
        let events = [access(7, 1, 0, 0, false), access(7, 2, 0, 9, true)];
        let (mut table, _, _) = build_rows(&program, Space::Ram, &events, &mut rom).unwrap();
        replace_row(&mut table, &program, 2, 0, (0, 0, 0), &access(7, 2, 0, 0, false));
        for time in [1, 2] {
            replace_row(&mut table, &program, 2, 1, (7, 2, 0), &access(7, time, 0, 9, true));
            assert!(!local_valid(&table));
        }
    }

    #[test]
    fn changed_elf_initial_value_fails_public_rom_lookup() {
        let program = program();
        let mut rom = RomCounter::new(&program);
        let event = access(DATA, 0, 0x5a, 0x5a, false);
        let (mut table, mut header, boundary) = build_rows(&program, Space::Ram, &[event], &mut rom).unwrap();
        assert!(accepts(&program, &table, &header, boundary, &[event], &rom));
        let forged = access(DATA, 0, 0x5b, 0x5b, false);
        replace_row(&mut table, &program, header.count, 0, (0, 0, 0), &forged);
        let metadata = metadata_values(&program, Space::Ram, header.count, header.logrows).unwrap();
        for index in 1..table.rows.len() {
            let inputs = row_inputs(Space::Ram, index as u64, (DATA, 0, 0x5b), None, 1, &metadata);
            let row = table.spec.circuit.witness(&inputs.0).unwrap();
            table.rows[index] = table.packing.circuit.pack_row(&row).unwrap();
        }
        header.last_value = 0x5b;
        assert!(local_valid(&table), "initial file bytes are bound through the ROM bus");
        assert!(!accepts(&program, &table, &header, boundary, &[forged], &rom));
    }

    #[test]
    fn empty_histories_close_zero_seed_and_nonempty_padding_preserves_tail() {
        let program = program();
        for space in [Space::Ram, Space::Register] {
            let mut rom = RomCounter::new(&program);
            let (table, mut header, boundary) = build_rows(&program, space, &[], &mut rom).unwrap();
            assert!(accepts(&program, &table, &header, boundary, &[], &rom));
            header.last_time = 1;
            assert!(!accepts(&program, &table, &header, boundary, &[], &rom));
        }
        let mut rom = RomCounter::new(&program);
        let events = [
            access(0, 0, 0, 3, true),
            access(0, 1, 3, 3, false),
            access(DATA + 1, 2, 0, 0, false),
        ];
        let (table, header, boundary) = build_rows(&program, Space::Ram, &events, &mut rom).unwrap();
        assert!(accepts(&program, &table, &header, boundary, &events, &rom));
    }

    #[test]
    fn register_initialization_and_permissions_are_equations() {
        let program = program();
        let mut rom = RomCounter::new(&program);
        let sp = Access {
            space: Space::Register,
            address: 2,
            time: 0,
            before: RAM_END,
            after: RAM_END,
            write: false,
        };
        let (mut table, header, boundary) = build_rows(&program, Space::Register, &[sp], &mut rom).unwrap();
        assert!(accepts(&program, &table, &header, boundary, &[sp], &rom));
        replace_row(
            &mut table,
            &program,
            header.count,
            0,
            (0, 0, 0),
            &Access {
                before: 0,
                after: 0,
                ..sp
            },
        );
        assert!(!local_valid(&table));
        replace_row(
            &mut table,
            &program,
            header.count,
            0,
            (0, 0, 0),
            &Access {
                address: 0,
                before: 0,
                after: 1,
                write: true,
                ..sp
            },
        );
        assert!(!local_valid(&table));

        let (spec, _) = build_spec(&program, Space::Ram, 1, 3).unwrap();
        let forbidden = access(CODE, 0, 0x73, 0x74, true);
        let metadata = metadata_values(&program, Space::Ram, 1, 3).unwrap();
        let inputs = row_inputs(Space::Ram, 0, (0, 0, 0), Some(&forbidden), 1, &metadata);
        let row = spec.circuit.witness(&inputs.0).unwrap();
        let packing = crate::packed::PackedSpec::new(&spec);
        let row = packing.circuit.pack_row(&row).unwrap();
        assert!(!local_valid(&TableRows {
            spec,
            packing,
            rows: vec![row]
        }));
    }
}
