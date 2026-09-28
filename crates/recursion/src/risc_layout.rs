use riscv_proof::{
    ProgramInfo, cpu_tables,
    layout::{CPU_TABLES, RAM_TABLE, REG_TABLE, TABLES},
    memory,
    packed::PackedSpec,
    schema::{PublicSource, Space},
};

use crate::{Error, context::Context, protocol::Dimension, transcript::Transcript, uint::Uint};

#[derive(Clone)]
pub(crate) struct TableShape<F: Copy> {
    pub present: F,
    pub dim: Dimension<F>,
}

#[derive(Clone)]
pub(crate) struct MemoryHeader<F: Copy> {
    pub count: Uint<F>,
    pub last_address: Uint<F>,
    pub last_time: Uint<F>,
    pub last_value: Uint<F>,
}

#[derive(Clone)]
pub(crate) struct Header<F: Copy> {
    pub cycles: Uint<F>,
    pub rate: Uint<F>,
    pub tables: Vec<TableShape<F>>,
    pub ram: MemoryHeader<F>,
    pub registers: MemoryHeader<F>,
}

fn power<C: Context>(ctx: &C, dim: &Dimension<C::F>, width: usize) -> Result<Uint<C::F>, Error> {
    Uint::from_bits(ctx, (0..width).map(|i| dim.equals(ctx, i)).collect())
}

impl<F: Copy> MemoryHeader<F> {
    fn read<C: Context<F = F>>(
        transcript: &mut Transcript<C>,
        enabled: F,
        space: Space,
        shape: &TableShape<F>,
    ) -> Result<Self, Error> {
        let ctx = transcript.context();
        let (count_width, address_width, time_width, value_width, limit) = match space {
            Space::Ram => (33, 32, 64, 8, 1u64 << 32),
            Space::Register => (37, 5, 36, 64, 1u64 << 36),
        };
        let count = Uint::from_field(ctx, transcript.scalar(enabled)?, count_width)?;
        let last_address = Uint::from_field(ctx, transcript.scalar(enabled)?, address_width)?;
        let last_time = Uint::from_field(ctx, transcript.scalar(enabled)?, time_width)?;
        let last_value = Uint::from_field(ctx, transcript.scalar(enabled)?, value_width)?;
        let absent = count.eq_const(ctx, 0);
        ctx.assert_equal(shape.present, ctx.not(absent))?;
        ctx.assert_zero(Uint::constant(ctx, limit, count_width).lt(ctx, &count))?;
        for terminal in [last_address.value(ctx), last_time.value(ctx), last_value.value(ctx)] {
            ctx.assert_equal_if(absent, terminal, ctx.zero())?;
        }
        if space == Space::Register {
            ctx.assert_equal_if(last_address.eq_const(ctx, 0), last_value.value(ctx), ctx.zero())?;
        }
        let rows = power(ctx, &shape.dim, count_width)?;
        ctx.assert_zero(rows.lt(ctx, &count))?;
        // ceil(log2(max(count, 8))): equality at a power belongs to the
        // smaller cube, whereas counts 1..=8 all use the minimum height 3.
        let half_rows = Uint::from_bits(ctx, rows.bits()[1..].iter().copied().chain([ctx.zero()]).collect())?;
        ctx.assert_equal_if(shape.dim.contains(3), half_rows.lt(ctx, &count), ctx.one())?;
        Ok(Self {
            count,
            last_address,
            last_time,
            last_value,
        })
    }
}

impl<F: Copy> Header<F> {
    pub(crate) fn read<C: Context<F = F>>(transcript: &mut Transcript<C>, enabled: F) -> Result<Self, Error> {
        let ctx = transcript.context();
        ctx.assert_bool(enabled)?;
        // Disabled transcripts consume nothing; use valid algorithmic defaults.
        let cycles_value = ctx.select(enabled, transcript.scalar(enabled)?, ctx.one());
        let cycles = Uint::from_field(ctx, cycles_value, 32)?;
        ctx.assert_zero(cycles.eq_const(ctx, 0))?;
        let rate_value = ctx.select(enabled, transcript.scalar(enabled)?, ctx.one());
        let rate = Uint::from_field(ctx, rate_value, 3)?;
        ctx.assert_zero(rate.eq_const(ctx, 0))?;
        ctx.assert_equal(rate.lt(ctx, &Uint::constant(ctx, 5, 3)), ctx.one())?;
        let mut tables = Vec::with_capacity(TABLES);
        for _ in 0..TABLES {
            let encoded = Uint::from_field(ctx, transcript.scalar(enabled)?, 6)?;
            let present = ctx.not(encoded.eq_const(ctx, 0));
            let decrement = Uint::select(ctx, present, &Uint::constant(ctx, 1, 6), &Uint::constant(ctx, 0, 6));
            let (tau, borrow) = encoded.sub(ctx, &decrement);
            ctx.assert_zero(borrow)?;
            // Every present table has at least one private physical cube,
            // so the committed layout's 28-bit bound already applies here.
            let dim = Dimension::from_uint(ctx, tau, 28)?;
            ctx.assert_equal_if(present, dim.contains(2), ctx.one())?;
            tables.push(TableShape { present, dim });
        }
        let ram = MemoryHeader::read(transcript, enabled, Space::Ram, &tables[RAM_TABLE])?;
        let registers = MemoryHeader::read(transcript, enabled, Space::Register, &tables[REG_TABLE])?;
        Ok(Self {
            cycles,
            rate,
            tables,
            ram,
            registers,
        })
    }
}

pub(crate) struct Templates {
    pub specs: Vec<PackedSpec>,
    pub rom_keys: Vec<u64>,
    pub rom_values: Vec<u64>,
    pub rom_log: usize,
    pub iv: [u8; 32],
    pub entry: u64,
}

impl Templates {
    pub(crate) fn new(program: &ProgramInfo) -> Result<Self, Error> {
        let mut specs = Vec::with_capacity(TABLES);
        for logical in 0..TABLES {
            let spec = if logical < CPU_TABLES {
                cpu_tables::build_spec([0; 32], 1, logical)
            } else {
                let space = if logical == RAM_TABLE {
                    Space::Ram
                } else {
                    Space::Register
                };
                memory::build_spec(program, space, 1, 3)
                    .map_err(|_| Error::InvalidInput)?
                    .0
            };
            specs.push(PackedSpec::new(&spec));
        }
        let (mut rom_keys, mut rom_values): (Vec<_>, Vec<_>) = program.rom_entries().into_iter().unzip();
        let length = rom_keys
            .len()
            .max(1)
            .checked_next_power_of_two()
            .ok_or(Error::InvalidInput)?;
        let rom_log = length.trailing_zeros() as usize;
        if rom_log > 28 {
            return Err(Error::InvalidInput);
        }
        rom_keys.resize(length, u64::MAX);
        rom_values.resize(length, 0);
        Ok(Self {
            specs,
            rom_keys,
            rom_values,
            rom_log,
            iv: program.iv(),
            entry: program.entry(),
        })
    }
}

pub(crate) struct Layout<F: Copy> {
    pub header: Header<F>,
    pub mu: Dimension<F>,
    pub n_lanes: Uint<F>,
    pub bus_dim: Dimension<F>,
    pub rom_offset: Uint<F>,
    pub flock_offset: Uint<F>,
    pub raw_offsets: Vec<Uint<F>>,
    pub packed_offsets: Vec<Uint<F>>,
    pub bus_offsets: Vec<Uint<F>>,
    pub count_offsets: Vec<Uint<F>>,
    pub framework_offsets: [Uint<F>; 4],
}

struct Group<F: Copy> {
    heights: [F; 29],
    columns: usize,
}

impl<F: Copy> Group<F> {
    fn fixed<C: Context<F = F>>(ctx: &C, present: F, height: usize) -> Result<Self, Error> {
        if height > 28 {
            return Err(Error::InvalidInput);
        }
        Ok(Self {
            heights: std::array::from_fn(|i| if i == height { present } else { ctx.zero() }),
            columns: 1,
        })
    }

    fn table<C: Context<F = F>>(ctx: &C, shape: &TableShape<F>, extra: usize, columns: usize) -> Result<Self, Error> {
        if extra > 28 {
            return Err(Error::InvalidInput);
        }
        ctx.assert_zero(ctx.mul(shape.present, shape.dim.contains(28 - extra)))?;
        Ok(Self {
            heights: std::array::from_fn(|i| {
                if i < extra {
                    ctx.zero()
                } else {
                    ctx.mul(shape.present, shape.dim.equals(ctx, i - extra))
                }
            }),
            columns,
        })
    }
}

type Placement<F> = (Vec<Uint<F>>, Uint<F>);

/// Stable decreasing-height placement. At height h the cursor is measured in
/// units of 2^h, allowing short checked adds instead of 32-bit pairwise ranks.
fn place<C: Context>(ctx: &C, groups: &[Group<C::F>]) -> Result<Placement<C::F>, Error> {
    let mut positions = vec![ctx.zero(); groups.len()];
    let mut cursor = Uint::constant(ctx, 0, 1);
    for height in (0..=28).rev() {
        if height < 28 {
            cursor = Uint::from_bits(
                ctx,
                core::iter::once(ctx.zero())
                    .chain(cursor.bits().iter().copied())
                    .collect(),
            )?;
        }
        for (index, group) in groups.iter().enumerate() {
            if group.columns == 0 {
                continue;
            }
            let selected = group.heights[height];
            if group.columns > (1usize << (28 - height)) {
                ctx.assert_zero(selected)?;
                continue;
            }
            positions[index] = ctx.add(
                positions[index],
                ctx.mul(selected, ctx.mul(cursor.value(ctx), ctx.base(1u64 << height))),
            );
            let increment = Uint::select(
                ctx,
                selected,
                &Uint::constant(ctx, group.columns as u64, cursor.width()),
                &Uint::constant(ctx, 0, cursor.width()),
            );
            let (next, carry) = cursor.add(ctx, &increment);
            ctx.assert_zero(carry)?;
            cursor = next;
        }
    }
    ctx.assert_zero(Uint::constant(ctx, 1 << 28, 29).lt(ctx, &cursor))?;
    let size = Uint::from_field(ctx, cursor.value(ctx), 32)?;
    let offsets = positions
        .into_iter()
        .map(|position| Uint::from_field(ctx, position, 32))
        .collect::<Result<_, _>>()?;
    Ok((offsets, size))
}

fn ceil_log<C: Context>(ctx: &C, size: &Uint<C::F>, minimum: usize) -> Result<Dimension<C::F>, Error> {
    let (less_one, borrow) = size.sub(ctx, &Uint::constant(ctx, 1, 32));
    ctx.assert_zero(borrow)?;
    let mut log = Uint::constant(ctx, minimum as u64, 6);
    for i in minimum..28 {
        log = Uint::select(ctx, less_one.bits()[i], &Uint::constant(ctx, (i + 1) as u64, 6), &log);
    }
    Dimension::from_uint(ctx, log, 28)
}

impl<F: Copy> Layout<F> {
    pub(crate) fn new<C: Context<F = F>>(ctx: &C, templates: &Templates, header: Header<F>) -> Result<Self, Error> {
        if templates.specs.len() != TABLES || header.tables.len() != TABLES {
            return Err(Error::InvalidInput);
        }
        let mut private = Vec::with_capacity(2 + 2 * TABLES);
        private.push(Group::fixed(ctx, ctx.one(), templates.rom_log)?);
        private.push(Group::table(ctx, &header.tables[cpu_tables::BLAKE_TABLE], 8, 1)?);
        let mut bus = Vec::with_capacity(4 + TABLES);
        bus.push(Group::fixed(ctx, ctx.one(), 0)?);
        bus.push(Group::fixed(ctx, ctx.one(), templates.rom_log)?);
        bus.push(Group::fixed(ctx, header.tables[RAM_TABLE].present, 0)?);
        bus.push(Group::fixed(ctx, header.tables[REG_TABLE].present, 0)?);
        let mut counts = Vec::with_capacity(TABLES);
        for (spec, shape) in templates.specs.iter().zip(&header.tables) {
            let extra = spec.circuit.k_log.checked_sub(6).ok_or(Error::InvalidInput)?;
            let raw = Group::table(ctx, shape, 0, spec.circuit.raw_columns.len())?;
            // All table flushes share the raw cube's already checked height masks.
            bus.push(Group {
                heights: raw.heights,
                columns: spec.flushes.len(),
            });
            counts.push(Group {
                heights: raw.heights,
                columns: spec.flushes.iter().filter(|flush| flush.count.is_some()).count(),
            });
            private.push(raw);
            private.push(Group::table(ctx, shape, extra, 1)?);
        }
        let (private_offsets, placed) = place(ctx, &private)?;
        let mu = ceil_log(ctx, &placed, 15)?;
        let (lane_log, borrow) = mu.bits().sub(ctx, &Uint::constant(ctx, 6, 6));
        ctx.assert_zero(borrow)?;
        let (last, borrow) = placed.sub(ctx, &Uint::constant(ctx, 1, 32));
        ctx.assert_zero(borrow)?;
        let (lanes, carry) = last.shr(ctx, &lane_log).add(ctx, &Uint::constant(ctx, 1, 32));
        ctx.assert_zero(carry)?;
        let n_lanes = Uint::from_field(ctx, lanes.value(ctx), 7)?;
        ctx.assert_zero(Uint::constant(ctx, 64, 7).lt(ctx, &n_lanes))?;
        let (bus_placements, bus_size) = place(ctx, &bus)?;
        let bus_dim = ceil_log(ctx, &bus_size, 0)?;
        let (count_offsets, count_size) = place(ctx, &counts)?;
        ctx.assert_zero(power(ctx, &bus_dim, 32)?.lt(ctx, &count_size))?;
        Ok(Self {
            header,
            mu,
            n_lanes,
            bus_dim,
            rom_offset: private_offsets[0].clone(),
            flock_offset: private_offsets[1].clone(),
            raw_offsets: (0..TABLES).map(|i| private_offsets[2 + 2 * i].clone()).collect(),
            packed_offsets: (0..TABLES).map(|i| private_offsets[3 + 2 * i].clone()).collect(),
            bus_offsets: bus_placements[4..].to_vec(),
            count_offsets,
            framework_offsets: std::array::from_fn(|i| bus_placements[i].clone()),
        })
    }

    pub(crate) fn parameter<C: Context<F = F>>(
        &self,
        ctx: &C,
        public_bytes: &[F; 32],
        source: PublicSource,
    ) -> Result<F, Error> {
        Ok(match source {
            PublicSource::Cycles => self.header.cycles.value(ctx),
            PublicSource::Byte(index) => {
                let value = *public_bytes.get(index).ok_or(Error::InvalidInput)?;
                Uint::from_field(ctx, value, 8)?.value(ctx)
            }
            PublicSource::MemoryCount(space) => match space {
                Space::Ram => self.header.ram.count.value(ctx),
                Space::Register => self.header.registers.count.value(ctx),
            },
            PublicSource::MemoryRows(space) => {
                let table = match space {
                    Space::Ram => RAM_TABLE,
                    Space::Register => REG_TABLE,
                };
                power(ctx, &self.header.tables[table].dim, 32)?.value(ctx)
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::{Source, Symbolic, Witness};
    use leanvm_guest::Field;
    use riscv_proof::layout::{self, ABSENT};
    use std::sync::LazyLock;

    fn fixture() -> &'static (ProgramInfo, Templates) {
        static FIXTURE: LazyLock<(ProgramInfo, Templates)> = LazyLock::new(|| {
            // One executable ELF segment containing addi a7,zero,0; ecall.
            let code = [0x00000893u32, 0x00000073];
            let mut elf = vec![0u8; 0x108];
            elf[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
            for (at, value) in [(16, 2u16), (18, 243), (52, 64), (54, 56), (56, 1)] {
                elf[at..at + 2].copy_from_slice(&value.to_le_bytes());
            }
            elf[20..24].copy_from_slice(&1u32.to_le_bytes());
            for (at, value) in [
                (24, 0x10000u64),
                (32, 64),
                (72, 0x100),
                (80, 0x10000),
                (96, 8),
                (104, 8),
                (112, 4),
            ] {
                elf[at..at + 8].copy_from_slice(&value.to_le_bytes());
            }
            elf[64..68].copy_from_slice(&1u32.to_le_bytes());
            elf[68..72].copy_from_slice(&5u32.to_le_bytes());
            for (i, word) in code.into_iter().enumerate() {
                elf[0x100 + 4 * i..0x104 + 4 * i].copy_from_slice(&word.to_le_bytes());
            }
            let program = ProgramInfo::from_elf(&elf).unwrap();
            let templates = Templates::new(&program).unwrap();
            (program, templates)
        });
        &FIXTURE
    }

    fn memory(count: u64, registers: bool) -> memory::Header {
        memory::Header {
            count,
            logrows: if count == 0 {
                0
            } else {
                (64 - (count.max(8) - 1).leading_zeros()) as usize
            },
            last_address: u64::from(count != 0),
            last_time: if count == 0 {
                0
            } else if registers {
                (1 << 36) - 1
            } else {
                u64::MAX
            },
            last_value: if count == 0 {
                0
            } else if registers {
                u64::MAX
            } else {
                255
            },
        }
    }

    fn header(count: u64, variant: usize) -> layout::Header {
        let ram = memory(count, false);
        let registers = memory(count, true);
        let mut taus = vec![ABSENT; TABLES];
        for logical in 0..CPU_TABLES {
            if logical % 4 == variant % 4 {
                taus[logical] = 3 + logical % 3;
            }
        }
        if count != 0 {
            taus[RAM_TABLE] = ram.logrows;
            taus[REG_TABLE] = registers.logrows;
        }
        layout::Header {
            cycles: 7 + variant as u64,
            log_inv_rate: 1 + variant % 4,
            taus,
            ram,
            registers,
        }
    }

    fn expected(native: &layout::Layout, bytes: &[u8; 32]) -> Vec<Field> {
        let (bus, size) =
            layout::offsets(&native.blocks[0].iter().map(|block| block.log_rows).collect::<Vec<_>>()).unwrap();
        let (counts, _) =
            layout::offsets(&native.blocks[2].iter().map(|block| block.log_rows).collect::<Vec<_>>()).unwrap();
        let mut raw = vec![0usize; TABLES];
        let mut packed = raw.clone();
        let mut flush = raw.clone();
        let mut count = raw.clone();
        let mut framework = [0usize; 4];
        framework[0] = bus[0];
        framework[1] = bus[1];
        let mut boundary = 2;
        for (i, table) in [RAM_TABLE, REG_TABLE].into_iter().enumerate() {
            if native.header.taus[table] != ABSENT {
                framework[i + 2] = bus[boundary];
                boundary += 1;
            }
        }
        for (index, &logical) in native.table_ids.iter().enumerate() {
            if !native.tables[index].circuit.raw_columns.is_empty() {
                raw[logical] = native.placements[native.bases[index]].offset;
            }
            packed[logical] = native.placements[native.packed_columns[index]].offset;
            if let Some(first) = native.blocks[0].iter().position(|block| block.owner == Some(index)) {
                flush[logical] = bus[first];
            }
            if let Some(first) = native.blocks[2].iter().position(|block| block.owner == Some(index)) {
                count[logical] = counts[first];
            }
        }
        let mut result = vec![
            native.mu as u64,
            native.n_lanes as u64,
            size.next_power_of_two().trailing_zeros() as u64,
            native.placements[0].offset as u64,
            native.flock_column.map_or(0, |column| native.placements[column].offset) as u64,
        ];
        result.extend(
            raw.into_iter()
                .chain(packed)
                .chain(flush)
                .chain(count)
                .chain(framework)
                .map(|n| n as u64),
        );
        result.extend([
            native.header.cycles,
            native.header.ram.count,
            native.header.registers.count,
            1 << native.header.ram.logrows,
            1 << native.header.registers.logrows,
            bytes[0] as u64,
            bytes[31] as u64,
        ]);
        result.into_iter().map(Field::from).collect()
    }

    fn program<C: Context>(ctx: &C, templates: &Templates) -> Result<(), Error> {
        let enabled = ctx.public(0)?;
        let compare = ctx.public(1)?;
        ctx.assert_bool(compare)?;
        let bytes = (0..32).map(|i| ctx.public(2 + i)).collect::<Result<Vec<_>, _>>()?;
        let bytes: [C::F; 32] = bytes.try_into().map_err(|_| Error::InvalidInput)?;
        let mut transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        let header = Header::read(&mut transcript, enabled)?;
        let layout = Layout::new(ctx, templates, header)?;
        let mut result = vec![
            layout.mu.value(ctx),
            layout.n_lanes.value(ctx),
            layout.bus_dim.value(ctx),
            layout.rom_offset.value(ctx),
            layout.flock_offset.value(ctx),
        ];
        result.extend(
            layout
                .raw_offsets
                .iter()
                .chain(&layout.packed_offsets)
                .chain(&layout.bus_offsets)
                .chain(&layout.count_offsets)
                .chain(&layout.framework_offsets)
                .map(|offset| offset.value(ctx)),
        );
        for source in [
            PublicSource::Cycles,
            PublicSource::MemoryCount(Space::Ram),
            PublicSource::MemoryCount(Space::Register),
            PublicSource::MemoryRows(Space::Ram),
            PublicSource::MemoryRows(Space::Register),
            PublicSource::Byte(0),
            PublicSource::Byte(31),
        ] {
            result.push(layout.parameter(ctx, &bytes, source)?);
        }
        for (index, value) in result.into_iter().enumerate() {
            ctx.assert_equal_if(compare, value, ctx.public(34 + index)?)?;
        }
        Ok(())
    }

    #[test]
    fn one_symbolic_layout_matches_native_and_rejects_malformed_boundaries() {
        let (elf, templates) = fixture();
        let bytes = std::array::from_fn(|i| (3 + 7 * i) as u8);
        let baseline = header(9, 0);
        let native = layout::Layout::new(elf, bytes, baseline.clone()).unwrap();
        let public_for = |native: &layout::Layout, enabled: bool| {
            let mut public = vec![Field::from(u64::from(enabled)), Field::ONE];
            public.extend(bytes.map(|byte| Field::from(byte as u64)));
            public.extend(expected(native, &bytes));
            public
        };
        let initial_public = public_for(&native, true);
        let symbolic = Symbolic::new(initial_public.len());
        program(&symbolic, templates).unwrap();
        let circuit = symbolic.finish();
        for (variant, count) in [0, 1, 8, 9, 16, 17, 32, 33].into_iter().enumerate() {
            let header = header(count, variant);
            let native = layout::Layout::new(elf, bytes, header.clone()).unwrap();
            let public = public_for(&native, true);
            let advice = header.values().into_iter().map(Field::from).collect::<Vec<_>>();
            let witness = Witness::new(&public, vec![Source::Advice(&advice)]);
            program(&witness, templates).unwrap();
            circuit.evaluate(&public, &witness.finish().unwrap()).unwrap();
        }
        // Inactive header reads leave the real source empty, but retain a
        // fully constrained fixed ROM/CPU framework layout.
        let mut absent = header(0, 0);
        absent.taus.fill(ABSENT);
        absent.cycles = 1;
        absent.log_inv_rate = 1;
        let native = layout::Layout::new(elf, bytes, absent).unwrap();
        let public = public_for(&native, false);
        let witness = Witness::new(&public, vec![Source::Advice(&[])]);
        program(&witness, templates).unwrap();
        circuit.evaluate(&public, &witness.finish().unwrap()).unwrap();

        // Turn off differential output checks: rejection below must come
        // from the header/layout relation, not stale expected offsets.
        let mut public = initial_public;
        public[1] = Field::ZERO;
        let good = baseline.values().into_iter().map(Field::from).collect::<Vec<_>>();
        let ram = 2 + TABLES;
        let reg = ram + 4;
        let mut malformed = Vec::new();
        for (index, value) in [
            (0, 0),
            (0, 1 << 32),
            (1, 0),
            (1, 5),
            (2, 1),
            (2, 3),
            (2, 34),
            (2, 29),
            (2 + RAM_TABLE, 0),
            (2 + RAM_TABLE, 4),
            (ram, 0),
            (ram, 8),
            (ram, 17),
            (ram, (1 << 32) + 1),
            (ram + 1, 1 << 32),
            (ram + 3, 256),
            (reg, (1 << 36) + 1),
            (reg + 1, 32),
            (reg + 1, 0),
            (reg + 2, 1 << 36),
            (2 + cpu_tables::BLAKE_TABLE, 22),
        ] {
            let mut bad = good.clone();
            bad[index] = Field::from(value);
            malformed.push(bad);
        }
        let mut noncanonical = good.clone();
        noncanonical[0] = Field([7, 1, 0]);
        malformed.push(noncanonical);
        // A present height-three memory table must not encode an empty
        // history, and an absent history must have zero terminal metadata.
        let mut empty = good.clone();
        empty[ram] = Field::ZERO;
        empty[2 + RAM_TABLE] = Field::ZERO;
        malformed.push(empty);
        // Each individual cube fits, but two height-28 packed cubes cannot
        // fit in the committed capacity.
        let mut overflow = good.clone();
        for logical in 0..2 {
            overflow[2 + logical] = Field::from((29 - (templates.specs[logical].circuit.k_log - 6)) as u64);
        }
        malformed.push(overflow);
        for bad in malformed {
            let witness = Witness::new(&public, vec![Source::Advice(&bad)]);
            assert!(program(&witness, templates).is_err());
            assert!(circuit.evaluate(&public, &bad).is_err());
        }
        let mut invalid_byte = public.clone();
        invalid_byte[2] = Field::from(256);
        let witness = Witness::new(&invalid_byte, vec![Source::Advice(&good)]);
        assert!(program(&witness, templates).is_err());
        assert!(circuit.evaluate(&invalid_byte, &good).is_err());
    }
}
