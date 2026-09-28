use crate::portable::{algebra::log2_ceil, transcript::Transcript};
use crate::{
    Error, ProgramInfo, cpu_tables, memory,
    packed::PackedSpec,
    schema::{Coord, SEP_CPU, SEP_ROM, Space},
};
use alloc::{vec, vec::Vec};

pub const ROM_COUNTS: usize = 0;
pub const ABSENT: usize = usize::MAX;
pub const CPU_TABLES: usize = 69;
pub const TABLES: usize = CPU_TABLES + 2;
pub const RAM_TABLE: usize = CPU_TABLES;
pub const REG_TABLE: usize = CPU_TABLES + 1;

#[derive(Clone, Debug)]
pub struct Header {
    pub cycles: u64,
    pub log_inv_rate: usize,
    pub taus: Vec<usize>,
    pub ram: memory::Header,
    pub registers: memory::Header,
}

impl Header {
    pub fn read(transcript: &mut Transcript<'_>) -> Result<Self, Error> {
        fn number(t: &mut Transcript<'_>) -> Result<u64, Error> {
            let f = t.next_scalar()?;
            if f.0[1] != 0 || f.0[2] != 0 {
                return Err(Error::InvalidShape);
            }
            Ok(f.0[0])
        }
        let cycles = number(transcript)?;
        let log_inv_rate = usize::try_from(number(transcript)?).map_err(|_| Error::InvalidShape)?;
        let mut taus = Vec::with_capacity(TABLES);
        for _ in 0..TABLES {
            let encoded = usize::try_from(number(transcript)?).map_err(|_| Error::InvalidShape)?;
            taus.push(if encoded == 0 { ABSENT } else { encoded - 1 });
        }
        let mut read_memory = |table| -> Result<memory::Header, Error> {
            Ok(memory::Header {
                count: number(transcript)?,
                logrows: if taus[table] == ABSENT { 0 } else { taus[table] },
                last_address: number(transcript)?,
                last_time: number(transcript)?,
                last_value: number(transcript)?,
            })
        };
        let ram = read_memory(RAM_TABLE)?;
        let registers = read_memory(REG_TABLE)?;
        let header = Self {
            cycles,
            log_inv_rate,
            taus,
            ram,
            registers,
        };
        header.validate()?;
        Ok(header)
    }

    pub fn values(&self) -> Vec<u64> {
        let mut values = vec![self.cycles, self.log_inv_rate as u64];
        values.extend(
            self.taus
                .iter()
                .map(|&tau| if tau == ABSENT { 0 } else { tau as u64 + 1 }),
        );
        for memory in [&self.ram, &self.registers] {
            values.extend([memory.count, memory.last_address, memory.last_time, memory.last_value]);
        }
        values
    }

    pub fn validate(&self) -> Result<(), Error> {
        if self.cycles == 0
            || self.cycles >= 1u64 << 32
            || !(1..=4).contains(&self.log_inv_rate)
            || self.taus.len() != TABLES
            || self.taus.iter().any(|&tau| tau != ABSENT && !(3..=32).contains(&tau))
        {
            return Err(Error::InvalidShape);
        }
        for (table, memory) in [(RAM_TABLE, &self.ram), (REG_TABLE, &self.registers)] {
            if memory.count == 0 {
                if self.taus[table] != ABSENT || memory.logrows != 0 {
                    return Err(Error::InvalidShape);
                }
            } else if self.taus[table] != memory.logrows {
                return Err(Error::InvalidShape);
            }
        }
        self.ram.validate(Space::Ram)?;
        self.registers.validate(Space::Register)?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum Coordinate {
    Constant(u64),
    Column(usize),
    Scaled(usize, u64),
    Product(usize, usize, u64),
    Sum(Vec<Coordinate>),
    Public(usize),
}

impl Coordinate {
    pub fn from_local(coord: &Coord, base: usize) -> Self {
        match coord {
            Coord::Constant(v) => Self::Constant(*v),
            Coord::Column(c) => Self::Column(base + c),
            Coord::Scaled(c, k) | Coord::PublicScaled(c, _, k) => Self::Scaled(base + c, *k),
            Coord::Product(a, b, k) => Self::Product(base + a, base + b, *k),
            Coord::Sum(terms) => Self::Sum(terms.iter().map(|c| Self::from_local(c, base)).collect()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Block {
    pub log_rows: usize,
    pub coordinates: Vec<Coordinate>,
    pub owner: Option<usize>,
}

#[derive(Clone, Copy, Debug)]
pub struct Placement {
    pub offset: usize,
    pub log_rows: Option<usize>,
}

#[derive(Clone, Debug)]
pub struct Layout {
    pub header: Header,
    pub tables: Vec<PackedSpec>,
    pub table_ids: Vec<usize>,
    pub bases: Vec<usize>,
    pub packed_columns: Vec<usize>,
    pub flock_column: Option<usize>,
    pub placements: Vec<Placement>,
    pub public_columns: Vec<Vec<u64>>,
    pub blocks: [Vec<Block>; 3],
    pub mu: usize,
    pub n_lanes: usize,
    pub flock_log: Option<usize>,
}

pub fn offsets(logs: &[usize]) -> Result<(Vec<usize>, usize), Error> {
    let mut order: Vec<usize> = (0..logs.len()).collect();
    order.sort_by(|&a, &b| logs[b].cmp(&logs[a]).then(a.cmp(&b)));
    let mut offsets = vec![0; logs.len()];
    let mut size = 0usize;
    for index in order {
        let length = 1usize.checked_shl(logs[index] as u32).ok_or(Error::InvalidShape)?;
        offsets[index] = size;
        size = size.checked_add(length).ok_or(Error::InvalidShape)?;
    }
    Ok((offsets, size))
}

impl Layout {
    pub fn new(program: &ProgramInfo, public: [u8; 32], header: Header) -> Result<Self, Error> {
        header.validate()?;
        let mut tables = Vec::new();
        let mut table_ids = Vec::new();
        let mut memory_boundaries = Vec::new();
        for logical in 0..TABLES {
            if header.taus[logical] == ABSENT {
                continue;
            }
            let spec = if logical < CPU_TABLES {
                cpu_tables::build_spec(public, header.cycles, logical)
            } else {
                let (space, memory_header) = if logical == RAM_TABLE {
                    (Space::Ram, &header.ram)
                } else {
                    (Space::Register, &header.registers)
                };
                let (spec, boundary) = memory::build_spec(program, space, memory_header.count, memory_header.logrows)?;
                memory_boundaries.push((logical, boundary));
                spec
            };
            table_ids.push(logical);
            tables.push(PackedSpec::new(&spec));
        }
        let (mut rom_keys, mut rom_values): (Vec<_>, Vec<_>) = program.rom_entries().into_iter().unzip();
        let rom_length = rom_keys
            .len()
            .max(1)
            .checked_next_power_of_two()
            .ok_or(Error::InvalidShape)?;
        rom_keys.resize(rom_length, u64::MAX);
        rom_values.resize(rom_length, 0);
        let rom_log = rom_length.trailing_zeros() as usize;
        let flock_log =
            (header.taus[cpu_tables::BLAKE_TABLE] != ABSENT).then(|| 8 + header.taus[cpu_tables::BLAKE_TABLE]);
        let mut kappas = vec![rom_log];
        let flock_column = flock_log.map(|log| {
            let index = kappas.len();
            kappas.push(log);
            index
        });
        let mut bases = Vec::with_capacity(tables.len());
        let mut packed_columns = Vec::with_capacity(tables.len());
        for (table, &logical) in tables.iter().zip(&table_ids) {
            let tau = header.taus[logical];
            bases.push(kappas.len());
            kappas.extend(core::iter::repeat_n(tau, table.circuit.raw_columns.len()));
            packed_columns.push(kappas.len());
            kappas.push(table.circuit.k_log + tau - 6);
        }
        // Reject oversized layouts before allocating committed windows.
        if kappas.iter().any(|&log| log > 28) {
            return Err(Error::InvalidShape);
        }
        let (positions, placed) = offsets(&kappas)?;
        let placements = positions
            .into_iter()
            .zip(kappas)
            .map(|(offset, log)| Placement {
                offset,
                log_rows: Some(log),
            })
            .collect();
        let mu = log2_ceil(placed.max(1)).max(15);
        if mu > 28 {
            return Err(Error::InvalidShape);
        }
        let n_lanes = placed.div_ceil(1usize << (mu - 6)).max(1);
        let mut blocks: [Vec<Block>; 3] = core::array::from_fn(|_| Vec::new());
        let mut boundary = |push: Vec<Coordinate>, pull: Vec<Coordinate>, log_rows: usize| {
            blocks[0].push(Block {
                log_rows,
                coordinates: push,
                owner: None,
            });
            blocks[1].push(Block {
                log_rows,
                coordinates: pull,
                owner: None,
            });
        };
        boundary(
            vec![
                Coordinate::Constant(SEP_CPU),
                Coordinate::Constant(program.entry()),
                Coordinate::Constant(0),
                Coordinate::Constant(0),
            ],
            vec![
                Coordinate::Constant(SEP_CPU),
                Coordinate::Constant(0),
                Coordinate::Constant(header.cycles),
                Coordinate::Constant(1),
            ],
            0,
        );
        boundary(
            vec![
                Coordinate::Constant(SEP_ROM),
                Coordinate::Public(0),
                Coordinate::Constant(1),
                Coordinate::Public(1),
            ],
            vec![
                Coordinate::Constant(SEP_ROM),
                Coordinate::Public(0),
                Coordinate::Column(ROM_COUNTS),
                Coordinate::Public(1),
            ],
            rom_log,
        );
        for (logical, boundary_spec) in memory_boundaries {
            let memory_header = if logical == RAM_TABLE {
                &header.ram
            } else {
                &header.registers
            };
            let flush = boundary_spec.flush(memory_header)?;
            boundary(
                flush.push.iter().map(|c| Coordinate::from_local(c, 0)).collect(),
                flush.pull.iter().map(|c| Coordinate::from_local(c, 0)).collect(),
                0,
            );
        }
        for (index, table) in tables.iter().enumerate() {
            for flush in &table.flushes {
                for (side, coordinates) in [(0, &flush.push), (1, &flush.pull)] {
                    blocks[side].push(Block {
                        log_rows: header.taus[table_ids[index]],
                        owner: Some(index),
                        coordinates: coordinates
                            .iter()
                            .map(|c| Coordinate::from_local(c, bases[index]))
                            .collect(),
                    });
                }
                if let Some(count) = &flush.count {
                    blocks[2].push(Block {
                        log_rows: header.taus[table_ids[index]],
                        owner: Some(index),
                        coordinates: vec![Coordinate::from_local(count, bases[index])],
                    });
                }
            }
        }
        Ok(Self {
            header,
            tables,
            table_ids,
            bases,
            packed_columns,
            flock_column,
            placements,
            public_columns: vec![rom_keys, rom_values],
            blocks,
            mu,
            n_lanes,
            flock_log,
        })
    }

    pub fn committed_len(&self) -> usize {
        self.n_lanes << (self.mu - 6)
    }

    pub fn table_tau(&self, table: usize) -> usize {
        self.header.taus[self.table_ids[table]]
    }
}
