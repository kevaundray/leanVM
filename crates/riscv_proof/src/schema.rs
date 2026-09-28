use crate::{Error, ProgramInfo, circuit::Circuit};
use alloc::{collections::BTreeMap, vec::Vec};
use leanvm_guest::Field;

pub const SEP_CPU: u64 = 1;
pub const SEP_RAM: u64 = 2;
pub const SEP_REG: u64 = 4;
pub const SEP_ROM: u64 = 8;
pub const SEP_SORT_RAM: u64 = 16;
pub const SEP_SORT_REG: u64 = 32;
pub const SEP_SYSCALL: u64 = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PublicSource {
    Cycles,
    Byte(usize),
    MemoryCount(Space),
    MemoryRows(Space),
}

#[derive(Clone, Debug)]
pub enum Coord {
    Constant(u64),
    Column(usize),
    Scaled(usize, u64),
    PublicScaled(usize, PublicSource, u64),
    Product(usize, usize, u64),
    Sum(Vec<Coord>),
}

impl Coord {
    pub fn eval(&self, columns: &[Field], quadratic: bool) -> Field {
        self.eval_with(&|c| columns[c], quadratic)
    }

    #[cfg(feature = "host")]
    pub fn accumulate(&self, form: &mut lean_vm::leaf::BusForm, weight: primitives::field::F192) {
        use primitives::field::F64;
        match self {
            Self::Constant(value) => form.constant += weight.mul_base(F64(*value)),
            Self::Column(column) => form.coeffs[*column] += weight,
            Self::Scaled(column, coefficient) | Self::PublicScaled(column, _, coefficient) => {
                form.coeffs[*column] += weight.mul_base(F64(*coefficient));
            }
            Self::Product(a, b, coefficient) => form.prods.push((*a, *b, weight.mul_base(F64(*coefficient)))),
            Self::Sum(terms) => {
                for term in terms {
                    term.accumulate(form, weight);
                }
            }
        }
    }

    #[cfg(feature = "host")]
    pub(crate) fn eval_raw(&self, columns: &[u64]) -> Field {
        self.eval_with(&|c| Field::from(columns[c]), false)
    }

    fn eval_with(&self, column: &impl Fn(usize) -> Field, quadratic: bool) -> Field {
        match self {
            Self::Constant(v) => {
                if quadratic {
                    Field::ZERO
                } else {
                    Field::from(*v)
                }
            }
            Self::Column(c) => {
                if quadratic {
                    Field::ZERO
                } else {
                    column(*c)
                }
            }
            Self::Scaled(c, k) | Self::PublicScaled(c, _, k) => {
                if quadratic {
                    Field::ZERO
                } else {
                    column(*c) * Field::from(*k)
                }
            }
            Self::Product(a, b, k) => column(*a) * column(*b) * Field::from(*k),
            Self::Sum(terms) => terms
                .iter()
                .fold(Field::ZERO, |sum, term| sum + term.eval_with(column, quadratic)),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Flush {
    pub push: Vec<Coord>,
    pub pull: Vec<Coord>,
    pub count: Option<Coord>,
}

#[derive(Clone, Debug)]
pub struct TableSpec {
    pub circuit: Circuit,
    pub relations: Vec<Coord>,
    pub flushes: Vec<Flush>,
    /// Raw circuit column to packed Flock slot for the BLAKE2s linkage.
    pub flock_slots: Vec<(usize, usize)>,
}

impl TableSpec {
    pub fn new(circuit: Circuit) -> Self {
        Self {
            circuit,
            relations: Vec::new(),
            flushes: Vec::new(),
            flock_slots: Vec::new(),
        }
    }

    pub fn constraints(&self) -> usize {
        self.circuit.constraints() + self.relations.len()
    }

    pub fn constraint(&self, index: usize, columns: &[Field], quadratic: bool) -> Field {
        if index < self.circuit.constraints() {
            self.circuit.constraint(index, columns, quadratic)
        } else {
            self.relations[index - self.circuit.constraints()].eval(columns, quadratic)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Space {
    Ram,
    Register,
}

#[derive(Clone, Copy, Debug)]
pub struct Access {
    pub space: Space,
    pub address: u64,
    pub time: u64,
    pub before: u64,
    pub after: u64,
    pub write: bool,
}

#[derive(Clone, Debug)]
pub struct TableRows {
    pub spec: TableSpec,
    pub packing: crate::packed::PackedSpec,
    pub rows: Vec<crate::packed::PackedRow>,
}

#[derive(Clone, Debug, Default)]
pub struct InputValues(pub Vec<bool>);

impl InputValues {
    pub fn word(&mut self, value: u64, width: usize) {
        assert!(width <= 64);
        self.0.extend((0..width).map(|bit| value >> bit & 1 != 0));
    }

    pub fn bit(&mut self, value: bool) {
        self.0.push(value);
    }
}

/// Read-only lookup counts, shared by instruction fetch and RAM initialization.
#[derive(Clone, Debug)]
pub struct RomCounter {
    counts: BTreeMap<u64, u64>,
}

impl RomCounter {
    pub fn new(program: &ProgramInfo) -> Self {
        let counts = program.rom_entries().into_iter().map(|(key, _)| (key, 0)).collect();
        Self { counts }
    }

    pub fn take(&mut self, key: u64) -> Result<u64, Error> {
        let count = self.counts.get_mut(&key).ok_or(Error::InvalidProgram)?;
        let value = base_power(*count);
        *count = count.checked_add(1).ok_or(Error::InvalidShape)?;
        Ok(value)
    }

    pub fn final_count(&self, key: u64) -> u64 {
        base_power(self.counts.get(&key).copied().unwrap_or(0))
    }
}

fn base_power(exponent: u64) -> u64 {
    #[cfg(feature = "host")]
    {
        primitives::field::g_pow(exponent as usize).0
    }
    #[cfg(not(feature = "host"))]
    {
        Field::from(2).pow(exponent).0[0]
    }
}
