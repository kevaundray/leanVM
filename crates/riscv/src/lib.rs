//! Native RV64IM execution with raw-instruction, register, and byte-memory traces.
//! Execution is not a proof: consumers must constrain these traces and bind the
//! immutable program image and public input in their proof system.

mod decode;
mod elf;
mod execute;
mod memory;

pub use decode::{Class, Decoded, Op, decode};
pub use elf::{Program, Segment};
pub use memory::{MemorySnapshot, PAGE_SIZE};

pub const RAM_END: u64 = 1u64 << 32;
pub const STACK_TOP: u64 = RAM_END;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    /// Faulting instruction PC, or ELF entry (zero before it can be read).
    pub pc: u64,
    pub kind: ErrorKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    InvalidElf(&'static str),
    IllegalInstruction(u32),
    MisalignedPc(u64),
    MemoryOutOfBounds { address: u64, length: u64 },
    PermissionDenied { address: u64, kind: AccessKind },
    Breakpoint,
    UnknownEcall(u64),
    ExitFailure(u64),
    WitnessExhausted { requested: u64, remaining: u64 },
    CycleLimit,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RV64IM error at PC {:#x}: {:?}", self.pc, self.kind)
    }
}
impl std::error::Error for Error {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AccessKind {
    Fetch,
    Read,
    Write,
}

/// One data/ECALL byte in temporal order. Reads have before == after.
/// Writes retain the replaced byte, including writes which preserve its value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryEvent {
    pub address: u64,
    pub before: u8,
    pub after: u8,
    pub kind: AccessKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ecall {
    Exit,
    ReadWitness { offset: u64, length: u64 },
    ReadPublic,
    Blake2s,
    F192Mul,
}

/// Only the pre-instruction register values consumed by the proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperandValues {
    Instruction {
        rs1: u64,
        rs2: u64,
        rd: u64,
    },
    Ecall {
        a0: u64,
        a1: u64,
        a2: u64,
        a3: u64,
        a4: u64,
        a5: u64,
        number: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub pc: u64,
    pub instruction: u32,
    pub next_pc: u64,
    pub operands: OperandValues,
    /// Data/ECALL accesses only; instruction fetch is bound by pc/instruction.
    pub memory: Vec<MemoryEvent>,
    pub ecall: Option<Ecall>,
    pub witness_offset_before: u64,
    pub witness_offset_after: u64,
}

impl Step {
    /// Resolve a captured register by its raw instruction field or ECALL ABI.
    /// Uncaptured registers are unavailable, not implicitly zero. In particular,
    /// raw x0 operand values are retained so proof checks can reject forged ones.
    pub fn register_before(&self, index: usize) -> Option<u64> {
        match self.operands {
            OperandValues::Instruction { rs1, rs2, rd } => {
                if index == ((self.instruction >> 15) & 31) as usize {
                    Some(rs1)
                } else if index == ((self.instruction >> 20) & 31) as usize {
                    Some(rs2)
                } else if index == ((self.instruction >> 7) & 31) as usize {
                    Some(rd)
                } else {
                    None
                }
            }
            OperandValues::Ecall {
                a0,
                a1,
                a2,
                a3,
                a4,
                a5,
                number,
            } => match index {
                0 => Some(0),
                10 => Some(a0),
                11 => Some(a1),
                12 => Some(a2),
                13 => Some(a3),
                14 => Some(a4),
                15 => Some(a5),
                17 => Some(number),
                _ => None,
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct Execution<T = Vec<Step>> {
    pub steps: T,
    pub registers: [u64; 32],
    /// Includes the successful EXIT instruction.
    pub cycles: u64,
    pub public: [u8; 32],
    pub witness_consumed: u64,
    /// Initial mapped data plus final writes, in sparse pages. All other bytes
    /// below RAM_END are zero.
    pub memory: MemorySnapshot,
}

#[cfg(test)]
mod tests;
