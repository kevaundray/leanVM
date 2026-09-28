use crate::{Error, ErrorKind};

/// The complete unprivileged RV64IM semantic instruction set. CSR, FENCE.I,
/// atomics, compressed instructions, and privileged instructions are not RV64IM.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Lui,
    Auipc,
    Jal,
    Jalr,
    Beq,
    Bne,
    Blt,
    Bge,
    Bltu,
    Bgeu,
    Lb,
    Lh,
    Lw,
    Ld,
    Lbu,
    Lhu,
    Lwu,
    Sb,
    Sh,
    Sw,
    Sd,
    Addi,
    Slti,
    Sltiu,
    Xori,
    Ori,
    Andi,
    Slli,
    Srli,
    Srai,
    Add,
    Sub,
    Sll,
    Slt,
    Sltu,
    Xor,
    Srl,
    Sra,
    Or,
    And,
    Addiw,
    Slliw,
    Srliw,
    Sraiw,
    Addw,
    Subw,
    Sllw,
    Srlw,
    Sraw,
    Mul,
    Mulh,
    Mulhsu,
    Mulhu,
    Div,
    Divu,
    Rem,
    Remu,
    Mulw,
    Divw,
    Divuw,
    Remw,
    Remuw,
    Fence,
    Ecall,
    Ebreak,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    Upper,
    Jump,
    Branch,
    Load,
    Store,
    Immediate,
    Register,
    Fence,
    System,
}

/// Register fields are the *raw* bit fields, even when unused by an opcode.
/// `immediate` is sign-extended, except shift amounts and FENCE's 12-bit mask.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Decoded {
    pub raw: u32,
    pub op: Op,
    pub class: Class,
    pub rd: u8,
    pub rs1: u8,
    pub rs2: u8,
    pub immediate: i64,
}

pub(crate) fn sext(value: u64, bits: u32) -> u64 {
    ((value << (64 - bits)) as i64 >> (64 - bits)) as u64
}

/// Decode exactly one 32-bit instruction, reporting the supplied PC on failure.
pub fn decode(raw: u32, pc: u64) -> Result<Decoded, Error> {
    use Op::*;
    let rd = ((raw >> 7) & 31) as u8;
    let rs1 = ((raw >> 15) & 31) as u8;
    let rs2 = ((raw >> 20) & 31) as u8;
    let f3 = (raw >> 12) & 7;
    let f7 = raw >> 25;
    let invalid = || Error {
        pc,
        kind: ErrorKind::IllegalInstruction(raw),
    };
    let i_imm = sext((raw >> 20) as u64, 12) as i64;
    let (op, class, immediate) = match raw & 0x7f {
        0x37 => (Lui, Class::Upper, sext((raw & 0xfffff000) as u64, 32) as i64),
        0x17 => (Auipc, Class::Upper, sext((raw & 0xfffff000) as u64, 32) as i64),
        0x6f => {
            let imm = ((raw >> 31) << 20)
                | (((raw >> 12) & 255) << 12)
                | (((raw >> 20) & 1) << 11)
                | (((raw >> 21) & 1023) << 1);
            (Jal, Class::Jump, sext(imm as u64, 21) as i64)
        }
        0x67 if f3 == 0 => (Jalr, Class::Jump, i_imm),
        0x63 => {
            let op = match f3 {
                0 => Beq,
                1 => Bne,
                4 => Blt,
                5 => Bge,
                6 => Bltu,
                7 => Bgeu,
                _ => return Err(invalid()),
            };
            let imm =
                ((raw >> 31) << 12) | (((raw >> 7) & 1) << 11) | (((raw >> 25) & 63) << 5) | (((raw >> 8) & 15) << 1);
            (op, Class::Branch, sext(imm as u64, 13) as i64)
        }
        0x03 => {
            let op = match f3 {
                0 => Lb,
                1 => Lh,
                2 => Lw,
                3 => Ld,
                4 => Lbu,
                5 => Lhu,
                6 => Lwu,
                _ => return Err(invalid()),
            };
            (op, Class::Load, i_imm)
        }
        0x23 => {
            let op = match f3 {
                0 => Sb,
                1 => Sh,
                2 => Sw,
                3 => Sd,
                _ => return Err(invalid()),
            };
            let imm = ((raw >> 25) << 5) | ((raw >> 7) & 31);
            (op, Class::Store, sext(imm as u64, 12) as i64)
        }
        0x13 => {
            let op = match f3 {
                0 => Addi,
                2 => Slti,
                3 => Sltiu,
                4 => Xori,
                6 => Ori,
                7 => Andi,
                1 if raw >> 26 == 0 => Slli,
                5 if raw >> 26 == 0 => Srli,
                5 if raw >> 26 == 0x10 => Srai,
                _ => return Err(invalid()),
            };
            (
                op,
                Class::Immediate,
                if f3 == 1 || f3 == 5 {
                    ((raw >> 20) & 63) as i64
                } else {
                    i_imm
                },
            )
        }
        0x1b => {
            let op = match (f3, f7) {
                (0, _) => Addiw,
                (1, 0) => Slliw,
                (5, 0) => Srliw,
                (5, 0x20) => Sraiw,
                _ => return Err(invalid()),
            };
            (op, Class::Immediate, if f3 == 0 { i_imm } else { rs2 as i64 })
        }
        0x33 => {
            let op = match (f7, f3) {
                (0, 0) => Add,
                (0x20, 0) => Sub,
                (0, 1) => Sll,
                (0, 2) => Slt,
                (0, 3) => Sltu,
                (0, 4) => Xor,
                (0, 5) => Srl,
                (0x20, 5) => Sra,
                (0, 6) => Or,
                (0, 7) => And,
                (1, 0) => Mul,
                (1, 1) => Mulh,
                (1, 2) => Mulhsu,
                (1, 3) => Mulhu,
                (1, 4) => Div,
                (1, 5) => Divu,
                (1, 6) => Rem,
                (1, 7) => Remu,
                _ => return Err(invalid()),
            };
            (op, Class::Register, 0)
        }
        0x3b => {
            let op = match (f7, f3) {
                (0, 0) => Addw,
                (0x20, 0) => Subw,
                (0, 1) => Sllw,
                (0, 5) => Srlw,
                (0x20, 5) => Sraw,
                (1, 0) => Mulw,
                (1, 4) => Divw,
                (1, 5) => Divuw,
                (1, 6) => Remw,
                (1, 7) => Remuw,
                _ => return Err(invalid()),
            };
            (op, Class::Register, 0)
        }
        // Base FENCE ignores rd/rs1. The defined FENCE.TSO mask is also a
        // fence on this single-hart, sequentially consistent machine.
        0x0f if f3 == 0 && (raw >> 28 == 0 || raw >> 20 == 0x833) => (Fence, Class::Fence, (raw >> 20) as i64),
        0x73 if raw == 0x00000073 => (Ecall, Class::System, 0),
        0x73 if raw == 0x00100073 => (Ebreak, Class::System, 0),
        _ => return Err(invalid()),
    };
    Ok(Decoded {
        raw,
        op,
        class,
        rd,
        rs1,
        rs2,
        immediate,
    })
}
