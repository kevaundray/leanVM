//! Fixed native RV64IM instruction circuits. Program lookup and chronological
//! state/memory buses are external; this module constrains their instruction
//! semantics, register indices, byte values, and addresses.

use crate::circuit::{Bit, Circuit};
use alloc::{vec, vec::Vec};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Opcode {
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
}

impl Opcode {
    pub const ALL: [Self; 64] = [
        Self::Lui,
        Self::Auipc,
        Self::Jal,
        Self::Jalr,
        Self::Beq,
        Self::Bne,
        Self::Blt,
        Self::Bge,
        Self::Bltu,
        Self::Bgeu,
        Self::Lb,
        Self::Lh,
        Self::Lw,
        Self::Ld,
        Self::Lbu,
        Self::Lhu,
        Self::Lwu,
        Self::Sb,
        Self::Sh,
        Self::Sw,
        Self::Sd,
        Self::Addi,
        Self::Slti,
        Self::Sltiu,
        Self::Xori,
        Self::Ori,
        Self::Andi,
        Self::Slli,
        Self::Srli,
        Self::Srai,
        Self::Add,
        Self::Sub,
        Self::Sll,
        Self::Slt,
        Self::Sltu,
        Self::Xor,
        Self::Srl,
        Self::Sra,
        Self::Or,
        Self::And,
        Self::Addiw,
        Self::Slliw,
        Self::Srliw,
        Self::Sraiw,
        Self::Addw,
        Self::Subw,
        Self::Sllw,
        Self::Srlw,
        Self::Sraw,
        Self::Mul,
        Self::Mulh,
        Self::Mulhsu,
        Self::Mulhu,
        Self::Div,
        Self::Divu,
        Self::Rem,
        Self::Remu,
        Self::Mulw,
        Self::Divw,
        Self::Divuw,
        Self::Remw,
        Self::Remuw,
        Self::Fence,
        Self::Ecall,
    ];

    /// Bits which distinguish this operation. Unmasked operand/immediate fields
    /// remain variables, and are separately decoded by the circuit.
    pub const fn encoding(self) -> (u32, u32) {
        use Opcode::*;
        let i = 0x0000707f;
        let r = 0xfe00707f;
        let s = 0xfc00707f;
        match self {
            Lui => (0x7f, 0x37),
            Auipc => (0x7f, 0x17),
            Jal => (0x7f, 0x6f),
            Jalr => (i, 0x67),
            Beq => (i, 0x63),
            Bne => (i, 0x1063),
            Blt => (i, 0x4063),
            Bge => (i, 0x5063),
            Bltu => (i, 0x6063),
            Bgeu => (i, 0x7063),
            Lb => (i, 0x03),
            Lh => (i, 0x1003),
            Lw => (i, 0x2003),
            Ld => (i, 0x3003),
            Lbu => (i, 0x4003),
            Lhu => (i, 0x5003),
            Lwu => (i, 0x6003),
            Sb => (i, 0x23),
            Sh => (i, 0x1023),
            Sw => (i, 0x2023),
            Sd => (i, 0x3023),
            Addi => (i, 0x13),
            Slti => (i, 0x2013),
            Sltiu => (i, 0x3013),
            Xori => (i, 0x4013),
            Ori => (i, 0x6013),
            Andi => (i, 0x7013),
            Slli => (s, 0x1013),
            Srli => (s, 0x5013),
            Srai => (s, 0x40005013),
            Add => (r, 0x33),
            Sub => (r, 0x40000033),
            Sll => (r, 0x1033),
            Slt => (r, 0x2033),
            Sltu => (r, 0x3033),
            Xor => (r, 0x4033),
            Srl => (r, 0x5033),
            Sra => (r, 0x40005033),
            Or => (r, 0x6033),
            And => (r, 0x7033),
            Addiw => (i, 0x1b),
            Slliw => (r, 0x101b),
            Srliw => (r, 0x501b),
            Sraiw => (r, 0x4000501b),
            Addw => (r, 0x3b),
            Subw => (r, 0x4000003b),
            Sllw => (r, 0x103b),
            Srlw => (r, 0x503b),
            Sraw => (r, 0x4000503b),
            Mul => (r, 0x02000033),
            Mulh => (r, 0x02001033),
            Mulhsu => (r, 0x02002033),
            Mulhu => (r, 0x02003033),
            Div => (r, 0x02004033),
            Divu => (r, 0x02005033),
            Rem => (r, 0x02006033),
            Remu => (r, 0x02007033),
            Mulw => (r, 0x0200003b),
            Divw => (r, 0x0200403b),
            Divuw => (r, 0x0200503b),
            Remw => (r, 0x0200603b),
            Remuw => (r, 0x0200703b),
            Fence => (i, 0x0f),
            Ecall => (u32::MAX, 0x73),
        }
    }

    pub fn decode(raw: u32) -> Option<Self> {
        Self::ALL.into_iter().find(|&op| {
            let (mask, value) = op.encoding();
            raw & mask == value && (op != Self::Fence || raw >> 28 == 0 || raw >> 20 == 0x833)
        })
    }

    pub const fn memory_width(self) -> usize {
        use Opcode::*;
        match self {
            Lb | Lbu | Sb => 1,
            Lh | Lhu | Sh => 2,
            Lw | Lwu | Sw => 4,
            Ld | Sd => 8,
            _ => 0,
        }
    }

    pub const fn is_store(self) -> bool {
        matches!(self, Self::Sb | Self::Sh | Self::Sw | Self::Sd)
    }
}

#[derive(Clone, Debug)]
pub struct InstructionCircuit {
    pub op: Opcode,
    pub circuit: Circuit,
    pub raw: usize,
    pub pc: usize,
    pub next_pc: usize,
    pub rs1: usize,
    pub rs2: usize,
    pub rd: usize,
    pub rs1_value: usize,
    pub rs2_value: usize,
    /// The value written architecturally; always zero when rd is x0.
    pub rd_value: Option<usize>,
    pub memory_address: Option<usize>,
    pub memory_bytes: Vec<usize>,
    pub memory_write: bool,
    pub raw_bits: Vec<Bit>,
    pub pc_bits: Vec<Bit>,
    pub next_pc_bits: Vec<Bit>,
    pub rs1_value_bits: Vec<Bit>,
    pub rs2_value_bits: Vec<Bit>,
    pub rd_value_bits: Option<Vec<Bit>>,
    pub memory_address_bits: Option<Vec<Bit>>,
    pub memory_byte_bits: Vec<Vec<Bit>>,
}

fn constrain_zero_register(c: &mut Circuit, index: &[Bit], value: &[Bit]) {
    let zero = c.constant(0, index.len());
    let is_zero = c.equals(index, &zero);
    for &bit in value {
        let forbidden = c.and(is_zero, bit);
        c.assert_equal(forbidden, Circuit::ZERO);
    }
}

impl InstructionCircuit {
    pub fn build(op: Opcode) -> Self {
        use Opcode::*;
        let mut c = Circuit::default();
        let raw_bits = c.input_word(32);
        let pc_bits = c.input_word(64);
        let a = c.input_word(64);
        let b = c.input_word(64);
        let width = op.memory_width();
        let load: Vec<_> = if width != 0 && !op.is_store() {
            c.input_word(width * 8)
        } else {
            Vec::new()
        };
        let (mask, encoding) = op.encoding();
        for i in 0..32 {
            if mask >> i & 1 != 0 {
                c.assert_equal(
                    raw_bits[i],
                    if encoding >> i & 1 != 0 {
                        Circuit::ONE
                    } else {
                        Circuit::ZERO
                    },
                );
            }
        }
        if op == Fence {
            let zero = c.constant(0, 4);
            let normal = c.equals(&raw_bits[28..32], &zero);
            let tso = c.constant(0x833, 12);
            let tso = c.equals(&raw_bits[20..32], &tso);
            let legal = c.or(normal, tso);
            c.assert_equal(legal, Circuit::ONE);
        }
        // Every instruction fetch is four aligned in-bounds bytes.
        c.assert_equal(pc_bits[0], Circuit::ZERO);
        c.assert_equal(pc_bits[1], Circuit::ZERO);
        for &bit in &pc_bits[32..] {
            c.assert_equal(bit, Circuit::ZERO);
        }
        constrain_zero_register(&mut c, &raw_bits[15..20], &a);
        constrain_zero_register(&mut c, &raw_bits[20..25], &b);
        let immediate = match op {
            Lui | Auipc => {
                let mut bits = vec![Circuit::ZERO; 12];
                bits.extend_from_slice(&raw_bits[12..32]);
                c.extend(&bits, 64, true)
            }
            Jal => {
                let mut bits = vec![Circuit::ZERO];
                bits.extend_from_slice(&raw_bits[21..31]);
                bits.push(raw_bits[20]);
                bits.extend_from_slice(&raw_bits[12..20]);
                bits.push(raw_bits[31]);
                c.extend(&bits, 64, true)
            }
            Beq | Bne | Blt | Bge | Bltu | Bgeu => {
                let mut bits = vec![Circuit::ZERO];
                bits.extend_from_slice(&raw_bits[8..12]);
                bits.extend_from_slice(&raw_bits[25..31]);
                bits.push(raw_bits[7]);
                bits.push(raw_bits[31]);
                c.extend(&bits, 64, true)
            }
            Sb | Sh | Sw | Sd => {
                let mut bits = raw_bits[7..12].to_vec();
                bits.extend_from_slice(&raw_bits[25..32]);
                c.extend(&bits, 64, true)
            }
            _ => c.extend(&raw_bits[20..32], 64, true),
        };
        let four = c.constant(4, 64);
        let sequential = c.add(&pc_bits, &four);
        let mut next_pc_bits = sequential.clone();
        let mut memory_address_bits = None;
        let mut memory_byte_bits = Vec::new();
        let result = match op {
            Lui => Some(immediate.clone()),
            Auipc => Some(c.add(&pc_bits, &immediate)),
            Jal | Jalr => {
                next_pc_bits = c.add(if op == Jal { &pc_bits } else { &a }, &immediate);
                if op == Jalr {
                    next_pc_bits[0] = Circuit::ZERO;
                }
                Some(sequential)
            }
            Beq | Bne | Blt | Bge | Bltu | Bgeu => {
                let taken = match op {
                    Beq => c.equals(&a, &b),
                    Bne => {
                        let equal = c.equals(&a, &b);
                        c.not(equal)
                    }
                    Blt | Bltu => c.less_than(&a, &b, op == Blt),
                    Bge | Bgeu => {
                        let less = c.less_than(&a, &b, op == Bge);
                        c.not(less)
                    }
                    _ => unreachable!(),
                };
                let target = c.add(&pc_bits, &immediate);
                next_pc_bits = c.select(taken, &target, &next_pc_bits);
                None
            }
            Lb | Lh | Lw | Ld | Lbu | Lhu | Lwu | Sb | Sh | Sw | Sd => {
                let address = c.add(&a, &immediate);
                // Integer address arithmetic wraps architecturally; the actual
                // accessed range must then lie within the flat RAM interval.
                let last_offset = c.constant((width - 1) as u64, 64);
                let last_address = c.add(&address, &last_offset);
                for &bit in &address[32..] {
                    c.assert_equal(bit, Circuit::ZERO);
                }
                for &bit in &last_address[32..] {
                    c.assert_equal(bit, Circuit::ZERO);
                }
                memory_address_bits = Some(address);
                let bytes = if op.is_store() { &b[..width * 8] } else { &load };
                memory_byte_bits = bytes.chunks_exact(8).map(|byte| byte.to_vec()).collect();
                if op.is_store() {
                    None
                } else {
                    Some(c.extend(&load, 64, matches!(op, Lb | Lh | Lw | Ld)))
                }
            }
            Addi => Some(c.add(&a, &immediate)),
            Add => Some(c.add(&a, &b)),
            Sub => Some(c.subtract(&a, &b).0),
            Slti | Sltiu | Slt | Sltu => {
                let rhs = if matches!(op, Slti | Sltiu) { &immediate } else { &b };
                let bit = c.less_than(&a, rhs, matches!(op, Slti | Slt));
                Some(c.extend(&[bit], 64, false))
            }
            Xori | Ori | Andi | Xor | Or | And => {
                let rhs = if matches!(op, Xori | Ori | Andi) {
                    &immediate
                } else {
                    &b
                };
                Some(
                    a.iter()
                        .zip(rhs)
                        .map(|(&x, &y)| match op {
                            Xori | Xor => c.xor(x, y),
                            Ori | Or => c.or(x, y),
                            _ => c.and(x, y),
                        })
                        .collect(),
                )
            }
            Slli | Srli | Srai | Sll | Srl | Sra | Slliw | Srliw | Sraiw | Sllw | Srlw | Sraw => {
                let word = matches!(op, Slliw | Srliw | Sraiw | Sllw | Srlw | Sraw);
                let immediate_shift = matches!(op, Slli | Srli | Srai | Slliw | Srliw | Sraiw);
                let bits = if word { 32 } else { 64 };
                let shift_bits = if word { 5 } else { 6 };
                let amount = if immediate_shift {
                    &raw_bits[20..20 + shift_bits]
                } else {
                    &b[..shift_bits]
                };
                let value = c.shift(
                    &a[..bits],
                    amount,
                    !matches!(op, Slli | Sll | Slliw | Sllw),
                    matches!(op, Srai | Sra | Sraiw | Sraw),
                );
                Some(c.extend(&value, 64, word))
            }
            Addiw | Addw | Subw => {
                let value = if op == Subw {
                    c.subtract(&a[..32], &b[..32]).0
                } else {
                    c.add(&a[..32], if op == Addiw { &immediate[..32] } else { &b[..32] })
                };
                Some(c.extend(&value, 64, true))
            }
            Mul | Mulh | Mulhsu | Mulhu | Mulw => {
                let bits = if op == Mulw { 32 } else { 64 };
                let product = c.multiply(&a[..bits], &b[..bits], matches!(op, Mulh | Mulhsu), op == Mulh);
                let value = if matches!(op, Mulh | Mulhsu | Mulhu) {
                    &product[bits..]
                } else {
                    &product[..bits]
                };
                Some(c.extend(value, 64, op == Mulw))
            }
            Div | Divu | Rem | Remu | Divw | Divuw | Remw | Remuw => {
                let word = matches!(op, Divw | Divuw | Remw | Remuw);
                let bits = if word { 32 } else { 64 };
                let (quotient, remainder) = c.divide(&a[..bits], &b[..bits], matches!(op, Div | Rem | Divw | Remw));
                let value = if matches!(op, Rem | Remu | Remw | Remuw) {
                    remainder
                } else {
                    quotient
                };
                Some(c.extend(&value, 64, word))
            }
            Fence | Ecall => None,
        };
        // Taken branches and jumps must not manufacture a misaligned next PC.
        c.assert_equal(next_pc_bits[0], Circuit::ZERO);
        c.assert_equal(next_pc_bits[1], Circuit::ZERO);
        let rd_value_bits = result.map(|value| {
            let zero = c.constant(0, 5);
            let rd_zero = c.equals(&raw_bits[7..12], &zero);
            let zeros = c.constant(0, 64);
            c.select(rd_zero, &zeros, &value)
        });
        let raw = c.pack(&raw_bits);
        let pc = c.pack(&pc_bits);
        let next_pc = c.pack(&next_pc_bits);
        let rd = c.pack(&raw_bits[7..12]);
        let rs1 = c.pack(&raw_bits[15..20]);
        let rs2 = c.pack(&raw_bits[20..25]);
        let rs1_value = c.pack(&a);
        let rs2_value = c.pack(&b);
        let rd_value = rd_value_bits.as_ref().map(|bits| c.pack(bits));
        let memory_address = memory_address_bits.as_ref().map(|bits| c.pack(bits));
        let memory_bytes = memory_byte_bits.iter().map(|bits| c.pack(bits)).collect();
        Self {
            op,
            circuit: c,
            raw,
            pc,
            next_pc,
            rs1,
            rs2,
            rd,
            rs1_value,
            rs2_value,
            rd_value,
            memory_address,
            memory_bytes,
            memory_write: op.is_store(),
            raw_bits,
            pc_bits,
            next_pc_bits,
            rs1_value_bits: a,
            rs2_value_bits: b,
            rd_value_bits,
            memory_address_bits,
            memory_byte_bits,
        }
    }

    /// A locally valid row for external bus-disabled padding. ECALL scheduling
    /// remains disabled by the enclosing table, just like all other buses.
    pub fn canonical_inputs(&self) -> Vec<bool> {
        let load = vec![0; if self.memory_write { 0 } else { self.op.memory_width() }];
        self.inputs(self.op.encoding().1, 0, 0, 0, &load).unwrap()
    }

    /// Initial inputs in schema order. Additional table inputs, such as cycle
    /// or enable bits, must be appended by the enclosing table's witness builder.
    pub fn inputs(&self, raw: u32, pc: u64, a: u64, b: u64, load: &[u8]) -> Option<Vec<bool>> {
        let bytes = if self.memory_write { 0 } else { self.op.memory_width() };
        if load.len() != bytes {
            return None;
        }
        let mut inputs = Vec::with_capacity(224 + bytes * 8);
        for (word, width) in [(raw as u64, 32), (pc, 64), (a, 64), (b, 64)] {
            inputs.extend((0..width).map(|bit| word >> bit & 1 != 0));
        }
        for &byte in load {
            inputs.extend((0..8).map(|bit| byte >> bit & 1 != 0));
        }
        Some(inputs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanvm_guest::Field;

    fn row(c: &InstructionCircuit, raw: u32, a: u64, b: u64, bytes: &[u8]) -> Vec<u64> {
        c.circuit
            .witness(&c.inputs(raw, 0x10000, a, b, bytes).unwrap())
            .unwrap()
    }

    fn valid(c: &InstructionCircuit, values: &[u64]) -> bool {
        let values: Vec<_> = values.iter().map(|&x| Field::new(x, 0, 0)).collect();
        (0..c.circuit.constraints()).all(|i| c.circuit.constraint(i, &values, false).is_zero())
    }

    fn register_raw(op: Opcode) -> u32 {
        op.encoding().1 | (1 << 7) | (2 << 15) | (3 << 20)
    }

    #[test]
    fn every_opcode_has_valid_padding_and_unique_decoder() {
        for op in Opcode::ALL {
            let c = InstructionCircuit::build(op);
            assert_eq!(Opcode::decode(op.encoding().1), Some(op));
            let witness = c.circuit.witness(&c.canonical_inputs()).unwrap();
            assert!(valid(&c, &witness), "{op:?}");
        }
        for raw in [
            0x00100073, 0x0000100f, 0x1000000f, 0x04001013, 0x0400101b, 0x0200103b, 0xffffffff,
        ] {
            assert_eq!(Opcode::decode(raw), None, "{raw:#x}");
        }
        assert_eq!(Opcode::decode(0x8330000f), Some(Opcode::Fence));
    }

    #[test]
    fn opcode_substitution_and_nonzero_x0_reads_reject() {
        let c = InstructionCircuit::build(Opcode::Add);
        let substituted = row(&c, register_raw(Opcode::And), 13, 7, &[]);
        assert!(!valid(&c, &substituted));
        let x0_read = row(&c, Opcode::Add.encoding().1 | (1 << 7) | (3 << 20), 99, 7, &[]);
        assert!(!valid(&c, &x0_read));
        let discard = row(&c, Opcode::Add.encoding().1 | (2 << 15) | (3 << 20), 13, 7, &[]);
        assert_eq!(discard[c.rd_value.unwrap()], 0);
        assert!(valid(&c, &discard));
    }

    #[test]
    fn multiply_divide_architectural_edges() {
        use Opcode::*;
        for op in [
            Mul, Mulh, Mulhsu, Mulhu, Mulw, Div, Divu, Rem, Remu, Divw, Divuw, Remw, Remuw,
        ] {
            let c = InstructionCircuit::build(op);
            for (a, b) in [
                (0, 0),
                (u64::MAX, 0),
                (1 << 63, u64::MAX),
                (0xffff_ffff_8000_0000, u64::MAX),
                (u64::MAX, 3),
                (0x123456789abcdef0, 0xfedcba9876543210),
            ] {
                let value = row(&c, register_raw(op), a, b, &[]);
                let signed_div = |x: i64, y: i64| if y == 0 { -1 } else { x.wrapping_div(y) };
                let signed_rem = |x: i64, y: i64| if y == 0 { x } else { x.wrapping_rem(y) };
                let expected = match op {
                    Mul => a.wrapping_mul(b),
                    Mulh => (((a as i64 as i128) * (b as i64 as i128)) >> 64) as u64,
                    Mulhsu => (((a as i64 as i128) * (b as i128)) >> 64) as u64,
                    Mulhu => (((a as u128) * (b as u128)) >> 64) as u64,
                    Mulw => (a as u32).wrapping_mul(b as u32) as i32 as i64 as u64,
                    Div => signed_div(a as i64, b as i64) as u64,
                    Rem => signed_rem(a as i64, b as i64) as u64,
                    Divu => {
                        if b == 0 {
                            u64::MAX
                        } else {
                            a / b
                        }
                    }
                    Remu => {
                        if b == 0 {
                            a
                        } else {
                            a % b
                        }
                    }
                    Divw => signed_div(a as i32 as i64, b as i32 as i64) as i32 as i64 as u64,
                    Remw => signed_rem(a as i32 as i64, b as i32 as i64) as i32 as i64 as u64,
                    Divuw => (if b as u32 == 0 { u32::MAX } else { a as u32 / b as u32 }) as i32 as i64 as u64,
                    Remuw => (if b as u32 == 0 { a as u32 } else { a as u32 % b as u32 }) as i32 as i64 as u64,
                    _ => unreachable!(),
                };
                assert_eq!(value[c.rd_value.unwrap()], expected, "{op:?} {a:#x} {b:#x}");
            }
            let mut forged = row(&c, register_raw(op), 19, 3, &[]);
            forged[c.rd_value.unwrap()] ^= 1;
            assert!(!valid(&c, &forged), "{op:?} forged result");
        }
    }

    #[test]
    fn shifts_mask_amount_and_word_results_sign_extend() {
        use Opcode::*;
        for op in [Sll, Srl, Sra, Sllw, Srlw, Sraw, Addw, Subw] {
            let c = InstructionCircuit::build(op);
            let a = 0x8000000080000001u64;
            let b = 127u64;
            let values = row(&c, register_raw(op), a, b, &[]);
            let expected = match op {
                Sll => a.wrapping_shl(b as u32),
                Srl => a.wrapping_shr(b as u32),
                Sra => (a as i64).wrapping_shr(b as u32) as u64,
                Sllw => (a as u32).wrapping_shl(b as u32) as i32 as i64 as u64,
                Srlw => (a as u32).wrapping_shr(b as u32) as i32 as i64 as u64,
                Sraw => (a as i32).wrapping_shr(b as u32) as i64 as u64,
                Addw => (a as u32).wrapping_add(b as u32) as i32 as i64 as u64,
                Subw => (a as u32).wrapping_sub(b as u32) as i32 as i64 as u64,
                _ => unreachable!(),
            };
            assert_eq!(values[c.rd_value.unwrap()], expected, "{op:?}");
            assert!(valid(&c, &values));
        }
    }

    #[test]
    fn byte_memory_sign_extension_range_and_alignment() {
        let signed = InstructionCircuit::build(Opcode::Lh);
        let unsigned = InstructionCircuit::build(Opcode::Lhu);
        for c in [&signed, &unsigned] {
            let raw = c.op.encoding().1 | (1 << 7) | (2 << 15);
            let values = row(c, raw, 0x101, 0, &[1, 0x80]);
            assert_eq!(values[c.memory_address.unwrap()], 0x101);
            assert_eq!(values[c.memory_bytes[0]], 1);
            assert_eq!(values[c.memory_bytes[1]], 0x80);
            assert_eq!(
                values[c.rd_value.unwrap()],
                if c.op == Opcode::Lh {
                    0xffff_ffff_ffff_8001
                } else {
                    0x8001
                }
            );
            assert!(valid(c, &values));
            assert!(!valid(c, &row(c, raw, 0xffff_ffff, 0, &[1, 0x80])));
        }
        let store = InstructionCircuit::build(Opcode::Sw);
        let raw = Opcode::Sw.encoding().1 | (2 << 15) | (3 << 20);
        let values = row(&store, raw, 0x103, 0xdead_beef_1234_5678, &[]);
        assert_eq!(
            store.memory_bytes.iter().map(|&i| values[i]).collect::<Vec<_>>(),
            [0x78, 0x56, 0x34, 0x12]
        );
        assert!(valid(&store, &values));
    }

    #[test]
    fn taken_branch_alignment_and_jalr_low_bit_clearing() {
        let branch = InstructionCircuit::build(Opcode::Beq);
        let raw = Opcode::Beq.encoding().1 | (2 << 15) | (3 << 20) | (1 << 8); // offset +2
        assert!(!valid(&branch, &row(&branch, raw, 9, 9, &[])));
        let not_taken = row(&branch, raw, 9, 10, &[]);
        assert_eq!(not_taken[branch.next_pc], 0x10004);
        assert!(valid(&branch, &not_taken));
        let jump = InstructionCircuit::build(Opcode::Jalr);
        let raw = Opcode::Jalr.encoding().1 | (1 << 7) | (2 << 15);
        let values = row(&jump, raw, 0x20001, 0, &[]);
        assert_eq!(values[jump.next_pc], 0x20000);
        assert_eq!(values[jump.rd_value.unwrap()], 0x10004);
        assert!(valid(&jump, &values));
        assert!(!valid(&jump, &row(&jump, raw, 0x20003, 0, &[])));
    }
}
