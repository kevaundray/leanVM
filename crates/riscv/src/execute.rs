use crate::{Error, ErrorKind, Execution, Op, OperandValues, Program, STACK_TOP, Step, decode};
use crate::{decode::sext, memory::Memory};
use primitives::field::F192;

fn word(value: u64) -> u64 {
    sext(value, 32)
}
fn signed_div(a: u64, b: u64) -> u64 {
    if b == 0 {
        u64::MAX
    } else {
        (a as i64).wrapping_div(b as i64) as u64
    }
}
fn signed_rem(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        (a as i64).wrapping_rem(b as i64) as u64
    }
}
fn unsigned_div(a: u64, b: u64) -> u64 {
    if b == 0 { u64::MAX } else { a / b }
}
fn unsigned_rem(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { a % b }
}

impl Program {
    /// Execute to a successful EXIT, or return the first trap. One cycle is one
    /// retired instruction, including an ECALL regardless of its byte count.
    /// Trailing witness bytes are permitted; witness_consumed identifies the
    /// exact prefix read by the guest. EXIT must have a0 == 0.
    pub fn execute(&self, public: [u8; 32], witness: &[u8], max_cycles: u64) -> Result<Execution, Error> {
        self.execute_with_trace(public, witness, max_cycles, Vec::new())
    }

    /// Execute with a caller-owned trace sink, allowing counting without retaining steps.
    /// The sink receives every retired instruction, including successful EXIT.
    pub fn execute_with_trace<T: Extend<Step>>(
        &self,
        public: [u8; 32],
        witness: &[u8],
        max_cycles: u64,
        mut steps: T,
    ) -> Result<Execution<T>, Error> {
        use Op::*;
        let mut memory = Memory::new(self);
        let mut registers = [0u64; 32];
        registers[2] = STACK_TOP;
        let mut pc = self.entry();
        let mut witness_offset = 0usize;
        for cycle in 0..max_cycles {
            if pc & 3 != 0 {
                return Err(Error {
                    pc,
                    kind: ErrorKind::MisalignedPc(pc),
                });
            }
            let mut events = Vec::new();
            let instruction = memory.fetch(pc)?;
            let decoded = decode(instruction, pc)?;
            let operands = if decoded.op == Ecall {
                OperandValues::Ecall {
                    a0: registers[10],
                    a1: registers[11],
                    a2: registers[12],
                    a3: registers[13],
                    a4: registers[14],
                    a5: registers[15],
                    number: registers[17],
                }
            } else {
                OperandValues::Instruction {
                    rs1: registers[decoded.rs1 as usize],
                    rs2: registers[decoded.rs2 as usize],
                    rd: registers[decoded.rd as usize],
                }
            };
            let witness_offset_before = witness_offset as u64;
            let a = registers[decoded.rs1 as usize];
            let b = registers[decoded.rs2 as usize];
            let imm = decoded.immediate as u64;
            let mut next_pc = pc.wrapping_add(4);
            let mut ecall = None;
            let mut exited = false;
            let mut result = None;
            match decoded.op {
                Lui => result = Some(imm),
                Auipc => result = Some(pc.wrapping_add(imm)),
                Jal | Jalr => {
                    next_pc = if decoded.op == Jal {
                        pc.wrapping_add(imm)
                    } else {
                        a.wrapping_add(imm) & !1
                    };
                    if next_pc & 3 != 0 {
                        return Err(Error {
                            pc,
                            kind: ErrorKind::MisalignedPc(next_pc),
                        });
                    }
                    result = Some(pc.wrapping_add(4));
                }
                Beq | Bne | Blt | Bge | Bltu | Bgeu => {
                    let taken = match decoded.op {
                        Beq => a == b,
                        Bne => a != b,
                        Blt => (a as i64) < (b as i64),
                        Bge => (a as i64) >= (b as i64),
                        Bltu => a < b,
                        Bgeu => a >= b,
                        _ => unreachable!(),
                    };
                    if taken {
                        next_pc = pc.wrapping_add(imm);
                        if next_pc & 3 != 0 {
                            return Err(Error {
                                pc,
                                kind: ErrorKind::MisalignedPc(next_pc),
                            });
                        }
                    }
                }
                Lb | Lh | Lw | Ld | Lbu | Lhu | Lwu => {
                    let length = match decoded.op {
                        Lb | Lbu => 1,
                        Lh | Lhu => 2,
                        Lw | Lwu => 4,
                        Ld => 8,
                        _ => unreachable!(),
                    };
                    let value = memory.load(pc, a.wrapping_add(imm), length, &mut events)?;
                    result = Some(match decoded.op {
                        Lb | Lh | Lw => sext(value, length as u32 * 8),
                        _ => value,
                    });
                }
                Sb | Sh | Sw | Sd => {
                    let length = match decoded.op {
                        Sb => 1,
                        Sh => 2,
                        Sw => 4,
                        Sd => 8,
                        _ => unreachable!(),
                    };
                    memory.write(pc, a.wrapping_add(imm), &b.to_le_bytes()[..length], &mut events)?;
                }
                Addi => result = Some(a.wrapping_add(imm)),
                Slti => result = Some(((a as i64) < decoded.immediate) as u64),
                Sltiu => result = Some((a < imm) as u64),
                Xori => result = Some(a ^ imm),
                Ori => result = Some(a | imm),
                Andi => result = Some(a & imm),
                Slli => result = Some(a << imm),
                Srli => result = Some(a >> imm),
                Srai => result = Some(((a as i64) >> imm) as u64),
                Add => result = Some(a.wrapping_add(b)),
                Sub => result = Some(a.wrapping_sub(b)),
                Sll => result = Some(a << (b & 63)),
                Srl => result = Some(a >> (b & 63)),
                Sra => result = Some(((a as i64) >> (b & 63)) as u64),
                Slt => result = Some(((a as i64) < (b as i64)) as u64),
                Sltu => result = Some((a < b) as u64),
                Xor => result = Some(a ^ b),
                Or => result = Some(a | b),
                And => result = Some(a & b),
                Addiw => result = Some(word(a.wrapping_add(imm))),
                Slliw => result = Some(word(a << imm)),
                Srliw => result = Some(word((a as u32 >> imm) as u64)),
                Sraiw => result = Some(word((a as i32 >> imm) as u64)),
                Addw => result = Some(word(a.wrapping_add(b))),
                Subw => result = Some(word(a.wrapping_sub(b))),
                Sllw => result = Some(word(a << (b & 31))),
                Srlw => result = Some(word((a as u32 >> (b & 31)) as u64)),
                Sraw => result = Some(word((a as i32 >> (b & 31)) as u64)),
                Mul => result = Some(a.wrapping_mul(b)),
                Mulh => result = Some((((a as i64 as i128) * (b as i64 as i128)) >> 64) as u64),
                Mulhsu => result = Some((((a as i64 as i128) * (b as i128)) >> 64) as u64),
                Mulhu => result = Some((((a as u128) * (b as u128)) >> 64) as u64),
                Div => result = Some(signed_div(a, b)),
                Divu => result = Some(unsigned_div(a, b)),
                Rem => result = Some(signed_rem(a, b)),
                Remu => result = Some(unsigned_rem(a, b)),
                Mulw => result = Some(word(a.wrapping_mul(b))),
                Divw => result = Some(word(signed_div(word(a), word(b)))),
                Divuw => result = Some(word(unsigned_div(a as u32 as u64, b as u32 as u64))),
                Remw => result = Some(word(signed_rem(word(a), word(b)))),
                Remuw => result = Some(word(unsigned_rem(a as u32 as u64, b as u32 as u64))),
                Fence => {}
                Ebreak => {
                    return Err(Error {
                        pc,
                        kind: ErrorKind::Breakpoint,
                    });
                }
                Ecall => {
                    let dst = registers[10];
                    match registers[17] {
                        0 => {
                            if dst != 0 {
                                return Err(Error {
                                    pc,
                                    kind: ErrorKind::ExitFailure(dst),
                                });
                            }
                            ecall = Some(crate::Ecall::Exit);
                            exited = true;
                        }
                        1 => {
                            let length = registers[11];
                            let remaining = (witness.len() - witness_offset) as u64;
                            if length > remaining {
                                return Err(Error {
                                    pc,
                                    kind: ErrorKind::WitnessExhausted {
                                        requested: length,
                                        remaining,
                                    },
                                });
                            }
                            let end = witness_offset + length as usize;
                            memory.write(pc, dst, &witness[witness_offset..end], &mut events)?;
                            ecall = Some(crate::Ecall::ReadWitness {
                                offset: witness_offset as u64,
                                length,
                            });
                            witness_offset = end;
                            registers[10] = length;
                        }
                        2 => {
                            memory.write(pc, dst, &public, &mut events)?;
                            registers[10] = 32;
                            ecall = Some(crate::Ecall::ReadPublic);
                        }
                        0x100 => {
                            // All operands are read before any output write, even
                            // when output overlaps message, state, or metadata.
                            let message = memory.read::<64>(pc, dst, &mut events)?;
                            let state = memory.read::<32>(pc, registers[11], &mut events)?;
                            let metadata = memory.read::<16>(pc, registers[12], &mut events)?;
                            let m = std::array::from_fn(|i| {
                                u32::from_le_bytes(message[4 * i..4 * i + 4].try_into().unwrap())
                            });
                            let h = std::array::from_fn(|i| {
                                u32::from_le_bytes(state[4 * i..4 * i + 4].try_into().unwrap())
                            });
                            let t = u64::from_le_bytes(metadata[..8].try_into().unwrap());
                            let f0 = u32::from_le_bytes(metadata[8..12].try_into().unwrap());
                            let f1 = u32::from_le_bytes(metadata[12..].try_into().unwrap());
                            let output = flock::hash::blake2s_compress(&h, &m, t, f0, f1);
                            let mut bytes = [0; 32];
                            for (i, v) in output.iter().enumerate() {
                                bytes[4 * i..4 * i + 4].copy_from_slice(&v.to_le_bytes());
                            }
                            memory.write(pc, registers[13], &bytes, &mut events)?;
                            registers[10] = 0;
                            ecall = Some(crate::Ecall::Blake2s);
                        }
                        0x101 => {
                            let lhs = F192::new(registers[10], registers[11], registers[12]);
                            let rhs = F192::new(registers[13], registers[14], registers[15]);
                            let product = lhs * rhs;
                            registers[10..13].copy_from_slice(&[product.c0, product.c1, product.c2]);
                            ecall = Some(crate::Ecall::F192Mul);
                        }
                        number => {
                            return Err(Error {
                                pc,
                                kind: ErrorKind::UnknownEcall(number),
                            });
                        }
                    }
                }
            }
            if let Some(value) = result
                && decoded.rd != 0
            {
                registers[decoded.rd as usize] = value;
            }
            registers[0] = 0;
            steps.extend(core::iter::once(Step {
                pc,
                instruction,
                next_pc,
                operands,
                memory: events,
                ecall,
                witness_offset_before,
                witness_offset_after: witness_offset as u64,
            }));
            if exited {
                return Ok(Execution {
                    steps,
                    registers,
                    cycles: cycle + 1,
                    public,
                    witness_consumed: witness_offset as u64,
                    memory: memory.snapshot,
                });
            }
            pc = next_pc;
        }
        Err(Error {
            pc,
            kind: ErrorKind::CycleLimit,
        })
    }
}
