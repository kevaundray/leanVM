use super::*;

const ENTRY: u64 = 0x10000;
const DATA: u64 = 0x20000;

fn put16(bytes: &mut [u8], at: usize, value: u16) {
    bytes[at..at + 2].copy_from_slice(&value.to_le_bytes());
}
fn put32(bytes: &mut [u8], at: usize, value: u32) {
    bytes[at..at + 4].copy_from_slice(&value.to_le_bytes());
}
fn put64(bytes: &mut [u8], at: usize, value: u64) {
    bytes[at..at + 8].copy_from_slice(&value.to_le_bytes());
}

fn elf(code: &[u32], data: &[u8]) -> Vec<u8> {
    let data_offset = 0x100 + code.len() * 4;
    let mut bytes = vec![0; data_offset + data.len()];
    bytes[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    put16(&mut bytes, 16, 2);
    put16(&mut bytes, 18, 243);
    put32(&mut bytes, 20, 1);
    put64(&mut bytes, 24, ENTRY);
    put64(&mut bytes, 32, 64);
    put16(&mut bytes, 52, 64);
    put16(&mut bytes, 54, 56);
    put16(&mut bytes, 56, 2);
    for (p, address, offset, size, flags) in [
        (64, ENTRY, 0x100, code.len() * 4, 5),
        (120, DATA, data_offset, data.len(), 6),
    ] {
        put32(&mut bytes, p, 1);
        put32(&mut bytes, p + 4, flags);
        put64(&mut bytes, p + 8, offset as u64);
        put64(&mut bytes, p + 16, address);
        put64(&mut bytes, p + 32, size as u64);
        put64(&mut bytes, p + 40, size as u64 + if flags == 6 { 64 } else { 0 });
        put64(&mut bytes, p + 48, 4);
    }
    for (i, &raw) in code.iter().enumerate() {
        put32(&mut bytes, 0x100 + i * 4, raw);
    }
    bytes[data_offset..].copy_from_slice(data);
    bytes
}
fn i(opcode: u32, rd: u32, f3: u32, rs1: u32, immediate: i32) -> u32 {
    ((immediate as u32 & 0xfff) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | opcode
}
fn r(opcode: u32, rd: u32, f3: u32, rs1: u32, rs2: u32, f7: u32) -> u32 {
    (f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | opcode
}
fn store(f3: u32, rs1: u32, rs2: u32, immediate: u32) -> u32 {
    ((immediate >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | ((immediate & 31) << 7) | 0x23
}
fn addi(rd: u32, rs1: u32, immediate: i32) -> u32 {
    i(0x13, rd, 0, rs1, immediate)
}
fn binary(raw: u32, a: u64, b: u64) -> u64 {
    let code = [0x000202b7, i(3, 6, 3, 5, 0), i(3, 7, 3, 5, 8), raw, 0x73];
    let data: Vec<_> = a.to_le_bytes().into_iter().chain(b.to_le_bytes()).collect();
    Program::from_elf(&elf(&code, &data))
        .unwrap()
        .execute([0; 32], &[], 5)
        .unwrap()
        .registers[8]
}

#[test]
fn reserved_encodings_are_not_silently_decoded() {
    for raw in [
        0,
        0xffff_ffff,
        0x0000_100f,            // compressed/unknown/FENCE.I
        i(0x13, 1, 1, 2, 0x40), // reserved SLLI high bits
        i(0x1b, 1, 1, 2, 0x20), // W shift with shamt[5]
        r(0x3b, 1, 1, 2, 3, 1), // nonexistent MULHW
        r(0x33, 1, 2, 2, 3, 0x20),
        i(0x67, 1, 1, 2, 0),
        i(3, 1, 7, 2, 0),
        0x00200073,
        0x00001073,
        0x000000f3,
        0x1000000f,
    ] {
        assert_eq!(
            decode(raw, 12).unwrap_err(),
            Error {
                pc: 12,
                kind: ErrorKind::IllegalInstruction(raw)
            }
        );
    }
    assert_eq!(decode(i(0x13, 1, 1, 2, 63), 0).unwrap().immediate, 63);
    assert_eq!(decode(addi(1, 2, -2048), 0).unwrap().immediate, -2048);
    assert_eq!(decode(0x8330000f, 0).unwrap().op, Op::Fence);
}

#[test]
fn high_multiply_signedness_and_division_boundaries() {
    let min = 1u64 << 63;
    for (f3, a, b, expected) in [
        (1, u64::MAX, 2, u64::MAX),
        (1, min, min, 1 << 62),
        (2, u64::MAX, u64::MAX, u64::MAX),
        (2, min, u64::MAX, min),
        (3, u64::MAX, u64::MAX, u64::MAX - 1),
        (4, min, u64::MAX, min),
        (6, min, u64::MAX, 0),
        (4, 17, 0, u64::MAX),
        (5, 17, 0, u64::MAX),
        (6, 17, 0, 17),
        (7, 17, 0, 17),
        (4, (-7i64) as u64, 3, (-2i64) as u64),
        (6, (-7i64) as u64, 3, u64::MAX),
        (5, u64::MAX, 2, i64::MAX as u64),
        (7, u64::MAX, 2, 1),
    ] {
        assert_eq!(
            binary(r(0x33, 8, f3, 6, 7, 1), a, b),
            expected,
            "funct3={f3}, a={a:x}, b={b:x}"
        );
    }
}

#[test]
fn word_results_sign_extend_and_ignore_upper_operands() {
    for (raw, a, b, expected) in [
        (r(0x3b, 8, 0, 6, 7, 0), 0x7fffffff, 1, 0xffffffff80000000),
        (r(0x3b, 8, 5, 6, 7, 0), 0x1234567880000000, 0, 0xffffffff80000000),
        (r(0x3b, 8, 5, 6, 7, 0), u64::MAX, 1, 0x7fffffff),
        (r(0x3b, 8, 5, 6, 7, 0x20), 0x80000000, 1, 0xffffffffc0000000),
        (r(0x3b, 8, 1, 6, 7, 0), 1, 63, 0xffffffff80000000),
        (r(0x3b, 8, 0, 6, 7, 1), 0x180000000, 3, 0xffffffff80000000),
        (r(0x3b, 8, 4, 6, 7, 1), 0x80000000, 0xffffffff, 0xffffffff80000000),
        (r(0x3b, 8, 6, 6, 7, 1), 0x80000000, 0xffffffff, 0),
        (r(0x3b, 8, 5, 6, 7, 1), 0xffffffffffffffff, 1, u64::MAX),
        (r(0x3b, 8, 5, 6, 7, 1), 7, 1 << 32, u64::MAX),
        (r(0x3b, 8, 7, 6, 7, 1), 0x180000000, 1 << 32, 0xffffffff80000000),
        (i(0x1b, 8, 0, 6, 1), 0x7fffffff, 0, 0xffffffff80000000),
        (i(0x1b, 8, 1, 6, 31), 1, 0, 0xffffffff80000000),
        (i(0x1b, 8, 5, 6, 1), u64::MAX, 0, 0x7fffffff),
        (i(0x1b, 8, 5, 6, 0x401), 0x80000000, 0, 0xffffffffc0000000),
    ] {
        assert_eq!(binary(raw, a, b), expected, "raw={raw:x}");
    }
}

#[test]
fn zero_register_and_misaligned_memory_have_complete_byte_events() {
    let code = [
        addi(0, 0, 9),
        addi(6, 0, -1),
        store(3, 0, 6, 4093),
        i(3, 7, 3, 0, -3),
        0x73,
    ];
    // Immediate 4093 in the store is -3 and must trap rather than wrap into RAM.
    let err = Program::from_elf(&elf(&code, &[]))
        .unwrap()
        .execute([0; 32], &[], 10)
        .unwrap_err();
    assert_eq!(err.pc, ENTRY + 8);
    assert!(matches!(err.kind, ErrorKind::MemoryOutOfBounds { .. }));
    let code = [
        addi(0, 0, 9),
        addi(6, 0, -1),
        store(3, 0, 6, 1),
        i(3, 7, 3, 0, 1),
        i(3, 8, 6, 0, 1),
        0x73,
    ];
    let run = Program::from_elf(&elf(&code, &[]))
        .unwrap()
        .execute([0; 32], &[], 6)
        .unwrap();
    assert_eq!(run.registers[0], 0);
    assert_eq!(run.registers[7], u64::MAX);
    assert_eq!(run.registers[8], 0xffffffff);
    assert_eq!(run.steps[2].memory.len(), 8);
    for (index, event) in run.steps[2].memory.iter().enumerate() {
        assert_eq!(
            *event,
            MemoryEvent {
                address: index as u64 + 1,
                before: 0,
                after: 255,
                kind: AccessKind::Write
            }
        );
    }
    for event in &run.steps[3].memory {
        assert_eq!(event.before, 255);
        assert_eq!(event.before, event.after);
    }
    assert_eq!(run.memory.read_byte(0), Some(0));
    assert_eq!(run.memory.read_byte(8), Some(255));
    assert_eq!(run.memory.read_byte(RAM_END), None);
}

#[test]
fn compact_operands_retain_prewrite_values_and_only_captured_registers() {
    let code = [addi(5, 0, 7), addi(5, 5, 1), 0x73];
    let run = Program::from_elf(&elf(&code, &[]))
        .unwrap()
        .execute([0; 32], &[], 3)
        .unwrap();
    assert_eq!(run.registers[5], 8);
    assert_eq!(run.steps[1].register_before(5), Some(7));
    assert_eq!(run.steps[1].register_before(1), Some(0));
    assert_eq!(run.steps[1].register_before(0), None);
    assert_eq!(run.steps[1].register_before(32), None);
    assert_eq!(run.steps[2].register_before(10), Some(0));
    assert_eq!(run.steps[2].register_before(17), Some(0));
    assert_eq!(run.steps[2].register_before(0), Some(0));
    assert_eq!(run.steps[2].register_before(5), None);
    assert!(run.steps.iter().all(|step| step.memory.is_empty()));
    let mut forged = run.steps[0].clone();
    forged.operands = OperandValues::Instruction { rs1: 1, rs2: 0, rd: 0 };
    assert_eq!(forged.register_before(0), Some(1));
}

#[test]
fn x0_loads_still_trap_and_executable_writes_are_denied() {
    let code = [i(3, 0, 0, 2, 0), 0x73];
    assert!(matches!(
        Program::from_elf(&elf(&code, &[]))
            .unwrap()
            .execute([0; 32], &[], 3)
            .unwrap_err()
            .kind,
        ErrorKind::MemoryOutOfBounds { .. }
    ));
    let code = [0x000102b7, store(0, 5, 0, 0), 0x73];
    assert_eq!(
        Program::from_elf(&elf(&code, &[]))
            .unwrap()
            .execute([0; 32], &[], 3)
            .unwrap_err(),
        Error {
            pc: ENTRY + 4,
            kind: ErrorKind::PermissionDenied {
                address: ENTRY,
                kind: AccessKind::Write
            },
        }
    );
}

#[test]
fn loader_rejects_bad_ranges_flags_overlap_and_entries() {
    let original = elf(&[0x73], &[7]);
    for (at, value) in [(48, 1u32), (48, 4), (68, 7)] {
        let mut bytes = original.clone();
        put32(&mut bytes, at, value);
        assert!(Program::from_elf(&bytes).is_err());
    }
    for (at, value) in [
        (24, ENTRY + 2),
        (24, DATA),
        (32, u64::MAX),
        (80, RAM_END - 2),
        (96, 8),
        (104, u64::MAX),
        (112, 3),
        (136, ENTRY),
        (128, u64::MAX),
    ] {
        let mut bytes = original.clone();
        put64(&mut bytes, at, value);
        assert!(Program::from_elf(&bytes).is_err(), "field {at}, value {value}");
    }
    let p = Program::from_elf(&original).unwrap();
    assert_eq!(p.initial_memory().read_byte(DATA), Some(7));
    assert_eq!(p.initial_memory().read_byte(DATA + 1), Some(0));
    assert_eq!(p.execute([0; 32], &[], 1).unwrap().registers[2], STACK_TOP);
}

#[test]
fn control_flow_traps_and_cycle_limit_are_precise() {
    for (code, expected_pc, kind) in [
        (vec![0x0020006f], ENTRY, ErrorKind::MisalignedPc(ENTRY + 2)),
        (vec![0x00100073], ENTRY, ErrorKind::Breakpoint),
        (vec![addi(17, 0, 3), 0x73], ENTRY + 4, ErrorKind::UnknownEcall(3)),
        (vec![addi(10, 0, 1), 0x73], ENTRY + 4, ErrorKind::ExitFailure(1)),
        (vec![0x0000006f], ENTRY, ErrorKind::CycleLimit),
    ] {
        assert_eq!(
            Program::from_elf(&elf(&code, &[]))
                .unwrap()
                .execute([0; 32], &[], 4)
                .unwrap_err(),
            Error { pc: expected_pc, kind }
        );
    }
    // A non-taken BEQ has an otherwise misaligned target; no trap is raised.
    let code = [addi(1, 0, 1), 0x00008163, 0x73];
    assert_eq!(
        Program::from_elf(&elf(&code, &[]))
            .unwrap()
            .execute([0; 32], &[], 3)
            .unwrap()
            .cycles,
        3
    );
}

#[test]
fn witness_is_sequential_public_is_exact_and_short_reads_fail() {
    let code = [
        addi(10, 0, 1),
        addi(11, 0, 2),
        addi(17, 0, 1),
        0x73,
        addi(10, 0, 5),
        0x73,
        addi(10, 0, 9),
        addi(17, 0, 2),
        0x73,
        addi(10, 0, 0),
        addi(17, 0, 0),
        0x73,
    ];
    let p = Program::from_elf(&elf(&code, &[])).unwrap();
    let run = p.execute([17; 32], &[1, 2, 3, 4, 99], 12).unwrap();
    assert_eq!(run.witness_consumed, 4);
    assert_eq!(run.steps[5].ecall, Some(Ecall::ReadWitness { offset: 2, length: 2 }));
    assert_eq!(run.memory.read_byte(5), Some(3));
    assert_eq!(run.memory.read_byte(6), Some(4));
    for address in 9..41 {
        assert_eq!(run.memory.read_byte(address), Some(17));
    }
    assert_eq!(run.steps[9].register_before(10), Some(32));
    assert_eq!(
        p.execute([17; 32], &[1, 2, 3], 12).unwrap_err(),
        Error {
            pc: ENTRY + 20,
            kind: ErrorKind::WitnessExhausted {
                requested: 2,
                remaining: 1
            },
        }
    );
}

#[test]
fn field_ecall_returns_in_place_register_product() {
    let code = [
        addi(12, 0, 1),
        addi(14, 0, 1),
        addi(17, 0, 0x101),
        0x73,
        addi(6, 10, 0),
        addi(7, 11, 0),
        addi(8, 12, 0),
        addi(10, 0, 0),
        addi(17, 0, 0),
        0x73,
    ];
    let p = Program::from_elf(&elf(&code, &[])).unwrap();
    let run = p.execute([0; 32], &[], code.len() as u64).unwrap();
    assert_eq!(run.registers[6..9], [1, 1, 0]); // y² * y = 1 + y.
    assert_eq!(run.registers[14], 1);
    assert_eq!(run.steps[3].register_before(12), Some(1));
    assert!(run.steps[3].memory.is_empty());
}

#[test]
fn blake_ecall_reads_all_metadata_before_overlapping_output() {
    let code = [
        0x00020537,
        addi(11, 10, 64),
        addi(12, 10, 96),
        addi(13, 10, 88),
        addi(17, 0, 0x100),
        0x73,
        addi(17, 0, 0),
        0x73,
    ];
    let mut data = vec![0; 128];
    for (i, byte) in data[..64].iter_mut().enumerate() {
        *byte = i as u8;
    }
    for (i, value) in primitives::hash::PARAM_IV.iter().enumerate() {
        put32(&mut data, 64 + i * 4, *value);
    }
    put64(&mut data, 96, 64);
    put32(&mut data, 104, u32::MAX);
    let expected = primitives::hash::hash(&data[..64]);
    let run = Program::from_elf(&elf(&code, &data))
        .unwrap()
        .execute([0; 32], &[], 8)
        .unwrap();
    for (i, &byte) in expected.iter().enumerate() {
        assert_eq!(run.memory.read_byte(DATA + 88 + i as u64), Some(byte));
    }
    let events = &run.steps[5].memory;
    assert_eq!(events.len(), 64 + 32 + 16 + 32);
    assert!(events[..112].iter().all(|e| e.kind == AccessKind::Read));
    assert!(events[112..].iter().all(|e| e.kind == AccessKind::Write));
    for (event, &before) in events[..112].iter().zip(&data) {
        assert_eq!(event.before, before);
    }
    for (event, &before) in events[112..].iter().zip(&data[88..120]) {
        assert_eq!(event.before, before);
    }
    assert_eq!(run.registers[10], 0);
}
