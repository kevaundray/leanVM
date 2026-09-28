#![cfg(feature = "host")]

use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
};

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!("leanvm-rv64-python-{}-{nonce}", std::process::id()));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn verify(&self, public: &[u8; 32]) -> Output {
        let verifier = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py");
        let public_hex: String = public.iter().map(|byte| format!("{byte:02x}")).collect();
        Command::new(std::env::var_os("PYTHON").unwrap_or_else(|| "python3".into()))
            .arg(verifier)
            .arg("--elf")
            .arg(self.0.join("program.elf"))
            .arg("--public-input")
            .arg(public_hex)
            .arg("--proof")
            .arg(self.0.join("proof.bin"))
            .output()
            .expect("launch independent Python verifier")
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn addi(rd: u32, rs1: u32, immediate: u32) -> u32 {
    (immediate << 20) | (rs1 << 15) | (rd << 7) | 0x13
}

// Native instructions exercise every ECALL, including variable witness copying,
// ELF-initialized bytes, public-input writes, and both proof-checked crypto paths.
fn program_elf() -> Vec<u8> {
    let data = |rd: u32| (0x20 << 12) | (rd << 7) | 0x37;
    let load = |rd: u32, offset: u32| (offset << 20) | (5 << 15) | (3 << 12) | (rd << 7) | 3;
    let instructions = [
        data(10),
        addi(11, 0, 64),
        addi(17, 0, 1),
        0x73,
        data(10),
        addi(10, 10, 192),
        addi(17, 0, 2),
        0x73,
        data(10),
        addi(11, 10, 64),
        addi(12, 10, 96),
        addi(13, 10, 112),
        addi(17, 0, 0x100),
        0x73,
        data(5),
        load(10, 0),
        load(11, 8),
        load(12, 16),
        load(13, 24),
        load(14, 32),
        load(15, 40),
        addi(17, 0, 0x101),
        0x73,
        addi(10, 0, 0),
        addi(17, 0, 0),
        0x73,
    ];
    let code: Vec<u8> = instructions.into_iter().flat_map(u32::to_le_bytes).collect();
    let mut elf = vec![0u8; 0x300];
    elf[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    for (at, value) in [(16, 2u16), (18, 243), (52, 64), (54, 56), (56, 2)] {
        elf[at..at + 2].copy_from_slice(&value.to_le_bytes());
    }
    elf[20..24].copy_from_slice(&1u32.to_le_bytes());
    elf[24..32].copy_from_slice(&0x10000u64.to_le_bytes());
    elf[32..40].copy_from_slice(&64u64.to_le_bytes());
    for (p, address, offset, filesz, memsz, flags) in [
        (64, 0x10000u64, 0x100u64, code.len() as u64, code.len() as u64, 5u32),
        (120, 0x20000, 0x200, 0x100, 0x200, 6),
    ] {
        elf[p..p + 4].copy_from_slice(&1u32.to_le_bytes());
        elf[p + 4..p + 8].copy_from_slice(&flags.to_le_bytes());
        for (field, value) in [(8, offset), (16, address), (32, filesz), (40, memsz), (48, 4)] {
            elf[p + field..p + field + 8].copy_from_slice(&value.to_le_bytes());
        }
    }
    elf[0x100..0x100 + code.len()].copy_from_slice(&code);
    // Nonzero chaining value and metadata are read from immutable ELF initial RAM.
    for (i, byte) in elf[0x240..0x270].iter_mut().enumerate() {
        *byte = (i as u8).wrapping_mul(7).wrapping_add(3);
    }
    elf
}

fn require_rejection(output: Output) {
    assert!(!output.status.success(), "tampered statement/proof accepted");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("reject:"),
        "verifier crashed instead of rejecting: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn native_proof_interoperates_with_independent_python_verifier() {
    lean_vm::init_prover_pool();
    let fixture = Fixture::new();
    let elf = program_elf();
    let program = riscv::Program::from_elf(&elf).unwrap();
    let public = [0x91; 32];
    let witness: Vec<u8> = (0u8..64).map(|byte| byte.wrapping_mul(11)).collect();
    let (proof, _) = riscv_proof::host::prove(&program, public, &witness, 100, 1).unwrap();
    let encoded = proof.to_bytes();
    fs::write(fixture.0.join("program.elf"), &elf).unwrap();
    fs::write(fixture.0.join("proof.bin"), &encoded).unwrap();
    let accepted = fixture.verify(&public);
    assert!(
        accepted.status.success(),
        "Python rejected native proof: {}",
        String::from_utf8_lossy(&accepted.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&accepted.stdout).trim(), "accept");

    let mut changed_public = public;
    changed_public[0] ^= 1;
    require_rejection(fixture.verify(&changed_public));

    let mut changed_elf = elf.clone();
    // A non-loaded ELF byte still belongs to the exact public program digest.
    changed_elf[0xff] ^= 1;
    fs::write(fixture.0.join("program.elf"), changed_elf).unwrap();
    require_rejection(fixture.verify(&public));
    fs::write(fixture.0.join("program.elf"), elf).unwrap();

    let mut changed_proof = proof;
    // Header contains 2 dimensions, 71 presence/height tags, and two 4-word histories.
    changed_proof.stream[81].0[0] ^= 1;
    fs::write(fixture.0.join("proof.bin"), changed_proof.to_bytes()).unwrap();
    require_rejection(fixture.verify(&public));

    let mut trailing = encoded;
    trailing.push(0);
    fs::write(fixture.0.join("proof.bin"), trailing).unwrap();
    require_rejection(fixture.verify(&public));

    // No RAM accesses or BLAKE calls: these tables and their reductions are absent.
    // The register history remains present and is padded to the minimum eight rows.
    let mut exit_elf = program_elf();
    exit_elf[0x100..0x104].copy_from_slice(&0x73u32.to_le_bytes());
    exit_elf[96..104].copy_from_slice(&4u64.to_le_bytes());
    exit_elf[104..112].copy_from_slice(&4u64.to_le_bytes());
    let exit_program = riscv::Program::from_elf(&exit_elf).unwrap();
    let (exit_proof, _) = riscv_proof::host::prove(&exit_program, public, &[], 1, 1).unwrap();
    fs::write(fixture.0.join("program.elf"), exit_elf).unwrap();
    fs::write(fixture.0.join("proof.bin"), exit_proof.to_bytes()).unwrap();
    let accepted = fixture.verify(&public);
    assert!(
        accepted.status.success(),
        "Python rejected sparse EXIT proof: {}",
        String::from_utf8_lossy(&accepted.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&accepted.stdout).trim(), "accept");
}
