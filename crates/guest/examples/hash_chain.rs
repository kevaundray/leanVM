#![cfg_attr(all(target_arch = "riscv64", target_os = "none"), no_std)]
#![cfg_attr(all(target_arch = "riscv64", target_os = "none"), no_main)]

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
leanvm_guest::entry!(guest_main);

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
fn guest_main() -> u64 {
    let mut bytes = [0u8; 8];
    leanvm_guest::read_witness_exact(&mut bytes);
    let mut digest = [0u8; 32];
    for _ in 0..u64::from_le_bytes(bytes) {
        digest = leanvm_guest::hash(&digest);
    }
    let mut statement = [0u8; 40];
    statement[..8].copy_from_slice(&bytes);
    statement[8..].copy_from_slice(&digest);
    u64::from(leanvm_guest::hash(&statement) != leanvm_guest::public_input())
}

#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
fn main() {
    panic!("build hash_chain for riscv64im-unknown-none-elf to execute it");
}
