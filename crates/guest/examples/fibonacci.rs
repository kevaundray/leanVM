#![cfg_attr(all(target_arch = "riscv64", target_os = "none"), no_std)]
#![cfg_attr(all(target_arch = "riscv64", target_os = "none"), no_main)]

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
leanvm_guest::entry!(guest_main);

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
fn guest_main() -> u64 {
    let mut bytes = [0u8; 8];
    leanvm_guest::read_witness_exact(&mut bytes);
    let steps = u64::from_le_bytes(bytes);
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..steps / 2 {
        a = a.wrapping_add(b);
        b = a.wrapping_add(b);
    }
    if steps & 1 != 0 {
        a = b;
    }
    let mut statement = [0u8; 32];
    statement[..8].copy_from_slice(&bytes);
    statement[8..16].copy_from_slice(&a.to_le_bytes());
    u64::from(statement != leanvm_guest::public_input())
}

#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
fn main() {
    panic!("build fibonacci for riscv64im-unknown-none-elf to execute it");
}
