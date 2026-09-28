#![cfg_attr(all(target_arch = "riscv64", target_os = "none"), no_std)]
#![cfg_attr(all(target_arch = "riscv64", target_os = "none"), no_main)]

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
leanvm_guest::entry!(guest_main);

/// The witness is exactly eight bytes. Public input must be its BLAKE2s-256
/// digest. A short witness, different digest or panic cannot exit successfully.
#[cfg(all(target_arch = "riscv64", target_os = "none"))]
fn guest_main() -> u64 {
    let mut witness = [0u8; 8];
    leanvm_guest::read_witness_exact(&mut witness);
    let expected = leanvm_guest::public_input();
    if leanvm_guest::hash(&witness) == expected { 0 } else { 1 }
}

// Keep workspace host builds possible without pretending to execute a guest.
#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
fn main() {
    panic!("build hash_witness for riscv64im-unknown-none-elf to execute it");
}
