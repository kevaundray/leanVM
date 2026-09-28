#![cfg_attr(all(target_arch = "riscv64", target_os = "none"), no_std)]
#![cfg_attr(all(target_arch = "riscv64", target_os = "none"), no_main)]

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
leanvm_guest::entry!(aggregate);

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
fn aggregate() -> u64 {
    match leanvm_aggregation_guest::run_guest() {
        Ok(()) => 0,
        Err(_) => 1,
    }
}

#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
fn main() {
    panic!("aggregate must run as a riscv64im-unknown-none-elf guest");
}
