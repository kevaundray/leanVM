#![no_std]
//! RV64IM guest ABI and portable verifier cryptography.
//!
//! Witness bytes are untrusted; programs must verify them against the public
//! input before returning zero. Cryptographic ECALLs only compute primitives;
//! they do not verify a statement or replace the host's proof constraints.
//!
//! Enable `runtime`, link with `link.x`, and use [`entry!`] in a bare-metal
//! executable. Host builds retain the same field/hash semantics, but input and
//! exit syscalls cannot be invoked outside the guest machine.

extern crate alloc;

pub const ECALL_EXIT: usize = 0;
pub const ECALL_READ_WITNESS: usize = 1;
pub const ECALL_READ_PUBLIC: usize = 2;
pub const ECALL_BLAKE2S: usize = 0x100;
pub const ECALL_F192_MUL: usize = 0x101;

pub mod deferred;
pub mod field;
pub mod hash;

pub use field::{Field, field_mul};
pub use hash::{Hasher, blake2s_compress, hash};

#[cfg(all(feature = "runtime", target_arch = "riscv64", target_os = "none"))]
mod runtime;

/// Read exactly `destination.len()` bytes from the sequential witness stream.
/// A short stream terminates execution unsuccessfully in the machine.
pub fn read_witness_exact(destination: &mut [u8]) {
    // SAFETY: the slice owns a writable region of exactly this length.
    unsafe {
        read_witness_raw(destination.as_mut_ptr(), destination.len());
    }
}

/// Allocate and read witness bytes without first filling the destination.
/// A short stream terminates unsuccessfully; allocation errors are returned.
pub fn read_witness_vec(count: usize) -> Result<alloc::vec::Vec<u8>, alloc::collections::TryReserveError> {
    let mut bytes = alloc::vec::Vec::new();
    bytes.try_reserve_exact(count)?;
    // SAFETY: the allocated prefix is writable, and a successful read
    // initializes every byte before the vector's length exposes it.
    unsafe {
        read_witness_raw(bytes.as_mut_ptr(), count);
        bytes.set_len(count);
    }
    Ok(bytes)
}

// The destination must be writable for count bytes; success initializes all of it.
unsafe fn read_witness_raw(destination: *mut u8, count: usize) {
    #[cfg(target_arch = "riscv64")]
    {
        // SAFETY: the destination is writable for exactly count bytes.
        let read = unsafe { ecall(ECALL_READ_WITNESS, destination as usize, count, 0, 0) };
        assert_eq!(read, count, "short witness read");
    }
    #[cfg(not(target_arch = "riscv64"))]
    {
        let _ = (destination, count);
        panic!("witness input is only available inside the guest machine");
    }
}

/// Read the machine's fixed 32-byte public input.
pub fn public_input() -> [u8; 32] {
    #[cfg(target_arch = "riscv64")]
    {
        let mut input = [0u8; 32];
        // SAFETY: input is writable for the ABI's fixed 32-byte output.
        let count = unsafe { ecall(ECALL_READ_PUBLIC, input.as_mut_ptr() as usize, 0, 0, 0) };
        assert_eq!(count, input.len(), "invalid public input length");
        input
    }
    #[cfg(not(target_arch = "riscv64"))]
    panic!("public input is only available inside the guest machine");
}

/// Terminate execution. Only status zero denotes success.
pub fn exit(status: u64) -> ! {
    #[cfg(target_arch = "riscv64")]
    // SAFETY: EXIT does not return; no memory arguments are passed.
    unsafe {
        core::arch::asm!("ecall", in("a7") ECALL_EXIT, in("a0") status, options(noreturn));
    }
    #[cfg(not(target_arch = "riscv64"))]
    panic!("guest exit invoked on host with status {status}");
}

#[cfg(target_arch = "riscv64")]
#[inline]
unsafe fn ecall(number: usize, a0: usize, a1: usize, a2: usize, a3: usize) -> usize {
    let result;
    // These pointer-based syscalls preserve registers other than a0. Omit nomem and
    // readonly: the machine reads all inputs before writing any output, and
    // output buffers are permitted to overlap the input buffers.
    unsafe {
        core::arch::asm!(
            "ecall",
            in("a7") number,
            inlateout("a0") a0 => result,
            in("a1") a1,
            in("a2") a2,
            in("a3") a3,
            options(nostack),
        );
    }
    result
}

/// Define the entry point of a guest executable.
///
/// `main` must be a Rust function of type `fn() -> u64`; its return value is
/// passed to EXIT. The executable must enable this crate's `runtime` feature
/// and link with `crates/guest/link.x`. Only one entry point may be defined.
#[macro_export]
macro_rules! entry {
    ($main:path) => {
        #[cfg(all(target_arch = "riscv64", target_os = "none"))]
        #[unsafe(no_mangle)]
        pub extern "C" fn __leanvm_guest_main() -> u64 {
            let main: fn() -> u64 = $main;
            main()
        }
    };
}
