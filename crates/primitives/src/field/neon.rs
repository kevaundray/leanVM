//! Small AArch64 SIMD helpers shared by the NEON kernels.
//!
//! The ARMv8.2 SHA3 extension provides `EOR3`, a three-way XOR in one instruction.
//!
//! - The binary-field kernels are XOR-dominated, so one `EOR3` replaces two dependent `EOR`s.
//! - Builds without the extension keep the two-`EOR` form.
//! - `sha3` names the feature block that carries `EOR3`, not the hash function.

use core::arch::aarch64::*;

/// The three-way XOR of 64-bit-lane vectors, one `EOR3`.
#[cfg(target_feature = "sha3")]
#[inline(always)]
pub fn xor3_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
    // SAFETY: `sha3` is enabled at compile time.
    unsafe { veor3q_u64(a, b, c) }
}

/// The three-way XOR of 64-bit-lane vectors, two `EOR`s where the SHA3 extension is off.
#[cfg(not(target_feature = "sha3"))]
#[inline(always)]
pub fn xor3_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
    // SAFETY: NEON is part of the aarch64 baseline.
    unsafe { veorq_u64(a, veorq_u64(b, c)) }
}
