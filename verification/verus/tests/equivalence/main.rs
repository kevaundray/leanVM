//! The verified copies agree with the production functions they were copied from.
//!
//! Each verified function in `src/` is a copy of a portable production function. These tests run both on
//! random inputs and on the edge cases, so an edit to one side without the other fails here.

mod bits;
mod gf2_64;
mod gf2_64x3;
mod gf2_8;
#[cfg(target_arch = "aarch64")]
mod intrinsics_aarch64;
#[cfg(target_arch = "aarch64")]
mod intrinsics_aarch64_gfneon;
#[cfg(target_arch = "x86_64")]
mod intrinsics_x86;
#[cfg(target_arch = "x86_64")]
mod intrinsics_x86_gfneon;
mod ntt;
mod phi8_tower;
mod bit_fold;
