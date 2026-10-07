//! Verus proofs of leanVM's portable field arithmetic, bit transposes and additive NTT.
#![allow(unused_parens, unused_imports, unused_variables, dead_code, clippy::all)]

pub mod bit_fold;
pub mod bits;
pub mod clmul;
pub mod flock_ntt;
pub mod gf2_64;
pub mod gf2_64x3;
pub mod gf2_8;
pub mod intrinsics;
#[cfg(target_arch = "aarch64")]
pub mod neon;
pub mod ntt;
pub mod ntt_lanes;
pub mod phi8_tower;
