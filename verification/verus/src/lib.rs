//! Verus proofs of portable field arithmetic, bit transposes, additive NTT and BLAKE2s copies/models.
#![allow(unused_parens, unused_imports, unused_variables, dead_code, clippy::all)]

pub mod bits;
pub mod blake2s;
pub mod blake2s_batch;
pub mod clmul;
pub mod gf2_64;
pub mod gf2_64x3;
pub mod gf2_8;
pub mod ntt;
