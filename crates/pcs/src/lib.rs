// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Tower-field polynomial commitment infrastructure.
//!
//! Boolean witnesses are packed into `K = GF(2^64)` and WHIR opens them
//! over its cubic extension `E = GF(2^192)`.

// The proof path computes in integers and binary fields alone. The soundness analysis behind the WHIR table computes in floating point and is `#[cfg(test)]`, which is what keeps it out of a build; these lints are a partial second check, catching float operators and lossy integer-to-float casts but not float method calls or lossless casts.
#![deny(clippy::float_arithmetic, clippy::cast_precision_loss)]

pub mod merkle;
pub mod ntt;
pub mod pack;
pub mod ring_switch;
pub mod stack_open;
pub(crate) mod tensor_algebra;
pub mod whir;
pub mod whir_config;
mod whir_induce;
mod whir_ntt_ext;

pub use pack::LOG_PACKING;
