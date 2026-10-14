// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The fields: `K = F64 = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)` and `E = F192 = K[y] / (y^3 + y + 1)`.
//!
//! - Machine words, addresses, the pc, timestamps and every committed column are `K`-valued.
//! - Challenges, sumcheck and GKR values, and transcript scalars are `E`-valued.
//!
//! The types:
//!
//! - [`F64`] is `K`.
//! - [`F192`] is `E`.
//! - [`F192Unreduced`] is a sum of `E` products, reduced once at its end.
//! - [`F8`] is `GF(2^8)` modulo the AES polynomial `x^8 + x^4 + x^3 + x + 1`, embedded in `E` as a subfield.
//! - [`Subfield`] puts `K` and `E` behind one interface.
//! - [`lanes::Lanes`] holds elements of `E` in vector registers, so one kernel serves every target.

#[cfg(target_arch = "aarch64")]
pub mod neon;

pub mod gf2_64;
mod gf2_64x3;
pub mod gf2_8;
pub mod lanes;
mod subfield;

pub use gf2_8::{F8, PHI8_TABLE};
pub use gf2_64::F64;
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub use gf2_64x3::aarch64::{F192x1, F192x1Unreduced};
#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
pub use gf2_64x3::x86_64::{F192x1, F192x1Unreduced};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
pub use gf2_64x3::x86_64::{F192x8, F192x8Sum};
pub use gf2_64x3::{F192, F192Unreduced, Weights8, dot_base};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
pub use gf2_64x3::{F192x4, F192x4Unreduced, MixedSums8};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
pub use subfield::PackedCoeffs;
pub use subfield::{Subfield, padded_width};
