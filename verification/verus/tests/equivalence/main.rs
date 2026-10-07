//! Differential checks between verified executable copies/models and production.
//!
//! Deterministic samples and edge cases can detect disagreement on exercised inputs, but neither
//! prove production-source equivalence nor prevent drift.

mod bits;
mod blake2s;
mod blake2s_batch;
mod gf2_64;
mod gf2_64x3;
mod gf2_8;
mod ntt;
