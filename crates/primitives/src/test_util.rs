//! Shared deterministic generators for tests and benchmarks.
//!
//! The test-support feature lets other crates use these fixtures through development dependencies.

use rand::{RngCore, SeedableRng, rngs::StdRng};

use crate::field::F192;

/// A seeded [`StdRng`] plus the draws this repo's tests actually need.
pub struct Rng(StdRng);

impl Rng {
    /// The generator seeded by `seed`.
    pub fn new(seed: u64) -> Self {
        Self(StdRng::seed_from_u64(seed))
    }

    /// A uniform 32-bit word.
    pub fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    /// A uniform 64-bit word.
    pub fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    /// A uniform byte.
    pub fn next_u8(&mut self) -> u8 {
        self.next_u32() as u8
    }

    /// A uniform bit.
    pub fn bit(&mut self) -> bool {
        self.next_u64() & 1 != 0
    }

    /// `n` uniform bits.
    pub fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.bit()).collect()
    }

    /// A uniform element of `E`.
    pub fn ext(&mut self) -> F192 {
        F192::new(self.next_u64(), self.next_u64(), self.next_u64())
    }

    /// `n` uniform elements of `E`.
    pub fn ext_vec(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.ext()).collect()
    }
}
