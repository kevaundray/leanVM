//! Recursion as a circuit: a machine whose program is the fixed list of rows that verify leanVM proofs of
//! given shapes, proven with the same bus, table sumcheck, flock and stacked WHIR as the RISC-V machine.

pub mod circuit;
pub mod inner;
pub mod transcript;
