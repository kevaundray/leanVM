//! leanVM: a minimal zkVM for RISC-V (rv64im).
//!
//! # Overview
//!
//! A program is a guest's ELF executable, or a text written by hand with the assembler.
//!
//! The prover runs it on its advice and proves the run.
//!
//! The verifier checks the proof against two public things only:
//!
//! - the program,
//! - the output the run claims, the registers `a0..a3` at its exit.
//!
//! ```text
//!     prover  : program + advice  ──run──▶  output  ──prove──▶  proof
//!     verifier: program + output + proof  ──▶  accept or refuse
//! ```
//!
//! # The advice
//!
//! The advice is the words the program finds at the advice base.
//!
//! It is the prover's alone: the statement says nothing about it, beyond how many words fit.
//!
//! So a proof shows that *some* advice makes the program exit with the output.
//!
//! What a program reads there, it must check itself.
//!
//! # Zero knowledge
//!
//! A plain proof is no secret: a verifier who can guess the advice recomputes the proof and compares.
//! A prover made with [`Prover::zk`] makes zero-knowledge proofs, which reveal nothing of the advice or the run beyond the statement and the run's shape (each table's height and the rate).
//! A program whose advice is private must therefore prove at a fixed public shape.
//!
//! # Examples
//!
//! ```no_run
//! use leanvm::{Program, Proof, Prover, Rate};
//!
//! // The prover's side.
//! let program = Program::from_elf(&std::fs::read("guest.elf")?)?;
//! let run = Prover::new(Rate::MIN).prove(&program, &[42])?;
//! let bytes = run.proof.to_bytes();
//!
//! // The verifier's side: the same program, the claimed output, and the bytes.
//! program.verify(run.output, &Proof::from_bytes(&bytes)?)?;
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! Many proofs of one program aggregate into one proof through the aggregation module.

pub use leanvm_core::{
    DecodeError, ElfError, InvalidRate, Output, Program, ProgramError, Proof, ProveError, ProvenRun, Prover,
    Randomness, Rate, Region, Stats, Trap, VerifyError, asm,
};

/// Aggregation trees: many proofs of one program, verified as one.
///
/// # Overview
///
/// ```text
///                 node                  verifies `arity` tree proofs, of either kind
///               /      \
///        first-level   first-level      each verifies `arity_0` proofs of the program
///          /  \          /  \
///       leaf  leaf    leaf  leaf
/// ```
///
/// Every tree proof states the same few hundred words:
///
/// - a digest of its leaves' outputs,
/// - claims that only the root's verifier evaluates.
///
/// A tree over one leaf, with `arity_0 = 1`, is a single proof's recursion.
pub mod aggregate {
    pub use leanvm_core::{
        CircuitStats, DensePoly, FalseClaim, Kind, Leaf, LeafShape, Part, TableStats, Tree, TreeError, TreeProof,
        TreeShape, Unsatisfied,
    };
}
