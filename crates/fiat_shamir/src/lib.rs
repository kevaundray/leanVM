//! Fiat-Shamir: an interactive proof made non-interactive by a duplex sponge.
//!
//! The design is spongefish's, after `draft-irtf-cfrg-fiat-shamir` and Chiesa-Orru (eprint 2025/536).
//!
//! A transcript has four operations:
//!
//! - a prover message is absorbed and written to the proof;
//! - a public message is absorbed only;
//! - a verifier message is squeezed;
//! - a hint is written to the proof and never absorbed.
//!
//! - A session identifier names the protocol and the relation.
//! - The instance is the first message, so every challenge depends on the statement.
//! - A message is absorbed in the same call that writes or reads it.
//! - The proof's messages are exactly the bytes the sponge absorbed.
//!
//! The sponge is a duplex built from the BLAKE2s compression function, the one hash the VM proves.
//!
//! A transcript hashes by its [`Hashing`]: the prover's the build's fastest kernels ([`Native`]), the native
//! verifier's the portable code ([`Portable`]). Both give the same bytes.

pub mod arith;
mod codec;
mod duplex;
mod error;
mod pow;
mod proof;
mod prover;
mod session;
mod verifier;

use arith::{Native, Portable};
use primitives::hash::portable;

pub use codec::{Encoding, FromNarg, FromUniform, LengthPrefixed};
pub use duplex::{Blake2sDuplex, DuplexSponge, MAX_SQUEEZE, Role};
pub use error::TranscriptError;
pub use pow::ProofOfWork;
pub use proof::ProofTranscript;
pub use prover::ProverState;
pub use session::SessionId;
pub use verifier::VerifierState;

/// What both sides of a transcript do alike: draw verifier messages.
///
/// A step that only draws challenges, such as sampling query positions, is then written once.
pub trait Challenger {
    /// Draw a verifier message from the sponge.
    fn verifier_message<T: FromUniform>(&mut self) -> T;
}

/// How a transcript hashes: its duplex's compressions and its proof of work's trials.
pub trait Hashing: Copy {
    /// The BLAKE2s compression of `m` into `h` at byte counter `t`, final if `last`.
    fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool);

    /// One-shot BLAKE2s-256.
    fn hash(data: &[u8]) -> [u8; 32];
}

/// The prover's: the build's kernels.
impl Hashing for Native {
    fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
        primitives::hash::compress(h, m, t, last);
    }

    fn hash(data: &[u8]) -> [u8; 32] {
        primitives::hash::hash(data)
    }
}

/// The native verifier's: the portable code.
impl Hashing for Portable {
    fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
        portable::compress(h, m, t, last);
    }

    fn hash(data: &[u8]) -> [u8; 32] {
        portable::hash(data)
    }
}
