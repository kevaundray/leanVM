//! Field-native circuits with authenticated static dataflow.

mod air;
mod algebra;
mod circuit;
mod context;
mod flock_verifier;
mod gkr;
mod native;
mod opening;
mod packed_verifier;
mod proof;
mod protocol;
mod recursor;
mod ring;
mod risc_layout;
mod risc_verifier;
mod stacked;
mod tables;
mod transcript;
mod uint;

pub use circuit::{Builder, Circuit, Wire};
pub use fiat_shamir::transcript::Proof;
pub use proof::{Key, Summary};
pub use recursor::{Child, NodeProof, Recursor};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidCircuit,
    InvalidInput,
    InvalidWitness,
    InvalidProof,
    Capacity,
}

impl core::fmt::Display for Error {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::InvalidCircuit => "invalid native circuit",
            Self::InvalidInput => "invalid native circuit input",
            Self::InvalidWitness => "invalid native circuit witness",
            Self::InvalidProof => "invalid native circuit proof",
            Self::Capacity => "native circuit exceeds proving capacity",
        })
    }
}

impl std::error::Error for Error {}
