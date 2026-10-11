//! The recursion machine: a circuit of rows over eight tables, wired by copy cycles and dynamic tuples, and its proof
//! (Annex E).

mod bus;
pub mod circuit;
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "the STEP and LINK slot indices serve the chain builder, which no circuit uses yet")
)]
mod clean;
mod error;
mod fixed;
mod layout;
pub mod proof;
pub mod sphincs;
pub mod table;
pub mod transcript;
pub mod tree;
pub mod verifier;
pub mod xmss;

pub use error::RecError;
pub(crate) use fixed::FixedColumn;
