pub mod aggregation;
pub mod benchmark;
pub mod fibonacci;
/// End-to-end RV64IM BLAKE2s hash-chain workload.
#[cfg(test)]
mod hash_chain;
#[cfg(test)]
mod runtime_tests;
pub mod signers_cache;

pub use aggregation::{
    AggregateVerifyError, AggregationError, ClaimSelection, DA_LOG_CELL, DA_LOG_K, DA_MAX_ROWS, EthereumProof,
    GuestImageError, MAX_DA_ROOTS, MAX_EPOCHS, MAX_KEYS, MAX_RECURSIONS, SignatureClaims, SphincsClaim, XmssClaimGroup,
    aggregate, warm_up,
};
pub use benchmark::{run_aggregation, run_recursion};
pub use fibonacci::run_fibonacci;

/// The pieces every workload's benchmark report ends with.
///
/// Each caller drops its root tracing span before printing: tracing-forest
/// renders its tree only when that span closes, so the complete trace has to be
/// flushed above the report.
mod report {
    use primitives::pretty_f64;

    /// Peak resident set size, in GiB.
    pub fn peak_gib() -> String {
        pretty_f64(primitives::bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    }

    pub fn print_proof_size(bytes: usize) {
        println!("  proof size                  : {:.1} KiB", bytes as f64 / 1024.0);
    }
}
