//! End-to-end proof verification across arena phase resets.
//!
//! This has its own binary because arena phases are process-global and cannot nest.

use rec_aggregation::{aggregate, signers_cache};

#[test]
fn repeated_proofs_survive_phase_resets() {
    lean_vm::init_prover();
    assert!(
        zk_alloc::is_enabled(),
        "this test is meaningless unless the arena is engaged"
    );

    let raw_xmss: Vec<_> = signers_cache::get_signers(3)
        .into_iter()
        .map(|(pk, sig)| (pk, signers_cache::XMSS_EPOCH_A, signers_cache::message(), sig))
        .collect();
    let raw_sphincs = signers_cache::get_sphincs_signers(1);
    let blob: Vec<u64> = (0..lean_da::BLOB_SYMBOLS as u64).collect();
    let proofs: Vec<_> = (0..3)
        .map(|_| {
            aggregate(
                &[],
                raw_xmss.clone(),
                raw_sphincs.clone(),
                &blob,
                None,
                lean_vm::pcs::TEST_LOG_INV_RATE,
            )
            .expect("leaf aggregates")
        })
        .collect();
    // Verified only after the last phase reset, so a proof holding arena memory fails too.
    for proof in &proofs {
        proof.verify().expect("the leaf aggregate verifies");
    }

    let stats = zk_alloc::stats();
    assert!(stats.phases >= 3, "expected one phase per proof, got {stats:?}");
    assert!(
        stats.peak_bytes > 0,
        "no buffer reached the arena, so nothing was actually exercised: {stats:?}"
    );
    assert_eq!(
        stats.overflow, 0,
        "a slab overflowed into the system allocator, so SLAB_SIZE is undersized: {stats:?}"
    );
}
