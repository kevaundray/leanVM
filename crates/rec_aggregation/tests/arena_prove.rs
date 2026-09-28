//! A retained proof must remain valid after later native prover invocations.

#[test]
fn repeated_proofs_survive_phase_resets() {
    parallel::init();
    zk_alloc::enable_arena();
    let signers = rec_aggregation::signers_cache::get_signers(3);
    let prove = |index: usize| {
        let (key, signature) = &signers[index];
        rec_aggregation::aggregate(
            &[],
            vec![(
                key.clone(),
                rec_aggregation::signers_cache::XMSS_EPOCH_A,
                rec_aggregation::signers_cache::message(),
                signature.clone(),
            )],
            vec![],
            &[],
            None,
            2,
        )
        .unwrap()
    };
    let first = prove(0);
    let saved = first.to_bytes();
    for index in [1, 2] {
        let proof = prove(index);
        proof.verify().unwrap();
        first.verify().unwrap();
        rec_aggregation::EthereumProof::from_bytes(&saved)
            .unwrap()
            .verify()
            .unwrap();
    }
}
