//! End-to-end proof of a Rust RV64IM BLAKE2s hash chain.

#[test]
fn blake2s_hash_chain() {
    let steps: u64 = std::env::var("LEANVM_HASH_N")
        .map(|s| s.parse().expect("LEANVM_HASH_N is a u64"))
        .unwrap_or(8);
    let image = crate::aggregation::load_guest("LEANVM_HASH_CHAIN_ELF").expect("load hash-chain RV64IM guest");
    let mut digest = [0u8; 32];
    for _ in 0..steps {
        digest = primitives::hash::hash(&digest);
    }
    let mut statement = [0u8; 40];
    statement[..8].copy_from_slice(&steps.to_le_bytes());
    statement[8..].copy_from_slice(&digest);
    let public = primitives::hash::hash(&statement);
    let started = std::time::Instant::now();
    let (proof, stats) = riscv_proof::host::prove(&image.program, public, &steps.to_le_bytes(), u64::MAX, 2)
        .expect("prove hash-chain guest");
    let elapsed = started.elapsed();
    riscv_proof::verify(&image.info, public, &proof).expect("verify hash-chain proof");
    println!(
        "RV64IM BLAKE2s hash chain: {steps} hashes, {} cycles, {} memory events, {elapsed:?}",
        stats.cycles, stats.memory_events
    );
    let mut wrong_public = public;
    wrong_public[0] ^= 1;
    assert!(riscv_proof::verify(&image.info, wrong_public, &proof).is_err());
    assert!(
        image
            .program
            .execute(public, &(steps + 1).to_le_bytes(), u64::MAX)
            .is_err()
    );
}
