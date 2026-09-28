//! Wrapping-u64 Fibonacci computed by an actual Rust RV64IM guest.

use primitives::{bench::Plan, pretty_f64, pretty_integer};

fn public_input(n: u64) -> [u8; 32] {
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..n {
        (a, b) = (b, a.wrapping_add(b));
    }
    let mut public = [0; 32];
    public[..8].copy_from_slice(&n.to_le_bytes());
    public[8..16].copy_from_slice(&a.to_le_bytes());
    public
}

/// Prove and verify Rust guest Fibonacci modulo 2^64. The guest reads `n` from
/// its witness and checks both `n` and the result against the public input.
/// Set LEANVM_FIBONACCI_ELF to the built Fibonacci RV64IM executable.
pub fn run_fibonacci(n: usize, log_inv_rate: usize, plan: Plan) {
    let trace_span = tracing::info_span!("RV64IM Fibonacci", n, log_inv_rate).entered();
    let rate = u8::try_from(log_inv_rate).expect("inverse rate fits u8");
    let image = crate::aggregation::load_guest("LEANVM_FIBONACCI_ELF").expect("load Fibonacci RV64IM guest");
    let public = public_input(n as u64);
    let witness = (n as u64).to_le_bytes();
    parallel::init();
    let ((proof, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        riscv_proof::host::prove(&image.program, public, &witness, u64::MAX, rate)
            .expect("prove Fibonacci RV64IM execution")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        riscv_proof::verify(&image.info, public, &proof).expect("verify Fibonacci proof")
    });
    drop(trace_span);
    println!("RV64IM Fibonacci (modulo 2^64), N = {}", pretty_integer(n));
    println!("  RV64IM instruction cycles   : {}", pretty_integer(stats.cycles));
    println!(
        "  byte memory events          : {}",
        pretty_integer(stats.memory_events)
    );
    println!(
        "  committed words             : {}",
        pretty_integer(stats.committed_words)
    );
    crate::report::print_proof_size(proof.to_bytes().len());
    let cycles_per_second = (stats.cycles as f64 / prove_time.mean()).round() as u64;
    println!(
        "  proving                     : {} s{}   {} cycles/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_integer(cycles_per_second),
        crate::report::peak_gib()
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}

#[cfg(test)]
mod tests {
    #[test]
    fn fibonacci() {
        super::run_fibonacci(200_000, 2, primitives::bench::Plan::default());
    }

    #[test]
    fn fibonacci_result_and_count_are_bound() {
        let image = crate::aggregation::load_guest("LEANVM_FIBONACCI_ELF").unwrap();
        for n in [0u64, 1, 2, 94, 95] {
            let public = super::public_input(n);
            image.program.execute(public, &n.to_le_bytes(), 1_000_000).unwrap();
            let mut wrong_result = public;
            wrong_result[8] ^= 1;
            assert!(
                image
                    .program
                    .execute(wrong_result, &n.to_le_bytes(), 1_000_000)
                    .is_err()
            );
            assert!(
                image
                    .program
                    .execute(public, &(n + 1).to_le_bytes(), 1_000_000)
                    .is_err()
            );
        }
    }
}
