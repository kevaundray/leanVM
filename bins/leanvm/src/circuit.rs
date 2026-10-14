//! The dedicated XMSS program of `xmss_circuits`: one leaf over `n` signatures, or a merge of `merge`
//! such leaves, measured as `aggregate` measures the recursion guest.

use bench::Plan;
use primitives::{pretty_f64, pretty_integer};
use rec_aggregation::signers_cache;
use xmss_circuits::{RawSignature, aggregate, aggregate_with_stats};

fn signers(from: usize, to: usize) -> Vec<RawSignature> {
    signers_cache::get_signers(to)[from..to]
        .iter()
        .map(|(pk, sig)| {
            (
                pk.clone(),
                signers_cache::XMSS_LEAF_INDEX_A,
                signers_cache::message(),
                sig.clone(),
            )
        })
        .collect()
}

/// Prove one leaf of `n` signatures (`merge == 0`), or `merge` leaves of `n` distinct signers each and
/// then the merge node over them, which is what gets measured. The whole tree is verified after.
pub fn run_xmss_circuit(n: usize, merge: usize, log_inv_rate: usize, plan: Plan) {
    assert!(n > 0, "a leaf needs signatures");
    assert!(
        merge != 1 && merge <= xmss_circuits::MAX_RECURSIONS,
        "a merge takes 2 to 16 leaves"
    );
    let trace_span = tracing::info_span!("xmss circuit", n, merge, log_inv_rate).entered();
    leanvm_core::init_prover();
    let started = std::time::Instant::now();
    xmss_circuits::warm_up();
    let compile_time = started.elapsed();
    let program = xmss_circuits::program();
    let (children, raw) = if merge == 0 {
        (Vec::new(), signers(0, n))
    } else {
        let all = signers(0, merge * n);
        let leaves = (0..merge)
            .map(|k| aggregate(vec![], all[k * n..(k + 1) * n].to_vec(), None, log_inv_rate).expect("leaf proves"))
            .collect();
        (leaves, Vec::new())
    };
    let ((node, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        aggregate_with_stats(children.clone(), raw.clone(), None, log_inv_rate).expect("node proves")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        node.verify().expect("the tree verifies");
    });
    drop(trace_span);

    println!(
        "xmss node program: {} instructions (2^{} padded), compiled in {} s",
        pretty_integer(program.code_len()),
        program.prog.len().trailing_zeros(),
        pretty_f64(compile_time.as_secs_f64())
    );
    let label = if merge == 0 {
        format!("\nxmss circuit, {} XMSS signatures", pretty_integer(n))
    } else {
        format!(
            "\nxmss circuit merge {merge}\u{2192}1, over leaves of {} XMSS signatures",
            pretty_integer(n)
        )
    };
    crate::benchmark::report(&label, &stats, node.proof(), &prove_time);
    if merge > 0 {
        let bytes: u64 = node
            .proofs()
            .iter()
            .map(|proof| bincode::serialized_size(proof).expect("proof is serializable"))
            .sum();
        println!(
            "  tree proofs                 : {} proofs, {:.1} KiB",
            node.proofs().len(),
            bytes as f64 / 1024.0
        );
    } else {
        println!(
            "  per signature               : {} signatures/s",
            pretty_f64(n as f64 / prove_time.mean())
        );
    }
    println!(
        "  verifying (whole tree)      : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}
