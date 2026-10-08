use fiat_shamir::transcript::{Challenger, ProofTranscript, ProverState, Receiver, Transmitter, VerifierState};
use pcs::ntt::AdditiveNttF64;
use pcs::ring_switch::{RingSwitch, SliceClaim};
use pcs::stack_open::{self, StackClaim};
use pcs::verifier::OpeningVerifier;
use pcs::whir;
use primitives::field::{F64, F192};
use primitives::multilinear::{eq_table, inner_product, interp, mle_eval};

fn seed(i: usize) -> u64 {
    let x = (i as u64 + 1).wrapping_mul(11400714819323198485);
    (x ^ (x >> 29)).wrapping_mul(13787848793156543929)
}

fn fixture(i: usize) -> F192 {
    F192::new(seed(3 * i), seed(3 * i + 1), seed(3 * i + 2))
}

fn emit_n(key: &str, xs: impl IntoIterator<Item = u64>) {
    let values: Vec<String> = xs.into_iter().map(|x| x.to_string()).collect();
    println!("{key}={}", values.join(","));
}

fn emit_e(key: &str, xs: impl IntoIterator<Item = F192>) {
    emit_n(key, xs.into_iter().flat_map(|x| [x.c0, x.c1, x.c2]));
}

// Use the production NTT over each K limb, not another polynomial evaluator.
fn encode_ext(message: &[F192], lanes: usize, rate: usize) -> Vec<F192> {
    let len = message.len() << rate;
    let depth = (len / lanes).ilog2() as usize;
    let ntt = AdditiveNttF64::standard(depth);
    let mut limbs = vec![vec![F64::ZERO; len]; 3];
    for (i, x) in message.iter().enumerate() {
        limbs[0][i] = F64(x.c0);
        limbs[1][i] = F64(x.c1);
        limbs[2][i] = F64(x.c2);
    }
    for limb in &mut limbs {
        ntt.encode_interleaved_in_place(limb, lanes, rate);
    }
    (0..len)
        .map(|i| F192::new(limbs[0][i].0, limbs[1][i].0, limbs[2][i].0))
        .collect()
}

fn vectors() {
    emit_n("kmul", (0..40).map(|i| (F64(seed(i)) * F64(seed(i + 41))).0));
    emit_n("kinv", (0..12).map(|i| F64(seed(i)).inv().0));
    emit_e("emul", (0..32).map(|i| fixture(i) * fixture(i + 33)));
    emit_e("eq", eq_table(&(0..4).map(fixture).collect::<Vec<_>>()));
    emit_n("roots", whir::eval_sk_at_vks(8).into_iter().map(|x| x.0));
    for lanes in [1, 3, 4] {
        let w: Vec<F64> = (0..lanes * 8).map(|i| F64(seed(i))).collect();
        let (_, pd) = whir::commit(&w, 5, 2, 1);
        emit_e(&format!("base_{lanes}"), pd.codeword.into_iter().map(F192::from));
    }
    let f: Vec<F192> = (0..32).map(fixture).collect();
    emit_e("ext", encode_ext(&f, 4, 1));
    let r = fixture(70);
    emit_e(
        "lane_fold",
        (0..16).map(|i| {
            let offset = (i / 8) * 16 + i % 8;
            interp(f[offset], f[offset + 8], r)
        }),
    );
    emit_e("low_fold", f.chunks_exact(2).map(|p| interp(p[0], p[1], r)));
    let mut point: Vec<F192> = (0..5).map(fixture).collect();
    point.rotate_left(2);
    emit_e("rotation", point.iter().copied());
    emit_e("rotation_mle", [inner_product(&f, &eq_table(&point))]);
    let qs = [0, 5, 5, 13];
    let mut ws = vec![F192::ONE];
    for i in 1..qs.len() {
        ws.push(ws[i - 1] * fixture(80));
    }
    // Columns are extracted by running unit coefficient vectors through the actual NTT.
    let mut basis = vec![F192::ZERO; 8];
    for j in 0..8 {
        let mut unit = vec![F192::ZERO; 8];
        unit[j] = F192::ONE;
        let col = encode_ext(&unit, 1, 1);
        basis[j] = qs
            .iter()
            .zip(&ws)
            .map(|(&q, &w)| col[q] * w)
            .fold(F192::ZERO, |a, x| a + x);
    }
    emit_e("induced", basis.iter().copied());
    emit_e(
        "induced_at",
        [inner_product(
            &basis,
            &eq_table(&(0..3).map(fixture).collect::<Vec<_>>()),
        )],
    );
    for rate in 1..=4 {
        for n in 15..=28 {
            let c = whir::config_for_rate(n, rate).unwrap();
            let values = std::iter::once(c.initial_k())
                .chain(c.level_ks().iter().copied())
                .chain(c.log_inv_rates().iter().copied())
                .chain(c.queries().iter().copied())
                .chain(c.ood_samples().iter().copied());
            emit_n(&format!("config_{n}_{rate}"), values.map(|x| x as u64));
        }
    }
    for (n, rate) in [(14, 1), (29, 1), (15, 0), (15, 5)] {
        assert!(whir::config_for_rate(n, rate).is_err());
    }
}

fn queries() {
    let empty = ProofTranscript {
        stream: vec![],
        merkle: vec![],
    };
    // Includes cross-limb chunks, several squeezes, duplicate positions, count zero,
    // and strata wider than the domain. The sampler itself is production code.
    for (depth, count) in [(1usize, 9usize), (5, 47), (7, 29), (17, 31), (63, 8), (8, 0)] {
        let label = format!("whir-lean-query-{depth}-{count}");
        let mut source = VerifierState::from_label(label.as_bytes(), &empty);
        let squeezes: Vec<_> = (0..count.div_ceil(192 / depth))
            .map(|_| Challenger::sample(&mut source))
            .collect();
        let mut verifier = VerifierState::from_label(label.as_bytes(), &empty);
        let qs = verifier.sample_queries(depth, count);
        emit_e(&format!("query_input_{depth}_{count}"), squeezes);
        emit_n(
            &format!("query_output_{depth}_{count}"),
            qs.into_iter().map(|q| q as u64),
        );
    }
}

fn production_smoke() {
    let log_n = whir::MIN_LOG_N;
    let config = whir::config_for_rate(log_n, 1).unwrap();
    let vars = log_n - config.initial_k();
    let stack: Vec<_> = (0..1 << vars).map(|i| F64(seed(i))).collect();
    let point: Vec<_> = (0..vars).map(fixture).collect();
    let eq = eq_table(&point);
    let slices = (0..64)
        .map(|bit| {
            stack
                .iter()
                .zip(&eq)
                .filter(|(x, _)| x.0 >> bit & 1 == 1)
                .fold(F192::ZERO, |acc, (_, &e)| acc + e)
        })
        .collect();
    let rings = vec![RingSwitch {
        offset: 0,
        qflock_vars: vars,
        claims: vec![SliceClaim {
            suffix_point: point.clone(),
            s_hat_v: slices,
        }],
    }];
    let claims = vec![StackClaim::Point {
        offset: 0,
        low_point: point.clone(),
        value: mle_eval(&stack, &point),
    }];
    let (commitment, pd) = whir::commit(&stack, log_n, config.initial_k(), 1);
    let label = b"whir-lean-production-smoke-fixed-statement-v1";
    let mut prover = ProverState::from_label(label);
    prover.add_root(&commitment.root);
    // Statement values ride the stream exactly once before the opening.
    for ring in &rings {
        prover.add_scalars(&ring.claims[0].s_hat_v);
    }
    prover.add_scalar(claims[0].value());
    stack_open::open(&mut prover, log_n, &stack, &pd, &config, &claims, &rings);
    let proof = prover.into_proof();
    let accepts = |proof: &ProofTranscript, lanes: usize| -> bool {
        let mut verifier = VerifierState::from_label(label, proof);
        let Ok(root) = Receiver::next_root(&mut verifier) else {
            return false;
        };
        if root != commitment.root {
            return false;
        }
        for &expected in &rings[0].claims[0].s_hat_v {
            if Receiver::next_scalar(&mut verifier).ok() != Some(expected) {
                return false;
            }
        }
        if Receiver::next_scalar(&mut verifier).ok() != Some(claims[0].value()) {
            return false;
        }
        stack_open::verify(&mut verifier, &config, log_n, lanes, root, &claims, &rings).is_ok()
            && verifier.finish().is_ok()
    };
    assert!(accepts(&proof, 1), "production honest opening rejected");
    let opening_start = 2 + rings[0].claims[0].s_hat_v.len() + claims.len();
    let first_ood = opening_start + 2 + 2 * config.initial_k() + 2;
    let mut residual_start = first_ood + 3 * config.ood_samples()[1] + 1 + 2;
    for (i, &k) in config.level_ks().iter().enumerate() {
        residual_start += 2 * k;
        if i + 1 < config.level_steps() {
            residual_start += 2 + 3 * config.ood_samples()[i + 2] + 1 + 2;
        }
    }
    let mut bad = proof.clone();
    bad.stream[first_ood] += F192::ONE;
    assert!(!accepts(&bad, 1), "production bad OOD value accepted");
    let mut bad = proof.clone();
    bad.stream[residual_start] += F192::ONE;
    assert!(!accepts(&bad, 1), "production bad final polynomial accepted");
    let mut bad = proof.clone();
    bad.stream.pop();
    assert!(!accepts(&bad, 1), "production truncated stream accepted");
    let mut bad = proof.clone();
    bad.stream.push(F192::ONE);
    assert!(!accepts(&bad, 1), "production trailing stream accepted");
    let mut bad = proof.clone();
    bad.stream[opening_start] += F192::ONE;
    assert!(!accepts(&bad, 1), "production bad opening round accepted");
    let mut bad = proof.clone();
    bad.merkle.pop();
    assert!(!accepts(&bad, 1), "production missing authentication accepted");
    assert!(!accepts(&proof, 0), "production zero lanes accepted");
    println!(
        "rust_smoke=honest,ring_switch,point_claim,truncated_lanes,short_stream,trailing_stream,bad_round,bad_ood,bad_final,missing_authentication,bad_layout"
    );
}

fn main() {
    vectors();
    queries();
    production_smoke();
}
