use super::reduce::{FORGE, Forge, Term};
use super::*;
use crate::rv::asm::*;
use primitives::test_rng::Rng;

fn program() -> Program {
    let text = Asm::new()
        .li(Reg::T0, 7)
        .li(Reg::T1, 9)
        .r(Xor, Reg::A0, Reg::T0, Reg::T1)
        .label("loop")
        .i(Addi, Reg::T1, Reg::T1, -1)
        .branch(Bne, Reg::T1, Reg::ZERO, "loop")
        .exit()
        .finish();
    Program::new(&text, crate::rv::Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
}

fn forged<T>(forge: Forge, f: impl FnOnce() -> T) -> T {
    FORGE.set(forge);
    let out = f();
    FORGE.set(Forge::None);
    out
}

/// A tree of four leaves at arity two verifies, and each forgery is refused: by the prover where the circuit
/// cannot hold, by the root's verifier where the claims it carries are false.
#[test]
fn a_tree_verifies_and_refuses_forgeries() {
    let program = program();
    let (proof, output, _) = program.prove(&[], Rate::MIN).expect("the run halts");
    let leaf = InnerProof::new(&program, &proof, output).expect("an honest proof");
    let (taus, log_inv_rate) = announced_shape(&leaf.proof).expect("a shape");
    let tree = Tree::new(&program, taus, log_inv_rate, 2, Rate::MIN).expect("a valid shape");

    let lift = tree.prove_lift(&leaf).expect("an honest leaf");
    tree.verify(&lift, &[output]).expect("a lift is the root of one leaf");
    let node = tree.prove_node(&[lift.clone(), lift.clone()]).expect("honest children");
    let root = tree.prove_node(&[node.clone(), node.clone()]).expect("honest children");
    let outputs = [output; 4];
    tree.verify(&root, &outputs).expect("the root verifies");

    // The root's statement.
    let mut wrong = outputs;
    wrong[2][0] ^= 1;
    assert_eq!(tree.verify(&root, &wrong), Err(TreeError::Outputs), "a wrong leaf output");
    assert_eq!(tree.verify(&root, &outputs[..2]), Err(TreeError::Outputs), "too few leaves");
    let mut tampered = root.clone();
    tampered.statement.matrices[3][0] += F192::ONE;
    assert!(matches!(tree.verify(&tampered, &outputs), Err(TreeError::Root(_))), "a matrix value");
    let mut tampered = root.clone();
    tampered.statement.dense_point[1] += F192::ONE;
    assert!(matches!(tree.verify(&tampered, &outputs), Err(TreeError::Root(_))), "a reduced point");
    let mut tampered = root.clone();
    tampered.statement.dense_values[BYTECODE] += F192::ONE;
    assert!(matches!(tree.verify(&tampered, &outputs), Err(TreeError::Root(_))), "a program value");

    // A child the node's prover is handed.
    let mut forged_child = node.clone();
    let mid = forged_child.proof.stream.len() / 2;
    forged_child.proof.stream[mid] += F192::ONE;
    assert!(matches!(
        tree.prove_node(&[node.clone(), forged_child]),
        Err(TreeError::Child { index: 1, .. })
    ));
    let mut forged_child = node.clone();
    forged_child.statement.matrices[0][1] += F192::ONE;
    assert!(matches!(
        tree.prove_node(&[forged_child, node.clone()]),
        Err(TreeError::Child { index: 0, .. })
    ));
    let other = Tree::new(&program, taus, log_inv_rate, 3, Rate::MIN).expect("a valid shape");
    let other_lift = other.prove_lift(&leaf).expect("an honest leaf");
    assert!(
        matches!(
            tree.prove_node(&[lift.clone(), other_lift]),
            Err(TreeError::Child { index: 1, .. })
        ),
        "a child of another tree's shape"
    );
    assert!(matches!(tree.prove_node(&[lift.clone()]), Err(TreeError::Arity { .. })));

    // A forged leaf.
    let mut bad = InnerProof {
        program: &program,
        proof: leaf.proof.clone(),
        output,
    };
    let mid = bad.proof.stream.len() / 2;
    bad.proof.stream[mid] += F192::ONE;
    assert!(matches!(tree.prove_lift(&bad), Err(TreeError::Unsatisfied(_))), "a forged leaf");

    // Reduced claims that satisfy every identity and are false: an honest node's prover cannot reduce them, a
    // cheating one carries them up, and the root's verifier refuses them.
    for forge in [Forge::Matrix, Forge::Dense] {
        let false_lift = forged(forge, || tree.prove_lift(&leaf)).expect("the forgery satisfies the circuit");
        assert!(matches!(tree.verify(&false_lift, &[output]), Err(TreeError::Claim(_))), "{forge:?}");
        let children = [lift.clone(), false_lift];
        assert!(matches!(tree.prove_node(&children), Err(TreeError::Unsatisfied(_))), "{forge:?}");
        let carried = forged(forge, || tree.prove_node(&children)).expect("a cheating node");
        assert!(matches!(tree.verify(&carried, &[output; 2]), Err(TreeError::Claim(_))), "{forge:?} carried");
    }
}

/// The dense reduction leaves each polynomial's own value at its prefix of the point, and refuses a false claim.
#[test]
fn the_dense_reduction_reduces_to_the_polynomials() {
    let mut rng = Rng::new(17);
    let n_vars = [3, 6, 4];
    let tables: Vec<Vec<F64>> = n_vars.iter().map(|&n| (0..1 << n).map(|_| F64(rng.next_u64())).collect()).collect();
    let refs: Vec<&[F64]> = tables.iter().map(Vec::as_slice).collect();
    let run = |lie: bool| {
        let mut rng = Rng::new(5);
        let mut b = Builder::new();
        let mut claims = Vec::new();
        for (j, &n) in n_vars.iter().enumerate() {
            for _ in 0..2 {
                let p = rng.ext_vec(n);
                let v = mle_eval(&tables[j], &p);
                let point = p.iter().map(|&x| b.free_e(x)).collect();
                let value = b.free_e(v);
                claims.push(DenseClaim::at(j, point, value));
            }
        }
        // `c·P(z, 1, 0, k) + P(z', 0, 1, k)` on the last polynomial, `k` a Boolean wire.
        let low = rng.ext_vec(2);
        let c = rng.ext();
        let at = |bits: [u64; 2]| -> F192 {
            let mut p = low.clone();
            p.extend(bits.map(|x| F192::new(x, 0, 0)));
            mle_eval(&tables[2], &p)
        };
        let mut v = c * at([1, 0]) + mle_eval(&tables[2], &[low[0], F192::ZERO, F192::ONE, F192::ZERO]);
        if lie {
            v += F192::ONE;
        }
        let low_w: Vec<Ew> = low.iter().map(|&x| b.free_e(x)).collect();
        let cw = b.free_e(c);
        let k = b.free_e(F192::ZERO);
        let value = b.free_e(v);
        claims.push(DenseClaim {
            poly: 2,
            low: low_w,
            terms: vec![
                Term {
                    coef: Some(cw),
                    n_low: 2,
                    bits: vec![true],
                    top: vec![k],
                },
                Term {
                    coef: None,
                    n_low: 1,
                    bits: vec![false, true],
                    top: vec![k],
                },
            ],
            value,
        });
        let mut t = Design::aggregate(&mut b);
        let out = reduce_dense(&mut b, &mut t, &n_vars, Some(&refs), &claims);
        let point: Vec<F192> = out.point.iter().map(|&w| b.e(w)).collect();
        let values: Vec<F192> = out.values.iter().map(|&w| b.e(w)).collect();
        (b.finish().2, point, values)
    };
    let (failures, point, values) = run(false);
    assert!(failures.is_empty(), "{failures:?}");
    for (j, &n) in n_vars.iter().enumerate() {
        assert_eq!(values[j], mle_eval(&tables[j], &point[..n]), "polynomial {j}");
    }
    assert!(!run(true).0.is_empty(), "a false claim is reduced");
}

/// The matrix reduction leaves each circuit's `A` and `B` at its prefixes of the points, from lincheck's claims
/// and from claims at points, and refuses a false claim.
#[test]
fn the_matrix_reduction_reduces_to_the_matrices() {
    let k_skip = flock::zerocheck::K_SKIP;
    let run = |lie: bool| {
        let mut rng = Rng::new(9);
        let mut b = Builder::new();
        let mut claims = Vec::new();
        for f in [0, 3, machine::hash_flock()] {
            let circuit = class_flock::circuit(f);
            let k = circuit.k_log();
            let (z, x_rest, r_rest, slices) = (rng.ext(), rng.ext_vec(k - k_skip), rng.ext_vec(k - k_skip), rng.ext_vec(64));
            let alpha = rng.ext();
            let form = flock::lincheck::MatrixForm {
                alpha,
                z_skip: z,
                x_inner_rest: x_rest.clone(),
                r_inner_rest: r_rest.clone(),
                s_hat_v: slices.clone(),
            };
            let mut v = form.evaluate(circuit);
            if lie && f == 3 {
                v += F192::ONE;
            }
            let w = |b: &mut Builder, xs: &[F192]| xs.iter().map(|&x| b.free_e(x)).collect::<Vec<_>>();
            let (zw, xw, rw, sw, aw, vw) = (b.free_e(z), w(&mut b, &x_rest), w(&mut b, &r_rest), w(&mut b, &slices), b.free_e(alpha), b.free_e(v));
            claims.push(MatrixClaim {
                circuit: f,
                row: Row::Quirky { z: zw, rest: xw },
                col: Col::Slices { slices: sw, rest: rw },
                weights: [Weight::One, Weight::W(aw)],
                value: vw,
            });
            let (px, py) = (rng.ext_vec(k), rng.ext_vec(k));
            let (ra, rb) = circuit.row_values(&eq_table(&py));
            let u = eq_table(&px);
            let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
            for (weights, value) in [([Weight::One, Weight::Zero], dot(&ra)), ([Weight::Zero, Weight::One], dot(&rb))] {
                let (pxw, pyw, vw) = (w(&mut b, &px), w(&mut b, &py), b.free_e(value));
                claims.push(MatrixClaim {
                    circuit: f,
                    row: Row::Point(pxw),
                    col: Col::Point(pyw),
                    weights,
                    value: vw,
                });
            }
        }
        let mut t = Design::aggregate(&mut b);
        let out = reduce_matrices(&mut b, &mut t, true, &claims);
        let rows: Vec<F192> = out.rows.iter().map(|&w| b.e(w)).collect();
        let cols: Vec<F192> = out.cols.iter().map(|&w| b.e(w)).collect();
        let values: Vec<[F192; 2]> = out.values.iter().map(|v| v.map(|w| b.e(w))).collect();
        (b.finish().2, rows, cols, values)
    };
    let (failures, rows, cols, values) = run(false);
    assert!(failures.is_empty(), "{failures:?}");
    for (f, v) in values.iter().enumerate() {
        let circuit = class_flock::circuit(f);
        let k = circuit.k_log();
        let (ra, rb) = circuit.row_values(&eq_table(&cols[..k]));
        let u = eq_table(&rows[..k]);
        let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
        assert_eq!(*v, [dot(&ra), dot(&rb)], "circuit {f}");
    }
    assert!(!run(true).0.is_empty(), "a false claim is reduced");
}
