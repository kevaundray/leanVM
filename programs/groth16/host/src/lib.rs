//! The Groth16 program off the VM: proofs World Chain verified, laid out as the guest's advice,
//! and the output the guest must give.
//!
//! The proofs are `proofs.txt`: each the call World ID 4.0's `WorldIDVerifier` made to its
//! Groth16 verifier contract in one transaction, the proof compressed as the contract takes it.
//! The host decompresses the points as the contract does, so the guest reads `A`, `B` and `C`
//! whole and checks them itself.

use ark_bn254::{Fq, Fq2};
use ark_ff::{BigInt, Field, PrimeField};
use groth16::{G1Point, G2Point, Inputs, N_INPUTS, Proof};
use leanvm_guest::{PublicValues, as_words_unchecked};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../groth16.elf");

/// The proofs, with the transactions that carried them.
const PROOFS: &str = include_str!("../proofs.txt");

/// What one run of the guest is given, and what it must output.
pub struct Run {
    pub advice: Vec<u64>,
    pub expected: [u64; 4],
}

/// A proof from the chain: the transaction that carried it, its block, the proof and its public
/// inputs.
pub struct Fixture {
    pub tx: &'static str,
    pub block: u64,
    pub proof: Proof,
    pub inputs: Inputs,
}

/// Every proof `proofs.txt` holds, in its order.
pub fn fixtures() -> Vec<Fixture> {
    PROOFS
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let mut fields = line.split_whitespace();
            let tx = fields.next().expect("a transaction");
            let block = fields.next().expect("a block").parse().expect("a block number");
            let words: Vec<[u64; 4]> = fields.map(word).collect();
            assert_eq!(words.len(), 4 + N_INPUTS, "{tx}: a compressed proof and its inputs");
            Fixture {
                tx,
                block,
                proof: decompress(&words[..4]),
                inputs: words[4..].try_into().expect("the inputs"),
            }
        })
        .collect()
}

/// `n` proofs, the fixtures in turn.
pub fn batch(n: usize) -> Run {
    // What the guest reads: the count, then each proof and its inputs.
    let mut advice = vec![n as u64];
    // What it commits: each proof's inputs.
    let mut public = PublicValues::new();
    for fixture in fixtures().iter().cycle().take(n) {
        groth16::verify(&fixture.proof, &fixture.inputs).expect("the chain's proofs verify");
        // SAFETY: `repr(C)` words, with no padding (see its definition).
        advice.extend(unsafe { as_words_unchecked(&fixture.proof) });
        advice.extend(fixture.inputs.as_flattened());
        public.commit(&fixture.inputs);
    }
    Run {
        advice,
        expected: public.digest(),
    }
}

/// A 256-bit word from its hex, as little-endian limbs.
fn word(hex: &str) -> [u64; 4] {
    let digits = hex.strip_prefix("0x").expect("a hex word");
    let padded = format!("{digits:0>64}");
    assert_eq!(padded.len(), 64, "a 256-bit word");
    std::array::from_fn(|i| u64::from_str_radix(&padded[64 - 16 * (i + 1)..64 - 16 * i], 16).expect("hex"))
}

/// `x >> k` for `k` in `1..64`.
fn shr(x: &[u64; 4], k: u32) -> [u64; 4] {
    std::array::from_fn(|i| x[i] >> k | x.get(i + 1).map_or(0, |high| high << (64 - k)))
}

fn fq(limbs: [u64; 4]) -> Fq {
    Fq::from_bigint(BigInt(limbs)).expect("a coordinate below p")
}

fn limbs(x: Fq) -> [u64; 4] {
    x.into_bigint().0
}

/// The contract's square root, `a^((p + 1) / 4)`, if `a` is a square.
fn sqrt(a: Fq) -> Option<Fq> {
    let mut exponent = Fq::MODULUS.0;
    exponent[0] += 1;
    let x = a.pow(shr(&exponent, 2));
    (x.square() == a).then_some(x)
}

/// The contract's square root in `F_p2`: `hint` picks the sign of the norm's root.
fn sqrt2(a: Fq2, hint: bool) -> Option<Fq2> {
    let d = sqrt(a.c0.square() + a.c1.square())?;
    let d = if hint { -d } else { d };
    let x0 = sqrt((a.c0 + d) / Fq::from(2))?;
    let x = Fq2::new(x0, a.c1 / (x0 + x0));
    (x.square() == a).then_some(x)
}

/// The contract's `decompress_g1`: `x` with the sign of `y` in its low bit.
fn decompress_g1(c: &[u64; 4]) -> G1Point {
    let x = fq(shr(c, 1));
    let y = sqrt(x.square() * x + Fq::from(3)).expect("a point on G1");
    let y = if c[0] & 1 == 1 { -y } else { y };
    G1Point {
        x: limbs(x),
        y: limbs(y),
    }
}

/// The contract's `decompress_g2`: `x`'s real part with the hint and the sign in its low bits.
fn decompress_g2(c0: &[u64; 4], c1: &[u64; 4]) -> G2Point {
    let x = Fq2::new(fq(shr(c0, 2)), fq(*c1));
    let b = Fq2::from(3) / Fq2::new(Fq::from(9), Fq::ONE);
    let y = sqrt2(x.square() * x + b, c0[0] & 2 == 2).expect("a point on the twist");
    let y = if c0[0] & 1 == 1 { -y } else { y };
    G2Point {
        x: [limbs(x.c0), limbs(x.c1)],
        y: [limbs(y.c0), limbs(y.c1)],
    }
}

/// The contract's compressed proof: `A`, `B`'s imaginary then real part of `x`, `C`.
fn decompress(words: &[[u64; 4]]) -> Proof {
    Proof {
        a: decompress_g1(&words[0]),
        b: decompress_g2(&words[2], &words[1]),
        c: decompress_g1(&words[3]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Bn254, Fr, G1Affine, G2Affine};
    use ark_ec::AffineRepr;
    use ark_groth16::{Groth16, PreparedVerifyingKey, VerifyingKey, prepare_verifying_key};
    use groth16::Error::{InputNotInField, NotInField, NotInSubgroup, NotOnCurve, Rejected};
    use groth16::vk;
    use leanvm_core::cpu::Program;
    use leanvm_core::rv::{Machine, Trap};
    use primitives::hash::{digest_words, hash};

    fn g1(p: &G1Point) -> G1Affine {
        G1Affine::new(fq(p.x), fq(p.y))
    }

    fn g2(p: &G2Point) -> G2Affine {
        G2Affine::new(Fq2::new(fq(p.x[0]), fq(p.x[1])), Fq2::new(fq(p.y[0]), fq(p.y[1])))
    }

    /// arkworks' verifier, with the guest's key.
    fn reference() -> PreparedVerifyingKey<Bn254> {
        prepare_verifying_key(&VerifyingKey {
            alpha_g1: g1(&vk::ALPHA),
            beta_g2: -g2(&vk::BETA_NEG),
            gamma_g2: -g2(&vk::GAMMA_NEG),
            delta_g2: -g2(&vk::DELTA_NEG),
            gamma_abc_g1: vk::IC.iter().map(g1).collect(),
        })
    }

    fn accepts(pvk: &PreparedVerifyingKey<Bn254>, proof: &Proof, inputs: &Inputs) -> bool {
        let proof = ark_groth16::Proof {
            a: g1(&proof.a),
            b: g2(&proof.b),
            c: g1(&proof.c),
        };
        let inputs: Vec<Fr> = inputs
            .iter()
            .map(|x| Fr::from_bigint(BigInt(*x)).expect("an input below r"))
            .collect();
        Groth16::<Bn254>::verify_proof(pvk, &proof, &inputs).expect("well-formed")
    }

    fn negated(y: [u64; 4]) -> [u64; 4] {
        limbs(-fq(y))
    }

    #[test]
    fn the_chains_proofs_verify_and_nothing_near_them() {
        // Fixture: proofs World Chain accepted, from different transactions.
        let pvk = reference();
        let fixtures = fixtures();
        for f in &fixtures {
            assert!(accepts(&pvk, &f.proof, &f.inputs), "{}: arkworks", f.tx);
            assert_eq!(groth16::verify(&f.proof, &f.inputs), Ok(()), "{}", f.tx);

            // Mutation: A negated, still on the curve.
            //
            //     e(-A, B) = e(A, B)^-1 → the product is e(A, B)^-2, not one
            let mut proof = f.proof;
            proof.a.y = negated(proof.a.y);
            assert!(!accepts(&pvk, &proof, &f.inputs));
            assert_eq!(groth16::verify(&proof, &f.inputs), Err(Rejected), "{}", f.tx);

            // Mutation: B negated, still in G2; then C.
            let mut proof = f.proof;
            proof.b.y = [negated(proof.b.y[0]), negated(proof.b.y[1])];
            assert!(!accepts(&pvk, &proof, &f.inputs));
            assert_eq!(groth16::verify(&proof, &f.inputs), Err(Rejected), "{}", f.tx);
            let mut proof = f.proof;
            proof.c.y = negated(proof.c.y);
            assert_eq!(groth16::verify(&proof, &f.inputs), Err(Rejected), "{}", f.tx);

            // Mutation: the low bit of each public input in turn.
            //
            //     L moves by IC[i + 1] → e(L, -gamma) changes
            for i in 0..N_INPUTS {
                let mut inputs = f.inputs;
                inputs[i][0] ^= 1;
                assert!(!accepts(&pvk, &f.proof, &inputs));
                assert_eq!(groth16::verify(&f.proof, &inputs), Err(Rejected), "{}: input {i}", f.tx);
            }
        }
    }

    #[test]
    fn malformed_points_and_inputs_are_refused() {
        let f = &fixtures()[0];
        let refused = |proof: &Proof, inputs: &Inputs| groth16::verify(proof, inputs).unwrap_err();

        // A's x plus p: the same point mod p, but not canonical.
        let mut proof = f.proof;
        let mut carry = 0;
        for (x, p) in proof.a.x.iter_mut().zip(Fq::MODULUS.0) {
            let sum = u128::from(*x) + u128::from(p) + carry;
            (*x, carry) = (sum as u64, sum >> 64);
        }
        assert_eq!(refused(&proof, &f.inputs), NotInField);

        // The point at infinity, as EIP-197 writes it, and points off their curves.
        let mut proof = f.proof;
        proof.c = G1Point { x: [0; 4], y: [0; 4] };
        assert_eq!(refused(&proof, &f.inputs), NotOnCurve);
        let mut proof = f.proof;
        proof.c.y[0] ^= 1;
        assert_eq!(refused(&proof, &f.inputs), NotOnCurve);
        let mut proof = f.proof;
        proof.b.x[1][0] ^= 1;
        assert_eq!(refused(&proof, &f.inputs), NotOnCurve);

        // B on the twist, outside G2: the first such x of the form k.
        let outside = (1..)
            .find_map(|k| {
                G2Affine::get_point_from_x_unchecked(Fq2::from(k), false)
                    .filter(|q| !q.is_in_correct_subgroup_assuming_on_curve())
            })
            .expect("a twist point outside G2");
        let (x, y) = outside.xy().expect("not infinity");
        let mut proof = f.proof;
        proof.b = G2Point {
            x: [limbs(x.c0), limbs(x.c1)],
            y: [limbs(y.c0), limbs(y.c1)],
        };
        assert_eq!(refused(&proof, &f.inputs), NotInSubgroup);

        // An input equal to r, which reduces to zero.
        let mut inputs = f.inputs;
        inputs[3] = Fr::MODULUS.0;
        assert_eq!(refused(&f.proof, &inputs), InputNotInField);
    }

    /// Words as their little-endian bytes.
    fn bytes(words: &[u64]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], Trap> {
        let program = Program::from_elf(ELF).expect("the guest's ELF file");
        Machine::new(program.rv(), &run.advice).run()
    }

    #[test]
    fn the_guest_accepts_the_chains_proofs_and_outputs_their_inputs() {
        // Invariant: the output is BLAKE2s-256 of the inputs, proof after proof.
        let fixtures = fixtures();
        let run = batch(fixtures.len());
        let inputs: Vec<u64> = fixtures.iter().flat_map(|f| f.inputs.as_flattened().to_vec()).collect();
        assert_eq!(run.expected, digest_words(&hash(&bytes(&inputs))));
        assert_eq!(on_the_vm(&run), Ok(run.expected));

        // Mutation: the last input's low bit.
        //
        //     the pairing check fails → the guest panics → an illegal instruction → no output
        let mut tampered = batch(1);
        *tampered.advice.last_mut().unwrap() ^= 1;
        assert!(on_the_vm(&tampered).is_err());

        // Mutation: A's y negated.
        let mut tampered = batch(1);
        let y = 1 + 4;
        let a_y: [u64; 4] = tampered.advice[y..y + 4].try_into().unwrap();
        tampered.advice[y..y + 4].copy_from_slice(&negated(a_y));
        assert!(on_the_vm(&tampered).is_err());
    }
}
