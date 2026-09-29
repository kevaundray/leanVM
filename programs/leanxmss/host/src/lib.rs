//! The leanXMSS program off the VM: it signs, lays the signatures out as the guest's
//! advice, and runs the guest's own library natively for the output the guest must give.
//!
//! One message at one leaf index for all signers is the Ethereum shape: validators attest to one block.

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../leanxmss.elf");

/// What one run of the guest is given, and what it must output.
pub struct Run {
    pub input: [u64; 4],
    pub advice: Vec<u64>,
    pub expected: [u64; 4],
}

/// The message every signer signs.
const MESSAGE: [u64; 4] = [0x4242_4242_4242_4242; 4];
/// The leaf index every signer signs at.
const LEAF_INDEX: u32 = 1234;

/// A signer's secret seed: its index, then zeros.
fn seed(i: usize) -> [u8; 32] {
    let mut seed = [0; 32];
    seed[..8].copy_from_slice(&(i as u64).to_le_bytes());
    seed
}

/// `n` signers, each with its own key, sign the message.
pub fn batch(n: usize) -> Run {
    // Keys and signatures are independent, so they are made in parallel.
    let entries = parallel::map_collect(n, |i| {
        let (sk, pk) = leanxmss::key_gen(seed(i), LEAF_INDEX);
        leanxmss::Entry::new(pk, LEAF_INDEX, MESSAGE, sk.sign(&MESSAGE).expect("a valid encoding"))
    });
    Run {
        input: [n as u64, 0, 0, 0],
        advice: entries.iter().flat_map(|e| e.as_words()).copied().collect(),
        // The native run of the guest's own code is the reference output.
        expected: leanxmss::verify_batch(&entries).expect("honest signatures verify"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(bytes: impl IntoIterator<Item = u8>) -> String {
        bytes.into_iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Words as their little-endian bytes.
    fn bytes(words: &[u64]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    /// The seed `0, 1, .., 31` and the message `7, 10, 13, ..` the known answers were made with.
    fn fixed() -> ([u8; 32], [u64; 4]) {
        let message: [u8; 32] = std::array::from_fn(|i| (i * 3 + 7) as u8);
        (
            std::array::from_fn(|i| i as u8),
            std::array::from_fn(|i| u64::from_le_bytes(message[8 * i..8 * i + 8].try_into().unwrap())),
        )
    }

    #[test]
    fn leanxmss_is_the_specified_scheme() {
        // Known answers of the XMSS specification's implementation, at the edges of the leaf indices.
        //
        // Each: the leaf index, the public key's bytes, the BLAKE2s digest of the signature's bytes.
        let (seed, message) = fixed();
        let known = [
            (
                0,
                "40b9356800f80f5952f617427ab29fd6c487ed3aef7201c095bf4c74aad6b6e3",
                "02ceeee5d838dcb47290e7c7d0ce8485df70c070bf97ac6bf06d294c5e9a3d61",
            ),
            (
                1234,
                "57c45784ed52b81893def5b5e3ef0aedc487ed3aef7201c095bf4c74aad6b6e3",
                "304b4e5fbb27dec445245843c7919907b3ea8c5b3f39397cd9483f47171a31e6",
            ),
            (
                u32::MAX,
                "4a66306093cfbc702910ce5dd02071e9c487ed3aef7201c095bf4c74aad6b6e3",
                "c06f727fd8bbaa02bc641f8d9382e2d69b9ad4f3e5022d4fa140c53d60a1e5d2",
            ),
        ];
        for (leaf_index, pk_hex, sig_digest) in known {
            let (sk, pk) = leanxmss::key_gen(seed, leaf_index);
            let entry = leanxmss::Entry::new(pk, leaf_index, message, sk.sign(&message).unwrap());
            // An entry's words are its bytes:
            //
            //     words 0..4   public key
            //     words 4..9   leaf index, message
            //     words 9..    signature
            assert_eq!(hex(bytes(&entry.as_words()[..4])), pk_hex, "leaf index {leaf_index}");
            assert_eq!(
                hex(primitives::hash::hash(&bytes(&entry.as_words()[9..]))),
                sig_digest,
                "leaf index {leaf_index}"
            );
            assert_eq!(leanxmss::verify(&pk, leaf_index, &message, &entry.signature), Ok(()));
        }
    }

    #[test]
    fn leanxmss_rejects_a_change_anywhere() {
        use leanxmss::VerifyError::{InvalidEncoding, InvalidMerklePath, LeafIndexOutOfRange};
        // Invariant: a verifier binds the claim and every part of the signature.
        //
        // Fixture state: one honest signature at leaf index 7.
        let (seed, message) = fixed();
        let (sk, pk) = leanxmss::key_gen(seed, 7);
        let signature = sk.sign(&message).unwrap();
        let verify = |pk: &leanxmss::PublicKey, leaf_index, message: &[u64; 4], signature: &leanxmss::Signature| {
            leanxmss::verify(pk, leaf_index, message, signature).err()
        };

        // Mutation: the message, the leaf index, the randomness.
        //
        //     all three enter the encoding digest
        //     → a new digest, valid with probability about 2^-15
        let mut other = message;
        other[0] ^= 1;
        assert_eq!(verify(&pk, 7, &other, &signature), Some(InvalidEncoding));
        assert_eq!(verify(&pk, 8, &message, &signature), Some(InvalidEncoding));
        let mut bad = signature.clone();
        bad.randomness[0] ^= 1;
        assert_eq!(verify(&pk, 7, &message, &bad), Some(InvalidEncoding));

        // Mutation: the last chain tip's top bit, the last path node, the root.
        //
        //     the encoding still holds
        //     → a different leaf or fold, which misses the root
        let mut bad = signature.clone();
        bad.chain_tips[41][1] ^= 1 << 63;
        assert_eq!(verify(&pk, 7, &message, &bad), Some(InvalidMerklePath));
        let mut bad = signature.clone();
        bad.merkle_proof[31][0] ^= 1;
        assert_eq!(verify(&pk, 7, &message, &bad), Some(InvalidMerklePath));
        let mut bad_pk = pk;
        bad_pk.merkle_root[0] ^= 1;
        assert_eq!(verify(&bad_pk, 7, &message, &signature), Some(InvalidMerklePath));

        // Mutation: an entry's leaf index word with bit 32 set.
        //
        //     claimed leaf index   2^32 + 7
        //     truncated            7
        //     → rejected rather than verified at another leaf index than claimed
        let mut entry = leanxmss::Entry::new(pk, 7, message, signature);
        entry.leaf_index |= 1 << 32;
        assert_eq!(leanxmss::verify_batch(&[entry]), Err((0, LeafIndexOutOfRange)));
    }

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], leanvm_core::rv::Trap> {
        let program = leanvm_core::cpu::Program::from_elf(ELF).expect("the guest's ELF file");
        leanvm_core::rv::Machine::new(&program.rv, run.input, &run.advice).run(1 << 30)
    }

    #[test]
    fn the_guest_checks_what_the_native_code_checks() {
        // The guest on the interpreter outputs what its code computes natively.
        let mut run = batch(3);
        assert_eq!(on_the_vm(&run), Ok(run.expected));

        // Mutation: the top bit of the advice's last word, a node of the last signature's path.
        //
        //     the guest's check fails → it panics → an illegal instruction → no output
        *run.advice.last_mut().unwrap() ^= 1 << 63;
        assert!(on_the_vm(&run).is_err());
    }
}
