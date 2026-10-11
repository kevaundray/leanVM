//! The leansigners program off the VM: it signs under both schemes, lays the signatures out as the guest's advice
//! (the leanxmss guest's, then the leansphincs guest's), and builds the one signer set the guest proves, whose
//! digest gives its output.
//!
//! Signer `i` has a key of each scheme, both from `i`'s seed: so one signer index may sign under both, as two keys.

use core::ops::Range;
use leanvm::{SignerSet, SphincsClaim, XmssGroup};
use leanvm_guest::{PublicValues, Run, as_words_unchecked};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../leansigners.elf");

/// A signer's secret seed: its index, then zeros.
fn seed(i: usize) -> [u8; 32] {
    let mut seed = [0; 32];
    seed[..8].copy_from_slice(&(i as u64).to_le_bytes());
    seed
}

/// Signers that sign one message at one leaf index with leanXMSS.
///
/// Signer `i` signs at a leaf index with its key for that leaf index, from `i`'s seed: so a signer in two groups at
/// one leaf index is one key, and at two leaf indices is two keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Xmss {
    /// The leaf index.
    pub leaf_index: leanxmss::LeafIndex,
    /// The message.
    pub message: leanxmss::Message,
    /// The signers, by index.
    pub signers: Range<usize>,
}

/// Signers that sign one message with leanSPHINCS. Signer `i`'s key is the one from `i`'s seed, in every group.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sphincs {
    /// The message.
    pub message: leansphincs::Message,
    /// The signers, by index.
    pub signers: Range<usize>,
}

/// Signatures as the guest reads them, and the signer set it proves.
#[derive(Clone, Debug)]
pub struct Batch {
    /// The guest's advice, and the output it must give: the BLAKE2s of `set`'s digest, the one value it commits.
    pub run: Run,
    /// The claims the guest verifies: one XMSS group per [`Xmss`] group, then each [`Sphincs`] group's signers
    /// under its message, in their order (not canonical).
    pub set: SignerSet,
}

/// Each XMSS group's signers sign its message at its leaf index, and each SPHINCS group's signers sign its message.
pub fn batch(xmss: &[Xmss], sphincs: &[Sphincs]) -> Batch {
    // What the guest reads: the XMSS groups, then the SPHINCS groups, each scheme's as its own guest reads them.
    let mut advice = Vec::new();
    let mut set = SignerSet::new();
    xmss_groups(xmss, &mut advice, &mut set);
    sphincs_groups(sphincs, &mut advice, &mut set);
    // What it commits: the set's digest.
    let mut public = PublicValues::new();
    public.commit(&set.digest());
    Batch {
        run: Run {
            advice,
            expected: public.digest(),
        },
        set,
    }
}

/// Sign the XMSS groups, and write them as the guest reads them: the number of groups, then for each its leaf index,
/// message and count, then each key and signature.
fn xmss_groups(groups: &[Xmss], advice: &mut Vec<u64>, set: &mut SignerSet) {
    // Every group's signers, one after the other; their keys and signatures are independent, so made in parallel.
    let jobs: Vec<(&Xmss, usize)> = (groups.iter())
        .flat_map(|g| g.signers.clone().map(move |i| (g, i)))
        .collect();
    let signed = parallel::map_collect(jobs.len(), |j| {
        let (g, i) = jobs[j];
        let (sk, pk) = leanxmss::key_gen(seed(i), g.leaf_index);
        (pk, sk.sign(&g.message).expect("a valid encoding"))
    });
    let mut signed = signed.iter();
    advice.push(groups.len() as u64);
    for g in groups {
        advice.push(g.leaf_index.into());
        advice.extend(g.message);
        advice.push(g.signers.len() as u64);
        let mut keys = Vec::with_capacity(g.signers.len());
        for (pk, signature) in signed.by_ref().take(g.signers.len()) {
            leanxmss::verify(pk, g.leaf_index, &g.message, signature).expect("honest signatures verify");
            // SAFETY: `repr(C)` words, with no padding (see their definitions).
            advice.extend(unsafe { as_words_unchecked(pk) });
            advice.extend(unsafe { as_words_unchecked(signature) });
            let [r0, r1] = pk.merkle_root;
            let [p0, p1] = pk.public_param;
            keys.push([r0, r1, p0, p1]);
        }
        set.xmss.push(XmssGroup {
            leaf_index: g.leaf_index,
            message: g.message,
            keys,
        });
    }
}

/// Sign the SPHINCS groups, and write them as the guest reads them: the number of groups, then for each its message
/// and count, then each key and signature.
fn sphincs_groups(groups: &[Sphincs], advice: &mut Vec<u64>, set: &mut SignerSet) {
    // As for XMSS: made in parallel.
    let jobs: Vec<(&Sphincs, usize)> = (groups.iter())
        .flat_map(|g| g.signers.clone().map(move |i| (g, i)))
        .collect();
    let signed = parallel::map_collect(jobs.len(), |j| {
        let (g, i) = jobs[j];
        let (sk, pk) = leansphincs::key_gen(seed(i));
        (pk, sk.sign(&g.message).expect("an admissible digest and encodings"))
    });
    let mut signed = signed.iter();
    advice.push(groups.len() as u64);
    for g in groups {
        advice.extend(g.message);
        advice.push(g.signers.len() as u64);
        for (pk, signature) in signed.by_ref().take(g.signers.len()) {
            leansphincs::verify(pk, &g.message, signature).expect("honest signatures verify");
            // SAFETY: `repr(C)` words, with no padding (see their definitions).
            advice.extend(unsafe { as_words_unchecked(pk) });
            advice.extend(unsafe { as_words_unchecked(signature) });
            let [r0, r1] = pk.root;
            let [p0, p1] = pk.public_param;
            set.sphincs.push(SphincsClaim {
                key: [r0, r1, p0, p1],
                message: g.message,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanvm::aggregate::{Leaf, LeafShape, SignerLeaf, Tree, TreeError, TreeShape};
    use leanvm::{Capacity, Claim, Machine, Program, Prover, Rate, Scheme, Trap};

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], Trap> {
        let program = Program::from_elf(ELF).expect("the guest's ELF file");
        Machine::new(program.rv(), &run.advice).run()
    }

    /// The words of a key and of a signature in the advice, per scheme.
    const XMSS_ENTRY: usize = (size_of::<leanxmss::PublicKey>() + size_of::<leanxmss::Signature>()) / 8;
    const SPHINCS_ENTRY: usize = (size_of::<leansphincs::PublicKey>() + size_of::<leansphincs::Signature>()) / 8;

    /// Message `i`: the word `i`, then zeros.
    const fn message(i: u64) -> [u64; 4] {
        [i, 0, 0, 0]
    }

    const fn xmss(leaf_index: u32, message: [u64; 4], signers: Range<usize>) -> Xmss {
        Xmss {
            leaf_index,
            message,
            signers,
        }
    }

    const fn sphincs(message: [u64; 4], signers: Range<usize>) -> Sphincs {
        Sphincs { message, signers }
    }

    #[test]
    fn leansigners_outputs_the_digest_of_its_signer_set() {
        // Invariant: the guest commits one value, the digest of the signer set the host builds, whatever the schemes
        // and the advice's grouping.
        let outputs = |batch: &Batch| {
            let mut public = PublicValues::new();
            public.commit(&batch.set.digest());
            assert_eq!(batch.run.expected, public.digest(), "natively");
            assert_eq!(on_the_vm(&batch.run), Ok(batch.run.expected), "on the VM");
        };

        // Neither scheme, one scheme alone.
        let empty = batch(&[], &[]);
        assert_eq!(empty.set, SignerSet::new());
        assert_eq!(empty.run.advice, [0, 0]);
        outputs(&empty);
        outputs(&batch(&[xmss(1234, message(1), 0..3)], &[]));
        outputs(&batch(&[], &[sphincs(message(1), 0..3)]));

        // Both, with an empty group of each, and SPHINCS groups of one message split around an empty group of
        // another: one run in the digest.
        let mixed = batch(
            &[
                xmss(1234, message(1), 0..2),
                xmss(7, message(2), 0..0),
                xmss(7, message(1), 1..2),
            ],
            &[
                sphincs(message(1), 0..1),
                sphincs(message(2), 0..0),
                sphincs(message(1), 1..2),
                sphincs(message(3), 0..1),
            ],
        );
        assert_eq!(
            mixed.run.advice.len(),
            1 + 3 * 6 + 3 * XMSS_ENTRY + 1 + 4 * 5 + 3 * SPHINCS_ENTRY
        );
        assert_eq!((mixed.set.xmss.len(), mixed.set.sphincs.len()), (3, 3));
        outputs(&mixed);

        // Signer 0 under both schemes, at one message: two keys, two claims.
        let set = &mixed.set;
        assert_ne!(set.xmss[0].keys[0], set.sphincs[0].key);
        assert_eq!(
            SignerSet::from_claims(set.claims()).n_claims(),
            set.n_claims(),
            "no claim repeats"
        );
    }

    #[test]
    fn a_bad_signature_of_either_scheme_traps() {
        let batch = batch(&[xmss(1234, message(1), 0..2)], &[sphincs(message(1), 0..2)]);
        assert_eq!(on_the_vm(&batch.run), Ok(batch.run.expected));
        let forged = |at: usize, change: u64| {
            let mut run = batch.run.clone();
            run.advice[at] ^= change;
            on_the_vm(&run)
        };
        // Where the SPHINCS groups start: after the XMSS count, its group's header and 2 entries.
        let sphincs = 1 + 6 + 2 * XMSS_ENTRY;

        // Mutation: the last word of the first XMSS signature, then of the last SPHINCS signature.
        //
        //     the guest's check fails → it panics → an illegal instruction → no output
        assert!(forged(1 + 6 + XMSS_ENTRY - 1, 1 << 63).is_err());
        assert!(forged(batch.run.advice.len() - 1, 1 << 63).is_err());

        // Mutation: each scheme's message.
        //
        //     its signatures were made under another message → they fail
        assert!(forged(2, 1).is_err());
        assert!(forged(sphincs + 1, 1).is_err());

        // Mutation: the XMSS leaf index with bit 32 set.
        //
        //     claimed leaf index   2^32 + 1234
        //     truncated            1234, which verifies
        //     → the guest refuses the word rather than verify at another leaf index than it publishes
        assert!(forged(1, 1 << 32).is_err());
    }

    /// The least the leaves' union fits: six claims, in an XMSS group and a run of SPHINCS claims.
    const CAPACITY: Capacity = Capacity { claims: 7, groups: 2 };

    #[test]
    fn a_mixed_signer_set_tree_aggregates_both_schemes() {
        // Fixture state: two leaves, one mostly XMSS and one mostly SPHINCS, which overlap on claims of each scheme.
        // Their sizes are ones whose runs fill the same table heights.
        let m = message(1);
        let batches = [
            batch(&[xmss(1234, m, 0..3)], &[sphincs(m, 0..2)]),
            batch(&[xmss(1234, m, 2..3)], &[sphincs(m, 0..3)]),
        ];
        let program = Program::from_elf(ELF).expect("the guest's ELF file");
        let prover = Prover::new(Rate::MIN);

        // One tree takes both leaves: their runs fill the same table heights.
        let shapes = batches.each_ref().map(|b| {
            let stats = program.measure(&b.run.advice).expect("an honest run");
            LeafShape::measured(&stats, Rate::MIN)
        });
        assert_eq!(shapes[0], shapes[1], "one leaf shape");
        let runs = batches.each_ref().map(|b| {
            let run = prover.prove(&program, &b.run.advice).expect("an honest run");
            assert_eq!(*run.output.words(), b.run.expected);
            run
        });
        let leaf = LeafShape::of(&runs[0].proof).expect("a canonical announcement");
        assert_eq!(leaf, shapes[0]);
        let tree = Tree::new(
            &program,
            TreeShape {
                leaf,
                arity_0: 1,
                arity: 2,
                rate: Rate::MIN,
                signers: Some(CAPACITY),
            },
        )
        .expect("a tree");

        let firsts = [0, 1].map(|i| {
            let leaf = SignerLeaf::new(Leaf::new(&runs[i].proof, runs[i].output), &batches[i].set);
            tree.aggregate_leaves(&[leaf], None).expect("an honest leaf")
        });
        let root = tree
            .aggregate(&[&firsts[0], &firsts[1]], None)
            .expect("honest children");

        // The root states the canonical union: each scheme's claims, the overlap once.
        let union = SignerSet::from_claims(batches.iter().flat_map(|b| b.set.claims()));
        assert_eq!(root.signers, union);
        assert_eq!(
            (union.xmss.len(), union.xmss[0].keys.len(), union.sphincs.len()),
            (1, 3, 3)
        );
        assert_eq!(
            union.n_claims() + 3,
            batches[0].set.n_claims() + batches[1].set.n_claims()
        );
        tree.verify_signers(&root.proof, &union).expect("the root");

        // A declared part of it, one claim of each scheme, each from another leaf.
        let xmss_key = batches[0].set.xmss[0].keys[0];
        let xmss_claim = Claim {
            scheme: Scheme::Xmss,
            leaf_index: 1234,
            message: m,
            key: xmss_key,
        };
        let sphincs_claim = Claim {
            scheme: Scheme::Sphincs,
            leaf_index: 0,
            message: m,
            key: batches[1].set.sphincs[2].key,
        };
        let part = SignerSet::from_claims([xmss_claim, sphincs_claim]);
        let narrowed = tree.aggregate(&[&root], Some(&part)).expect("a covered declaration");
        assert_eq!(narrowed.signers, part);
        tree.verify_signers(&narrowed.proof, &part).expect("a narrowed root");

        // Mutation: an XMSS claim declared as SPHINCS, of the same key and message.
        //
        //     no SPHINCS claim of the children has that key → the declaration is refused
        let claim = Claim {
            scheme: Scheme::Sphincs,
            leaf_index: 0,
            message: m,
            key: xmss_key,
        };
        assert_eq!(
            tree.aggregate(&[&root], Some(&SignerSet::from_claims([claim]))),
            Err(TreeError::NotCovered(claim))
        );
    }
}
