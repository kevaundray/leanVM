//! The leansigners program off the VM: it signs under both schemes as the leanxmss and leansphincs hosts do, lays
//! the signatures out as the guest's advice (the leanxmss guest's, then the leansphincs guest's), and builds the one
//! signer set the guest proves, whose digest gives its output.
//!
//! Signer `i` has a key of each scheme, both from `i`'s seed: so one signer index may sign under both, as two keys.
//!
//! It also owns the program's signer sets ([`SignerSet`]): the claims an aggregate of its proofs publishes.

use leanvm_guest::{PublicValues, Run};
use thiserror::Error;

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../leansigners.elf");

/// A set of leanXMSS and leanSPHINCS claims, as an aggregate publishes it: the XMSS groups, then the SPHINCS claims.
///
/// Its canonical form, which a root publishes, is both parts' canonical forms: the XMSS labels (scheme word 1) all
/// order before the SPHINCS ones (2), so that is also the canonical claim set of its labels and keys.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SignerSet {
    /// The leanXMSS claims.
    pub xmss: leanxmss_host::SignerSet,
    /// The leanSPHINCS claims.
    pub sphincs: leansphincs_host::SignerSet,
}

/// Why a set is not canonical: the part that is not.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum SignerSetError {
    /// The XMSS part.
    #[error("XMSS: {0}")]
    Xmss(#[from] leanxmss_host::SignerSetError),
    /// The SPHINCS part.
    #[error("SPHINCS: {0}")]
    Sphincs(#[from] leansphincs_host::SignerSetError),
}

impl SignerSet {
    /// The empty set.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            xmss: leanxmss_host::SignerSet::new(),
            sphincs: leansphincs_host::SignerSet::new(),
        }
    }

    /// The canonical set of both sets' claims.
    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        Self {
            xmss: self.xmss.union(&other.xmss),
            sphincs: self.sphincs.union(&other.sphincs),
        }
    }

    /// How many claims it holds, repeats included.
    #[must_use]
    pub fn n_claims(&self) -> usize {
        self.xmss.n_claims() + self.sphincs.claims.len()
    }

    /// Each group's label and its keys' words, in order: what a recursion circuit reads the set from.
    #[must_use]
    pub fn label_groups(&self) -> Vec<([u64; 6], Vec<[u64; 4]>)> {
        let mut groups = self.xmss.label_groups();
        groups.extend(self.sphincs.label_groups());
        groups
    }

    /// Its digest, as the guest computes it.
    #[must_use]
    pub fn digest(&self) -> [u64; 4] {
        let mut stream = leansigners::Stream::new();
        for (label, keys) in self.label_groups() {
            stream.group(&label);
            keys.iter().for_each(|k| stream.key(k));
        }
        stream.finish()
    }

    /// Check it is canonical: what a root's verifier asks of the set it publishes.
    ///
    /// # Errors
    ///
    /// The first rule a part breaks, the XMSS part first.
    pub fn check(&self) -> Result<(), SignerSetError> {
        self.xmss.check()?;
        self.sphincs.check()?;
        Ok(())
    }
}

/// Signatures as the guest reads them, and the signer set it proves.
#[derive(Clone, Debug)]
pub struct Batch {
    /// The guest's advice, and the output it must give: the BLAKE2s of `set`'s digest, the one value it commits.
    pub run: Run,
    /// The claims the guest verifies, each part in its groups' order (not canonical).
    pub set: SignerSet,
}

/// Each XMSS group's signers sign its message at its leaf index, and each SPHINCS group's signers sign its message.
pub fn batch(xmss: &[leanxmss_host::Group], sphincs: &[leansphincs_host::Group]) -> Batch {
    // Each scheme's advice is its own guest's, which the combined guest reads one after the other.
    let xmss = leanxmss_host::batch_groups(xmss);
    let sphincs = leansphincs_host::batch_groups(sphincs);
    let mut advice = xmss.run.advice;
    advice.extend(sphincs.run.advice);
    let set = SignerSet {
        xmss: xmss.set,
        sphincs: sphincs.set,
    };
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

#[cfg(test)]
mod tests {
    use super::*;
    use core::ops::Range;
    use leanvm::aggregate::{
        Capacity, Claim, ClaimGroup, ClaimLeaf, ClaimSet, Leaf, LeafShape, Tree, TreeError, TreeShape,
    };
    use leanvm::{Machine, Program, Prover, Rate, Trap};

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

    const fn xmss(leaf_index: u32, message: [u64; 4], signers: Range<usize>) -> leanxmss_host::Group {
        leanxmss_host::Group {
            leaf_index,
            message,
            signers,
        }
    }

    const fn sphincs(message: [u64; 4], signers: Range<usize>) -> leansphincs_host::Group {
        leansphincs_host::Group { message, signers }
    }

    /// The claim set a tree takes for a signer set.
    fn claim_set(set: &SignerSet) -> ClaimSet {
        ClaimSet {
            groups: (set.label_groups().into_iter())
                .map(|(label, members)| ClaimGroup { label, members })
                .collect(),
        }
    }

    #[test]
    fn leansigners_outputs_the_digest_of_its_signer_set() {
        // Invariant: the guest commits one value, the digest of the signer set the host builds, whatever the schemes
        // and the advice's grouping; it is the digest of the set's claim set.
        let outputs = |batch: &Batch| {
            let mut public = PublicValues::new();
            public.commit(&batch.set.digest());
            assert_eq!(batch.run.expected, public.digest(), "natively");
            assert_eq!(claim_set(&batch.set).digest(), batch.set.digest(), "as a claim set");
            assert_eq!(on_the_vm(&batch.run), Ok(batch.run.expected), "on the VM");
        };

        // Neither scheme.
        let empty = batch(&[], &[]);
        assert_eq!(empty.set, SignerSet::new());
        assert_eq!(empty.run.advice, [0, 0]);
        outputs(&empty);

        // One scheme alone: the digest and the output are that scheme's own program's.
        let groups = [xmss(1234, message(1), 0..3), xmss(7, message(2), 1..2)];
        let alone = batch(&groups, &[]);
        let theirs = leanxmss_host::batch_groups(&groups);
        assert_eq!(alone.set.digest(), theirs.set.digest());
        assert_eq!(alone.run.expected, theirs.run.expected);
        outputs(&alone);
        let groups = [
            sphincs(message(1), 0..2),
            sphincs(message(1), 2..3),
            sphincs(message(2), 0..1),
        ];
        let alone = batch(&[], &groups);
        let theirs = leansphincs_host::batch_groups(&groups);
        assert_eq!(alone.set.digest(), theirs.set.digest());
        assert_eq!(alone.run.expected, theirs.run.expected);
        outputs(&alone);

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
        assert_eq!((mixed.set.xmss.groups.len(), mixed.set.sphincs.claims.len()), (3, 3));
        assert_eq!(mixed.set.label_groups().len(), 3 + 2);
        outputs(&mixed);

        // Signer 0 under both schemes, at one message: two keys, two claims.
        let set = &mixed.set;
        assert_ne!(
            leanxmss::signers::key_words(&set.xmss.groups[0].keys[0]),
            leansphincs::signers::key_words(&set.sphincs.claims[0].key)
        );
        assert_eq!(
            ClaimSet::from_claims(claim_set(set).claims()).n_claims(),
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

    /// A claim-set tree of `capacity` over two leaves, one mostly XMSS and one mostly SPHINCS, which overlap on claims
    /// of each scheme.
    fn aggregates_mixed_sets(capacity: Capacity) {
        // Their sizes are ones whose runs fill the same table heights.
        let m = message(1);
        let batches = [
            batch(&[xmss(1234, m, 0..3)], &[sphincs(m, 0..2)]),
            batch(&[xmss(1234, m, 2..3)], &[sphincs(m, 0..3)]),
        ];
        let sets = batches.each_ref().map(|b| claim_set(&b.set));
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
                claims: Some(capacity),
            },
        )
        .expect("a tree");

        let firsts = [0, 1].map(|i| {
            let leaf = ClaimLeaf::new(Leaf::new(&runs[i].proof, runs[i].output), &sets[i]);
            tree.aggregate_leaves(&[leaf], None).expect("an honest leaf")
        });
        let root = tree
            .aggregate(&[&firsts[0], &firsts[1]], None)
            .expect("honest children");

        // The root states the canonical union, each scheme's claims and the overlap once: the host's union.
        let union = batches[0].set.union(&batches[1].set);
        assert_eq!(union.check(), Ok(()));
        assert_eq!(root.claims, claim_set(&union));
        assert_eq!(
            root.claims,
            ClaimSet::from_claims(sets.iter().flat_map(ClaimSet::claims))
        );
        assert_eq!(
            (
                union.xmss.groups.len(),
                union.xmss.n_claims(),
                union.sphincs.claims.len()
            ),
            (1, 3, 3)
        );
        assert_eq!(
            union.n_claims() + 3,
            batches[0].set.n_claims() + batches[1].set.n_claims()
        );
        tree.verify_claims(&root.proof, &root.claims).expect("the root");

        // A declared part of it, one claim of each scheme, each from another leaf.
        let xmss_key = leanxmss::signers::key_words(&batches[0].set.xmss.groups[0].keys[0]);
        let xmss_claim = Claim {
            label: leanxmss::signers::label(1234, &m),
            member: xmss_key,
        };
        let sphincs_claim = Claim {
            label: leansphincs::signers::label(&m),
            member: leansphincs::signers::key_words(&batches[1].set.sphincs.claims[2].key),
        };
        let part = ClaimSet::from_claims([xmss_claim, sphincs_claim]);
        let narrowed = tree.aggregate(&[&root], Some(&part)).expect("a covered declaration");
        assert_eq!(narrowed.claims, part);
        tree.verify_claims(&narrowed.proof, &part).expect("a narrowed root");

        // Mutation: an XMSS claim declared as SPHINCS, of the same key and message.
        //
        //     no SPHINCS claim of the children has that key → the declaration is refused
        let claim = Claim {
            label: leansphincs::signers::label(&m),
            member: xmss_key,
        };
        assert_eq!(
            tree.aggregate(&[&root], Some(&ClaimSet::from_claims([claim]))),
            Err(TreeError::NotCovered(claim))
        );
    }

    #[test]
    fn a_mixed_claim_set_tree_aggregates_both_schemes() {
        aggregates_mixed_sets(Capacity { claims: 7, groups: 2 });
    }
}
