use super::*;
use rec_aggregation::signers_cache::{KEY_START, XMSS_LEAF_INDEX_A, get_signers_at, message_for};

const RATE: usize = leanvm_core::pcs::TEST_LOG_INV_RATE;
const LEAF_B: LeafIndex = KEY_START + 3;

/// Signers `[from, to)` of the cache, each signing `message_for(leaf_index)` at `leaf_index`.
fn raw(from: usize, to: usize, leaf_index: LeafIndex) -> Vec<RawSignature> {
    get_signers_at(to, leaf_index)[from..]
        .iter()
        .map(|(pk, sig)| (pk.clone(), leaf_index, message_for(leaf_index), sig.clone()))
        .collect()
}

fn group(signatures: &[RawSignature]) -> XmssClaimGroup {
    let (_, leaf_index, message, _) = &signatures[0];
    let mut keys: Vec<XmssPublicKey> = signatures.iter().map(|(pk, ..)| pk.clone()).collect();
    keys.sort();
    keys.dedup();
    XmssClaimGroup {
        leaf_index: *leaf_index,
        message: *message,
        keys,
    }
}

fn leaf(signatures: Vec<RawSignature>) -> XmssAggregate {
    let aggregate = aggregate(vec![], signatures, None, RATE).expect("the leaf proves");
    aggregate.verify().expect("the leaf verifies");
    aggregate
}

fn assert_snark_rejects(signers: Vec<XmssClaimGroup>, children: Vec<XmssAggregate>, proof: &Proof) {
    let forged = XmssAggregate::new(signers, children, proof.clone());
    assert!(matches!(forged.verify(), Err(VerifyError::Snark(_))));
}

/// Hints for an honest node, before any test bends them.
fn honest(children: &[XmssAggregate], raw: &[RawSignature]) -> (Coverage, Hints) {
    let claims: Vec<_> = raw.iter().map(|(pk, i, m, _)| (pk.clone(), *i, *m)).collect();
    let cover = plan_coverage(&claims, children, None).unwrap();
    let hints = node_hints(&cover, raw, children).unwrap();
    (cover, hints)
}

#[test]
fn a_leaf_round_trips_and_publishes_the_signer_set_digest() {
    let a = raw(0, 3, XMSS_LEAF_INDEX_A);
    let b = raw(1, 3, LEAF_B);
    let leaf = leaf([a.clone(), b.clone()].concat());
    assert_eq!(leaf.signers(), [group(&b), group(&a)]);
    assert_eq!(leaf.statement(), signers_hash(leaf.signers()));
}

#[test]
fn a_tampered_signature_is_rejected() {
    let mut tip = raw(0, 2, XMSS_LEAF_INDEX_A);
    tip[1].3.wots_signature.chain_tips[7][0] ^= 1;
    let mut sibling = raw(0, 2, XMSS_LEAF_INDEX_A);
    sibling[0].3.merkle_proof[9][3] ^= 0x10;
    for signatures in [tip, sibling] {
        let result = aggregate(vec![], signatures, None, RATE);
        assert!(matches!(result, Err(AggregationError::ProofError(_))));
    }
}

/// The host refuses a signature under the wrong claim before the program runs, so these bend the
/// group the program verifies at: the honest witness, the published group moved to another leaf
/// index or message.
#[test]
fn a_wrong_message_or_leaf_index_is_rejected() {
    let signatures = raw(0, 2, XMSS_LEAF_INDEX_A);
    let wrong_index = XMSS_LEAF_INDEX_A ^ 4;
    let mut wrong_message = message_for(XMSS_LEAF_INDEX_A);
    wrong_message[31] ^= 1;
    for (leaf_index, message) in [
        (wrong_index, message_for(XMSS_LEAF_INDEX_A)),
        (XMSS_LEAF_INDEX_A, wrong_message),
    ] {
        let (cover, mut hints) = honest(&[], &signatures);
        let cells = &mut hints.0.get_mut("group").unwrap()[0];
        cells[0] = F192::new(u64::from(leaf_index), 0, 0);
        cells[1] = pack_16_bytes(&message[..16]);
        cells[2] = pack_16_bytes(&message[16..]);
        let mut signers = cover.groups;
        signers[0].leaf_index = leaf_index;
        signers[0].message = message;
        let result = prove_node(signers, vec![], hints, RATE);
        assert!(matches!(result, Err(AggregationError::ProofError(_))));
    }

    let leaf = leaf(signatures);
    let mut moved = leaf.signers().to_vec();
    moved[0].leaf_index = wrong_index;
    assert_snark_rejects(moved, vec![], leaf.proof());
    let mut moved = leaf.signers().to_vec();
    moved[0].message = wrong_message;
    assert_snark_rejects(moved, vec![], leaf.proof());
}

#[test]
fn a_signer_set_mismatch_is_rejected() {
    let leaf = leaf(raw(0, 4, XMSS_LEAF_INDEX_A));
    let honest = leaf.signers().to_vec();

    let mut dropped = honest.clone();
    dropped[0].keys.remove(2);
    assert_snark_rejects(dropped, vec![], leaf.proof());

    let mut replaced = honest.clone();
    replaced[0].keys[3] = raw(4, 5, XMSS_LEAF_INDEX_A)[0].0.clone();
    replaced[0].keys.sort();
    assert_snark_rejects(replaced, vec![], leaf.proof());

    let mut unsorted = honest;
    unsorted[0].keys.swap(0, 1);
    let forged = XmssAggregate::new(unsorted, vec![], leaf.proof().clone());
    assert_eq!(forged.verify(), Err(VerifyError::MalformedSignerSet));

    // A merge binds its children's sets: another valid child does not take one's place.
    let other = self::leaf(raw(4, 6, XMSS_LEAF_INDEX_A));
    let merged = aggregate(vec![leaf.clone()], vec![], None, RATE).unwrap();
    merged.verify().unwrap();
    assert_snark_rejects(merged.signers().to_vec(), vec![other], merged.proof());
}

#[test]
fn a_merge_publishes_the_union() {
    let left = leaf(raw(0, 4, XMSS_LEAF_INDEX_A));
    let right = leaf([raw(2, 6, XMSS_LEAF_INDEX_A), raw(0, 2, LEAF_B)].concat());
    let direct = raw(5, 7, LEAF_B);
    let merged = aggregate(vec![left, right], direct, None, RATE).unwrap();
    merged.verify().unwrap();
    assert_eq!(
        merged.signers(),
        [
            group(&[raw(0, 2, LEAF_B), raw(5, 7, LEAF_B)].concat()),
            group(&raw(0, 6, XMSS_LEAF_INDEX_A))
        ]
    );

    // Merges nest: the tree verifies proof by proof.
    let top = aggregate(
        vec![merged.clone(), leaf(raw(6, 8, XMSS_LEAF_INDEX_A))],
        vec![],
        None,
        RATE,
    )
    .unwrap();
    top.verify().unwrap();
    assert_eq!(top.signers()[1], group(&raw(0, 8, XMSS_LEAF_INDEX_A)));
    assert_eq!(top.proofs().len(), 5);
}

#[test]
fn a_declared_subset_is_accepted() {
    let left = leaf(raw(0, 4, XMSS_LEAF_INDEX_A));
    let right = leaf(raw(0, 3, LEAF_B));
    // Two of the left child's keys, and nothing of the right child's group.
    let declared = [group(&raw(1, 3, XMSS_LEAF_INDEX_A))];
    let merged = aggregate(vec![left, right], vec![], Some(&declared), RATE).unwrap();
    merged.verify().unwrap();
    assert_eq!(merged.signers(), declared);

    let subset = aggregate(vec![], raw(0, 5, XMSS_LEAF_INDEX_A), Some(&declared), RATE).unwrap();
    subset.verify().unwrap();
    assert_eq!(subset.signers(), declared);
}

#[test]
fn an_uncovered_claim_is_rejected() {
    let child = leaf(raw(0, 3, XMSS_LEAF_INDEX_A));
    let outsider = raw(3, 4, XMSS_LEAF_INDEX_A);
    let declared = [group(&[raw(0, 1, XMSS_LEAF_INDEX_A), outsider.clone()].concat())];
    let result = aggregate(vec![child.clone()], vec![], Some(&declared), RATE);
    assert!(matches!(result, Err(AggregationError::NotCovered)));

    // The program refuses a declared key no signature or child covers: the coverage count falls short.
    let (mut cover, _) = honest(std::slice::from_ref(&child), &[]);
    let extra = XmssPublicKey {
        merkle_root: [0xff; xmss::DIGEST_LEN],
        public_param: [0xff; xmss::PUBLIC_PARAM_LEN],
    };
    cover.groups[0].keys.push(extra);
    let hints = node_hints(&cover, &[], std::slice::from_ref(&child)).unwrap();
    let result = prove_node(cover.groups, vec![child.clone()], hints, RATE);
    assert!(matches!(result, Err(AggregationError::ProofError(_))));

    let merged = aggregate(vec![child.clone()], vec![], None, RATE).unwrap();
    let mut claimed = merged.signers().to_vec();
    claimed[0].keys.push(outsider[0].0.clone());
    claimed[0].keys.sort();
    assert_snark_rejects(claimed, vec![child], merged.proof());
}
