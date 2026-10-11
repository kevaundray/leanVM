//! Verify the leanXMSS and leanSPHINCS signatures the advice holds: the leanxmss guest's advice, then the
//! leansphincs guest's.
//!
//! - XMSS: the number of groups, then for each a leaf index, a message, a count, and that many public keys and
//!   signatures.
//! - SPHINCS: the number of groups, then for each a message, a count, and that many public keys and signatures.
//!
//! Each signature is verified with its scheme's library, and the one signer set they form (`leansigners`: one XMSS
//! group per advice group, then the SPHINCS claims, all in the advice's order) is digested as they are read; that
//! digest is the one value committed.
//!
//! A set writes its SPHINCS claims as runs of one message, so a SPHINCS group opens a run only if it has a
//! signature and its message is not the open run's: the digest is the set's whatever the advice's grouping.
//!
//! One signer may sign under both schemes, with a key of each: a key is a claim only under its own scheme's label.
//!
//! A bad signature leaves the run without a proof.
#![no_std]
#![no_main]

use leansigners::Stream;
use leanvm_guest::{commit, read, read_unchecked};

leanvm_guest::advice_words!(1 << 16);

#[unsafe(no_mangle)]
extern "C" fn main() {
    let mut signers = Stream::new();
    xmss(&mut signers);
    sphincs(&mut signers);
    commit(&signers.finish());
}

/// Read and verify the XMSS groups, as the leanxmss guest does.
#[inline(always)]
fn xmss(signers: &mut Stream) {
    use leanxmss::signers::{key_words, label};
    use leanxmss::{LeafIndex, Message, PublicKey, Signature};
    let n_groups = *read::<u64>();
    for _ in 0..n_groups {
        let leaf_index = *read::<u64>();
        // A leaf index past `2^32 - 1` would be published whole but verified truncated.
        let leaf = LeafIndex::try_from(leaf_index).expect("a leaf index below 2^32");
        let message = read::<Message>();
        signers.group(&label(leaf, message));
        let n = *read::<u64>();
        for _ in 0..n {
            // Read in place. SAFETY: both types are `repr(C)` words, with no padding, and any
            // words are one (see their definitions).
            let public_key = unsafe { read_unchecked::<PublicKey>() };
            let signature = unsafe { read_unchecked::<Signature>() };

            leanxmss::verify(public_key, leaf, message, signature).expect("every signature verifies");

            signers.key(&key_words(public_key));
        }
    }
}

/// Read and verify the SPHINCS groups, as the leansphincs guest does.
#[inline(always)]
fn sphincs(signers: &mut Stream) {
    use leansphincs::signers::{key_words, label};
    use leansphincs::{Message, PublicKey, Signature};
    // The message of the open run, if any.
    let mut open: Option<&Message> = None;
    let n_groups = *read::<u64>();
    for _ in 0..n_groups {
        let message = read::<Message>();
        let n = *read::<u64>();
        if n != 0 && open != Some(message) {
            signers.group(&label(message));
            open = Some(message);
        }
        for _ in 0..n {
            // Read in place. SAFETY: both types are `repr(C)` words, with no padding, and any
            // words are one (see their definitions).
            let public_key = unsafe { read_unchecked::<PublicKey>() };
            let signature = unsafe { read_unchecked::<Signature>() };

            leansphincs::verify(public_key, message, signature).expect("every signature verifies");

            signers.key(&key_words(public_key));
        }
    }
}
