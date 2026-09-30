//! Verify the leanXMSS signatures the advice holds: their count, then for each a public
//! key, a leaf index, a message and a signature.
//!
//! Each claim (key, leaf index, message) is committed, so the output is the digest of the
//! claims.
//!
//! A bad signature leaves the run without a proof.
#![no_std]
#![no_main]

use leanvm_guest::{Words, commit, read, read_slice};
use leanxmss::{LeafIndex, Message, PublicKey, Signature};

leanvm_guest::advice_words!(1 << 16);

/// One signature as the advice lays it out: the claim, then the signature.
#[repr(C)]
struct Entry {
    public_key: PublicKey,
    leaf_index: u64,
    message: Message,
    signature: Signature,
}

/// The claim's words: the key, the leaf index and the message.
const CLAIM_WORDS: usize = (size_of::<PublicKey>() + size_of::<u64>() + size_of::<Message>()) / 8;

// SAFETY: every field is `repr(C)` words with no padding, and any words are one (see their definitions).
unsafe impl Words for Entry {}

impl Entry {
    /// The claim, the entry's first words, in place.
    fn claim(&self) -> &[u64; CLAIM_WORDS] {
        // SAFETY: `repr(C)`, so the key, the leaf index and the message are the first words, back to back.
        unsafe { &*(self as *const Self).cast() }
    }
}

#[unsafe(no_mangle)]
extern "C" fn main() {
    let n = *read::<u64>();
    // Read in place, all at once: one bounds check for the whole batch.
    for entry in read_slice::<Entry>(usize::try_from(n).expect("a count that fits")) {
        // A leaf index past `2^32 - 1` would be committed whole but verified truncated.
        let leaf = LeafIndex::try_from(entry.leaf_index).expect("a leaf index below 2^32");
        leanxmss::verify(&entry.public_key, leaf, &entry.message, &entry.signature).expect("every signature verifies");
        commit(entry.claim());
    }
}
