//! The digest of a signer set: the signature claims an aggregate publishes.
//!
//! A claim is a scheme, a leaf index (XMSS only, zero for SPHINCS), a message and a key. A set is written as
//! groups of claims sharing their scheme, leaf index and message, each group one header block then its keys two
//! to a block, and the digest is a chain of BLAKE2s compressions over those blocks, one an item:
//!
//! ```text
//! header   scheme, leaf_index, message[0..4], 0, 0     t = START?
//! keys     key_a[0..4], key_b[0..4] (zeros if absent)  t = START? | KEY | PAIR if key_b is a key
//! end      TAG, 0, 0, 0, 0, 0, 0, 0                    t = START? | END, the last block
//! ```
//!
//! The chain starts from the parameter IV, each item compressing its block onto the previous item's output with
//! the counter `t` above, and the digest is the end item's output; `START` marks the first item, and the empty set
//! is the end item alone.
//!
//! So each item says what it is: the counter is part of every compression's input, and a parse of the blocks is
//! fixed by their counters. That is what lets a recursion circuit read a set of any shape in a fixed number of rows.
//!
//! The order of groups and keys is the writer's; only a root's verifier asks for the canonical one.

use crate::blake2s::{IV, compress};

/// The XMSS scheme's word in a header.
pub const XMSS: u64 = 1;
/// The SPHINCS scheme's word in a header.
pub const SPHINCS: u64 = 2;

/// The counter bit of a set's first item.
pub const START: u64 = 1;
/// The counter bit of a block of keys.
pub const KEY: u64 = 2;
/// The counter bit of the end item.
pub const END: u64 = 4;
/// The counter bit of a block of keys whose second key is one.
pub const PAIR: u64 = 8;

/// The end item's first word.
pub const TAG: u64 = u64::from_le_bytes(*b"signers1");

/// A signer set's digest, written one group and one key at a time.
pub struct SignerStream {
    /// The output of the last item compressed.
    h: [u64; 4],
    /// Whether no item has been compressed yet.
    first: bool,
    /// Whether a group is open, so keys can follow.
    open: bool,
    /// A block's first key, waiting for its second.
    pending: Option<[u64; 4]>,
}

impl Default for SignerStream {
    fn default() -> Self {
        Self::new()
    }
}

impl SignerStream {
    /// The stream of the empty set.
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            h: IV,
            first: true,
            open: false,
            pending: None,
        }
    }

    /// Compress one item.
    #[inline(always)]
    fn item(&mut self, m: &[u64; 8], code: u64, last: bool) {
        let t = code | if self.first { START } else { 0 };
        self.h = compress(&self.h, m, t, last);
        self.first = false;
    }

    /// Write the block of keys waiting for its second key, if any.
    #[inline(always)]
    fn flush(&mut self) {
        if let Some(a) = self.pending.take() {
            self.item(&[a[0], a[1], a[2], a[3], 0, 0, 0, 0], KEY, false);
        }
    }

    /// Open a group: the keys that follow signed `message` under `scheme`, at `leaf_index`.
    #[inline(always)]
    pub fn group(&mut self, scheme: u64, leaf_index: u64, message: &[u64; 4]) {
        self.flush();
        let [m0, m1, m2, m3] = *message;
        self.item(&[scheme, leaf_index, m0, m1, m2, m3, 0, 0], 0, false);
        self.open = true;
    }

    /// Add a key to the open group.
    ///
    /// # Panics
    ///
    /// Panics if no group is open.
    #[inline(always)]
    pub fn key(&mut self, key: &[u64; 4]) {
        assert!(self.open, "a key belongs to a group");
        match self.pending.take() {
            None => self.pending = Some(*key),
            Some(a) => self.item(
                &[a[0], a[1], a[2], a[3], key[0], key[1], key[2], key[3]],
                KEY | PAIR,
                false,
            ),
        }
    }

    /// The set's digest.
    #[inline(always)]
    pub fn finish(mut self) -> [u64; 4] {
        self.flush();
        self.item(&[TAG, 0, 0, 0, 0, 0, 0, 0], END, true);
        self.h
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The chain written out item by item.
    fn chain(items: &[([u64; 8], u64)]) -> [u64; 4] {
        let last = items.len() - 1;
        (items.iter().enumerate()).fold(IV, |h, (i, (m, code))| {
            compress(&h, m, code | if i == 0 { START } else { 0 }, i == last)
        })
    }

    #[test]
    fn the_stream_is_the_chain_of_its_items() {
        let end = ([TAG, 0, 0, 0, 0, 0, 0, 0], END);
        assert_eq!(SignerStream::new().finish(), chain(&[end]));

        let (msg, k1, k2, k3) = ([5, 6, 7, 8], [11, 12, 13, 14], [21, 22, 23, 24], [31, 32, 33, 34]);
        let mut s = SignerStream::new();
        s.group(XMSS, 9, &msg);
        s.key(&k1);
        s.key(&k2);
        s.key(&k3);
        s.group(SPHINCS, 0, &msg);
        let items = [
            ([XMSS, 9, 5, 6, 7, 8, 0, 0], 0),
            ([11, 12, 13, 14, 21, 22, 23, 24], KEY | PAIR),
            ([31, 32, 33, 34, 0, 0, 0, 0], KEY),
            ([SPHINCS, 0, 5, 6, 7, 8, 0, 0], 0),
            end,
        ];
        assert_eq!(s.finish(), chain(&items));
    }

    #[test]
    #[should_panic(expected = "a key belongs to a group")]
    fn a_key_needs_a_group() {
        SignerStream::new().key(&[1, 2, 3, 4]);
    }
}
