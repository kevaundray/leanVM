//! The digest of a signer set of both leanXMSS and leanSPHINCS claims: the claims an aggregate of leansigners proofs
//! publishes.
//!
//! The format is the one both schemes write theirs in (`leanxmss::signers`, `leansphincs::signers`): groups of claims
//! sharing a label, each a header block then its keys two to a block, then an end block, chained by BLAKE2s
//! compressions from the parameter IV. A group's label is its scheme's: `[1, leaf_index, message]` for leanXMSS and
//! `[2, 0, message]` for leanSPHINCS, so one set holds both, and a key is a claim only under its own scheme's label.
//!
//! The order of groups and keys is the writer's.
#![no_std]

#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
use leanvm_guest::blake2s_compress;
#[cfg(all(target_arch = "riscv64", target_os = "none"))]
use leanvm_guest::precompile::blake2s_compress;
use leanxmss::signers::{END, IV, KEY, PAIR, START, TAG};

/// A signer set's digest, written one group and one key at a time.
pub struct Stream {
    /// The output of the last block compressed.
    h: [u64; 4],
    /// Whether no block has been compressed yet.
    first: bool,
    /// A block's first key, waiting for its second.
    pending: Option<[u64; 4]>,
}

impl Default for Stream {
    fn default() -> Self {
        Self::new()
    }
}

impl Stream {
    /// The stream of the empty set.
    #[inline(always)]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            h: IV,
            first: true,
            pending: None,
        }
    }

    /// Compress one block.
    #[inline(always)]
    fn block(&mut self, m: &[u64; 8], code: u64, last: bool) {
        let t = code | if self.first { START } else { 0 };
        self.h = blake2s_compress(&self.h, m, t, last);
        self.first = false;
    }

    /// Write the block of keys waiting for its second key, if any.
    #[inline(always)]
    fn flush(&mut self) {
        if let Some([a0, a1, a2, a3]) = self.pending.take() {
            self.block(&[a0, a1, a2, a3, 0, 0, 0, 0], KEY, false);
        }
    }

    /// Open a group: the keys that follow are claims under `label`.
    #[inline(always)]
    pub fn group(&mut self, label: &[u64; 6]) {
        self.flush();
        let [l0, l1, l2, l3, l4, l5] = *label;
        self.block(&[l0, l1, l2, l3, l4, l5, 0, 0], 0, false);
    }

    /// Add a key's words to the open group, which a group must have been opened for.
    #[inline(always)]
    pub fn key(&mut self, key: &[u64; 4]) {
        let [b0, b1, b2, b3] = *key;
        match self.pending.take() {
            None => self.pending = Some([b0, b1, b2, b3]),
            Some([a0, a1, a2, a3]) => self.block(&[a0, a1, a2, a3, b0, b1, b2, b3], KEY | PAIR, false),
        }
    }

    /// The set's digest.
    #[inline(always)]
    #[must_use]
    pub fn finish(mut self) -> [u64; 4] {
        self.flush();
        self.block(&[TAG, 0, 0, 0, 0, 0, 0, 0], END, true);
        self.h
    }
}
