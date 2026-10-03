//! The one-time signature: `v` hash chains, and the target-sum code that replaces
//! the Winternitz checksum (WOTS+C).
//!
//! Two codewords of equal sum are never ordered chunk by chunk.
//!
//! So a revealed signature gives a forger no chain value it could extend.

use crate::*;

/// `sk_{lay,tau,e,i}`: the start of chain `i`, derived from the master secret.
pub(crate) fn secret(pp: &PublicParam, master: &[u64; 4], pos: Pos, i: usize) -> Digest {
    th(pp, &tweak(TWEAK_PRF, pos.lay, pos.tau, i as u32, pos.e), master)
}

/// `Chain`'s hash, `tw | P | value`, kept across a one-time key's steps and chains: a step writes only its tweak's
/// position and its value.
pub(crate) struct Chains {
    step: Template<6>,
}

/// Bytes 4..8 of a tweak: its position `p`.
const TWEAK_POSITION: usize = 4;

impl Chains {
    pub(crate) fn new(pp: &PublicParam, pos: Pos) -> Self {
        let [t0, t1] = tweak(TWEAK_CHAIN, pos.lay, pos.tau, 0, pos.e);
        Self {
            step: Template::new([t0, t1, pp[0], pp[1], 0, 0]),
        }
    }

    /// `Chain`: walk chain `i` for `steps` steps from value number `start`.
    ///
    /// The step out of value `s` is hashed at position `8i + s`, so no two steps share a tweak. Only the tweak's
    /// position field changes: the rest, `tau | e` included, is the template's.
    #[inline(always)]
    pub(crate) fn walk(&mut self, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
        let first = (CHAIN_LEN * i + start) as u32;
        self.step
            .chain::<TWEAK_POSITION, { 8 * PAYLOAD }>(first..first + steps as u32, value)
    }
}

/// The Merkle leaf of a one-time key: `Th` over its `v` chain ends, chain `i`'s being `end(i)`, the chains in
/// order, each written into the hash as it is reached.
#[inline(always)]
pub(crate) fn leaf_hash(pp: &PublicParam, pos: Pos, end: impl FnMut(usize) -> Digest) -> Digest {
    digest(hash_with(|m| {
        m.write(tweak(TWEAK_LEAF, pos.lay, pos.tau, 0, pos.e))
            .write(*pp)
            .write_each(V, end);
    }))
}

/// A codeword: `v` chunks of `w` bits, 21 to a word, where each chain is opened.
#[derive(Clone, Copy)]
pub(crate) struct Digits([u64; 2]);

impl Digits {
    /// Chunk `i`: bits `3r..3r+3` of word `i / 21`, `r = i % 21`.
    pub(crate) const fn get(self, i: usize) -> usize {
        (self.0[i / (V / 2)] >> (W * (i % (V / 2)))) as usize & (CHAIN_LEN - 1)
    }

    /// The chunks in order, a call each: shifted out of the words, which no division by 21 costs.
    #[inline(always)]
    fn in_order(self) -> impl FnMut() -> usize {
        let [low, high] = self.0;
        // The high word's chunks start right after the low word's 63 bits.
        let mut rest = u128::from(low) | u128::from(high) << (W * V / 2);
        move || {
            let chunk = rest as usize & (CHAIN_LEN - 1);
            rest >>= W;
            chunk
        }
    }

    /// The sum of the chunks, by adding neighbouring fields in place.
    ///
    /// No field overflows into the next: the top bits are zero, a chunk is at most 7, and all of them sum to at
    /// most 294.
    const fn sum(self) -> u64 {
        let [low, high] = self.0;
        // 7 in every 6-bit field: the even chunks.
        const EVEN: u64 = 0x71C7_1C71_C71C_71C7;
        // 63 in every 12-bit field.
        const LOW6: u64 = 0xF03F_03F0_3F03_F03F;
        // Four chunks to a 6-bit field, two of each word: at most 28.
        let s = (low & EVEN) + (low >> W & EVEN) + (high & EVEN) + (high >> W & EVEN);
        // Two fields to a 12-bit field: at most 56.
        let s = (s & LOW6) + (s >> 6 & LOW6);
        // The six fields, folded into the lowest.
        let s = s + (s >> 12);
        let s = s + (s >> 24);
        (s + (s >> 48)) & 0xFFF
    }
}

/// `Enc`: the codeword of `message` under `counter`, or `None` if it has none.
///
/// Each 64-bit half of the digest is 21 chunks of `w` bits and a top bit pinned to zero.
///
/// Pinning it makes the codeword determine the digest.
pub(crate) fn encode(pp: &PublicParam, pos: Pos, message: &Digest, counter: u32) -> Option<Digits> {
    // `M | counter`: the counter is 4 bytes, so it takes the byte path.
    let mut hasher = Blake2s::new();
    hasher
        .update_words(&tweak(TWEAK_ENC, pos.lay, pos.tau, 0, pos.e))
        .update_words(pp);
    hasher.update_words(message).update(&counter.to_le_bytes());
    let [low, high, ..] = hasher.finalize_words();
    if (low | high) >> (W * V / 2) != 0 {
        return None;
    }
    let digits = Digits([low, high]);
    (digits.sum() == TARGET_SUM as u64).then_some(digits)
}

/// `Ots.leaf`: the leaf a one-time signature recovers, or `None` if `counter` gives no codeword.
pub(crate) fn leaf(pp: &PublicParam, pos: Pos, message: &Digest, counter: u32, ots: &[Digest; V]) -> Option<Digest> {
    let digits = encode(pp, pos, message, counter)?;
    // Chain `i` was opened at value `x_i`: walk it the rest of the way to value 7.
    let mut chains = Chains::new(pp, pos);
    let mut next_digit = digits.in_order();
    Some(leaf_hash(pp, pos, |i| {
        let start = next_digit();
        chains.walk(i, start, CHAIN_LEN - 1 - start, ots[i])
    }))
}
