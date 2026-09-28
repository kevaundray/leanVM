//! Verification of the repository's BLAKE2s WOTS+C / FORS+C SPHINCS scheme.

use crate::{Error, codeword, hash_finish, hash_start, pair, th, tweak};

pub const N: usize = 16;
pub const PUB_KEY_SIZE: usize = 32;
pub const SIG_SIZE: usize = 4924;
pub const V: usize = 42;
pub const W: usize = 3;
pub const CHAIN_LEN: usize = 8;
pub const TARGET_SUM: usize = 191;
pub const D: usize = 3;
pub const HEIGHTS: [usize; D] = [12, 7, 7];
pub const SUFFIX: [usize; D + 1] = [26, 14, 7, 0];
pub const H: usize = 26;
pub const A: usize = 10;
pub const K: usize = 15;
pub const NUM_FTS_TREES: usize = K - 1;
pub const RANDOMIZER_LEN: usize = 16;
pub const COUNTER_LEN: usize = 4;
const FTS_END: usize = RANDOMIZER_LEN + NUM_FTS_TREES * (1 + A) * N;

fn bits(bytes: &[u8; 32], offset: usize, len: usize) -> u32 {
    let mut out = 0;
    for bit in 0..len {
        let position = offset + bit;
        out |= u32::from((bytes[position / 8] >> (position % 8)) & 1) << bit;
    }
    out
}

/// Verify `SphincsPublicKey::flatten()` and `SphincsSignature::to_bytes()`.
///
/// Signature order: randomizer16; 14 records of secret16 and ten siblings16;
/// then layers 0,1,2, each containing counter LE32, 42 chain values16, and
/// respectively 12,7,7 siblings16. The least-counter grinding rule is a signer
/// obligation: like the reference verifier, this checks admissibility only.
/// The verifier has fixed work bounds and does not allocate.
pub fn verify(public_key: &[u8], message: &[u8; 32], signature: &[u8]) -> Result<(), Error> {
    if public_key.len() != PUB_KEY_SIZE {
        return Err(Error::PublicKeyLength);
    }
    if signature.len() != SIG_SIZE {
        return Err(Error::SignatureLength);
    }
    let pp = &public_key[16..];
    let mut h = hash_start(pp, &tweak(1, 9, 0, 0, 0, 0));
    h.update(&signature[..RANDOMIZER_LEN]);
    h.update(&public_key[..16]);
    h.update(message);
    let digest = h.finalize();
    let idx = bits(&digest, 0, H);
    if bits(&digest, H + (K - 1) * A, A) != 0 {
        return Err(Error::InadmissibleDigest);
    }
    let mut roots = hash_start(pp, &tweak(1, 8, 0, idx, 0, 0));
    for kappa in 0..NUM_FTS_TREES {
        let opened = bits(&digest, H + kappa * A, A);
        let start = RANDOMIZER_LEN + kappa * (1 + A) * N;
        let mut current = th(pp, &tweak(1, 6, kappa, idx, 0, opened), &signature[start..start + N]);
        for level in 0..A {
            let at = start + (level + 1) * N;
            current = pair(
                pp,
                &tweak(1, 7, kappa, idx, (level + 1) as u32, opened >> (level + 1)),
                current,
                &signature[at..at + N],
                (opened >> level) & 1 != 0,
            );
        }
        roots.update(&current);
    }
    let mut current = hash_finish(roots);
    let mut layer_offset = [0; D];
    let mut at = FTS_END;
    for layer in 0..D {
        layer_offset[layer] = at;
        at += COUNTER_LEN + (V + HEIGHTS[layer]) * N;
    }
    for layer in (0..D).rev() {
        let tree = idx >> SUFFIX[layer];
        let leaf = (idx >> SUFFIX[layer + 1]) & ((1 << HEIGHTS[layer]) - 1);
        let start = layer_offset[layer];
        let mut payload = [0; N + COUNTER_LEN];
        payload[..N].copy_from_slice(&current);
        payload[N..].copy_from_slice(&signature[start..start + COUNTER_LEN]);
        let encoding = th(pp, &tweak(1, 4, layer, tree, 0, leaf), &payload);
        let digits = codeword(&encoding, TARGET_SUM)?;
        let mut leaf_hash = hash_start(pp, &tweak(1, 2, layer, tree, 0, leaf));
        for (i, &digit) in digits.iter().enumerate() {
            let at = start + COUNTER_LEN + i * N;
            let mut value = [0; N];
            value.copy_from_slice(&signature[at..at + N]);
            for step in digit as usize..CHAIN_LEN - 1 {
                value = th(
                    pp,
                    &tweak(1, 1, layer, tree, (CHAIN_LEN * i + step) as u32, leaf),
                    &value,
                );
            }
            leaf_hash.update(&value);
        }
        current = hash_finish(leaf_hash);
        for level in 0..HEIGHTS[layer] {
            let at = start + COUNTER_LEN + (V + level) * N;
            current = pair(
                pp,
                &tweak(1, 3, layer, tree, (level + 1) as u32, leaf >> (level + 1)),
                current,
                &signature[at..at + N],
                (leaf >> level) & 1 != 0,
            );
        }
    }
    if current != public_key[..N] {
        return Err(Error::RootMismatch);
    }
    Ok(())
}
