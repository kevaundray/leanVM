//! XMSS SSZ verification: `root | pp` and `tips | randomness | path`.

use crate::{Error, codeword, hash_finish, hash_start, pair, th, tweak};

pub const DIGEST_LEN: usize = 16;
pub const PUBLIC_PARAM_LEN: usize = 16;
pub const PUB_KEY_SIZE: usize = 32;
pub const SIG_SIZE: usize = 1208;
pub const V: usize = 42;
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 8;
pub const TARGET_SUM: usize = 195;
pub const RANDOMNESS_LEN: usize = 24;
pub const LOG_LIFETIME: usize = 32;
pub const WOTS_SIG_SIZE: usize = 696;

/// Verify the exact fixed-size SSZ encodings used by `xmss::Encode`.
///
/// Public key: root (16), public parameter (16). Signature: 42 chain values
/// (16 each), randomness (24), then 32 bottom-up Merkle siblings (16 each).
/// All `u32` epochs are valid. No untrusted input causes allocation.
pub fn verify(public_key: &[u8], message: &[u8; 32], signature: &[u8], epoch: u32) -> Result<(), Error> {
    if public_key.len() != PUB_KEY_SIZE {
        return Err(Error::PublicKeyLength);
    }
    if signature.len() != SIG_SIZE {
        return Err(Error::SignatureLength);
    }
    let pp = &public_key[16..];
    let mut payload = [0; 64];
    payload[..32].copy_from_slice(message);
    payload[32..56].copy_from_slice(&signature[V * 16..WOTS_SIG_SIZE]);
    let digest = th(pp, &tweak(0, 4, 0, 0, 0, epoch), &payload);
    let digits = codeword(&digest, TARGET_SUM)?;
    let mut leaf = hash_start(pp, &tweak(0, 2, 0, 0, 0, epoch));
    for (i, &digit) in digits.iter().enumerate() {
        let mut value = [0; 16];
        value.copy_from_slice(&signature[i * 16..(i + 1) * 16]);
        for step in digit as usize..CHAIN_LENGTH - 1 {
            value = th(pp, &tweak(0, 1, 0, 0, (i * CHAIN_LENGTH + step) as u32, epoch), &value);
        }
        leaf.update(&value);
    }
    let mut current = hash_finish(leaf);
    for level in 0..LOG_LIFETIME {
        let index = (u64::from(epoch) >> (level + 1)) as u32;
        let start = WOTS_SIG_SIZE + level * 16;
        current = pair(
            pp,
            &tweak(0, 3, 0, 0, (level + 1) as u32, index),
            current,
            &signature[start..start + 16],
            (epoch >> level) & 1 != 0,
        );
    }
    if current != public_key[..16] {
        return Err(Error::RootMismatch);
    }
    Ok(())
}
