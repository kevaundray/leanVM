//! The XMSS signer-set statement and the files `gen-xmss` writes.
//!
//! `signers.json` is the statement: groups of keys that signed one `(leaf_index, message)`. Its digest is BLAKE2s-256
//! over little-endian `u64` words:
//!
//! ```text
//! key_list(keys)  = BLAKE2s(per key: merkle_root (2 words), public_param (2 words))
//! signer_set(S)   = BLAKE2s(TAG, n_groups, n_sphincs = 0, 0, BLAKE2s(""),
//!                           per group: leaf_index, n_keys, message (4 words), 0, 0,
//!                                      key_list(keys), 0, 0, 0, 0)
//! ```
//!
//! with `TAG = b"signers1"`. `inputs.json` carries the signatures for the circuit's witness generator.

use binary_spartan::proof::Boundary;
use primitives::hash::hash;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

const TAG: &[u8; 8] = b"signers1";
/// The link registers holding the final digest: link `j < 256` is bit `j % 8` of digest byte `j / 8`.
const DIGEST_BITS: usize = 256;

/// `N` bytes as a lowercase hex string.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Hex<const N: usize>(pub [u8; N]);

impl<const N: usize> Serialize for Hex<N> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&self.0.iter().map(|b| format!("{b:02x}")).collect::<String>())
    }
}

impl<'de, const N: usize> Deserialize<'de> for Hex<N> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let text = String::deserialize(d)?;
        let digit = |c: u8| (c as char).to_digit(16).filter(|_| !c.is_ascii_uppercase());
        if text.len() != 2 * N {
            return Err(serde::de::Error::custom(format!("expected {} hex digits", 2 * N)));
        }
        let mut out = [0u8; N];
        for (byte, pair) in out.iter_mut().zip(text.as_bytes().chunks_exact(2)) {
            match (digit(pair[0]), digit(pair[1])) {
                (Some(hi), Some(lo)) => *byte = (hi << 4 | lo) as u8,
                _ => return Err(serde::de::Error::custom("expected lowercase hex")),
            }
        }
        Ok(Self(out))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Key {
    pub root: Hex<16>,
    pub pp: Hex<16>,
}

impl Key {
    /// The key's encoded bytes, which the canonical order compares.
    fn bytes(&self) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[..16].copy_from_slice(&self.root.0);
        out[16..].copy_from_slice(&self.pp.0);
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Group {
    pub leaf_index: u32,
    pub message: Hex<32>,
    pub keys: Vec<Key>,
}

/// `signers.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SignerSet {
    pub groups: Vec<Group>,
}

impl SignerSet {
    /// Non-empty groups strictly increasing on `(leaf_index, message bytes)`, keys strictly increasing on their
    /// encoded bytes.
    pub fn check_canonical(&self) -> Result<(), String> {
        for (g, group) in self.groups.iter().enumerate() {
            if group.keys.is_empty() {
                return Err(format!("group {g} is empty"));
            }
            if g > 0 {
                let previous = &self.groups[g - 1];
                if (previous.leaf_index, previous.message) >= (group.leaf_index, group.message) {
                    return Err(format!("group {g} does not follow group {}", g - 1));
                }
            }
            if let Some(k) = (1..group.keys.len()).find(|&k| group.keys[k - 1].bytes() >= group.keys[k].bytes()) {
                return Err(format!("key {k} of group {g} does not follow key {}", k - 1));
            }
        }
        Ok(())
    }

    pub fn digest(&self) -> [u8; 32] {
        let mut data = Vec::with_capacity(64 * (1 + 2 * self.groups.len()));
        data.extend_from_slice(TAG);
        data.extend_from_slice(&(self.groups.len() as u64).to_le_bytes());
        data.extend_from_slice(&[0u8; 16]);
        data.extend_from_slice(&hash(&[]));
        for group in &self.groups {
            let keys: Vec<u8> = group.keys.iter().flat_map(Key::bytes).collect();
            data.extend_from_slice(&u64::from(group.leaf_index).to_le_bytes());
            data.extend_from_slice(&(group.keys.len() as u64).to_le_bytes());
            data.extend_from_slice(&group.message.0);
            data.extend_from_slice(&[0u8; 16]);
            data.extend_from_slice(&hash(&keys));
            data.extend_from_slice(&[0u8; 32]);
        }
        hash(&data)
    }

    /// The XMSS block's boundary for this set: every `in` register zero, the `out` registers the digest then zeros.
    pub fn boundary(&self, n_link: usize) -> Result<Boundary, String> {
        if n_link < DIGEST_BITS {
            return Err(format!("{n_link} links cannot hold a {DIGEST_BITS}-bit digest"));
        }
        let words = n_link.div_ceil(64);
        let mut output = vec![0u64; words];
        for (w, chunk) in self.digest().chunks_exact(8).enumerate() {
            output[w] = u64::from_le_bytes(chunk.try_into().expect("8 bytes"));
        }
        Ok(Boundary {
            input: vec![0; words],
            output,
        })
    }
}

/// One signature of `inputs.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Signer {
    pub root: Hex<16>,
    pub pp: Hex<16>,
    pub randomness: Hex<24>,
    pub chain_tips: Vec<Hex<16>>,
    pub merkle_proof: Vec<Hex<16>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InputGroup {
    pub leaf_index: u32,
    pub message: Hex<32>,
    pub signers: Vec<Signer>,
}

/// `inputs.json`, the witness generator's input.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Inputs {
    pub groups: Vec<InputGroup>,
}

/// Deterministic keys and signatures: group `g` of `sizes[g]` keys signs its own message at its own leaf index. The
/// groups and keys come out in canonical order. With `tamper`, one byte of the first signer's first chain tip is
/// flipped in the inputs only, so the statement is honest and the signature is not.
pub fn generate(sizes: &[usize], tamper: bool) -> Result<(Inputs, SignerSet), String> {
    let mut groups = Vec::with_capacity(sizes.len());
    for (g, &size) in sizes.iter().enumerate() {
        if size == 0 {
            return Err(format!("group {g} is empty"));
        }
        let label = |what: &[u8], k: usize| {
            let mut data = b"binary-spartan gen-xmss ".to_vec();
            data.extend_from_slice(what);
            data.extend_from_slice(&(g as u64).to_le_bytes());
            data.extend_from_slice(&(k as u64).to_le_bytes());
            hash(&data)
        };
        let leaf_index = u32::from_le_bytes(label(b"leaf", 0)[..4].try_into().expect("4 bytes"));
        let message = label(b"message", 0);
        let mut signers = Vec::with_capacity(size);
        for k in 0..size {
            let (secret, public) =
                xmss::key_gen_from_seed(label(b"key", k), leaf_index, leaf_index).map_err(|e| e.to_string())?;
            let signature = xmss::sign(&secret, &message, leaf_index).map_err(|e| e.to_string())?;
            xmss::verify(&public, &message, &signature, leaf_index).map_err(|e| e.to_string())?;
            let wots = &signature.wots_signature;
            signers.push(Signer {
                root: Hex(public.merkle_root),
                pp: Hex(public.public_param),
                randomness: Hex(wots.randomness),
                chain_tips: wots.chain_tips.iter().copied().map(Hex).collect(),
                merkle_proof: signature.merkle_proof.iter().copied().map(Hex).collect(),
            });
        }
        signers.sort_by_key(|s| (s.root, s.pp));
        groups.push(InputGroup {
            leaf_index,
            message: Hex(message),
            signers,
        });
    }
    groups.sort_by_key(|group| (group.leaf_index, group.message));
    let set = SignerSet {
        groups: groups
            .iter()
            .map(|group| Group {
                leaf_index: group.leaf_index,
                message: group.message,
                keys: group.signers.iter().map(|s| Key { root: s.root, pp: s.pp }).collect(),
            })
            .collect(),
    };
    set.check_canonical()?;
    if tamper {
        groups[0].signers[0].chain_tips[0].0[0] ^= 1;
    }
    Ok((Inputs { groups }, set))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn signer(inputs: &Inputs, g: usize, k: usize) -> (xmss::XmssPublicKey, xmss::XmssSignature) {
        let s = &inputs.groups[g].signers[k];
        let public = xmss::XmssPublicKey {
            merkle_root: s.root.0,
            public_param: s.pp.0,
        };
        let signature = xmss::XmssSignature {
            wots_signature: xmss::WotsSignature {
                chain_tips: std::array::from_fn(|i| s.chain_tips[i].0),
                randomness: s.randomness.0,
            },
            merkle_proof: std::array::from_fn(|i| s.merkle_proof[i].0),
        };
        (public, signature)
    }

    /// Generated sets are canonical and survive the JSON round trip, their signatures verify, and the tampered
    /// signature does not.
    #[test]
    fn generated_sets_are_canonical_and_signed() {
        let (inputs, set) = generate(&[2, 3], false).expect("generated");
        let mut sizes: Vec<usize> = set.groups.iter().map(|g| g.keys.len()).collect();
        sizes.sort_unstable();
        assert_eq!(sizes, [2, 3]);
        let json = serde_json::to_string(&set).expect("serializes");
        assert_eq!(serde_json::from_str::<SignerSet>(&json).expect("parses"), set);
        for (g, group) in inputs.groups.iter().enumerate() {
            for k in 0..group.signers.len() {
                let (public, signature) = signer(&inputs, g, k);
                assert_eq!(
                    xmss::verify(&public, &group.message.0, &signature, group.leaf_index),
                    Ok(())
                );
            }
        }
        let (tampered, tampered_set) = generate(&[2, 3], true).expect("generated");
        assert_eq!(tampered_set, set);
        let (public, signature) = signer(&tampered, 0, 0);
        let group = &tampered.groups[0];
        assert!(xmss::verify(&public, &group.message.0, &signature, group.leaf_index).is_err());
    }

    #[test]
    fn non_canonical_sets_are_refused() {
        let (_, set) = generate(&[2, 2], false).expect("generated");
        let mut swapped = set.clone();
        swapped.groups.swap(0, 1);
        assert!(swapped.check_canonical().is_err());
        let mut repeated = set.clone();
        repeated.groups[1].keys[1] = repeated.groups[1].keys[0];
        assert!(repeated.check_canonical().is_err());
        let mut same_group = set.clone();
        same_group.groups[1].leaf_index = same_group.groups[0].leaf_index;
        same_group.groups[1].message = same_group.groups[0].message;
        assert!(same_group.check_canonical().is_err());
        let mut empty = set.clone();
        empty.groups[0].keys.clear();
        assert!(empty.check_canonical().is_err());
    }

    /// The boundary's `out` words are the digest's bytes, little-endian, then zeros.
    #[test]
    fn boundary_carries_the_digest() {
        let (_, set) = generate(&[1], false).expect("generated");
        let boundary = set.boundary(300).expect("enough links");
        let digest = set.digest();
        assert_eq!(boundary.input, vec![0; 5]);
        for j in 0..320 {
            let bit = boundary.output[j / 64] >> (j % 64) & 1;
            let expected = if j < 256 { digest[j / 8] >> (j % 8) & 1 } else { 0 };
            assert_eq!(bit, u64::from(expected), "bit {j}");
        }
        assert!(set.boundary(255).is_err());
    }
}
