//! Portable verification of the repository's canonical signature and LeanDA claims.
#![no_std]

extern crate alloc;

pub mod da;
pub mod sphincs;
pub mod xmss;

use leanvm_guest::Hasher;

type Digest = [u8; 16];

/// Verification failures, including malformed input and bounded allocation failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    PublicKeyLength,
    SignatureLength,
    InvalidEncoding,
    InadmissibleDigest,
    RootMismatch,
    InvalidShape,
    MembershipDigestMismatch,
    InvalidMembership,
    Allocation,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl core::error::Error for Error {}

fn tweak(domain: u8, kind: u8, layer: usize, tree: u32, position: u32, index: u32) -> Digest {
    let mut out = [0; 16];
    out[0] = domain;
    out[1] = kind;
    out[2] = layer as u8;
    out[4..8].copy_from_slice(&position.to_le_bytes());
    out[8..12].copy_from_slice(&tree.to_le_bytes());
    out[12..].copy_from_slice(&index.to_le_bytes());
    out
}

fn hash_start(pp: &[u8], tw: &Digest) -> Hasher {
    let mut h = Hasher::new();
    h.update(tw);
    h.update(pp);
    h
}

fn hash_finish(h: Hasher) -> Digest {
    let mut out = [0; 16];
    out.copy_from_slice(&h.finalize()[..16]);
    out
}

fn th(pp: &[u8], tw: &Digest, payload: &[u8]) -> Digest {
    let mut h = hash_start(pp, tw);
    h.update(payload);
    hash_finish(h)
}

fn pair(pp: &[u8], tw: &Digest, value: Digest, sibling: &[u8], right: bool) -> Digest {
    let mut h = hash_start(pp, tw);
    if right {
        h.update(sibling);
        h.update(&value);
    } else {
        h.update(&value);
        h.update(sibling);
    }
    hash_finish(h)
}

fn codeword(digest: &Digest, target: usize) -> Result<[u8; 42], Error> {
    let mut digits = [0; 42];
    let mut sum = 0;
    for half in 0..2 {
        let mut bytes = [0; 8];
        bytes.copy_from_slice(&digest[half * 8..half * 8 + 8]);
        let word = u64::from_le_bytes(bytes);
        if word >> 63 != 0 {
            return Err(Error::InvalidEncoding);
        }
        for i in 0..21 {
            let digit = ((word >> (3 * i)) & 7) as u8;
            digits[half * 21 + i] = digit;
            sum += digit as usize;
        }
    }
    if sum != target {
        return Err(Error::InvalidEncoding);
    }
    Ok(digits)
}
