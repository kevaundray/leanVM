//! Public framing for field-native recursive proofs of RV64IM executions.

use crate::{Field, Hasher, hash};

pub const MAX_CHILDREN: usize = 2;
pub const PUBLIC_FIELDS: usize = 9;
pub const PUBLIC_DOMAIN: &[u8] = b"leanVM/native-circuit/public/v2\0";
pub const CLAIMS_DOMAIN: &[u8] = b"leanVM/deferred-claims/v1\0";
pub const BINDING_DOMAIN: &[u8] = b"leanVM/RV64IM/deferred-binding/v1\0";

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Claim {
    pub statement: [u8; 32],
    pub key: [u8; 32],
    pub height: u32,
}

pub fn public_fields(claim: &Claim) -> [Field; PUBLIC_FIELDS] {
    core::array::from_fn(|i| match i {
        0..=3 => Field::new(
            u64::from_le_bytes(claim.statement[8 * i..8 * i + 8].try_into().unwrap()),
            0,
            0,
        ),
        4..=7 => Field::new(
            u64::from_le_bytes(claim.key[8 * (i - 4)..8 * (i - 4) + 8].try_into().unwrap()),
            0,
            0,
        ),
        _ => Field::new(u64::from(claim.height), 0, 0),
    })
}

pub fn public_digest(public: &[Field]) -> [u8; 32] {
    let mut h = Hasher::new();
    h.update(&hash(PUBLIC_DOMAIN));
    h.update(&(public.len() as u64).to_le_bytes());
    for value in public {
        h.update(&value.to_le_bytes());
    }
    h.finalize()
}

/// Bind the ordered proof kinds, authorized keys and complete child public inputs.
pub fn claims_digest(claims: &[Claim]) -> [u8; 32] {
    let mut h = Hasher::new();
    h.update(&hash(CLAIMS_DOMAIN));
    h.update(&(claims.len() as u64).to_le_bytes());
    for claim in claims {
        h.update(&1u64.to_le_bytes());
        h.update(&claim.key);
        h.update(&public_digest(&public_fields(claim)));
    }
    h.finalize()
}

pub fn binding(statement: [u8; 32], claims: &[Claim]) -> [u8; 32] {
    let mut h = Hasher::new();
    h.update(&hash(BINDING_DOMAIN));
    h.update(&statement);
    h.update(&claims_digest(claims));
    h.finalize()
}
