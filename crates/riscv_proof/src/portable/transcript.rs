//! Fiat–Shamir transport for the unpruned recursive proof.

use alloc::vec::Vec;
use leanvm_guest::{Field as F, Hasher, hash};

/// Resource ceiling for a single portable-verifier allocation. Callers of
/// infallible challenge/algebra helpers must validate dimensions against it.
pub const MAX_ELEMENTS: usize = 1 << 24;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    UnexpectedEnd,
    TrailingData,
    InvalidRoot,
    InvalidGrinding,
    InvalidMerkle,
    InvalidShape,
    InvalidSumcheck,
    InvalidGkr,
    ZeroCount,
    ClaimMismatch,
    Allocation,
}

fn compress(left: [u8; 32], right: [u64; 4]) -> [u8; 32] {
    let mut input = [0u8; 64];
    input[..32].copy_from_slice(&left);
    for (bytes, word) in input[32..].chunks_exact_mut(8).zip(right) {
        bytes.copy_from_slice(&word.to_le_bytes());
    }
    hash(&input)
}

fn scalar_block(value: F, domain: u64) -> [u64; 4] {
    [value.0[0], value.0[1], value.0[2], domain]
}

fn reserve<T>(count: usize) -> Result<Vec<T>, Error> {
    if count > MAX_ELEMENTS {
        return Err(Error::InvalidShape);
    }
    let mut out = Vec::new();
    out.try_reserve_exact(count).map_err(|_| Error::Allocation)?;
    Ok(out)
}

pub struct Transcript<'a> {
    proof: &'a crate::Proof,
    state: [u8; 32],
    stream_offset: usize,
    opening_offset: usize,
}

impl<'a> Transcript<'a> {
    pub fn new(proof: &'a crate::Proof, iv: [u8; 32], public: [u8; 32]) -> Self {
        let mut input = [0u8; 64];
        input[..32].copy_from_slice(&iv);
        input[32..].copy_from_slice(&public);
        Self {
            proof,
            state: hash(&input),
            stream_offset: 0,
            opening_offset: 0,
        }
    }

    fn take_raw(&mut self) -> Result<F, Error> {
        let value = *self.proof.stream.get(self.stream_offset).ok_or(Error::UnexpectedEnd)?;
        self.stream_offset += 1;
        Ok(value)
    }

    pub fn next_scalar(&mut self) -> Result<F, Error> {
        let value = self.take_raw()?;
        self.state = compress(self.state, scalar_block(value, 1));
        Ok(value)
    }

    pub fn next_scalars(&mut self, count: usize) -> Result<Vec<F>, Error> {
        if count > self.proof.stream.len() - self.stream_offset {
            return Err(Error::UnexpectedEnd);
        }
        let mut values = reserve(count)?;
        for _ in 0..count {
            values.push(self.next_scalar()?);
        }
        Ok(values)
    }

    pub fn sample(&mut self) -> F {
        self.state = compress(self.state, [0, 0, 0, 2]);
        F(core::array::from_fn(|i| {
            u64::from_le_bytes(self.state[8 * i..8 * i + 8].try_into().unwrap())
        }))
    }

    /// `count` is a validated protocol dimension, never an unchecked wire length.
    pub fn samples(&mut self, count: usize) -> Vec<F> {
        assert!(count <= MAX_ELEMENTS, "unvalidated challenge count");
        (0..count).map(|_| self.sample()).collect()
    }

    pub fn next_root(&mut self) -> Result<[u8; 32], Error> {
        let halves = [self.next_scalar()?, self.next_scalar()?];
        if halves.iter().any(|half| half.0[2] != 0) {
            return Err(Error::InvalidRoot);
        }
        let mut root = [0u8; 32];
        for (bytes, half) in root.chunks_exact_mut(16).zip(halves) {
            bytes[..8].copy_from_slice(&half.0[0].to_le_bytes());
            bytes[8..].copy_from_slice(&half.0[1].to_le_bytes());
        }
        Ok(root)
    }

    pub fn grind_check(&mut self, bits: usize) -> Result<(), Error> {
        if bits >= 64 {
            return Err(Error::InvalidShape);
        }
        // Nonces bypass scalar absorption: only DS_POW_NONCE binds them.
        let nonce = self.take_raw()?;
        let block = scalar_block(nonce, 4);
        let base = compress(self.state, [0, 0, 0, 3]);
        let digest = compress(base, block);
        let low = u64::from_le_bytes(digest[..8].try_into().unwrap());
        let valid = if bits == 0 {
            nonce == F::ZERO
        } else {
            low & ((1u64 << bits) - 1) == 0
        };
        self.state = compress(self.state, block);
        if valid { Ok(()) } else { Err(Error::InvalidGrinding) }
    }

    pub fn merkle(
        &mut self,
        root: &[u8; 32],
        num_leaves: usize,
        queries: &[usize],
        leaf_words: usize,
    ) -> Result<Vec<Vec<u64>>, Error> {
        if !num_leaves.is_power_of_two() || leaf_words > MAX_ELEMENTS {
            return Err(Error::InvalidShape);
        }
        if queries.len() > self.proof.merkle.len() - self.opening_offset {
            return Err(Error::UnexpectedEnd);
        }
        if queries.iter().any(|&query| query >= num_leaves) {
            return Err(Error::InvalidMerkle);
        }
        let height = num_leaves.trailing_zeros() as usize;
        let end = self.opening_offset + queries.len();
        let openings = &self.proof.merkle[self.opening_offset..end];
        // Reject extra lanes/siblings as well as missing ones; never hash a
        // proof-chosen shape and silently ignore its unauthenticated suffix.
        if openings
            .iter()
            .any(|o| o.leaf.len() != leaf_words || o.siblings.len() != height)
        {
            return Err(Error::InvalidMerkle);
        }
        let mut rows = reserve(queries.len())?;
        for (&query, opening) in queries.iter().zip(openings) {
            let mut hasher = Hasher::new();
            for &word in &opening.leaf {
                hasher.update(&word.to_le_bytes());
            }
            let mut node = hasher.finalize();
            for (level, sibling) in opening.siblings.iter().enumerate() {
                let mut pair = [0u8; 64];
                let (left, right) = if (query >> level) & 1 == 0 {
                    (&node, sibling)
                } else {
                    (sibling, &node)
                };
                pair[..32].copy_from_slice(left);
                pair[32..].copy_from_slice(right);
                node = hash(&pair);
            }
            if &node != root {
                return Err(Error::InvalidMerkle);
            }
            let mut row = reserve(leaf_words)?;
            row.extend_from_slice(&opening.leaf);
            rows.push(row);
        }
        self.opening_offset = end;
        Ok(rows)
    }

    pub fn sumcheck_round_poly(&mut self, count: usize, claim: F, eq: Option<F>) -> Result<Vec<F>, Error> {
        if !(2..=MAX_ELEMENTS).contains(&count) {
            return Err(Error::InvalidShape);
        }
        if count - 1 > self.proof.stream.len() - self.stream_offset {
            return Err(Error::UnexpectedEnd);
        }
        let mut coefficients = reserve(count)?;
        let fixed = usize::from(eq.is_none());
        let mut sum = F::ZERO;
        for i in 0..count {
            let value = if i == fixed { F::ZERO } else { self.next_scalar()? };
            if i > fixed {
                sum += value;
            }
            coefficients.push(value);
        }
        coefficients[fixed] = claim + eq.map_or(sum, |r| r * sum);
        Ok(coefficients)
    }

    pub fn finish(&self) -> Result<(), Error> {
        if self.stream_offset != self.proof.stream.len() || self.opening_offset != self.proof.merkle.len() {
            Err(Error::TrailingData)
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Opening, Proof};
    use alloc::vec;

    fn proof(stream: Vec<F>) -> Proof {
        Proof {
            stream,
            merkle: Vec::new(),
        }
    }

    #[test]
    fn scalar_and_root_absorption_match_blake2s_reference() {
        // Independently generated with Python hashlib.blake2s and LE packing.
        let p = proof(vec![F::new(7, 8, 9), F::new(10, 11, 12)]);
        let mut t = Transcript::new(&p, [0; 32], [0; 32]);
        t.next_scalars(2).unwrap();
        assert_eq!(
            t.sample(),
            F::new(9374537067478678717, 11862126481582659783, 10730703474248180329)
        );
        t.finish().unwrap();

        let p = proof(vec![F::new(1, 2, 0), F::new(3, 4, 0)]);
        let mut t = Transcript::new(&p, [0; 32], [0; 32]);
        let mut expected = [0u8; 32];
        for (bytes, value) in expected.chunks_exact_mut(8).zip(1u64..=4) {
            bytes.copy_from_slice(&value.to_le_bytes());
        }
        assert_eq!(t.next_root(), Ok(expected));
        assert_eq!(
            t.sample(),
            F::new(6514737399734456270, 103111743797671231, 4751384375517628443)
        );
    }

    #[test]
    fn root_top_limbs_and_zero_work_nonce_are_canonical() {
        for half in 0..2 {
            let mut stream = vec![F::ZERO; 2];
            stream[half] = F::new(0, 0, 1);
            let p = proof(stream);
            assert_eq!(
                Transcript::new(&p, [0; 32], [0; 32]).next_root(),
                Err(Error::InvalidRoot)
            );
        }
        let p = proof(vec![F::ONE]);
        assert_eq!(
            Transcript::new(&p, [0; 32], [0; 32]).grind_check(0),
            Err(Error::InvalidGrinding)
        );
        let p = proof(vec![F::ZERO]);
        let mut t = Transcript::new(&p, [0; 32], [0; 32]);
        t.grind_check(0).unwrap();
        assert_eq!(
            t.sample(),
            F::new(271679801638136788, 5902818954076678183, 1479951744110167976)
        );
        t.finish().unwrap();
    }

    #[test]
    fn positive_grinding_accepts_the_full_field_nonce_domain() {
        let p = proof(vec![F::new(0, 1, 1)]);
        let mut t = Transcript::new(&p, [0; 32], [0; 32]);
        t.grind_check(2).unwrap();
        assert_eq!(
            t.sample(),
            F::new(14331141553217168346, 5440131817678940893, 2564821914688928678)
        );
        t.finish().unwrap();
    }

    #[test]
    fn merkle_rejects_extra_data_and_wrong_query_shape() {
        let root = hash(&7u64.to_le_bytes());
        let mut p = proof(Vec::new());
        p.merkle.push(Opening {
            leaf: vec![7],
            siblings: Vec::new(),
        });
        let mut t = Transcript::new(&p, [0; 32], [0; 32]);
        assert_eq!(t.finish(), Err(Error::TrailingData));
        assert_eq!(t.merkle(&root, 1, &[0], 1).unwrap(), vec![vec![7]]);
        t.finish().unwrap();
        assert_eq!(
            Transcript::new(&p, [0; 32], [0; 32]).merkle(&root, 1, &[1], 1),
            Err(Error::InvalidMerkle)
        );
        p.merkle[0].siblings.push([0; 32]);
        assert_eq!(
            Transcript::new(&p, [0; 32], [0; 32]).merkle(&root, 1, &[0], 1),
            Err(Error::InvalidMerkle)
        );
        p.merkle[0].siblings.clear();
        p.merkle[0].leaf.push(0);
        assert_eq!(
            Transcript::new(&p, [0; 32], [0; 32]).merkle(&root, 1, &[0], 1),
            Err(Error::InvalidMerkle)
        );
    }

    #[test]
    fn sumcheck_binds_only_transmitted_coefficients_in_order() {
        let p = proof(vec![F::new(7, 8, 9), F::new(10, 11, 12)]);
        for equality in [None, Some(F::new(2, 3, 4))] {
            let mut t = Transcript::new(&p, [0; 32], [0; 32]);
            let coefficients = t.sumcheck_round_poly(3, F::Y, equality).unwrap();
            let q0 = coefficients[0];
            let q1 = coefficients.iter().fold(F::ZERO, |sum, &c| sum + c);
            assert_eq!(
                match equality {
                    None => q0 + q1,
                    Some(r) => (F::ONE + r) * q0 + r * q1,
                },
                F::Y
            );
            assert_eq!(
                t.sample(),
                F::new(9374537067478678717, 11862126481582659783, 10730703474248180329)
            );
        }
    }
}
