//! LeanDA's systematic additive RS code, two-branch commitment, and membership.
//!
//! Symbols are row-major little-endian `u64`s in GF(2^64). A direct claim carries
//! encoded rows, not just payload rows. Roots bind the zero-padded row matrix,
//! not its original row count. The membership vector is derived here, never
//! trusted as an unchecked hint.

use alloc::vec::Vec;
use leanvm_guest::{Field, Hasher, hash};

use crate::Error;

pub const DA_LOG_K: usize = 14;
pub const DA_LOG_CELL: usize = 8;
pub const DA_MAX_ROWS: usize = 1024;
pub const BLOB_SYMBOLS: usize = 1 << DA_LOG_K;
pub const CODEWORD_SYMBOLS: usize = 2 * BLOB_SYMBOLS;
pub const CELL_SYMBOLS: usize = 1 << DA_LOG_CELL;
pub const CELLS_PER_ROW: usize = CODEWORD_SYMBOLS / CELL_SYMBOLS;
pub const VECTOR_BYTES: usize = CODEWORD_SYMBOLS * 24;
const PAYLOAD_CELLS: usize = BLOB_SYMBOLS / CELL_SYMBOLS;
const LOG_M: usize = DA_LOG_K + 1;
const LABEL: &[u8] = b"leanDA/rs-membership/v1";
type Hash = [u8; 32];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Commitment {
    pub root: Hash,
    pub root_row: Hash,
    pub root_col: Hash,
}

fn filled<T: Clone>(len: usize, value: T) -> Result<Vec<T>, Error> {
    let mut result = Vec::new();
    result.try_reserve_exact(len).map_err(|_| Error::Allocation)?;
    result.resize(len, value);
    Ok(result)
}

fn rows(symbols: usize) -> Result<usize, Error> {
    if symbols == 0 || !symbols.is_multiple_of(CODEWORD_SYMBOLS) || symbols > DA_MAX_ROWS * CODEWORD_SYMBOLS {
        return Err(Error::InvalidShape);
    }
    Ok(symbols / CODEWORD_SYMBOLS)
}

#[derive(Clone, Copy)]
enum Symbols<'a> {
    Words(&'a [u64]),
    Bytes(&'a [u8]),
}

impl Symbols<'_> {
    fn len(self) -> Result<usize, Error> {
        match self {
            Self::Words(words) => Ok(words.len()),
            Self::Bytes(bytes) if bytes.len() % 8 == 0 => Ok(bytes.len() / 8),
            Self::Bytes(_) => Err(Error::InvalidShape),
        }
    }

    fn at(self, index: usize) -> u64 {
        match self {
            Self::Words(words) => words[index],
            Self::Bytes(bytes) => {
                let mut word = [0; 8];
                word.copy_from_slice(&bytes[index * 8..index * 8 + 8]);
                u64::from_le_bytes(word)
            }
        }
    }

    fn cell_hash(self, start: usize) -> Hash {
        match self {
            Self::Bytes(bytes) => hash(&bytes[start * 8..(start + CELL_SYMBOLS) * 8]),
            Self::Words(words) => {
                let mut h = Hasher::new();
                for word in &words[start..start + CELL_SYMBOLS] {
                    h.update(&word.to_le_bytes());
                }
                h.finalize()
            }
        }
    }
}

fn hash_pair(left: &Hash, right: &Hash) -> Hash {
    let mut h = Hasher::new();
    h.update(left);
    h.update(right);
    h.finalize()
}

/// Fold a nonempty, power-of-two slice of already-hashed leaves in place.
fn tree_root(leaves: &mut [Hash]) -> Hash {
    let mut width = leaves.len();
    while width > 1 {
        for i in 0..width / 2 {
            leaves[i] = hash_pair(&leaves[2 * i], &leaves[2 * i + 1]);
        }
        width /= 2;
    }
    leaves[0]
}

pub fn padding_digests() -> (Hash, Hash) {
    let cell = hash(&[0; CELL_SYMBOLS * 8]);
    let mut h = Hasher::new();
    for _ in 0..PAYLOAD_CELLS {
        h.update(&cell);
    }
    (cell, h.finalize())
}

fn commit_symbols(symbols: Symbols<'_>) -> Result<Commitment, Error> {
    let n = rows(symbols.len()?)?;
    let padded = n.next_power_of_two();
    let (padding_cell, padding_row) = padding_digests();
    let mut cells = filled(n * CELLS_PER_ROW, [0; 32])?;
    let mut row_hashes = filled(padded, padding_row)?;
    for row in 0..n {
        let mut prefix = Hasher::new();
        for column in 0..CELLS_PER_ROW {
            let digest = symbols.cell_hash(row * CODEWORD_SYMBOLS + column * CELL_SYMBOLS);
            cells[row * CELLS_PER_ROW + column] = digest;
            if column < PAYLOAD_CELLS {
                prefix.update(&digest);
            }
        }
        row_hashes[row] = prefix.finalize();
    }
    let root_row = tree_root(&mut row_hashes);
    let mut column_roots = [[0; 32]; CELLS_PER_ROW];
    let mut column = filled(padded, padding_cell)?;
    for j in 0..CELLS_PER_ROW {
        for i in 0..padded {
            column[i] = if i < n {
                cells[i * CELLS_PER_ROW + j]
            } else {
                padding_cell
            };
        }
        column_roots[j] = tree_root(&mut column);
    }
    let root_col = tree_root(&mut column_roots);
    Ok(Commitment {
        root: hash_pair(&root_row, &root_col),
        root_row,
        root_col,
    })
}

/// Recompute both branches over 1..=1024 encoded rows. This alone does NOT check
/// code membership; use `verify` when accepting an untrusted direct claim.
pub fn commitment(codewords: &[u64]) -> Result<Commitment, Error> {
    commit_symbols(Symbols::Words(codewords))
}

pub fn commitment_bytes(codewords_le: &[u8]) -> Result<Commitment, Error> {
    commit_symbols(Symbols::Bytes(codewords_le))
}

fn transcript_step(state: &Hash, data: &[u8; 32]) -> Hash {
    hash_pair(state, data)
}

/// Exact Fiat-Shamir challenge sequence from `lean_da::membership_challenges`.
pub fn membership_challenges(root: &Hash) -> [Field; DA_LOG_K] {
    let mut state = hash(LABEL);
    for half in root.chunks_exact(16) {
        let mut block = [0; 32];
        block[..16].copy_from_slice(half);
        block[24] = 1;
        state = transcript_step(&state, &block);
    }
    let mut z = [Field::ZERO; DA_LOG_K];
    let mut block = [0; 32];
    block[24] = 2;
    for challenge in &mut z {
        state = transcript_step(&state, &block);
        let mut limbs = [0; 3];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let mut bytes = [0; 8];
            bytes.copy_from_slice(&state[i * 8..i * 8 + 8]);
            *limb = u64::from_le_bytes(bytes);
        }
        *challenge = Field(limbs);
    }
    z
}

fn base_mul(a: u64, b: u64) -> u64 {
    (Field([a, 0, 0]) * Field([b, 0, 0])).0[0]
}

/// Normalized subspace evaluations with the reference NTT's layer convention.
/// Storage is fixed by the protocol; no input controls a transform dimension.
struct Ntt {
    evals: [[u64; LOG_M]; LOG_M],
    dim: usize,
}

impl Ntt {
    fn new(dim: usize) -> Self {
        let mut evals = [[0; LOG_M]; LOG_M];
        for (j, value) in evals[0][..dim].iter_mut().enumerate() {
            *value = 1 << j;
        }
        for i in 1..dim {
            for j in 0..dim - i {
                let value = evals[i - 1][j + 1];
                evals[i][j] = base_mul(value, value ^ evals[i - 1][0]);
            }
        }
        for (i, row) in evals.iter_mut().enumerate().take(dim) {
            // Every leading subspace evaluation is nonzero. The base-field
            // inverse exponent is 2^64-2, not the extension-field exponent.
            let inv = Field([row[0], 0, 0]).pow(u64::MAX - 1).0[0];
            for value in &mut row[..dim - i] {
                *value = base_mul(*value, inv);
            }
        }
        Self { evals, dim }
    }

    fn twiddle(&self, layer: usize, block: usize) -> u64 {
        let row = &self.evals[self.dim - layer - 1];
        let mut out = 0;
        for j in 0..layer {
            if (block >> j) & 1 != 0 {
                out ^= row[1 + j];
            }
        }
        out
    }

    fn transform_words(&self, data: &mut [u64], inverse: bool) {
        for pass in 0..self.dim {
            let layer = if inverse { self.dim - pass - 1 } else { pass };
            let half = 1 << (self.dim - layer - 1);
            for block in 0..1 << layer {
                let twiddle = self.twiddle(layer, block);
                let start = block * 2 * half;
                for a in start..start + half {
                    let b = a + half;
                    if inverse {
                        data[b] ^= data[a];
                        data[a] ^= base_mul(data[b], twiddle);
                    } else {
                        data[a] ^= base_mul(data[b], twiddle);
                        data[b] ^= data[a];
                    }
                }
            }
        }
    }

    fn transform_fields(&self, data: &mut [Field]) {
        for layer in 0..self.dim {
            let half = 1 << (self.dim - layer - 1);
            for block in 0..1 << layer {
                let twiddle = Field([self.twiddle(layer, block), 0, 0]);
                let start = block * 2 * half;
                for a in start..start + half {
                    let b = a + half;
                    let value = data[b];
                    let next = data[a] + value * twiddle;
                    data[a] = next;
                    data[b] = value + next;
                }
            }
        }
    }
}

/// Systematically encode one payload row into an exact 32768-symbol output.
/// Output starts with the unchanged payload; the second half is its redundancy.
pub fn encode_row(payload: &[u64], output: &mut [u64]) -> Result<(), Error> {
    if payload.len() != BLOB_SYMBOLS || output.len() != CODEWORD_SYMBOLS {
        return Err(Error::InvalidShape);
    }
    output[..BLOB_SYMBOLS].copy_from_slice(payload);
    output[BLOB_SYMBOLS..].fill(0);
    Ntt::new(DA_LOG_K).transform_words(&mut output[..BLOB_SYMBOLS], true);
    Ntt::new(LOG_M).transform_words(output, false);
    Ok(())
}

/// Derive the entire extension-field dual codeword, in domain order.
pub fn membership_vector(root: &Hash) -> Result<Vec<Field>, Error> {
    dual_codeword(&membership_challenges(root))
}

pub fn dual_codeword(z: &[Field; DA_LOG_K]) -> Result<Vec<Field>, Error> {
    let mut buffer = filled(CODEWORD_SYMBOLS, Field::ZERO)?;
    buffer[0] = Field::ONE;
    for (j, &challenge) in z.iter().enumerate() {
        let (low, high) = buffer[..1 << (j + 1)].split_at_mut(1 << j);
        for (out, &value) in high.iter_mut().zip(low.iter()) {
            *out = value * challenge;
        }
    }
    Ntt::new(LOG_M).transform_fields(&mut buffer);
    Ok(buffer)
}

/// Standard BLAKE2s of 32768 entries, each three LE64 limbs with no padding.
pub fn vector_digest(vector: &[Field]) -> Result<Hash, Error> {
    if vector.len() != CODEWORD_SYMBOLS {
        return Err(Error::InvalidShape);
    }
    let mut h = Hasher::new();
    for value in vector {
        for limb in value.0 {
            h.update(&limb.to_le_bytes());
        }
    }
    Ok(h.finalize())
}

fn verify_symbols(symbols: Symbols<'_>, root: &Hash, membership_digest: &Hash) -> Result<(), Error> {
    let n = rows(symbols.len()?)?;
    if commit_symbols(symbols)?.root != *root {
        return Err(Error::RootMismatch);
    }
    let vector = membership_vector(root)?;
    if vector_digest(&vector)? != *membership_digest {
        return Err(Error::MembershipDigestMismatch);
    }
    for row in 0..n {
        let mut residual = Field::ZERO;
        for (column, &weight) in vector.iter().enumerate() {
            residual += weight * Field([symbols.at(row * CODEWORD_SYMBOLS + column), 0, 0]);
        }
        if !residual.is_zero() {
            return Err(Error::InvalidMembership);
        }
    }
    Ok(())
}

/// Verify the commitment, required membership-vector digest, and every row's
/// dual inner product. Both roots and the vector are recomputed inside the guest.
/// Allocations are fallible and bounded independently of untrusted row lengths.
pub fn verify(codewords: &[u64], root: &Hash, membership_digest: &Hash) -> Result<(), Error> {
    verify_symbols(Symbols::Words(codewords), root, membership_digest)
}

/// Byte-slice variant: exact encoded rows in LE64, without copying the matrix.
pub fn verify_bytes(codewords_le: &[u8], root: &Hash, membership_digest: &Hash) -> Result<(), Error> {
    verify_symbols(Symbols::Bytes(codewords_le), root, membership_digest)
}
