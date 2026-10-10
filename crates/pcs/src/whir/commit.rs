// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The commitments: the L0 base encode of the `F64` message, and each deeper
//! level's extension-field encode, both Merkle-committed one leaf per row.

use crate::merkle::{Hash, MerkleBuilder};
use crate::ntt::AdditiveNttF64;
use crate::verifier::OpeningVerifier;
use crate::whir::anchor::anchor_value;
use crate::whir::ntt_ext::{encode_rows_ext, rows_at_ext};
use crate::whir::verify::WhirError;
use fiat_shamir::TranscriptContext;
use fiat_shamir::merkle::hash_to_scalars;
use fiat_shamir::transcript::Transmitter;
use primitives::field::{F64, F192};
use std::sync::Arc;

/// The public shape of the committed, zero-padded witness.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CommitmentShape {
    pub log_n: usize,
    pub log_batch_size: usize,
    pub log_inv_rate: usize,
    pub n_lanes: usize,
}

impl CommitmentShape {
    /// Check the raw encoding shape before any shape-dependent shifts or reads.
    pub(crate) fn valid(self) -> bool {
        self.log_n > self.log_batch_size
            && self.log_n < usize::BITS as usize
            && self.log_inv_rate >= 1
            && (self.log_n - self.log_batch_size)
                .checked_add(self.log_inv_rate)
                .is_some_and(|log_code| log_code < usize::BITS as usize)
            && self.n_lanes >= 1
            && self.n_lanes <= 1usize << self.log_batch_size
    }
}

/// Immutable commitment identity: its pre-commit context, shape, root, and MLE anchor.
#[derive(Clone, Debug)]
pub struct Commitment<E = F192, R = Hash, K = F64> {
    pub(crate) root: R,
    pub(crate) shape: CommitmentShape,
    pub(crate) context: TranscriptContext<K, R>,
    pub(crate) point: Vec<E>,
    pub(crate) value: E,
}

impl<E, R, K> Commitment<E, R, K> {
    pub const fn root(&self) -> R
    where
        R: Copy,
    {
        self.root
    }

    pub const fn shape(&self) -> CommitmentShape {
        self.shape
    }

    pub const fn context(&self) -> TranscriptContext<K, R>
    where
        K: Copy,
        R: Copy,
    {
        self.context
    }

    pub fn point(&self) -> &[E] {
        &self.point
    }

    pub const fn value(&self) -> E
    where
        E: Copy,
    {
        self.value
    }

    pub(crate) fn valid_context(&self) -> bool {
        if self.context.pending_bytes > 64 {
            return false;
        }
        let words = self.context.pending_bytes.div_ceil(8);
        let mut i = 0;
        while i < 8 {
            if self.context.pending[i].is_some() != (i < words) {
                return false;
            }
            i += 1;
        }
        true
    }
}

// Little-endian bytes "whir-anchor-v1", padded with zeros to three limbs.
const ANCHOR_DOMAIN: F192 = F192::new(0x636e612d72696877, 0x000031762d726f68, 0);

// Little-endian bytes "whir-opening-v1", padded with zeros to three limbs.
const OPENING_DOMAIN: F192 = F192::new(0x65706f2d72696877, 0x0031762d676e696e, 0);

fn commitment_constants(shape: CommitmentShape) -> [F192; 3] {
    [
        ANCHOR_DOMAIN,
        F192::new(
            shape.log_n as u64,
            shape.log_batch_size as u64,
            shape.log_inv_rate as u64,
        ),
        F192::from(F64(shape.n_lanes as u64)),
    ]
}

/// Bind the whole immutable record before any opening challenge, including in a fresh session.
pub(crate) fn send_record_binding(ps: &mut impl Transmitter, commitment: &Commitment) {
    let mut constants = commitment_constants(commitment.shape);
    constants[0] = OPENING_DOMAIN;
    let mut i = 0;
    while i < constants.len() {
        ps.add_scalar(constants[i]);
        i += 1;
    }
    let root = hash_to_scalars(&commitment.root);
    let state = hash_to_scalars(&commitment.context.state);
    let mut i = 0;
    while i < 2 {
        ps.add_scalar(root[i]);
        i += 1;
    }
    let mut i = 0;
    while i < 2 {
        ps.add_scalar(state[i]);
        i += 1;
    }
    let context = &commitment.context;
    ps.add_scalar(F192::new(
        context.pending_bytes as u64,
        u64::from(context.first),
        context.previous,
    ));
    ps.add_scalar(F192::new(context.squeezed, 0, 0));
    let words = context.pending_bytes.div_ceil(8);
    let mut i = 0;
    while i + 3 <= words {
        ps.add_scalar(F192::new(
            context.pending[i].unwrap().0,
            context.pending[i + 1].unwrap().0,
            context.pending[i + 2].unwrap().0,
        ));
        i += 3;
    }
    if i < words {
        let second = if i + 1 < words {
            context.pending[i + 1].unwrap().0
        } else {
            0
        };
        ps.add_scalar(F192::new(context.pending[i].unwrap().0, second, 0));
    }
    let mut i = 0;
    while i < commitment.shape.log_n {
        ps.add_scalar(commitment.point[i]);
        i += 1;
    }
    ps.add_scalar(commitment.value);
}

fn verify_record_constants<V: OpeningVerifier>(v: &mut V, constants: &[F192]) -> Result<(), WhirError> {
    let mut i = 0;
    while i < constants.len() {
        let actual = v.next_scalar()?;
        let expected = v.constant(constants[i]);
        v.ensure_eq(actual, expected, || WhirError::CommitmentMismatch)?;
        i += 1;
    }
    Ok(())
}

fn verify_record_values<V: OpeningVerifier>(v: &mut V, values: &[V::E], len: usize) -> Result<(), WhirError> {
    let mut i = 0;
    while i < len {
        let actual = v.next_scalar()?;
        v.ensure_eq(actual, values[i], || WhirError::CommitmentMismatch)?;
        i += 1;
    }
    Ok(())
}

fn verify_record_pending<V: OpeningVerifier>(
    v: &mut V,
    context: &TranscriptContext<V::K, V::Root>,
) -> Result<(), WhirError> {
    let words = context.pending_bytes.div_ceil(8);
    let mut i = 0;
    while i + 3 <= words {
        let actual = v.next_scalar()?;
        let expected = v.e_of_limbs([
            context.pending[i].unwrap(),
            context.pending[i + 1].unwrap(),
            context.pending[i + 2].unwrap(),
        ]);
        v.ensure_eq(actual, expected, || WhirError::CommitmentMismatch)?;
        i += 3;
    }
    if i < words {
        let actual = v.next_scalar()?;
        let zero = v.zero_k();
        let second = if i + 1 < words {
            context.pending[i + 1].unwrap()
        } else {
            zero
        };
        let expected = v.e_of_limbs([context.pending[i].unwrap(), second, zero]);
        v.ensure_eq(actual, expected, || WhirError::CommitmentMismatch)?;
    }
    Ok(())
}

/// Check every record field before opening batching; reads are determined only by the supplied record.
pub(crate) fn verify_record_binding<V: OpeningVerifier>(
    v: &mut V,
    commitment: &Commitment<V::E, V::Root, V::K>,
) -> Result<(), WhirError> {
    let mut constants = commitment_constants(commitment.shape);
    constants[0] = OPENING_DOMAIN;
    verify_record_constants(v, &constants)?;
    let root = v.root_scalars(commitment.root);
    let state = v.root_scalars(commitment.context.state);
    verify_record_values(v, &root, 2)?;
    verify_record_values(v, &state, 2)?;
    let context = &commitment.context;
    verify_record_constants(
        v,
        &[
            F192::new(context.pending_bytes as u64, u64::from(context.first), context.previous),
            F192::new(context.squeezed, 0, 0),
        ],
    )?;
    verify_record_pending(v, context)?;
    verify_record_values(v, &commitment.point, commitment.shape.log_n)?;
    let actual = v.next_scalar()?;
    v.ensure_eq(actual, commitment.value, || WhirError::CommitmentMismatch)?;
    Ok(())
}

/// Receive one commitment, retaining the pre-header context and binding its public shape before drawing its anchor.
///
/// # Errors
///
/// Rejects an invalid expected shape or different public constants with
/// [`WhirError::CommitmentMismatch`], and propagates malformed transcript errors.
pub fn receive_commitment<V: OpeningVerifier>(
    v: &mut V,
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
    n_lanes: usize,
) -> Result<Commitment<V::E, V::Root, V::K>, WhirError> {
    let shape = CommitmentShape {
        log_n,
        log_batch_size,
        log_inv_rate,
        n_lanes,
    };
    if !shape.valid() {
        return Err(WhirError::CommitmentMismatch);
    }
    let context = v.context();
    let mut constants_match = Ok(());
    for expected in commitment_constants(shape) {
        constants_match = match v.next_scalar() {
            Ok(actual) => {
                let expected = v.constant(expected);
                v.ensure_eq(actual, expected, || WhirError::CommitmentMismatch)
            }
            Err(error) => Err(error.into()),
        };
        if constants_match.is_err() {
            break;
        }
    }
    constants_match?;
    let root = v.next_root()?;
    let point = v.sample_vec(log_n);
    let value = v.next_scalar()?;
    Ok(Commitment {
        root,
        shape,
        context,
        point,
        value,
    })
}

/// Prover-side state retained after commit for the opening phase. The message
/// itself is not stored; the caller retains it for opening.
pub struct ProverData {
    pub codeword: Vec<F64>,
    pub merkle_tree: Vec<Hash>,
}

/// Commit to the `F64` message of a `2^log_n`-word witness: the message is its
/// leading `n_lanes` lane blocks of `2^(log_n - log_batch_size)` words each, one
/// RS codeword per lane, Merkle-committed one leaf per codeword position, the
/// leaf being that position across all `2^log_batch_size` lanes
/// (`2^log_batch_size * 8` bytes).
///
/// `n_lanes` is read off the message length, and `n_lanes < 2^log_batch_size` is
/// the padding-free case: the stacked witness's zero tail is whole lanes, so those
/// lanes are never encoded. Their codeword is zero (the encoding is linear), so the
/// leaf image is the one a full-width commitment would have hashed, with those
/// zeros LEADING it: lane `t` of the codeword is message block `n_lanes-1-t`, which
/// puts them at the front of the image where their whole blocks are one BLAKE2s
/// chaining value every leaf shares. Only the image's tail, the committed lanes,
/// rides the proof, so a verifier derives `n_lanes` from the announced layout to
/// read a row and supplies the prefix itself.
///
/// After encoding, retain the pre-header context, transmit the domain and shape as three scalars, then the root; draw one anchor point and transmit the zero-padded witness's MLE there.
pub fn commit(
    ps: &mut impl Transmitter,
    message: &[F64],
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
) -> (Commitment, ProverData) {
    let mut shape = CommitmentShape {
        log_n,
        log_batch_size,
        log_inv_rate,
        n_lanes: 1,
    };
    assert!(shape.valid(), "invalid commitment encoding shape");
    let log_rows = log_n - log_batch_size;
    let n_lanes = message.len() >> log_rows;
    shape.n_lanes = n_lanes;
    assert!(shape.valid(), "at most 2^log_batch_size lanes carry data");
    assert_eq!(message.len(), n_lanes << log_rows, "message is whole lane blocks");
    let k_code = log_rows + log_inv_rate;
    let n_positions = 1usize << k_code;
    let codeword_len = n_positions * n_lanes;

    let mut codeword = Box::new_uninit_slice(codeword_len);

    // Leaves are hashed as the encode finishes each block of rows.
    let tree = MerkleBuilder::new(n_positions, n_lanes, 1usize << log_batch_size);
    tracing::info_span!("NTT", kind = "base encode", log_domain = k_code, lanes = n_lanes).in_scope(|| {
        // SAFETY: every codeword element is written before it is read.
        // The transpose covers every word of the message region (its tiles are asserted to).
        // The encode writes every other replica from it before transforming that region in place.
        let codeword = unsafe { primitives::write_only(&mut codeword) };
        crate::ntt::transpose_lane_major(&mut codeword[..message.len()], message, n_lanes, log_rows);
        let ntt = AdditiveNttF64::standard(k_code);
        ntt.encode_interleaved_in_place_with(codeword, n_lanes, log_inv_rate, &|row, rows| {
            tree.absorb(row, rows);
        });
    });
    // SAFETY: the encode wrote the whole codeword.
    let codeword = unsafe { codeword.assume_init() }.into_vec();
    let merkle_tree = tracing::info_span!("Merkle").in_scope(|| tree.finish());
    let root = *merkle_tree.last().expect("merkle tree non-empty");
    let context = ps.context();
    ps.add_scalars(&commitment_constants(shape));
    ps.add_root(&root);
    let point = ps.sample_vec(log_n);
    let value = anchor_value(message, log_rows, &point);
    ps.add_scalar(value);

    (
        Commitment {
            root,
            shape,
            context,
            point,
            value,
        },
        ProverData { codeword, merkle_tree },
    )
}

/// One deeper WHIR commitment level: its message and Merkle tree.
///
/// The codeword is not kept.
/// Each row is one Merkle leaf of `num_interleaved` E values, and an opened row is evaluated again from the message.
pub(crate) struct LigeroWitness {
    msg: Arc<Vec<F192>>,
    ntt: AdditiveNttF64,
    pub tree: Vec<Hash>,
    pub(crate) block_len: usize,
    num_interleaved: usize,
}

impl LigeroWitness {
    #[inline]
    pub(super) fn root(&self) -> Hash {
        self.tree[self.tree.len() - 1]
    }

    /// The codeword rows at `positions`, each evaluated once however often it repeats.
    pub(super) fn open(&self, positions: &[usize]) -> OpenedRows {
        let mut unique = positions.to_vec();
        unique.sort_unstable();
        unique.dedup();
        let rows = rows_at_ext(&self.ntt, &self.msg, self.num_interleaved, &unique);
        OpenedRows {
            positions: unique,
            rows,
            width: self.num_interleaved,
        }
    }
}

/// Codeword rows of one level, by position.
pub(super) struct OpenedRows {
    /// The positions, ascending.
    positions: Vec<usize>,
    /// Their rows, one after another.
    rows: Vec<F192>,
    width: usize,
}

impl OpenedRows {
    /// The row at `position`.
    ///
    /// # Panics
    ///
    /// Panics unless the row was opened.
    pub(super) fn row(&self, position: usize) -> &[F192] {
        let index = self.positions.binary_search(&position).expect("an opened position");
        &self.rows[index * self.width..][..self.width]
    }
}

/// Commit an extension-field polynomial at one recursive WHIR level.
///
/// - Each lane of the row-major message is RS-encoded with base-field twiddles.
/// - Each row is hashed as one Merkle leaf as the encode finishes it, and dropped.
pub(crate) fn ligero_commit_ext(
    poly: Arc<Vec<F192>>,
    log_msg_cols: usize,
    log_num_interleaved: usize,
    log_inv_rate: usize,
) -> LigeroWitness {
    let msg_cols = 1usize << log_msg_cols;
    let num_interleaved = 1usize << log_num_interleaved;
    let block_len = msg_cols << log_inv_rate;
    let log_block_len = log_msg_cols + log_inv_rate;
    assert_eq!(poly.len(), num_interleaved * msg_cols);
    let ntt = AdditiveNttF64::standard(log_block_len);

    // One leaf per row, its F192s as K words: hashed as the encode finishes each block.
    let row_words = 3 * num_interleaved;
    let builder = MerkleBuilder::new(block_len, row_words, row_words);
    tracing::info_span!(
        "NTT",
        kind = "extension encode",
        log_domain = log_block_len,
        lanes = num_interleaved
    )
    .in_scope(|| {
        encode_rows_ext(&ntt, &poly, num_interleaved, log_inv_rate, &|row, rows| {
            builder.absorb(row, rows);
        });
    });
    let tree = tracing::info_span!("Merkle").in_scope(|| builder.finish());

    LigeroWitness {
        msg: poly,
        ntt,
        tree,
        block_len,
        num_interleaved,
    }
}
