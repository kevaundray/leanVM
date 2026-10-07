// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The commitments: the L0 base encode of the `F64` message, and each deeper
//! level's extension-field encode, both Merkle-committed one leaf per row.

use crate::merkle::{Hash, MerkleBuilder};
use crate::ntt::{AdditiveNttF64, Pad};
use crate::whir::induce::padding_shift;
use crate::whir::ntt_ext::encode_interleaved_ext;
use primitives::field::{F64, F192};

/// Public commitment for an `F64` message: the L0 Merkle root.
#[derive(Clone, Debug)]
pub struct Commitment {
    pub root: Hash,
}

/// Prover-side state retained after commit for the opening phase. The message
/// itself is not stored; the caller retains it for opening.
pub struct ProverData {
    pub codeword: Vec<F64>,
    pub merkle_tree: Vec<Hash>,
    /// The padding of a hiding commitment, lane block `u`'s `k` coefficients at `[u k, (u + 1) k)`; empty otherwise.
    pub pads: Vec<F64>,
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
pub fn commit(message: &[F64], log_n: usize, log_batch_size: usize, log_inv_rate: usize) -> (Commitment, ProverData) {
    commit_hiding(message, log_n, log_batch_size, log_inv_rate, &[])
}

/// [`commit`] with each lane padded past its power of two: the hiding commitment.
///
/// With `m = log_n - log_batch_size`, `r = log_inv_rate` and `k = pads.len() / n_lanes`, lane block `u` encodes `P_u(X) + W_m(X + s) R_u(X)`: `P_u` its `2^m` words as novel-basis coefficients, `R_u` its padding `pads[u k..(u + 1) k]`, and `s = F64(2^(m + r))`.
/// Since `W_m(X + s) = W_m(X) + W_m(s)` and `X_{2^m + j} = W_m X_j`, that is `2^m + k` coefficients, so the codeword stays on the same `2^(m + r)` points, and the encode is the one butterfly layer more that pairs the message with the padding (`AdditiveNttF64::encode_interleaved_in_place_with`).
/// The shift by `s` keeps the factor nonzero on the whole domain, where `W_m` alone vanishes on its first `2^m` points: any `k` symbols of a lane are then uniform, whatever its message.
/// Empty `pads` is [`commit`].
///
/// # Panics
///
/// Panics as [`commit`] does, or unless the padding is `k <= 2^m` coefficients for every lane.
pub fn commit_hiding(
    message: &[F64],
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
    pads: &[F64],
) -> (Commitment, ProverData) {
    assert!(log_inv_rate >= 1, "log_inv_rate must be >= 1 for a non-trivial RS code");
    assert!(log_n > log_batch_size, "witness must be wider than the interleaving");
    let log_rows = log_n - log_batch_size;
    let n_lanes = message.len() >> log_rows;
    assert_eq!(message.len(), n_lanes << log_rows, "message is whole lane blocks");
    assert!(
        n_lanes >= 1 && n_lanes <= 1usize << log_batch_size,
        "at most 2^log_batch_size lanes carry data"
    );
    let k_code = log_rows + log_inv_rate;
    let n_positions = 1usize << k_code;
    let codeword_len = n_positions * n_lanes;
    let k = pads.len() / n_lanes;
    assert_eq!(pads.len(), k * n_lanes, "every lane takes as many padding coefficients");
    assert!(k <= 1 << log_rows, "a lane's padding is at most its message's length");
    // Row `j` of the padding is coefficient `j` of every codeword lane's `R`, lane `t` being block `n_lanes - 1 - t`.
    let pad_rows: Vec<F64> = (0..k * n_lanes)
        .map(|w| pads[(n_lanes - 1 - w % n_lanes) * k + w / n_lanes])
        .collect();
    let pad = (k > 0).then(|| Pad {
        rows: &pad_rows,
        offset: padding_shift(log_rows, log_inv_rate),
    });
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
        ntt.encode_interleaved_in_place_with(codeword, n_lanes, log_inv_rate, pad, &|row, rows| {
            tree.absorb(row, rows);
        });
    });
    // SAFETY: the encode wrote the whole codeword.
    let codeword = unsafe { codeword.assume_init() }.into_vec();
    let merkle_tree = tracing::info_span!("Merkle").in_scope(|| tree.finish());
    let root = *merkle_tree.last().expect("merkle tree non-empty");

    let pads = pads.to_vec();
    (
        Commitment { root },
        ProverData {
            codeword,
            merkle_tree,
            pads,
        },
    )
}

/// Codeword + Merkle tree for one deeper WHIR commitment level.
/// `mat[pos * num_interleaved + lane]`; each row (one `pos` across all lanes)
/// is one Merkle leaf of `num_interleaved * 16` bytes.
pub(crate) struct LigeroWitness {
    pub(crate) mat: Vec<F192>,
    pub tree: Vec<Hash>,
    pub(crate) block_len: usize,
    pub(crate) num_interleaved: usize,
}

impl LigeroWitness {
    #[inline]
    pub(super) fn row(&self, pos: usize) -> &[F192] {
        let start = pos * self.num_interleaved;
        &self.mat[start..start + self.num_interleaved]
    }

    #[inline]
    pub(super) fn root(&self) -> Hash {
        self.tree[self.tree.len() - 1]
    }
}

/// Commit an extension-field polynomial at one recursive WHIR level.
///
/// - Each lane of the row-major message is RS-encoded with base-field twiddles.
/// - The codeword is then Merkle-committed, one leaf per row.
pub(crate) fn ligero_commit_ext(
    poly: &[F192],
    log_msg_cols: usize,
    log_num_interleaved: usize,
    log_inv_rate: usize,
    ntt: &AdditiveNttF64,
) -> LigeroWitness {
    let msg_cols = 1usize << log_msg_cols;
    let num_interleaved = 1usize << log_num_interleaved;
    let block_len = msg_cols << log_inv_rate;
    let log_block_len = log_msg_cols + log_inv_rate;
    assert_eq!(poly.len(), num_interleaved * msg_cols);
    assert!(log_block_len <= ntt.log_domain_size());

    let codeword_len = block_len * num_interleaved;
    // The encode builds the replicas itself, so the codeword starts unwritten.
    let mut mat = Box::new_uninit_slice(codeword_len);

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
        // SAFETY: the encode writes every matrix element before reading it.
        let mat = unsafe { primitives::write_only(&mut mat) };
        encode_interleaved_ext(ntt, mat, poly, num_interleaved, log_inv_rate, &|row, rows| {
            builder.absorb(row, rows);
        });
    });
    // SAFETY: the encode wrote the whole matrix.
    let mat = unsafe { mat.assume_init() }.into_vec();
    let tree = tracing::info_span!("Merkle").in_scope(|| builder.finish());

    LigeroWitness {
        mat,
        tree,
        block_len,
        num_interleaved,
    }
}
