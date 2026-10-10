// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The succinct verifier: it replays the transcript and checks the terminal claim through closed forms, never materializing a weight.
//!
//! It is written once over the opening verifier's operations, so the native verifier and the recursion machine's rows run the same steps.
//! Every query opens a full row whose path follows the query's bits, so the rows never depend on which rows are opened.

use super::anchor::anchor_eq_at;
use super::commit::Commitment;
use crate::verifier::OpeningVerifier;
use crate::whir::config::{ConfigError, VerifierConfig};
use crate::whir::induce::eval_sk_at_vks;
use fiat_shamir::arith::Arith;
use fiat_shamir::transcript::TranscriptError;
use primitives::field::{F64, F192};
use thiserror::Error;

/// Why a WHIR opening is rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum WhirError {
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// The opening's size and rate have no configuration.
    #[error(transparent)]
    Config(#[from] ConfigError),
    /// The announced layout stores no lanes, or more than a leaf holds.
    #[error("{n_lanes} committed lanes, and a leaf holds 1 to {max}")]
    LaneCount { n_lanes: usize, max: usize },
    /// A level of the configuration does not fit the witness.
    #[error("level {level} of the configuration does not fit the witness")]
    InvalidShape { level: usize },
    /// The immutable commitment record has a different shape or domain context.
    #[error("the immutable commitment record does not match its public context")]
    CommitmentMismatch,
    /// The opening has no ring-switched claim.
    #[error("the opening has no ring-switched claim")]
    NoRingClaim,
    /// A ring-switched region is no aligned slice of the committed cube, or a claim on it does not span it.
    #[error("ring-switched region {index} is no aligned slice of the cube spanned by its claims")]
    Region { index: usize },
    /// A point claim reaches past the committed cube.
    #[error("point claim {index} reaches past the committed cube")]
    PointClaim { index: usize },
    /// The final folded value does not match the claimed evaluation.
    #[error("the final sumcheck claim does not match the opening")]
    TerminalMismatch,
}

/// A round's quadratic `c + b X + a X^2`.
#[derive(Clone, Copy)]
struct Quad<E> {
    c: E,
    b: E,
    a: E,
}

/// An out-of-domain claim on a level's oracle: its point, its value, and its intro round.
struct Ood<E> {
    z: Vec<E>,
    y: E,
    intro: Quad<E>,
}

/// What a level's query batch leaves for the terminal weight.
struct LevelCtx<Q, E> {
    log_msg_cols: usize,
    queries: Vec<Q>,
    /// One power of the level's batching challenge per query.
    weights: Vec<E>,
    /// Where the level's fold challenges start among all of them.
    ris_start: usize,
    /// The level's power in the running claim.
    beta: E,
}

/// What an out-of-domain claim leaves for the terminal weight.
struct OodCtx<E> {
    z: Vec<E>,
    ris_start: usize,
    beta: E,
}

/// The oracle the next query batch opens.
struct Oracle<R> {
    root: R,
    log_num_interleaved: usize,
    log_msg_cols: usize,
    log_inv_rate: usize,
}

/// One level's query batch: its grinding, its index width and its count.
#[derive(Clone, Copy)]
struct QueryPhase {
    grinding: u32,
    depth: usize,
    count: usize,
}

/// The succinct WHIR verifier's state.
struct WhirReplay<'c, V: OpeningVerifier> {
    config: &'c VerifierConfig,
    /// The running claim and its round's quadratic.
    t_r: V::E,
    quad: Quad<V::E>,
    /// Every fold challenge, in round order.
    ris: Vec<V::E>,
    levels: Vec<LevelCtx<V::Query, V::E>>,
    oods: Vec<OodCtx<V::E>>,
}

/// The level-0 rows a query batch opened, one per query, of committed words.
struct BaseRows<K>(Vec<Vec<K>>);

/// A later level's rows a query batch opened, one per query, of elements of `E`.
struct ExtRows<E>(Vec<Vec<E>>);

/// A public weight evaluated once at the terminal point by the native verifier or recursion rows.
pub trait WeightAt<V: OpeningVerifier, E = <V as Arith>::E> {
    /// Evaluate the caller's weight at the final point in witness-coordinate order.
    fn evaluate(self, v: &mut V, point: &[E]) -> E;
}

struct AnchoredWeight<'a, W, E> {
    caller: W,
    shape: super::CommitmentShape,
    point: &'a [E],
    beta: E,
}

impl<V: OpeningVerifier, W: WeightAt<V>> WeightAt<V> for AnchoredWeight<'_, W, V::E> {
    fn evaluate(self, v: &mut V, point: &[V::E]) -> V::E {
        let caller = self.caller.evaluate(v, point);
        let anchor = anchor_eq_at(v, self.shape, self.point, point);
        v.mul_add(self.beta, anchor, caller)
    }
}

struct QueryBatch<Q, E> {
    queries: Vec<Q>,
    weights: Vec<E>,
    lambda: E,
}

fn enforce_base<V: OpeningVerifier>(
    v: &mut V,
    root: &V::Root,
    phase: QueryPhase,
    n_lanes: usize,
    max: usize,
    fold: &[V::E],
    batch: &QueryBatch<V::Query, V::E>,
) -> Result<V::E, TranscriptError> {
    let mut rows = v.open_rows(root, phase.depth, &batch.queries, n_lanes, max)?;
    let mut i = 0;
    while i < rows.len() {
        rows[i].reverse();
        i += 1;
    }
    Ok(base_enforced_sum(&BaseRows(rows), v, fold, &batch.weights))
}

fn enforce_ext<V: OpeningVerifier>(
    v: &mut V,
    oracle: &Oracle<V::Root>,
    fold: &[V::E],
    batch: &QueryBatch<V::Query, V::E>,
) -> Result<V::E, TranscriptError> {
    let rows = oracle.open_e_rows(v, &batch.queries)?;
    Ok(ext_enforced_sum(&rows, v, fold, &batch.weights))
}

/// Succinct verifier for the recursive prover, against a weight `b` over the `2^log_n` committed words.
///
/// It takes no dense weight: `weight_at` evaluates b's multilinear extension once, at the final fold point indexed by witness coordinate.
/// Verify a public linear claim with the same immutable commitment record used
/// at commitment time. `weight_at` evaluates the claimed weight on the full
/// Boolean cube and must vanish outside the record's occupied lane prefix.
///
/// The caller binds the public claim before entry. This samples only the
/// opening batch scalar and reuses the commitment's point and advertised value.
///
/// # Errors
///
/// Returns an incompatible commitment/configuration, malformed opening stream,
/// failed authentication, or a terminal opening that violates either claim.
pub fn verify_with_basis<V: OpeningVerifier>(
    v: &mut V,
    config: &VerifierConfig,
    commitment: &Commitment<V::E, V::Root>,
    target: V::E,
    weight_at: impl WeightAt<V>,
) -> Result<(), WhirError> {
    let shape = commitment.shape;
    if !shape.valid()
        || shape.log_batch_size != config.initial_k()
        || config.log_inv_rates().first() != Some(&shape.log_inv_rate)
        || commitment.point.len() != shape.log_n
    {
        return Err(WhirError::CommitmentMismatch);
    }
    super::commit::verify_record_binding(v, commitment)?;
    let beta = v.sample();
    let target = v.mul_add(beta, commitment.value, target);
    let combined_weight = AnchoredWeight {
        caller: weight_at,
        shape,
        point: &commitment.point,
        beta,
    };
    verify_protocol_with_basis(
        v,
        config,
        shape.log_n,
        shape.n_lanes,
        target,
        commitment.root,
        combined_weight,
    )
}

/// The fold challenges arrive in round order, and the first `initial_k` rounds, the lane fold, bind the witness's top `initial_k` coordinates.
/// So the point is rotated left by `initial_k` before the weight sees it.
///
/// Per-level induced bases are never materialized: a level's enforced sum is recomputed from its opened rows, and its basis taken in closed form at the terminal point.
/// The L0 rows the proof stores are the committed lanes, `n_lanes` of them, which the caller derives from the announced layout.
///
/// # Errors
///
/// Returns a lane count a leaf cannot hold, a configuration that does not fit the witness, a malformed stream, or a terminal claim the opening does not reproduce.
pub(crate) fn verify_protocol_with_basis<V: OpeningVerifier>(
    v: &mut V,
    config: &VerifierConfig,
    log_n: usize,
    n_lanes: usize,
    target: V::E,
    root: V::Root,
    weight_at: impl WeightAt<V>,
) -> Result<(), WhirError> {
    WhirReplay::run(v, config, log_n, n_lanes, target, root, weight_at)
}

impl<E: Copy> Quad<E> {
    /// The next round's quadratic, its linear coefficient fixed by the running claim.
    fn recv<V: OpeningVerifier<E = E>>(v: &mut V, claim: E) -> Result<Self, TranscriptError> {
        let h = v.next_round_poly(3, claim, None)?;
        Ok(Self {
            c: h[0],
            b: h[1],
            a: h[2],
        })
    }

    fn eval<V: OpeningVerifier<E = E>>(self, v: &mut V, x: E) -> E {
        let u = v.mul_add(self.a, x, self.b);
        v.mul_add(u, x, self.c)
    }

    /// `self + s·other`.
    fn fold<V: OpeningVerifier<E = E>>(self, v: &mut V, other: Self, s: E) -> Self {
        Self {
            c: v.mul_add(s, other.c, self.c),
            b: v.mul_add(s, other.b, self.b),
            a: v.mul_add(s, other.a, self.a),
        }
    }
}

impl<E: Copy> Ood<E> {
    /// Draw an out-of-domain point, then read its value and its intro round.
    fn replay<V: OpeningVerifier<E = E>>(v: &mut V, n_vars: usize) -> Result<Self, TranscriptError> {
        let z = v.sample_vec(n_vars);
        let y = v.next_scalar()?;
        let intro = Quad::recv(v, y)?;
        Ok(Self { z, y, intro })
    }
}

fn replay_oods<V: OpeningVerifier>(v: &mut V, count: usize, n_vars: usize) -> Result<Vec<Ood<V::E>>, TranscriptError> {
    let mut oods = Vec::new();
    for _ in 0..count {
        oods.push(Ood::replay(v, n_vars)?);
    }
    Ok(oods)
}

#[inline]
fn level_factors<A: Arith>(v: &mut A, point: &[A::E], sks: &[F64]) -> Vec<(A::E, A::E)> {
    let mut lin = Vec::with_capacity(point.len().min(sks.len()));
    for i in 0..point.len().min(sks.len()) {
        let p = point[i];
        let sigma = sks[i];
        let inv = if sigma == F64(0) { F64(0) } else { sigma.inv() };
        lin.push((v.add_const(p, F192::ONE), v.mul_const(p, F192::from(inv))));
    }
    lin
}

#[inline]
fn query_product<A: Arith>(v: &mut A, mut s: A::E, lin: &[(A::E, A::E)], sks: &[F64]) -> A::E {
    let mut product = v.one();
    for (k, &(a, c)) in lin.iter().enumerate() {
        if k > 0 {
            // The subspace polynomials' recurrence `s_k = s_{k-1}^2 + s_{k-1}(v_{k-1}) s_{k-1}`.
            let u = v.mul_const(s, F192::from(sks[k - 1]));
            s = v.mul_add(s, s, u);
        }
        let f = v.mul_add(c, s, a);
        product = v.mul(product, f);
    }
    product
}

/// The level's induced basis at `point`: `sum_i w_i prod_k (1 + p_k (1 + s_k(q_i) / s_k(v_k)))`, `q_i` the query index in `K`.
fn level_basis_at<V: OpeningVerifier>(ctx: &LevelCtx<V::Query, V::E>, v: &mut V, point: &[V::E]) -> V::E {
    assert_eq!(point.len(), ctx.log_msg_cols, "a point of the level's cube");
    let sks = eval_sk_at_vks(ctx.log_msg_cols);
    // `1 + p (1 + s / sigma) = (1 + p) + (p / sigma) s`.
    let lin = level_factors(v, point, &sks);
    let mut acc = v.zero();
    for i in 0..ctx.queries.len().min(ctx.weights.len()) {
        let w = ctx.weights[i];
        let s = v.query_point(&ctx.queries[i]);
        let product = query_product(v, s, &lin, &sks);
        acc = v.mul_add(w, product, acc);
    }
    acc
}

#[inline]
fn levels_weight<V: OpeningVerifier>(
    v: &mut V,
    levels: &[LevelCtx<V::Query, V::E>],
    ris: &[V::E],
    tail: &[V::E],
) -> V::E {
    let mut weight = v.zero();
    let mut i = 0;
    while i < levels.len() {
        let ctx = &levels[i];
        let folded = ctx.log_msg_cols - tail.len();
        let mut point = ris[ctx.ris_start..ctx.ris_start + folded].to_vec();
        point.extend_from_slice(tail);
        let at = level_basis_at(ctx, v, &point);
        weight = v.mul_add(ctx.beta, at, weight);
        i += 1;
    }
    weight
}

#[inline]
const fn folded_coordinate<E: Copy>(prefix: &[E], tail: &[E], folded: usize, index: usize) -> E {
    if index < folded {
        prefix[index]
    } else {
        tail[index - folded]
    }
}

#[inline]
fn oods_weight<A: Arith>(v: &mut A, oods: &[OodCtx<A::E>], ris: &[A::E], tail: &[A::E], mut weight: A::E) -> A::E {
    let mut i = 0;
    while i < oods.len() {
        let ctx = &oods[i];
        let folded = ctx.z.len() - tail.len();
        let prefix = &ris[ctx.ris_start..ctx.ris_start + folded];
        let mut scalar = ctx.beta;
        let mut j = 0;
        while j < ctx.z.len() {
            let x = folded_coordinate(prefix, tail, folded, j);
            let s = v.add(ctx.z[j], x);
            scalar = v.times_one_plus(scalar, s);
            j += 1;
        }
        weight = v.add(weight, scalar);
        i += 1;
    }
    weight
}

impl QueryPhase {
    /// The batch's queries.
    fn sample<V: OpeningVerifier>(self, v: &mut V) -> Vec<V::Query> {
        v.sample_queries(self.depth, self.count)
    }
}

impl<R> Oracle<R> {
    /// The width of a query's index bits.
    const fn depth(&self) -> usize {
        self.log_msg_cols + self.log_inv_rate
    }

    /// Open each query's row of `E` elements, three words each.
    fn open_e_rows<V: OpeningVerifier<Root = R>>(
        &self,
        v: &mut V,
        queries: &[V::Query],
    ) -> Result<ExtRows<V::E>, TranscriptError> {
        let leaf_words = 3 << self.log_num_interleaved;
        let rows = v.open_rows(&self.root, self.depth(), queries, leaf_words, leaf_words)?;
        let mut out = Vec::with_capacity(rows.len());
        for words in rows {
            let len = words.len();
            let mut row = Vec::with_capacity(len / 3 + usize::from(len % 3 != 0));
            let mut i = 0;
            while i < len {
                row.push(v.e_of_limbs([words[i], words[i + 1], words[i + 2]]));
                i += 3;
            }
            out.push(row);
        }
        Ok(ExtRows(out))
    }
}

impl<'c, V: OpeningVerifier> WhirReplay<'c, V> {
    /// The succinct WHIR verifier.
    ///
    /// The caller's weight is evaluated once, at the terminal point indexed by witness coordinate.
    fn run(
        v: &mut V,
        config: &'c VerifierConfig,
        log_n: usize,
        n_lanes: usize,
        target: V::E,
        root: V::Root,
        weight_at: impl WeightAt<V>,
    ) -> Result<(), WhirError> {
        let initial_k = config.initial_k();
        let max = 1usize << initial_k;
        if n_lanes == 0 || n_lanes > max {
            return Err(WhirError::LaneCount { n_lanes, max });
        }
        let quad = Quad::recv(v, target)?;
        let mut w = Self {
            config,
            t_r: target,
            quad,
            ris: Vec::new(),
            levels: Vec::new(),
            oods: Vec::new(),
        };
        let mut n_current = log_n
            .checked_sub(initial_k)
            .ok_or(WhirError::InvalidShape { level: 0 })?;
        let lane_fold = w.fold_rounds(v, initial_k)?;
        let root_1 = v.next_root()?;
        let oods = replay_oods(v, config.ood_samples()[1], n_current)?;
        let phase = w.phase(0, n_current + config.log_inv_rates()[0]);
        // The proof stores the committed lanes, the image's tail; the image is lane-descending.
        let batch = Self::begin_query(v, phase)?;
        let sum = enforce_base(v, &root, phase, n_lanes, max, &lane_fold, &batch);
        w.finish_query(v, oods, n_current, batch, sum)?;

        let mut oracle = w.oracle(root_1, 0, n_current)?;
        let final_level = config.level_steps() - 1;
        let mut error = None;
        for i in 0..final_level {
            match w.middle_level(v, &oracle, n_current, i) {
                Ok((next, n)) => {
                    oracle = next;
                    n_current = n;
                }
                Err(err) => {
                    error = Some(err);
                    break;
                }
            }
        }
        if let Some(error) = error {
            return Err(error);
        }
        let k = config.level_ks()[final_level];
        if n_current < k {
            return Err(WhirError::InvalidShape { level: final_level });
        }
        let level_rs = w.fold_rounds(v, k)?;
        n_current -= k;
        w.last_level(v, &oracle, &level_rs, n_current, weight_at)
    }

    fn middle_level(
        &mut self,
        v: &mut V,
        oracle: &Oracle<V::Root>,
        mut n_current: usize,
        i: usize,
    ) -> Result<(Oracle<V::Root>, usize), WhirError> {
        let k = self.config.level_ks()[i];
        if n_current < k {
            return Err(WhirError::InvalidShape { level: i });
        }
        let level_rs = self.fold_rounds(v, k)?;
        n_current -= k;
        let root = v.next_root()?;
        let oods = replay_oods(v, self.config.ood_samples()[i + 2], n_current)?;
        let phase = self.phase(i + 1, oracle.depth());
        let batch = Self::begin_query(v, phase)?;
        let sum = enforce_ext(v, oracle, &level_rs, &batch);
        self.finish_query(v, oods, n_current, batch, sum)?;
        Ok((self.oracle(root, i + 1, n_current)?, n_current))
    }

    /// Level `level`'s query batch over indices of `depth` bits.
    fn phase(&self, level: usize, depth: usize) -> QueryPhase {
        QueryPhase {
            // The private config constructor bounds this by MAX_GRINDING_BITS.
            grinding: self.config.grinding_bits()[level] as u32,
            depth,
            count: self.config.queries()[level],
        }
    }

    /// The oracle a level's fold commits, on the variables left after it.
    fn oracle(&self, root: V::Root, level: usize, n_current: usize) -> Result<Oracle<V::Root>, WhirError> {
        let k = self.config.level_ks()[level];
        Ok(Oracle {
            root,
            log_num_interleaved: k,
            log_msg_cols: n_current.checked_sub(k).ok_or(WhirError::InvalidShape { level })?,
            log_inv_rate: self.config.log_inv_rates()[level + 1],
        })
    }

    /// `k` fold rounds: each draws a challenge, evaluates the running quadratic, and reads the next.
    fn fold_rounds(&mut self, v: &mut V, k: usize) -> Result<Vec<V::E>, TranscriptError> {
        let mut rs = Vec::with_capacity(k);
        for _ in 0..k {
            let ri = v.sample();
            self.t_r = self.quad.eval(v, ri);
            self.quad = Quad::recv(v, self.t_r)?;
            rs.push(ri);
        }
        self.ris.extend_from_slice(&rs);
        Ok(rs)
    }

    /// Begin a query batch and enter its row scope after grinding and sampling.
    fn begin_query(v: &mut V, phase: QueryPhase) -> Result<QueryBatch<V::Query, V::E>, TranscriptError> {
        v.grind_check(phase.grinding)?;
        let queries = phase.sample(v);
        let lambda = v.sample();
        let weights = v.powers(lambda, phase.count);
        v.begin_scope(fiat_shamir::arith::Stage::Rows);
        Ok(QueryBatch {
            queries,
            weights,
            lambda,
        })
    }

    /// Leave the row scope before propagating an opening error, then batch the level's claims.
    fn finish_query(
        &mut self,
        v: &mut V,
        oods: Vec<Ood<V::E>>,
        log_msg_cols: usize,
        batch: QueryBatch<V::Query, V::E>,
        enforced: Result<V::E, TranscriptError>,
    ) -> Result<(), TranscriptError> {
        v.end_scope();
        let sum = enforced?;
        let QueryBatch {
            queries,
            weights,
            lambda,
        } = batch;
        let intro = Quad::recv(v, sum)?;

        // The OOD claims, then the query batch, each at the next power of the level's challenge.
        let ris_start = self.ris.len();
        let mut scalar = v.one();
        for ood in oods {
            scalar = v.mul(scalar, lambda);
            self.quad = self.quad.fold(v, ood.intro, scalar);
            self.t_r = v.mul_add(scalar, ood.y, self.t_r);
            self.oods.push(OodCtx {
                z: ood.z,
                ris_start,
                beta: scalar,
            });
        }
        scalar = v.mul(scalar, lambda);
        self.quad = self.quad.fold(v, intro, scalar);
        self.t_r = v.mul_add(scalar, sum, self.t_r);
        self.levels.push(LevelCtx {
            log_msg_cols,
            queries,
            weights,
            ris_start,
            beta: scalar,
        });
        Ok(())
    }

    /// The last level: its residual polynomial, its query batch, the residual rounds, then the terminal check.
    fn last_level(
        mut self,
        v: &mut V,
        oracle: &Oracle<V::Root>,
        level_rs: &[V::E],
        n_current: usize,
        weight_at: impl WeightAt<V>,
    ) -> Result<(), WhirError> {
        let yr = v.next_scalars(1 << n_current)?;
        let phase = self.phase(self.config.level_steps(), oracle.depth());
        let batch = Self::begin_query(v, phase)?;
        let sum = enforce_ext(v, oracle, level_rs, &batch);
        self.finish_query(v, Vec::new(), n_current, batch, sum)?;
        let mut ris_tail = Vec::with_capacity(n_current);
        for j in 0..n_current {
            let ri = v.sample();
            self.t_r = self.quad.eval(v, ri);
            ris_tail.push(ri);
            if j + 1 < n_current {
                self.quad = Quad::recv(v, self.t_r)?;
            }
        }
        {
            v.begin_scope(fiat_shamir::arith::Stage::Terminal);
            let scoped_result = self.terminal(v, &yr, &ris_tail, weight_at);
            v.end_scope();
            scoped_result
        }
    }

    /// `weight · <yr, eq(ris_tail)> = t_r`, the weight every level's basis, every OOD claim and the caller's at the full point.
    fn terminal(
        &self,
        v: &mut V,
        yr: &[V::E],
        ris_tail: &[V::E],
        weight_at: impl WeightAt<V>,
    ) -> Result<(), WhirError> {
        let weight = levels_weight(v, &self.levels, &self.ris, ris_tail);
        let weight = oods_weight(v, &self.oods, &self.ris, ris_tail, weight);
        // `ris ++ ris_tail` is the fold challenges in ROUND order, and the first `initial_k` rounds are the lane fold,
        // which binds the committed witness's TOP `initial_k` variables (lane `l` is the stack block `q[l·H ..)`).
        // Rotating by `initial_k` re-indexes the point by witness variable, so the caller's weight is in witness coordinates.
        let mut full_point = self.ris.clone();
        full_point.extend_from_slice(ris_tail);
        full_point.rotate_left(self.config.initial_k());
        let caller = weight_at.evaluate(v, &full_point);
        let weight = v.add(weight, caller);
        let folded_yr = v.mle(yr, ris_tail);
        let lhs = v.mul(weight, folded_yr);
        v.ensure_eq(lhs, self.t_r, || WhirError::TerminalMismatch)
    }
}

/// The level-0 enforced sum over `K` rows: `sum_i w_i <row_i, eq(v, .)>`.
///
/// Each row's inner product is its own, so the first query's weight, one, costs no product in rows.
fn base_enforced_sum<V: OpeningVerifier>(rows: &BaseRows<V::K>, v: &mut V, point: &[V::E], weights: &[V::E]) -> V::E {
    let rows = &rows.0;
    let eq = v.eq_table_prefix(point, rows[0].len());
    let zero = v.zero();
    let mut acc = zero;
    for i in 0..rows.len().min(weights.len()) {
        let row = &rows[i];
        let mut inner = zero;
        for j in 0..eq.len().min(row.len()) {
            inner = v.mul_k_add(eq[j], row[j], inner);
        }
        acc = v.mul_add(weights[i], inner, acc);
    }
    acc
}

/// A later level's enforced sum over `E` rows: `sum_l eq(v, l) sum_i w_i row_i[l]`.
fn ext_enforced_sum<A: Arith>(rows: &ExtRows<A::E>, v: &mut A, point: &[A::E], weights: &[A::E]) -> A::E {
    let rows = &rows.0;
    let eq = v.eq_table_prefix(point, rows[0].len());
    let zero = v.zero();
    let mut acc = zero;
    for (l, &e) in eq.iter().enumerate() {
        let mut column = zero;
        for i in 0..rows.len().min(weights.len()) {
            column = v.mul_add(weights[i], rows[i][l], column);
        }
        acc = v.mul_add(e, column, acc);
    }
    acc
}
