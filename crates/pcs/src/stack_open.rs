// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Stacked batch-mixed opening for the F64-committed PCS.
//!
//! The committed witness is a stack of `2^log_n` [`F64`] words (committed via
//! [`super::whir::commit`], which only encodes and only transmits the lane blocks
//! that carry data: every claim lives inside them and the weight is zero past
//! them), and one WHIR run discharges
//!
//! - **point claims** ([`StackClaim`]): multilinear evaluations whose weight is a sum of aligned [`Term`]s, each `scale * eq(point[..n_vars], j)` at the words `offset + slot + j * 2^stride_log`.
//!   One term over a whole aligned slice is a plain evaluation of that slice (`slot` and `stride_log` freeze the low in-block coords of a packed column).
//!   Several scaled terms are a column whose rows are committed in several aligned pieces (a jagged column), the scales being what the claim's point puts on each piece.
//! - **ring-switched claims** (one region per packed column, each circuit committing its own): bit-MLE evaluation claims
//!   on the packed region, committed whole or in aligned [`Piece`]s,
//!   combined into ONE family, whose 64 slices are the claims' slices weighted by
//!   powers of one challenge `gamma_rs`, and ring-switched once to an inner-product
//!   claim `<q, rs_eq_ind> = target` against the transparent E-valued weight
//!   `rs_eq_ind`, claim `j` contributing `Phi(gamma_rs^j * s_{j,t} * eq(r_j[..n_t], .))` on piece `t` of its region, `s_{j,t}` the claim's scale on the piece
//!   (doc `leanvm` Annex A, `rs:family`). The claims' points need not be related.
//!
//! All claims are lambda-folded into ONE combined weight `b_stack` over the
//! whole stack plus one `target`, then proved by
//! [`super::whir::recursive_prover_with_basis`]. The verifier replays
//! the ring switch succinctly (the family's target, with no dense `rs_eq_ind`) and drives
//! [`super::whir::recursive_verifier_with_basis_succinct`] with a
//! terminal evaluator that reconstructs `MLE(b_stack)` once, at the final fold
//! point, using closed-form eq / stride selectors and the family's weight.
//!
//! ## Transcript order (identical on both sides)
//!
//! Sample the family's challenge `gamma_rs`, then the shared linear map, then one batching challenge for the family and the point claims, then run WHIR. The caller already bound each claim's slices and value through the transcript, so none is observed again here.
//!
//! ## The combined weight
//!
//! A term or a piece over `2^n` words at `offset` has selector coords `sel = offset >> n`, and at a full-stack point `x = (x_lo, x_hi)` (split at `n`, LSB-first) it is its low-dimensional weight at `x_lo` times `eq(sel, x_hi)`.
//! So, with `t` running over the pieces of claim `j`'s region and over the terms of point claim `i`,
//!
//! ```text
//! b(x) = sum_j sum_t eq(sel_t, x_hi) * MLE(Phi(gamma_rs^j * s_{j,t} * eq(r_j[..n_t], .)))(x_lo)
//!      + sum_i lambda^(1 + i) * sum_t scale_t * eq(sel_t, x_hi) * eq(claim_i-term, x_lo)
//! ```
//!
//! which is exactly what the dense `b_stack` scatter produces (each piece's and term's
//! weight lives on its aligned slice, so scattering the low-dimensional eq /
//! rs_eq_ind tensor at the slice offset IS multiplying by the boolean
//! selector eq).
//!
//! The family takes `lambda^0` and the point claims the next powers of ONE
//! challenge, as the table sumcheck's xi ranges do (the batching step of `thm:rbr`).
//! A claim's terms share its power.
//! `lambda` is drawn after the map, so the family's error is fixed by then and is the
//! constant term of the batched error, which is what lets it take `lambda^0 = 1`.

use super::pack::PACKING_WIDTH;
use super::ring_switch;
use super::ring_switch::{DeferredWeight, RsEqQuery};
use super::whir::{Basis, ProverConfig, ProverData, VerifierConfig, WhirError, recursive_verifier_with_basis_succinct};
use crate::merkle::Hash;
use basis::StackWeight;
use fiat_shamir::transcript::{Challenger, Receiver, Transmitter};
use primitives::bit_fold::F192Map;
use primitives::field::{F64, F192, powers};
use std::cmp::Reverse;

mod basis;

// ---------------------------------------------------------------------------
// Claim types
// ---------------------------------------------------------------------------

/// One aligned piece of a [`StackClaim`]'s weight: `scale * eq(point[..n_vars], j)` at the word `offset + slot + j * 2^stride_log` for every `j < 2^n_vars`.
///
/// - The claim fixes `point`, `slot` and `stride_log`.
/// - `offset` must be a multiple of `2^(stride_log + n_vars)`, and `n_vars` at most the claim's point length.
///
/// Its scale is a value, or whatever a verifier holds it as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term<E = F192> {
    /// The first word of the term's block.
    pub offset: usize,
    /// The claim's point coordinates the term weighs.
    pub n_vars: usize,
    /// The factor on the term's equality weight.
    pub scale: E,
}

/// An owning point claim folded into the stacked mixed opening: the stack against the sum of its terms' weights is `value`.
///
/// - The low `stride_log` in-block coords of every term are frozen to `slot`'s bits, which is how a claim reads one port of a packed column; `slot < 2^stride_log`.
/// - One term of scale one over a whole aligned slice is a plain evaluation of that slice.
/// - Several scaled terms are a column committed in aligned pieces (a jagged column), the scales being what the claim's point puts on each piece.
///
/// Its point, scales and value are values, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackClaim<E = F192> {
    /// The point, at least as long as every term's `n_vars`.
    pub point: Vec<E>,
    /// The in-block word every term reads.
    pub slot: usize,
    /// The base-two logarithm of the words between two reads.
    pub stride_log: usize,
    /// The weight's aligned pieces.
    pub terms: Vec<Term<E>>,
    /// The value the claim states.
    pub value: E,
}

impl<E> StackClaim<E> {
    /// `eq(low_point, .)` on the aligned slice `[offset, offset + 2^|low_point|)`, `offset` a multiple of `2^|low_point|`.
    ///
    /// Its one term takes the scale `one`, the unit of whatever holds the elements.
    pub fn point(offset: usize, low_point: Vec<E>, value: E, one: E) -> Self {
        Self::strided(offset, 0, 0, low_point, value, one)
    }

    /// `eq(point, j)` at `offset + slot + j * 2^stride_log`: a [`Self::point`] whose low `stride_log` coords are `slot`'s bits, folded in `O(2^|point|)`.
    ///
    /// `offset` must be a multiple of `2^(stride_log + |point|)` and `slot < 2^stride_log`; its one term takes the scale `one`.
    pub fn strided(offset: usize, slot: usize, stride_log: usize, point: Vec<E>, value: E, one: E) -> Self {
        Self {
            terms: vec![Term {
                offset,
                n_vars: point.len(),
                scale: one,
            }],
            point,
            slot,
            stride_log,
            value,
        }
    }

    /// The b_stack range `term` is supported on.
    ///
    /// Every range is an aligned dyadic interval (the offset asserts below), so two of them are nested or disjoint and never partially overlap.
    /// A strided term reports its whole block rather than the strided positions inside it.
    /// That is conservative in the direction that matters: it only ever makes a later claim accumulate.
    pub const fn range(&self, term: &Term<E>) -> (usize, usize) {
        (term.offset, term.offset + (1usize << (self.stride_log + term.n_vars)))
    }
}

/// One ring-switched claim's slices: its 64 bit-slice values at a suffix point.
///
/// - The suffix point is at least as long as every piece of the claim's region.
/// - Slice `i` is the multilinear extension of bit `i` of the region's words, each piece weighed by the claim's scale on it, at that point.
/// - The caller sends and checks the slices itself, so the opening only binds them to the commitment.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceClaim<E = F192> {
    /// The point.
    pub suffix_point: Vec<E>,
    /// The 64 slice values at the point.
    pub s_hat_v: Vec<E>,
}

/// One aligned piece of a ring-switched region: the `2^n_vars` words from `offset`, a multiple of that.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Piece {
    /// The piece's first word.
    pub offset: usize,
    /// The base-two logarithm of the piece's length in words.
    pub n_vars: usize,
}

impl Piece {
    /// The word past the piece.
    pub const fn end(&self) -> usize {
        self.offset + (1usize << self.n_vars)
    }
}

/// A ring-switched claim on a region: its slices, and what its point puts on each piece of the region.
///
/// Piece `t` of `2^n_t` words weighs `scales[t] * eq(suffix_point[..n_t], .)`.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingClaim<E = F192> {
    /// The claim's point and slices.
    pub slices: SliceClaim<E>,
    /// One scale per piece of the region, in the region's order.
    pub scales: Vec<E>,
}

/// A ring-switched region of the committed stack, the aligned pieces it is committed in, and the claims on it.
///
/// A packed column committed whole is one piece of scale one ([`Self::whole`]); a jagged column is committed in several pieces.
/// Prover and verifier describe a region with the same data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitch<E = F192> {
    /// The region's pieces.
    pub pieces: Vec<Piece>,
    /// The claims on the region.
    pub claims: Vec<RingClaim<E>>,
}

impl<E: Copy> RingSwitch<E> {
    /// The aligned slice `[offset, offset + 2^n_vars)` as one piece, each claim weighing it at the scale `one`, the unit of whatever holds the elements.
    pub fn whole(offset: usize, n_vars: usize, claims: Vec<SliceClaim<E>>, one: E) -> Self {
        Self {
            pieces: vec![Piece { offset, n_vars }],
            claims: (claims.into_iter())
                .map(|slices| RingClaim {
                    slices,
                    scales: vec![one],
                })
                .collect(),
        }
    }
}

// ---------------------------------------------------------------------------
// Shared claim checks / evaluation
// ---------------------------------------------------------------------------

/// The statement's invariants, the same on both sides: every term and piece aligned to its size and inside the first `len` words, every point as long as what it weighs, and one scale per piece.
fn check_statement<E>(point_claims: &[StackClaim<E>], rings: &[RingSwitch<E>], len: usize) {
    for claim in point_claims {
        assert!(
            claim.slot < 1usize << claim.stride_log,
            "claim slot must fit the stride"
        );
        for term in &claim.terms {
            assert!(
                term.n_vars <= claim.point.len(),
                "a term weighs a prefix of its claim's point"
            );
            let (start, end) = claim.range(term);
            assert!(start.is_multiple_of(end - start), "a term is aligned to its size");
            assert!(end <= len, "every claim must live inside the committed lanes");
        }
    }
    for ring in rings {
        for piece in &ring.pieces {
            assert!(
                piece.offset.is_multiple_of(1usize << piece.n_vars),
                "a piece is aligned to its size"
            );
            assert!(piece.end() <= len, "a ring-switched piece must fit inside the stack");
        }
        for claim in &ring.claims {
            assert_eq!(
                claim.scales.len(),
                ring.pieces.len(),
                "a ring claim scales each piece of its region"
            );
            assert!(
                (ring.pieces.iter()).all(|piece| piece.n_vars <= claim.slices.suffix_point.len()),
                "a piece weighs a prefix of its claim's point"
            );
        }
    }
}

/// `eq(bits, x)` for the integer `bits`, least significant bit first.
fn eq_bits(bits: usize, x: &[F192]) -> F192 {
    (x.iter().enumerate()).fold(F192::ONE, |e, (k, &xi)| {
        e * if (bits >> k) & 1 == 1 { xi } else { F192::ONE + xi }
    })
}

/// The claim's weight at an arbitrary point `x` of the full stack cube: every term's full point is `[slot_bits, point[..n_vars], sel_bits]`, none materialized.
fn stack_claim_weight_at(claim: &StackClaim, x: &[F192]) -> F192 {
    let s = claim.stride_log;
    let longest = claim.terms.iter().map(|t| t.n_vars).max().unwrap_or(0);
    // `eq(point[..n], x[s..s + n])` at index `n`, one factor `1 + p + x` each.
    let mut prefix_eq = Vec::with_capacity(longest + 1);
    prefix_eq.push(F192::ONE);
    for (&p, &xi) in claim.point[..longest].iter().zip(&x[s..]) {
        prefix_eq.push(prefix_eq[prefix_eq.len() - 1] * (F192::ONE + p + xi));
    }
    let terms = claim.terms.iter().fold(F192::ZERO, |acc, t| {
        let block = s + t.n_vars;
        acc + t.scale * prefix_eq[t.n_vars] * eq_bits(t.offset >> block, &x[block..])
    });
    eq_bits(claim.slot, &x[..s]) * terms
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Open the committed `F64` stack: discharge every `point_claims` weighted
/// evaluation AND the ring-switched claims (`rings`) in ONE WHIR
/// run, reusing the caller's [`super::whir::commit`] output as L0.
///
/// `stack` is the committed message (the caller retains it; it is not stored in
/// [`ProverData`]): the `2^log_n`-word stack truncated to the lane blocks that
/// carry data, so every claim must live inside it and the padding past it is
/// exactly the weight's zero region. `config.initial_k` / `config.log_inv_rates[0]`
/// must match the commit's `log_batch_size` / `log_inv_rate` (enforced by shape
/// asserts inside the WHIR prover).
pub fn open_batch_mixed_whir_stacked(
    ps: &mut impl Transmitter,
    log_n: usize,
    stack: &[F64],
    prover_data: &ProverData,
    config: &ProverConfig,
    point_claims: &[StackClaim],
    rings: &[RingSwitch],
) {
    check_statement(point_claims, rings, stack.len());
    let n_rs: usize = rings.iter().map(|ring| ring.claims.len()).sum();
    assert!(n_rs > 0, "stacked PCS opening carries at least one ring-switched claim");
    let span = tracing::info_span!("Ring switch").entered();

    // 1. Every claim's slices (the caller bound them upstream), combined into the
    //    family by powers of one challenge, then one shared linear map.
    let family = RingFamily::sample(ps);
    let map = F192Map::new(&family.coordinate_weights());

    // 2. The ONE batching challenge: the family takes its first power, the point claims the rest. Nothing is
    //    observed first: every claim value reached the caller through a binding stream read, so the challenge
    //    already depends on all of them (`leanvm_core::pcs::open`).
    let lambdas = powers(ps.sample(), 1 + point_claims.len());
    let lambdas_pd = &lambdas[1..];
    // Each piece with its claims' weights, claim `j` at `gamma_rs^j` times its scale on the piece.
    let gammas = powers(family.gamma_rs(), n_rs);
    let mut first = 0;
    let mut ring_weights: Vec<(Piece, Vec<DeferredWeight<'_>>)> = Vec::new();
    for ring in rings {
        let gammas = &gammas[first..first + ring.claims.len()];
        first += ring.claims.len();
        for (t, piece) in ring.pieces.iter().enumerate() {
            let weights = (ring.claims.iter().zip(gammas))
                .map(|(claim, &gamma)| {
                    let point = &claim.slices.suffix_point[..piece.n_vars];
                    ring_switch::deferred_weight(point, gamma * claim.scales[t], &map)
                })
                .collect();
            ring_weights.push((*piece, weights));
        }
    }
    drop(span);

    // 3. Combined target and lifted stack weight b_stack: each claim's share of
    //    the family's weight scattered at its region's pieces, plus the point-claim
    //    terms' eq tensors scattered at their offsets.
    let slices = rings.iter().flat_map(|ring| &ring.claims);
    let target = family.target(slices.map(|claim| claim.slices.s_hat_v.as_slice()))
        + point_claims
            .iter()
            .zip(lambdas_pd)
            .fold(F192::ZERO, |sum, (claim, &lambda)| sum + lambda * claim.value);

    // The lifted weight is never stored.
    //
    //     first pass:  each chunk is filled, then feeds the first lane rounds' sums while hot
    //     first fold:  each chunk is filled again, then folded by those rounds' challenges
    //
    // Filling costs less than writing the weight out and reading it back.
    let lane_block = 1usize << (log_n - config.initial_k());
    let weight = StackWeight::new(stack.len(), lane_block, point_claims, lambdas_pd, &ring_weights);
    let fill = |start: usize, dst: &mut [F192]| weight.fill(start, dst);
    let initial = tracing::info_span!("Basis")
        .in_scope(|| super::whir::initial_rounds(stack, lane_block, config.initial_k(), &Basis::Virtual(&fill)));

    // 4. One WHIR over the full stack against the combined claim (the
    //    stack is borrowed by the prover; no copy).
    super::whir::recursive_prover_with_prepared_basis(
        config,
        log_n,
        stack,
        Basis::Virtual(&fill),
        target,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        Some(initial),
        ps,
    );
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/// Verifier mirror of [`open_batch_mixed_whir_stacked`]: replay the
/// ring-switch reductions succinctly, recompute the combined target, then
/// drive the succinct WHIR verifier with one terminal evaluation of the
/// lifted weight. `log_n` is the committed stack's log size in F64 words and
/// `root` the L0 commitment root ([`super::whir::Commitment::root`]).
pub fn verify_opening_batch_mixed_whir_stacked(
    vs: &mut impl Receiver,
    config: &VerifierConfig,
    log_n: usize,
    n_lanes: usize,
    root: &Hash,
    point_claims: &[StackClaim],
    rings: &[RingSwitch],
) -> Result<(), WhirError> {
    let n_rs: usize = rings.iter().map(|ring| ring.claims.len()).sum();
    assert!(n_rs > 0, "stacked PCS opening carries at least one ring-switched claim");
    // Caller (statement) invariants: panic on misuse, like the extension-field layer.
    // Every term's and piece's support must lie inside the cube, or its selector coords
    // would run off the end of the fold point (mirror of the opener's own bound).
    check_statement(point_claims, rings, 1usize << log_n);

    // 1. The family: every claim arrives with its 64 slices, bound upstream by the
    //    caller, so nothing is read here; they combine by powers of one challenge.
    //    Then sample one shared map.
    let family = RingFamily::sample(vs);

    // 2. The one batching challenge (see the opener: the caller already bound the claim values),
    //    the family taking its first power.
    let lambdas = powers(vs.sample(), 1 + point_claims.len());
    let lambdas_pd = &lambdas[1..];
    let slices = rings
        .iter()
        .flat_map(|ring| &ring.claims)
        .map(|claim| claim.slices.s_hat_v.as_slice());
    let mut target = family.target(slices);
    for (claim, g) in point_claims.iter().zip(lambdas_pd.iter()) {
        target += *g * claim.value;
    }

    // 3. Evaluate the lifted weight once, at the terminal sumcheck point.
    let eval_b_at = |x: &[F192]| -> F192 {
        let point_part = (point_claims.iter().zip(lambdas_pd)).fold(F192::ZERO, |acc, (claim, &lambda)| {
            acc + lambda * stack_claim_weight_at(claim, x)
        });
        family.weight(rings, x) + point_part
    };

    recursive_verifier_with_basis_succinct(config, log_n, n_lanes, target, root, eval_b_at, vs)
}

/// The ring switch's one family per opening: claim `j` scaled by `gamma_rs^j`, then one map `Phi` for all.
///
/// Both sides draw `gamma_rs` once every claim's slices are bound, then the map's six challenges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RingFamily {
    gamma_rs: F192,
    map_challenges: [F192; ring_switch::COMPOSITION_SHIFTS.len()],
}

impl RingFamily {
    /// The family at its challenges.
    pub const fn new(gamma_rs: F192, map_challenges: [F192; ring_switch::COMPOSITION_SHIFTS.len()]) -> Self {
        Self {
            gamma_rs,
            map_challenges,
        }
    }

    /// Draw the family's challenges: `gamma_rs`, then the map's.
    pub fn sample(ch: &mut impl Challenger) -> Self {
        let gamma_rs = ch.sample();
        Self::new(gamma_rs, ring_switch::sample_map_challenges(ch))
    }

    /// The challenge `gamma_rs` whose powers scale the claims.
    pub const fn gamma_rs(&self) -> F192 {
        self.gamma_rs
    }

    /// The map's weight on each of the 192 coordinates.
    fn coordinate_weights(&self) -> Vec<F192> {
        ring_switch::build_coordinate_weights(&self.map_challenges)
    }

    /// The family's target `sum_i x^i Phi(s_i)`, its slices `s_i = sum_j gamma_rs^j s_{j,i}` over the claims in order.
    ///
    /// # Panics
    ///
    /// If a claim does not carry 64 slices.
    pub fn target<'s>(&self, slices: impl IntoIterator<Item = &'s [F192]>) -> F192 {
        let mut family = [F192::ZERO; PACKING_WIDTH];
        let mut scale = F192::ONE;
        for claim in slices {
            assert_eq!(claim.len(), PACKING_WIDTH, "a ring-switched claim has 64 slices");
            for (f, &s) in family.iter_mut().zip(claim) {
                *f += scale * s;
            }
            scale *= self.gamma_rs;
        }
        ring_switch::verify_finish(&family, &self.coordinate_weights())
    }

    /// The family's weight at a point `x` of the stack cube: `sum_j sum_t eq(sel_t, x_hi) MLE(Phi(gamma_rs^j s_{j,t} eq(r_j[..n_t], .)))(x_lo)`.
    ///
    /// Claim `j` is the `j`-th claim across the regions in order, `t` runs over its region's pieces, `sel_t` a piece's selector bits and `s_{j,t}` the claim's scale on it.
    ///
    /// - The Frobenius moves onto `x`, so one precomputed query serves every claim.
    /// - Claims whose points are prefixes of one another share one pass over the longest, which serves each piece's prefix too.
    /// - The claims of one region add their scaled terms on each piece and close once per piece.
    ///
    /// # Panics
    ///
    /// If a piece is longer than `x` or than a claim's point, or a claim does not scale each piece of its region.
    pub fn weight(&self, rings: &[RingSwitch], x: &[F192]) -> F192 {
        let n_rs: usize = rings.iter().map(|ring| ring.claims.len()).sum();
        let gammas = powers(self.gamma_rs, n_rs);
        let max_vars = (rings.iter().flat_map(|ring| &ring.pieces))
            .map(|piece| piece.n_vars)
            .max()
            .unwrap_or(0);
        let rs_query = RsEqQuery::new(&self.map_challenges, &x[..max_vars]);
        let mut terms: Vec<Vec<[F192; ring_switch::LINEARIZED_TERMS]>> = (rings.iter())
            .map(|ring| vec![[F192::ZERO; ring_switch::LINEARIZED_TERMS]; ring.pieces.len()])
            .collect();
        for group in PrefixGroup::of(rings) {
            let at = ring_switch::rs_eq_prefix_terms(group.lead, &rs_query, &group.lengths);
            for member in group.members {
                let scale = gammas[member.claim] * rings[member.ring].claims[member.ring_claim].scales[member.piece];
                for (term, &t) in terms[member.ring][member.piece].iter_mut().zip(&at[member.length]) {
                    *term += scale * t;
                }
            }
        }
        let pieces = (rings.iter().zip(&terms)).flat_map(|(ring, terms)| ring.pieces.iter().zip(terms));
        pieces.fold(F192::ZERO, |acc, (piece, terms)| {
            acc + eq_bits(piece.offset >> piece.n_vars, &x[piece.n_vars..]) * ring_switch::close_rs_eq(terms)
        })
    }
}

/// Ring claims whose suffix points are all prefixes of the longest, `lead`.
///
/// A claim's point counts up to its region's longest piece, the most of it the weight reads.
/// Its elements are values, or whatever a verifier holds them as: two points are prefixes of one another when their elements are equal.
#[derive(Clone, Debug)]
pub struct PrefixGroup<'a, E = F192> {
    /// The longest point.
    pub lead: &'a [E],
    /// The distinct prefix lengths its claims' pieces sit at.
    pub lengths: Vec<usize>,
    /// One member per claim and piece of the claim's region.
    pub members: Vec<PrefixMember>,
}

/// One piece of one claim of a prefix group: the claim's weight on that piece.
#[derive(Clone, Copy, Debug)]
pub struct PrefixMember {
    /// Its claim's index across every ring, which picks the claim's power of `gamma_rs`.
    pub claim: usize,
    /// Its ring.
    pub ring: usize,
    /// Its claim's index among the ring's claims.
    pub ring_claim: usize,
    /// Its piece's index among the ring's pieces, which picks the claim's scale on it.
    pub piece: usize,
    /// Its entry in the group's lengths: the piece's `n_vars`.
    pub length: usize,
}

impl<'a, E: PartialEq> PrefixGroup<'a, E> {
    /// Every ring claim in a group whose lead point it is a prefix of, longest points first, with a member for each piece of its region.
    ///
    /// # Panics
    ///
    /// If a piece is longer than a claim's point on its region.
    pub fn of(rings: &'a [RingSwitch<E>]) -> Vec<Self> {
        let mut claims: Vec<(usize, usize, usize, &'a [E])> = Vec::new();
        for (r, ring) in rings.iter().enumerate() {
            let used = ring.pieces.iter().map(|piece| piece.n_vars).max().unwrap_or(0);
            for (c, claim) in ring.claims.iter().enumerate() {
                claims.push((claims.len(), r, c, &claim.slices.suffix_point[..used]));
            }
        }
        claims.sort_by_key(|&(_, _, _, point)| Reverse(point.len()));
        let mut groups: Vec<Self> = Vec::new();
        for (claim, ring, ring_claim, point) in claims {
            let g = groups
                .iter()
                .position(|g| g.lead.starts_with(point))
                .unwrap_or_else(|| {
                    groups.push(Self {
                        lead: point,
                        lengths: Vec::new(),
                        members: Vec::new(),
                    });
                    groups.len() - 1
                });
            let group = &mut groups[g];
            for (piece, &Piece { n_vars, .. }) in rings[ring].pieces.iter().enumerate() {
                let length = group.lengths.iter().position(|&n| n == n_vars).unwrap_or_else(|| {
                    group.lengths.push(n_vars);
                    group.lengths.len() - 1
                });
                group.members.push(PrefixMember {
                    claim,
                    ring,
                    ring_claim,
                    piece,
                    length,
                });
            }
        }
        groups
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring_switch::tests::{fold_dense, s_hat_v_reference};
    use crate::whir::{INITIAL_BASIS_CHUNK, commit, inner_product_base_ext};
    use crate::whir_config::tests::{default_config, test_config_for};
    use basis::StackWeight;
    use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
    use primitives::multilinear::eq_table;
    use primitives::test_util::Rng;

    const DOMAIN: &[u8] = b"stack-open-test";

    /// The 64 slices of a ring claim at `suffix_point` with `scales` on `pieces`: each piece's slices at its prefix of the point, scaled.
    fn piece_slices(stack: &[F64], pieces: &[Piece], suffix_point: &[F192], scales: &[F192]) -> Vec<F192> {
        let mut slices = vec![F192::ZERO; PACKING_WIDTH];
        for (piece, &scale) in pieces.iter().zip(scales) {
            let words = &stack[piece.offset..piece.end()];
            for (s, v) in slices
                .iter_mut()
                .zip(s_hat_v_reference(words, &suffix_point[..piece.n_vars]))
            {
                *s += scale * v;
            }
        }
        slices
    }

    #[test]
    fn fused_basis_matches_dense_weights() {
        let mut rng = Rng::new(0xBA515);
        for (lane_vars, lanes) in [(6usize, 1usize), (6, 3), (10, 15), (10, 37)] {
            let lane_block = 1 << lane_vars;
            let stack: Vec<F64> = (0..lanes * lane_block).map(|_| F64(rng.next_u64())).collect();
            let qflock_vars = lane_vars + usize::from(lanes > 1);
            let qflock_len = 1 << qflock_vars;
            let offset = if stack.len() >= 2 * qflock_len { qflock_len } else { 0 };
            // A region committed whole, and the same region in two pieces at its two ends, as a jagged column's.
            let whole = [Piece {
                offset,
                n_vars: qflock_vars,
            }];
            let split = [
                Piece {
                    offset,
                    n_vars: qflock_vars - 1,
                },
                Piece {
                    offset: offset + qflock_len - 1,
                    n_vars: 0,
                },
            ];
            let map = F192Map::new(&rng.ext_vec(192));
            // The weight reads only the points and the scales: two claims on each region.
            let ring_weights: Vec<(Piece, Vec<DeferredWeight<'_>>)> = [&whole[..], &split[..]]
                .into_iter()
                .flat_map(|pieces| {
                    let points = [rng.ext_vec(qflock_vars), rng.ext_vec(qflock_vars)];
                    (pieces.iter().map(|piece| {
                        let weights = (points.iter())
                            .map(|point| ring_switch::deferred_weight(&point[..piece.n_vars], rng.ext(), &map))
                            .collect();
                        (*piece, weights)
                    }))
                    .collect::<Vec<_>>()
                })
                .collect();
            let mut claims: Vec<_> = [
                (offset, qflock_vars),
                ((lanes - 1) * lane_block, lane_vars),
                (8, 3),
                (0, 0),
            ]
            .into_iter()
            .map(|(offset, vars)| StackClaim::point(offset, rng.ext_vec(vars), rng.ext(), F192::ONE))
            .collect();
            for stride_log in [0, 1, 3, qflock_vars - 1, qflock_vars] {
                claims.push(StackClaim::strided(
                    offset,
                    (1 << stride_log) - 1,
                    stride_log,
                    rng.ext_vec(qflock_vars - stride_log),
                    rng.ext(),
                    F192::ONE,
                ));
            }
            // A claim of two scaled pieces, plain and strided.
            for stride_log in [0, 1] {
                let mut jagged = StackClaim::strided(offset, stride_log, stride_log, Vec::new(), rng.ext(), F192::ONE);
                jagged.point = rng.ext_vec(qflock_vars - stride_log);
                jagged.terms = vec![
                    Term {
                        offset,
                        n_vars: qflock_vars - stride_log - 1,
                        scale: rng.ext(),
                    },
                    Term {
                        offset: offset + qflock_len - (1 << stride_log),
                        n_vars: 0,
                        scale: rng.ext(),
                    },
                ];
                claims.push(jagged);
            }
            let lambdas = rng.ext_vec(claims.len());
            // Oracle: the dense weight written out naively, one eq entry at a
            // time, so it shares no code with the fused build under test.
            let mut expected = vec![F192::ZERO; stack.len()];
            for (piece, weights) in &ring_weights {
                ring_switch::combine_deferred_chunk(weights, 0, &mut expected[piece.offset..piece.end()]);
            }
            for (claim, &lambda) in claims.iter().zip(&lambdas) {
                for term in &claim.terms {
                    let point = &claim.point[..term.n_vars];
                    for j in 0..1usize << point.len() {
                        let w = point.iter().enumerate().fold(lambda * term.scale, |w, (i, &p_i)| {
                            w * if (j >> i) & 1 == 1 { p_i } else { F192::ONE + p_i }
                        });
                        expected[term.offset + claim.slot + (j << claim.stride_log)] += w;
                    }
                }
            }
            // The weight, filled chunk by chunk as the opening reads it.
            let weight = StackWeight::new(stack.len(), lane_block, &claims, &lambdas, &ring_weights);
            let chunk = lane_block.min(INITIAL_BASIS_CHUNK);
            let mut actual = vec![F192::ZERO; stack.len()];
            for (i, out) in actual.chunks_exact_mut(chunk).enumerate() {
                weight.fill(i * chunk, out);
            }
            assert_eq!(actual, expected, "lane_vars={lane_vars}, lanes={lanes}");
        }
    }

    /// The family's closed-form weight against its definition: every claim's scaled piece weights `Phi(gamma_rs^j s_{j,t} eq(r_j[..n_t], .))` written out over the stack, then the MLE at the point.
    /// Pieces of every length down to one word, lengths shared within a region, points that are prefixes of one another and points that are not.
    #[test]
    fn family_weight_matches_dense() {
        let mut rng = Rng::new(0xFA417);
        let log_n = 9;
        let challenges = std::array::from_fn(|_| rng.ext());
        let family = RingFamily::new(rng.ext(), challenges);
        let coordinate_weights = ring_switch::build_coordinate_weights(&challenges);
        let lead = rng.ext_vec(7);
        let piece = |offset, n_vars| Piece { offset, n_vars };
        let regions = [
            vec![piece(0, 7)],
            vec![piece(128, 6), piece(192, 3), piece(200, 3), piece(208, 0)],
            vec![piece(256, 5), piece(320, 0)],
            vec![piece(384, 4), piece(448, 4), piece(511, 0)],
        ];
        let points = [
            vec![lead.clone(), rng.ext_vec(7)],
            vec![lead[..6].to_vec(), lead.clone()],
            vec![rng.ext_vec(6)],
            vec![lead[..4].to_vec(), rng.ext_vec(5), lead[..5].to_vec()],
        ];
        let rings: Vec<RingSwitch> = (regions.iter().zip(&points))
            .map(|(pieces, points)| RingSwitch {
                pieces: pieces.clone(),
                claims: (points.iter())
                    .map(|point| RingClaim {
                        slices: SliceClaim {
                            suffix_point: point.clone(),
                            s_hat_v: Vec::new(),
                        },
                        scales: rng.ext_vec(pieces.len()),
                    })
                    .collect(),
            })
            .collect();

        let mut dense = vec![F192::ZERO; 1 << log_n];
        let mut gamma = F192::ONE;
        for ring in &rings {
            for claim in &ring.claims {
                for (piece, &scale) in ring.pieces.iter().zip(&claim.scales) {
                    let point = &claim.slices.suffix_point[..piece.n_vars];
                    let scaled: Vec<F192> = eq_table(point).iter().map(|&e| gamma * scale * e).collect();
                    let mapped = fold_dense(&scaled, &coordinate_weights);
                    for (d, w) in dense[piece.offset..piece.end()].iter_mut().zip(mapped) {
                        *d += w;
                    }
                }
                gamma *= family.gamma_rs();
            }
        }
        for _ in 0..3 {
            let x = rng.ext_vec(log_n);
            let expected = (dense.iter().zip(eq_table(&x))).fold(F192::ZERO, |acc, (&d, e)| acc + d * e);
            assert_eq!(family.weight(&rings, &x), expected);
        }
    }

    struct Instance {
        vc: VerifierConfig,
        log_n: usize,
        root: Hash,
        point_claims: Vec<StackClaim>,
        rings: Vec<RingSwitch>,
        fs: ProofTranscript,
    }

    /// Synthetic stack of 2^14 F64 words: three aligned 2^12-word columns
    /// plus a q_flock region (a random bit-witness packed by pack) at the
    /// top slice, padded with random filler. Pool: one point claim per
    /// column at a random E point, one strided claim into q_flock, one claim
    /// split into two scaled terms (a jagged column's shape), one
    /// ring-switched claim with plain eq prefix weights, and on the filler past
    /// it, rings whose points are prefixes of its point (two of one length),
    /// sharing its pass, and one whose point is not; last, q_flock again in two
    /// scaled pieces, one claim at its point and one elsewhere.
    ///
    /// q_flock is kept SMALL (2^8 words) so the succinct verifier's residual
    /// cube sits entirely above the q_flock coords (the production regime:
    /// shared tensor prefix folded once, y coords all selector-indicator,
    /// nonempty E-valued selector prefix from ris); the crossing regime is
    /// exercised by `stacked_open_residual_crosses_qflock`.
    fn build_instance(seed: u64) -> Instance {
        let log_n = 14usize;
        let col_vars = 12usize;
        let col_len = 1usize << col_vars;
        let qflock_vars = 8usize;
        let qflock_offset = 3 * col_len;
        let mut rng = Rng::new(seed);

        // Three random columns, the packed bit-witness region, then filler.
        let mut stack: Vec<F64> = (0..3 * col_len).map(|_| F64(rng.next_u64())).collect();
        stack.extend((0..1usize << qflock_vars).map(|_| F64(rng.next_u64())));
        while stack.len() < 1 << log_n {
            stack.push(F64(rng.next_u64()));
        }
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim per column, at a random E point.
        let mut point_claims: Vec<StackClaim> = (0..3)
            .map(|c| {
                let offset = c * col_len;
                let low_point = rng.ext_vec(col_vars);
                let eq = eq_table(&low_point);
                let value = inner_product_base_ext(&stack[offset..offset + col_len], &eq);
                StackClaim::point(offset, low_point, value, F192::ONE)
            })
            .collect();

        // One strided claim into the q_flock region: freeze the low 3 in-block
        // coords to slot 5, eq over the remaining coords of the slice.
        {
            let stride_log = 3usize;
            let slot = 5usize;
            let point = rng.ext_vec(qflock_vars - stride_log);
            let eq = eq_table(&point);
            let mut value = F192::ZERO;
            for (j, &ej) in eq.iter().enumerate() {
                value += ej.mul_base(stack[qflock_offset + slot + (j << stride_log)]);
            }
            point_claims.push(StackClaim::strided(
                qflock_offset,
                slot,
                stride_log,
                point,
                value,
                F192::ONE,
            ));
        }

        // One claim of two scaled pieces: the low half of column 1 and one word of column 2.
        {
            let point = rng.ext_vec(col_vars);
            let (a, b) = (rng.ext(), rng.ext());
            let eq = eq_table(&point[..col_vars - 1]);
            let value = a * inner_product_base_ext(&stack[col_len..col_len + col_len / 2], &eq)
                + b.mul_base(stack[2 * col_len + 7]);
            let mut claim = StackClaim::point(col_len, point, value, F192::ONE);
            claim.terms = vec![
                Term {
                    offset: col_len,
                    n_vars: col_vars - 1,
                    scale: a,
                },
                Term {
                    offset: 2 * col_len + 7,
                    n_vars: 0,
                    scale: b,
                },
            ];
            point_claims.push(claim);
        }

        // The ring-switched regions committed whole, each with one claim (plain eq prefix weights).
        let suffix_point = rng.ext_vec(qflock_vars);
        let past = qflock_offset + (1 << qflock_vars);
        let regions = [
            (qflock_offset, suffix_point.clone()),
            (past, suffix_point[..qflock_vars - 1].to_vec()),
            (past + (1 << (qflock_vars - 1)), rng.ext_vec(qflock_vars - 2)),
            (
                past + 3 * (1 << (qflock_vars - 2)),
                suffix_point[..qflock_vars - 2].to_vec(),
            ),
            (
                past + 4 * (1 << (qflock_vars - 2)),
                suffix_point[..qflock_vars - 2].to_vec(),
            ),
        ];
        let mut rings: Vec<RingSwitch> = regions
            .iter()
            .map(|(offset, suffix_point)| {
                let n_vars = suffix_point.len();
                let s_hat_v = s_hat_v_reference(&stack[*offset..*offset + (1 << n_vars)], suffix_point);
                let claim = SliceClaim {
                    suffix_point: suffix_point.clone(),
                    s_hat_v,
                };
                RingSwitch::whole(*offset, n_vars, vec![claim], F192::ONE)
            })
            .collect();

        // q_flock in two scaled pieces: one claim at the whole region's point, one elsewhere.
        let pieces = vec![
            Piece {
                offset: qflock_offset,
                n_vars: qflock_vars - 2,
            },
            Piece {
                offset: qflock_offset + (1 << qflock_vars) - 2,
                n_vars: 1,
            },
        ];
        let claims = [suffix_point, rng.ext_vec(qflock_vars)]
            .into_iter()
            .map(|suffix_point| {
                let scales = rng.ext_vec(pieces.len());
                RingClaim {
                    slices: SliceClaim {
                        s_hat_v: piece_slices(&stack, &pieces, &suffix_point, &scales),
                        suffix_point,
                    },
                    scales,
                }
            })
            .collect();
        rings.push(RingSwitch { pieces, claims });

        let pc = test_config_for(log_n);
        // Pin the intended residual regime: the residual cube must sit
        // entirely above the q_flock coords, with at least one selector coord
        // covered by ris (the E-valued sel prefix) and the rest by y bits.
        let yr_log_n = log_n - pc.initial_k() - pc.level_ks().iter().sum::<usize>();
        assert!(
            qflock_vars < log_n - yr_log_n,
            "test shape must keep the residual cube above q_flock (yr_log_n = {yr_log_n})"
        );
        let (cm, pd) = commit(&stack, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
        let mut ps = ProverState::from_label(DOMAIN);
        open_batch_mixed_whir_stacked(&mut ps, log_n, &stack, &pd, &pc, &point_claims, &rings);

        Instance {
            vc: pc,
            log_n,
            root: cm.root,
            point_claims,
            rings,
            fs: ps.into_proof(),
        }
    }

    fn verify_instance(
        inst: &Instance,
        point_claims: &[StackClaim],
        rings: &[RingSwitch],
        fs: &ProofTranscript,
    ) -> bool {
        let mut vs = VerifierState::from_label(DOMAIN, fs);
        verify_opening_batch_mixed_whir_stacked(
            &mut vs,
            &inst.vc,
            inst.log_n,
            1 << inst.vc.initial_k(),
            &inst.root,
            point_claims,
            rings,
        )
        .is_ok()
    }

    #[test]
    fn stacked_open_roundtrip_and_tampering() {
        let inst = build_instance(1);
        assert!(
            verify_instance(&inst, &inst.point_claims, &inst.rings, &inst.fs),
            "honest stacked opening rejected"
        );

        // Wrong values: a dense column claim, a strided one, a two-piece one.
        for (c, what) in [(0, "Point"), (3, "Strided"), (4, "split")] {
            let mut bad_points = inst.point_claims.clone();
            bad_points[c].value += F192::ONE;
            assert!(
                !verify_instance(&inst, &bad_points, &inst.rings, &inst.fs),
                "tampered {what} value accepted"
            );
        }

        // A piece's scale and place are part of the statement: moving weight between pieces is caught.
        let mut bad_points = inst.point_claims.clone();
        bad_points[4].terms[1].scale += F192::ONE;
        assert!(
            !verify_instance(&inst, &bad_points, &inst.rings, &inst.fs),
            "rescaled piece accepted"
        );
        let mut bad_points = inst.point_claims.clone();
        bad_points[4].terms[1].offset += 1;
        assert!(
            !verify_instance(&inst, &bad_points, &inst.rings, &inst.fs),
            "moved piece accepted"
        );

        // Wrong ring-switched slices: rejected by the ring-switch binding. A wrong
        // point is rejected by the weight, shared pass or not.
        for r in 0..inst.rings.len() {
            for c in 0..inst.rings[r].claims.len() {
                let mut bad_ring = inst.rings.clone();
                bad_ring[r].claims[c].slices.s_hat_v[7] += F192::ONE;
                assert!(
                    !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
                    "tampered ring-switch slice {r}.{c} accepted"
                );
                let mut bad_ring = inst.rings.clone();
                bad_ring[r].claims[c].slices.suffix_point[0] += F192::ONE;
                assert!(
                    !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
                    "moved ring-switch point {r}.{c} accepted"
                );
            }
        }

        // A ring piece's scale and place are part of the statement too.
        let split = inst.rings.len() - 1;
        for c in 0..inst.rings[split].claims.len() {
            let mut bad_ring = inst.rings.clone();
            bad_ring[split].claims[c].scales[1] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
                "rescaled ring piece of claim {c} accepted"
            );
        }
        let mut bad_ring = inst.rings.clone();
        bad_ring[split].pieces[1].offset -= 2;
        assert!(
            !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
            "moved ring piece accepted"
        );

        // Every scalar the opening sends rides the stream, all of them WHIR's:
        // tampering any of them must be rejected.
        for idx in [17usize, inst.fs.stream.len() - 1] {
            let mut bad_fs = inst.fs.clone();
            bad_fs.stream[idx] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &inst.rings, &bad_fs),
                "tampered stream word {idx} accepted"
            );
        }

        // Shape tamper: a truncated stream must return false, not panic.
        let mut short_fs = inst.fs.clone();
        short_fs.stream.pop();
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.rings, &short_fs),
            "short stream accepted"
        );
    }

    /// Residual cube crossing INTO the q_flock slice (case split = n_ris in the
    /// verifier closure): q_flock occupies half a 2^14 stack (qflock_vars = 13),
    /// and the fallback config's residual cube (yr_log_n = 3) is wider than
    /// the single selector coordinate, so some q_flock coords are covered by
    /// binary y bits and the tensor finish runs with a nonempty suffix.
    #[test]
    fn stacked_open_residual_crosses_qflock() {
        let log_n = 14usize;
        let qflock_vars = 13usize;
        let qflock_offset = 1usize << 13;
        let mut rng = Rng::new(3);

        let mut stack: Vec<F64> = (0..1usize << 13).map(|_| F64(rng.next_u64())).collect();
        stack.extend((0..1usize << qflock_vars).map(|_| F64(rng.next_u64())));
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim on the low column.
        let low_point = rng.ext_vec(12);
        let eq = eq_table(&low_point);
        let value = inner_product_base_ext(&stack[..1 << 12], &eq);
        let point_claims = vec![StackClaim::point(0, low_point, value, F192::ONE)];

        // One ring-switched claim on the wide q_flock.
        let qflock = &stack[qflock_offset..];
        let suffix_point = rng.ext_vec(qflock_vars);
        let s_hat_v = s_hat_v_reference(qflock, &suffix_point);
        let claims = vec![SliceClaim { suffix_point, s_hat_v }];

        // Fixed fallback config so the residual cube size is known: the
        // crossing regime needs qflock_vars > log_n - yr_log_n.
        let pc = default_config(log_n, 5, 1).unwrap();
        let yr_log_n = log_n - pc.initial_k() - pc.level_ks().iter().sum::<usize>();
        assert!(
            qflock_vars > log_n - yr_log_n,
            "test shape must exercise the crossing regime (yr_log_n = {yr_log_n})"
        );

        let (cm, pd) = commit(&stack, log_n, pc.initial_k(), pc.log_inv_rates()[0]);
        let ring = RingSwitch::whole(qflock_offset, qflock_vars, claims, F192::ONE);
        let mut ps = ProverState::from_label(DOMAIN);
        open_batch_mixed_whir_stacked(
            &mut ps,
            log_n,
            &stack,
            &pd,
            &pc,
            &point_claims,
            std::slice::from_ref(&ring),
        );
        let fs = ps.into_proof();

        let mut vs = VerifierState::from_label(DOMAIN, &fs);
        assert!(
            verify_opening_batch_mixed_whir_stacked(
                &mut vs,
                &pc,
                log_n,
                1 << pc.initial_k(),
                &cm.root,
                &point_claims,
                std::slice::from_ref(&ring)
            )
            .is_ok(),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip a slice.
        let mut bad_ring = ring.clone();
        bad_ring.claims[0].slices.s_hat_v[7] += F192::ONE;
        let mut vs = VerifierState::from_label(DOMAIN, &fs);
        assert!(
            verify_opening_batch_mixed_whir_stacked(
                &mut vs,
                &pc,
                log_n,
                1 << pc.initial_k(),
                &cm.root,
                &point_claims,
                std::slice::from_ref(&bad_ring)
            )
            .is_err(),
            "tampered crossing-regime ring slice accepted"
        );
    }
}
