//! Production WHIR over opaque native-field wires. Every loop bound is public
//! circuit shape; configuration and transcript activity are constrained masks.

use std::collections::BTreeMap;
use std::sync::LazyLock;

use leanvm_guest::Field;
use riscv_proof::portable::pcs::WHIR_QUERIES;

use crate::Error;
use crate::algebra::{dot, eq_kernel, mle_eval, poly_eval};
use crate::context::Context;
use crate::protocol::{Dimension, MAX_STACK_VARS};
use crate::transcript::{Transcript, compress, hash_words};
use crate::uint::Uint;

const LEVELS: usize = 6;
const MAX_DEPTH: usize = 26;
const MAX_MESSAGE: usize = MAX_STACK_VARS - 6;

struct Config<F> {
    mask: F,
    mu: usize,
    rate: usize,
    queries: &'static [usize],
}

fn configurations<C: Context>(
    ctx: &C,
    enabled: C::F,
    log_n: &Dimension<C::F>,
    rate: &Uint<C::F>,
    lanes: &Uint<C::F>,
) -> Result<Vec<Config<C::F>>, Error> {
    if rate.width() != 3 || lanes.width() != 7 {
        return Err(Error::InvalidInput);
    }
    ctx.assert_bool(enabled)?;
    ctx.assert_zero(ctx.mul(enabled, lanes.eq_const(ctx, 0)))?;
    ctx.assert_zero(ctx.mul(enabled, Uint::constant(ctx, 64, 7).lt(ctx, lanes)))?;
    let rates: [_; 4] = std::array::from_fn(|r| rate.eq_const(ctx, (r + 1) as u64));
    let sizes: [_; 14] = std::array::from_fn(|m| log_n.equals(ctx, m + 15));
    let mut configs = Vec::with_capacity(56);
    let mut valid = ctx.zero();
    for (r, &rate_mask) in rates.iter().enumerate() {
        for (m, &size_mask) in sizes.iter().enumerate() {
            // The checked binary representations make these disjoint. A sum
            // alone would NOT establish one-hotness in characteristic two.
            let mask = ctx.mul(enabled, ctx.mul(rate_mask, size_mask));
            valid = ctx.add(valid, mask);
            configs.push(Config {
                mask,
                mu: m + 15,
                rate: r + 1,
                queries: WHIR_QUERIES[r][m],
            });
        }
    }
    ctx.assert_equal(valid, enabled)?;
    Ok(configs)
}

struct Query<F> {
    enabled: F,
    bits: [F; MAX_DEPTH],
    position: F,
}

/// Coalesce equal profiles, squeeze each required 192-bit word once, then
/// route disjoint chunks. In particular a chunk is never truncated at bit64.
fn sample_queries<C: Context>(
    transcript: &mut Transcript<C>,
    groups: &BTreeMap<(usize, usize), C::F>,
) -> Result<Vec<Query<C::F>>, Error> {
    let ctx = transcript.context();
    let max_count = groups.keys().map(|&(_, count)| count).max().unwrap_or(0);
    let max_samples = groups
        .keys()
        .map(|&(depth, count)| count.div_ceil(192 / depth))
        .max()
        .unwrap_or(0);
    let mut words = Vec::with_capacity(max_samples);
    for sample in 0..max_samples {
        let mut active = ctx.zero();
        for (&(depth, count), &mask) in groups {
            if sample < count.div_ceil(192 / depth) {
                active = ctx.add(active, mask);
            }
        }
        words.push(ctx.bits(transcript.sample(active)?, 192)?);
    }
    let mut queries = Vec::with_capacity(max_count);
    for index in 0..max_count {
        let mut active = ctx.zero();
        let mut bits = [ctx.zero(); MAX_DEPTH];
        for (&(depth, count), &mask) in groups {
            if index < count {
                active = ctx.add(active, mask);
                let chunks = 192 / depth;
                let word = &words[index / chunks];
                let offset = (index % chunks) * depth;
                for bit in 0..depth {
                    bits[bit] = ctx.add(bits[bit], ctx.mul(mask, word[offset + bit]));
                }
            }
        }
        let position = bits.iter().enumerate().fold(ctx.zero(), |sum, (i, &bit)| {
            ctx.add(sum, ctx.mul(bit, ctx.base(1u64 << i)))
        });
        queries.push(Query {
            enabled: active,
            bits,
            position,
        });
    }
    Ok(queries)
}

fn canonical_word<C: Context>(ctx: &C, word: C::F) -> Result<(), Error> {
    ctx.assert_equal(word, ctx.limb(word, 0))
}

fn authenticated_row<C: Context>(
    transcript: &Transcript<C>,
    query: &Query<C::F>,
    depth: &Dimension<C::F>,
    root: [C::F; 4],
    level_zero: bool,
    zero_prefix: &[C::F; 64],
) -> Result<Vec<C::F>, Error> {
    let ctx = transcript.context();
    let words = if level_zero { 64 } else { 48 };
    let path = transcript.merkle(
        query.enabled,
        ctx.base(words as u64),
        depth.value(ctx),
        words,
        MAX_DEPTH,
    )?;
    for (i, &word) in path.leaf.iter().enumerate() {
        canonical_word(ctx, word)?;
        if level_zero {
            ctx.assert_zero(ctx.mul(zero_prefix[i], word))?;
        }
    }
    let mut hash = hash_words(ctx, &path.leaf, ctx.base(words as u64))?;
    for (i, sibling) in path.siblings.iter().enumerate() {
        let present = depth.contains(i);
        ctx.assert_bool(query.bits[i])?;
        ctx.assert_zero(ctx.mul(ctx.not(present), query.bits[i]))?;
        for &word in sibling {
            canonical_word(ctx, word)?;
            ctx.assert_zero(ctx.mul(ctx.not(present), word))?;
        }
        let left = std::array::from_fn(|j| ctx.select(query.bits[i], sibling[j], hash[j]));
        let right = std::array::from_fn(|j| ctx.select(query.bits[i], hash[j], sibling[j]));
        let next = compress(ctx, left, right)?;
        hash = std::array::from_fn(|j| ctx.select(present, next[j], hash[j]));
    }
    for i in 0..4 {
        ctx.assert_equal_if(query.enabled, hash[i], root[i])?;
    }
    if level_zero {
        Ok(path.leaf.into_iter().rev().collect())
    } else {
        path.leaf
            .chunks_exact(3)
            .map(|v| ctx.compose([v[0], v[1], v[2]]))
            .collect()
    }
}

// s_i(2^i) and its inverse depend only on the public polynomial-basis
// additive-NTT domain, never on a proof or circuit input.
static SUBSPACE_ROOTS: LazyLock<[(Field, Field); MAX_MESSAGE]> = LazyLock::new(|| {
    let mut layer: [Field; MAX_MESSAGE] = std::array::from_fn(|i| Field::from(1u64 << (i + 1)));
    let mut root = Field::ONE;
    std::array::from_fn(|i| {
        let pair = (root, root.inverse().expect("nonzero additive subspace root"));
        for value in &mut layer[i..] {
            *value = *value * *value + root * *value;
        }
        root = layer[i];
        pair
    })
});

struct Glued<F> {
    start: usize,
    ood_scalar: F,
    ood_point: Vec<F>,
    query_scalar: F,
    queries: Vec<Query<F>>,
    weights: Vec<F>,
}

/// Verifies all 56 production profiles with one topology and one evaluation of
/// the caller's (possibly expensive) stacked weight at the terminal point.
pub(crate) fn verify_whir<C: Context>(
    transcript: &mut Transcript<C>,
    enabled: C::F,
    log_n: &Dimension<C::F>,
    log_inv_rate: &Uint<C::F>,
    n_lanes: &Uint<C::F>,
    target: C::F,
    root: [C::F; 4],
    evaluate_basis: impl FnOnce(&[C::F; MAX_STACK_VARS]) -> Result<C::F, Error>,
) -> Result<(), Error> {
    let ctx = transcript.context();
    let configs = configurations(ctx, enabled, log_n, log_inv_rate, n_lanes)?;
    let zero_prefix = std::array::from_fn(|i| ctx.not(Uint::constant(ctx, (63 - i) as u64, 7).lt(ctx, n_lanes)));
    for word in root {
        canonical_word(ctx, word)?;
    }
    let mut quad = transcript.round_poly(enabled, 3, ctx.mul(enabled, target), None)?;
    let mut folds = [ctx.zero(); MAX_STACK_VARS];
    let mut current_root = root;
    let mut residual = [ctx.zero(); 32];
    let mut tail = [ctx.zero(); 5];
    let mut terminal_target = ctx.zero();
    let mut glued = Vec::with_capacity(LEVELS);

    for level in 0..LEVELS {
        let start = if level == 0 { 0 } else { 6 + 4 * (level - 1) };
        let end = 6 + 4 * level;
        let mut live = ctx.zero();
        let mut final_level = ctx.zero();
        let mut depth_value = ctx.zero();
        let mut groups = BTreeMap::new();
        let mut residual_live = [ctx.zero(); 32];
        for config in &configs {
            if level < config.queries.len() {
                live = ctx.add(live, config.mask);
                let depth = config.mu + config.rate - 6 - level;
                depth_value = ctx.add(depth_value, ctx.mul(config.mask, ctx.base(depth as u64)));
                let entry = groups.entry((depth, config.queries[level])).or_insert(ctx.zero());
                *entry = ctx.add(*entry, config.mask);
                if level + 1 == config.queries.len() {
                    final_level = ctx.add(final_level, config.mask);
                    for slot in &mut residual_live[..1 << (config.mu - end)] {
                        *slot = ctx.add(*slot, config.mask);
                    }
                }
            }
        }
        let more = ctx.add(live, final_level);
        let depth = Dimension::new(ctx, depth_value, MAX_DEPTH)?;
        for coordinate in &mut folds[start..end] {
            let challenge = transcript.sample(live)?;
            *coordinate = ctx.select(live, challenge, *coordinate);
            let claim = poly_eval(ctx, &quad, challenge);
            let next = transcript.round_poly(live, 3, claim, None)?;
            for i in 0..3 {
                quad[i] = ctx.select(live, next[i], quad[i]);
            }
        }
        // At a final level residual values precede queries. Otherwise the root
        // and OOD point/value/intro precede them. Disabled operations do not ratchet.
        for i in 0..32 {
            let value = transcript.scalar(residual_live[i])?;
            residual[i] = ctx.select(final_level, value, residual[i]);
        }
        let next_root = transcript.root(more)?;
        let mut ood_point = Vec::with_capacity(MAX_STACK_VARS - end);
        for i in end..MAX_STACK_VARS {
            ood_point.push(transcript.sample(ctx.mul(more, log_n.contains(i)))?);
        }
        let ood_value = transcript.scalar(more)?;
        let ood_intro = transcript.round_poly(more, 3, ood_value, None)?;
        transcript.grind(live, ctx.base(17))?;
        let queries = sample_queries(transcript, &groups)?;
        let lambda = transcript.sample(live)?;
        let lane_weights = eq_kernel(ctx, &folds[start..end]);
        let mut weights = Vec::with_capacity(queries.len());
        let mut power = ctx.one();
        let mut enforced = ctx.zero();
        for query in &queries {
            let weight = ctx.mul(query.enabled, power);
            weights.push(weight);
            let row = authenticated_row(transcript, query, &depth, current_root, level == 0, &zero_prefix)?;
            enforced = ctx.add(enforced, ctx.mul(weight, dot(ctx, &row, &lane_weights)));
            power = ctx.select(query.enabled, ctx.mul(power, lambda), power);
        }
        let intro = transcript.round_poly(live, 3, enforced, None)?;
        let ood_scalar = ctx.mul(more, lambda);
        let query_scalar = ctx.mul(live, ctx.select(more, ctx.mul(lambda, lambda), lambda));
        for i in 0..3 {
            quad[i] = ctx.add(
                quad[i],
                ctx.add(ctx.mul(ood_scalar, ood_intro[i]), ctx.mul(query_scalar, intro[i])),
            );
        }
        glued.push(Glued {
            start: end,
            ood_scalar,
            ood_point,
            query_scalar,
            queries,
            weights,
        });

        for i in 0..5 {
            // The final suffix is at most five variables; the last static
            // level has only two available coordinates.
            if end + i < MAX_STACK_VARS {
                let active = ctx.mul(final_level, log_n.contains(end + i));
                let challenge = transcript.sample(active)?;
                folds[end + i] = ctx.select(active, challenge, folds[end + i]);
                tail[i] = ctx.select(final_level, challenge, tail[i]);
                let claim = poly_eval(ctx, &quad, challenge);
                terminal_target = ctx.select(active, claim, terminal_target);
                let another = ctx.mul(final_level, log_n.contains(end + i + 1));
                let next = transcript.round_poly(another, 3, claim, None)?;
                for j in 0..3 {
                    quad[j] = ctx.select(another, next[j], quad[j]);
                }
            } else {
                tail[i] = ctx.select(final_level, ctx.zero(), tail[i]);
            }
        }
        current_root = std::array::from_fn(|i| ctx.select(more, next_root[i], current_root[i]));
    }

    // Rotate ONLY the actual dimension: zero padding must not move lane
    // challenges into the wrong witness coordinates on smaller configurations.
    let mut witness_point = [ctx.zero(); MAX_STACK_VARS];
    for mu in 15..=MAX_STACK_VARS {
        let mask = ctx.mul(enabled, log_n.equals(ctx, mu));
        for i in 0..mu {
            witness_point[i] = ctx.add(witness_point[i], ctx.mul(mask, folds[(i + 6) % mu]));
        }
    }
    let mut weight = evaluate_basis(&witness_point)?;
    for claim in glued {
        let mut equality = ctx.one();
        for (i, &z) in claim.ood_point.iter().enumerate() {
            let active = log_n.contains(claim.start + i);
            let factor = ctx.add(ctx.one(), ctx.add(z, folds[claim.start + i]));
            equality = ctx.mul(equality, ctx.select(active, factor, ctx.one()));
        }
        weight = ctx.add(weight, ctx.mul(claim.ood_scalar, equality));
        let mut induced = ctx.zero();
        for (query, query_weight) in claim.queries.iter().zip(claim.weights) {
            let mut basis = query.position;
            let mut product = query_weight;
            for i in 0..MAX_STACK_VARS - claim.start {
                let (root, inverse) = SUBSPACE_ROOTS[i];
                let factor = ctx.add(
                    ctx.one(),
                    ctx.mul(
                        folds[claim.start + i],
                        ctx.add(ctx.one(), ctx.mul(basis, ctx.constant(inverse))),
                    ),
                );
                product = ctx.mul(product, ctx.select(log_n.contains(claim.start + i), factor, ctx.one()));
                basis = ctx.add(ctx.mul(basis, basis), ctx.mul(ctx.constant(root), basis));
            }
            induced = ctx.add(induced, product);
        }
        weight = ctx.add(weight, ctx.mul(claim.query_scalar, induced));
    }
    // A short residual is zero-extended to 32 entries and its point is padded
    // with zero high coordinates, so this is exactly its original MLE.
    ctx.assert_equal_if(
        enabled,
        ctx.mul(weight, mle_eval(ctx, &residual, &tail)),
        terminal_target,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::eq_eval;
    use crate::context::{Source, Symbolic, Witness};
    use fiat_shamir::transcript::{ProverState, RawProof, VerifierState};
    use primitives::field::{F64, F192};
    use zk_alloc::ArenaVec;

    fn field(x: F192) -> Field {
        Field::new(x.c0, x.c1, x.c2)
    }
    fn digest(hash: [u8; 32]) -> [Field; 4] {
        fiat_shamir::digest_words(&hash).map(|word| Field::from(word.0))
    }

    struct Fixture {
        raw: RawProof,
        public: Vec<Field>,
        mu: usize,
        rate: usize,
        root: [u8; 32],
        target: Field,
        point: Vec<Field>,
    }

    fn fixture(mu: usize, rate: usize, lanes: usize) -> Fixture {
        let config = pcs::whir::config_for_rate(mu, rate).unwrap();
        let witness: Vec<_> = (0..lanes << (mu - 6))
            .map(|i| F64((i as u64).wrapping_mul(0x9e3779b97f4a7c15).rotate_left(17) ^ 123))
            .collect();
        let point: Vec<_> = (0..mu)
            .map(|i| {
                if i >= mu - 6 && lanes < 64 {
                    F192::ZERO
                } else {
                    F192::new(7 + i as u64, 19 + i as u64, 31 + i as u64)
                }
            })
            .collect();
        // The lane-zero equality basis vanishes on every omitted lane.
        let mut basis = pcs::whir::build_eq_table_ext(&point);
        basis.truncate(witness.len());
        let target = pcs::whir::inner_product_base_ext(&witness, &basis);
        let (commitment, data) = pcs::whir::commit(&witness, mu, 6, rate);
        let mut prover = ProverState::new([F64::ZERO; 4], [F64::ZERO; 4]);
        pcs::whir::recursive_prover_with_basis(
            &config,
            mu,
            &witness,
            ArenaVec::from_slice(&basis),
            target,
            &data.codeword,
            &data.merkle_tree,
            &mut prover,
        );
        let proof = prover.into_proof();
        let mut reference = VerifierState::new([F64::ZERO; 4], &proof, [F64::ZERO; 4]);
        pcs::whir::recursive_verifier_with_basis_succinct(
            &config,
            mu,
            lanes,
            target,
            &commitment.root,
            |r| {
                point
                    .iter()
                    .zip(r)
                    .fold(F192::ONE, |v, (&a, &b)| v * (F192::ONE + a + b))
            },
            &mut reference,
        )
        .unwrap();
        reference.finish().unwrap();
        let raw = reference.into_raw_proof();
        let point: Vec<_> = point.into_iter().map(field).collect();
        let mut public = vec![
            Field::ONE,
            Field::from(mu as u64),
            Field::from(rate as u64),
            Field::from(lanes as u64),
            field(target),
        ];
        public.extend(digest(commitment.root));
        public.extend(&point);
        public.resize(37, Field::ZERO);
        Fixture {
            raw,
            public,
            mu,
            rate,
            root: commitment.root,
            target: field(target),
            point,
        }
    }

    fn program<C: Context>(ctx: &C, basis_bias: C::F) -> Result<(), Error> {
        let enabled = ctx.public(0)?;
        let dim = Dimension::new(ctx, ctx.public(1)?, 34)?;
        let rate = Uint::from_field(ctx, ctx.public(2)?, 3)?;
        let lanes = Uint::from_field(ctx, ctx.public(3)?, 7)?;
        let target = ctx.public(4)?;
        let mut root = [ctx.zero(); 4];
        for (i, word) in root.iter_mut().enumerate() {
            *word = ctx.public(5 + i)?;
        }
        let mut point = [ctx.zero(); MAX_STACK_VARS];
        for (i, coordinate) in point.iter_mut().enumerate() {
            *coordinate = ctx.public(9 + i)?;
        }
        let mut transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        verify_whir(&mut transcript, enabled, &dim, &rate, &lanes, target, root, |r| {
            let mut value = ctx.one();
            for i in 0..MAX_STACK_VARS {
                let factor = ctx.add(ctx.one(), ctx.add(point[i], r[i]));
                value = ctx.mul(value, ctx.select(dim.contains(i), factor, ctx.one()));
            }
            Ok(ctx.add(value, basis_bias))
        })
    }

    #[test]
    fn production_proofs_match_portable_and_one_symbolic_circuit() {
        let symbolic = Symbolic::new(37);
        program(&symbolic, symbolic.zero()).unwrap();
        let circuit = symbolic.finish();
        for (mu, rate, lanes) in [(15, 1, 1), (16, 4, 64)] {
            let instance = fixture(mu, rate, lanes);
            let portable = riscv_proof::Proof {
                stream: instance.raw.stream.iter().copied().map(field).collect(),
                merkle: instance
                    .raw
                    .merkle
                    .iter()
                    .map(|p| riscv_proof::Opening {
                        leaf: p.leaf_data.iter().map(|w| w.0).collect(),
                        siblings: p.path.clone(),
                    })
                    .collect(),
            };
            let mut reference = riscv_proof::portable::transcript::Transcript::new(&portable, [0; 32], [0; 32]);
            riscv_proof::portable::pcs::verify_whir(
                &mut reference,
                instance.mu,
                instance.rate,
                instance.target,
                instance.root,
                |r| eq_eval(&Witness::new(&[], Vec::new()), &instance.point, r),
            )
            .unwrap();
            reference.finish().unwrap();
            let witness = Witness::new(&instance.public, vec![Source::Native(&instance.raw)]);
            program(&witness, Field::ZERO).unwrap();
            circuit.evaluate(&instance.public, &witness.finish().unwrap()).unwrap();

            // A changed terminal basis must fail without changing transcript
            // challenges; this specifically defends the final product relation.
            let witness = Witness::new(&instance.public, vec![Source::Native(&instance.raw)]);
            assert!(program(&witness, Field::ONE).is_err());
        }
        let mut public = vec![Field::ZERO; 37];
        // Invalid active dimensions are harmless for an absent opening.
        public[1] = Field::from(34);
        public[2] = Field::from(7);
        public[3] = Field::from(127);
        let witness = Witness::new(&public, Vec::new());
        program(&witness, Field::ZERO).unwrap();
        circuit.evaluate(&public, &witness.finish().unwrap()).unwrap();
    }

    #[test]
    fn production_opening_rejects_modified_leaf_path_order_and_residual() {
        let instance = fixture(15, 2, 17);
        let rejects = |raw: &RawProof, public: &[Field]| {
            let witness = Witness::new(public, vec![Source::Native(raw)]);
            assert!(program(&witness, Field::ZERO).is_err());
        };
        let mut bad = instance.raw.clone();
        bad.merkle[0].leaf_data[63].0 ^= 1;
        rejects(&bad, &instance.public);
        let mut bad = instance.raw.clone();
        bad.merkle[0].path[0][0] ^= 1;
        rejects(&bad, &instance.public);
        let mut bad = instance.raw.clone();
        let different = (1..bad.merkle.len()).find(|&i| bad.merkle[i] != bad.merkle[0]).unwrap();
        bad.merkle.swap(0, different);
        rejects(&bad, &instance.public);
        let mut bad = instance.raw.clone();
        // mu15: intro2, six fold rounds12, root2, OOD value1,
        // OOD intro2, grind1, query intro2, four fold rounds8.
        bad.stream[30].c0 ^= 1;
        rejects(&bad, &instance.public);
        let mut bad = instance.raw.clone();
        bad.stream.last_mut().unwrap().c0 ^= 1;
        rejects(&bad, &instance.public);
        let mut public = instance.public.clone();
        public[3] = Field::ONE; // authentic committed nonzero lanes now forbidden
        rejects(&instance.raw, &public);
        for (slot, value) in [(1, 14), (1, 29), (2, 0), (2, 5), (3, 0), (3, 65)] {
            let mut public = instance.public.clone();
            public[slot] = Field::from(value);
            rejects(&instance.raw, &public);
        }
    }

    #[test]
    fn finite_profile_selection_matches_every_production_configuration() {
        let ctx = Witness::new(&[], Vec::new());
        for mu in 15..=28 {
            for rate in 1..=4 {
                let config = pcs::whir::config_for_rate(mu, rate).unwrap();
                let selected = configurations(
                    &ctx,
                    Field::ONE,
                    &Dimension::constant(&ctx, mu),
                    &Uint::constant(&ctx, rate as u64, 3),
                    &Uint::constant(&ctx, 64, 7),
                )
                .unwrap();
                let active: Vec<_> = selected.iter().filter(|c| c.mask == Field::ONE).collect();
                assert_eq!(active.len(), 1);
                assert_eq!(active[0].queries, config.queries);
                assert_eq!(config.initial_k, 6);
                assert!(config.level_ks.iter().all(|&k| k == 4));
                assert!(config.grinding_bits.iter().all(|&g| g == 17));
                assert_eq!(config.ood_samples[0], 0);
                assert!(config.ood_samples[1..].iter().all(|&n| n == 1));
                for level in 0..active[0].queries.len() {
                    assert_eq!(
                        mu + rate - 6 - level,
                        mu - (6 + 4 * level) + config.log_inv_rates[level]
                    );
                }
            }
        }
    }

    fn query_program<C: Context>(ctx: &C) -> Result<(Vec<C::F>, C::F), Error> {
        let enabled = ctx.public(0)?;
        let choice = ctx.public(1)?;
        ctx.assert_bool(enabled)?;
        ctx.assert_bool(choice)?;
        let groups = BTreeMap::from([
            ((10, 223), ctx.mul(enabled, ctx.not(choice))),
            ((26, 228), ctx.mul(enabled, choice)),
        ]);
        let mut transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        let queries = sample_queries(&mut transcript, &groups)?;
        Ok((
            queries.into_iter().map(|q| q.position).collect(),
            transcript.sample(ctx.one())?,
        ))
    }

    #[test]
    fn chunk_sampling_crosses_limbs_preserves_duplicates_and_masks_squeezes() {
        let symbolic = Symbolic::new(2);
        let (positions, following) = query_program(&symbolic).unwrap();
        let circuit = symbolic.finish();
        let empty = riscv_proof::Proof {
            stream: Vec::new(),
            merkle: Vec::new(),
        };
        for (enabled, choice) in [(0, 0), (1, 0), (1, 1)] {
            let public = [Field::from(enabled), Field::from(choice)];
            let ctx = Witness::new(&public, Vec::new());
            let (actual, next) = query_program(&ctx).unwrap();
            let mut reference = riscv_proof::portable::transcript::Transcript::new(&empty, [0; 32], [0; 32]);
            let mut expected = if enabled == 0 {
                Vec::new()
            } else {
                let (depth, count) = if choice == 0 { (10, 223) } else { (26, 228) };
                riscv_proof::portable::pcs::sample_queries(&mut reference, 1 << depth, count)
                    .unwrap()
                    .into_iter()
                    .map(|q| Field::from(q as u64))
                    .collect::<Vec<_>>()
            };
            if enabled == 1 && choice == 0 {
                assert!(expected.iter().enumerate().any(|(i, q)| expected[..i].contains(q)));
            }
            expected.resize(228, Field::ZERO);
            assert_eq!(actual, expected);
            assert_eq!(next, reference.sample());
            let values = circuit.evaluate(&public, &ctx.finish().unwrap()).unwrap();
            assert_eq!(
                positions.iter().map(|w| values[w.index()]).collect::<Vec<_>>(),
                expected
            );
            assert_eq!(values[following.index()], next);
        }
    }

    fn row_program<C: Context>(ctx: &C) -> Result<Vec<C::F>, Error> {
        let position = Uint::from_field(ctx, ctx.public(0)?, MAX_DEPTH)?;
        let bits = std::array::from_fn(|i| position.bits()[i]);
        let query = Query {
            enabled: ctx.one(),
            bits,
            position: position.value(ctx),
        };
        let mut root = [ctx.zero(); 4];
        for (i, word) in root.iter_mut().enumerate() {
            *word = ctx.public(i + 1)?;
        }
        let prefix = std::array::from_fn(|i| ctx.base(u64::from(i < 63)));
        let transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        authenticated_row(&transcript, &query, &Dimension::constant(ctx, 1), root, true, &prefix)
    }

    #[test]
    fn authenticated_rows_reject_noncanonical_advice_high_query_bits_and_padding() {
        let mut path = fiat_shamir::merkle::RawMerklePath {
            leaf_index: 0,
            leaf_data: vec![F64::ZERO; 64],
            path: vec![[0; 32]],
        };
        path.leaf_data[63] = F64(17);
        let root = path.root(0);
        let mut public = vec![Field::ZERO];
        public.extend(digest(root));
        let raw = RawProof {
            stream: Vec::new(),
            merkle: vec![path.clone()],
        };
        let witness = Witness::new(&public, vec![Source::Native(&raw)]);
        let row = row_program(&witness).unwrap();
        assert_eq!(row[0], Field::from(17));
        assert!(row[1..].iter().all(|&v| v == Field::ZERO));
        let advice = witness.finish().unwrap();
        let symbolic = Symbolic::new(5);
        row_program(&symbolic).unwrap();
        let circuit = symbolic.finish();
        circuit.evaluate(&public, &advice).unwrap();
        for index in [63, 64] {
            let mut bad = advice.clone();
            bad[index] = Field::new(bad[index].0[0], 1, 0);
            assert!(circuit.evaluate(&public, &bad).is_err());
        }
        let mut bad = advice.clone();
        bad[68] = Field::ONE; // sibling above the declared depth
        assert!(circuit.evaluate(&public, &bad).is_err());
        let mut bad_query = public.clone();
        bad_query[0] = Field::from(2); // same low path bit, outside depth1
        let witness = Witness::new(&bad_query, vec![Source::Native(&raw)]);
        assert!(row_program(&witness).is_err());
        assert!(circuit.evaluate(&bad_query, &advice).is_err());

        // Even a correctly authenticated image cannot populate an absent lane.
        path.leaf_data[0] = F64(1);
        let mut public = vec![Field::ZERO];
        public.extend(digest(path.root(0)));
        let raw = RawProof {
            stream: Vec::new(),
            merkle: vec![path],
        };
        let witness = Witness::new(&public, vec![Source::Native(&raw)]);
        assert!(row_program(&witness).is_err());
    }
}
