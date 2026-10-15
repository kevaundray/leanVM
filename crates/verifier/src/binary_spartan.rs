//! Binary Spartan for block R1CS over GF(2), as exported from Clean circuits: `2^n_log` instances of one block
//! `(A0, B0, C0)` padded to `2^k_log` rows and columns, the matrices being `I ⊗ A0` and likewise (SIMD R1CS).
//!
//! The proof commits the packed witness, runs flock's zerocheck and lincheck (with the block's general `C0`), then
//! opens the commitment in one stacked WHIR that discharges lincheck's ring-switched slice claim and pins every
//! instance's public words. Lincheck's terminal leaves `e_row^T (A0 + alpha B0 + alpha^2 C0) w_col` to the block,
//! which the verifier evaluates from the sparse matrices or checks against a SPARK proof ([`spark`]).
//!
//! A linked block ([`Links`]) adds `S_N ⊗ A_link` to `A`: link row `first_row + j` of instance `i` also reads column
//! `out_base + j` of instance `i - 1`, and instance 0's reads the statement's `in` bit `j` instead ([`Boundary`]).
//! The zerocheck's A claim at `x = (x_in, x_out)` then splits as
//!
//! ```text
//! v_a = (I ⊗ A0) part + eq(x_out, 0) sum_j rho_j in_j + T,   T = sum_i next(i, x_out) Q(i),   Q(i) = sum_j rho_j z_i[out_j]
//! ```
//!
//! with `rho_j` the quirky row weight of link row `j` and `next(i, y)` one iff `y = i + 1` (no wrap, [`next_eval`]).
//! The prover sends `T`, lincheck reduces the rest of `v_a` unchanged, an `n_log`-round sumcheck on
//! `next(i, x_out) Q(i)` takes `T` to `next(r, x_out) Q(r)`, and an `out_log - 6`-round sumcheck over the `out`
//! block's word bits takes `Q(r)` to its 64 slices, which the verifier closes with `sum_j rho_j eq(r_sub, j / 64)
//! s[j % 64]`. The slices are a second ring-switched claim, at `(r_sub, out block, r)`, discharged in the same stacked
//! opening as lincheck's (one shared map, ring claims first), where strided claims at the last instance also pin its
//! `out` words to the statement.
//!
//! Transcript order: commitment root, zerocheck, for a linked block `T`, the `n_log` rounds, the `out_log - 6` rounds
//! and the 64 link slices, lincheck, the public-pin point, the stacked opening (lincheck's ring claim, the link's, the
//! public pins, the `out` pins), then SPARK.

use crate::field::{E, K, ONE, ZERO};
use crate::flock::{FlockClaims, RingMap, ZerocheckResult, lagrange_weights, verify_flock_zerocheck, verify_lincheck};
use crate::hash::{Digest, blake2s_hash};
use crate::layout::{FLOCK_K_SKIP, K_BITS, MAX_STACKED_LOG, MIN_STACKED_LOG};
use crate::multilinear::{Placement, dot, eq_eval, eq_kernel};
use crate::transcript::{Proof, Transcript, sumcheck};
use crate::{StackClaim, VerifierError, require, verify_stacked_opening};

pub mod spark;

/// Domain label of the transcript seed.
pub const LABEL: &[u8] = b"binary-spartan-1";
/// flock's floors: the zerocheck's fixed challenges need `m >= 13`, lincheck's byte stripes `n_log >= 3`.
const MIN_M: usize = FLOCK_K_SKIP + 7;
const MIN_N_LOG: usize = 3;

/// A GF(2) matrix in compressed sparse row form: every listed entry is 1.
#[derive(Clone, Copy, Debug)]
pub struct Csr<'a> {
    pub row_ptr: &'a [u32],
    pub cols: &'a [u32],
}

impl Csr<'_> {
    fn row(&self, r: usize) -> &[u32] {
        &self.cols[self.row_ptr[r] as usize..self.row_ptr[r + 1] as usize]
    }
}

/// The statement's fixed part: the block, `2^k_log` rows each, columns below `2^k_log`.
///
/// Column 0 is the constant one and columns `1..=n_public` the public bits, zero-padded to whole 64-bit words.
#[derive(Clone, Copy, Debug)]
pub struct Block<'a> {
    pub k_log: usize,
    pub n_public: usize,
    pub a: Csr<'a>,
    pub b: Csr<'a>,
    pub c: Csr<'a>,
    /// A linked block's links; their `in` side is in `a` already.
    pub links: Option<Links>,
    /// The block's own digest, bound into the transcript seed.
    pub digest: [u8; 32],
}

impl Block<'_> {
    /// Packed 64-bit words per instance in the public region.
    pub fn public_words(&self) -> usize {
        (self.n_public + 1).div_ceil(64)
    }
}

/// Where a linked block's `count` links sit: link `j` is row `first_row + j` (`A0 = {in_j}`, `B0 = {constant}`,
/// `C0 = {}`), and its `out` signal is column `out_base + j`, inside the aligned `2^out_log` block at `out_base`, whose
/// first `ceil(count / 64)` words hold nothing else.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Links {
    pub count: usize,
    pub first_row: usize,
    pub out_base: usize,
    pub out_log: usize,
}

impl Links {
    fn words(&self) -> usize {
        self.count.div_ceil(64)
    }

    fn well_formed(&self, block: &Block) -> bool {
        let k = 1usize << block.k_log;
        self.count > 0
            && (FLOCK_K_SKIP..=block.k_log).contains(&self.out_log)
            && self.count <= 1 << self.out_log
            && self.out_base.is_multiple_of(1 << self.out_log)
            && self.out_base >= 64 * block.public_words()
            && self.out_base + (1 << self.out_log) <= k
            && self.first_row + self.count <= k
    }
}

/// A linked batch's boundary statement: instance 0's `in` link values and instance `N - 1`'s `out` link values, link
/// `j` at bit `j` of `ceil(count / 64)` words each, spare bits clear.
#[derive(Clone, Copy, Debug)]
pub struct Boundary<'a> {
    pub input: &'a [u64],
    pub output: &'a [u64],
}

impl Boundary<'_> {
    fn well_formed(&self, links: &Links) -> bool {
        let spare = if links.count.is_multiple_of(64) {
            0
        } else {
            !0u64 << (links.count % 64)
        };
        [self.input, self.output]
            .iter()
            .all(|words| words.len() == links.words() && words[words.len() - 1] & spare == 0)
    }
}

/// The batch's instance-count logarithm: the next power of two, raised to flock's floors.
pub fn batch_log(k_log: usize, n_instances: usize) -> Result<usize, VerifierError> {
    require(n_instances > 0, VerifierError::PublicWords)?;
    let n_log = (n_instances.next_power_of_two().trailing_zeros() as usize)
        .max(MIN_N_LOG)
        .max(MIN_M.saturating_sub(k_log));
    require(
        k_log >= FLOCK_K_SKIP && k_log + n_log - FLOCK_K_SKIP <= MAX_STACKED_LOG,
        VerifierError::CommittedSize,
    )?;
    Ok(n_log)
}

/// The transcript's two seed digests: the label's, then the statement's (the block digest, the batch shape, every
/// real instance's public words, then a linked batch's boundary `in` and `out` words, little-endian).
fn seed(
    block: &Block,
    n_instances: usize,
    n_log: usize,
    publics: &[u64],
    boundary: Option<&Boundary>,
) -> (Digest, Digest) {
    let mut statement = Vec::with_capacity(LABEL.len() + 56 + 8 * publics.len());
    statement.extend_from_slice(LABEL);
    statement.extend_from_slice(&block.digest);
    for value in [n_instances, block.k_log, n_log] {
        statement.extend_from_slice(&(value as u64).to_le_bytes());
    }
    let boundary = boundary.map(|b| b.input.iter().chain(b.output)).into_iter().flatten();
    for word in publics.iter().chain(boundary) {
        statement.extend_from_slice(&word.to_le_bytes());
    }
    (blake2s_hash(LABEL), blake2s_hash(&statement))
}

/// Every instance's constant bit is set and its padding bits are clear.
fn well_formed(block: &Block, publics: &[u64]) -> bool {
    let words = block.public_words();
    let used = block.n_public + 1;
    let padding = if used.is_multiple_of(64) {
        0
    } else {
        !0u64 << (used % 64)
    };
    !publics.is_empty()
        && publics.len().is_multiple_of(words)
        && publics
            .chunks_exact(words)
            .all(|instance| instance[0] & 1 == 1 && instance[words - 1] & padding == 0)
}

/// Transpose an 8x8 bit matrix held one row per byte: bit `q` of byte `j` trades places with bit `j` of byte `q`.
fn transpose8(mut x: u64) -> u64 {
    let mut t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^ t ^ (t << 28)
}

/// Every public word slot's MLE over the instances at `point`: `sum_i eq(point, i) w_i` for the `K`-valued word `w_i`
/// of instance `i`, padding instances repeating the last real one.
///
/// The product is F2-bilinear, so it is `sum_b x^b S_b`, `S_b` summing the weights whose word has bit `b` set. Eight
/// instances at a time, every subset sum of their weights is tabulated once, and each slot's bit `b` selects one entry
/// by the eight words' bits `b`.
fn public_evaluations(publics: &[u64], words: usize, point: &[E]) -> Vec<E> {
    let weights = eq_kernel(point);
    let last = publics.len() / words - 1;
    let mut sums = vec![[ZERO; 64]; words];
    let mut subsets = [ZERO; 256];
    for (group, weights) in weights.as_chunks::<8>().0.iter().enumerate() {
        for (j, &weight) in weights.iter().enumerate() {
            for low in 0..1 << j {
                subsets[1 << j | low] = subsets[low] + weight;
            }
        }
        for (slot, sums) in sums.iter_mut().enumerate() {
            let block: [u64; 8] = std::array::from_fn(|j| publics[(8 * group + j).min(last) * words + slot]);
            for byte in 0..8 {
                let rows = u64::from_le_bytes(block.map(|word| (word >> (8 * byte)) as u8));
                for (bit, mask) in transpose8(rows).to_le_bytes().into_iter().enumerate() {
                    sums[8 * byte + bit] += subsets[mask as usize];
                }
            }
        }
    }
    let times_x = |limb: u64| limb << 1 ^ (0u64.wrapping_sub(limb >> 63) & 0x1B);
    let horner = |bits: &[E; 64]| {
        bits.iter().rev().fold(ZERO, |acc, &sum| {
            E::new(times_x(acc.c0), times_x(acc.c1), times_x(acc.c2)) + sum
        })
    };
    sums.iter().map(horner).collect()
}

/// `e_row^T (A0 + alpha B0 + alpha^2 C0) w_col`, one sparse pass over the rows for each matrix.
fn block_form(block: &Block, claims: &FlockClaims) -> Result<E, VerifierError> {
    let w_col = claims.column_weights();
    let rows = 1usize << block.k_log;
    let row_values = |matrix: &Csr| -> Vec<E> {
        (0..rows)
            .map(|r| E::sum(matrix.row(r).iter().map(|&col| w_col[col as usize])))
            .collect()
    };
    let [a, b, c] = claims.row_forms([&row_values(&block.a), &row_values(&block.b), &row_values(&block.c)])?;
    Ok(a + claims.alpha * (b + claims.alpha * c))
}

/// Verify that `proof` shows every instance of a batch satisfies `block`, the instances' public words being `publics`
/// (`block.public_words()` per instance: the constant bit, the public bits, zero padding). With `spark`, the
/// block's matrix evaluation is checked against the SPARK proof the key was preprocessed for rather than evaluated.
///
/// A linked block takes its `boundary` (and only a linked block takes one), and its batch is exactly `2^n_log`
/// instances.
pub fn verify(
    block: &Block,
    publics: &[u64],
    boundary: Option<&Boundary>,
    log_inv_rate: usize,
    spark: Option<&spark::Key>,
    proof: &Proof,
) -> Result<(), VerifierError> {
    require(well_formed(block, publics), VerifierError::PublicWords)?;
    let public_words = block.public_words();
    let n_instances = publics.len() / public_words;
    let k_log = block.k_log;
    let n_log = batch_log(k_log, n_instances)?;
    let linked = match (block.links, boundary) {
        (None, None) => None,
        (Some(links), Some(boundary)) => {
            require(
                links.well_formed(block) && boundary.well_formed(&links) && n_instances == 1 << n_log,
                VerifierError::Links,
            )?;
            Some((links, boundary))
        }
        _ => return Err(VerifierError::Links),
    };
    let m = k_log + n_log;
    let qflock_vars = m - FLOCK_K_SKIP;
    let stack_log = qflock_vars.max(MIN_STACKED_LOG);
    let (iv, statement) = seed(block, n_instances, n_log, publics, boundary);
    let mut transcript = Transcript::new(proof, iv, statement, true);

    let halves = transcript.next_scalars(2)?;
    let root = Digest::from_halves(halves[0], halves[1])?;
    let mut zc = verify_flock_zerocheck(m, &mut transcript)?;
    let linked = match linked {
        Some((links, boundary)) => Some((
            links,
            boundary,
            verify_links(&links, boundary, k_log, &mut zc, &mut transcript)?,
        )),
        None => None,
    };
    let (claims, running) = verify_lincheck(zc, k_log - FLOCK_K_SKIP, &mut transcript)?;
    // The constant pin sits at column 0, so its weight is `s[0] eq(chi_in_prime, 0)`; moved across, it leaves the
    // matrix form alone.
    let zeros = vec![ZERO; claims.round_challenges.len()];
    let value = running + claims.alpha.pow(3) * claims.s[0] * eq_eval(&claims.chi_in_prime(), &zeros);
    if spark.is_none() {
        require(
            block_form(block, &claims)? == value,
            VerifierError::FlockLincheckTerminal,
        )?;
    }

    // The ring-switched slice claims (lincheck's, then the links'), then one strided claim per public word: the MLE
    // over the instances of that word, padding instances repeating the last real one, on the slot's column of the
    // packed witness. Last, a linked batch's `out` words of its last instance.
    let point = transcript.samples(n_log);
    let mut stack_claims: Vec<StackClaim> = Vec::with_capacity(3 + public_words);
    let map = RingMap::sample(&mut transcript);
    let qflock = Placement {
        variables: qflock_vars,
        index: 0,
        low: 0,
    };
    let ring_claims = std::iter::once((claims.point(), claims.s.as_slice()))
        .chain(linked.as_ref().map(|(_, _, (point, s))| (point.clone(), s.as_slice())));
    for (ring_point, s) in ring_claims {
        let (target, weight) = map.claim(ring_point, s);
        stack_claims.push((
            Box::new(move |x| qflock.eq_above(x) * weight(&x[..qflock_vars])),
            target,
        ));
    }
    let pin = |slot: usize, point: &[E]| {
        Placement {
            variables: n_log,
            index: slot as u64,
            low: k_log - FLOCK_K_SKIP,
        }
        .stack_point(point, stack_log)
    };
    for (slot, value) in public_evaluations(publics, public_words, &point)
        .into_iter()
        .enumerate()
    {
        let pin = pin(slot, &point);
        stack_claims.push((Box::new(move |x| eq_eval(&pin, x)), value));
    }
    if let Some((links, boundary, _)) = &linked {
        let last = vec![ONE; n_log];
        for (w, &word) in boundary.output.iter().enumerate() {
            let pin = pin(links.out_base / 64 + w, &last);
            stack_claims.push((Box::new(move |x| eq_eval(&pin, x)), K(word).into()));
        }
    }
    verify_stacked_opening(
        &mut transcript,
        root,
        stack_log,
        1 << qflock_vars,
        log_inv_rate,
        &stack_claims,
    )?;

    if let Some(key) = spark {
        spark::verify(key, k_log, &claims, value, log_inv_rate, &mut transcript)?;
    }
    transcript.finish()?;
    Ok(())
}

/// The link term, between the zerocheck and lincheck: takes `T` and the `in` boundary's part out of the A claim,
/// then reduces `T` to the 64 slices of the `out` block it returns with their point.
fn verify_links(
    links: &Links,
    boundary: &Boundary,
    k_log: usize,
    zc: &mut ZerocheckResult,
    transcript: &mut Transcript,
) -> Result<(Vec<E>, Vec<E>), VerifierError> {
    let (x_in, x_out) = zc.chi().split_at(k_log - FLOCK_K_SKIP);
    let x_out = x_out.to_vec();
    // The quirky row weight of link row `j`: the skip weight of its low bits times `eq(x_in, row / 64)`, one eq for
    // every 64 rows.
    let skip = lagrange_weights(K_BITS, zc.z_skip());
    let mut high = (usize::MAX, ZERO);
    let rho: Vec<E> = (links.first_row..links.first_row + links.count)
        .map(|row| {
            if high.0 != row >> FLOCK_K_SKIP {
                high = (
                    row >> FLOCK_K_SKIP,
                    eq_eval(x_in, &bits(row >> FLOCK_K_SKIP, x_in.len())),
                );
            }
            skip[row % K_BITS] * high.1
        })
        .collect();
    let input = E::sum(
        (0..links.count)
            .filter(|&j| boundary.input[j / 64] >> (j % 64) & 1 == 1)
            .map(|j| rho[j]),
    );
    let shifted = transcript.next_scalar()?;
    zc.add_to_a(shifted + eq_eval(&x_out, &vec![ZERO; x_out.len()]) * input);

    let (rounds, running) = sumcheck(transcript, shifted, 3, &vec![None; x_out.len()])?;
    let r_out: Vec<E> = rounds.into_iter().rev().collect();
    let (rounds, running) = sumcheck(transcript, running, 3, &vec![None; links.out_log - FLOCK_K_SKIP])?;
    let r_sub: Vec<E> = rounds.into_iter().rev().collect();
    let s = transcript.next_scalars(K_BITS)?;
    let eq_sub = eq_kernel(&r_sub);
    let form = E::sum(
        rho.iter()
            .enumerate()
            .map(|(j, &r)| r * eq_sub[j / K_BITS] * s[j % K_BITS]),
    );
    require(next_eval(&r_out, &x_out) * form == running, VerifierError::LinkTerminal)?;
    let block = bits(links.out_base >> links.out_log, k_log - links.out_log);
    Ok(([r_sub, block, r_out].concat(), s))
}

/// `value`'s low `length` bits as a boolean point, LSB first.
fn bits(value: usize, length: usize) -> Vec<E> {
    (0..length).map(|bit| E::new((value >> bit & 1) as u64, 0, 0)).collect()
}

/// The multilinear extension of `next(x, y)`, one iff `y = x + 1` as integers on little-endian bits, with no wrap:
/// `x` starts with `k` ones then a zero, `y` with `k` zeros then a one, and the bits above agree. `O(len)`.
pub fn next_eval(x: &[E], y: &[E]) -> E {
    assert_eq!(x.len(), y.len());
    let mut above = vec![ONE; x.len() + 1];
    for t in (0..x.len()).rev() {
        above[t] = above[t + 1] * (ONE + x[t] + y[t]);
    }
    let mut carry = ONE;
    let mut total = ZERO;
    for t in 0..x.len() {
        total += carry * (ONE + x[t]) * y[t] * above[t + 1];
        carry *= x[t] * (ONE + y[t]);
    }
    total
}

/// The lincheck terminal's row weights `e_row = eq(chi_in) ⊗ skip weights`, as an MLE over `k_log` coordinates.
fn row_weights_mle(claims: &FlockClaims, point: &[E]) -> E {
    let (low, high) = point.split_at(FLOCK_K_SKIP);
    let skip = lagrange_weights(K_BITS, claims.z_skip);
    dot(&skip, &eq_kernel(low)) * eq_eval(claims.chi_in(), high)
}

/// The lincheck terminal's column weights `w_col = eq(chi_in_prime) ⊗ s`, as an MLE over `k_log` coordinates.
fn column_weights_mle(claims: &FlockClaims, point: &[E]) -> E {
    let (low, high) = point.split_at(FLOCK_K_SKIP);
    dot(&claims.s, &eq_kernel(low)) * eq_eval(&claims.chi_in_prime(), high)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::multilinear::multilinear_eval;

    fn xorshift(mut state: u64) -> impl FnMut() -> u64 {
        move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        }
    }

    /// `next_eval` against its definition, `sum_{a < 2^n - 1} eq(x, a) eq(y, a + 1)`, and on boolean points.
    #[test]
    fn next_eval_matches_definition() {
        let mut next = xorshift(0x2545_F491_4F6C_DD1D);
        for n in 1..=5 {
            let mut random = || E::new(next(), next(), next());
            let x: Vec<E> = (0..n).map(|_| random()).collect();
            let y: Vec<E> = (0..n).map(|_| random()).collect();
            let expected =
                E::sum((0..(1usize << n) - 1).map(|a| eq_eval(&x, &bits(a, n)) * eq_eval(&y, &bits(a + 1, n))));
            assert_eq!(next_eval(&x, &y), expected, "n = {n}");
            for a in 0..1usize << n {
                for b in 0..1usize << n {
                    let one = if b == a + 1 { ONE } else { ZERO };
                    assert_eq!(next_eval(&bits(a, n), &bits(b, n)), one, "n = {n}, {a} -> {b}");
                }
            }
        }
    }

    /// The subset-sum evaluation of the public pins against one `multilinear_eval` per slot, with a padded batch.
    #[test]
    fn public_evaluations_match_multilinear_eval() {
        let mut next = xorshift(0x9E37_79B9_7F4A_7C15);
        let (words, n_instances, n_log) = (3, 21, 5);
        let publics: Vec<u64> = (0..words * n_instances).map(|_| next()).collect();
        let point: Vec<E> = (0..n_log).map(|_| E::new(next(), next(), next())).collect();
        let values = public_evaluations(&publics, words, &point);
        for (slot, &value) in values.iter().enumerate() {
            let column: Vec<K> = (0..1usize << n_log)
                .map(|i| K(publics[i.min(n_instances - 1) * words + slot]))
                .collect();
            assert_eq!(value, multilinear_eval(&column, &point).unwrap(), "slot {slot}");
        }
    }
}
