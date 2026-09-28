// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Flock zerocheck and lincheck for the current fused-add BLAKE2s R1CS.
#[cfg(test)]
use alloc::vec;
use alloc::vec::Vec;
use leanvm_guest::Field as F;

use super::algebra::{dot, eq_eval, eq_kernel, poly_eval};
use super::transcript::{Error, Transcript};

pub const BLAKE2S_R1CS_LOG_SIZE: usize = 14;
pub const K_BITS: usize = 64;
pub const FLOCK_K_SKIP: usize = 6;
pub const FLOCK_NUM_LINCHECK_ROUNDS: usize = BLAKE2S_R1CS_LOG_SIZE - FLOCK_K_SKIP;
pub const BLAKE2S_CONSTANT_COLUMN: usize = 512;

const PHI_BASIS: [u64; 8] = [
    0x0000000000000001,
    0x033CE8BEDDC8A656,
    0x512620375ED2A108,
    0x0C9E636090AAFC01,
    0xBA4F3CD82801769C,
    0xBA26E7904ADB4A47,
    0x467698598926DC01,
    0x4418AE808B28BDD0,
];

fn phi_node(index: usize) -> F {
    let mut word = 0;
    for (bit, basis) in PHI_BASIS.iter().enumerate() {
        if index & (1 << bit) != 0 {
            word ^= basis;
        }
    }
    F([word, 0, 0])
}

fn fixed_challenges() -> [F; 7] {
    let mut result = [F::ZERO; 7];
    result[..3].copy_from_slice(&[phi_node(0xF7), phi_node(0x53), phi_node(0xB5)]);
    let mut generator = F([0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0]);
    for value in &mut result[3..] {
        *value = generator * (F::ONE + generator).inverse().expect("fixed generator is not one");
        generator = generator.square();
    }
    result
}

/// Division-free numerator interpolation also works when point is a node.
/// Power-of-two prefixes have one common nonzero barycentric denominator.
pub fn lagrange_weights(count: usize, point: F) -> Result<Vec<F>, Error> {
    if !count.is_power_of_two() || count > 256 {
        return Err(Error::InvalidShape);
    }
    let mut weights = Vec::with_capacity(count);
    let mut prefix = F::ONE;
    let mut denominator = F::ONE;
    for i in 0..count {
        weights.push(prefix);
        let node = phi_node(i);
        prefix *= point + node;
        if i != 0 {
            denominator *= node;
        }
    }
    let mut suffix = denominator.inverse().ok_or(Error::InvalidShape)?;
    for i in (0..count).rev() {
        weights[i] *= suffix;
        suffix *= point + phi_node(i);
    }
    Ok(weights)
}

pub struct ZerocheckResult {
    pub z_skip: F,
    pub chi: Vec<F>,
    pub v_a: F,
    pub v_b: F,
    pub v_c: F,
}

pub fn verify_flock_zerocheck(log_n: usize, transcript: &mut Transcript<'_>) -> Result<ZerocheckResult, Error> {
    if !(FLOCK_K_SKIP + 7..=super::pcs::MAX_STACKED_LOG + FLOCK_K_SKIP).contains(&log_n) {
        return Err(Error::InvalidShape);
    }
    let mut r = Vec::with_capacity(log_n - FLOCK_K_SKIP);
    r.extend_from_slice(&fixed_challenges());
    r.extend(transcript.samples(log_n - FLOCK_K_SKIP - r.len()));
    let coset = transcript.next_scalars(K_BITS)?;
    let z_skip = transcript.sample();
    let weights = lagrange_weights(2 * K_BITS, z_skip)?;
    let mut running = dot(&weights[K_BITS..], &coset);
    let mut chi = Vec::with_capacity(r.len());
    for equality in r {
        let message = transcript.sumcheck_round_poly(3, running, Some(equality))?;
        let challenge = transcript.sample();
        chi.push(challenge);
        running = poly_eval(&message, challenge);
    }
    let v_a = transcript.next_scalar()?;
    let v_b = transcript.next_scalar()?;
    Ok(ZerocheckResult {
        z_skip,
        chi,
        v_a,
        v_b,
        v_c: running + v_a * v_b,
    })
}

pub fn verify_flock_lincheck(zc: ZerocheckResult, transcript: &mut Transcript<'_>) -> Result<(Vec<F>, Vec<F>), Error> {
    verify_lincheck(
        zc,
        BLAKE2S_R1CS_LOG_SIZE,
        BLAKE2S_CONSTANT_COLUMN,
        None,
        blake2s_bilinear,
        transcript,
    )
}

/// Public-circuit lincheck. The matrix callback is derived from circuit wiring,
/// never from prover-announced matrix evaluations.
pub fn verify_lincheck(
    zc: ZerocheckResult,
    k_log: usize,
    one_pin: usize,
    zero_pin: Option<usize>,
    bilinear: impl FnOnce(F, &[F], &[F]) -> Result<F, Error>,
    transcript: &mut Transcript<'_>,
) -> Result<(Vec<F>, Vec<F>), Error> {
    if !(FLOCK_K_SKIP..=super::pcs::MAX_STACKED_LOG).contains(&k_log) {
        return Err(Error::InvalidShape);
    }
    let rounds = k_log - FLOCK_K_SKIP;
    let width = 1usize << k_log;
    if one_pin >= width
        || zero_pin.is_some_and(|pin| pin >= width)
        || zc.chi.len() < rounds
        || zc.chi.len() > super::pcs::MAX_STACKED_LOG
    {
        return Err(Error::InvalidShape);
    }
    let alpha = transcript.sample();
    let alpha2 = alpha.square();
    let alpha3 = alpha2 * alpha;
    let skip_weights = lagrange_weights(K_BITS, zc.z_skip)?;
    let chi_in = &zc.chi[..rounds];
    let mut e_row = Vec::with_capacity(width);
    for weight in eq_kernel(chi_in) {
        e_row.extend(skip_weights.iter().map(|&value| weight * value));
    }
    let mut running = zc.v_a + alpha * zc.v_b + alpha2 * zc.v_c + alpha3;
    let mut point = Vec::with_capacity(zc.chi.len());
    for _ in 0..rounds {
        let message = transcript.sumcheck_round_poly(3, running, None)?;
        let challenge = transcript.sample();
        point.push(challenge);
        running = poly_eval(&message, challenge);
    }
    let slices = transcript.next_scalars(K_BITS)?;
    // Lincheck eliminates high coordinates first; the rest of the protocol is LSB-first.
    point.reverse();
    let mut w_col = Vec::with_capacity(width);
    for weight in eq_kernel(&point) {
        w_col.extend(slices.iter().map(|&value| weight * value));
    }
    let mut terminal = bilinear(alpha, &e_row, &w_col)?
        + alpha2 * eq_eval(chi_in, &point) * dot(&skip_weights, &slices)
        + alpha3 * w_col[one_pin];
    if let Some(pin) = zero_pin {
        terminal += alpha2.square() * w_col[pin];
    }
    if terminal != running {
        return Err(Error::ClaimMismatch);
    }
    point.extend_from_slice(&zc.chi[rounds..]);
    Ok((point, slices))
}

pub fn verify_flock(log_n: usize, transcript: &mut Transcript<'_>) -> Result<(Vec<F>, Vec<F>), Error> {
    let zc = verify_flock_zerocheck(log_n, transcript)?;
    verify_flock_lincheck(zc, transcript)
}

const IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];
const SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];
const G_LANES: [[usize; 4]; 8] = [
    [0, 4, 8, 12],
    [1, 5, 9, 13],
    [2, 6, 10, 14],
    [3, 7, 11, 15],
    [0, 5, 10, 15],
    [1, 6, 11, 12],
    [2, 7, 8, 13],
    [3, 4, 9, 14],
];
type Word = [F; 32];

fn slots(columns: &[F], base: usize) -> Word {
    core::array::from_fn(|bit| columns[base + bit])
}
fn literal(value: u32, constant: F) -> Word {
    core::array::from_fn(|bit| if value & (1 << bit) != 0 { constant } else { F::ZERO })
}
fn xor(a: &Word, b: &Word) -> Word {
    core::array::from_fn(|bit| a[bit] + b[bit])
}
fn rotate_right(word: &Word, amount: usize) -> Word {
    core::array::from_fn(|bit| word[(bit + amount) & 31])
}

/// Consume each nonzero matrix row once; no sparse matrices or two full row
/// vectors are allocated. Unused R1CS rows contribute exactly zero.
struct Circuit<'a> {
    alpha: F,
    rows: &'a [F],
    columns: &'a [F],
    total: F,
}

impl Circuit<'_> {
    fn row(&mut self, index: usize, a: F, b: F) {
        self.total += self.rows[index] * (a + self.alpha * b);
    }

    fn add(&mut self, x: &Word, y: &Word, carry_base: usize) -> Word {
        let mut carry = F::ZERO;
        let mut output = [F::ZERO; 32];
        for bit in 0..32 {
            if bit < 31 {
                self.row(carry_base + bit, x[bit] + carry, y[bit] + carry);
            }
            output[bit] = x[bit] + y[bit] + carry;
            if bit < 31 {
                carry += self.columns[carry_base + bit];
            }
        }
        output
    }

    fn add3(&mut self, x: &Word, y: &Word, z: &Word, base: usize) -> Word {
        let mut majority = [F::ZERO; 31];
        for bit in 0..31 {
            self.row(base + bit, x[bit] + z[bit], y[bit] + z[bit]);
            majority[bit] = self.columns[base + bit] + z[bit];
        }
        let ripple_base = base + 31;
        let mut carry = F::ZERO;
        let mut output = [F::ZERO; 32];
        for bit in 0..32 {
            let q = if bit == 0 { F::ZERO } else { majority[bit - 1] };
            let left = x[bit] + y[bit] + z[bit] + carry;
            output[bit] = left + q;
            if (1..=30).contains(&bit) {
                self.row(ripple_base + bit - 1, left, q + carry);
                carry += self.columns[ripple_base + bit - 1];
            }
        }
        output
    }
}

/// Evaluate e_row^T (A0 + alpha B0) w_col for the actual 10-round circuit.
/// This evaluates matrix entries from the circuit wiring, never from proof data.
pub fn blake2s_bilinear(alpha: F, rows: &[F], columns: &[F]) -> Result<F, Error> {
    let size = 1 << BLAKE2S_R1CS_LOG_SIZE;
    if rows.len() != size || columns.len() != size {
        return Err(Error::InvalidShape);
    }
    let constant = columns[BLAKE2S_CONSTANT_COLUMN];
    let mut circuit = Circuit {
        alpha,
        rows,
        columns,
        total: F::ZERO,
    };
    for (base, len) in [(0, 256), (640, 512), (1152, 128)] {
        for row in base..base + len {
            circuit.row(row, columns[row], constant);
        }
    }
    let mut state = [[F::ZERO; 32]; 16];
    for word in 0..8 {
        state[word] = slots(columns, 32 * word);
    }
    for word in 0..4 {
        state[8 + word] = literal(IV[word], constant);
        state[12 + word] = xor(&literal(IV[4 + word], constant), &slots(columns, 1152 + 32 * word));
    }
    for (round, sigma) in SIGMA.iter().enumerate() {
        for (gate, &[a, b, c, d]) in G_LANES.iter().enumerate() {
            let base = 1280 + 184 * (8 * round + gate);
            let mx = slots(columns, 640 + 32 * sigma[2 * gate]);
            let my = slots(columns, 640 + 32 * sigma[2 * gate + 1]);
            let a1 = circuit.add3(&state[a], &state[b], &mx, base);
            let d1 = rotate_right(&xor(&state[d], &a1), 16);
            let c1 = circuit.add(&state[c], &d1, base + 61);
            let b1 = rotate_right(&xor(&state[b], &c1), 12);
            let a2 = circuit.add3(&a1, &b1, &my, base + 92);
            let d2 = rotate_right(&xor(&d1, &a2), 8);
            let c2 = circuit.add(&c1, &d2, base + 153);
            let b2 = rotate_right(&xor(&b1, &c2), 7);
            state[a] = a2;
            state[b] = b2;
            state[c] = c2;
            state[d] = d2;
        }
    }
    for word in 0..8 {
        let output = xor(&xor(&state[word], &state[word + 8]), &slots(columns, 32 * word));
        for (bit, value) in output.into_iter().enumerate() {
            circuit.row(256 + 32 * word + bit, value, constant);
        }
    }
    circuit.row(BLAKE2S_CONSTANT_COLUMN, constant, constant);
    Ok(circuit.total)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interpolation_at_nodes_including_zero() {
        for index in [0, 1, 63, 64, 127] {
            let weights = lagrange_weights(128, phi_node(index)).unwrap();
            for (i, value) in weights.into_iter().enumerate() {
                assert_eq!(value, if i == index { F::ONE } else { F::ZERO });
            }
        }
    }

    #[test]
    fn constant_pin_matrix_entry() {
        let mut rows = vec![F::ZERO; 1 << BLAKE2S_R1CS_LOG_SIZE];
        let mut columns = rows.clone();
        rows[BLAKE2S_CONSTANT_COLUMN] = F::ONE;
        columns[BLAKE2S_CONSTANT_COLUMN] = F::Y;
        let alpha = F([7, 9, 11]);
        assert_eq!(
            blake2s_bilinear(alpha, &rows, &columns).unwrap(),
            (F::ONE + alpha) * F::Y
        );
        columns[BLAKE2S_CONSTANT_COLUMN] += F::ONE;
        assert_ne!(
            blake2s_bilinear(alpha, &rows, &columns).unwrap(),
            (F::ONE + alpha) * F::Y
        );
    }
}
