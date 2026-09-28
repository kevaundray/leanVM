// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Bounded Flock reduction and the public fused-add BLAKE2s matrix walk.
//! All witness-dependent decisions are checked field masks, including the
//! equality-tail length and the inactive suffix of the zerocheck.
use leanvm_guest::Field;

use crate::Error;
use crate::algebra::{dot, eq_eval, eq_kernel, poly_eval};
use crate::context::Context;
use crate::protocol::{DIM_BITS, Dimension, MAX_STACK_VARS, Point, SliceFamily};
use crate::transcript::Transcript;
use crate::uint::Uint;

const SKIP: usize = 6;
const SLICES: usize = 1 << SKIP;
const BLAKE2S_LOG_SIZE: usize = 14;
const BLAKE2S_ONE_PIN: usize = 512;
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

fn phi_node(index: usize) -> Field {
    let mut word = 0;
    for (bit, basis) in PHI_BASIS.iter().enumerate() {
        if index & (1 << bit) != 0 {
            word ^= basis;
        }
    }
    Field::from(word)
}

fn fixed_challenges() -> &'static [Field; 7] {
    static FIXED: std::sync::LazyLock<[Field; 7]> = std::sync::LazyLock::new(|| {
        let mut result = [Field::ZERO; 7];
        result[..3].copy_from_slice(&[phi_node(0xF7), phi_node(0x53), phi_node(0xB5)]);
        let mut generator = Field([0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0]);
        for value in &mut result[3..] {
            *value = generator * (Field::ONE + generator).inverse().expect("fixed generator is not one");
            generator = generator.square();
        }
        result
    });
    &FIXED
}

/// Prefix/suffix products avoid division by `point + node`, including when
/// the challenge is exactly an interpolation node. Only a public nonzero
/// barycentric denominator is inverted, never a witness-dependent value.
pub(crate) fn lagrange_weights<C: Context>(ctx: &C, count: usize, point: C::F) -> Result<Vec<C::F>, Error> {
    if !count.is_power_of_two() || count > 256 {
        return Err(Error::InvalidInput);
    }
    let mut weights = Vec::with_capacity(count);
    let mut prefix = ctx.one();
    let mut denominator = Field::ONE;
    for i in 0..count {
        weights.push(prefix);
        let node = phi_node(i);
        prefix = ctx.mul(prefix, ctx.add(point, ctx.constant(node)));
        if i != 0 {
            denominator *= node;
        }
    }
    let mut suffix = ctx.constant(denominator.inverse().ok_or(Error::InvalidCircuit)?);
    for i in (0..count).rev() {
        weights[i] = ctx.mul(weights[i], suffix);
        suffix = ctx.mul(suffix, ctx.add(point, ctx.constant(phi_node(i))));
    }
    Ok(weights)
}

pub(crate) struct ZerocheckResult<F: Copy> {
    pub z_skip: F,
    pub chi: Point<F>,
    pub v_a: F,
    pub v_b: F,
    pub v_c: F,
}

pub(crate) fn verify_flock_zerocheck<C: Context>(
    log_n: &Dimension<C::F>,
    enabled: C::F,
    transcript: &mut Transcript<C>,
) -> Result<ZerocheckResult<C::F>, Error> {
    let ctx = transcript.context();
    ctx.assert_bool(enabled)?;
    ctx.assert_equal_if(enabled, log_n.contains(SKIP + 6), ctx.one())?;
    // Subtraction is integer arithmetic, not characteristic-two addition.
    // An absent family has the canonical empty suffix regardless of log_n.
    let skip = Uint::constant(ctx, SKIP as u64, DIM_BITS);
    let effective = Uint::select(ctx, enabled, log_n.bits(), &skip);
    let (tail, borrow) = effective.sub(ctx, &skip);
    ctx.assert_zero(borrow)?;
    let dim = Dimension::from_uint(ctx, tail, MAX_STACK_VARS)?;
    let mut equality = [ctx.zero(); MAX_STACK_VARS];
    for (slot, &fixed) in equality[..7].iter_mut().zip(fixed_challenges()) {
        *slot = ctx.mul(enabled, ctx.constant(fixed));
    }
    for (i, slot) in equality.iter_mut().enumerate().skip(7) {
        *slot = transcript.sample(ctx.mul(enabled, dim.contains(i)))?;
    }
    let coset = (0..SLICES)
        .map(|_| transcript.scalar(enabled))
        .collect::<Result<Vec<_>, _>>()?;
    let z_skip = transcript.sample(enabled)?;
    let weights = lagrange_weights(ctx, 2 * SLICES, z_skip)?;
    let mut running = ctx.mul(enabled, dot(ctx, &weights[SLICES..], &coset));
    let mut chi = Point::zero(ctx, dim);
    for (i, &eq) in equality.iter().enumerate() {
        let live = ctx.mul(enabled, chi.dim.contains(i));
        let message = transcript.round_poly(live, 3, running, Some(eq))?;
        let challenge = transcript.sample(live)?;
        chi.coords[i] = challenge;
        running = ctx.select(live, poly_eval(ctx, &message, challenge), running);
    }
    let v_a = transcript.scalar(enabled)?;
    let v_b = transcript.scalar(enabled)?;
    let v_c = ctx.mul(enabled, ctx.add(running, ctx.mul(v_a, v_b)));
    Ok(ZerocheckResult {
        z_skip,
        chi,
        v_a,
        v_b,
        v_c,
    })
}

/// Batched A/B/C lincheck plus native integer one/zero-column pins. The
/// callback must evaluate public wiring; matrix evaluations are not advice.
pub(crate) fn verify_lincheck<C: Context>(
    zc: ZerocheckResult<C::F>,
    enabled: C::F,
    k_log: usize,
    one_pin: usize,
    zero_pin: Option<usize>,
    bilinear: impl FnOnce(&C, C::F, &[C::F], &[C::F]) -> Result<C::F, Error>,
    transcript: &mut Transcript<C>,
) -> Result<SliceFamily<C::F>, Error> {
    if !(SKIP..=MAX_STACK_VARS).contains(&k_log) {
        return Err(Error::InvalidInput);
    }
    let rounds = k_log - SKIP;
    let width = 1usize << k_log;
    if one_pin >= width || zero_pin.is_some_and(|pin| pin >= width) {
        return Err(Error::InvalidInput);
    }
    let ctx = transcript.context();
    ctx.assert_bool(enabled)?;
    if rounds != 0 {
        ctx.assert_equal_if(enabled, zc.chi.dim.contains(rounds - 1), ctx.one())?;
    }
    ctx.assert_zero(ctx.mul(enabled, zc.chi.dim.contains(MAX_STACK_VARS)))?;
    let dim_bits = Uint::select(ctx, enabled, zc.chi.dim.bits(), &Uint::constant(ctx, 0, DIM_BITS));
    let dim = Dimension::from_uint(ctx, dim_bits, MAX_STACK_VARS)?;
    let alpha = transcript.sample(enabled)?;
    let alpha2 = ctx.mul(alpha, alpha);
    let alpha3 = ctx.mul(alpha2, alpha);
    let skip_weights = lagrange_weights(ctx, SLICES, zc.z_skip)?;
    let chi_in = &zc.chi.coords[..rounds];
    let mut rows = Vec::with_capacity(width);
    for weight in eq_kernel(ctx, chi_in) {
        rows.extend(skip_weights.iter().map(|&value| ctx.mul(weight, value)));
    }
    let mut running = ctx.mul(
        enabled,
        ctx.add(
            ctx.add(zc.v_a, ctx.mul(alpha, zc.v_b)),
            ctx.add(ctx.mul(alpha2, zc.v_c), alpha3),
        ),
    );
    let mut point = Point::zero(ctx, dim);
    for i in 0..rounds {
        let message = transcript.round_poly(enabled, 3, running, None)?;
        let challenge = transcript.sample(enabled)?;
        // Lincheck eliminates high coordinates first; canonical points are LSB-first.
        point.coords[rounds - 1 - i] = challenge;
        running = ctx.select(enabled, poly_eval(ctx, &message, challenge), running);
    }
    let mut slices = [ctx.zero(); SLICES];
    for slice in &mut slices {
        *slice = transcript.scalar(enabled)?;
    }
    let mut columns = Vec::with_capacity(width);
    for weight in eq_kernel(ctx, &point.coords[..rounds]) {
        columns.extend(slices.iter().map(|&value| ctx.mul(weight, value)));
    }
    let c_term = ctx.mul(
        ctx.mul(alpha2, eq_eval(ctx, chi_in, &point.coords[..rounds])),
        dot(ctx, &skip_weights, &slices),
    );
    let mut terminal = ctx.add(
        ctx.add(bilinear(ctx, alpha, &rows, &columns)?, c_term),
        ctx.mul(alpha3, columns[one_pin]),
    );
    if let Some(pin) = zero_pin {
        terminal = ctx.add(terminal, ctx.mul(ctx.mul(alpha2, alpha2), columns[pin]));
    }
    ctx.assert_equal_if(enabled, terminal, running)?;
    for i in rounds..MAX_STACK_VARS {
        point.coords[i] = ctx.mul(ctx.mul(enabled, point.dim.contains(i)), zc.chi.coords[i]);
    }
    Ok(SliceFamily { enabled, point, slices })
}

pub(crate) fn verify_flock<C: Context>(
    log_n: &Dimension<C::F>,
    enabled: C::F,
    transcript: &mut Transcript<C>,
) -> Result<SliceFamily<C::F>, Error> {
    let zc = verify_flock_zerocheck(log_n, enabled, transcript)?;
    verify_lincheck(
        zc,
        enabled,
        BLAKE2S_LOG_SIZE,
        BLAKE2S_ONE_PIN,
        None,
        blake2s_bilinear,
        transcript,
    )
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
type Word<F> = [F; 32];

fn slots<F: Copy>(columns: &[F], base: usize) -> Word<F> {
    std::array::from_fn(|bit| columns[base + bit])
}
fn literal<C: Context>(ctx: &C, value: u32, constant: C::F) -> Word<C::F> {
    std::array::from_fn(|bit| if value & (1 << bit) != 0 { constant } else { ctx.zero() })
}
fn xor<C: Context>(ctx: &C, a: &Word<C::F>, b: &Word<C::F>) -> Word<C::F> {
    std::array::from_fn(|bit| ctx.add(a[bit], b[bit]))
}
fn rotate_right<F: Copy>(word: &Word<F>, amount: usize) -> Word<F> {
    std::array::from_fn(|bit| word[(bit + amount) & 31])
}

/// Each live public matrix row is consumed once; padded rows contribute zero.
struct MatrixWalk<'a, C: Context> {
    ctx: &'a C,
    alpha: C::F,
    rows: &'a [C::F],
    columns: &'a [C::F],
    total: C::F,
}
impl<C: Context> MatrixWalk<'_, C> {
    fn row(&mut self, index: usize, a: C::F, b: C::F) {
        let ctx = self.ctx;
        self.total = ctx.add(
            self.total,
            ctx.mul(self.rows[index], ctx.add(a, ctx.mul(self.alpha, b))),
        );
    }

    fn add(&mut self, x: &Word<C::F>, y: &Word<C::F>, carry_base: usize) -> Word<C::F> {
        let ctx = self.ctx;
        let mut carry = ctx.zero();
        let mut output = [ctx.zero(); 32];
        for bit in 0..32 {
            if bit < 31 {
                self.row(carry_base + bit, ctx.add(x[bit], carry), ctx.add(y[bit], carry));
            }
            output[bit] = ctx.add(ctx.add(x[bit], y[bit]), carry);
            if bit < 31 {
                carry = ctx.add(carry, self.columns[carry_base + bit]);
            }
        }
        output
    }

    fn add3(&mut self, x: &Word<C::F>, y: &Word<C::F>, z: &Word<C::F>, base: usize) -> Word<C::F> {
        let ctx = self.ctx;
        let mut majority = [ctx.zero(); 31];
        for bit in 0..31 {
            self.row(base + bit, ctx.add(x[bit], z[bit]), ctx.add(y[bit], z[bit]));
            majority[bit] = ctx.add(self.columns[base + bit], z[bit]);
        }
        let ripple_base = base + 31;
        let mut carry = ctx.zero();
        let mut output = [ctx.zero(); 32];
        for bit in 0..32 {
            let q = if bit == 0 { ctx.zero() } else { majority[bit - 1] };
            let left = ctx.add(ctx.add(ctx.add(x[bit], y[bit]), z[bit]), carry);
            output[bit] = ctx.add(left, q);
            if (1..=30).contains(&bit) {
                self.row(ripple_base + bit - 1, left, ctx.add(q, carry));
                carry = ctx.add(carry, self.columns[ripple_base + bit - 1]);
            }
        }
        output
    }
}

/// Evaluate row^T (A + alpha B) column from the actual ten-round BLAKE2s
/// wiring, including fused additions, input/output rows and constant row.
pub(crate) fn blake2s_bilinear<C: Context>(
    ctx: &C,
    alpha: C::F,
    rows: &[C::F],
    columns: &[C::F],
) -> Result<C::F, Error> {
    let size = 1 << BLAKE2S_LOG_SIZE;
    if rows.len() != size || columns.len() != size {
        return Err(Error::InvalidInput);
    }
    let constant = columns[BLAKE2S_ONE_PIN];
    let mut circuit = MatrixWalk {
        ctx,
        alpha,
        rows,
        columns,
        total: ctx.zero(),
    };
    for (base, len) in [(0, 256), (640, 512), (1152, 128)] {
        for row in base..base + len {
            circuit.row(row, columns[row], constant);
        }
    }
    let mut state = [[ctx.zero(); 32]; 16];
    for word in 0..8 {
        state[word] = slots(columns, 32 * word);
    }
    for word in 0..4 {
        state[8 + word] = literal(ctx, IV[word], constant);
        state[12 + word] = xor(
            ctx,
            &literal(ctx, IV[4 + word], constant),
            &slots(columns, 1152 + 32 * word),
        );
    }
    for (round, sigma) in SIGMA.iter().enumerate() {
        for (gate, &[a, b, c, d]) in G_LANES.iter().enumerate() {
            let base = 1280 + 184 * (8 * round + gate);
            let mx = slots(columns, 640 + 32 * sigma[2 * gate]);
            let my = slots(columns, 640 + 32 * sigma[2 * gate + 1]);
            let a1 = circuit.add3(&state[a], &state[b], &mx, base);
            let d1 = rotate_right(&xor(ctx, &state[d], &a1), 16);
            let c1 = circuit.add(&state[c], &d1, base + 61);
            let b1 = rotate_right(&xor(ctx, &state[b], &c1), 12);
            let a2 = circuit.add3(&a1, &b1, &my, base + 92);
            let d2 = rotate_right(&xor(ctx, &d1, &a2), 8);
            let c2 = circuit.add(&c1, &d2, base + 153);
            let b2 = rotate_right(&xor(ctx, &b1, &c2), 7);
            state[a] = a2;
            state[b] = b2;
            state[c] = c2;
            state[d] = d2;
        }
    }
    for word in 0..8 {
        let output = xor(
            ctx,
            &xor(ctx, &state[word], &state[word + 8]),
            &slots(columns, 32 * word),
        );
        for (bit, value) in output.into_iter().enumerate() {
            circuit.row(256 + 32 * word + bit, value, constant);
        }
    }
    circuit.row(BLAKE2S_ONE_PIN, constant, constant);
    Ok(circuit.total)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::{Source, Symbolic, Witness};
    use fiat_shamir::transcript::{Challenger, ProverState, RawProof, VerifierState};
    use primitives::field::{F64, F192};

    fn field(value: F192) -> Field {
        Field::new(value.c0, value.c1, value.c2)
    }
    fn native(value: Field) -> F192 {
        F192::new(value.0[0], value.0[1], value.0[2])
    }

    #[test]
    fn interpolation_nodes_and_extension_points_match_portable() {
        for count in [1, 64, 128, 256] {
            let symbolic = Symbolic::new(1);
            let weights = lagrange_weights(&symbolic, count, symbolic.public(0).unwrap()).unwrap();
            let circuit = symbolic.finish();
            for point in [
                phi_node(0),
                phi_node(count / 2),
                phi_node(count - 1),
                Field::new(7, 9, 11),
            ] {
                let ctx = Witness::new(&[], Vec::new());
                let actual = lagrange_weights(&ctx, count, point).unwrap();
                let expected = riscv_proof::portable::flock::lagrange_weights(count, point).unwrap();
                assert_eq!(actual, expected);
                let private = ctx.finish().unwrap();
                let values = circuit.evaluate(&[point], &private).unwrap();
                for (wire, &expected) in weights.iter().zip(&expected) {
                    assert_eq!(values[wire.index()], expected);
                }
                if let Some(index) = (0..count).find(|&i| phi_node(i) == point) {
                    for (i, weight) in actual.into_iter().enumerate() {
                        assert_eq!(weight, if i == index { Field::ONE } else { Field::ZERO });
                    }
                }
            }
        }
    }

    fn zerocheck_program<C: Context>(ctx: &C) -> Result<Vec<C::F>, Error> {
        let enabled = ctx.public(0)?;
        let log_n = Dimension::new(ctx, ctx.public(1)?, 34)?;
        let mut transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        let zc = verify_flock_zerocheck(&log_n, enabled, &mut transcript)?;
        let mut out = vec![zc.z_skip, zc.v_a, zc.v_b, zc.v_c, zc.chi.dim.value(ctx)];
        out.extend(zc.chi.coords);
        out.extend(transcript.state());
        // This is deliberately live after an absent family as well.
        out.push(transcript.scalar(ctx.one())?);
        Ok(out)
    }

    #[test]
    fn one_symbolic_zerocheck_handles_live_dimensions_and_absence() {
        let symbolic = Symbolic::new(2);
        let output = zerocheck_program(&symbolic).unwrap();
        let circuit = symbolic.finish();
        for (enabled, log_n) in [(true, 13), (true, 14), (true, 34), (false, 0), (false, 34)] {
            let count = if enabled { 64 + 2 * (log_n - 6) + 2 } else { 0 };
            let mut stream: Vec<_> = (0..count)
                .map(|i| Field::new(i as u64 + 1, 3 * i as u64 + 7, 11))
                .collect();
            let sentinel = Field::new(0xfedc, 0xba98, 0x7654);
            stream.push(sentinel);
            let proof = riscv_proof::Proof {
                stream,
                merkle: Vec::new(),
            };
            let public = [Field::from(u64::from(enabled)), Field::from(log_n as u64)];
            let ctx = Witness::new(&public, vec![Source::Risc(&proof)]);
            let actual = zerocheck_program(&ctx).unwrap();
            let mut reference = riscv_proof::portable::transcript::Transcript::new(&proof, [0; 32], [0; 32]);
            if enabled {
                let expected = riscv_proof::portable::flock::verify_flock_zerocheck(log_n, &mut reference).unwrap();
                assert_eq!(
                    &actual[..5],
                    &[
                        expected.z_skip,
                        expected.v_a,
                        expected.v_b,
                        expected.v_c,
                        Field::from((log_n - 6) as u64)
                    ]
                );
                assert_eq!(&actual[5..5 + log_n - 6], &expected.chi);
                assert!(actual[5 + log_n - 6..39].iter().all(|&value| value == Field::ZERO));
            } else {
                assert!(actual[..39].iter().all(|&value| value == Field::ZERO));
                let empty = Witness::new(&[], Vec::new());
                let initial = Transcript::new(&empty, 0, [Field::ZERO; 4], [Field::ZERO; 4]).unwrap();
                assert_eq!(&actual[39..43], &initial.state());
            }
            assert_eq!(reference.next_scalar().unwrap(), sentinel);
            reference.finish().unwrap();
            assert_eq!(actual[43], sentinel);
            let private = ctx.finish().unwrap();
            let values = circuit.evaluate(&public, &private).unwrap();
            for (wire, expected) in output.iter().zip(actual) {
                assert_eq!(values[wire.index()], expected);
            }
        }
        for (enabled, log_n) in [(Field::ONE, 12), (Field::ONE, 35), (Field::from(2), 13)] {
            let public = [enabled, Field::from(log_n)];
            let ctx = Witness::new(&public, vec![Source::Advice(&[])]);
            assert!(zerocheck_program(&ctx).is_err());
        }
    }

    #[test]
    fn public_blake2s_matrix_matches_production_walk() {
        let rows: Vec<_> = (0..1 << BLAKE2S_LOG_SIZE)
            .map(|i| Field::new(i as u64 * 17 + 3, i as u64 ^ 0xdead, 5))
            .collect();
        let columns: Vec<_> = (0..rows.len())
            .map(|i| Field::new(i as u64 * 31 + 9, 7, i as u64 ^ 0xbeef))
            .collect();
        let alpha = Field::new(13, 17, 19);
        let (a, b) = flock::hash::bilinear_walk_pair(
            &rows.iter().copied().map(native).collect::<Vec<_>>(),
            &columns.iter().copied().map(native).collect::<Vec<_>>(),
        );
        let ctx = Witness::new(&[], Vec::new());
        assert_eq!(
            blake2s_bilinear(&ctx, alpha, &rows, &columns).unwrap(),
            field(a + native(alpha) * b)
        );
        let mut pin_rows = vec![Field::ZERO; rows.len()];
        let mut pin_columns = pin_rows.clone();
        pin_rows[BLAKE2S_ONE_PIN] = Field::ONE;
        pin_columns[BLAKE2S_ONE_PIN] = Field::Y;
        assert_eq!(
            blake2s_bilinear(&ctx, alpha, &pin_rows, &pin_columns).unwrap(),
            (Field::ONE + alpha) * Field::Y
        );
    }

    fn flock_program<C: Context>(ctx: &C) -> Result<Vec<C::F>, Error> {
        let enabled = ctx.public(0)?;
        let log_n = Dimension::new(ctx, ctx.public(1)?, 34)?;
        let mut transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        let family = verify_flock(&log_n, enabled, &mut transcript)?;
        let mut out = vec![family.point.dim.value(ctx)];
        out.extend(family.point.coords);
        out.extend(family.slices);
        out.push(transcript.sample(ctx.one())?);
        Ok(out)
    }

    #[test]
    fn real_flock_proof_matches_prover_native_and_symbolic_verifiers() {
        let setup = flock::hash::Blake2sSetup::new(1);
        let blocks = [flock::hash::padding_block()];
        let mut prover = ProverState::new([F64::ZERO; 4], [F64::ZERO; 4]);
        let (_, expected) = setup.prove_reduction(&blocks, &mut prover);
        let next_challenge = field(prover.sample());
        let proof = prover.into_proof();
        let mut reference = VerifierState::new([F64::ZERO; 4], &proof, [F64::ZERO; 4]);
        assert_eq!(setup.verify_reduction(&mut reference).unwrap().claim, expected);
        assert_eq!(field(reference.sample()), next_challenge);
        let raw = RawProof {
            stream: proof.stream,
            merkle: Vec::new(),
        };
        let public = [Field::ONE, Field::from(setup.m() as u64)];
        let ctx = Witness::new(&public, vec![Source::Native(&raw)]);
        let actual = flock_program(&ctx).unwrap();
        let dimension = expected.suffix_point.len();
        assert_eq!(actual[0], Field::from(dimension as u64));
        assert_eq!(
            &actual[1..1 + dimension],
            &expected.suffix_point.iter().copied().map(field).collect::<Vec<_>>()
        );
        assert!(actual[1 + dimension..35].iter().all(|&value| value == Field::ZERO));
        assert_eq!(
            &actual[35..99],
            &expected.s_hat_v.iter().copied().map(field).collect::<Vec<_>>()
        );
        assert_eq!(actual[99], next_challenge);
        let private = ctx.finish().unwrap();
        let symbolic = Symbolic::new(2);
        let output = flock_program(&symbolic).unwrap();
        let circuit = symbolic.finish();
        let values = circuit.evaluate(&public, &private).unwrap();
        for (wire, expected) in output.iter().zip(&actual) {
            assert_eq!(values[wire.index()], *expected);
        }
        let inactive_public = [Field::ZERO, Field::ZERO];
        let inactive = Witness::new(&inactive_public, vec![Source::Advice(&[])]);
        let absent = flock_program(&inactive).unwrap();
        assert!(absent[..99].iter().all(|&value| value == Field::ZERO));
        let values = circuit.evaluate(&inactive_public, &inactive.finish().unwrap()).unwrap();
        for (wire, expected) in output.iter().zip(absent) {
            assert_eq!(values[wire.index()], expected);
        }
        // The final slice enters the public matrix relation, not just transport.
        let mut corrupted = raw.clone();
        *corrupted.stream.last_mut().unwrap() += F192::ONE;
        let bad = Witness::new(&public, vec![Source::Native(&corrupted)]);
        assert!(flock_program(&bad).is_err());
    }

    fn pin_program<C: Context>(ctx: &C, zero_pin: Option<usize>) -> Result<SliceFamily<C::F>, Error> {
        let enabled = ctx.public(0)?;
        let mut transcript = Transcript::new(ctx, 0, [ctx.zero(); 4], [ctx.zero(); 4])?;
        let zc = ZerocheckResult {
            z_skip: ctx.zero(),
            chi: Point::zero(ctx, Dimension::constant(ctx, 0)),
            v_a: ctx.zero(),
            v_b: ctx.zero(),
            v_c: ctx.zero(),
        };
        // A=B=0, C=I at the first interpolation node; pin column 1 to one,
        // and optionally column 2 to zero. There are no lincheck rounds.
        verify_lincheck(
            zc,
            enabled,
            6,
            1,
            zero_pin,
            |ctx, _, _, _| Ok(ctx.zero()),
            &mut transcript,
        )
    }

    #[test]
    fn terminal_identity_enforces_one_and_optional_zero_pins() {
        let mut slices = [Field::ZERO; 64];
        slices[1] = Field::ONE;
        let public = [Field::ONE];
        let symbolic = Symbolic::new(1);
        let output = pin_program(&symbolic, Some(2)).unwrap();
        let circuit = symbolic.finish();
        let ctx = Witness::new(&public, vec![Source::Advice(&slices)]);
        let family = pin_program(&ctx, Some(2)).unwrap();
        assert_eq!(family.slices, slices);
        let private = ctx.finish().unwrap();
        let values = circuit.evaluate(&public, &private).unwrap();
        assert_eq!(values[output.slices[1].index()], Field::ONE);
        for index in [0, 1, 2] {
            let mut changed = slices;
            changed[index] += Field::ONE;
            let bad = Witness::new(&public, vec![Source::Advice(&changed)]);
            assert!(pin_program(&bad, Some(2)).is_err());
        }
        let mut unpinned = slices;
        unpinned[2] = Field::ONE;
        let ctx = Witness::new(&public, vec![Source::Advice(&unpinned)]);
        assert!(pin_program(&ctx, None).is_ok());
        let inactive_public = [Field::ZERO];
        let ctx = Witness::new(&inactive_public, vec![Source::Advice(&[])]);
        let family = pin_program(&ctx, Some(2)).unwrap();
        assert_eq!(family.slices, [Field::ZERO; 64]);
        let values = circuit.evaluate(&inactive_public, &ctx.finish().unwrap()).unwrap();
        assert_eq!(values[output.slices[1].index()], Field::ZERO);
    }
}
