//! Packed GF(2) circuit validity and physical-column projection reductions.
//!
//! Both reductions leave 64 low-wire slices of the same committed bit cube.
use crate::portable::{
    algebra::{eq_kernel, poly_eval},
    flock,
    transcript::Transcript,
};
use crate::{
    Error,
    packed::{PackedCircuit, PackedGate, PackedSpec},
};
use alloc::{vec, vec::Vec};
use leanvm_guest::Field;

const SKIP: usize = 6;
const SLICES: usize = 1 << SKIP;

#[derive(Clone, Debug)]
pub struct BitClaim {
    pub point: Vec<Field>,
    pub slices: Vec<Field>,
}

// Each A row has at most two entries, each B row at most one. Duplicate
// entries deliberately cancel in characteristic two, including XOR(x, x).
#[cfg(feature = "host")]
fn terms(gate: &PackedGate, output: usize) -> ([usize; 2], usize, Option<usize>) {
    match *gate {
        PackedGate::Input => ([output, 0], 1, Some(1)),
        PackedGate::Zero => ([0, 0], 0, None),
        PackedGate::One => ([1, 0], 1, Some(1)),
        PackedGate::Xor(a, b) => ([a, b], 2, Some(1)),
        PackedGate::And(a, b) => ([a, 0], 1, Some(b)),
    }
}

fn shape(spec: &PackedSpec, tau: usize, point_len: usize, values_len: usize) -> Result<(), Error> {
    let k_log = spec.circuit.k_log;
    if k_log < 10
        || tau < 3
        || k_log
            .checked_add(tau)
            .is_none_or(|m| m > crate::portable::pcs::MAX_STACKED_LOG + SKIP)
        || point_len != tau
        || values_len != spec.circuit.aliases.len()
        || spec.circuit.gates.len() != 1usize << k_log
        || spec.circuit.zero_pin >= spec.circuit.gates.len()
    {
        return Err(Error::InvalidShape);
    }
    Ok(())
}

fn bilinear(circuit: &PackedCircuit, alpha: Field, rows: &[Field], columns: &[Field]) -> Field {
    let mut result = Field::ZERO;
    let alpha_one = alpha * columns[1];
    for (output, gate) in circuit.gates.iter().enumerate() {
        let value = match *gate {
            PackedGate::Zero => continue,
            PackedGate::Input => columns[output] + alpha_one,
            PackedGate::One => columns[1] + alpha_one,
            PackedGate::Xor(a, b) => columns[a] + columns[b] + alpha_one,
            PackedGate::And(a, b) => columns[a] + alpha * columns[b],
        };
        result += rows[output] * value;
    }
    result
}

fn projection_terminal(circuit: &PackedCircuit, gamma: Field, point: &[Field], slices: &[Field]) -> Field {
    let weights = eq_kernel(point);
    let mut coefficients = [Field::ZERO; SLICES];
    let mut scaled = [Field::ZERO; 64];
    let mut power = Field::ONE;
    for (column, aliases) in circuit.aliases.iter().enumerate() {
        if column != 0 {
            power *= gamma;
        }
        if power.is_zero() {
            break;
        }
        let mut high = usize::MAX;
        let mut scaled_len = 0;
        for &(wire, mut coefficient) in aliases {
            let next_high = wire / SLICES;
            if coefficient == 0 || weights[next_high].is_zero() {
                continue;
            }
            if next_high != high {
                high = next_high;
                scaled[0] = power * weights[high];
                scaled_len = 1;
            }
            // Share gamma^column * eq(high) across adjacent aliases. Base
            // coefficients are linear combinations of x^i, not ECALL products.
            while coefficient != 0 {
                let bit = coefficient.trailing_zeros() as usize;
                while scaled_len <= bit {
                    scaled[scaled_len] = scaled[scaled_len - 1].mul_base_generator();
                    scaled_len += 1;
                }
                coefficients[wire % SLICES] += scaled[bit];
                coefficient &= coefficient - 1;
            }
        }
    }
    coefficients
        .iter()
        .zip(slices)
        .filter(|(coefficient, slice)| !coefficient.is_zero() && !slice.is_zero())
        .fold(Field::ZERO, |sum, (&coefficient, &slice)| sum + coefficient * slice)
}

/// Independently verify public circuit matrices and projection coefficients.
pub fn verify(
    spec: &PackedSpec,
    tau: usize,
    column_point: &[Field],
    column_values: &[Field],
    t: &mut Transcript<'_>,
) -> Result<Vec<BitClaim>, Error> {
    shape(spec, tau, column_point.len(), column_values.len())?;
    let circuit = &spec.circuit;
    let zc = flock::verify_flock_zerocheck(circuit.k_log + tau, t)?;
    let (point, slices) = flock::verify_lincheck(
        zc,
        circuit.k_log,
        1,
        Some(circuit.zero_pin),
        |alpha, rows, columns| Ok(bilinear(circuit, alpha, rows, columns)),
        t,
    )?;
    let first = BitClaim { point, slices };
    let gamma = t.sample();
    let mut running = poly_eval(column_values, gamma);
    let mut point = Vec::with_capacity(circuit.k_log - SKIP + tau);
    for _ in SKIP..circuit.k_log {
        let q = t.sumcheck_round_poly(3, running, None)?;
        let r = t.sample();
        running = poly_eval(&q, r);
        point.push(r);
    }
    point.reverse();
    let slices = t.next_scalars(SLICES)?;
    if projection_terminal(circuit, gamma, &point, &slices) != running {
        return Err(Error::InvalidProof);
    }
    point.extend_from_slice(column_point);
    Ok(vec![first, BitClaim { point, slices }])
}

#[cfg(feature = "host")]
mod native {
    use super::*;
    use crate::packed::PackedRow;
    use ::flock::{
        lincheck::{self, LincheckCircuit, QuirkyPoint},
        zerocheck,
    };
    use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
    use pcs::ring_switch::inner_product_ext;
    use primitives::{
        field::{F64, F192},
        multilinear::eq_table,
    };

    fn field(value: F192) -> Field {
        Field([value.c0, value.c1, value.c2])
    }
    fn claim(point: Vec<F192>, slices: Vec<F192>) -> BitClaim {
        BitClaim {
            point: point.into_iter().map(field).collect(),
            slices: slices.into_iter().map(field).collect(),
        }
    }

    struct Circuit<'a>(&'a PackedCircuit);
    impl LincheckCircuit for Circuit<'_> {
        fn n_cols(&self) -> usize {
            1usize << self.0.k_log
        }
        fn const_pin_col(&self) -> usize {
            1
        }
        fn zero_pin_col(&self) -> Option<usize> {
            Some(self.0.zero_pin)
        }
        fn fold_alpha_batched(&self, alpha: F192, weights: &[F192]) -> Vec<F192> {
            let mut out = vec![F192::ZERO; self.n_cols()];
            for (output, gate) in self.0.gates.iter().enumerate() {
                let (a, count, b) = terms(gate, output);
                for &column in &a[..count] {
                    out[column] += weights[output];
                }
                if let Some(column) = b {
                    out[column] += alpha * weights[output];
                }
            }
            out
        }
        fn bilinear_form(&self, alpha: F192, rows: &[F192], columns: &[F192]) -> Option<F192> {
            let mut result = F192::ZERO;
            let alpha_one = alpha * columns[1];
            for (output, gate) in self.0.gates.iter().enumerate() {
                let value = match *gate {
                    PackedGate::Zero => continue,
                    PackedGate::Input => columns[output] + alpha_one,
                    PackedGate::One => columns[1] + alpha_one,
                    PackedGate::Xor(a, b) => columns[a] + columns[b] + alpha_one,
                    PackedGate::And(a, b) => columns[a] + alpha * columns[b],
                };
                result += rows[output] * value;
            }
            Some(result)
        }
    }

    fn quirky(zc: &zerocheck::ZerocheckClaim, k_log: usize) -> QuirkyPoint {
        QuirkyPoint {
            z_skip: zc.z,
            x_inner_rest: zc.mlv_challenges[..k_log - SKIP].to_vec(),
            x_outer: zc.mlv_challenges[k_log - SKIP..].to_vec(),
        }
    }

    fn projection_native(circuit: &PackedCircuit, gamma: F192, values: &[F192]) -> (Vec<F192>, F192) {
        let mut psi = vec![F192::ZERO; 1usize << circuit.k_log];
        let mut power = F192::ONE;
        let mut target = F192::ZERO;
        for (aliases, &value) in circuit.aliases.iter().zip(values) {
            target += power * value;
            for &(wire, coefficient) in aliases {
                psi[wire] += power.mul_base(F64(coefficient));
            }
            power *= gamma;
        }
        (psi, target)
    }

    fn projection_terminal_native(circuit: &PackedCircuit, gamma: F192, point: &[F192], slices: &[F192]) -> F192 {
        let weights = eq_table(point);
        let mut coefficients = [F192::ZERO; SLICES];
        let mut power = F192::ONE;
        for (column, aliases) in circuit.aliases.iter().enumerate() {
            if column != 0 {
                power *= gamma;
            }
            if power == F192::ZERO {
                break;
            }
            let mut high = usize::MAX;
            let mut scaled = F192::ZERO;
            for &(wire, coefficient) in aliases {
                let next_high = wire / SLICES;
                if coefficient == 0 || weights[next_high] == F192::ZERO {
                    continue;
                }
                if next_high != high {
                    high = next_high;
                    scaled = power * weights[high];
                }
                coefficients[wire % SLICES] += scaled.mul_base(F64(coefficient));
            }
        }
        coefficients
            .iter()
            .zip(slices)
            .filter(|(coefficient, slice)| **coefficient != F192::ZERO && **slice != F192::ZERO)
            .fold(F192::ZERO, |sum, (&coefficient, &slice)| sum + coefficient * slice)
    }

    fn bit(row: &PackedRow, wire: usize) -> u8 {
        ((row.bits[wire / 64] >> (wire % 64)) & 1) as u8
    }

    // Both layouts are byte-packed. No field-per-bit or unpacked gate witness
    // is ever allocated: ZC scans row-major bytes, LC scans eight-row stripes.
    fn witness(circuit: &PackedCircuit, rows: &[PackedRow]) -> (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>) {
        let width = 1usize << circuit.k_log;
        let bytes = rows.len() * (width / 8);
        let mut a = vec![0; bytes];
        let mut b = vec![0; bytes];
        let mut z = Vec::with_capacity(bytes);
        let mut striped = vec![0; bytes];
        for (row_index, row) in rows.iter().enumerate() {
            for &word in &row.bits {
                z.extend_from_slice(&word.to_le_bytes());
            }
            for (wire, gate) in circuit.gates.iter().enumerate() {
                let (columns, count, b_column) = terms(gate, wire);
                let mut av = 0;
                for &column in &columns[..count] {
                    av ^= bit(row, column);
                }
                let bv = b_column.map_or(0, |column| bit(row, column));
                let byte = row_index * (width / 8) + wire / 8;
                a[byte] |= av << (wire % 8);
                b[byte] |= bv << (wire % 8);
                striped[(row_index / 8) * width + wire] |= bit(row, wire) << (row_index % 8);
            }
        }
        (a, b, z, striped)
    }

    fn fold_rows(striped: &[u8], width: usize, point: &[F192]) -> Vec<F192> {
        let weights = eq_table(point);
        let mut out = vec![F192::ZERO; width];
        let mut sums = [F192::ZERO; 256];
        for (stripe, eq) in striped.chunks_exact(width).zip(weights.chunks_exact(8)) {
            for (bit, &weight) in eq.iter().enumerate() {
                for index in 0..1usize << bit {
                    sums[index + (1 << bit)] = sums[index] + weight;
                }
            }
            for (value, &byte) in out.iter_mut().zip(stripe) {
                *value += sums[byte as usize];
            }
        }
        out
    }

    fn bind_top(values: &mut Vec<F192>, r: F192) {
        let half = values.len() / 2;
        for index in 0..half {
            let low = values[index];
            let high = values[index + half];
            values[index] = low + r * (low + high);
        }
        values.truncate(half);
    }

    /// Prove circuit validity, followed by the gamma-batched physical projection.
    pub fn prove(
        spec: &PackedSpec,
        tau: usize,
        rows: &[PackedRow],
        column_point: &[F192],
        column_values: &[F192],
        ps: &mut ProverState,
    ) -> Result<Vec<BitClaim>, Error> {
        shape(spec, tau, column_point.len(), column_values.len())?;
        let circuit = &spec.circuit;
        let width = 1usize << circuit.k_log;
        if rows.len() != 1usize << tau
            || rows
                .iter()
                .any(|row| row.bits.len() != width / 64 || row.values.len() != column_values.len())
        {
            return Err(Error::InvalidShape);
        }
        let (a, b, z, striped) = witness(circuit, rows);
        let m = circuit.k_log + tau;
        // Dense padding prevents an invalid padded wire from escaping the R1CS.
        let zc = zerocheck::prove_packed_padded(&a, &b, &z, m, &zerocheck::PaddingSpec::dense(m), ps);
        drop((a, b, z));
        let x = quirky(&zc, circuit.k_log);
        let lc =
            lincheck::prove_padded_capture_s_hat_v(&striped, m, circuit.k_log, SKIP, width, &Circuit(circuit), &x, ps);
        let mut point = lc.r_inner_rest;
        point.extend_from_slice(&x.x_outer);
        let first = claim(point, lc.s_hat_v);
        let (mut psi, mut running) = projection_native(circuit, ps.sample(), column_values);
        let mut folded = fold_rows(&striped, width, column_point);
        drop(striped);
        if inner_product_ext(&psi, &folded) != running {
            return Err(Error::InvalidExecution);
        }
        let mut point = Vec::with_capacity(circuit.k_log - SKIP + tau);
        for _ in SKIP..circuit.k_log {
            let half = psi.len() / 2;
            let mut e1 = F192::ZERO;
            let mut einf = F192::ZERO;
            for index in 0..half {
                e1 += psi[index + half] * folded[index + half];
                einf += (psi[index] + psi[index + half]) * (folded[index] + folded[index + half]);
            }
            let e0 = running + e1;
            let q = [e0, e0 + e1 + einf, einf];
            ps.add_round_poly(&q, false);
            let r = ps.sample();
            running = primitives::multilinear::poly_eval(&q, r);
            point.push(r);
            bind_top(&mut psi, r);
            bind_top(&mut folded, r);
        }
        for &value in &folded {
            ps.add_scalar(value);
        }
        point.reverse();
        point.extend_from_slice(column_point);
        Ok(vec![first, claim(point, folded)])
    }

    /// Replay the same two reductions using native field arithmetic.
    pub fn verify_native(
        spec: &PackedSpec,
        tau: usize,
        column_point: &[F192],
        column_values: &[F192],
        vs: &mut VerifierState<'_>,
    ) -> Result<Vec<BitClaim>, Error> {
        shape(spec, tau, column_point.len(), column_values.len())?;
        let circuit = &spec.circuit;
        let m = circuit.k_log + tau;
        let zc = zerocheck::verify(m, vs).map_err(|_| Error::InvalidProof)?;
        let x = quirky(&zc, circuit.k_log);
        let lc = lincheck::verify(
            m,
            circuit.k_log,
            SKIP,
            &Circuit(circuit),
            &x,
            zc.a_eval,
            zc.b_eval,
            zc.c_eval,
            vs,
        )
        .map_err(|_| Error::InvalidProof)?;
        let mut point = lc.r_inner_rest;
        point.extend_from_slice(&x.x_outer);
        let first = claim(point, lc.s_hat_v);
        let gamma = vs.sample();
        let mut running = primitives::multilinear::poly_eval(column_values, gamma);
        let mut point = Vec::with_capacity(circuit.k_log - SKIP + tau);
        for _ in SKIP..circuit.k_log {
            let q = vs.next_round_poly(3, running, None).map_err(|_| Error::InvalidProof)?;
            let r = vs.sample();
            running = primitives::multilinear::poly_eval(&q, r);
            point.push(r);
        }
        point.reverse();
        let slices = vs.next_scalars(SLICES).map_err(|_| Error::InvalidProof)?;
        if projection_terminal_native(circuit, gamma, &point, &slices) != running {
            return Err(Error::InvalidProof);
        }
        point.extend_from_slice(column_point);
        Ok(vec![first, claim(point, slices)])
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::{circuit::Circuit as RawCircuit, schema::TableSpec};

        #[test]
        fn sparse_projection_matches_dense_with_alias_cancellation_and_base_reduction() {
            let mut circuit = PackedSpec::new(&TableSpec::new(RawCircuit::default())).circuit;
            circuit.aliases = vec![
                vec![(63, 1), (64, 1 << 63), (65, 0x8000_0000_0000_001b), (63, 1)],
                vec![(130, 3), (131, 1 << 62), (130, 3), (66, 0), (66, 7)],
                vec![],
                vec![(1023, u64::MAX), (1, 1), (1023, 1 << 63)],
            ];
            let values = vec![
                F192::new(0x8123, 17, 1 << 63),
                F192::ZERO,
                F192::new(71, u64::MAX, 23),
                F192::ONE,
            ];
            let slices: Vec<_> = (0..SLICES)
                .map(|i| {
                    if i % 7 == 0 {
                        F192::ZERO
                    } else {
                        F192::new(i as u64, u64::MAX - i as u64, 1 << (i % 64))
                    }
                })
                .collect();
            let points = [
                vec![
                    F192::new(17, 19, 23),
                    F192::new(31, 37, 41),
                    F192::new(43, 47, 53),
                    F192::new(59, 61, 67),
                ],
                vec![F192::ZERO, F192::ONE, F192::ZERO, F192::ONE],
            ];
            let portable_values: Vec<_> = values.iter().copied().map(field).collect();
            let portable_slices: Vec<_> = slices.iter().copied().map(field).collect();
            for gamma in [F192::ZERO, F192::ONE, F192::new(0x8000_0000_0000_0000, u64::MAX, 29)] {
                let (psi, target) = projection_native(&circuit, gamma, &values);
                assert_eq!(poly_eval(&portable_values, field(gamma)), field(target));
                for point in &points {
                    let dense = eq_table(point)
                        .into_iter()
                        .enumerate()
                        .fold(F192::ZERO, |sum, (high, weight)| {
                            sum + weight * inner_product_ext(&psi[high * SLICES..(high + 1) * SLICES], &slices)
                        });
                    let portable_point: Vec<_> = point.iter().copied().map(field).collect();
                    assert_eq!(projection_terminal_native(&circuit, gamma, point, &slices), dense);
                    assert_eq!(
                        projection_terminal(&circuit, field(gamma), &portable_point, &portable_slices),
                        field(dense)
                    );
                }
            }
        }
    }
}

#[cfg(feature = "host")]
pub use native::{prove, verify_native};
