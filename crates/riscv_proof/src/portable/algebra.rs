//! Characteristic-two algebra with least-significant-bit-first cube points.
//!
//! Slice dimensions are protocol parameters validated by the verifier before
//! entering these infallible helpers. A mismatch is a programming error, not
//! implicit truncation or zero padding.

use super::transcript::MAX_ELEMENTS;
use alloc::vec::Vec;
use leanvm_guest::Field as F;

pub fn eq_eval(left: &[F], right: &[F]) -> F {
    assert_eq!(left.len(), right.len(), "equality point dimensions differ");
    left.iter()
        .zip(right)
        .fold(F::ONE, |value, (&x, &y)| value * (F::ONE + x + y))
}

pub fn eq_kernel(point: &[F]) -> Vec<F> {
    assert!(
        point.len() < usize::BITS as usize,
        "equality kernel dimension overflows"
    );
    let size = 1usize << point.len();
    assert!(size <= MAX_ELEMENTS, "unvalidated equality kernel dimension");
    let mut values = Vec::with_capacity(size);
    values.push(F::ONE);
    for &r in point {
        let width = values.len();
        for i in 0..width {
            let high = values[i] * r;
            values.push(high);
            values[i] += high;
        }
    }
    values
}

/// Evaluate without copying the input table or allocating an equality kernel.
pub fn mle_eval(table: &[F], point: &[F]) -> F {
    assert!(point.len() < usize::BITS as usize, "multilinear dimension overflows");
    assert_eq!(
        table.len(),
        1usize << point.len(),
        "multilinear table dimension differs"
    );
    fn evaluate(table: &[F], point: &[F]) -> F {
        match point.split_last() {
            None => table[0],
            Some((&high, low)) => {
                let (left, right) = table.split_at(table.len() / 2);
                let left = evaluate(left, low);
                left + high * (left + evaluate(right, low))
            }
        }
    }
    evaluate(table, point)
}

pub fn poly_eval(coefficients: &[F], point: F) -> F {
    let mut coefficients = coefficients.iter().rev();
    let Some(&leading) = coefficients.next() else {
        return F::ZERO;
    };
    coefficients.fold(leading, |value, &coefficient| value * point + coefficient)
}

pub fn powers(base: F, count: usize) -> Vec<F> {
    assert!(count <= MAX_ELEMENTS, "unvalidated powers count");
    let mut values = Vec::with_capacity(count);
    if count != 0 {
        values.push(F::ONE);
        for i in 1..count {
            values.push(values[i - 1] * base);
        }
    }
    values
}

pub fn dot(left: &[F], right: &[F]) -> F {
    assert_eq!(left.len(), right.len(), "dot product dimensions differ");
    left.iter().zip(right).fold(F::ZERO, |sum, (&x, &y)| sum + x * y)
}

/// MLE of [1,g,g²,...], where g is the base-field polynomial generator 2,
/// not the extension generator Y.
pub fn index_mle(point: &[F]) -> F {
    let mut result = F::ONE;
    let mut generator = F::new(2, 0, 0);
    for (i, &challenge) in point.iter().enumerate() {
        result *= F::ONE + challenge * (F::ONE + generator);
        if i + 1 != point.len() {
            generator = generator.square();
        }
    }
    result
}

pub fn log2_ceil(value: usize) -> usize {
    if value <= 1 {
        0
    } else {
        (usize::BITS - (value - 1).leading_zeros()) as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cube_point_uses_low_bit_first_and_index_uses_base_generator() {
        let table = [F::new(9, 0, 0), F::new(7, 0, 0), F::new(5, 0, 0), F::new(3, 0, 0)];
        for (index, &expected) in table.iter().enumerate() {
            let point = [F::new((index & 1) as u64, 0, 0), F::new((index >> 1) as u64, 0, 0)];
            assert_eq!(mle_eval(&table, &point), expected);
            assert_eq!(dot(&table, &eq_kernel(&point)), expected);
            assert_eq!(index_mle(&point), F::new(2, 0, 0).pow(index as u64));
        }
        let point = [F::new(6, 7, 8), F::new(9, 10, 11)];
        assert_eq!(mle_eval(&table, &point), dot(&table, &eq_kernel(&point)));
    }
}
