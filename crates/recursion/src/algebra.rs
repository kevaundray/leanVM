//! Characteristic-two algebra with low-bit-first cube coordinates.

use crate::{
    Error,
    context::Context,
    protocol::{Dimension, MAX_VARS},
};

const MAX_ELEMENTS: usize = 1 << 24;

pub(crate) fn poly_eval<C: Context>(ctx: &C, coefficients: &[C::F], point: C::F) -> C::F {
    let mut coefficients = coefficients.iter().rev();
    let Some(&leading) = coefficients.next() else {
        return ctx.zero();
    };
    coefficients.fold(leading, |value, &coefficient| {
        ctx.add(ctx.mul(value, point), coefficient)
    })
}

pub(crate) fn dot<C: Context>(ctx: &C, left: &[C::F], right: &[C::F]) -> C::F {
    assert_eq!(left.len(), right.len(), "dot product dimensions differ");
    left.iter()
        .zip(right)
        .fold(ctx.zero(), |sum, (&x, &y)| ctx.add(sum, ctx.mul(x, y)))
}

pub(crate) fn eq_eval<C: Context>(ctx: &C, left: &[C::F], right: &[C::F]) -> C::F {
    assert_eq!(left.len(), right.len(), "equality point dimensions differ");
    left.iter().zip(right).fold(ctx.one(), |product, (&x, &y)| {
        ctx.mul(product, ctx.add(ctx.one(), ctx.add(x, y)))
    })
}

pub(crate) fn eq_prefix<C: Context>(
    ctx: &C,
    left: &[C::F],
    right: &[C::F],
    dimension: &Dimension<C::F>,
) -> Result<C::F, Error> {
    let length = left.len().min(right.len()).min(MAX_VARS);
    if length < MAX_VARS {
        ctx.assert_zero(dimension.contains(length))?;
    }
    let mut product = ctx.one();
    for i in 0..length {
        // Inactive factors are one, not zero. The cached masks are checked
        // Boolean by Dimension's bounded integer construction.
        product = ctx.mul(
            product,
            ctx.add(ctx.one(), ctx.mul(dimension.contains(i), ctx.add(left[i], right[i]))),
        );
    }
    Ok(product)
}

pub(crate) fn eq_kernel<C: Context>(ctx: &C, point: &[C::F]) -> Vec<C::F> {
    assert!(
        point.len() < usize::BITS as usize,
        "equality kernel dimension overflows"
    );
    let size = 1usize << point.len();
    assert!(size <= MAX_ELEMENTS, "unvalidated equality kernel dimension");
    let mut values = Vec::with_capacity(size);
    values.push(ctx.one());
    for &r in point {
        let width = values.len();
        for i in 0..width {
            let high = ctx.mul(values[i], r);
            values.push(high);
            values[i] = ctx.add(values[i], high);
        }
    }
    values
}

pub(crate) fn mle_eval<C: Context>(ctx: &C, table: &[C::F], point: &[C::F]) -> C::F {
    assert!(point.len() < usize::BITS as usize, "multilinear dimension overflows");
    assert_eq!(
        table.len(),
        1usize << point.len(),
        "multilinear table dimension differs"
    );
    fn evaluate<C: Context>(ctx: &C, table: &[C::F], point: &[C::F]) -> C::F {
        match point.split_last() {
            None => table[0],
            Some((&high, low)) => {
                let (left, right) = table.split_at(table.len() / 2);
                let left = evaluate(ctx, left, low);
                ctx.add(left, ctx.mul(high, ctx.add(left, evaluate(ctx, right, low))))
            }
        }
    }
    evaluate(ctx, table, point)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::{Symbolic, Witness};
    use leanvm_guest::Field;

    #[test]
    fn equality_prefix_uses_one_fixed_program_and_masks_the_suffix() {
        fn program<C: Context>(ctx: &C) -> Result<C::F, Error> {
            let dim = Dimension::new(ctx, ctx.public(0)?, 3)?;
            let left: Vec<_> = (1..4).map(|i| ctx.public(i)).collect::<Result<_, _>>()?;
            let right: Vec<_> = (4..7).map(|i| ctx.public(i)).collect::<Result<_, _>>()?;
            eq_prefix(ctx, &left, &right, &dim)
        }
        let ctx = Symbolic::new(7);
        let output = program(&ctx).unwrap();
        let circuit = ctx.finish();
        let mut public = [
            Field::ZERO,
            Field::new(2, 3, 5),
            Field::new(7, 11, 13),
            Field::new(17, 19, 23),
            Field::new(29, 31, 37),
            Field::new(41, 43, 47),
            Field::new(53, 59, 61),
        ];
        for dimension in 0..=3 {
            public[0] = Field::from(dimension as u64);
            let witness = Witness::new(&public, vec![]);
            let actual = program(&witness).unwrap();
            let expected =
                riscv_proof::portable::algebra::eq_eval(&public[1..1 + dimension], &public[4..4 + dimension]);
            assert_eq!(actual, expected);
            let values = circuit.evaluate(&public, &witness.finish().unwrap()).unwrap();
            assert_eq!(values[output.index()], expected);
        }
        public[0] = Field::from(4);
        assert!(program(&Witness::new(&public, vec![])).is_err());
        assert!(circuit.evaluate(&public, &[]).is_err());
    }

    #[test]
    fn low_bit_cube_helpers_match_portable_extension_arithmetic() {
        let ctx = Witness::new(&[], vec![]);
        let point = [Field::new(6, 7, 8), Field::new(9, 10, 11)];
        let table = [Field::from(9), Field::from(7), Field::from(5), Field::from(3)];
        let expected = riscv_proof::portable::algebra::mle_eval(&table, &point);
        assert_eq!(mle_eval(&ctx, &table, &point), expected);
        assert_eq!(dot(&ctx, &table, &eq_kernel(&ctx, &point)), expected);
        assert_eq!(
            poly_eval(&ctx, &table, point[0]),
            riscv_proof::portable::algebra::poly_eval(&table, point[0])
        );
    }
}
