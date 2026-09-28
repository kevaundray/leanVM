use crate::{Error, context::Context, uint::Uint};

pub(crate) const MAX_VARS: usize = 34;
pub(crate) const MAX_STACK_VARS: usize = 28;
pub(crate) const DIM_BITS: usize = 6;

#[derive(Clone)]
pub(crate) struct Dimension<F: Copy> {
    bits: Uint<F>,
    active: [F; MAX_VARS],
}

impl<F: Copy> Dimension<F> {
    pub(crate) fn new<C: Context<F = F>>(ctx: &C, value: F, maximum: usize) -> Result<Self, Error> {
        Self::from_uint(ctx, Uint::from_field(ctx, value, DIM_BITS)?, maximum)
    }

    pub(crate) fn from_uint<C: Context<F = F>>(ctx: &C, bits: Uint<F>, maximum: usize) -> Result<Self, Error> {
        if maximum > MAX_VARS || bits.width() != DIM_BITS {
            return Err(Error::InvalidInput);
        }
        let bound = Uint::constant(ctx, (maximum + 1) as u64, DIM_BITS);
        ctx.assert_equal(bits.lt(ctx, &bound), ctx.one())?;
        let active = std::array::from_fn(|index| {
            if index >= maximum {
                ctx.zero()
            } else {
                Uint::constant(ctx, index as u64, DIM_BITS).lt(ctx, &bits)
            }
        });
        Ok(Self { bits, active })
    }

    pub(crate) fn constant<C: Context<F = F>>(ctx: &C, value: usize) -> Self {
        assert!(value <= MAX_VARS);
        Self {
            bits: Uint::constant(ctx, value as u64, DIM_BITS),
            active: std::array::from_fn(|index| ctx.base(u64::from(index < value))),
        }
    }

    pub(crate) fn bits(&self) -> &Uint<F> {
        &self.bits
    }
    pub(crate) fn value<C: Context<F = F>>(&self, ctx: &C) -> F {
        self.bits.value(ctx)
    }
    pub(crate) fn contains(&self, index: usize) -> F {
        self.active[index]
    }

    pub(crate) fn equals<C: Context<F = F>>(&self, ctx: &C, value: usize) -> F {
        if value > MAX_VARS {
            return ctx.zero();
        }
        let before = if value == 0 { ctx.one() } else { self.active[value - 1] };
        let after = if value == MAX_VARS {
            ctx.zero()
        } else {
            self.active[value]
        };
        ctx.add(before, after)
    }
}

#[derive(Clone)]
pub(crate) struct Point<F: Copy> {
    pub dim: Dimension<F>,
    pub coords: [F; MAX_VARS],
}

impl<F: Copy> Point<F> {
    pub(crate) fn zero<C: Context<F = F>>(ctx: &C, dim: Dimension<F>) -> Self {
        Self {
            dim,
            coords: [ctx.zero(); MAX_VARS],
        }
    }
}

pub(crate) struct SliceFamily<F: Copy> {
    pub enabled: F,
    pub point: Point<F>,
    pub slices: [F; 64],
}
