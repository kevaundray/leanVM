use crate::{
    Error, algebra,
    context::Context,
    opening,
    protocol::{Dimension, MAX_STACK_VARS, Point, SliceFamily},
    ring::RingMap,
    transcript::Transcript,
    uint::Uint,
};

pub(crate) struct PointClaim<F: Copy> {
    pub enabled: F,
    pub offset: Uint<F>,
    pub point: Point<F>,
    pub value: F,
}

pub(crate) struct RingOpening<F: Copy> {
    pub offset: Uint<F>,
    pub family: SliceFamily<F>,
}

// Offsets are aligned placements from the authenticated or checked layout.
pub(crate) fn selector<C: Context>(ctx: &C, offset: &Uint<C::F>, low: &Dimension<C::F>, point: &Point<C::F>) -> C::F {
    assert_eq!(offset.width(), 32);
    let mut product = ctx.one();
    for index in 0..MAX_STACK_VARS {
        let active = ctx.mul(point.dim.contains(index), ctx.not(low.contains(index)));
        let difference = ctx.add(point.coords[index], offset.bits()[index]);
        product = ctx.mul(product, ctx.not(ctx.mul(active, difference)));
    }
    product
}

fn check_placement<C: Context>(
    ctx: &C,
    enabled: C::F,
    offset: &Uint<C::F>,
    low: &Dimension<C::F>,
    high: &Dimension<C::F>,
) -> Result<(), Error> {
    if offset.width() != 32 {
        return Err(Error::InvalidInput);
    }
    ctx.assert_equal_if(enabled, high.bits().lt(ctx, low.bits()), ctx.zero())?;
    for index in 0..32 {
        let allowed = ctx.mul(high.contains(index), ctx.not(low.contains(index)));
        ctx.assert_zero(ctx.mul(ctx.mul(enabled, ctx.not(allowed)), offset.bits()[index]))?;
    }
    Ok(())
}

pub(crate) fn verify<C: Context>(
    transcript: &mut Transcript<'_, C>,
    enabled: C::F,
    log_n: &Dimension<C::F>,
    log_inv_rate: &Uint<C::F>,
    n_lanes: &Uint<C::F>,
    root: [C::F; 4],
    points: &[PointClaim<C::F>],
    rings: &[RingOpening<C::F>],
) -> Result<(), Error> {
    let ctx = transcript.context();
    ctx.assert_bool(enabled)?;
    let mut any_ring = ctx.zero();
    for ring in rings {
        ctx.assert_bool(ring.family.enabled)?;
        let active = ctx.mul(enabled, ring.family.enabled);
        check_placement(ctx, active, &ring.offset, &ring.family.point.dim, log_n)?;
        any_ring = ctx.or(any_ring, active);
    }
    let map = if rings.is_empty() {
        None
    } else {
        Some(RingMap::sample(transcript, any_ring)?)
    };
    let mut switched = Vec::with_capacity(rings.len());
    if let Some(map) = &map {
        for ring in rings {
            switched.push(map.switch(ctx, &ring.family.point, &ring.family.slices)?);
        }
    }
    let lambda = transcript.sample(enabled)?;
    let mut power = ctx.one();
    let mut target = ctx.zero();
    let mut ring_weights = Vec::with_capacity(rings.len());
    for (ring, claim) in rings.iter().zip(&switched) {
        let active = ctx.mul(enabled, ring.family.enabled);
        let weight = ctx.mul(active, power);
        target = ctx.add(target, ctx.mul(weight, claim.target));
        ring_weights.push(weight);
        power = ctx.select(active, ctx.mul(power, lambda), power);
    }
    let mut point_weights = Vec::with_capacity(points.len());
    for claim in points {
        ctx.assert_bool(claim.enabled)?;
        let active = ctx.mul(enabled, claim.enabled);
        check_placement(ctx, active, &claim.offset, &claim.point.dim, log_n)?;
        let weight = ctx.mul(active, power);
        target = ctx.add(target, ctx.mul(weight, claim.value));
        point_weights.push(weight);
        power = ctx.select(active, ctx.mul(power, lambda), power);
    }
    opening::verify_whir(
        transcript,
        enabled,
        log_n,
        log_inv_rate,
        n_lanes,
        target,
        root,
        |coordinates| {
            let mut query = Point::zero(ctx, log_n.clone());
            query.coords[..MAX_STACK_VARS].copy_from_slice(coordinates);
            let mut value = ctx.zero();
            for (claim, &weight) in points.iter().zip(&point_weights) {
                let equality = algebra::eq_prefix(ctx, &claim.point.coords, &query.coords, &claim.point.dim)?;
                let selected = selector(ctx, &claim.offset, &claim.point.dim, &query);
                value = ctx.add(value, ctx.mul(weight, ctx.mul(equality, selected)));
            }
            for ((ring, claim), &weight) in rings.iter().zip(&switched).zip(&ring_weights) {
                let selected = selector(ctx, &ring.offset, &ring.family.point.dim, &query);
                let equality = claim.evaluate(ctx, &query.coords[..MAX_STACK_VARS])?;
                value = ctx.add(value, ctx.mul(weight, ctx.mul(equality, selected)));
            }
            Ok(value)
        },
    )
}
