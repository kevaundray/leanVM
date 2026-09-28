use crate::{
    Error, algebra,
    context::Context,
    protocol::{Dimension, MAX_STACK_VARS, Point},
    transcript::Transcript,
};
use riscv_proof::schema::{Coord, PublicSource};

pub(crate) struct Form<'a, F: Copy> {
    pub constant: F,
    pub terms: Vec<(F, &'a Coord)>,
}

impl<F: Copy> Form<'_, F> {
    pub(crate) fn zero<C: Context<F = F>>(ctx: &C) -> Self {
        Self {
            constant: ctx.zero(),
            terms: Vec::new(),
        }
    }
}

pub(crate) struct Table<'a, F: Copy> {
    pub enabled: F,
    pub dim: Dimension<F>,
    pub width: usize,
    pub relations: &'a [Coord],
    pub forms: [Form<'a, F>; 3],
}

pub(crate) struct Claims<F: Copy> {
    pub point: Point<F>,
    pub evaluations: Vec<F>,
}

pub(crate) fn coordinate<C: Context>(
    ctx: &C,
    expression: &Coord,
    values: &[C::F],
    parameter: &impl Fn(PublicSource) -> Result<C::F, Error>,
) -> Result<C::F, Error> {
    let column = |index| values.get(index).copied().ok_or(Error::InvalidCircuit);
    Ok(match expression {
        Coord::Constant(value) => ctx.base(*value),
        Coord::Column(index) => column(*index)?,
        Coord::Scaled(index, coefficient) => ctx.mul(column(*index)?, ctx.base(*coefficient)),
        Coord::PublicScaled(index, source, _) => ctx.mul(column(*index)?, parameter(*source)?),
        Coord::Product(a, b, coefficient) => ctx.mul(ctx.mul(column(*a)?, column(*b)?), ctx.base(*coefficient)),
        Coord::Sum(terms) => {
            let mut sum = ctx.zero();
            for term in terms {
                sum = ctx.add(sum, coordinate(ctx, term, values, parameter)?);
            }
            sum
        }
    })
}

pub(crate) fn verify<C: Context>(
    transcript: &mut Transcript<'_, C>,
    enabled: C::F,
    tables: &[Table<'_, C::F>],
    bus_point: &Point<C::F>,
    totals: [C::F; 3],
    parameter: &impl Fn(PublicSource) -> Result<C::F, Error>,
) -> Result<Vec<Claims<C::F>>, Error> {
    let ctx = transcript.context();
    let eta = transcript.sample(enabled)?;
    let mut starts = Vec::with_capacity(tables.len());
    let mut active = Vec::with_capacity(tables.len());
    let mut power = ctx.one();
    for table in tables {
        ctx.assert_bool(table.enabled)?;
        let present = ctx.mul(enabled, table.enabled);
        ctx.assert_equal_if(present, bus_point.dim.bits().lt(ctx, table.dim.bits()), ctx.zero())?;
        active.push(present);
        starts.push(power);
        let mut next = power;
        for _ in table.relations {
            next = ctx.mul(next, eta);
        }
        power = ctx.select(present, next, power);
    }
    let shared = [power, ctx.mul(power, eta), ctx.mul(ctx.mul(power, eta), eta)];
    let mut running = algebra::dot(ctx, &shared, &totals);
    let mut point = Point::zero(ctx, bus_point.dim.clone());
    let mut weights = vec![ctx.one(); tables.len()];
    for variable in (0..MAX_STACK_VARS).rev() {
        let mut round = ctx.zero();
        for (table, &present) in tables.iter().zip(&active) {
            round = ctx.or(round, ctx.mul(present, table.dim.contains(variable)));
        }
        let message = transcript.round_poly(round, 4, running, None)?;
        let challenge = transcript.sample(round)?;
        point.coords[variable] = challenge;
        running = ctx.select(round, algebra::poly_eval(ctx, &message, challenge), running);
        for (table, weight) in tables.iter().zip(&mut weights) {
            let factor = ctx.add(
                challenge,
                ctx.mul(table.dim.contains(variable), ctx.not(bus_point.coords[variable])),
            );
            *weight = ctx.mul(*weight, ctx.select(round, factor, ctx.one()));
        }
    }
    let mut claims = Vec::with_capacity(tables.len());
    let mut terminal = ctx.zero();
    for (index, table) in tables.iter().enumerate() {
        let mut evaluations = Vec::with_capacity(table.width);
        for _ in 0..table.width {
            evaluations.push(transcript.scalar(active[index])?);
        }
        let mut value = ctx.zero();
        let mut power = starts[index];
        for relation in table.relations {
            value = ctx.add(
                value,
                ctx.mul(power, coordinate(ctx, relation, &evaluations, parameter)?),
            );
            power = ctx.mul(power, eta);
        }
        for (side, form) in table.forms.iter().enumerate() {
            let mut evaluated = form.constant;
            for &(weight, expression) in &form.terms {
                evaluated = ctx.add(
                    evaluated,
                    ctx.mul(weight, coordinate(ctx, expression, &evaluations, parameter)?),
                );
            }
            value = ctx.add(value, ctx.mul(shared[side], evaluated));
        }
        terminal = ctx.add(terminal, ctx.mul(ctx.mul(active[index], weights[index]), value));
        let coords = std::array::from_fn(|variable| ctx.mul(table.dim.contains(variable), point.coords[variable]));
        claims.push(Claims {
            point: Point {
                dim: table.dim.clone(),
                coords,
            },
            evaluations,
        });
    }
    ctx.assert_equal_if(enabled, terminal, running)?;
    Ok(claims)
}
