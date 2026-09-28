//! Witness-free verification of the native RV64IM table argument.
use alloc::{vec, vec::Vec};
use leanvm_guest::Field as F;

use crate::{
    Error, ProgramInfo, Proof, VerifySummary,
    layout::{Coordinate, Header, Layout, offsets},
    packed_reduction,
    portable::{
        algebra::{eq_eval, eq_kernel, log2_ceil, poly_eval},
        flock, gkr, pcs, ring,
        transcript::Transcript,
    },
};

const BUS_BITS: usize = 4;
const SLOT_BITS: usize = 8;

// Columns of a table share a point. Preserve their stream order without
// allocating a separate copy of that point for every circuit wire.
struct Claims {
    point: Vec<F>,
    columns: Vec<(usize, F)>,
}

#[derive(Default)]
struct Form<'a> {
    constant: F,
    terms: Vec<(F, &'a Coordinate)>,
}

struct Bus<'a> {
    claims: Vec<Claims>,
    point: Vec<F>,
    forms: Vec<[Form<'a>; 3]>,
    totals: [F; 3],
}

fn selector(offset: usize, low: usize, point: &[F]) -> F {
    point.iter().enumerate().skip(low).fold(F::ONE, |value, (bit, &r)| {
        value * (if offset >> bit & 1 == 0 { F::ONE + r } else { r })
    })
}

// Public ROM is the immutable statement, not an advised opening. Share one
// small equality/subset table across the recursion, never a field-valued ROM.
fn public_mle(values: &[u64], point: &[F]) -> F {
    if point.is_empty() {
        return F::from(values[0]);
    }
    let low = point.len().min(3);
    let mut weights = [F::ZERO; 8];
    weights[0] = F::ONE;
    for (bit, &r) in point[..low].iter().enumerate() {
        for lane in 0..1 << bit {
            let right = weights[lane] * r;
            weights[lane + (1 << bit)] = right;
            weights[lane] += right;
        }
    }
    let mut subsets = [F::ZERO; 256];
    for (lane, &weight) in weights[..1 << low].iter().enumerate() {
        for mask in 0..1 << lane {
            subsets[mask + (1 << lane)] = subsets[mask] + weight;
        }
    }
    public_mle_fold(values, &point[low..], &subsets)
}

fn public_mle_fold(values: &[u64], point: &[F], subsets: &[F; 256]) -> F {
    if let Some((&r, rest)) = point.split_last() {
        let (left, right) = values.split_at(values.len() / 2);
        let a = public_mle_fold(left, rest, subsets);
        return a + r * (a + public_mle_fold(right, rest, subsets));
    }

    // Equality weights sum to one, so a common word can be added back after
    // evaluating the XOR differences. Constant chunks need no bit-plane work.
    let anchor = values[0];
    let mut lanes = [0u64; 8];
    let mut varying = 0;
    for (lane, &word) in lanes.iter_mut().zip(values) {
        *lane = word ^ anchor;
        varying |= *lane;
    }
    if varying == 0 {
        return F::from(anchor);
    }
    let bits = (u64::BITS - varying.leading_zeros()) as usize;
    let mut value = F::ZERO;
    for byte in (0..bits.div_ceil(8)).rev() {
        let shift = byte * 8;
        let mut planes = 0;
        for (lane, &word) in lanes.iter().enumerate() {
            planes |= ((word >> shift) & 0xff) << (lane * 8);
        }
        // Same portable SWAR transpose as primitives::bits::transpose_8x8_bits;
        // primitives is host-only here. Output byte b selects bit b's lanes.
        let t = (planes ^ (planes >> 7)) & 0x00AA_00AA_00AA_00AA;
        planes ^= t ^ (t << 7);
        let t = (planes ^ (planes >> 14)) & 0x0000_CCCC_0000_CCCC;
        planes ^= t ^ (t << 14);
        let t = (planes ^ (planes >> 28)) & 0x0000_0000_F0F0_F0F0;
        planes ^= t ^ (t << 28);
        // Horner in the base-field generator reconstructs full u64 words,
        // without a general field multiplication for any bit plane.
        for bit in (0..8.min(bits - shift)).rev() {
            value = value.mul_base_generator() + subsets[((planes >> (bit * 8)) & 0xff) as usize];
        }
    }
    F::from(anchor) + value
}

fn framework_column(column: usize, point: &[F], claims: &mut Vec<Claims>, t: &mut Transcript<'_>) -> Result<F, Error> {
    for group in claims.iter() {
        if group.point == point
            && let Some((_, value)) = group.columns.iter().find(|(c, _)| *c == column)
        {
            return Ok(*value);
        }
    }
    let value = t.next_scalar()?;
    claims.push(Claims {
        point: point.to_vec(),
        columns: vec![(column, value)],
    });
    Ok(value)
}

fn framework_coordinate(
    coordinate: &Coordinate,
    point: &[F],
    layout: &Layout,
    claims: &mut Vec<Claims>,
    public: &mut Vec<(usize, usize, F)>,
    t: &mut Transcript<'_>,
) -> Result<F, Error> {
    match coordinate {
        Coordinate::Constant(value) => Ok(F::from(*value)),
        Coordinate::Column(column) => framework_column(*column, point, claims, t),
        Coordinate::Scaled(column, coefficient) => {
            Ok(framework_column(*column, point, claims, t)? * F::from(*coefficient))
        }
        Coordinate::Public(column) => {
            if let Some((_, _, value)) = public.iter().find(|(c, n, _)| c == column && *n == point.len()) {
                return Ok(*value);
            }
            let values = layout.public_columns.get(*column).ok_or(Error::InvalidShape)?;
            if values.len() != 1usize << point.len() {
                return Err(Error::InvalidShape);
            }
            let value = public_mle(values, point);
            public.push((*column, point.len(), value));
            Ok(value)
        }
        // A quadratic framework coordinate cannot be settled by individual
        // column MLEs: only table-owned forms may contain these expressions.
        Coordinate::Product(..) | Coordinate::Sum(..) => Err(Error::InvalidShape),
    }
}

fn table_coordinate(coordinate: &Coordinate, base: usize, columns: &[F]) -> Result<F, Error> {
    let column = |index: usize| -> Result<F, Error> {
        index
            .checked_sub(base)
            .and_then(|i| columns.get(i))
            .copied()
            .ok_or(Error::InvalidShape)
    };
    match coordinate {
        Coordinate::Constant(value) => Ok(F::from(*value)),
        Coordinate::Column(index) => column(*index),
        Coordinate::Scaled(index, coefficient) => Ok(column(*index)? * F::from(*coefficient)),
        Coordinate::Product(a, b, coefficient) => Ok(column(*a)? * column(*b)? * F::from(*coefficient)),
        Coordinate::Sum(terms) => terms
            .iter()
            .try_fold(F::ZERO, |sum, term| Ok(sum + table_coordinate(term, base, columns)?)),
        Coordinate::Public(_) => Err(Error::InvalidShape),
    }
}

fn verify_bus<'a>(layout: &'a Layout, t: &mut Transcript<'_>) -> Result<Bus<'a>, Error> {
    let mut placements = Vec::with_capacity(3);
    let mut depths = [0; 3];
    for (side, blocks) in layout.blocks.iter().enumerate() {
        if blocks.iter().any(|b| b.coordinates.len() > 1 << BUS_BITS) {
            return Err(Error::InvalidShape);
        }
        let logs: Vec<_> = blocks.iter().map(|b| b.log_rows).collect();
        let (positions, size) = offsets(&logs)?;
        depths[side] = log2_ceil(size);
        placements.push(positions);
    }
    if depths[0] != depths[1] || depths[2] > depths[0] || depths[0] >= usize::BITS as usize {
        return Err(Error::InvalidShape);
    }
    let weights = eq_kernel(&t.samples(BUS_BITS));
    let beta = t.sample();
    let product = gkr::verify(depths[0], t)?;
    let mut bus = Bus {
        claims: Vec::new(),
        point: product.point,
        forms: (0..layout.tables.len())
            .map(|_| core::array::from_fn(|_| Form::default()))
            .collect(),
        totals: product.values,
    };
    let mut public = Vec::new();
    for (side, blocks) in layout.blocks.iter().enumerate() {
        let side_beta = if side == 2 { F::ZERO } else { beta };
        let mut known = F::ZERO;
        let mut occupied = F::ZERO;
        for (block, &offset) in blocks.iter().zip(&placements[side]) {
            if block.log_rows > bus.point.len() {
                return Err(Error::InvalidShape);
            }
            let select = selector(offset, block.log_rows, &bus.point);
            occupied += select;
            if let Some(owner) = block.owner {
                let form = &mut bus.forms.get_mut(owner).ok_or(Error::InvalidShape)?[side];
                form.constant += select * side_beta;
                for (slot, coordinate) in block.coordinates.iter().enumerate() {
                    let weight = if side == 2 {
                        if slot == 0 { F::ONE } else { F::ZERO }
                    } else {
                        weights[slot]
                    };
                    form.terms.push((select * weight, coordinate));
                }
            } else {
                let mut value = side_beta;
                for (slot, coordinate) in block.coordinates.iter().enumerate() {
                    let weight = if side == 2 {
                        if slot == 0 { F::ONE } else { F::ZERO }
                    } else {
                        weights[slot]
                    };
                    value += weight
                        * framework_coordinate(
                            coordinate,
                            &bus.point[..block.log_rows],
                            layout,
                            &mut bus.claims,
                            &mut public,
                            t,
                        )?;
                }
                known += select * value;
            }
        }
        // Count uses the SAME padded cube as push/pull, even if it has no
        // occupied blocks. Its empty tree is the constant identity, not zero.
        bus.totals[side] += known + F::ONE + occupied;
    }
    Ok(bus)
}

fn verify_tables(layout: &Layout, bus: &mut Bus<'_>, t: &mut Transcript<'_>) -> Result<(), Error> {
    let eta = t.sample();
    let n_constraints: usize = layout.tables.iter().map(|table| table.relations.len()).sum();
    let mut bus_power = F::ONE;
    for _ in 0..n_constraints {
        bus_power *= eta;
    }
    let form_powers = [bus_power, bus_power * eta, bus_power * eta.square()];
    let mut claim = (0..3).fold(F::ZERO, |sum, side| sum + form_powers[side] * bus.totals[side]);
    let rounds = (0..layout.tables.len())
        .map(|index| layout.table_tau(index))
        .max()
        .unwrap_or(0);
    if rounds > bus.point.len() {
        return Err(Error::InvalidShape);
    }
    let mut point = vec![F::ZERO; rounds];
    let mut table_weights = vec![F::ONE; layout.tables.len()];
    // Back-loaded batching eliminates high variables first; smaller tables wait
    // on the high-one face, rather than being duplicated across that cube.
    for variable in (0..rounds).rev() {
        let coefficients = t.sumcheck_round_poly(4, claim, None)?;
        let r = t.sample();
        point[variable] = r;
        claim = poly_eval(&coefficients, r);
        for (index, weight) in table_weights.iter_mut().enumerate() {
            *weight *= if layout.table_tau(index) > variable {
                F::ONE + bus.point[variable] + r
            } else {
                r
            };
        }
    }
    let mut terminal = F::ZERO;
    let mut constraint_power = F::ONE;
    for (index, table) in layout.tables.iter().enumerate() {
        let evaluations = t.next_scalars(table.circuit.raw_columns.len())?;
        let mut value = F::ZERO;
        for relation in &table.relations {
            value += constraint_power * relation.eval(&evaluations, false);
            constraint_power *= eta;
        }
        for (form, power) in bus.forms[index].iter().zip(form_powers) {
            let mut evaluated = form.constant;
            for &(weight, coordinate) in &form.terms {
                evaluated += weight * table_coordinate(coordinate, layout.bases[index], &evaluations)?;
            }
            value += power * evaluated;
        }
        terminal += table_weights[index] * value;
        bus.claims.push(Claims {
            point: point[..layout.table_tau(index)].to_vec(),
            columns: evaluations
                .into_iter()
                .enumerate()
                .map(|(column, value)| (layout.bases[index] + column, value))
                .collect(),
        });
    }
    if terminal != claim {
        return Err(Error::InvalidProof);
    }
    Ok(())
}

fn verify_opening(
    layout: &Layout,
    claims: &mut Vec<Claims>,
    root: [u8; 32],
    t: &mut Transcript<'_>,
) -> Result<(), Error> {
    let table_start = claims
        .len()
        .checked_sub(layout.tables.len())
        .ok_or(Error::InvalidShape)?;
    let mut reductions = Vec::with_capacity(2 * layout.tables.len() + usize::from(layout.flock_column.is_some()));
    for (index, table) in layout.tables.iter().enumerate() {
        let group = &claims[table_start + index];
        let values: Vec<_> = group.columns.iter().map(|&(_, value)| value).collect();
        let bit_claims = packed_reduction::verify(table, layout.table_tau(index), &group.point, &values, t)?;
        if bit_claims.len() != 2 {
            return Err(Error::InvalidShape);
        }
        for claim in bit_claims {
            reductions.push((layout.packed_columns[index], claim));
        }
    }
    match (layout.flock_column, layout.flock_log) {
        (Some(column), Some(log)) => {
            let (point, slices) = flock::verify_flock(log + 6, t)?;
            if point.len() != log {
                return Err(Error::InvalidShape);
            }
            reductions.push((column, packed_reduction::BitClaim { point, slices }));
            let index = layout
                .table_ids
                .iter()
                .position(|&id| id == crate::cpu_tables::BLAKE_TABLE)
                .ok_or(Error::InvalidShape)?;
            let group = &claims[table_start + index];
            let mut slots = Vec::with_capacity(layout.tables[index].flock_slots.len());
            for &(local, slot) in &layout.tables[index].flock_slots {
                if slot >= 1 << SLOT_BITS || group.point.len() + SLOT_BITS != log {
                    return Err(Error::InvalidShape);
                }
                let &(physical, value) = group.columns.get(local).ok_or(Error::InvalidShape)?;
                if physical != layout.bases[index] + local {
                    return Err(Error::InvalidShape);
                }
                let mut point = Vec::with_capacity(log);
                point.extend((0..SLOT_BITS).map(|bit| F::from((slot >> bit & 1) as u64)));
                point.extend_from_slice(&group.point);
                slots.push(Claims {
                    point,
                    columns: vec![(column, value)],
                });
            }
            claims.extend(slots);
        }
        (None, None) => (),
        _ => return Err(Error::InvalidShape),
    }
    // All bit reductions precede the single shared map challenge.
    let map = ring::RingMap::sample(t);
    let mut rings = Vec::with_capacity(reductions.len());
    for (column, claim) in reductions {
        let placement = *layout.placements.get(column).ok_or(Error::InvalidShape)?;
        let height = placement.log_rows.ok_or(Error::InvalidShape)?;
        if height != claim.point.len() || height > layout.mu {
            return Err(Error::InvalidShape);
        }
        rings.push((placement, map.switch(&claim.point, &claim.slices)?));
    }
    // Every point claim now names a physical column, including BLAKE slots.
    // Establish dimensions before the infallible WHIR basis callback.
    for group in claims.iter() {
        for &(column, _) in &group.columns {
            let placement = layout.placements.get(column).ok_or(Error::InvalidShape)?;
            match placement.log_rows {
                Some(height) if height == group.point.len() && height <= layout.mu => (),
                _ => return Err(Error::InvalidShape),
            }
        }
    }
    // Rings take consecutive powers first, followed by framework, AIR and
    // BLAKE slot point claims in exactly their transmitted order.
    let lambda = t.sample();
    let mut power = F::ONE;
    let mut target = F::ZERO;
    for (_, ring) in &rings {
        target += power * ring.target;
        power *= lambda;
    }
    for group in claims.iter() {
        for &(_, value) in &group.columns {
            target += power * value;
            power *= lambda;
        }
    }
    pcs::verify_whir(t, layout.mu, layout.header.log_inv_rate, target, root, |query| {
        let mut weight = F::ZERO;
        let mut power = F::ONE;
        for (placement, ring) in &rings {
            let height = placement.log_rows.unwrap();
            weight += power * selector(placement.offset, height, query) * ring.evaluate(&query[..height]);
            power *= lambda;
        }
        for group in claims.iter() {
            let height = group.point.len();
            let row_weight = eq_eval(&group.point, &query[..height]);
            for &(column, _) in &group.columns {
                weight += power * row_weight * selector(layout.placements[column].offset, height, query);
                power *= lambda;
            }
        }
        weight
    })?;
    Ok(())
}

/// Verify the native RV64IM SNARK against the exact ELF and public digest.
/// No execution trace or host verifier is needed; all pending column claims
/// are discharged by the one authenticated WHIR opening before returning.
pub fn verify(program: &ProgramInfo, public: [u8; 32], proof: &Proof) -> Result<VerifySummary, Error> {
    let mut transcript = Transcript::new(proof, program.iv(), public);
    let header = Header::read(&mut transcript)?;
    let layout = Layout::new(program, public, header)?;
    let root = transcript.next_root()?;
    let mut bus = verify_bus(&layout, &mut transcript)?;
    verify_tables(&layout, &mut bus, &mut transcript)?;
    verify_opening(&layout, &mut bus.claims, root, &mut transcript)?;
    transcript.finish()?;
    Ok(VerifySummary {
        cycles: layout.header.cycles,
        memory_events: layout.header.ram.count + layout.header.registers.count,
        committed_words: layout.committed_len() as u64,
        log_inv_rate: layout.header.log_inv_rate as u8,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scalar_public_mle(values: &[u64], point: &[F]) -> F {
        let mut values: Vec<_> = values.iter().copied().map(F::from).collect();
        let mut len = values.len();
        for &r in point {
            for i in 0..len / 2 {
                values[i] = values[2 * i] + r * (values[2 * i] + values[2 * i + 1]);
            }
            len /= 2;
        }
        values[0]
    }

    fn word(index: usize) -> u64 {
        (index as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15).rotate_left(23) ^ 0xa5c3_69f0_1287_be4d
    }

    #[test]
    fn public_rom_mle_matches_scalar_at_coefficient_and_chunk_boundaries() {
        for log in 0..=7 {
            let point: Vec<_> = (0..log).map(|i| F::new(word(i), word(i + 11), word(i + 23))).collect();
            for bits in [0, 1, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64] {
                let mask = if bits == 64 { u64::MAX } else { (1u64 << bits) - 1 };
                for anchor in [0, u64::MAX, 0x8000_0001_ffff_ff00] {
                    let values: Vec<_> = (0..1 << log).map(|i| anchor ^ (word(i) & mask)).collect();
                    assert_eq!(
                        public_mle(&values, &point),
                        scalar_public_mle(&values, &point),
                        "log={log}, bits={bits}, anchor={anchor:#x}"
                    );
                }
            }
            // Padding may start inside a chunk, at a chunk boundary, or inside
            // either side of the higher-variable recursion.
            let len = 1 << log;
            for live in [0, 1, 3, 7, 8, 9, len / 2, len - 1, len] {
                if live > len {
                    continue;
                }
                let mut values = vec![u64::MAX; len];
                for (i, value) in values[..live].iter_mut().enumerate() {
                    *value = word(i);
                }
                assert_eq!(
                    public_mle(&values, &point),
                    scalar_public_mle(&values, &point),
                    "log={log}, live={live}"
                );
            }
        }
    }

    #[test]
    fn public_rom_mle_selects_boolean_rows() {
        for log in 0..=7 {
            let len = 1 << log;
            let values: Vec<_> = (0..len)
                .map(|i| if i >= len / 2 { u64::MAX } else { word(i) })
                .collect();
            for (row, &expected) in values.iter().enumerate() {
                let point: Vec<_> = (0..log).map(|bit| F::from((row >> bit & 1) as u64)).collect();
                assert_eq!(public_mle(&values, &point), F::from(expected), "log={log}, row={row}");
            }
        }
    }
}
