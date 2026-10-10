use std::mem::MaybeUninit;

use primitives::field::F192;
use primitives::multilinear::{eq_table_seeded, fill_eq_table_uninit};

use super::StackClaim;
use crate::ring_switch::RingSwitch;
use crate::ring_switch::{DeferredWeight, combine_deferred_chunk};
use crate::whir::{INITIAL_BASIS_CHUNK, anchor::eq_prefix};

struct PointWeight<'a> {
    offset: usize,
    end: usize,
    slot: usize,
    stride: usize,
    low: &'a [F192],
    high: Vec<F192>,
}

impl<'a> PointWeight<'a> {
    fn new(claim: &'a StackClaim, lambda: F192, chunk_log: usize) -> Self {
        let (offset, slot, stride_log, point) = match claim {
            StackClaim::Point { offset, low_point, .. } => (*offset, 0, 0, low_point.as_slice()),
            StackClaim::Strided {
                offset,
                slot,
                stride_log,
                point,
                ..
            } => (*offset, *slot, *stride_log, point.as_slice()),
        };
        let len = 1usize << (stride_log + point.len());
        let stride = 1usize << stride_log;
        assert!(offset.is_multiple_of(len), "claim must be aligned to its support");
        assert!(slot < stride, "claim slot must fit the stride");
        let low_vars = point.len().min(chunk_log.saturating_sub(stride_log));
        let (low, high_point) = point.split_at(low_vars);
        let high = eq_table_seeded(high_point, lambda);
        Self {
            offset,
            end: offset + len,
            slot,
            stride,
            low,
            high,
        }
    }

    fn anchor(point: &'a [F192], lambda: F192, stack_len: usize, chunk_log: usize) -> Self {
        let low_vars = point.len().min(chunk_log);
        let (low, high_point) = point.split_at(low_vars);
        let low_len = 1usize << low_vars;
        assert!(stack_len.is_multiple_of(low_len), "anchor support is whole low chunks");
        Self {
            offset: 0,
            end: stack_len,
            slot: 0,
            stride: 1,
            low,
            high: eq_prefix(high_point, stack_len / low_len, lambda),
        }
    }

    fn add(&self, start: usize, dst: &mut [F192], scratch: &mut [MaybeUninit<F192>]) {
        let base = self.offset + self.slot;
        let lo = start.max(base);
        let hi = (start + dst.len()).min(self.end);
        if lo >= hi {
            return;
        }
        let first = (lo - base).div_ceil(self.stride);
        let end = (hi - base).div_ceil(self.stride);
        if first == end {
            return;
        }
        let len = 1usize << self.low.len();
        assert!(first.is_multiple_of(len) && (end - first).is_multiple_of(len));
        for chunk_first in (first..end).step_by(len) {
            fill_eq_table_uninit(self.low, self.high[chunk_first / len], &mut scratch[..len]);
            // SAFETY: the build above initializes this prefix before the scatter reads it.
            let eq = unsafe { std::slice::from_raw_parts(scratch.as_ptr().cast::<F192>(), len) };
            let dst_offset = base + chunk_first * self.stride - start;
            for (i, &value) in eq.iter().enumerate() {
                dst[dst_offset + i * self.stride] += value;
            }
        }
    }
}

/// The stacked opening's lifted weight, one aligned chunk at a time.
///
/// It is the lambda-weighted sum of every claim's weight over the stack:
///
/// - each ring-switched region's combined weight, over that region;
/// - each point claim's equality weight, over its own support.
/// - the immutable anchor's equality weight, clipped to the occupied lanes.
///
/// It is filled one chunk at a time, as the opening reads it.
pub(super) struct StackWeight<'a> {
    /// Each point claim's weight, its high equality table built once.
    weights: Vec<PointWeight<'a>>,
    /// For each lane block, the point claims whose support meets it.
    by_lane: Vec<Vec<usize>>,
    /// Each ring-switched region: its first word, its end, and its claims' weights.
    regions: Vec<(usize, usize, &'a [DeferredWeight])>,
    /// Words per lane block.
    lane_block: usize,
}

impl<'a> StackWeight<'a> {
    /// The point claims and immutable anchor batched by `lambdas`, with the anchor's coefficient last, plus the ring-switched regions.
    pub(super) fn new(
        stack_len: usize,
        lane_block: usize,
        claims: &'a [StackClaim],
        lambdas: &[F192],
        anchor_point: &'a [F192],
        rings: &[RingSwitch],
        rs_outputs: &'a [DeferredWeight],
    ) -> Self {
        assert_eq!(claims.len() + 1, lambdas.len());
        // A fill writes one chunk, or one whole lane block when blocks are smaller.
        let chunk_log = lane_block.min(INITIAL_BASIS_CHUNK).ilog2() as usize;
        let mut weights = Vec::with_capacity(claims.len() + 1);
        weights.extend(
            claims
                .iter()
                .zip(lambdas)
                .map(|(claim, &lambda)| PointWeight::new(claim, lambda, chunk_log)),
        );
        weights.push(PointWeight::anchor(
            anchor_point,
            lambdas[claims.len()],
            stack_len,
            chunk_log,
        ));

        // Index the claims by the lane blocks they touch, so a fill visits only those.
        let mut by_lane = vec![Vec::new(); stack_len / lane_block];
        for (index, weight) in weights.iter().enumerate() {
            for lane in &mut by_lane[weight.offset / lane_block..weight.end.div_ceil(lane_block)] {
                lane.push(index);
            }
        }

        // Each ring's outputs are its own run of the outputs, in ring order.
        let mut first = 0;
        let regions = rings
            .iter()
            .map(|ring| {
                let outputs = &rs_outputs[first..first + ring.claims.len()];
                first += ring.claims.len();
                (ring.offset, ring.offset + (1usize << ring.qflock_vars), outputs)
            })
            .collect();
        assert_eq!(first, rs_outputs.len());

        Self {
            weights,
            by_lane,
            regions,
            lane_block,
        }
    }

    /// Writes the weight of words `start..start + dst.len()`, one aligned fill chunk.
    pub(super) fn fill(&self, start: usize, dst: &mut [F192]) {
        dst.fill(F192::ZERO);

        // The ring-switched regions this chunk meets.
        for &(offset, end, outputs) in &self.regions {
            let lo = start.max(offset);
            let hi = (start + dst.len()).min(end);
            if lo < hi {
                combine_deferred_chunk(outputs, lo - offset, &mut dst[lo - start..hi - start]);
            }
        }

        // The point claims of this chunk's lane block.
        let mut scratch = [MaybeUninit::uninit(); INITIAL_BASIS_CHUNK];
        for &index in &self.by_lane[start / self.lane_block] {
            self.weights[index].add(start, dst, &mut scratch);
        }
    }
}
