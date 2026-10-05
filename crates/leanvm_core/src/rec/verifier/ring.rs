//! The ring-switched family's share of an opening, in rows: its target, and its weight at the terminal point.
//!
//! The native verifier computes the same two values with the stacked opening's family helpers; tests hold them equal.

use super::Rows;
use crate::arith::Arith;
use crate::rec::circuit::{Builder, Ew};
use ::pcs::pack::PACKING_WIDTH;
use ::pcs::ring_switch::COMPOSITION_SHIFTS;
use ::pcs::stack_open::{PrefixGroup, RingSwitch};
use primitives::field::{F64, F192};
use std::collections::BTreeMap;

/// The ring-switching map `Phi`, as the coefficients `C_k^(2^-k)` of its Frobenius form, `k < 64`.
pub(crate) struct RingMap {
    coefficients: Vec<Ew>,
}

/// Every ring-switched claim of an opening as one family, claim `j` scaled by `gamma_rs^j`, under one map.
pub(super) struct RingShare<'a> {
    rings: &'a [RingSwitch<Ew>],
    scales: Vec<Ew>,
    map: RingMap,
}

impl RingMap {
    /// The map drawn from its six challenges.
    ///
    /// `C_k^(2^-k) = prod_{p : k & d_p} f_p^(2^-(k - k mod d_p))`, and `k - k mod d_p` is the part of `k` at the shifts down to `d_p`.
    /// So the products grow one shift at a time, each prefix `k` extended by `d_p` or not.
    fn new(b: &mut Builder, challenges: &[Ew]) -> Self {
        let mut prefixes = vec![(0usize, b.one())];
        for (&f, &shift) in challenges.iter().zip(&COMPOSITION_SHIFTS) {
            let ladder = Self::ladder(b, f, shift);
            let extended: Vec<(usize, Ew)> = prefixes
                .iter()
                .map(|&(k, c)| (k + shift, b.mul(c, ladder[k + shift])))
                .collect();
            prefixes.extend(extended);
        }
        let mut coefficients = vec![b.one(); PACKING_WIDTH];
        for (k, c) in prefixes {
            coefficients[k] = c;
        }
        Self { coefficients }
    }

    /// `sum_i x^i Phi(s_i)` for the family's slices `s`: `sum_k (C_k^(2^-k) S(x^(2^-k)))^(2^k)` with `S(u) = sum_i s_i u^i`.
    fn target(&self, b: &mut Builder, slices: &[Ew]) -> Ew {
        assert_eq!(slices.len(), PACKING_WIDTH, "a family has 64 slices");
        let terms: Vec<Ew> = (0..PACKING_WIDTH)
            .map(|k| {
                // `x^(2^-k) = x^(2^(64 - k))` in `K`.
                let xk = (0..(PACKING_WIDTH - k) % PACKING_WIDTH).fold(F64(2), |x, _| x.square());
                let (&last, rest) = slices.split_last().expect("64 slices");
                let s = rest
                    .iter()
                    .rev()
                    .fold(last, |acc, &sj| b.mul_const_add(acc, F192::from(xk), sj));
                b.mul(self.coefficients[k], s)
            })
            .collect();
        Self::close(b, &terms)
    }

    /// The terms `C_k^(2^-k) P_k` of a claim's weight at several prefixes of one suffix point `z`, `P_k = prod_n (1 + z_n + q_n^(2^-k))`: entry `i` is at `z[..lengths[i]]`.
    ///
    /// `ladders[n]` holds the query's `q_n^(2^-k)`. The products of a prefix extend to the next coordinate by one product each, so one pass over the longest serves every length.
    fn prefix_terms(&self, b: &mut Builder, z: &[Ew], ladders: &[Vec<Ew>], lengths: &[usize]) -> Vec<Vec<Ew>> {
        let longest = lengths.iter().copied().max().unwrap_or(0);
        assert!(
            longest <= z.len() && longest <= ladders.len(),
            "a claim's point is a prefix of the query"
        );
        let mut out = vec![Vec::new(); lengths.len()];
        let take = |n: usize, terms: &[Ew], out: &mut [Vec<Ew>]| {
            for (slot, _) in out.iter_mut().zip(lengths).filter(|&(_, &len)| len == n) {
                *slot = terms.to_vec();
            }
        };
        let mut terms = self.coefficients.clone();
        take(0, &terms, &mut out);
        for (n, (&zn, ladder)) in z.iter().zip(ladders).take(longest).enumerate() {
            for (term, &power) in terms.iter_mut().zip(ladder) {
                let s = b.add(power, zn);
                *term = b.times_one_plus(*term, s);
            }
            take(n + 1, &terms, &mut out);
        }
        out
    }
}

impl RingMap {
    /// `sum_k term_k^(2^k)`, by the linearized Horner rule `acc <- acc^2 + term` from the last term down.
    fn close(b: &mut Builder, terms: &[Ew]) -> Ew {
        let (&last, rest) = terms.split_last().expect("the map has 64 terms");
        rest.iter().rev().fold(last, |acc, &term| b.mul_add(acc, acc, term))
    }

    /// `v^(2^128)`: two Frobenius maps, `v + c2 (Y + Y^2) + c1 Y^2` for `v = c0 + c1 Y + c2 Y^2`.
    fn frobenius2(b: &mut Builder, v: Ew) -> Ew {
        let [_, c1, c2] = b.e_to_k(v);
        let y_y2 = b.e_const(F192::new(0, 1, 1));
        let y2 = b.e_const(F192::new(0, 0, 1));
        let u = b.mul_k_add(y_y2, c2, v);
        b.mul_k_add(y2, c1, u)
    }

    /// `v^(2^-j)` at each index `j >= lowest` of 64, and `v` below.
    ///
    /// Squaring from `v^(2^128) = v^(2^-64)` climbs to `v^(2^-lowest)`.
    pub(crate) fn ladder(b: &mut Builder, v: Ew, lowest: usize) -> Vec<Ew> {
        let mut ladder = vec![v; PACKING_WIDTH];
        let lowest = lowest.max(1);
        let mut power = Self::frobenius2(b, v);
        for slot in ladder[lowest..].iter_mut().rev() {
            power = b.square(power);
            *slot = power;
        }
        ladder
    }
}

impl<'a> RingShare<'a> {
    /// The family of the regions' claims in order, under the challenge `gamma_rs` and the map's challenges.
    pub(super) fn new(r: &mut Rows<'_, '_>, rings: &'a [RingSwitch<Ew>], gamma_rs: Ew, map: &[Ew]) -> Self {
        let n_claims = rings.iter().map(|ring| ring.claims.len()).sum();
        let scales = r.powers(gamma_rs, n_claims);
        let map = r.scope("ring switch map", |r| RingMap::new(r.b, map));
        Self { rings, scales, map }
    }

    /// The family's target: the map applied once to the slices `sum_j gamma_rs^j s_{j,i}`.
    pub(super) fn target(&self, r: &mut Rows<'_, '_>) -> Ew {
        let claims = self.rings.iter().flat_map(|ring| &ring.claims);
        let zero = r.zero();
        let mut family = vec![zero; PACKING_WIDTH];
        for (claim, &scale) in claims.zip(&self.scales) {
            let slices = &claim.slices.s_hat_v;
            assert_eq!(slices.len(), PACKING_WIDTH, "a ring-switched claim has 64 slices");
            for (f, &s) in family.iter_mut().zip(slices) {
                *f = r.mul_add(scale, s, *f);
            }
        }
        self.map.target(r.b, &family)
    }

    /// The family's weight at the stack point `x`: `sum_j sum_t eq(sel_t, x_hi) MLE(Phi(gamma_rs^j s_{j,t} eq(r_j[..n_t], .)))(x_lo)` over each claim `j` and each piece `t` of its region.
    ///
    /// - Claims whose points are prefixes of one another, the same wires, share one pass over the longest, which serves each piece's prefix too.
    /// - On a piece, the claims of one group read one prefix's terms, so their scales add before the terms are scaled, and the piece closes once, the Frobenius being additive.
    /// - Two sibling pieces of one length and one group close once together (see [`Self::sibling_terms`]).
    pub(super) fn weight_at(&self, r: &mut Rows<'_, '_>, x: &[Ew]) -> Ew {
        let max_vars = (self.rings.iter().flat_map(|ring| &ring.pieces))
            .map(|piece| piece.n_vars)
            .max()
            .unwrap_or(0);
        let ladders: Vec<Vec<Ew>> = x[..max_vars].iter().map(|&q| RingMap::ladder(r.b, q, 1)).collect();
        let groups = PrefixGroup::of(self.rings);

        // Each piece's scale on each group it reads, the claims of a group on it summed.
        let mut scales: Vec<Vec<Vec<(usize, Ew)>>> = (self.rings.iter())
            .map(|ring| vec![Vec::new(); ring.pieces.len()])
            .collect();
        for (g, group) in groups.iter().enumerate() {
            for member in &group.members {
                let piece_scale = self.rings[member.ring].claims[member.ring_claim].scales[member.piece];
                let scale = r.mul(self.scales[member.claim], piece_scale);
                let parts = &mut scales[member.ring][member.piece];
                match parts.iter_mut().find(|(h, _)| *h == g) {
                    Some((_, sum)) => *sum = r.add(*sum, scale),
                    None => parts.push((g, scale)),
                }
            }
        }

        // The sibling pairs: a piece at an even block of its length and the piece at the next block, both of one group alone, the group's terms reaching one coordinate further.
        let mut pair_of: Vec<Vec<Option<(usize, usize)>>> =
            (self.rings.iter()).map(|ring| vec![None; ring.pieces.len()]).collect();
        let mut lengths: Vec<Vec<usize>> = groups.iter().map(|group| group.lengths.clone()).collect();
        let mut alone: BTreeMap<(usize, usize), (usize, usize, usize)> = BTreeMap::new();
        for (ring_index, ring) in self.rings.iter().enumerate() {
            for (piece_index, piece) in ring.pieces.iter().enumerate() {
                if let [(g, _)] = scales[ring_index][piece_index][..] {
                    alone.insert((piece.offset, piece.n_vars), (g, ring_index, piece_index));
                }
            }
        }
        for (&(offset, n), &(g, ring, piece)) in &alone {
            let longest = groups[g].lengths.iter().copied().max().unwrap_or(0);
            let sibling = alone.get(&(offset + (1 << n), n));
            if offset.is_multiple_of(2 << n)
                && n < longest
                && let Some(&(h, sibling_ring, sibling_piece)) = sibling
                && h == g
            {
                pair_of[ring][piece] = Some((sibling_ring, sibling_piece));
                pair_of[sibling_ring][sibling_piece] = Some((ring, piece));
                if !lengths[g].contains(&(n + 1)) {
                    lengths[g].push(n + 1);
                }
            }
        }

        let at: Vec<Vec<Vec<Ew>>> = (groups.iter().zip(&lengths))
            .map(|(group, lengths)| self.map.prefix_terms(r.b, group.lead, &ladders, lengths))
            .collect();
        let terms_at = |g: usize, n: usize| -> &[Ew] {
            let i = lengths[g].iter().position(|&m| m == n).expect("a length of the group");
            &at[g][i]
        };

        let zero = r.zero();
        let mut weight = zero;
        for (ring_index, ring) in self.rings.iter().enumerate() {
            for (piece_index, piece) in ring.pieces.iter().enumerate() {
                let n = piece.n_vars;
                let (terms, block) = match pair_of[ring_index][piece_index] {
                    // The odd sibling closes with the even one.
                    Some(_) if (piece.offset >> n) & 1 == 1 => continue,
                    Some((sibling_ring, sibling_piece)) => {
                        let [(g, even)] = scales[ring_index][piece_index][..] else {
                            unreachable!("a paired piece reads one group")
                        };
                        let [(_, odd)] = scales[sibling_ring][sibling_piece][..] else {
                            unreachable!("a paired piece reads one group")
                        };
                        let terms =
                            Self::sibling_terms(r, even, odd, groups[g].lead[n], terms_at(g, n), terms_at(g, n + 1));
                        (terms, n + 1)
                    }
                    None => {
                        let mut terms = vec![zero; PACKING_WIDTH];
                        for &(g, scale) in &scales[ring_index][piece_index] {
                            for (t, &term) in terms.iter_mut().zip(terms_at(g, n)) {
                                *t = r.mul_add(scale, term, *t);
                            }
                        }
                        (terms, n)
                    }
                };
                let part = RingMap::close(r.b, &terms);
                let sel_eq = r.eq_bits(piece.offset >> block, &x[block..]);
                weight = r.mul_add(sel_eq, part, weight);
            }
        }
        weight
    }

    /// The terms whose close is two sibling pieces' weight, both at the prefix of length `n` of one group's point `z` and scaled by `even` and `odd`, without their selectors' bit `n`.
    ///
    /// That bit puts `1 + x_n` on the even piece and `x_n` on the odd one, and `c close(t) = close(c^(2^-k) t_k)`, so the pair's terms are `(even + d x_n^(2^-k)) a_k` with `d = even + odd`, `a_k` the terms at length `n`.
    /// The terms one coordinate further are `a_k (1 + z_n + x_n^(2^-k))`, so `x_n^(2^-k) a_k` is a sum of the two lengths' terms, and the pair's terms are `(odd + d z_n) a_k + d b_k` with `b_k` the terms at length `n + 1`.
    fn sibling_terms(r: &mut Rows<'_, '_>, even: Ew, odd: Ew, z_n: Ew, at_n: &[Ew], at_next: &[Ew]) -> Vec<Ew> {
        let d = r.add(even, odd);
        let c = r.mul_add(d, z_n, odd);
        (at_n.iter().zip(at_next))
            .map(|(&a, &b)| {
                let ca = r.mul(c, a);
                r.mul_add(d, b, ca)
            })
            .collect()
    }
}
