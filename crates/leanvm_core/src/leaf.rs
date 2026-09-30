//! The bus: a single shared channel balanced by a grand product (§sec:gp through §sec:leafstack). Each
//! interaction wires a table's columns into width-`m` tuples and flushes them in a
//! direction; the bus balances when pushed and pulled tuples form the same
//! multiset, proven by two GKR passes over the leaf vectors `β − π_α(σ)`. Each pass
//! reduces to a leaf claim `Ṽ₀(ζ)`, decomposed into evaluation claims on the
//! committed columns. Tuple coordinates `σ_i` are `K`-valued (column entries,
//! g-powers, separators); the fingerprint challenges `α, β` are `E`-valued, so a
//! leaf accumulates via the mixed `mul_base` product (2 PMULL per coordinate).

use crate::PAR_THRESHOLD;
use crate::colval::ColVal;
use crate::gkr;
use crate::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192, F192Unreduced, g_pow, index_mle, int_index_mle, powers_mle};
use primitives::multilinear::{eq_eval, eq_table_arena, mle_eval};
use std::collections::HashMap;
use std::sync::Arc;
use zk_alloc::ArenaVec;

/// One tuple coordinate as a function of the block's row `z`.
#[derive(Clone, Debug)]
pub enum Coord {
    /// A public constant (domain separator, opcode, the seed count `1`).
    Const(F64),
    /// A committed column, value `col[z]`.
    Col(usize),
    /// The free increment `g^k · col[z]` (a virtual column, §sec:vm): `k = 1` for the
    /// count/state steps, `k ∈ {1,2,3}` for BLAKE2s's consecutive-word successors.
    GCol(usize, u32),
    /// The product `g^k · col_a[z] · col_b[z]` of two committed columns. The g-power
    /// of an address `fp + o + k` is `g^fp·g^o·g^k`, so this carries one on the bus
    /// without committing it: the coordinate IS the product, so no column can
    /// disagree with it and the binding constraint that used to say so is unnecessary
    /// (§sec:m3).
    Prod(usize, usize, u32),
    /// The integer index column `base ^ (z << shift)` (§sec:idxcol), the element
    /// whose bits are that integer's: what addresses a region whose cell `z` sits at
    /// `base + (z << shift)`. Free, its MLE being linear.
    IntIndex { base: F64, shift: u32 },
    /// The exponent column `g^z` (§sec:idxcol), free via the factored MLE: the
    /// values of the `EXP` array.
    Index,
    /// The geometric column `first·ratio^z`, free the same way: the addresses of a
    /// range-check array (§sec:rangecheck).
    Powers { first: F64, ratio: F64 },
    /// A public column (the bytecode program, §sec:e2e-bc): not committed; both parties form
    /// its MLE directly, so it raises no claim. Shared rather than owned: push and
    /// pull carry the same ten columns, tens of megabytes at production sizes.
    Public(Arc<Vec<F64>>),
    /// A public column that is zero outside a few blocks (RAM as the run finds it,
    /// §sec:memchan): the verifier evaluates it in time proportional to the blocks,
    /// not to the column.
    Sparse(Arc<SparseColumn>),
    /// A sum of [`SumTerm`]s: any degree-2 form over the table's columns, which is
    /// all §sec:m3 asks of a coordinate. This is what
    /// carries a value a row DERIVES from its columns (a branch's successor, what a
    /// jump writes to `rd`, a hash row's block addresses) without committing a column for it, and
    /// with it the identity that would have tied the two. Like [`Coord::Prod`],
    /// only a table's blocks may carry one: the table sumcheck settles them,
    /// while a framework block has to split into per-column openings.
    Sum(Vec<SumTerm>),
}

/// A term of a [`Coord::Sum`], valued as the [`Coord`] of the same name.
#[derive(Clone, Copy, Debug)]
pub enum SumTerm {
    Const(F64),
    Col(usize),
    GCol(usize, u32),
    Prod(usize, usize, u32),
}

impl SumTerm {
    /// The term with its columns moved up by `base`.
    pub fn offset(self, base: usize) -> SumTerm {
        match self {
            SumTerm::Const(v) => SumTerm::Const(v),
            SumTerm::Col(i) => SumTerm::Col(base + i),
            SumTerm::GCol(i, k) => SumTerm::GCol(base + i, k),
            SumTerm::Prod(i, j, k) => SumTerm::Prod(base + i, base + j, k),
        }
    }
}

/// A public column of `2^log_len` words given by its nonzero stretches, each cut into
/// ALIGNED blocks: a power of two of words, at an offset that is a multiple of it. Such
/// a block's share of the column's multilinear extension is its own extension in the
/// low variables times the indicator of its offset's bits in the high ones.
#[derive(Debug)]
pub struct SparseColumn {
    log_len: usize,
    blocks: Vec<(usize, Vec<F64>)>,
}

impl SparseColumn {
    /// A column of zeros.
    pub fn new(log_len: usize) -> Self {
        Self {
            log_len,
            blocks: Vec::new(),
        }
    }

    /// Add the stretch `words` at offset `at`, which must not overlap another.
    pub fn with_stretch(mut self, mut at: usize, words: &[u64]) -> Self {
        assert!(at + words.len() <= 1 << self.log_len, "a stretch runs past the column");
        let mut next = 0;
        while next < words.len() {
            // The largest aligned block starting here that the stretch still fills.
            let mut size = 1;
            while 2 * size <= words.len() - next && at & (2 * size - 1) == 0 {
                size *= 2;
            }
            let mut block = Vec::with_capacity(size);
            for i in 0..size {
                block.push(F64(words[next + i]));
            }
            self.blocks.push((at, block));
            at += size;
            next += size;
        }
        self
    }

    /// The column written out, which only the prover needs.
    fn dense(&self) -> Vec<F64> {
        let mut column = vec![F64::ZERO; 1 << self.log_len];
        for (at, words) in &self.blocks {
            column[*at..at + words.len()].copy_from_slice(words);
        }
        column
    }

    /// The column's multilinear extension at `point`.
    fn eval(&self, point: &[F192]) -> F192 {
        assert_eq!(point.len(), self.log_len);
        let mut acc = F192::ZERO;
        for b in 0..self.blocks.len() {
            let (at, words) = &self.blocks[b];
            let k = words.len().ilog2() as usize;
            let mut selector = F192::ONE;
            for j in 0..point.len() - k {
                selector *= if (at >> (k + j)) & 1 == 1 {
                    point[k + j]
                } else {
                    point[k + j] + F192::ONE
                };
            }
            acc += selector * primitives::multilinear::mle_eval(words, &point[..k]);
        }
        acc
    }
}

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates. Every one of them is a
/// row the program executed, since a table's height is its row count (§sec:e2e-pad), so a
/// block has no padding rows to divide back out of the product.
#[derive(Clone, Debug)]
pub struct Block {
    pub kappa: usize,
    pub coords: Vec<Coord>,
}

/// Placement of each block in the stacked leaf vector (input order).
#[derive(Clone, Debug)]
pub struct Layout {
    pub mu: usize,
    pub offsets: Vec<usize>,
}

/// An evaluation claim on a committed column, settled against the witness.
/// Reconstructed identically by both sides (its value rides the stream).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnClaim {
    pub col: usize,
    pub point: Vec<F192>,
    pub value: F192,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    /// A lookup's read count is zero, so the read self-cancels on the bus (§sec:lookup).
    ZeroCount,
    Gkr(gkr::GkrError),
}

/// The fingerprint weights `eq(α⃗, x)` over the `2^N_TUPLE_BITS` slots (§sec:gp).
/// A tuple is fingerprinted as `Σ_x eq(α⃗, x)·σ_x`, a MULTILINEAR combination
/// rather than a power chain: each leaf factor is then of total degree
/// `N_TUPLE_BITS` in the challenges instead of the tuple width, and slot `x`'s
/// weight is an `eq` weight, which is what lets the aligned bytecode polynomial
/// be read off at `α⃗` itself (§sec:e2e-bc).
pub fn fingerprint_weights(alphas: &[F192]) -> Vec<F192> {
    debug_assert_eq!(alphas.len(), N_TUPLE_BITS);
    let mut w = vec![F192::ONE; 1 << N_TUPLE_BITS];
    for bit in 0..alphas.len() {
        let a = alphas[bit];
        for x in 0..w.len() {
            w[x] *= if (x >> bit) & 1 == 1 { a } else { a + F192::ONE };
        }
    }
    w
}

/// Bits indexing a bus tuple's coordinates: `m = 11` coordinates live in the
/// `2^4` slots of the bytecode encoding (§sec:m3, §sec:e2e-bc).
pub const N_TUPLE_BITS: usize = 4;

/// Conservative sum of the degree bounds for every random-challenge failure in
/// the bus argument. A side contains at most `2^mu` leaf factors, each of total
/// degree `N_TUPLE_BITS` in `α⃗` and one in `β`. The second term covers all
/// radix-four GKR batching and sumcheck challenges.
fn soundness_degree_bound(mu: usize) -> u128 {
    assert!(mu < u128::BITS as usize, "bus layout is too large to bound");
    let fingerprint = (N_TUPLE_BITS as u128 + 1) * (1u128 << mu);
    let gkr = 8u128 * (mu as u128 + 1).pow(2);
    fingerprint + gkr
}

fn soundness_bits(mu: usize) -> u32 {
    let degree = soundness_degree_bound(mu);
    192u32.saturating_sub(u128::BITS - degree.leading_zeros())
}

/// Check that the 192-bit challenge field supplies the target bus soundness.
/// Push and pull have the same logical height, and the count product is checked
/// by the same GKR rather than by a separate root-at-random test.
fn assert_grinding_unnecessary(
    push_blocks: &[Block],
    pull_blocks: &[Block],
    push: &Layout,
    pull: &Layout,
    count: &Layout,
) {
    assert_eq!(
        push.mu, pull.mu,
        "push/pull bus blocks are paired, so their layouts match"
    );
    assert!(count.mu <= push.mu, "count sums fewer bus messages than push");
    let widest = push_blocks
        .iter()
        .chain(pull_blocks)
        .map(|block| block.coords.len())
        .max()
        .unwrap_or(0);
    assert!(widest <= 1 << N_TUPLE_BITS, "a tuple's coordinates index its slots");
    assert!(
        soundness_bits(push.mu) >= crate::SECURITY_BITS,
        "bus layout exceeds the unground F192 soundness budget"
    );
}

/// Stack blocks largest-first at aligned offsets; `μ = ⌈log2 Σ 2^{κ_b}⌉`.
pub fn layout(blocks: &[Block]) -> Layout {
    let kappas: Vec<Option<usize>> = blocks.iter().map(|b| Some(b.kappa)).collect();
    let (offsets, placed) = crate::witness::stack_offsets(&kappas);
    Layout {
        mu: crate::log2_ceil_usize(placed.max(1)),
        offsets,
    }
}

/// The leaves one side leaves unmatched on the other, as `(side, block, row)`, under
/// one fixed fingerprint: what to look at when a bus does not balance.
#[cfg(test)]
pub(crate) fn unmatched_leaves(push: &[Block], pull: &[Block], cols: &[&[F64]]) -> Vec<(&'static str, usize, usize)> {
    let alphas: Vec<F192> = (0..N_TUPLE_BITS as u64)
        .map(|i| F192::new(3 + i, 5 + 7 * i, 11))
        .collect();
    let (w, beta) = (fingerprint_weights(&alphas), F192::new(13, 17, 19));
    let powers = power_tables([push, pull, &[]]);
    let longest = push.iter().chain(pull).map(|b| b.kappa).max().unwrap_or(0);
    let gpow = primitives::field::g_powers(1 << longest);
    let side = |blocks: &[Block]| {
        let lay = layout(blocks);
        let leaves = build_leaves(blocks, &lay, cols, &w, beta, &gpow, &powers);
        let mut at = Vec::new();
        for (b, block) in blocks.iter().enumerate() {
            at.extend((0..1usize << block.kappa).map(|z| (leaves[lay.offsets[b] + z], b, z)));
        }
        at
    };
    let (pushed, pulled) = (side(push), side(pull));
    let key = |leaf: &F192| (leaf.c0, leaf.c1, leaf.c2);
    let mut counts: HashMap<_, i64> = HashMap::new();
    for (leaf, ..) in &pushed {
        *counts.entry(key(leaf)).or_default() += 1;
    }
    for (leaf, ..) in &pulled {
        *counts.entry(key(leaf)).or_default() -= 1;
    }
    let unmatched = |name: &'static str, leaves: &[(F192, usize, usize)]| {
        leaves
            .iter()
            .filter(|(leaf, ..)| counts[&key(leaf)] != 0)
            .map(|&(_, b, z)| (name, b, z))
            .collect::<Vec<_>>()
    };
    [unmatched("push", &pushed), unmatched("pull", &pulled)].concat()
}

/// A non-constant coordinate as `(source, coefficient)`: its leaf contribution is
/// the mixed product `coeff · source(z)` with `source(z) ∈ K`, `coeff ∈ E`.
/// `GCol` folds the `g^k` factor into the coefficient.
enum Term<'a> {
    Col(usize, F192),
    Prod(usize, usize, F192),
    Index(F192),
    IntIndex(F192, u32),
    Public(&'a [F64], F192),
}

/// The values of each distinct [`Coord::Powers`] column, prover-side.
pub type PowerTables = Vec<((F64, F64), Vec<F64>)>;

fn power_tables(sides: [&[Block]; 3]) -> PowerTables {
    let mut tables = PowerTables::new();
    for blk in sides.into_iter().flatten() {
        for c in &blk.coords {
            if let Coord::Powers { first, ratio } = *c
                && !tables.iter().any(|(k, _)| *k == (first, ratio))
            {
                tables.push((
                    (first, ratio),
                    primitives::field::geometric(first, ratio, 1 << blk.kappa),
                ));
            }
        }
    }
    tables
}

/// Flatten one coordinate into leaf terms at coefficient `w`. A [`Coord::Sum`]
/// spreads its children over the SAME `w`: they are one coordinate, so they share
/// its `α`-power. `dense` is the coordinate written out, if it is a sparse column.
fn push_terms<'a>(
    c: &'a Coord,
    w: F192,
    powers: &'a PowerTables,
    dense: Option<&'a [F64]>,
    terms: &mut Vec<Term<'a>>,
    constant: &mut F192,
) {
    match c {
        Coord::Const(v) => push_sum_term(SumTerm::Const(*v), w, terms, constant),
        Coord::Col(i) => push_sum_term(SumTerm::Col(*i), w, terms, constant),
        Coord::GCol(i, k) => push_sum_term(SumTerm::GCol(*i, *k), w, terms, constant),
        Coord::Prod(i, j, k) => push_sum_term(SumTerm::Prod(*i, *j, *k), w, terms, constant),
        Coord::Index => terms.push(Term::Index(w)),
        Coord::IntIndex { base, shift } => {
            *constant += w.mul_base(*base);
            terms.push(Term::IntIndex(w, *shift));
        }
        Coord::Powers { first, ratio } => {
            let table = &powers
                .iter()
                .find(|(k, _)| *k == (*first, *ratio))
                .expect("every geometric column was tabulated")
                .1;
            terms.push(Term::Public(table, w));
        }
        Coord::Public(vals) => terms.push(Term::Public(vals.as_slice(), w)),
        Coord::Sparse(_) => terms.push(Term::Public(dense.expect("a sparse column is written out"), w)),
        Coord::Sum(ts) => {
            for &t in ts {
                push_sum_term(t, w, terms, constant);
            }
        }
    }
}

/// [`push_terms`] for one term of a sum.
fn push_sum_term(t: SumTerm, w: F192, terms: &mut Vec<Term<'_>>, constant: &mut F192) {
    match t {
        SumTerm::Const(v) => *constant += w.mul_base(v),
        SumTerm::Col(i) => terms.push(Term::Col(i, w)),
        SumTerm::GCol(i, k) => terms.push(Term::Col(i, w.mul_base(g_pow(k as usize)))),
        SumTerm::Prod(i, j, k) => terms.push(Term::Prod(i, j, w.mul_base(g_pow(k as usize)))),
    }
}

/// Build one side's leaf vector: block `b` row `z` holds `β − Σ_i w_i c_i(z)` for
/// the fingerprint weights `w = eq(α⃗, ·)`, followed implicitly by the identity `1`
/// up to `2^μ`. The row-invariant weights and constant coordinates are folded once
/// per block into `const_part`. `gpow` supplies `g^z` for [`Coord::Index`] and is
/// the caller's, shared by the three sides.
pub fn build_leaves(
    blocks: &[Block],
    lay: &Layout,
    cols: &[&[F64]],
    w: &[F192],
    beta: F192,
    gpow: &[F64],
    powers: &PowerTables,
) -> ArenaVec<F192> {
    let explicit = blocks
        .iter()
        .enumerate()
        .map(|(b, block)| lay.offsets[b] + (1usize << block.kappa))
        .max()
        .unwrap_or(1);
    debug_assert!(explicit <= 1usize << lay.mu);
    // `stack_offsets` packs the power-of-two blocks contiguously from zero, so the
    // blocks tile `0..explicit` and every slot below is written by one of them: the
    // identity fill would be overwritten in full, and this is the largest buffer in
    // the proof. The `covered` test is what licenses skipping it, so a layout that
    // ever left a hole falls back to filling rather than reading uninitialized rows.
    // Capacity is rounded to whole four-tuples because `gkr::QuaternaryLayerState`
    // pads this level to that before reading it, and growing it here would copy it.
    let covered: usize = blocks.iter().map(|blk| 1usize << blk.kappa).sum();
    let mut leaves = if covered == explicit {
        let mut values = ArenaVec::with_capacity(explicit.next_multiple_of(4));
        // SAFETY: the per-block fills below cover `0..explicit` exactly, and each
        // joins before this function returns.
        unsafe { values.set_len(explicit) };
        values
    } else {
        let mut values = ArenaVec::with_capacity(explicit.next_multiple_of(4));
        values.resize(explicit, F192::ONE);
        values
    };
    for (b, blk) in blocks.iter().enumerate() {
        let mut const_part = beta;
        let mut terms: Vec<Term> = Vec::with_capacity(blk.coords.len());
        let dense: Vec<Option<Vec<F64>>> = blk
            .coords
            .iter()
            .map(|c| match c {
                Coord::Sparse(column) => Some(column.dense()),
                _ => None,
            })
            .collect();
        for (i, c) in blk.coords.iter().enumerate() {
            push_terms(c, w[i], powers, dense[i].as_deref(), &mut terms, &mut const_part);
        }
        let row = |z: usize| -> F192 {
            // The α-weighted coordinate sum defers its reductions: each mixed
            // product contributes its three raw limb products (3 PMULL, no
            // reduction tail), one combined reduction per row at the end,
            // bit-identical to summing reduced `mul_base` terms.
            let mut acc = F192Unreduced::ZERO;
            for t in &terms {
                acc ^= match t {
                    Term::Col(i, c) => c.mul_base_unreduced(cols[*i][z]),
                    Term::Prod(i, j, c) => c.mul_base_unreduced(cols[*i][z] * cols[*j][z]),
                    Term::Index(c) => c.mul_base_unreduced(gpow[z]),
                    Term::IntIndex(c, shift) => c.mul_base_unreduced(F64((z as u64) << shift)),
                    Term::Public(vals, c) => c.mul_base_unreduced(vals[z]),
                };
            }
            const_part + acc.reduce()
        };
        let off = lay.offsets[b];
        // Every row of every block is a real row: a table's height is exactly the
        // number of rows it executed (`cpu::filler`), so no block has padding rows
        // whose tuples would have to be divided back out of the product.
        let dst = &mut leaves[off..off + (1usize << blk.kappa)];
        if dst.len() >= PAR_THRESHOLD {
            parallel::fill(dst, row);
        } else {
            for (z, slot) in dst.iter_mut().enumerate() {
                *slot = row(z);
            }
        }
    }
    leaves
}

/// One table's bus contribution on one side, as a form over that table's committed
/// columns: `Σ_c coeffs[c]·col_c(z) + Σ (a,b,c) c·col_a(z)·col_b(z) + constant`.
/// Every coefficient is a public function of `α`, `β` and the block selectors at
/// `ζ`, because a table's bus blocks carry only `Const`/`Col`/`GCol`/`Prod`
/// coordinates. The table sumcheck sums this against `eq(ζ[..τ], ·)` instead of
/// opening each column at `ζ`, which is why those per-column claims no longer reach
/// the PCS.
///
/// The quadratic part comes from [`Coord::Prod`] and is free: the AIR identities are
/// already degree 2, so a degree-2 form does not raise the round-polynomial degree
/// the batch pays for.
#[derive(Clone, Debug)]
pub struct BusForm {
    pub coeffs: Vec<F192>,
    /// `(col_a, col_b, coeff)` in LOCAL column indices.
    pub prods: Vec<(usize, usize, F192)>,
    pub constant: F192,
}

impl BusForm {
    fn new(n_cols: usize) -> Self {
        Self {
            coeffs: vec![F192::ZERO; n_cols],
            prods: Vec::new(),
            constant: F192::ZERO,
        }
    }

    /// The same form scaled by `w`. Every coefficient is `E`-valued already, so
    /// folding the side's `η`-power in here costs three multiplies once per table
    /// instead of one per [`eval`](Self::eval), which the zerocheck calls per row
    /// per round.
    pub fn scaled(&self, w: F192) -> Self {
        let mut coeffs = Vec::with_capacity(self.coeffs.len());
        for i in 0..self.coeffs.len() {
            coeffs.push(self.coeffs[i] * w);
        }
        let mut prods = Vec::with_capacity(self.prods.len());
        for i in 0..self.prods.len() {
            let (a, b, c) = self.prods[i];
            prods.push((a, b, c * w));
        }
        Self {
            coeffs,
            prods,
            constant: self.constant * w,
        }
    }

    /// The pointwise sum of several forms over the same columns.
    ///
    /// Evaluating the sum is evaluating each and adding, and the constraint batch
    /// only ever wants a table's total, so its three bus sides collapse to one
    /// dot product and one product list: the row loop then reads the column
    /// values once for all three rather than once each.
    pub fn sum(forms: &[Self]) -> Self {
        let mut out = forms[0].clone();
        for f in 1..forms.len() {
            let form = &forms[f];
            assert_eq!(out.coeffs.len(), form.coeffs.len(), "forms over the same columns");
            for i in 0..out.coeffs.len() {
                out.coeffs[i] += form.coeffs[i];
            }
            out.constant += form.constant;
            for i in 0..form.prods.len() {
                let (a, b, c) = form.prods[i];
                let mut merged = false;
                for j in 0..out.prods.len() {
                    if !merged && out.prods[j].0 == a && out.prods[j].1 == b {
                        out.prods[j].2 += c;
                        merged = true;
                    }
                }
                if !merged {
                    out.prods.push((a, b, c));
                }
            }
        }
        let mut prods = Vec::with_capacity(out.prods.len());
        for i in 0..out.prods.len() {
            if out.prods[i].2 != F192::ZERO {
                prods.push(out.prods[i]);
            }
        }
        out.prods = prods;
        out
    }

    /// The form at one point, unreduced: `evals` are the columns' values there.
    /// This is what the zerocheck evaluates, per row while a table is unfolded and
    /// at the sumcheck point after, so a table's several forms share one reduction
    /// rather than paying one per term.
    /// `quadratic` selects only degree-two terms, for a sumcheck round coefficient.
    pub fn eval_unreduced<T: ColVal>(&self, evals: &[T], quadratic: bool) -> F192Unreduced {
        self.prods.iter().fold(
            if quadratic {
                T::lift(F192::ZERO)
            } else {
                T::dot_unreduced(&self.coeffs, evals) ^ T::lift(self.constant)
            },
            |acc, &(a, b, c)| acc ^ (evals[a] * evals[b]).mul_e_unreduced(c),
        )
    }

    /// [`eval_unreduced`](Self::eval_unreduced) on its own.
    pub fn eval<T: ColVal>(&self, evals: &[T]) -> F192 {
        T::reduce(self.eval_unreduced(evals, false))
    }

    /// What the form sums to over the table's rows against `eq(ζ, ·)`, the target the
    /// zerocheck settles. The linear part factors through the columns' evaluations at
    /// `ζ`, which is the whole point of a form; a product coordinate does NOT, so
    /// `prod_sums` supplies `Σ_z eq(ζ,z)·col_a(z)·col_b(z)` for each pair it uses.
    fn sum_at(&self, evals: &[F192], prod_sums: &[(usize, usize, F192)]) -> F192 {
        self.prods
            .iter()
            .fold(F192::dot(&self.coeffs, evals, self.constant), |acc, &(a, b, c)| {
                let s = prod_sums
                    .iter()
                    .find(|p| (p.0, p.1) == (a, b))
                    .expect("every pair was summed");
                acc + c * s.2
            })
    }
}

/// One zero form per table, over its `(base, n_cols)` span's columns.
fn empty_forms(tables: &[(usize, usize)]) -> Vec<BusForm> {
    let mut forms = Vec::with_capacity(tables.len());
    for t in 0..tables.len() {
        forms.push(BusForm::new(tables[t].1));
    }
    forms
}

/// Accumulate one coordinate of a table's block into that table's form, at
/// coefficient `w`. A [`Coord::Sum`]'s children share `w`, so a derived value
/// lands as the several coefficients and products it is made of.
fn accumulate_form(c: &Coord, w: F192, base: usize, form: &mut BusForm) {
    match c {
        Coord::Const(v) => accumulate_term(SumTerm::Const(*v), w, base, form),
        Coord::Col(i) => accumulate_term(SumTerm::Col(*i), w, base, form),
        Coord::GCol(i, k) => accumulate_term(SumTerm::GCol(*i, *k), w, base, form),
        Coord::Prod(i, j, k) => accumulate_term(SumTerm::Prod(*i, *j, *k), w, base, form),
        Coord::Sum(ts) => {
            for i in 0..ts.len() {
                accumulate_term(ts[i], w, base, form);
            }
        }
        Coord::Index | Coord::IntIndex { .. } | Coord::Powers { .. } | Coord::Public(_) | Coord::Sparse(_) => {
            unreachable!("a table's bus block carries no virtual coordinate")
        }
    }
}

/// [`accumulate_form`] for one term of a sum.
fn accumulate_term(t: SumTerm, w: F192, base: usize, form: &mut BusForm) {
    match t {
        SumTerm::Const(v) => form.constant += w.mul_base(v),
        SumTerm::Col(i) => form.coeffs[i - base] += w,
        SumTerm::GCol(i, k) => form.coeffs[i - base] += w.mul_base(g_pow(k as usize)),
        SumTerm::Prod(i, j, k) => form.prods.push((i - base, j - base, w.mul_base(g_pow(k as usize)))),
    }
}

/// Where a framework block's values come from: a committed column's FRESH value at a
/// point (the prover's evaluation, or the verifier's read off the stream), and a
/// public column's evaluation.
trait Values {
    fn fresh(&mut self, col: usize, point: &[F192]) -> Result<F192, Error>;
    fn public(&mut self, vals: &Arc<Vec<F64>>, point: &[F192]) -> F192;
}

/// The verifier's values: the stream's, and each public column evaluated where it
/// is met.
impl Values for VerifierState<'_> {
    fn fresh(&mut self, _col: usize, _point: &[F192]) -> Result<F192, Error> {
        self.next_scalar().map_err(|_| Error::Truncated)
    }

    fn public(&mut self, vals: &Arc<Vec<F64>>, point: &[F192]) -> F192 {
        primitives::multilinear::mle_eval_par(vals, point)
    }
}

/// Walk one side's blocks. A block owned by table `t` (with column base `base`)
/// accumulates into `forms[t]`; the framework blocks are decomposed into per-column
/// claims as before, `values` supplying those not already in `claims`. Returns the
/// framework blocks' contribution to `Ṽ₀(ζ)` plus the padding mass, so the caller
/// can settle the side once the zerocheck has proven the tables' forms.
fn decompose_formula<V: Values>(
    blocks: &[Block],
    lay: &Layout,
    zeta: &[F192],
    w: &[F192],
    beta: F192,
    owners: &[Option<(usize, usize)>],
    forms: &mut [BusForm],
    claims: &mut Vec<ColumnClaim>,
    values: &mut V,
) -> Result<F192, Error> {
    assert_eq!(zeta.len(), lay.mu);
    let mut acc = F192::ZERO;
    let mut sel_sum = F192::ZERO;
    let mut failure = None;
    for b in 0..blocks.len() {
        let blk = &blocks[b];
        let kappa = blk.kappa;
        let sel = lay.offsets[b] >> kappa;
        let mut sel_bits = Vec::with_capacity(lay.mu - kappa);
        for k in 0..lay.mu - kappa {
            sel_bits.push(F192::new(((sel >> k) & 1) as u64, 0, 0));
        }
        let eq_hi = eq_eval(&sel_bits, &zeta[kappa..]);
        sel_sum += eq_hi;

        // A table's block becomes a linear form the zerocheck will sum; only the
        // framework blocks (boundary, memory, bytecode) still open columns at ζ.
        let owner = owners[b];
        match owner {
            Some((t, base)) => {
                let form = &mut forms[t];
                form.constant += eq_hi * beta;
                for i in 0..blk.coords.len() {
                    accumulate_form(&blk.coords[i], eq_hi * w[i], base, form);
                }
            }
            None => match framework_value(blk, &zeta[..kappa], w, claims, values) {
                Ok(inner) => acc += eq_hi * (beta + inner),
                Err(e) => {
                    failure = Some(e);
                    break;
                }
            },
        }
    }
    if let Some(e) = failure {
        return Err(e);
    }
    // The padding rows (identity `1`) contribute the leftover mass `1 - Σ_b sel_b`.
    Ok(acc + (F192::ONE + sel_sum))
}

/// A framework block's `Σ_i w_i·σ_i(ζ_lo)`.
fn framework_value<V: Values>(
    blk: &Block,
    zeta_lo: &[F192],
    w: &[F192],
    claims: &mut Vec<ColumnClaim>,
    values: &mut V,
) -> Result<F192, Error> {
    let mut inner = F192::ZERO;
    let mut failure = None;
    for i in 0..blk.coords.len() {
        let coord_val = match &blk.coords[i] {
            Coord::Const(v) => F192::from(*v),
            Coord::Index => index_mle(zeta_lo),
            Coord::IntIndex { base, shift } => int_index_mle(*base, *shift, zeta_lo),
            Coord::Powers { first, ratio } => powers_mle(*first, *ratio, zeta_lo),
            Coord::Col(c) => match column_value(claims, *c, zeta_lo, values) {
                Ok(v) => v,
                Err(e) => {
                    failure = Some(e);
                    break;
                }
            },
            Coord::GCol(c, k) => match column_value(claims, *c, zeta_lo, values) {
                Ok(v) => v.mul_base(g_pow(*k as usize)),
                Err(e) => {
                    failure = Some(e);
                    break;
                }
            },
            Coord::Prod(..) | Coord::Sum(..) => {
                unreachable!("only a table's bus block carries a degree-2 coordinate")
            }
            Coord::Public(vals) => values.public(vals, zeta_lo),
            Coord::Sparse(column) => column.eval(zeta_lo),
        };
        inner += w[i] * coord_val;
    }
    if let Some(e) = failure {
        return Err(e);
    }
    Ok(inner)
}

/// Column `col` at `point`: the recorded claim's value, else a fresh one, which is
/// recorded. The push ORDER is the stream order, so every coordinate that needs a
/// column value must go through here.
fn column_value<V: Values>(
    claims: &mut Vec<ColumnClaim>,
    col: usize,
    point: &[F192],
    values: &mut V,
) -> Result<F192, Error> {
    if let Some(v) = known_claim(claims, col, point) {
        return Ok(v);
    }
    let value = values.fresh(col, point)?;
    claims.push(ColumnClaim {
        col,
        point: point.to_vec(),
        value,
    });
    Ok(value)
}

/// Look up an already-recorded claim on `(col, point)`. Push and pull share
/// their GKR point, so a column read by both sides (or by two same-κ blocks of
/// one side) is streamed and opened ONCE; later occurrences reuse the value.
fn known_claim(claims: &[ColumnClaim], col: usize, point: &[F192]) -> Option<F192> {
    let mut value = None;
    for i in 0..claims.len() {
        if value.is_none() && claims[i].col == col && claims[i].point == point {
            value = Some(claims[i].value);
        }
    }
    value
}

// One bus GKR point per cache; its prefixes are keyed by length and shared column identity.
type PublicEvals = HashMap<(usize, usize), F192>;

/// The prover's values: the fresh ones evaluated ahead in stream order, each
/// written onto the stream as it is taken, and the public columns' evaluations
/// cached, since push and pull share them.
struct ProverValues<'a> {
    jobs: &'a [(usize, usize)],
    vals: &'a [F192],
    next: usize,
    cols: &'a [&'a [F64]],
    public: &'a mut PublicEvals,
    ps: &'a mut ProverState,
}

impl Values for ProverValues<'_> {
    fn fresh(&mut self, col: usize, point: &[F192]) -> Result<F192, Error> {
        let (jc, jk) = self.jobs[self.next];
        let v = self.vals[self.next];
        self.next += 1;
        debug_assert_eq!((jc, jk), (col, point.len()), "job/coord order drift");
        debug_assert_eq!(v, mle_eval(self.cols[col], point), "job/coord order drift");
        self.ps.add_scalar(v);
        Ok(v)
    }

    fn public(&mut self, vals: &Arc<Vec<F64>>, point: &[F192]) -> F192 {
        *self
            .public
            .entry((Arc::as_ptr(vals) as usize, point.len()))
            .or_insert_with(|| primitives::multilinear::mle_eval_par(vals, point))
    }
}

/// Prover-side decomposition: reads the real columns, writing each FRESH
/// committed value onto the stream and recording the matching claim
/// (block/coord order); duplicates reuse the recorded value.
///
/// The fresh column MLE evaluations run in a parallel first pass: within one
/// `decompose_formula` call no challenge is sampled between claims (`zeta`,
/// `alpha`, `beta` are fixed arguments and each claim's point is
/// `zeta[..kappa]` of its block), so the values are independent of the
/// transcript and only their `add_scalar` ORDER matters. The second pass
/// replays them through the transcript in the original block/coord order,
/// keeping the stream byte-identical to the serial form.
fn decompose_prove(
    blocks: &[Block],
    lay: &Layout,
    cols: &[&[F64]],
    zeta: &[F192],
    w: &[F192],
    beta: F192,
    owners: &[Option<(usize, usize)>],
    forms: &mut [BusForm],
    claims: &mut Vec<ColumnClaim>,
    public: &mut PublicEvals,
    ps: &mut ProverState,
) -> F192 {
    // Pass 1: enumerate the FRESH committed coords exactly as `decompose_formula`
    // visits them (blocks in order, coords in order, Col/GCol only, first
    // occurrence per `(col, point)`, the same dedup as `known_claim`), then
    // evaluate the column MLEs in parallel.
    let mut jobs: Vec<(usize, usize)> = Vec::new();
    for (b, blk) in blocks.iter().enumerate() {
        if owners[b].is_some() {
            continue;
        }
        for c in &blk.coords {
            if let Coord::Col(i) | Coord::GCol(i, _) = c {
                let fresh = known_claim(claims, *i, &zeta[..blk.kappa]).is_none() && !jobs.contains(&(*i, blk.kappa));
                if fresh {
                    jobs.push((*i, blk.kappa));
                }
            }
        }
    }
    let vals: Vec<F192> = parallel::map_collect(jobs.len(), |i| {
        let (col, kappa) = jobs[i];
        mle_eval(cols[col], &zeta[..kappa])
    });

    // Pass 2: replay in the original order; duplicates reuse the recorded claim.
    let mut values = ProverValues {
        jobs: &jobs,
        vals: &vals,
        next: 0,
        cols,
        public,
        ps,
    };
    let framework = decompose_formula(blocks, lay, zeta, w, beta, owners, forms, claims, &mut values)
        .expect("prover decomposition is infallible");
    assert_eq!(
        values.next,
        jobs.len(),
        "job enumeration matches decompose_formula's order"
    );
    framework
}

/// Selector bits of the stacked bytecode polynomial: the public encoding
/// columns (opcode + seven operand/immediate slots = eight) stack along
/// `2^N_BYTECODE_SELECTORS` slots. A column's slot is its bus tuple coordinate,
/// which is what fixes the width at sixteen rather than at the column count.
pub const N_BYTECODE_SELECTORS: usize = 4;

/// Slot of the first public column: the bytecode block leads with three
/// non-public coordinates (tag, index, read count), and a column's slot IS its
/// bus tuple coordinate.
pub const BYTECODE_PUBLIC_SLOT: usize = 3;

/// The stacked bytecode polynomial as a dense table: eight public encoding
/// columns at their tuple coordinates, padded to sixteen selector slots. The
/// program's digest is taken over it ([`crate::cpu::Program`]).
pub fn stacked_bytecode_table(blocks: &[Block]) -> Vec<F64> {
    let mut kbc = 0;
    let mut cols: Vec<&[F64]> = Vec::new();
    for blk in blocks {
        for c in &blk.coords {
            if let Coord::Public(vals) = c {
                kbc = blk.kappa;
                cols.push(vals.as_slice());
            }
        }
    }
    let mut table = vec![F64::ZERO; 1 << (N_BYTECODE_SELECTORS + kbc)];
    for (i, vals) in cols.into_iter().enumerate() {
        let slot = BYTECODE_PUBLIC_SLOT + i;
        assert!(slot < 1 << N_BYTECODE_SELECTORS, "a public slot is a tuple coordinate");
        assert_eq!(vals.len(), 1 << kbc);
        table[(slot << kbc)..((slot + 1) << kbc)].copy_from_slice(vals);
    }
    table
}

/// The three bus sides in `[push, pull, count]` order with their fingerprint
/// weights. The count channel's leaf is the count itself (a single `Col`), so it
/// runs at `α⃗ = 0` (weight `1` on slot `0`, zero elsewhere), `β = 0`, and its GKR
/// root is the product of all counts.
fn sides<'a>(
    blocks: [&'a [Block]; 3],
    lays: [&'a Layout; 3],
    w: &'a [F192],
    count_w: &'a [F192],
    beta: F192,
) -> [(&'a [Block], &'a Layout, &'a [F192], F192); 3] {
    [
        (blocks[0], lays[0], w, beta),
        (blocks[1], lays[1], w, beta),
        (blocks[2], lays[2], count_w, F192::ZERO),
    ]
}

/// Prove the bus balances; returns the per-column claims to open (§sec:leafstack). `alpha`/
/// `beta` follow the witness commitment (the only ordering the grand product
/// needs), and the block structure is public, so no shape is observed.
/// Everything the bus hands on: the framework blocks' column claims,
/// the shared GKR point (the table sumcheck's eq point), and
/// per side the tables' linear forms plus what each is claimed to sum to.
pub struct BusProof {
    pub claims: Vec<ColumnClaim>,
    /// The GKR point ζ: the zerocheck reuses it, so no fresh point is sampled.
    pub point: Vec<F192>,
    /// `forms[side][table]`, in `[push, pull, count]` order.
    pub forms: [Vec<BusForm>; 3],
    /// `sigmas[side][table]`: each form's eq-weighted sum over its table's rows.
    /// Prover-side only. NOTHING here travels: the batch's target is the caller's
    /// derived `Σ_s η^·totals[s]`, and the shares serve only to build each round's
    /// waiting line, which rides inside the round polynomial.
    pub sigmas: [Vec<F192>; 3],
}

pub fn prove_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    cols: &[&[F64]],
    owners: &[Vec<Option<(usize, usize)>>; 3],
    tables: &[(usize, usize)],
    ps: &mut ProverState,
) -> BusProof {
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let mut count_lay = layout(count);
    assert_grinding_unnecessary(push, pull, &push_lay, &pull_lay, &count_lay);
    let alphas: Vec<F192> = (0..N_TUPLE_BITS).map(|_| ps.sample()).collect();
    let w = fingerprint_weights(&alphas);
    let count_w = fingerprint_weights(&[F192::ZERO; N_TUPLE_BITS]);
    let beta = ps.sample();
    // The `g^z` table backing `Coord::Index`, built once for the three sides: push
    // and pull would otherwise build the same table twice and count, which carries
    // no `Index` coordinate, would build one it never reads.
    let index_k = [push, pull, count]
        .into_iter()
        .flatten()
        .filter(|b| b.coords.iter().any(|c| matches!(c, Coord::Index)))
        .map(|b| b.kappa)
        .max();
    let gpow = index_k.map_or_else(Vec::new, |k| primitives::field::g_powers(1usize << k));
    let powers = power_tables([push, pull, count]);
    // Three independent leaf vectors, built one after another: each `build_leaves`
    // already fans its own blocks out across the whole pool, so nesting a
    // three-way outer split on top would only add a barrier.
    let [push_leaves, pull_leaves, count_leaves] = crate::stage!("Bus leaves", || {
        [
            build_leaves(push, &push_lay, cols, &w, beta, &gpow, &powers),
            build_leaves(pull, &pull_lay, cols, &w, beta, &gpow, &powers),
            build_leaves(count, &count_lay, cols, &count_w, F192::ZERO, &gpow, &powers),
        ]
    });
    // Leaf construction keeps the all-one padding implicit; decomposition uses the full logical depth.
    count_lay.mu = push_lay.mu;
    // All three trees run as ONE RLC-batched GKR (equal μ: push/pull match
    // block-for-block, count is padded), so every claim lands on ONE point ζ.
    let bus_gkr = crate::stage!("Bus GKR", || {
        gkr::prove_product_triple(
            [push_leaves, pull_leaves, count_leaves],
            ps,
            gkr::RootShape::FirstTwoShared,
        )
    });

    // Framework blocks keep their per-column claims (deduped: push/pull share ζ);
    // every table block becomes a form for the zerocheck instead.
    let mut claims: Vec<ColumnClaim> = Vec::new();
    let sides = sides(
        [push, pull, count],
        [&push_lay, &pull_lay, &count_lay],
        &w,
        &count_w,
        beta,
    );
    // Each table's columns at ζ[..τ], computed once and shared by the three sides
    // (a form's linear part factors through them). Nothing here travels, neither the
    // evaluations nor any total: the verifier derives each side's table share as `Ṽ₀(ζ)` less the
    // framework decomposition ([`verify_balance`]) and the batch settles it. A
    // transmitted total would appear in exactly one check, which it could always be
    // solved to satisfy, and would settle nothing.
    let mut forms = [empty_forms(tables), empty_forms(tables), empty_forms(tables)];
    let mut frameworks = [F192::ZERO; 3];
    let mut public = PublicEvals::new();
    crate::stage!("Bus decompose", || {
        for (s, &(blocks, lay, a, g)) in sides.iter().enumerate() {
            frameworks[s] = decompose_prove(
                blocks,
                lay,
                cols,
                &bus_gkr.point,
                a,
                g,
                &owners[s],
                &mut forms[s],
                &mut claims,
                &mut public,
                ps,
            );
        }
    });
    let (table_evals, prod_sums) = tables_and_prods_at(cols, tables, &forms, &bus_gkr.point);
    let sigmas: [Vec<F192>; 3] = std::array::from_fn(|s| {
        let sigmas: Vec<F192> = forms[s]
            .iter()
            .zip(&table_evals)
            .zip(&prod_sums)
            .map(|((f, e), p)| f.sum_at(e, p))
            .collect();
        // Completeness only: the verifier derives this identity rather than checking
        // it, so a mismatch here is a prover bug, not a rejection path.
        debug_assert_eq!(
            sigmas.iter().fold(frameworks[s], |acc, &b| acc + b),
            bus_gkr.values[s],
            "side {s} must decompose into its leaf value"
        );
        sigmas
    });

    BusProof {
        claims,
        point: bus_gkr.point,
        forms,
        sigmas,
    }
}

/// Every table's committed columns at `ζ[..τ_t]`, and, for every column pair its
/// forms multiply, `Σ_z eq(ζ[..τ], z)·col_a(z)·col_b(z)`.
///
/// One eq table per table, streamed once past every column and every pair at
/// the same time. Evaluated apart these are `n_cols + n_pairs` fold ladders
/// over the same table at the same point, and a ladder lifts every `K` word it
/// reads into an `E` it writes and reads again, where a dot against the weights
/// moves the column's own eight bytes. Pairs are deduped across the three sides
/// and the several blocks that carry the same address, so an address costs one
/// pass however often it is flushed. `tables[t] = (base, n_cols)` in the global
/// schema; a pair names LOCAL column indices.
#[allow(clippy::type_complexity)]
fn tables_and_prods_at(
    cols: &[&[F64]],
    tables: &[(usize, usize)],
    forms: &[Vec<BusForm>; 3],
    zeta: &[F192],
) -> (Vec<Vec<F192>>, Vec<Vec<(usize, usize, F192)>>) {
    /// Rows per task: the eq slice a task reads stays in L2 while every column
    /// and pair accumulator sweeps past it.
    const ROWS: usize = 1 << 12;

    tables
        .iter()
        .enumerate()
        .map(|(t, &(base, n_cols))| {
            let tau = crate::log2_strict_usize(cols[base].len());
            let mut pairs: Vec<(usize, usize)> = forms
                .iter()
                .flat_map(|side| side[t].prods.iter().map(|&(a, b, _)| (a, b)))
                .collect();
            pairs.sort_unstable();
            pairs.dedup();

            let eq = eq_table_arena(&zeta[..tau]);
            let n_acc = n_cols + pairs.len();
            let sums = parallel::fold_reduce(
                (1usize << tau).div_ceil(ROWS),
                || vec![F192Unreduced::ZERO; n_acc],
                |acc, chunk| {
                    let lo = chunk * ROWS;
                    let weights = &eq[lo..(lo + ROWS).min(1 << tau)];
                    let span = |c: usize| &cols[base + c][lo..lo + weights.len()];
                    for (c, slot) in acc[..n_cols].iter_mut().enumerate() {
                        for (&w, &v) in weights.iter().zip(span(c)) {
                            *slot ^= w.mul_base_unreduced(v);
                        }
                    }
                    for (&(a, b), slot) in pairs.iter().zip(&mut acc[n_cols..]) {
                        for ((&w, &x), &y) in weights.iter().zip(span(a)).zip(span(b)) {
                            *slot ^= w.mul_base_unreduced(x * y);
                        }
                    }
                },
                |mut left, right| {
                    for (slot, part) in left.iter_mut().zip(right) {
                        *slot ^= part;
                    }
                    left
                },
            );
            let evals = sums[..n_cols].iter().map(|s| s.reduce()).collect();
            let prods = pairs
                .iter()
                .zip(&sums[n_cols..])
                .map(|(&(a, b), s)| (a, b, s.reduce()))
                .collect();
            (evals, prods)
        })
        .unzip()
}

/// What [`verify_balance`] establishes: the per-column claims to open and the
/// table forms with their claimed sums.
pub struct BusVerify {
    pub claims: Vec<ColumnClaim>,
    /// The GKR point ζ, reused as the table sumcheck's eq point.
    pub point: Vec<F192>,
    /// `forms[side][table]`, for the zerocheck to settle.
    pub forms: [Vec<BusForm>; 3],
    /// Per side, what the tables' blocks owe its leaf claim: `Ṽ₀(ζ)` less the
    /// framework blocks' decomposition. Derived here, pinned by the batch's target.
    pub totals: [F192; 3],
}

/// Verify the bus balances, oracle-free (the prover's committed values arrive on
/// the stream and are certified by `pcs`). Returns the per-column claims to open.
pub fn verify_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    owners: &[Vec<Option<(usize, usize)>>; 3],
    tables: &[(usize, usize)],
    vs: &mut VerifierState,
) -> Result<BusVerify, Error> {
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let mut count_lay = layout(count);
    assert_grinding_unnecessary(push, pull, &push_lay, &pull_lay, &count_lay);
    let mut alphas = Vec::with_capacity(N_TUPLE_BITS);
    for _ in 0..N_TUPLE_BITS {
        alphas.push(vs.sample());
    }
    let w = fingerprint_weights(&alphas);
    let count_w = fingerprint_weights(&[F192::ZERO; N_TUPLE_BITS]);
    // The count tree is padded to the pair's depth (identity leaves), so all
    // three verify as ONE RLC-batched GKR at ONE shared point.
    count_lay.mu = push_lay.mu;
    let beta = vs.sample();
    let bus_gkr = gkr::verify_product_triple(push_lay.mu, vs, gkr::RootShape::FirstTwoShared).map_err(Error::Gkr)?;
    let count_root = bus_gkr.roots[2];
    // Every lookup's read count is nonzero iff this product is (§sec:lookup); a zero would
    // let a read self-cancel and free its value from memory.
    if count_root == F192::ZERO {
        return Err(Error::ZeroCount);
    }
    // Every row of every table is a real row (`cpu::filler`), so the two sides balance
    // outright: no padding tuples to divide back out, and no announced row counts whose
    // truthfulness the soundness argument would have to establish. The GKR sends ONE root
    // for both sides, so a prover cannot even state an unbalanced bus, and there is nothing
    // to check here.

    // Framework blocks decompose as before; the tables' blocks become linear forms.
    // Each side's table share is DERIVED from `framework + Ṽ₀(ζ)` rather than checked
    // here, the batch's target being what pins it, so no table column is opened at ζ.
    // The sides as [`sides`] pairs them: the count channel at `α⃗ = 0` and `β = 0`.
    let mut claims: Vec<ColumnClaim> = Vec::new();
    let mut forms = [empty_forms(tables), empty_forms(tables), empty_forms(tables)];
    let point = &bus_gkr.point;
    let push_framework = decompose_formula(
        push,
        &push_lay,
        point,
        &w,
        beta,
        &owners[0],
        &mut forms[0],
        &mut claims,
        vs,
    )?;
    let pull_framework = decompose_formula(
        pull,
        &pull_lay,
        point,
        &w,
        beta,
        &owners[1],
        &mut forms[1],
        &mut claims,
        vs,
    )?;
    let count_framework = decompose_formula(
        count,
        &count_lay,
        point,
        &count_w,
        F192::ZERO,
        &owners[2],
        &mut forms[2],
        &mut claims,
        vs,
    )?;
    // What the tables owe each side: DERIVED, never read. A transmitted total would be
    // a free variable in its own check and would settle nothing; the caller instead
    // pins these against the batch's target.
    let totals = [
        push_framework + bus_gkr.values[0],
        pull_framework + bus_gkr.values[1],
        count_framework + bus_gkr.values[2],
    ];

    Ok(BusVerify {
        claims,
        point: bus_gkr.point,
        forms,
        totals,
    })
}

#[cfg(test)]
mod tests {
    use super::{F64, F192, SparseColumn, soundness_bits};

    /// A sparse column's block-wise evaluation is its dense multilinear extension,
    /// whatever the stretches' offsets and lengths.
    #[test]
    fn sparse_column_evaluates_as_its_dense_form() {
        let words: Vec<u64> = (1..=37).map(|i| i * 0x9e37_79b9_7f4a_7c15).collect();
        let column = SparseColumn::new(9)
            .with_stretch(0, &words[..4])
            .with_stretch(5, &words[4..17])
            .with_stretch(300, &words[17..]);
        assert_eq!(
            column.dense()[5..18],
            words[4..17].iter().map(|&w| F64(w)).collect::<Vec<_>>()
        );
        assert_eq!(column.dense().iter().filter(|w| !w.is_zero()).count(), words.len());
        let point: Vec<F192> = (0..9).map(|i| F192::new(3 + i, 5 * i + 1, 7)).collect();
        assert_eq!(
            column.eval(&point),
            primitives::multilinear::mle_eval(&column.dense(), &point)
        );
    }

    /// The bound is `(N_TUPLE_BITS + 1)·2^mu` plus the GKR terms: only the bus
    /// DEPTH costs bits now, the multilinear fingerprint having fixed each factor's
    /// degree at four in `α⃗` and one in `β`, whatever the tuple's width.
    #[test]
    fn bus_soundness_tracks_depth_only() {
        assert!(soundness_bits(38) >= crate::SECURITY_BITS);
        assert!(soundness_bits(61) >= crate::SECURITY_BITS);
        assert!(soundness_bits(62) < crate::SECURITY_BITS);
    }
}
