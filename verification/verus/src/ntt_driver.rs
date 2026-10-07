//! The parallel driver of the additive NTT: `transform`, `gathered_pass`, `run_layers`, `fused_rows`,
//! `replicate` and the fused row groups of `crates/pcs/src/ntt/additive_ntt_f64.rs`.
//!
//! The copies keep production's bodies, with the buffer's memory held as permissions
//! ([`crate::parallel::owns`]): every raw pointer access goes through the permission of the element it
//! touches, and the pool's tasks receive disjoint permission maps, so the tasks cannot race and no access
//! is out of bounds. `tests/equivalence/ntt_driver.rs` checks the copies against production.
//!
//! Specification:
//!
//! - [`gather`]: rows `base + r + i * step` of a buffer, as a buffer of their own.
//! - [`sub_layers`]: the forward layers `first..end` of a `2^log_d`-row transform run on one of its
//!   `2^o` sub-blocks, which fixes the global block index, and so the twiddle, of each block.
//!
//! Main results: a layer commutes with a gather of rows it pairs among themselves
//! ([`lemma_gather_layer`], [`lemma_gather_sub_layers`]); `run_layers`, the fused groups and
//! `gathered_pass` run the layers they claim; `transform` computes [`forward_layers`], the specification of
//! the verified reference `forward_scalar_from_layer`.
// `global size_of usize` expands to a braced block.
#![allow(unused_braces)]

use crate::gf2_64::*;
use crate::ntt::*;
use crate::parallel::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// The index in the buffer of word `q` of a gather: row `base + r + (q / m) * step`, lane `q % m`.
pub open spec fn gidx(m: nat, base: int, r: int, step: int, q: int) -> int {
    (base + r + (q / (m as int)) * step) * (m as int) + q % (m as int)
}

/// Rows `base + r + i * step`, `i < cnt`, of a buffer of `m` lanes, as one buffer of `cnt` rows.
pub open spec fn gather(x: Seq<F64>, m: nat, base: int, r: int, step: int, cnt: nat) -> Seq<F64> {
    Seq::new(cnt * m, |q: int| x[gidx(m, base, r, step, q)])
}

/// The twiddles of one layer on sub-block `s` of `2^o`: block `b` of the sub-block is block
/// `s * 2^(layer - o) + b` of the domain.
pub open spec fn sub_twiddles(tab: Seq<Seq<F64>>, layer: nat, o: nat, s: int) -> spec_fn(int) -> u64 {
    |b: int| twiddle_spec(tab, layer, (s * pow2((layer - o) as nat) + b) as usize)
}

/// The forward layers `first..end` of a `2^log_d`-row transform on `m` lanes, run on its sub-block `s`
/// of `2^o` (`o <= first`), a buffer of `2^(log_d - o)` rows.
pub open spec fn sub_layers(
    tab: Seq<Seq<F64>>,
    x: Seq<F64>,
    m: nat,
    log_d: nat,
    o: nat,
    s: int,
    first: nat,
    end: nat,
) -> Seq<F64>
    decreases end,
{
    if end <= first {
        x
    } else {
        layer_map(
            sub_layers(tab, x, m, log_d, o, s, first, (end - 1) as nat),
            m,
            layer_half(log_d, (end - 1) as nat),
            sub_twiddles(tab, (end - 1) as nat, o, s),
            false,
        )
    }
}

// ---------------------------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------------------------
/// Word `lane` of row `row` is word `row * m + lane`.
pub proof fn lemma_word(row: int, lane: int, m: int)
    requires
        m > 0,
        0 <= lane < m,
    ensures
        (row * m + lane) / m == row,
        (row * m + lane) % m == lane,
{
    lemma_fundamental_div_mod_converse(row * m + lane, m, row, lane);
}

/// Every word is `row * m + lane`.
pub proof fn lemma_split_word(q: int, m: int)
    requires
        m > 0,
        q >= 0,
    ensures
        q == (q / m) * m + q % m,
        q / m >= 0,
        0 <= q % m < m,
{
    lemma_fundamental_div_mod(q, m);
    lemma_mod_bound(q, m);
    lemma_div_pos_is_pos(q, m);
    lemma_mul_is_commutative(q / m, m);
}

/// Row `base + r + i * step`, with `base` a multiple of `2H = 2 k step` and `r < step`, lies in block
/// `base / 2H + i / 2k`, at row `(i % 2k) * step + r` of it: a top row exactly when `i % 2k < k`.
pub proof fn lemma_row_split(base: int, r: int, i: int, step: int, k: int)
    requires
        step > 0,
        0 <= r < step,
        k > 0,
        i >= 0,
        base >= 0,
        base % (2 * k * step) == 0,
    ensures
        (base + r + i * step) / (2 * k * step) == base / (2 * k * step) + i / (2 * k),
        (base + r + i * step) % (2 * k * step) == (i % (2 * k)) * step + r,
        ((i % (2 * k)) * step + r < k * step) == (i % (2 * k) < k),
{
    let h2 = 2 * k * step;
    assert(h2 > 0) by (nonlinear_arith)
        requires
            k > 0,
            step > 0,
            h2 == 2 * k * step,
    ;
    let a = i / (2 * k);
    let j = i % (2 * k);
    let c0 = base / h2;
    lemma_fundamental_div_mod(i, 2 * k);
    lemma_mod_bound(i, 2 * k);
    lemma_fundamental_div_mod(base, h2);
    assert(base + r + i * step == (c0 + a) * h2 + (j * step + r)) by (nonlinear_arith)
        requires
            i == (2 * k) * a + j,
            base == h2 * c0,
            h2 == 2 * k * step,
    ;
    assert(0 <= j * step + r < h2) by (nonlinear_arith)
        requires
            0 <= j < 2 * k,
            0 <= r < step,
            h2 == 2 * k * step,
    ;
    lemma_fundamental_div_mod_converse(base + r + i * step, h2, c0 + a, j * step + r);
    if j < k {
        assert(j * step + r < k * step) by (nonlinear_arith)
            requires
                0 <= j <= k - 1,
                r < step,
                step > 0,
        ;
    } else {
        assert(j * step + r >= k * step) by (nonlinear_arith)
            requires
                j >= k,
                r >= 0,
                step > 0,
        ;
    }
}

/// A word of a gather below `cnt` rows, and its partner rows `k` away.
proof fn lemma_gather_rows(q: int, m: int, cnt: int, k: int)
    requires
        m > 0,
        k > 0,
        cnt % (2 * k) == 0,
        0 <= q < cnt * m,
    ensures
        0 <= q / m < cnt,
        (q / m) % (2 * k) < k ==> q / m + k < cnt && q + k * m < cnt * m && (q + k * m) / m == q / m + k && (q + k * m) % m
            == q % m,
        (q / m) % (2 * k) >= k ==> q / m >= k && q - k * m >= 0 && (q - k * m) / m == q / m - k && (q - k * m) % m == q % m,
        (q / m) / (2 * k) < cnt / (2 * k),
{
    let i = q / m;
    let lane = q % m;
    lemma_split_word(q, m);
    assert(i < cnt) by (nonlinear_arith)
        requires
            q == i * m + lane,
            0 <= lane,
            q < cnt * m,
            m > 0,
    ;
    let a = i / (2 * k);
    let j = i % (2 * k);
    let c = cnt / (2 * k);
    lemma_fundamental_div_mod(i, 2 * k);
    lemma_mod_bound(i, 2 * k);
    lemma_fundamental_div_mod(cnt, 2 * k);
    assert(a < c) by (nonlinear_arith)
        requires
            i == (2 * k) * a + j,
            cnt == (2 * k) * c,
            0 <= j,
            i < cnt,
            k > 0,
    ;
    if j < k {
        assert(i + k < cnt) by (nonlinear_arith)
            requires
                i == (2 * k) * a + j,
                cnt == (2 * k) * c,
                0 <= j < k,
                a + 1 <= c,
                k > 0,
        ;
        assert(q + k * m == (i + k) * m + lane) by (nonlinear_arith)
            requires
                q == i * m + lane,
        ;
        lemma_word(i + k, lane, m);
        assert((i + k) * m + lane < cnt * m) by (nonlinear_arith)
            requires
                i + k + 1 <= cnt,
                lane < m,
                m > 0,
        ;
    } else {
        assert(q - k * m == (i - k) * m + lane) by (nonlinear_arith)
            requires
                q == i * m + lane,
        ;
        lemma_word(i - k, lane, m);
        assert((i - k) * m + lane >= 0) by (nonlinear_arith)
            requires
                i >= k,
                lane >= 0,
                m > 0,
        ;
    }
}

// ---------------------------------------------------------------------------------------------
// A layer commutes with a gather of the rows it pairs
// ---------------------------------------------------------------------------------------------
/// One layer of half `H = k * step`, gathered on rows `base + r + i * step` (`r < step`, `base` a multiple
/// of a block), is the layer of half `k` on the gathered buffer, with the twiddles of the blocks the
/// gathered rows come from.
pub proof fn lemma_gather_layer(
    x: Seq<F64>,
    m: nat,
    h: nat,
    tw: spec_fn(int) -> u64,
    tw2: spec_fn(int) -> u64,
    inverse: bool,
    base: int,
    r: int,
    step: int,
    cnt: nat,
    k: nat,
)
    requires
        m > 0,
        step > 0,
        0 <= r < step,
        k > 0,
        h == k * step,
        cnt % (2 * k) == 0,
        base >= 0,
        base % (2 * h as int) == 0,
        (base + cnt * step) * m <= x.len(),
        forall|b: int| 0 <= b < cnt / (2 * k) ==> #[trigger] tw2(b) == tw(base / (2 * h as int) + b),
    ensures
        gather(layer_map(x, m, h, tw, inverse), m, base, r, step, cnt) == layer_map(
            gather(x, m, base, r, step, cnt),
            m,
            k,
            tw2,
            inverse,
        ),
{
    let y = layer_map(x, m, h, tw, inverse);
    let g = gather(x, m, base, r, step, cnt);
    let lhs = gather(y, m, base, r, step, cnt);
    let rhs = layer_map(g, m, k, tw2, inverse);
    let mi = m as int;
    assert forall|q: int| 0 <= q < cnt * m implies lhs[q] == rhs[q] by {
        let i = q / mi;
        let lane = q % mi;
        lemma_split_word(q, mi);
        lemma_gather_rows(q, mi, cnt as int, k as int);
        let row = base + r + i * step;
        let p = row * mi + lane;
        assert(gidx(m, base, r, step, q) == p);
        lemma_word(row, lane, mi);
        assert(2 * h as int == 2 * (k as int) * step) by (nonlinear_arith)
            requires
                h == k * step,
        ;
        lemma_row_split(base, r, i, step, k as int);
        assert(row >= 0) by (nonlinear_arith)
            requires
                row == base + r + i * step,
                base >= 0,
                r >= 0,
                i >= 0,
                step > 0,
        ;
        assert(row + 1 <= base + cnt * step) by (nonlinear_arith)
            requires
                row == base + r + i * step,
                i + 1 <= cnt,
                0 <= r < step,
                step > 0,
        ;
        assert(p < x.len()) by (nonlinear_arith)
            requires
                p == row * mi + lane,
                row + 1 <= base + cnt * step,
                0 <= lane < mi,
                row >= 0,
                (base + cnt * step) * mi <= x.len(),
        ;
        assert(p >= 0) by (nonlinear_arith)
            requires
                p == row * mi + lane,
                row >= 0,
                lane >= 0,
                mi > 0,
        ;
        // The full layer at `p`: row `row`, block `base / 2H + i / 2k`, in-block row `(i % 2k) step + r`.
        assert(row_of(p, m) == row);
        assert(blk_of(p, m, h) == base / (2 * h as int) + i / (2 * k as int));
        assert(r_of(p, m, h) == (i % (2 * k as int)) * step + r);
        // The gathered layer at `q`: row `i`, block `i / 2k`, in-block row `i % 2k`.
        assert(row_of(q, m) == i);
        assert(blk_of(q, m, k) == i / (2 * k as int));
        assert(r_of(q, m, k) == i % (2 * k as int));
        assert(tw2(i / (2 * k as int)) == tw(base / (2 * h as int) + i / (2 * k as int)));
        if i % (2 * k as int) < k {
            let q2 = q + k * m;
            assert((row + k * step) * mi == row * mi + (k * step) * mi) by (nonlinear_arith);
            assert((i + k) * step == i * step + k * step) by (nonlinear_arith);
            assert(h * m == (k * step) * mi);
            assert(gidx(m, base, r, step, q2) == p + h * m);
            assert(g[q2] == x[p + h * m]);
        } else {
            let q2 = q - k * m;
            assert((row - k * step) * mi == row * mi - (k * step) * mi) by (nonlinear_arith);
            assert((i - k) * step == i * step - k * step) by (nonlinear_arith);
            assert(h * m == (k * step) * mi);
            assert(gidx(m, base, r, step, q2) == p - h * m);
            assert(g[q2] == x[p - h * m]);
        }
    }
    assert(lhs =~= rhs);
}

/// Layers with twiddles that agree on every block are equal.
pub proof fn lemma_layer_map_tw(x: Seq<F64>, m: nat, h: nat, tw: spec_fn(int) -> u64, tw2: spec_fn(int) -> u64, inverse: bool)
    requires
        m > 0,
        h > 0,
        forall|b: int| 0 <= b ==> #[trigger] tw(b) == tw2(b),
    ensures
        layer_map(x, m, h, tw, inverse) == layer_map(x, m, h, tw2, inverse),
{
    assert forall|p: int| 0 <= p < x.len() implies layer_map(x, m, h, tw, inverse)[p] == layer_map(x, m, h, tw2, inverse)[p] by {
        lemma_div_pos_is_pos(p, m as int);
        lemma_div_pos_is_pos(row_of(p, m), 2 * h as int);
    }
    assert(layer_map(x, m, h, tw, inverse) =~= layer_map(x, m, h, tw2, inverse));
}

/// A gather of `cnt` consecutive rows is a subrange.
pub proof fn lemma_gather_contiguous(x: Seq<F64>, m: nat, base: int, cnt: nat)
    requires
        m > 0,
        base >= 0,
        (base + cnt) * m <= x.len(),
    ensures
        gather(x, m, base, 0, 1, cnt) == x.subrange(base * m, (base + cnt) * m),
{
    let mi = m as int;
    assert((base + cnt) * m - base * m == cnt * m) by (nonlinear_arith);
    assert(base * m >= 0) by (nonlinear_arith)
        requires
            base >= 0,
    ;
    assert forall|q: int| 0 <= q < cnt * m implies gather(x, m, base, 0, 1, cnt)[q] == x.subrange(base * m, (base + cnt) * m)[q] by {
        lemma_split_word(q, mi);
        assert(gidx(m, base, 0, 1, q) == base * mi + q) by (nonlinear_arith)
            requires
                gidx(m, base, 0, 1, q) == (base + 0 + (q / mi) * 1) * mi + q % mi,
                q == (q / mi) * mi + q % mi,
        ;
    }
    assert((base + cnt) * m - base * m == cnt * m) by (nonlinear_arith);
    assert(gather(x, m, base, 0, 1, cnt) =~= x.subrange(base * m, (base + cnt) * m));
}

proof fn lemma_sub_layers_len(tab: Seq<Seq<F64>>, x: Seq<F64>, m: nat, log_d: nat, o: nat, s: int, first: nat, end: nat)
    ensures
        sub_layers(tab, x, m, log_d, o, s, first, end).len() == x.len(),
    decreases end,
{
    if end > first {
        lemma_sub_layers_len(tab, x, m, log_d, o, s, first, (end - 1) as nat);
    }
}

/// Layers `first..end` are layers `first..mid` followed by layers `mid..end`.
pub proof fn lemma_sub_layers_split(tab: Seq<Seq<F64>>, x: Seq<F64>, m: nat, log_d: nat, o: nat, s: int, first: nat, mid: nat, end: nat)
    requires
        first <= mid <= end,
    ensures
        sub_layers(tab, sub_layers(tab, x, m, log_d, o, s, first, mid), m, log_d, o, s, mid, end) == sub_layers(
            tab,
            x,
            m,
            log_d,
            o,
            s,
            first,
            end,
        ),
    decreases end,
{
    if end > mid {
        lemma_sub_layers_split(tab, x, m, log_d, o, s, first, mid, (end - 1) as nat);
    }
}

/// On the whole domain (`o = 0`), the sub-block layers are [`forward_layers`].
pub proof fn lemma_forward_is_sub(tab: Seq<Seq<F64>>, x: Seq<F64>, m: nat, log_d: nat, first: nat, end: nat)
    requires
        m > 0,
        end <= log_d,
    ensures
        forward_layers(tab, x, m, log_d, first, end) == sub_layers(tab, x, m, log_d, 0, 0, first, end),
    decreases end,
{
    if end > first {
        let l = (end - 1) as nat;
        lemma_forward_is_sub(tab, x, m, log_d, first, l);
        lemma_layer_shape(log_d, l, m);
        lemma_layer_map_tw(
            sub_layers(tab, x, m, log_d, 0, 0, first, l),
            m,
            layer_half(log_d, l),
            layer_twiddles(tab, l),
            sub_twiddles(tab, l, 0, 0),
            false,
        );
    }
}

/// The layers of a sub-block, gathered on rows they pair among themselves, are the layers of a smaller
/// domain on the gathered buffer.
///
/// The buffer `x` is sub-block `s` of `2^o` of a `2^log_d`-row domain. The gather takes the rows
/// `base + r + i * 2^(log_d - log_d2)` of sub-block `s2` of `2^o2` of it, `i < 2^(log_d2 - o2)`; on them the
/// layers `first..end` (`o2 <= first`) are those of sub-block `s2` of a `2^log_d2`-row domain.
pub proof fn lemma_gather_sub_layers(
    tab: Seq<Seq<F64>>,
    x: Seq<F64>,
    m: nat,
    log_d: nat,
    o: nat,
    s: int,
    log_d2: nat,
    o2: nat,
    s2: int,
    r: int,
    first: nat,
    end: nat,
)
    requires
        m > 0,
        o <= o2 <= first <= end <= log_d2 <= log_d,
        s >= 0,
        s * pow2((o2 - o) as nat) <= s2 < (s + 1) * pow2((o2 - o) as nat),
        0 <= r < pow2((log_d - log_d2) as nat),
        x.len() == m * pow2((log_d - o) as nat),
    ensures
        ({
            let base = (s2 - s * pow2((o2 - o) as nat)) * pow2((log_d - o2) as nat);
            let step = pow2((log_d - log_d2) as nat) as int;
            let cnt = pow2((log_d2 - o2) as nat);
            gather(sub_layers(tab, x, m, log_d, o, s, first, end), m, base, r, step, cnt) == sub_layers(
                tab,
                gather(x, m, base, r, step, cnt),
                m,
                log_d2,
                o2,
                s2,
                first,
                end,
            )
        }),
    decreases end,
{
    let rb = s2 - s * pow2((o2 - o) as nat);
    let base = rb * pow2((log_d - o2) as nat);
    let step = pow2((log_d - log_d2) as nat) as int;
    let cnt = pow2((log_d2 - o2) as nat);
    if end > first {
        let l = (end - 1) as nat;
        lemma_gather_sub_layers(tab, x, m, log_d, o, s, log_d2, o2, s2, r, first, l);
        let y = sub_layers(tab, x, m, log_d, o, s, first, l);
        lemma_sub_layers_len(tab, x, m, log_d, o, s, first, l);
        let h = layer_half(log_d, l);
        let k = layer_half(log_d2, l);
        // H = k * step, 2k = 2^(log_d2 - l), cnt = 2k * 2^(l - o2), 2H = 2^(log_d - l).
        lemma_pow2_adds((log_d2 - l - 1) as nat, (log_d - log_d2) as nat);
        assert((log_d2 - l - 1) as nat + (log_d - log_d2) as nat == (log_d - l - 1) as nat);
        lemma_pow2_unfold((log_d2 - l) as nat);
        lemma_pow2_unfold((log_d - l) as nat);
        lemma_pow2_adds((log_d2 - l) as nat, (l - o2) as nat);
        assert((log_d2 - l) as nat + (l - o2) as nat == (log_d2 - o2) as nat);
        lemma_pow2_adds((log_d - l) as nat, (l - o2) as nat);
        assert((log_d - l) as nat + (l - o2) as nat == (log_d - o2) as nat);
        lemma_pow2_adds((o2 - o) as nat, (log_d - o2) as nat);
        assert((o2 - o) as nat + (log_d - o2) as nat == (log_d - o) as nat);
        lemma_pow2_adds((o2 - o) as nat, (l - o2) as nat);
        assert((o2 - o) as nat + (l - o2) as nat == (l - o) as nat);
        lemma_pow2_pos((l - o2) as nat);
        lemma_pow2_pos((log_d - l) as nat);
        lemma_pow2_pos((log_d - o2) as nat);
        lemma_pow2_pos((log_d2 - l - 1) as nat);
        lemma_pow2_pos((log_d - log_d2) as nat);
        lemma_pow2_adds((log_d2 - o2) as nat, (log_d - log_d2) as nat);
        assert((log_d2 - o2) as nat + (log_d - log_d2) as nat == (log_d - o2) as nat);
        let p_lo2 = pow2((l - o2) as nat) as int;
        let p2h = pow2((log_d - l) as nat) as int;
        assert(0 <= rb < pow2((o2 - o) as nat)) by (nonlinear_arith)
            requires
                rb == s2 - s * pow2((o2 - o) as nat),
                s * pow2((o2 - o) as nat) <= s2 < (s + 1) * pow2((o2 - o) as nat),
        ;
        assert(base == (rb * p_lo2) * p2h) by (nonlinear_arith)
            requires
                base == rb * pow2((log_d - o2) as nat),
                pow2((log_d - o2) as nat) == p2h * p_lo2,
        ;
        assert(2 * h == p2h);
        lemma_mod_multiples_basic(rb * p_lo2, p2h);
        lemma_div_multiples_vanish(rb * p_lo2, p2h);
        assert(base / (2 * h as int) == rb * p_lo2) by {
            lemma_mul_is_commutative(rb * p_lo2, p2h);
        }
        assert(base % (2 * h as int) == 0) by {
            lemma_mul_is_commutative(rb * p_lo2, p2h);
        }
        assert(cnt as int == (2 * k) * p_lo2);
        lemma_mod_multiples_basic(p_lo2, 2 * k as int);
        assert(cnt % (2 * k) == 0) by {
            lemma_mul_is_commutative(p_lo2, 2 * k as int);
        }
        assert(cnt / (2 * k) == p_lo2) by {
            lemma_div_multiples_vanish(p_lo2, 2 * k as int);
            lemma_mul_is_commutative(p_lo2, 2 * k as int);
        }
        assert((base + cnt * step) * m <= y.len()) by (nonlinear_arith)
            requires
                base == rb * pow2((log_d - o2) as nat),
                cnt * step == pow2((log_d - o2) as nat),
                rb + 1 <= pow2((o2 - o) as nat),
                y.len() == m * pow2((log_d - o) as nat),
                pow2((log_d - o) as nat) == pow2((o2 - o) as nat) * pow2((log_d - o2) as nat),
                m > 0,
        ;
        let tw = sub_twiddles(tab, l, o, s);
        let tw2 = sub_twiddles(tab, l, o2, s2);
        assert forall|b: int| 0 <= b < cnt / (2 * k) implies #[trigger] tw2(b) == tw(base / (2 * h as int) + b) by {
            assert(s * pow2((l - o) as nat) + rb * p_lo2 == s2 * p_lo2) by (nonlinear_arith)
                requires
                    rb == s2 - s * pow2((o2 - o) as nat),
                    pow2((l - o) as nat) == pow2((o2 - o) as nat) * p_lo2,
            ;
        }
        lemma_gather_layer(y, m, h, tw, tw2, false, base, r, step, cnt, k);
    }
}

} // verus!
