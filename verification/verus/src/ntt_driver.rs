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

// ---------------------------------------------------------------------------------------------
// Fused layers on row groups
// ---------------------------------------------------------------------------------------------
/// Rows of `m` words, as one buffer.
pub open spec fn rows_seq(rows: Seq<Seq<F64>>, m: nat) -> Seq<F64> {
    Seq::new(rows.len() * m, |p: int| rows[p / (m as int)][p % (m as int)])
}

/// The rows `b` are one butterfly layer of half `h` on the rows `a`, lane by lane.
pub open spec fn layer_rows(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, h: nat, tw: spec_fn(int) -> u64) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == m && b[i].len() == m
    &&& forall|i: int, lane: int|
        0 <= i < a.len() && 0 <= lane < m ==> if i % (2 * h as int) < h {
            (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + h][lane].0, tw(i / (2 * h as int)))
        } else {
            b[i][lane].0 == bf_bot(a[i - h][lane].0, a[i][lane].0, tw(i / (2 * h as int)))
        }
}

/// Layers L, L+1 and L+2 on a block of `8e` rows: rows `4e`, `2e`, then `e` apart, with the seven
/// twiddles `t` breadth-first.
pub open spec fn layer3(x: Seq<F64>, m: nat, e: nat, t: Seq<F64>) -> Seq<F64> {
    layer_map(
        layer_map(layer_map(x, m, 4 * e, |b: int| t[0].0, false), m, 2 * e, |b: int| t[1 + b].0, false),
        m,
        e,
        |b: int| t[3 + b].0,
        false,
    )
}

/// Layers L and L+1 on a block of `4e` rows: rows `2e` then `e` apart.
pub open spec fn layer2(x: Seq<F64>, m: nat, e: nat, t_outer: u64, t_inner_a: u64, t_inner_b: u64) -> Seq<F64> {
    layer_map(
        layer_map(x, m, 2 * e, |b: int| t_outer, false),
        m,
        e,
        pick2(t_inner_a, t_inner_b),
        false,
    )
}

/// Twiddle `a` for block 0, `b` for block 1.
pub open spec fn pick2(a: u64, b: u64) -> spec_fn(int) -> u64 {
    |x: int|
        if x == 0 {
            a
        } else {
            b
        }
}

/// `gp` holds exactly the permissions of the words `off .. off + m` of each of `n` slabs `stride` words
/// long, of the buffer at `base`.
pub open spec fn holds_group(gp: Map<int, PointsTo<F64>>, base: *mut F64, off: int, stride: int, n: nat, m: nat) -> bool {
    &&& 0 <= off
    &&& off + m <= stride
    &&& base@.addr + n * stride * size_of::<F64>() <= usize::MAX
    &&& n * stride <= usize::MAX
    &&& forall|k: int| #[trigger] gp.dom().contains(k) <==> 0 <= k < n * stride && off <= k % stride < off + m
    &&& forall|k: int| #[trigger] gp.dom().contains(k) ==> gp[k].ptr() == ptr_at(base, k) && gp[k].is_init()
}

/// The words of a group, row by row, as one buffer.
pub open spec fn group_seq(gp: Map<int, PointsTo<F64>>, off: int, stride: int, n: nat, m: nat) -> Seq<F64> {
    Seq::new(n * m, |q: int| gp[off + (q / (m as int)) * stride + q % (m as int)].value())
}

/// What `fused_rows` hands its closure: the permissions of row `off / m` of every slab, with the
/// block's values `x`.
pub open spec fn group_pre(gp: Map<int, PointsTo<F64>>, base: *mut F64, off: int, stride: int, n: nat, m: nat, x: Seq<F64>) -> bool {
    &&& holds_group(gp, base, off, stride, n, m)
    &&& off % (m as int) == 0
    &&& forall|k: int| #[trigger] gp.dom().contains(k) ==> gp[k].value() == x[k]
}

/// What the closure returns: the same permissions, with the values `target`.
pub open spec fn group_post(res: Map<int, PointsTo<F64>>, gp: Map<int, PointsTo<F64>>, target: Seq<F64>) -> bool {
    &&& res.dom() == gp.dom()
    &&& forall|k: int|
        #[trigger] gp.dom().contains(k) ==> res[k].ptr() == gp[k].ptr() && res[k].is_init() && res[k].value() == target[k]
}

/// A layer on rows given lane by lane is the layer on the buffer of the rows.
pub proof fn lemma_rows_layer(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, h: nat, tw: spec_fn(int) -> u64)
    requires
        m > 0,
        h > 0,
        a.len() % (2 * h) == 0,
        layer_rows(a, b, m, h, tw),
    ensures
        layer_map(rows_seq(a, m), m, h, tw, false) == rows_seq(b, m),
{
    let mi = m as int;
    let n = a.len() as int;
    let x = rows_seq(a, m);
    assert forall|p: int| 0 <= p < n * mi implies layer_map(x, m, h, tw, false)[p] == rows_seq(b, m)[p] by {
        lemma_split_word(p, mi);
        lemma_gather_rows(p, mi, n, h as int);
        let i = p / mi;
        assert(row_of(p, m) == i);
        if i % (2 * h as int) < h {
            assert(x[p + h * m] == a[i + h][p % mi]);
        } else {
            assert(x[p - h * m] == a[i - h][p % mi]);
        }
    }
    assert(layer_map(x, m, h, tw, false) =~= rows_seq(b, m));
}

/// The three layers of a block, gathered on one row group, are the three layers of the group.
pub proof fn lemma_gather_layer3(x: Seq<F64>, m: nat, e: nat, t: Seq<F64>, r: int)
    requires
        m > 0,
        e > 0,
        0 <= r < e,
        x.len() == 8 * e * m,
    ensures
        gather(layer3(x, m, e, t), m, 0, r, e as int, 8) == layer3(gather(x, m, 0, r, e as int, 8), m, 1, t),
{
    let t0 = |b: int| t[0].0;
    let t1 = |b: int| t[1 + b].0;
    let t2 = |b: int| t[3 + b].0;
    let x1 = layer_map(x, m, 4 * e, t0, false);
    let x2 = layer_map(x1, m, 2 * e, t1, false);
    let g = gather(x, m, 0, r, e as int, 8);
    assert((0 + 8 * e) * m <= x.len()) by (nonlinear_arith)
        requires
            x.len() == 8 * e * m,
    ;
    assert(8nat % (2 * 4nat) == 0 && 8nat % (2 * 2nat) == 0 && 8nat % (2 * 1nat) == 0) by (compute);
    lemma_gather_layer(x, m, 4 * e, t0, t0, false, 0, r, e as int, 8, 4);
    lemma_gather_layer(x1, m, 2 * e, t1, t1, false, 0, r, e as int, 8, 2);
    lemma_gather_layer(x2, m, e, t2, t2, false, 0, r, e as int, 8, 1);
}

/// The two layers of a block, gathered on one row group, are the two layers of the group.
pub proof fn lemma_gather_layer2(x: Seq<F64>, m: nat, e: nat, t_outer: u64, t_inner_a: u64, t_inner_b: u64, r: int)
    requires
        m > 0,
        e > 0,
        0 <= r < e,
        x.len() == 4 * e * m,
    ensures
        gather(layer2(x, m, e, t_outer, t_inner_a, t_inner_b), m, 0, r, e as int, 4) == layer2(
            gather(x, m, 0, r, e as int, 4),
            m,
            1,
            t_outer,
            t_inner_a,
            t_inner_b,
        ),
{
    let t0 = |b: int| t_outer;
    let t1 = pick2(t_inner_a, t_inner_b);
    let x1 = layer_map(x, m, 2 * e, t0, false);
    assert((0 + 4 * e) * m <= x.len()) by (nonlinear_arith)
        requires
            x.len() == 4 * e * m,
    ;
    assert(4nat % (2 * 2nat) == 0 && 4nat % (2 * 1nat) == 0) by (compute);
    lemma_gather_layer(x, m, 2 * e, t0, t0, false, 0, r, e as int, 4, 2);
    lemma_gather_layer(x1, m, e, t1, t1, false, 0, r, e as int, 4, 1);
}

/// Word `off + i * stride + lane` of a group is word `q = i * m + lane` of its gather.
proof fn lemma_group_word(q: int, m: int, e: int, r: int)
    requires
        m > 0,
        q >= 0,
    ensures
        gidx(m as nat, 0, r, e, q) == r * m + (q / m) * (e * m) + q % m,
{
    assert((0 + r + (q / m) * e) * m == r * m + (q / m) * (e * m)) by (nonlinear_arith);
}

/// The key `k` of a group is `off + i * stride + lane`, word `i * m + lane` of the group's buffer.
proof fn lemma_group_key(k: int, off: int, stride: int, n: nat, m: nat)
    requires
        m > 0,
        0 <= off,
        off + m <= stride,
        0 <= k < n * stride,
        off <= k % stride < off + m,
    ensures
        ({
            let i = k / stride;
            let lane = k % stride - off;
            &&& 0 <= i < n
            &&& 0 <= lane < m
            &&& k == off + i * stride + lane
            &&& 0 <= i * m + lane < n * m
            &&& (i * m + lane) / (m as int) == i
            &&& (i * m + lane) % (m as int) == lane
        }),
{
    let i = k / stride;
    let lane = k % stride - off;
    lemma_split_word(k, stride);
    assert(i < n) by (nonlinear_arith)
        requires
            k == i * stride + k % stride,
            k % stride >= 0,
            k < n * stride,
            stride > 0,
    ;
    lemma_word(i, lane, m as int);
    assert(i * m + lane < n * m) by (nonlinear_arith)
        requires
            i + 1 <= n,
            0 <= lane < m,
    ;
    assert(i * m + lane >= 0) by (nonlinear_arith)
        requires
            i >= 0,
            lane >= 0,
    ;
}

/// A group's buffer is the gather of its rows of the block.
proof fn lemma_group_seq(gp: Map<int, PointsTo<F64>>, base: *mut F64, x: Seq<F64>, off: int, n: nat, m: nat, e: nat)
    requires
        m > 0,
        e > 0,
        off % (m as int) == 0,
        x.len() == n * (e * m),
        group_pre(gp, base, off, (e * m) as int, n, m, x),
    ensures
        group_seq(gp, off, (e * m) as int, n, m) == gather(x, m, 0, off / (m as int), e as int, n),
{
    let mi = m as int;
    let stride = (e * m) as int;
    let r = off / mi;
    lemma_fundamental_div_mod(off, mi);
    assert forall|q: int| 0 <= q < n * m implies group_seq(gp, off, stride, n, m)[q] == gather(x, m, 0, r, e as int, n)[q] by {
        lemma_split_word(q, mi);
        lemma_group_word(q, mi, e as int, r);
        let i = q / mi;
        let lane = q % mi;
        let k = off + i * stride + lane;
        assert(r * mi == off) by {
            lemma_mul_is_commutative(r, mi);
        }
        assert(i < n) by (nonlinear_arith)
            requires
                q == i * mi + lane,
                lane >= 0,
                q < n * mi,
                mi > 0,
        ;
        assert(k >= 0) by (nonlinear_arith)
            requires
                k == off + i * stride + lane,
                off >= 0,
                i >= 0,
                stride > 0,
                lane >= 0,
        ;
        assert(k < n * stride) by (nonlinear_arith)
            requires
                k == off + i * stride + lane,
                i + 1 <= n,
                off + lane < stride,
                stride > 0,
        ;
        lemma_fundamental_div_mod_converse(k, stride, i, off + lane);
        assert(gp.dom().contains(k));
    }
    assert(group_seq(gp, off, stride, n, m) =~= gather(x, m, 0, r, e as int, n));
}

/// Back from a group's buffer to its keys: the group's words are the target's.
proof fn lemma_group_back(gp: Map<int, PointsTo<F64>>, res: Map<int, PointsTo<F64>>, base: *mut F64, target: Seq<F64>, off: int, n: nat, m: nat, e: nat)
    requires
        m > 0,
        e > 0,
        off % (m as int) == 0,
        target.len() == n * (e * m),
        holds_group(gp, base, off, (e * m) as int, n, m),
        res.dom() == gp.dom(),
        group_seq(res, off, (e * m) as int, n, m) == gather(target, m, 0, off / (m as int), e as int, n),
    ensures
        forall|k: int| #[trigger] gp.dom().contains(k) ==> res[k].value() == target[k],
{
    let mi = m as int;
    let stride = (e * m) as int;
    let r = off / mi;
    lemma_fundamental_div_mod(off, mi);
    assert forall|k: int| #[trigger] gp.dom().contains(k) implies res[k].value() == target[k] by {
        lemma_group_key(k, off, stride, n, m);
        let i = k / stride;
        let lane = k % stride - off;
        let q = i * mi + lane;
        lemma_group_word(q, mi, e as int, r);
        assert(r * mi == off) by {
            lemma_mul_is_commutative(r, mi);
        }
        assert(group_seq(res, off, stride, n, m)[q] == res[k].value());
        assert(gather(target, m, 0, r, e as int, n)[q] == target[k]);
    }
}

/// Row `i` of a group: its words are in the group, with their permissions, and end inside the block.
proof fn lemma_row_in_group(g: Map<int, PointsTo<F64>>, base: *mut F64, off: int, stride: int, n: nat, m: nat, i: int)
    requires
        m > 0,
        0 <= i < n,
        holds_group(g, base, off, stride, n, m),
    ensures
        Set::range(i * stride + off, i * stride + off + m) <= g.dom(),
        i * stride + off + m <= n * stride,
        i * stride >= 0,
        base@.addr + (i * stride + off + m) * size_of::<F64>() <= usize::MAX,
        base@.addr + (i * stride + off) * size_of::<F64>() <= usize::MAX,
{
    assert(i * stride + off + m <= n * stride) by (nonlinear_arith)
        requires
            i + 1 <= n,
            off + m <= stride,
            0 <= off,
    ;
    assert(i * stride >= 0) by (nonlinear_arith)
        requires
            i >= 0,
            stride >= 0,
    ;
    lemma_mul_le(i * stride + off + m, n * stride, size_of::<F64>() as int);
    lemma_mul_le(i * stride + off, i * stride + off + m, size_of::<F64>() as int);
    assert forall|k: int| Set::range(i * stride + off, i * stride + off + m).contains(k) implies g.dom().contains(k) by {
        lemma_fundamental_div_mod_converse(k, stride, i, k - i * stride);
    }
}

/// A group's buffer, given row by row.
proof fn lemma_rows_group_seq(g: Map<int, PointsTo<F64>>, off: int, stride: int, n: nat, m: nat, rows: Seq<Seq<F64>>)
    requires
        m > 0,
        rows.len() == n,
        forall|i: int| 0 <= i < n ==> (#[trigger] rows[i]).len() == m,
        forall|i: int, lane: int| 0 <= i < n && 0 <= lane < m ==> (#[trigger] rows[i][lane]) == g[i * stride + off + lane].value(),
    ensures
        group_seq(g, off, stride, n, m) == rows_seq(rows, m),
{
    let mi = m as int;
    assert forall|q: int| 0 <= q < n * m implies group_seq(g, off, stride, n, m)[q] == rows_seq(rows, m)[q] by {
        lemma_split_word(q, mi);
        assert(q / mi < n) by (nonlinear_arith)
            requires
                q == (q / mi) * mi + q % mi,
                q % mi >= 0,
                q < n * mi,
                mi > 0,
        ;
        assert(off + (q / mi) * stride + q % mi == (q / mi) * stride + off + q % mi);
    }
    assert(group_seq(g, off, stride, n, m) =~= rows_seq(rows, m));
}

/// The butterfly of rows `i` and `i + h` of `a`, lane by lane, gives rows `i` and `i + h` of `b`.
pub open spec fn pair_fact(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, i: int, h: int, t: u64) -> bool {
    forall|lane: int|
        0 <= lane < m ==> ((#[trigger] b[i][lane]).0, b[i + h][lane].0) == butterfly_spec(false, a[i][lane].0, a[i + h][lane].0, t)
}

/// Rows of `m` lanes, `n` of them.
pub open spec fn rows_shape(a: Seq<Seq<F64>>, n: nat, m: nat) -> bool {
    a.len() == n && forall|i: int| 0 <= i < n ==> (#[trigger] a[i]).len() == m
}

proof fn lemma_radix8_layer_a(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, tw: spec_fn(int) -> u64)
    requires
        rows_shape(a, 8, m),
        rows_shape(b, 8, m),
        pair_fact(a, b, m, 0, 4, tw(0)),
        pair_fact(a, b, m, 1, 4, tw(0)),
        pair_fact(a, b, m, 2, 4, tw(0)),
        pair_fact(a, b, m, 3, 4, tw(0)),
    ensures
        layer_rows(a, b, m, 4, tw),
{
    assert forall|i: int, lane: int| 0 <= i < 8 && 0 <= lane < m implies if i % (2 * 4nat as int) < 4 {
        (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + 4][lane].0, tw(i / (2 * 4nat as int)))
    } else {
        b[i][lane].0 == bf_bot(a[i - 4][lane].0, a[i][lane].0, tw(i / (2 * 4nat as int)))
    } by {
        if i == 0 {
            assert((b[0][lane].0, b[4][lane].0) == butterfly_spec(false, a[0][lane].0, a[4][lane].0, tw(0)));
        } else if i == 1 {
            assert((b[1][lane].0, b[5][lane].0) == butterfly_spec(false, a[1][lane].0, a[5][lane].0, tw(0)));
        } else if i == 2 {
            assert((b[2][lane].0, b[6][lane].0) == butterfly_spec(false, a[2][lane].0, a[6][lane].0, tw(0)));
        } else if i == 3 {
            assert((b[3][lane].0, b[7][lane].0) == butterfly_spec(false, a[3][lane].0, a[7][lane].0, tw(0)));
        } else if i == 4 {
            assert((b[0][lane].0, b[4][lane].0) == butterfly_spec(false, a[0][lane].0, a[4][lane].0, tw(0)));
        } else if i == 5 {
            assert((b[1][lane].0, b[5][lane].0) == butterfly_spec(false, a[1][lane].0, a[5][lane].0, tw(0)));
        } else if i == 6 {
            assert((b[2][lane].0, b[6][lane].0) == butterfly_spec(false, a[2][lane].0, a[6][lane].0, tw(0)));
        } else {
            assert((b[3][lane].0, b[7][lane].0) == butterfly_spec(false, a[3][lane].0, a[7][lane].0, tw(0)));
        }
    }
}

proof fn lemma_radix8_layer_b(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, tw: spec_fn(int) -> u64)
    requires
        rows_shape(a, 8, m),
        rows_shape(b, 8, m),
        pair_fact(a, b, m, 0, 2, tw(0)),
        pair_fact(a, b, m, 1, 2, tw(0)),
        pair_fact(a, b, m, 4, 2, tw(1)),
        pair_fact(a, b, m, 5, 2, tw(1)),
    ensures
        layer_rows(a, b, m, 2, tw),
{
    assert forall|i: int, lane: int| 0 <= i < 8 && 0 <= lane < m implies if i % (2 * 2nat as int) < 2 {
        (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + 2][lane].0, tw(i / (2 * 2nat as int)))
    } else {
        b[i][lane].0 == bf_bot(a[i - 2][lane].0, a[i][lane].0, tw(i / (2 * 2nat as int)))
    } by {
        if i == 0 {
            assert((b[0][lane].0, b[2][lane].0) == butterfly_spec(false, a[0][lane].0, a[2][lane].0, tw(0)));
        } else if i == 1 {
            assert((b[1][lane].0, b[3][lane].0) == butterfly_spec(false, a[1][lane].0, a[3][lane].0, tw(0)));
        } else if i == 2 {
            assert((b[0][lane].0, b[2][lane].0) == butterfly_spec(false, a[0][lane].0, a[2][lane].0, tw(0)));
        } else if i == 3 {
            assert((b[1][lane].0, b[3][lane].0) == butterfly_spec(false, a[1][lane].0, a[3][lane].0, tw(0)));
        } else if i == 4 {
            assert((b[4][lane].0, b[6][lane].0) == butterfly_spec(false, a[4][lane].0, a[6][lane].0, tw(1)));
        } else if i == 5 {
            assert((b[5][lane].0, b[7][lane].0) == butterfly_spec(false, a[5][lane].0, a[7][lane].0, tw(1)));
        } else if i == 6 {
            assert((b[4][lane].0, b[6][lane].0) == butterfly_spec(false, a[4][lane].0, a[6][lane].0, tw(1)));
        } else {
            assert((b[5][lane].0, b[7][lane].0) == butterfly_spec(false, a[5][lane].0, a[7][lane].0, tw(1)));
        }
    }
}

proof fn lemma_radix8_layer_c(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, tw: spec_fn(int) -> u64)
    requires
        rows_shape(a, 8, m),
        rows_shape(b, 8, m),
        pair_fact(a, b, m, 0, 1, tw(0)),
        pair_fact(a, b, m, 2, 1, tw(1)),
        pair_fact(a, b, m, 4, 1, tw(2)),
        pair_fact(a, b, m, 6, 1, tw(3)),
    ensures
        layer_rows(a, b, m, 1, tw),
{
    assert forall|i: int, lane: int| 0 <= i < 8 && 0 <= lane < m implies if i % (2 * 1nat as int) < 1 {
        (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + 1][lane].0, tw(i / (2 * 1nat as int)))
    } else {
        b[i][lane].0 == bf_bot(a[i - 1][lane].0, a[i][lane].0, tw(i / (2 * 1nat as int)))
    } by {
        if i == 0 {
            assert((b[0][lane].0, b[1][lane].0) == butterfly_spec(false, a[0][lane].0, a[1][lane].0, tw(0)));
        } else if i == 1 {
            assert((b[0][lane].0, b[1][lane].0) == butterfly_spec(false, a[0][lane].0, a[1][lane].0, tw(0)));
        } else if i == 2 {
            assert((b[2][lane].0, b[3][lane].0) == butterfly_spec(false, a[2][lane].0, a[3][lane].0, tw(1)));
        } else if i == 3 {
            assert((b[2][lane].0, b[3][lane].0) == butterfly_spec(false, a[2][lane].0, a[3][lane].0, tw(1)));
        } else if i == 4 {
            assert((b[4][lane].0, b[5][lane].0) == butterfly_spec(false, a[4][lane].0, a[5][lane].0, tw(2)));
        } else if i == 5 {
            assert((b[4][lane].0, b[5][lane].0) == butterfly_spec(false, a[4][lane].0, a[5][lane].0, tw(2)));
        } else if i == 6 {
            assert((b[6][lane].0, b[7][lane].0) == butterfly_spec(false, a[6][lane].0, a[7][lane].0, tw(3)));
        } else {
            assert((b[6][lane].0, b[7][lane].0) == butterfly_spec(false, a[6][lane].0, a[7][lane].0, tw(3)));
        }
    }
}

proof fn lemma_radix4_layer_a(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, tw: spec_fn(int) -> u64)
    requires
        rows_shape(a, 4, m),
        rows_shape(b, 4, m),
        pair_fact(a, b, m, 0, 2, tw(0)),
        pair_fact(a, b, m, 1, 2, tw(0)),
    ensures
        layer_rows(a, b, m, 2, tw),
{
    assert forall|i: int, lane: int| 0 <= i < 4 && 0 <= lane < m implies if i % (2 * 2nat as int) < 2 {
        (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + 2][lane].0, tw(i / (2 * 2nat as int)))
    } else {
        b[i][lane].0 == bf_bot(a[i - 2][lane].0, a[i][lane].0, tw(i / (2 * 2nat as int)))
    } by {
        if i == 0 {
            assert((b[0][lane].0, b[2][lane].0) == butterfly_spec(false, a[0][lane].0, a[2][lane].0, tw(0)));
        } else if i == 1 {
            assert((b[1][lane].0, b[3][lane].0) == butterfly_spec(false, a[1][lane].0, a[3][lane].0, tw(0)));
        } else if i == 2 {
            assert((b[0][lane].0, b[2][lane].0) == butterfly_spec(false, a[0][lane].0, a[2][lane].0, tw(0)));
        } else {
            assert((b[1][lane].0, b[3][lane].0) == butterfly_spec(false, a[1][lane].0, a[3][lane].0, tw(0)));
        }
    }
}

proof fn lemma_radix4_layer_b(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, tw: spec_fn(int) -> u64)
    requires
        rows_shape(a, 4, m),
        rows_shape(b, 4, m),
        pair_fact(a, b, m, 0, 1, tw(0)),
        pair_fact(a, b, m, 2, 1, tw(1)),
    ensures
        layer_rows(a, b, m, 1, tw),
{
    assert forall|i: int, lane: int| 0 <= i < 4 && 0 <= lane < m implies if i % (2 * 1nat as int) < 1 {
        (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + 1][lane].0, tw(i / (2 * 1nat as int)))
    } else {
        b[i][lane].0 == bf_bot(a[i - 1][lane].0, a[i][lane].0, tw(i / (2 * 1nat as int)))
    } by {
        if i == 0 {
            assert((b[0][lane].0, b[1][lane].0) == butterfly_spec(false, a[0][lane].0, a[1][lane].0, tw(0)));
        } else if i == 1 {
            assert((b[0][lane].0, b[1][lane].0) == butterfly_spec(false, a[0][lane].0, a[1][lane].0, tw(0)));
        } else if i == 2 {
            assert((b[2][lane].0, b[3][lane].0) == butterfly_spec(false, a[2][lane].0, a[3][lane].0, tw(1)));
        } else {
            assert((b[2][lane].0, b[3][lane].0) == butterfly_spec(false, a[2][lane].0, a[3][lane].0, tw(1)));
        }
    }
}

/// The union of `rest` with the maps `fs[0..n]`, later ones taking precedence.
pub open spec fn union_all(rest: Map<int, PointsTo<F64>>, fs: Seq<Map<int, PointsTo<F64>>>, n: nat) -> Map<int, PointsTo<F64>>
    decreases n,
{
    if n == 0 {
        rest
    } else {
        union_all(rest, fs, (n - 1) as nat).union_prefer_right(fs[n - 1])
    }
}

/// A key of `fs[i]` that no later map holds keeps its permission in the union.
proof fn lemma_union_all(rest: Map<int, PointsTo<F64>>, fs: Seq<Map<int, PointsTo<F64>>>, n: nat, i: int, k: int)
    requires
        0 <= i < n,
        fs[i].dom().contains(k),
        forall|j: int| i < j < n ==> !(#[trigger] fs[j].dom().contains(k)),
    ensures
        union_all(rest, fs, n).dom().contains(k),
        union_all(rest, fs, n)[k] == fs[i][k],
    decreases n,
{
    if i < n - 1 {
        lemma_union_all(rest, fs, (n - 1) as nat, i, k);
    }
}

/// The domain of the union.
proof fn lemma_union_all_dom(rest: Map<int, PointsTo<F64>>, fs: Seq<Map<int, PointsTo<F64>>>, n: nat, k: int)
    ensures
        union_all(rest, fs, n).dom().contains(k) <==> rest.dom().contains(k) || exists|j: int| 0 <= j < n && #[trigger] fs[j].dom().contains(k),
    decreases n,
{
    if n > 0 {
        lemma_union_all_dom(rest, fs, (n - 1) as nat, k);
        if exists|j: int| 0 <= j < n && #[trigger] fs[j].dom().contains(k) {
            let j = choose|j: int| 0 <= j < n && #[trigger] fs[j].dom().contains(k);
            if j < n - 1 {
                assert(exists|j: int| 0 <= j < n - 1 && #[trigger] fs[j].dom().contains(k));
            }
        }
    }
}

/// Take the permissions of the words `lo .. lo + m` out of a map.
proof fn take_row(tracked gp: &mut Map<int, PointsTo<F64>>, base: *mut F64, lo: int, m: nat) -> (tracked p: Map<int, PointsTo<F64>>)
    requires
        0 <= lo,
        base@.addr + (lo + m) * size_of::<F64>() <= usize::MAX,
        Set::range(lo, lo + m) <= old(gp).dom(),
        forall|k: int| #[trigger] old(gp).dom().contains(k) ==> old(gp)[k].ptr() == ptr_at(base, k) && old(gp)[k].is_init(),
    ensures
        owns(p, base, lo, m as int),
        forall|j: int| 0 <= j < m ==> #[trigger] vals(p, lo, m as int)[j] == old(gp)[lo + j].value(),
        *final(gp) == old(gp).remove_keys(Set::range(lo, lo + m)),
{
    let ghost g = *gp;
    let tracked p = gp.tracked_remove_keys(Set::range(lo, lo + m));
    assert(p.dom() =~= Set::range(lo, lo + m));
    assert forall|k: int| lo <= k < lo + m implies (#[trigger] p[k]).ptr() == ptr_at(base, k) && p[k].is_init() by {
        assert(g.dom().contains(k));
    }
    p
}

/// The rows of a group, taken out row by row, run, and put back: the group's permissions, with the
/// rows' new values.
proof fn lemma_group_rows_back(
    g0: Map<int, PointsTo<F64>>,
    rest: Map<int, PointsTo<F64>>,
    fs: Seq<Map<int, PointsTo<F64>>>,
    base: *mut F64,
    off: int,
    stride: int,
    n: nat,
    m: nat,
    s0: Seq<Seq<F64>>,
    s3: Seq<Seq<F64>>,
)
    requires
        m > 0,
        holds_group(g0, base, off, stride, n, m),
        fs.len() == n,
        rows_shape(s0, n, m),
        rows_shape(s3, n, m),
        forall|k: int| #[trigger] rest.dom().contains(k) ==> g0.dom().contains(k) && rest[k] == g0[k],
        forall|i: int| 0 <= i < n ==> owns(#[trigger] fs[i], base, i * stride + off, m as int) && s3[i] == vals(fs[i], i * stride + off, m as int),
        forall|i: int, lane: int| 0 <= i < n && 0 <= lane < m ==> (#[trigger] s0[i][lane]) == g0[i * stride + off + lane].value(),
    ensures
        union_all(rest, fs, n).dom() == g0.dom(),
        forall|k: int| #[trigger] g0.dom().contains(k) ==> union_all(rest, fs, n)[k].ptr() == g0[k].ptr() && union_all(rest, fs, n)[k].is_init(),
        group_seq(union_all(rest, fs, n), off, stride, n, m) == rows_seq(s3, m),
        group_seq(g0, off, stride, n, m) == rows_seq(s0, m),
{
    let u = union_all(rest, fs, n);
    // A word of row `i` of the group belongs to no other row.
    assert forall|i: int, lane: int| 0 <= i < n && 0 <= lane < m implies #[trigger] u[i * stride + off + lane] == fs[i][i * stride + off + lane]
        && u.dom().contains(i * stride + off + lane) by {
        let k = i * stride + off + lane;
        assert(fs[i].dom().contains(k));
        assert forall|j: int| i < j < n implies !(#[trigger] fs[j].dom().contains(k)) by {
            assert(j * stride >= (i + 1) * stride) by (nonlinear_arith)
                requires
                    j >= i + 1,
                    stride >= 0,
            ;
            assert((i + 1) * stride == i * stride + stride) by (nonlinear_arith);
        }
        lemma_union_all(rest, fs, n, i, k);
    }
    assert forall|k: int| #[trigger] g0.dom().contains(k) implies u.dom().contains(k) by {
        lemma_group_key(k, off, stride, n, m);
        let i = k / stride;
        let lane = k % stride - off;
        assert(u[i * stride + off + lane] == fs[i][i * stride + off + lane]);
        assert(u.dom().contains(i * stride + off + lane));
    }
    assert forall|k: int| #[trigger] u.dom().contains(k) implies g0.dom().contains(k) by {
        lemma_union_all_dom(rest, fs, n, k);
        if !rest.dom().contains(k) {
            let j = choose|j: int| 0 <= j < n && #[trigger] fs[j].dom().contains(k);
            lemma_row_in_group(g0, base, off, stride, n, m, j);
            assert(owns(fs[j], base, j * stride + off, m as int));
            assert(Set::range(j * stride + off, j * stride + off + m).contains(k));
        }
    }
    assert(u.dom() =~= g0.dom());
    assert forall|k: int| #[trigger] g0.dom().contains(k) implies u[k].ptr() == g0[k].ptr() && u[k].is_init() by {
        lemma_group_key(k, off, stride, n, m);
        let i = k / stride;
        let lane = k % stride - off;
        assert(u[i * stride + off + lane] == fs[i][i * stride + off + lane]);
    }
    lemma_rows_group_seq(u, off, stride, n, m, s3);
    lemma_rows_group_seq(g0, off, stride, n, m, s0);
}

/// The twelve butterflies of one radix-8 row group, with its seven twiddles breadth-first.
///
/// Rewritten: the eight rows are eight arguments (production's `rows: &mut [&mut [F64]; 8]` and
/// `let [r0, ..] = rows`); Verus does not support arrays of mutable references. The twelve calls are
/// production's.
fn radix8_butterflies(
    r0: &mut [F64],
    r1: &mut [F64],
    r2: &mut [F64],
    r3: &mut [F64],
    r4: &mut [F64],
    r5: &mut [F64],
    r6: &mut [F64],
    r7: &mut [F64],
    t: &[F64; 7],
)
    requires
        rows_shape(seq![old(r0)@, old(r1)@, old(r2)@, old(r3)@, old(r4)@, old(r5)@, old(r6)@, old(r7)@], 8, old(r0)@.len()),
    ensures
        rows_shape(seq![final(r0)@, final(r1)@, final(r2)@, final(r3)@, final(r4)@, final(r5)@, final(r6)@, final(r7)@], 8, old(r0)@.len()),
        rows_seq(seq![final(r0)@, final(r1)@, final(r2)@, final(r3)@, final(r4)@, final(r5)@, final(r6)@, final(r7)@], old(r0)@.len())
            == layer3(
            rows_seq(seq![old(r0)@, old(r1)@, old(r2)@, old(r3)@, old(r4)@, old(r5)@, old(r6)@, old(r7)@], old(r0)@.len()),
            old(r0)@.len(),
            1,
            t@,
        ),
{
    let ghost m = r0@.len();
    let ghost s0 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    // Layer L: rows 4 apart, one twiddle for the whole block.
    butterfly_lanes(r0, r4, t[0]);
    butterfly_lanes(r1, r5, t[0]);
    butterfly_lanes(r2, r6, t[0]);
    butterfly_lanes(r3, r7, t[0]);
    let ghost s1 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    // Layer L+1: rows 2 apart, one twiddle per half.
    butterfly_lanes(r0, r2, t[1]);
    butterfly_lanes(r1, r3, t[1]);
    butterfly_lanes(r4, r6, t[2]);
    butterfly_lanes(r5, r7, t[2]);
    let ghost s2 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    // Layer L+2: adjacent rows, one twiddle per quarter.
    butterfly_lanes(r0, r1, t[3]);
    butterfly_lanes(r2, r3, t[4]);
    butterfly_lanes(r4, r5, t[5]);
    butterfly_lanes(r6, r7, t[6]);
    let ghost s3 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    proof {
        let tw0 = |b: int| t@[0].0;
        let tw1 = |b: int| t@[1 + b].0;
        let tw2 = |b: int| t@[3 + b].0;
        assert(rows_shape(s1, 8, m) && rows_shape(s2, 8, m) && rows_shape(s3, 8, m));
        lemma_radix8_layer_a(s0, s1, m, tw0);
        lemma_radix8_layer_b(s1, s2, m, tw1);
        lemma_radix8_layer_c(s2, s3, m, tw2);
        if m > 0 {
            assert(8nat % (2 * 4nat) == 0 && 8nat % (2 * 2nat) == 0 && 8nat % (2 * 1nat) == 0) by (compute);
            lemma_rows_layer(s0, s1, m, 4, tw0);
            lemma_rows_layer(s1, s2, m, 2, tw1);
            lemma_rows_layer(s2, s3, m, 1, tw2);
        } else {
            assert(rows_seq(s3, m) =~= layer3(rows_seq(s0, m), m, 1, t@));
        }
    }
}

/// The rows of group `off` of a block of eight slabs, built as `fused_rows` builds them, through the
/// radix-8 butterflies.
///
/// This is production's `fused_rows` loop body for `N = 8` (`std::array::from_fn` of
/// `from_raw_parts_mut(base.add(i * stride + off), num_ntts)`, then `do_one(&mut rows)`), written out per
/// row: Verus has no `from_fn` and no arrays of mutable references.
fn radix8_group(
    base: *mut F64,
    stride: usize,
    off: usize,
    num_ntts: usize,
    gp: Tracked<Map<int, PointsTo<F64>>>,
    t: &[F64; 7],
) -> (res: Tracked<Map<int, PointsTo<F64>>>)
    requires
        num_ntts > 0,
        holds_group(gp@, base, off as int, stride as int, 8, num_ntts as nat),
    ensures
        res@.dom() == gp@.dom(),
        forall|k: int| #[trigger] gp@.dom().contains(k) ==> res@[k].ptr() == gp@[k].ptr() && res@[k].is_init(),
        group_seq(res@, off as int, stride as int, 8, num_ntts as nat) == layer3(
            group_seq(gp@, off as int, stride as int, 8, num_ntts as nat),
            num_ntts as nat,
            1,
            t@,
        ),
{
    let ghost g0 = gp@;
    let ghost m = num_ntts as nat;
    let tracked mut gp = gp.get();
    proof {
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 0);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 1);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 2);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 3);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 4);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 5);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 6);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 7);
    }
    let tracked mut p0 = take_row(&mut gp, base, (0 * stride + off) as int, m);
    let tracked mut p1 = take_row(&mut gp, base, (1 * stride + off) as int, m);
    let tracked mut p2 = take_row(&mut gp, base, (2 * stride + off) as int, m);
    let tracked mut p3 = take_row(&mut gp, base, (3 * stride + off) as int, m);
    let tracked mut p4 = take_row(&mut gp, base, (4 * stride + off) as int, m);
    let tracked mut p5 = take_row(&mut gp, base, (5 * stride + off) as int, m);
    let tracked mut p6 = take_row(&mut gp, base, (6 * stride + off) as int, m);
    let tracked mut p7 = take_row(&mut gp, base, (7 * stride + off) as int, m);
    // SAFETY:
    // - The groups are disjoint, as argued above.
    // - The row ends inside its slab, since the row index is below the slab height.
    let r0 = unsafe { from_raw_parts_mut(base.add(0 * stride + off), num_ntts, Ghost(base), Ghost((0 * stride + off) as int), Tracked(&mut p0)) };
    let r1 = unsafe { from_raw_parts_mut(base.add(1 * stride + off), num_ntts, Ghost(base), Ghost((1 * stride + off) as int), Tracked(&mut p1)) };
    let r2 = unsafe { from_raw_parts_mut(base.add(2 * stride + off), num_ntts, Ghost(base), Ghost((2 * stride + off) as int), Tracked(&mut p2)) };
    let r3 = unsafe { from_raw_parts_mut(base.add(3 * stride + off), num_ntts, Ghost(base), Ghost((3 * stride + off) as int), Tracked(&mut p3)) };
    let r4 = unsafe { from_raw_parts_mut(base.add(4 * stride + off), num_ntts, Ghost(base), Ghost((4 * stride + off) as int), Tracked(&mut p4)) };
    let r5 = unsafe { from_raw_parts_mut(base.add(5 * stride + off), num_ntts, Ghost(base), Ghost((5 * stride + off) as int), Tracked(&mut p5)) };
    let r6 = unsafe { from_raw_parts_mut(base.add(6 * stride + off), num_ntts, Ghost(base), Ghost((6 * stride + off) as int), Tracked(&mut p6)) };
    let r7 = unsafe { from_raw_parts_mut(base.add(7 * stride + off), num_ntts, Ghost(base), Ghost((7 * stride + off) as int), Tracked(&mut p7)) };
    let ghost s0 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    radix8_butterflies(r0, r1, r2, r3, r4, r5, r6, r7, t);
    let ghost s3 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    proof {
        let fs = seq![p0, p1, p2, p3, p4, p5, p6, p7];
        let rest = gp;
        gp.tracked_union_prefer_right(p0);
        gp.tracked_union_prefer_right(p1);
        gp.tracked_union_prefer_right(p2);
        gp.tracked_union_prefer_right(p3);
        gp.tracked_union_prefer_right(p4);
        gp.tracked_union_prefer_right(p5);
        gp.tracked_union_prefer_right(p6);
        gp.tracked_union_prefer_right(p7);
        reveal_with_fuel(union_all, 9);
        assert(gp == union_all(rest, fs, 8));
        assert forall|i: int| 0 <= i < 8 implies owns(#[trigger] fs[i], base, i * stride + off, m as int) && s3[i] == vals(
            fs[i],
            i * stride + off,
            m as int,
        ) by {
            if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {} else {}
        }
        assert forall|i: int, lane: int| 0 <= i < 8 && 0 <= lane < m implies (#[trigger] s0[i][lane]) == g0[i * stride + off + lane].value() by {
            if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {} else {}
        }
        lemma_group_rows_back(g0, rest, fs, base, off as int, stride as int, 8, m, s0, s3);
    }
    Tracked(gp)
}

} // verus!
