//! Each instruction class's function ([`super::semantics`]) as a flock gate list.
//!
//! A circuit's ports are whole 64-bit words, and they are the words its table puts
//! on the bus: the values read from the registers, the bytecode's immediate and
//! flags, the result. A circuit is defined on its class's legal flags only, which
//! are one-hot where they select, so a selection is an XOR of products.

use super::Class;
use flock::circuit::{Builder, Circuit, Wire};

/// A word of wires, low bit first.
type Word = Vec<Wire>;

/// The circuit of `class`'s table.
pub fn of(class: Class) -> Circuit {
    match class {
        Class::Alu => alu(),
        Class::Shift => shift(),
        Class::Load => load(),
        Class::Store => store(),
        Class::Mul => mul(),
        Class::Mulh => mulh(),
        Class::Div => div(),
        Class::Hash => blake2s(),
        Class::Illegal => panic!("no table runs an illegal instruction"),
    }
}

fn xor_words(c: &mut Builder, x: &[Wire], y: &[Wire]) -> Word {
    let mut out = Vec::with_capacity(x.len());
    for i in 0..x.len() {
        out.push(c.xor(x[i], y[i]));
    }
    out
}

/// `s·x`, bit by bit.
fn gate_word(c: &mut Builder, s: Wire, x: &[Wire]) -> Word {
    let mut out = Vec::with_capacity(x.len());
    for i in 0..x.len() {
        out.push(c.and(s, x[i]));
    }
    out
}

/// Whether any bit of `x` is set.
fn any(c: &mut Builder, x: &[Wire]) -> Wire {
    let mut acc = None;
    for i in 0..x.len() {
        acc = c.or(acc, x[i]);
    }
    acc
}

/// `x + y + carry_in`, and the carry out of the top bit.
fn add_with_carry(c: &mut Builder, x: &[Wire], y: &[Wire], carry_in: Wire) -> (Word, Wire) {
    let mut carry = carry_in;
    let mut sum = Vec::with_capacity(x.len());
    for i in 0..x.len() {
        let xc = c.xor(x[i], carry);
        let yc = c.xor(y[i], carry);
        sum.push(c.xor(xc, y[i]));
        let maj = c.and(xc, yc);
        carry = c.xor(maj, carry);
    }
    (sum, carry)
}

/// `x`, its bits from 32 up replaced by bit 31 when `word` is set.
fn sext32_if(c: &mut Builder, word: Wire, x: &[Wire]) -> Word {
    extend32_if(c, word, x[31], x)
}

/// `x`, its bits from 32 up replaced by `fill` when `word` is set.
fn extend32_if(c: &mut Builder, word: Wire, fill: Wire, x: &[Wire]) -> Word {
    let mut out = Vec::with_capacity(64);
    for i in 0..64 {
        out.push(if i < 32 { x[i] } else { c.mux(word, fill, x[i]) });
    }
    out
}

/// `x + y` over `x.len()` bits, the carry out of the top bit dropped: one product
/// per bit but the top, the carry into bit `i + 1` being `maj(x_i, y_i, c_i)`.
fn add(c: &mut Builder, x: &[Wire], y: &[Wire]) -> Word {
    let (mut carry, width) = (None, x.len());
    let mut sum = Vec::with_capacity(width);
    for i in 0..width {
        let xc = c.xor(x[i], carry);
        let yc = c.xor(y[i], carry);
        sum.push(c.xor(xc, y[i]));
        // The carry out of the top bit falls off the modulus, so it is never a product.
        if i + 1 < width {
            let maj = c.and(xc, yc);
            carry = c.xor(maj, carry);
        }
    }
    sum
}

/// `x` shifted by `8·amount` bits, `amount` being three bits: left, or right.
fn shift_bytes(c: &mut Builder, x: &[Wire], amount: &[Wire], left: bool) -> Word {
    let mut x = x.to_vec();
    for stage in 0..amount.len() {
        let by = 8 << stage;
        let mut shifted = Vec::with_capacity(64);
        for i in 0..64 {
            let from = if left {
                if i >= by { x[i - by] } else { None }
            } else if i + by < 64 {
                x[i + by]
            } else {
                None
            };
            shifted.push(c.mux(amount[stage], from, x[i]));
        }
        x = shifted;
    }
    x
}

/// The width thresholds of a load or a store, from the two bits of `log2` of its
/// width in bytes: at least 2, at least 4, exactly 8.
fn width_thresholds(c: &mut Builder, log_width: &[Wire]) -> [Wire; 3] {
    let ge2 = c.or(log_width[0], log_width[1]);
    let eq8 = c.and(log_width[0], log_width[1]);
    [ge2, log_width[1], eq8]
}

/// [`super::semantics::bus_address`]: the low three bits are the ones misaligning the access.
fn bus_address(c: &mut Builder, address: &[Wire], thresholds: [Wire; 3]) -> Word {
    let mut bus = Vec::with_capacity(64);
    for i in 0..64 {
        bus.push(if i < 3 {
            c.and(address[i], thresholds[i])
        } else {
            address[i]
        });
    }
    bus
}

/// Commits `word` as output port `port`.
fn output_word(c: &mut Builder, port: usize, word: &[Wire]) {
    for i in 0..word.len() {
        c.output(port, i, word[i]);
    }
}

/// [`super::Class::Load`]'s circuit: `(v1, imm, flags, cell) -> (address, out)`, the
/// address being what goes on the memory bus and `cell` the word read there.
pub fn load() -> Circuit {
    let mut c = Builder::new(&[64, 64, 3, 64], &[64, 64]);
    let (v1, imm, flags, cell) = (c.input(0), c.input(1), c.input(2), c.input(3));
    let address = add(&mut c, &v1, &imm);
    let [ge2, ge4, eq8] = width_thresholds(&mut c, &flags[..2]);
    let bus = bus_address(&mut c, &address, [ge2, ge4, eq8]);
    let value = shift_bytes(&mut c, &cell, &address[..3], false);
    // The extension: the value's top bit, which the width places, if the load is signed.
    let (w1, w2, w4) = (c.not(ge2), c.xor(ge2, ge4), c.xor(ge4, eq8));
    let widths = [(w1, 7), (w2, 15), (w4, 31)];
    let mut sign = None;
    for k in 0..widths.len() {
        let (width, bit) = widths[k];
        let term = c.and(width, value[bit]);
        sign = c.xor(sign, term);
    }
    let extension = c.and(flags[2], sign);
    output_word(&mut c, 0, &bus);
    for i in 0..64 {
        let wire = match i {
            0..8 => value[i],
            8..16 => c.mux(ge2, value[i], extension),
            16..32 => c.mux(ge4, value[i], extension),
            _ => c.mux(eq8, value[i], extension),
        };
        c.output(1, i, wire);
    }
    c.finish()
}

/// [`super::Class::Store`]'s circuit: `(v1, v2, imm, flags, cell) -> (address, new cell,
/// out)`. `out` is what the row writes to its destination, the sink: zero.
pub fn store() -> Circuit {
    let mut c = Builder::new(&[64, 64, 64, 2, 64], &[64, 64, 64]);
    let (v1, v2, imm, flags, cell) = (c.input(0), c.input(1), c.input(2), c.input(3), c.input(4));
    let address = add(&mut c, &v1, &imm);
    let thresholds = width_thresholds(&mut c, &flags);
    let bus = bus_address(&mut c, &address, thresholds);
    let value = shift_bytes(&mut c, &v2, &address[..3], true);
    // Byte `j` is written when it shares the access's block: bit `k` of `j` equals bit
    // `k` of the address wherever the width does not already span both.
    let mut spans = [[None; 2]; 3];
    for k in 0..3 {
        let is_zero = c.not(address[k]);
        spans[k] = [c.or(is_zero, thresholds[k]), c.or(address[k], thresholds[k])];
    }
    output_word(&mut c, 0, &bus);
    for j in 0..8 {
        let low = c.and(spans[0][j & 1], spans[1][(j >> 1) & 1]);
        let written = c.and(low, spans[2][j >> 2]);
        for i in 8 * j..8 * j + 8 {
            let wire = c.mux(written, value[i], cell[i]);
            c.output(1, i, wire);
        }
    }
    c.finish()
}

/// The wire of flag `bit` among the flags port's wires `f`.
fn flag(f: &[Wire], bit: u64) -> Wire {
    f[bit.trailing_zeros() as usize]
}

/// `x` reversed unless `right`.
fn reverse_unless(c: &mut Builder, right: Wire, x: &[Wire]) -> Word {
    let mut out = Vec::with_capacity(64);
    for i in 0..64 {
        out.push(c.mux(right, x[i], x[63 - i]));
    }
    out
}

/// [`super::semantics::shift`]: `(v1, v2, imm, flags) -> out`. One right shifter serves
/// both directions, a left shift being a right shift of the reversed word.
pub fn shift() -> Circuit {
    let mut c = Builder::new(&[64, 64, 64, 3], &[64]);
    let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
    use super::shift::*;
    let (right, arith, word) = (flag(&f, RIGHT), flag(&f, ARITH), flag(&f, WORD));

    // The amount: six bits, five for a word shift.
    let mut amount = xor_words(&mut c, &v2[..6], &imm[..6]);
    let not_word = c.not(word);
    amount[5] = c.and(not_word, amount[5]);
    // A word shift takes the low 32 bits, extended as the shift is: by the sign for an
    // arithmetic one, by zero otherwise.
    let low_sign = c.and(arith, v1[31]);
    let x = extend32_if(&mut c, word, low_sign, &v1);
    // What a right shift brings in from the top. `ARITH` comes with `RIGHT`.
    let fill = c.and(arith, x[63]);

    let mut y = reverse_unless(&mut c, right, &x);
    for stage in 0..amount.len() {
        let by = 1 << stage;
        let mut shifted = Vec::with_capacity(64);
        for i in 0..64 {
            shifted.push(c.mux(amount[stage], if i + by < 64 { y[i + by] } else { fill }, y[i]));
        }
        y = shifted;
    }
    let y = reverse_unless(&mut c, right, &y);
    let out = sext32_if(&mut c, word, &y);
    output_word(&mut c, 0, &out);
    c.finish()
}

/// [`super::semantics::mul`]: `(v1, v2, flags) -> out`, the low word of the product.
pub fn mul() -> Circuit {
    let mut c = Builder::new(&[64, 64, 1], &[64]);
    let (v1, v2, f) = (c.input(0), c.input(1), c.input(2));
    let (product, _) = flock::arith::mul::Multiplier::build(&mut c, &v1, &v2, 64);
    let out = sext32_if(&mut c, f[0], &product);
    output_word(&mut c, 0, &out);
    c.finish()
}

/// `high - other` if `signed` and `operand` is negative, `high + !other + 1`.
fn less_if_negative(c: &mut Builder, high: &[Wire], signed: Wire, operand: &[Wire], other: &[Wire]) -> Word {
    let negative = c.and(signed, operand[63]);
    let mut subtrahend = Vec::with_capacity(other.len());
    for i in 0..other.len() {
        let inverted = c.not(other[i]);
        subtrahend.push(c.and(negative, inverted));
    }
    add_with_carry(c, high, &subtrahend, negative).0
}

/// [`super::semantics::mulh`]: `(v1, v2, flags) -> out`, the high word of the product.
/// The unsigned product's high word, less `v2` if `v1` is signed and negative, less `v1`
/// if `v2` is: a negative operand is its unsigned reading minus `2^64`.
pub fn mulh() -> Circuit {
    let mut c = Builder::new(&[64, 64, 2], &[64]);
    let (v1, v2, f) = (c.input(0), c.input(1), c.input(2));
    let (product, _) = flock::arith::mul::Multiplier::build(&mut c, &v1, &v2, 128);
    let high = less_if_negative(&mut c, &product[64..], f[0], &v1, &v2);
    let high = less_if_negative(&mut c, &high, f[1], &v2, &v1);
    output_word(&mut c, 0, &high);
    c.finish()
}

/// `x` negated if `negative`: `(x ^ negative) + negative`.
fn negate_if(c: &mut Builder, negative: Wire, x: &[Wire]) -> Word {
    let mut flipped = Vec::with_capacity(x.len());
    for i in 0..x.len() {
        flipped.push(c.xor(x[i], negative));
    }
    add_with_carry(c, &flipped, &[None; 64], negative).0
}

/// [`super::semantics::div`]: `(v1, v2, flags, q, r) -> (out, bad)`. The quotient's and
/// the remainder's magnitudes `q` and `r` are the prover's ([`super::semantics::div_hints`]),
/// and `bad` is set unless they are the ones: `|n| = q·|d| + r` over the integers (the
/// product's high word zero, the sum without a carry) and `r < |d|`. A row puts `bad`
/// where its bytecode entry holds zero, so it is zero. Dividing by zero checks nothing
/// and returns what the specification says, all ones or the dividend, and the one
/// overflow, `-2^63 / -1`, is no special case on magnitudes.
pub fn div() -> Circuit {
    let mut c = Builder::new(&[64, 64, 3, 64, 64], &[64, 1]);
    let (v1, v2, f, q, r) = (c.input(0), c.input(1), c.input(2), c.input(3), c.input(4));
    let (signed, rem, word) = (f[0], f[1], f[2]);
    // A word form divides the low 32 bits, extended as the division is signed or not.
    let n_sign = c.and(signed, v1[31]);
    let n = extend32_if(&mut c, word, n_sign, &v1);
    let d_sign = c.and(signed, v2[31]);
    let d = extend32_if(&mut c, word, d_sign, &v2);
    let (n_negative, d_negative) = (c.and(signed, n[63]), c.and(signed, d[63]));
    let (n_abs, d_abs) = (negate_if(&mut c, n_negative, &n), negate_if(&mut c, d_negative, &d));

    let (product, _) = flock::arith::mul::Multiplier::build(&mut c, &q, &d_abs, 128);
    let overflows = any(&mut c, &product[64..]);
    let (sum, carries) = add_with_carry(&mut c, &product[..64], &r, None);
    let difference = xor_words(&mut c, &sum, &n_abs);
    let differs = any(&mut c, &difference);
    // `r - |d|` does not borrow, which is `r + !|d| + 1` carrying out, when `r >= |d|`.
    let mut d_inverted = Vec::with_capacity(64);
    for i in 0..64 {
        d_inverted.push(c.not(d_abs[i]));
    }
    let one = c.one();
    let (_, too_large) = add_with_carry(&mut c, &r, &d_inverted, one);
    let d_nonzero = any(&mut c, &d);
    let wrong = c.or(overflows, carries);
    let wrong = c.or(wrong, differs);
    let wrong = c.or(wrong, too_large);
    let bad = c.and(d_nonzero, wrong);

    // The quotient is negative when the operands' signs differ, the remainder when
    // the dividend is.
    let q_negative = c.xor(n_negative, d_negative);
    let (q_signed, r_signed) = (negate_if(&mut c, q_negative, &q), negate_if(&mut c, n_negative, &r));
    let mut out = Vec::with_capacity(64);
    for i in 0..64 {
        let result = c.mux(rem, r_signed[i], q_signed[i]);
        let by_zero = c.mux(rem, n[i], one);
        out.push(c.mux(d_nonzero, result, by_zero));
    }
    let out = sext32_if(&mut c, word, &out);
    output_word(&mut c, 0, &out);
    c.output(1, 0, bad);
    c.finish()
}

/// [`super::Class::Alu`]'s ports.
pub mod alu_ports {
    /// Input words: the two register values, the immediate, the flags.
    pub const V1: usize = 0;
    pub const V2: usize = 1;
    pub const IMM: usize = 2;
    pub const FLAGS: usize = 3;
    /// Output words.
    pub const OUT: usize = 4;
    pub const TAKEN: usize = 5;
}

/// [`super::semantics::alu`].
pub fn alu() -> Circuit {
    let mut c = Builder::new(&[64, 64, 64, 15], &[64, 1]);
    let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
    use super::alu::*;

    let b = xor_words(&mut c, &v2, &imm);
    // `v1 - b` is `v1 + !b + 1`, and it borrows exactly when that does not carry out.
    let sub = flag(&f, SUB);
    let mut b_or_not = Vec::with_capacity(64);
    for i in 0..64 {
        b_or_not.push(c.xor(b[i], sub));
    }
    let (sum, carry_out) = add_with_carry(&mut c, &v1, &b_or_not, sub);
    let ltu = c.not(carry_out);
    let signs = c.xor(v1[63], b[63]);
    let lt = c.xor(ltu, signs);
    let diff = xor_words(&mut c, &v1, &b);
    let ne = any(&mut c, &diff);
    let eq = c.not(ne);

    // `out`: the sum unless a selector is set. AND is a product, OR is AND plus XOR.
    let sum = sext32_if(&mut c, flag(&f, WORD), &sum);
    let selectors = [SEL_LT, SEL_LTU, SEL_AND, SEL_OR, SEL_XOR];
    let mut none = c.one();
    for k in 0..selectors.len() {
        none = c.xor(none, flag(&f, selectors[k]));
    }
    let and_or = c.xor(flag(&f, SEL_AND), flag(&f, SEL_OR));
    let or_xor = c.xor(flag(&f, SEL_OR), flag(&f, SEL_XOR));
    let mut out = gate_word(&mut c, none, &sum);
    for i in 0..64 {
        let both = c.and(v1[i], b[i]);
        let and_term = c.and(and_or, both);
        let xor_term = c.and(or_xor, diff[i]);
        let logic = c.xor(and_term, xor_term);
        out[i] = c.xor(out[i], logic);
    }
    let lt_term = c.and(flag(&f, SEL_LT), lt);
    let ltu_term = c.and(flag(&f, SEL_LTU), ltu);
    let compared = c.xor(lt_term, ltu_term);
    out[0] = c.xor(out[0], compared);
    let keep_bit0 = c.not(flag(&f, CLEAR_BIT0));
    out[0] = c.and(keep_bit0, out[0]);

    let (ge, geu) = (c.not(lt), c.not(ltu));
    let branches = [
        (BR_EQ, eq),
        (BR_NE, ne),
        (BR_LT, lt),
        (BR_GE, ge),
        (BR_LTU, ltu),
        (BR_GEU, geu),
    ];
    let mut taken = flag(&f, ALWAYS);
    for k in 0..branches.len() {
        let (when, holds) = branches[k];
        let term = c.and(flag(&f, when), holds);
        taken = c.xor(taken, term);
    }

    output_word(&mut c, 0, &out);
    c.output(1, 0, taken);
    c.finish()
}

/// The hash circuit's input ports in bits: `t`, `f0`, then the four words of `h` and the eight of `m`.
const HASH_INPUT_BITS: [usize; 14] = [64, 32, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64];

/// Where one 32-bit addition of the hash circuit put its carry products.
#[derive(Clone, Copy)]
struct Carries {
    /// The slot of the first product.
    slot: u32,
    /// The lowest bit with a product.
    ///
    /// Bits below it are structural zeros: a literal operand's low zero bits, with no carry yet.
    low: u32,
}

/// [`super::Class::Hash`]'s circuit: `(t, f0, h, m) -> out`, the BLAKE2s compression
/// ([`super::semantics::blake2s`]) on the 32-bit halves of the block's words, `h`
/// and `out` four words each and `m` eight. Every G is six 32-bit additions, its
/// two three-operand ones chained, and the state is never materialized: only the
/// carries are products, and the result's words are copied out.
pub fn blake2s() -> Circuit {
    blake2s_with_carries().0
}

/// The 32-bit half `i % 2` of input port `port`.
fn half(c: &Builder, port: usize, i: usize) -> Word {
    c.input(port)[32 * (i % 2)..32 * (i % 2) + 32].to_vec()
}

/// The 32-bit constant `x`.
fn literal(c: &Builder, x: u32) -> Word {
    let mut word = Vec::with_capacity(32);
    for i in 0..32 {
        word.push(if x >> i & 1 == 1 { c.one() } else { None });
    }
    word
}

/// `w` rotated right by `r` bits.
fn rotr(w: &[Wire], r: usize) -> Word {
    let mut word = Vec::with_capacity(32);
    for i in 0..32 {
        word.push(w[(i + r) % 32]);
    }
    word
}

/// A 32-bit addition of the hash circuit, its carry slots recorded.
///
/// An addition's products are its top bits, from the first bit where both operands exist.
/// Why: once one product is made, the carry is a wire, so every later bit has one too.
fn add32(c: &mut Builder, carries: &mut Vec<Carries>, x: &[Wire], y: &[Wire]) -> Word {
    let slot = c.next_slot();
    let sum = add(c, x, y);
    let products = (c.next_slot() - slot) as u32;
    carries.push(Carries {
        slot: slot as u32,
        low: 31 - products,
    });
    sum
}

/// Half of G on lanes `a, b, cc, d` of the working vector `v`: message word `x`, then
/// the rotations `r1` and `r2`.
#[allow(clippy::too_many_arguments)]
fn g_half(
    c: &mut Builder,
    carries: &mut Vec<Carries>,
    v: &mut [Word],
    lanes: [usize; 4],
    x: &[Wire],
    r1: usize,
    r2: usize,
) {
    let [a, b, cc, d] = lanes;
    let ab = add32(c, carries, &v[a], &v[b]);
    v[a] = add32(c, carries, &ab, x);
    let da = xor_words(c, &v[d], &v[a]);
    v[d] = rotr(&da, r1);
    v[cc] = add32(c, carries, &v[cc], &v[d]);
    let bc = xor_words(c, &v[b], &v[cc]);
    v[b] = rotr(&bc, r2);
}

/// The hash circuit, and its additions' carry slots in the order it made them.
fn blake2s_with_carries() -> (Circuit, Vec<Carries>) {
    use primitives::hash::{G_LANES, IV, SIGMA};
    let mut c = Builder::new(&HASH_INPUT_BITS, &[64, 64, 64, 64]);
    let (t, f0) = (c.input(0), c.input(1));
    let mut h = Vec::with_capacity(8);
    for i in 0..8 {
        h.push(half(&c, 2 + i / 2, i));
    }
    let mut m = Vec::with_capacity(16);
    for i in 0..16 {
        m.push(half(&c, 6 + i / 2, i));
    }

    let mut carries = Vec::with_capacity(SIGMA.len() * 8 * 6);
    let mut v = h.clone();
    for i in 0..4 {
        v.push(literal(&c, IV[i]));
    }
    let tweak = [t[..32].to_vec(), t[32..].to_vec(), f0, vec![None; 32]];
    for i in 0..4 {
        let iv = literal(&c, IV[4 + i]);
        v.push(xor_words(&mut c, &iv, &tweak[i]));
    }
    for round in 0..SIGMA.len() {
        let s = SIGMA[round];
        for g in 0..G_LANES.len() {
            g_half(&mut c, &mut carries, &mut v, G_LANES[g], &m[s[2 * g]], 16, 12);
            g_half(&mut c, &mut carries, &mut v, G_LANES[g], &m[s[2 * g + 1]], 8, 7);
        }
    }
    for i in 0..8 {
        let hv = xor_words(&mut c, &h[i], &v[i]);
        let out = xor_words(&mut c, &hv, &v[i + 8]);
        for bit in 0..32 {
            c.output(i / 2, 32 * (i % 2) + bit, out[bit]);
        }
    }
    (c.finish(), carries)
}

/// One instance of the hash circuit's witness, by word arithmetic instead of the gate walk.
///
/// Writes the same `z`, `A·z` and `B·z` the walk does, into zeroed buffers.
///
/// ```text
///     words 0..14     inputs     z = A·z = the word,  B·z = its wired bits
///     words 14..18    outputs    z = A·z = the word,  B·z = all ones
///     bit 1152        constant   z = A·z = B·z = 1
///     bits 1153..     products   one run of carries per 32-bit addition
/// ```
///
/// An addition `x + y` with carries `c = (x + y) ^ x ^ y` has, at each bit `i` of its run:
///
/// ```text
///     A·z = x_i ^ c_i    B·z = y_i ^ c_i    z = (x_i ^ c_i)(y_i ^ c_i)
/// ```
pub fn blake2s_witness(inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
    use primitives::hash::{G_LANES, IV, SIGMA};
    assert_eq!(inputs.len(), HASH_INPUT_BITS.len());

    // The carry runs, recorded once from the gate list itself.
    static CARRIES: std::sync::OnceLock<Vec<Carries>> = std::sync::OnceLock::new();
    let carries = CARRIES.get_or_init(|| blake2s_with_carries().1);

    // Input ports: the word, masked to the port's width.
    for (i, &bits) in HASH_INPUT_BITS.iter().enumerate() {
        let wired = u64::MAX >> (64 - bits);
        (z[i], az[i], bz[i]) = (inputs[i] & wired, inputs[i] & wired, wired);
    }

    // The working vector, as the circuit starts it.
    let half = |w: u64, i: usize| (w >> (32 * (i % 2))) as u32;
    let h: [u32; 8] = std::array::from_fn(|i| half(inputs[2 + i / 2], i));
    let m: [u32; 16] = std::array::from_fn(|i| half(inputs[6 + i / 2], i));
    let (t, f0) = (inputs[0], inputs[1] as u32);
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(&h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    v[14] ^= f0;

    // Each addition writes its run of carries, in the order the circuit made them.
    let mut runs = carries.iter();
    let mut add = |x: u32, y: u32| -> u32 {
        let Carries { slot, low } = *runs.next().expect("one run per addition");
        let sum = x.wrapping_add(y);
        let carry = sum ^ x ^ y;
        // The run covers bits `low..31`: the carry out of bit 31 is no product.
        let mask = (1u64 << (31 - low)) - 1;
        let left = u64::from(x ^ carry) >> low & mask;
        let right = u64::from(y ^ carry) >> low & mask;
        or_run(z, slot, left & right);
        or_run(az, slot, left);
        or_run(bz, slot, right);
        sum
    };

    // Ten rounds of eight G's, the working vector updated as the circuit updates it.
    for round in &SIGMA {
        for (g, &[a, b, c, d]) in G_LANES.iter().enumerate() {
            for (x, r1, r2) in [(m[round[2 * g]], 16, 12), (m[round[2 * g + 1]], 8, 7)] {
                let ab = add(v[a], v[b]);
                v[a] = add(ab, x);
                v[d] = (v[d] ^ v[a]).rotate_right(r1);
                v[c] = add(v[c], v[d]);
                v[b] = (v[b] ^ v[c]).rotate_right(r2);
            }
        }
    }

    // Output ports: the new chaining value, every bit copied out.
    let n_in = HASH_INPUT_BITS.len();
    for i in 0..4 {
        let word = |j: usize| u64::from(h[j] ^ v[j] ^ v[j + 8]);
        let out = word(2 * i) | word(2 * i + 1) << 32;
        (z[n_in + i], az[n_in + i], bz[n_in + i]) = (out, out, u64::MAX);
    }

    // The constant wire, right after the ports.
    let one = 64 * (n_in + 4);
    for buf in [z, az, bz] {
        buf[one / 64] |= 1 << (one % 64);
    }
}

/// OR a run of at most 32 bits into `buf` from bit `slot`.
#[inline(always)]
fn or_run(buf: &mut [u64], slot: u32, bits: u64) {
    let (word, shift) = (slot as usize / 64, slot % 64);
    buf[word] |= bits << shift;
    // `(x >> 1) >> (63 - s)` is `x >> (64 - s)`, with no overflowing shift at `s = 0`.
    buf[word + 1] |= (bits >> 1) >> (63 - shift);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics;
    use crate::transcript::{ProverState, VerifierState};

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn word(&mut self) -> u64 {
            match self.next() % 6 {
                0 => [
                    0,
                    1,
                    u64::MAX,
                    1 << 63,
                    (1 << 63) - 1,
                    1 << 31,
                    0xffff_ffff,
                    (1 << 31) - 1,
                ][(self.next() % 8) as usize],
                1 => self.next() as i32 as i64 as u64,
                _ => self.next(),
            }
        }
    }

    /// The circuit's output words on `inputs`, read off the witness it generates.
    fn run(circuit: &Circuit, inputs: &[u64], outputs: std::ops::Range<usize>) -> Vec<u64> {
        let words = 1 << (circuit.k_log() - 6);
        let (mut z, mut az, mut bz) = (vec![0; words], vec![0; words], vec![0; words]);
        circuit.witness_instance(inputs, &mut z, &mut az, &mut bz);
        z[outputs].to_vec()
    }

    #[test]
    fn alu_is_its_reference() {
        let circuit = alu();
        assert_eq!(circuit.k_log(), 10, "an ALU instance is 16 packed words");
        let mut rng = Rng(0xA1);
        for &flags in &crate::rv::alu::LEGAL {
            for round in 0..400 {
                let v1 = rng.word();
                // Equal operands now and then, which random words never are.
                let v2 = if round % 7 == 0 { v1 } else { rng.word() };
                // One of `v2` and `imm` is zero, as the decoder has it.
                let (v2, imm) = if round % 2 == 0 { (v2, 0) } else { (0, v2) };
                let (out, taken) = semantics::alu(v1, v2, imm, flags);
                assert_eq!(
                    run(&circuit, &[v1, v2, imm, flags], alu_ports::OUT..alu_ports::TAKEN + 1),
                    [out, taken as u64],
                    "flags {flags:#x} on {v1:#x}, {v2:#x}, {imm:#x}"
                );
            }
        }
    }

    #[test]
    fn load_and_store_are_their_references() {
        let (load, store) = (load(), store());
        assert_eq!(
            (load.k_log(), store.k_log()),
            (10, 10),
            "an instance is 16 packed words"
        );
        let mut rng = Rng(0xA3);
        for round in 0..4000 {
            let (v1, imm, v2, cell) = (rng.word(), rng.next() % 4096, rng.word(), rng.next());
            let address = semantics::address(v1, imm);
            for &flags in &crate::rv::load::LEGAL {
                let log_width = flags & crate::rv::load::LOG_WIDTH;
                // Aligned every other round, which a random address seldom is.
                let v1 = if round % 2 == 0 {
                    v1 & !((1 << log_width) - 1)
                } else {
                    v1
                };
                let imm = if round % 2 == 0 { imm & !7 } else { imm };
                let address = if round % 2 == 0 {
                    semantics::address(v1, imm)
                } else {
                    address
                };
                assert_eq!(
                    run(&load, &[v1, imm, flags, cell], 4..6),
                    [
                        semantics::bus_address(address, log_width),
                        semantics::load(cell, address, flags)
                    ],
                    "load {flags:#x} at {address:#x} of {cell:#x}"
                );
            }
            for &flags in &crate::rv::store::LEGAL {
                let got = run(&store, &[v1, v2, imm, flags, cell], 5..8);
                assert_eq!(
                    got[0],
                    semantics::bus_address(address, flags),
                    "store {flags:#x} at {address:#x}"
                );
                assert_eq!(got[2], 0);
                // A misaligned store names no cell, so what it would write is nobody's business.
                if semantics::is_aligned(address, flags) {
                    assert_eq!(
                        got[1],
                        semantics::store(cell, address, v2, flags),
                        "store {flags:#x} at {address:#x}"
                    );
                }
            }
        }
    }

    #[test]
    fn shift_and_multiplications_are_their_references() {
        let (shift, mul, mulh) = (shift(), mul(), mulh());
        assert_eq!((shift.k_log(), mul.k_log(), mulh.k_log()), (10, 12, 13));
        let mut rng = Rng(0xA4);
        for round in 0..1500 {
            let (v1, v2) = (rng.word(), rng.word());
            for &flags in &crate::rv::shift::LEGAL {
                // Every amount now and then, which a random word's low bits cover slowly.
                let amount = if round % 3 == 0 { round as u64 % 64 } else { v2 };
                let (v2, imm) = if round % 2 == 0 { (amount, 0) } else { (0, amount & 63) };
                assert_eq!(
                    run(&shift, &[v1, v2, imm, flags], 4..5),
                    [semantics::shift(v1, v2, imm, flags)],
                    "shift {flags:#x} of {v1:#x} by {v2:#x}, {imm:#x}"
                );
            }
            if round % 10 == 0 {
                for &flags in &crate::rv::mul::LEGAL {
                    assert_eq!(
                        run(&mul, &[v1, v2, flags], 3..4),
                        [semantics::mul(v1, v2, flags)],
                        "mul {flags:#x}"
                    );
                }
                for &flags in &crate::rv::mulh::LEGAL {
                    assert_eq!(
                        run(&mulh, &[v1, v2, flags], 3..4),
                        [semantics::mulh(v1, v2, flags)],
                        "mulh {flags:#x} of {v1:#x}, {v2:#x}"
                    );
                }
            }
        }
    }

    #[test]
    fn div_is_its_reference_and_refuses_other_hints() {
        let div = div();
        assert_eq!(div.k_log(), 13);
        let mut rng = Rng(0xA5);
        for round in 0..300 {
            let (v1, v2) = (
                rng.word(),
                if round % 9 == 0 {
                    0
                } else {
                    rng.word() >> (rng.next() % 64)
                },
            );
            for &flags in &crate::rv::div::LEGAL {
                let (q, r) = semantics::div_hints(v1, v2, flags);
                let expected = [semantics::div(v1, v2, flags), 0];
                assert_eq!(
                    run(&div, &[v1, v2, flags, q, r], 5..7),
                    expected,
                    "div {flags:#x} of {v1:#x} by {v2:#x}"
                );
                // Any other quotient or remainder is refused, unless the divisor is zero,
                // where they are ignored and the result is still the specification's.
                let by_zero = if flags & crate::rv::div::WORD != 0 {
                    v2 as u32 == 0
                } else {
                    v2 == 0
                };
                for (q, r) in [
                    (q.wrapping_add(1), r),
                    (q, r.wrapping_add(1)),
                    (q ^ (1 << 63), r),
                    (rng.next(), rng.next()),
                ] {
                    let got = run(&div, &[v1, v2, flags, q, r], 5..7);
                    if by_zero {
                        assert_eq!(got, expected);
                    } else {
                        assert_eq!(got[1], 1, "div {flags:#x} of {v1:#x} by {v2:#x} accepts {q:#x}, {r:#x}");
                    }
                }
            }
        }
        // The forgery a check modulo 2^64 would accept: 1 / 3 with a quotient of (2^64 + 1) / 3.
        assert_eq!(run(&div, &[1, 3, 0, 0x5555_5555_5555_5555, 2], 5..7)[1], 1);
        // The overflow, and division by zero, as the specification has them.
        let min = i64::MIN as u64;
        let (q, r) = semantics::div_hints(min, u64::MAX, crate::rv::div::SIGNED);
        assert_eq!(
            run(&div, &[min, u64::MAX, crate::rv::div::SIGNED, q, r], 5..7),
            [min, 0]
        );
        assert_eq!(run(&div, &[7, 0, 0, 0, 0], 5..7), [u64::MAX, 0]);
        assert_eq!(run(&div, &[7, 0, crate::rv::div::REM, 0, 0], 5..7), [7, 0]);
    }

    #[test]
    fn blake2s_is_its_reference() {
        let circuit = blake2s();
        assert_eq!(circuit.k_log(), 14, "a compression is 256 packed words");
        let mut rng = Rng(0xA6);
        for round in 0..40 {
            let block: [u64; 16] = std::array::from_fn(|_| rng.word());
            let t = rng.word();
            // The legal flags, and now and then any finalization word, which the
            // circuit XORs in like the reference does.
            let flags = match round % 4 {
                0 => crate::rv::hash::FINAL,
                1 => rng.next() as u32 as u64,
                _ => 0,
            };
            let inputs: Vec<u64> = [t, flags]
                .into_iter()
                .chain(block[..4].iter().chain(&block[8..]).copied())
                .collect();
            let expected = if crate::rv::hash::LEGAL.contains(&flags) {
                semantics::blake2s(&block, t, flags)
            } else {
                let half = |w: &[u64]| -> Vec<u32> { w.iter().flat_map(|&w| [w as u32, (w >> 32) as u32]).collect() };
                let out = flock::hash::blake2s_compress(
                    &half(&block[..4]).try_into().unwrap(),
                    &half(&block[8..]).try_into().unwrap(),
                    t,
                    flags as u32,
                    0,
                );
                std::array::from_fn(|i| out[2 * i] as u64 | (out[2 * i + 1] as u64) << 32)
            };
            assert_eq!(run(&circuit, &inputs, 14..18), expected, "flags {flags:#x}");
        }
    }

    #[test]
    fn blake2s_witness_is_the_gate_walk() {
        // Invariant: the word-level witness writes the tables the walk of the gate list writes.
        //
        // The walk is the reference: it reads the circuit itself, slot by slot.
        let circuit = blake2s();
        let n_log = 5;
        let mut rng = Rng(0xA7);
        let rows: Vec<[u64; 14]> = (0..1 << n_log)
            .map(|i| {
                // Counters at the edges of their two halves, then random ones.
                let t = [0, u32::MAX as u64, 1 << 32, u64::MAX]
                    .get(i)
                    .copied()
                    .unwrap_or_else(|| rng.word());
                // The legal finalization words, and any word, whose high half the port drops.
                let flags = [0, crate::rv::hash::FINAL, rng.next()][i % 3];
                std::array::from_fn(|k| match k {
                    0 => t,
                    1 => flags,
                    _ => rng.word(),
                })
            })
            .collect();

        // Both generators on the same batch, then every table compared.
        let walk = circuit.generate_witness(&rows, n_log);
        let fast =
            circuit.generate_witness_with(&rows, &[0; 14], n_log, |row, z, az, bz| blake2s_witness(row, z, az, bz));
        assert!(walk.0[..] == fast.0[..], "z");
        assert!(walk.1[..] == fast.1[..], "A·z");
        assert!(walk.2[..] == fast.2[..], "B·z");
        assert!(walk.3[..] == fast.3[..], "lincheck stripes");
    }

    /// flock proves a batch of honest instances, and refuses one with a flipped output bit.
    #[test]
    fn alu_reduction_roundtrip() {
        const LABEL: &[u8] = b"rv-alu-reduction-test";
        let circuit = alu();
        let block = circuit.block();
        let n_log = 4;
        let mut rng = Rng(0xA2);
        let legal = crate::rv::alu::LEGAL;
        let rows: Vec<[u64; 4]> = (0..1 << n_log)
            .map(|i| [rng.word(), rng.word(), 0, legal[i % legal.len()]])
            .collect();
        let run = |tamper: Option<usize>| {
            let (mut z, a, b, mut z_lincheck) = circuit.generate_witness(&rows, n_log);
            if let Some(bit) = tamper {
                z[bit / 64] ^= 1 << (bit % 64);
                z_lincheck[bit] ^= 1;
            }
            let mut ps = ProverState::from_label(LABEL);
            let stage = block.prove_zerocheck(n_log, &z, &a, &b, &mut ps);
            let claim = block.prove_lincheck(n_log, stage, &z_lincheck, &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(LABEL, &proof);
            block.verify(n_log, &mut vs).is_ok_and(|r| r.claim == claim) && vs.finish().is_ok()
        };
        assert!(run(None));
        // An output bit, a spare bit of `taken`'s word, a product.
        for bit in [
            64 * alu_ports::OUT + 5,
            64 * alu_ports::TAKEN + 1,
            circuit.useful_bits() - 1,
        ] {
            assert!(!run(Some(bit)), "flipping bit {bit} must reject");
        }
    }
}
