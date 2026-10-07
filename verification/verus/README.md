# Verus proofs of the field arithmetic, bit transposes and additive NTT

This crate proves, with [Verus](https://verus-lang.github.io/verus/guide/overview.html), that the portable
(non-SIMD) code of `crates/primitives` (the fields `K = GF(2^64)`, `E = GF(2^192)` and `GF(2^8)`, the bit
transposes, the embedding `φ₈`, the bit folds, the equality polynomial and multilinear evaluation), of
`crates/pcs/src/ntt` (the additive NTT), of `crates/flock/src/zerocheck/ntt` (the `GF(2^8)` NTT of flock's
zerocheck) and `crates/flock/src/zerocheck/skip_domain.rs` (the univariate-skip domain), and the Fiat-Shamir step
block of `crates/fiat_shamir`, compute the mathematics they are meant to.

It is a workspace of its own, outside the leanVM one: `cargo build`, `cargo testall` and the other CI jobs never
see it, and the production crates do not depend on Verus.

## How it is tied to the production code

Verus verifies code written inside `verus! { }`. Rather than putting `vstd` and the macro into the production
crates, each module here holds a copy of the production functions, with the same names, signatures and bodies
wherever Verus accepts them, and attaches its specification to the copy. A copy differs from production only
where Verus needs another form; each difference is noted at the function (iterator chains and
`array::map`/`from_fn` become index loops or explicit arrays, `step_by` becomes a `while`, slice patterns become
indexing, `assert!` on an argument becomes a `requires`, `debug_assert!` becomes a proven `assert`, `mut self`
is rebound). SIMD arms are not copied.

`tests/equivalence/` then runs every copy against the production function it copies: exhaustively where the
domain is small (all `GF(2^8)` pairs, all 16-bit reductions), and otherwise on 10k to 100k random inputs plus
edge cases (zero, one, all ones, top bits only, the reduction constant). Production functions that are private
are reached through the nearest public function that calls them (each test says which); flock's zerocheck NTT has
no public path at all, so its two source files are compiled into the test binary by `#[path]` and called directly.
An edit to one side without the other fails these tests. CI's `Verus proofs` job runs both the proofs and these tests.

Production is compiled natively there, so the tests also compare the dispatched SIMD arms of the machine (on
CI's runners the AVX2 arms) with the verified portable copies.

## What is proven

Polynomials over GF(2) are machine words, bit `i` the coefficient of `x^i`. The specifications are:

- `clmul(a, b)`: the carry-less product, defined as the XOR over the set bits `i` of `a` of `b << i`
  (`src/clmul.rs`).
- `is_remainder(p, r)`: `p = q * M + r` for some polynomial `q`, with `deg r < 64` (`M = x^64 + x^4 + x^3 + x + 1`);
  `k_mod(p)` is that remainder and `k_mul(a, b) = k_mod(clmul(a, b))`, the product in `K`. The same for
  `GF(2^8)` with `M = x^8 + x^4 + x^3 + x + 1` (`f8_mul`).
- `e_mul(a, b)`: the product of `a0 + a1 y + a2 y^2` and `b0 + b1 y + b2 y^2` as polynomials in `y` over `K`,
  folded by `y^3 = y + 1` and `y^4 = y^2 + y`.
- `k_pow`, `e_pow`, `f8_pow`: repeated products.

### `K = GF(2^64)` (`src/gf2_64.rs`)

- `software::clmul` computes `clmul`; so do `mul_wide` and `square_wide` (portable arms).
- `reduce(p)` returns the remainder of `p` modulo `M`, for every 128-bit `p`, and the remainder is unique.
- `F64 * F64` is `k_mul`, `F64::square` is `k_mul(a, a)`; `+` is XOR.
- `K` is a commutative ring: `k_mul` is commutative, associative, distributes over XOR, and has one and zero.
- `F64::inv(a)` is `a^(2^64 - 2)` (the Itoh-Tsujii addition chain is checked step by step), and
  `a * inv(a) = 1` for every nonzero `a`, `inv(0) = 0`.
- Fermat: `a^(2^64) = a` for every `a`.
- So `K` is a field, with no assumption on `M`: the proof shows the only idempotents (`e^2 = e`) are 0 and 1,
  one bit-vector query on the squaring map, then `a^(2^64 - 1)` is an idempotent that is not 0 when `a` is not.
- The reduction of the scalar SIMD products (`x86_64::mul`, `aarch64::mul_shift_tail`,
  `aarch64::reduce_pair_pmull4`: `t = hi(p) * 0x1B`, `u = hi(t) * 0x1B`, `lo(p ^ t ^ u)`) equals `reduce`, given
  that PCLMULQDQ and PMULL compute `clmul` (`lemma_clmul_fold_reduction`).

### `E = GF(2^192)` (`src/gf2_64x3.rs`)

- `software::mul_unreduced`, `F192::mul_unreduced`, `mul_base_unreduced` and `From<F192>` build an
  `F192Unreduced` whose three 128-bit coefficients, each reduced modulo `M`, are the product (`e_value`).
- `F192Unreduced::reduce` returns that element; `F192 * F192 = e_mul`; `mul_base(k) = e_mul(a, k)`;
  `square(a) = e_mul(a, a)` (the cross terms cancel).
- Lazy reduction: `e_value(u ^ v) = e_value(u) + e_value(v)`, and for any sequence of unreduced values,
  reducing their XOR once equals summing their reductions (`lemma_lazy_reduction`). This is what the
  accumulating kernels rely on.
- `mul2`, `mul4`, `mul_unreduced4`, `mul_base8` (portable arms) are lane-wise products; `Weights8::new` then
  `get(i)` returns weight `i`; `dot_base` returns `sum_i w_i * k_i`.
- `E` is a commutative ring (associativity by expansion into the 27 triple products).
- `frobenius(a)` is `a^(2^64)` (it is the 64th squaring, by Fermat in `K`).
- `F192::inv(a)` is `a^(2^192 - 2)`, and `a * inv(a) = 1` for every nonzero `a`; the norm `a * φ(a) * φ²(a)`
  lies in `K` (production's `debug_assert!`). So `E` is a field too, again with no assumption.
- The x86 Karatsuba product (six PCLMULQDQs and `fold`) gives the same three unreduced coefficients as the
  schoolbook product, given that PCLMULQDQ computes `clmul` (`lemma_karatsuba_fold`).

### `GF(2^8)` (`src/gf2_8.rs`)

- `clmul8_software` (and the portable arm of `clmul8`) computes the carry-less product of two bytes.
- `gf8_reduce(p)` is the remainder modulo `x^8 + x^4 + x^3 + x + 1` for every 16-bit `p`, not only the
  documented 15-bit ones, and the remainder is unique.
- `F8 * F8` is that product, a commutative ring as for `K`; `F8::inv(a)` is `a^254` and `a * inv(a) = 1` for
  every nonzero `a`.

### Bit transposes (`src/bits.rs`)

- `transpose_8x8_bits`: bit `8r + c` of the result is bit `8c + r` of the input; it is an involution.
- `transpose_64x64`: afterwards bit `r` of word `c` is bit `c` of word `r` before, for all `r, c < 64`;
  transposing twice restores the matrix. Each masked-swap round exchanges `(r, c)` and `(r ^ J, c ^ J)`
  exactly when bit `J` of `r` and `c` differ.
- `bit_transpose_64bytes_portable`: bit `x` of `output[8b + t]` is bit `t` of `input[8x + b]`.

### Additive NTT (`src/ntt.rs`)

Following annex `d` of the leanVM document:

- Butterflies: the forward butterfly evaluates the line `u + v X` at `X = t` and `X = t + 1`; the inverse
  butterfly of `inverse_transform` and the forward one undo each other for every twiddle; the transposed
  butterfly undoes the forward one with the rows swapped.
- Twiddles: `span_get(b, idx)` is the subset sum of `b` selected by the bits of `idx`, GF(2)-linear in `idx`;
  `twiddle(layer, block)` is `Ŵ_i(sum_j bit_j(block) b_(i+1+j))` with `i = L - layer - 1`; `twiddles_radix8`
  returns exactly the seven twiddles of the three layers it fuses.
- Twiddle table: entry `k` of row `i` of `generate_evals_from_subspace(b)` is `s_i(b_(i+k)) * s_i(b_i)^(-1)`,
  with `s_0(x) = x`, `s_i(x) = s_(i-1)(x) (s_(i-1)(x) + s_(i-1)(b_(i-1)))` the subspace polynomials; each `s_i`
  is GF(2)-linear and vanishes on the span of `b_0 .. b_(i-1)`.
- Layers: `radix8_butterflies` and the radix-4 group of `butterfly_interleaved_fused_2layer` equal three and
  two successive single layers. The layer-by-layer forward transform (`forward_scalar_from_layer`, the
  production tests' reference, which they compare with the parallel `transform`) followed by the inverse layers
  is the identity, for every number of interleaved lanes and every size up to the table's; with one lane the
  inverse layers are `inverse_transform`.
- Evaluation: for the table `AdditiveNttF64::standard(dim)` builds (`1 <= dim <= 63`), output word `v` of the
  forward transform on `2^dim` words is `P(v)`, where `P(x) = sum_j a_j X_j(x)` with novel basis
  `X_j = prod_i Ŵ_i(x)^(bit_i(j))` and the input `a` read as its coefficients; the domain point of index `v` is
  the field element `v` itself (no bit reversal). Encoding at rate `2^-r` (layers `r..dim` on `2^r` copies of the
  message) gives the evaluations of the polynomial whose coefficients are the message, zero-padded: the
  Reed-Solomon codeword (`lemma_standard_forward_evaluates`, `lemma_standard_encode_evaluates`; the sum is
  `novel_sum`, equal to the annex's even-odd recurrence `novel_eval` by `lemma_novel_eval_flat`). The proof
  needs every row of the table to start with one, `Ŵ_i(b_i) = 1`; it is proven for the standard basis, from
  `K` being a field and `s_i` vanishing only on the span of `b_0 .. b_(i-1)`. For an arbitrary basis the same
  theorems (`lemma_forward_evaluates`, `lemma_encode_evaluates`) take that as a hypothesis.

### The embedding `φ₈` (`src/phi8_tower.rs`)

`φ₈` (`phi8`) is the GF(2)-linear map sending the byte `x^i` to `PHI_8_BASIS[i]` in `K` (`phi8_basis`); `phi8_e(a)` is `φ₈(a)` in `E`. Annex `c` calls it the subfield embedding of `GF(2^8)` in `E`, and flock's univariate skip domain is `φ₈(0..64)`.

- `build_phi8_table_192` fills entry `v` with `φ₈(v)` embedded in `E`; so does the static `PHI_8_TABLE_192`, and `phi8_192(a)` returns `phi8_e(a)`.
- `φ₈` is GF(2)-linear (`lemma_phi8_xor`), so `φ₈(0..64)` is the span of `φ₈(1), φ₈(2), .., φ₈(32)`, and zero only at zero (`lemma_phi8_nonzero`, from injectivity).
- `φ₈` is multiplicative into `K`: `φ₈(a * b) = φ₈(a) φ₈(b)` for all bytes, `a * b` the product of `GF(2^8)` (`f8_mul`) and the right side `k_mul` (`lemma_phi8_mul`). The proof: `φ₈(x a) = φ₈(x) φ₈(a)` (`lemma_phi8_mulx`), which by linearity needs only the eight monomials, eight products of concrete constants in `K` checked by bit-vector evaluation of the closed-form carry-less product (`clmul64_closed`, `lemma_k_mul_closed`); then `φ₈(x^i b) = φ₈(x^i) φ₈(b)` by induction on `i` and associativity in `K`, and the general product by linearity in the left factor.
- So `φ₈` is a ring homomorphism into `E`, `φ₈(1) = 1`, `φ₈(0) = 0`, and it is injective (the eight basis images are GF(2)-independent), with image in `K` (`c1 = c2 = 0`) (`lemma_phi8_e_homomorphism`). Its image is therefore a subfield of `E` with 256 elements. That it is the only one (production's doc comment) is not proven: it would need that a polynomial of degree 256 has at most 256 roots.

### Bit folds and linear maps of `E` (`src/bit_fold.rs`)

The portable arm of `crates/primitives/src/bit_fold.rs` (`bit_fold/portable.rs`) and the wrappers `BitFold`, `F192Map`, `Sliced`. Bit `s` of a row of bytes is bit `s % 8` of byte `s / 8`; coordinate bit `b` of an `E` value is bit `b % 64` of coefficient `b / 64`.

- Tables: `lookup_tables(w)` returns one table per whole chunk of 8 weights, entry `[j][v]` the sum of `w[8j + i]` over the set bits `i` of `v` (`byte_sum`); the lowest-set-bit recurrence is proven to build exactly that (`lemma_byte_sum_clear`). The weight of bit `s` is recovered as table `s / 8` at the single bit `s % 8` (`lemma_byte_sum_monomial`), so `Imp::new(w)` holds the weights `w`, truncated to whole chunks.
- Fold: `BitFold::new(w)` (for 8, 16, 32, 64 or 128 bytes per row, production's `assert!` being the `requires`) then `fold_block(rows, out)` sets `out[p] = sum_{s : bit s of rows[p]} w_s` (`fold_spec`) for every `p < rows.len()`, the definition the module doc states, and leaves `out[rows.len()..]` unchanged. The table lookups add up to that sum byte by byte (`lemma_tables_fold`).
- Linear maps: `F192Map::new(w)` then `apply_add(xs, out)` (and `apply_sliced_add` on `Sliced::new(xs)`) adds `map(w, xs[p]) = sum_{b : coordinate bit b of xs[p]} w_b` (`map_spec`) to `out[p]` for every `p < out.len()`: the 24 little-endian bytes of a value fold to its map (`lemma_row_sum_le_row`). The map is GF(2)-linear (`lemma_coord_sum_add`, `lemma_coord_sum_zero`) and every element is the sum of the coordinate vectors of its set bits (`lemma_units_sum`), so a GF(2)-linear `Φ: E -> E` is the `F192Map` of the weights `Φ(unit(b))`, which is how ring switching uses it.
- `after_mul(c)` returns the map with weights `map(w, unit(b) * c)` and, for every `x`, `after_mul(c)(x) = map(w, x * c)` (`lemma_after_mul`, from the linearity of the map and the distributivity `(a + b) c = a c + b c` in `E`, `lemma_e_mul_add_left`). This is the identity production's `composed_map_is_the_map_after_the_product` tests.
### Lane-interleaved NTT (`src/ntt_lanes.rs`)

A buffer of `m` interleaved lanes holds word `v` of lane `l` at word `m v + l` (`lane(data, m, l)`).

- One layer commutes with taking a lane: lane `l` of a forward or inverse layer's output is the same layer applied to lane `l` alone (`lemma_lane_layer`), so the forward layers `start..end` and the inverse layers transform every lane independently (`lemma_lane_forward_layers`, `lemma_lane_inverse_layers`). This holds for any table and any lane count, and `forward_scalar_from_layer` computes `forward_layers` for any lane count.
- Evaluation: for `AdditiveNttF64::standard(dim)` on `m` lanes of `2^dim` rows, output word `m v + l` is `P_l(v) = sum_j a_(m j + l) X_j(v)`, lane `l`'s novel-basis polynomial at the domain point `v` (`lemma_standard_lanes_forward_evaluates`).
- Encoding: the encoder at rate `2^-r` on `m` lanes (layers `r..dim` on `2^r` copies of an `m`-lane message of `2^(dim - r)` rows, as `encode_interleaved_in_place` lays it out) gives at word `m v + l` the evaluation at `v` of the polynomial whose coefficients are lane `l` of the message, zero-padded: every lane is Reed-Solomon encoded (`lemma_standard_lanes_encode_evaluates`).
- No new executable copy: the lanes theorems are about `forward_scalar_from_layer`, already checked against `encode_interleaved_in_place` for 1, 2, 3, 5 and 8 lanes, at rate 1 and at several rates, in `tests/equivalence/ntt.rs`.

### `GF(2^8)` additive NTT of flock's zerocheck (`src/flock_ntt.rs`)

Over the field of `src/gf2_8.rs`, with the standard basis `b_i = x^i` (the byte with bit `i` alone), the subspace polynomials `s_0(x) = x`, `s_i(x) = s_(i-1)(x) (s_(i-1)(x) + s_(i-1)(b_(i-1)))` and `Ŵ_i(x) = s_i(b_i)^(-1) s_i(x)`. `novel8(m, a, x)` is the novel-basis polynomial `sum_(j < 2^m) a_j X_j(x)`, `X_j = prod_(i < m) Ŵ_i(x)^(bit_i(j))`, written by its split on the top bit of `j`; `lemma_novel8_flat` proves it equal to the flat sum `novel8_sum`. `fft_spec` and `ifft_spec` are the recursions of `fft_rec` and `ifft_rec`.

- Subspace polynomials: each `s_i` and `Ŵ_i` is GF(2)-linear, `s_i` vanishes exactly on `{0, .., 2^i - 1}` (`lemma_subspace_poly8_vanishes`, `lemma_subspace_poly8_roots`, from `GF(2^8)` having no zero divisors), so `Ŵ_i(b_i) = 1` for every `i < 8` (`lemma_normalized_poly8_at_basis`).
- Twiddles: `compute_twiddles(k, β)` (any `k <= 8`, any offset `β`) returns `2^k - 1` entries, entry `2^d - 1 + j` (depth `d < k`, block `j < 2^d`) being `Ŵ_(k-1-d)(β + j 2^(k-d))`, `Ŵ` of the first point of the block, as its documentation's layout says (`twiddles_of`, the postcondition).
- Butterflies and recursions: `fft_butterfly`, `ifft_butterfly`, `fft_rec` and `ifft_rec` compute `fft_spec` and `ifft_spec` on every power-of-two length; `AdditiveNttGf8::forward` and `inverse` are `fft_rec` and `ifft_rec` from the root.
- Evaluation: with the table of `new(k, β)`, output word `u` of `forward` on `2^k` coefficients is `P(β + u)` (the point `β ⊕ u`, no bit reversal), the novel-basis polynomial of the input at the `u`-th point of the domain `β + span{1, 2, .., 2^(k-1)}`, as the struct's documentation claims (`lemma_fft_evaluates`).
- Inverse: `inverse` undoes `forward` and `forward` undoes `inverse`, for any table and any buffer (`lemma_ifft_after_fft`, `lemma_fft_after_ifft`), so `inverse` interpolates: on the evaluations of `P` it returns `P`'s coefficients (`lemma_ifft_interpolates`).
- The extension matrix: let `M = forward_Λ ∘ inverse_S` for any two `2^k`-point NTTs (offsets `β_s`, `β_l`), column `t` being the image of `e_t` (`lde_column`). Then `M[i][j] = M[i ⊕ j][0]` (`lemma_lde_shift`): the interpolant of `e_j` on `S` is the interpolant of `e_0` translated by `j`, because a translate of a novel-basis polynomial is again one (`translate`, `lemma_translate`) and the transform is injective. This is the "XOR-shift relation" `inv_table.rs` relies on.
- The table: `InvNttTableByteSingleGf8::new(ntt_s, ntt_l)` (`3 <= k <= 7`) holds, at row `w`, the XOR of the columns `t < 8` of `M` over the set bits `t` of `w`, as its field's documentation claims (`table_row`, the postcondition), for any two NTTs of the same `k`.
- `apply_scalar` applies `M`: its output word `i` on a row of `ell / 8` bytes is `sum_b T[bytes[b]][i ⊕ 8b]` (the postcondition), which equals `sum_j x_j M[i][j]`, `x_(8b+t)` being bit `t` of byte `b`, for the table of two NTTs built by `new` (`lemma_table_applies_lde`).
- Copies: `compute_twiddles` and `new` take `k <= 8` as a precondition (the domain lies in `GF(2^8)`; production does not check it), `fft_rec` and `ifft_rec` take a power-of-two length and in-table twiddle reads (production's only caller guarantees both), the `assert!`s become `requires`, iterator loops and `copy_from_slice` become index loops, the `continue` of `new`'s last loop becomes an `if` (Verus's `for` has no `continue`), and `w.trailing_zeros()` is taken on `w as u64` (vstd specifies it for `u64`, not `usize`).

### Fiat-Shamir step block (`src/fiat_shamir.rs`)

- `step_block(scalars, tag)` (and `builder_step_message`, the message the circuit's `Builder::step` hashes for the same step, over its wires' values) puts the last scalar in words 4 to 6, the one before it (if any) in words 0 to 2, their count in word 3 and the tag in word 7, zero elsewhere (`block_word`). So the circuit hashes exactly the native block, as `hash.rs` documents.
- On the domain production takes (at most `MAX_PENDING = 2` scalars, longer slices panic) the block names its scalars and its tag (`lemma_step_block_decodes`), so two steps with the same block absorb the same scalars, so the same count, under the same tag (`lemma_step_block_injective`). This holds for every tag word; the four `DS_*` tags are pairwise distinct (`lemma_tags_distinct`).

### The equality polynomial and multilinear evaluation (`src/multilinear.rs`)

Over `E`, `eq(r, x) = prod_i (r_i x_i + (1 + r_i)(1 + x_i))` (`eq_poly`, `eq_factor`; `1 - a = 1 + a` in characteristic 2), and a table over `n` variables holds at index `x` the value at the cube point whose coordinate `i` is bit `i` of `x` (`cube_point`, `eq_at`). `is_eq_table(t, r, seed)` says `t[x] = seed * eq(r, x)` for all `2^n` indices.

- `eq_eval(r, x)`, the product of `1 + r_i + x_i`, is `eq(r, x)` for every `x` in `E^n`, not only on the cube (`lemma_eq_factor_sum`).
- `eq_table`, `eq_table_seeded` and `fill_eq_table_uninit` build `seed * eq(r, .)` entry by entry, LSB first, for `n < 64`: the doubling build below `2^16` entries (each level writes `v r_i` to the high child and `v (1 + r_i)` to the low one, `lemma_eq_at_high`) and the tensor build above (`eq(r, (h << L) | l) = eq(r[..L], l) eq(r[L..], h)`, `lemma_eq_at_tensor`).
- `shrink_eq_low` and `shrink_eq_high` sum the low pairs, or the two halves, of any table; on `seed * eq(r, .)` the result is `seed * eq(r[1..], .)`, or `seed * eq(r[..n-1], .)` (`lemma_shrink_low_eq`, `lemma_shrink_high_eq`).
- `SplitEq::with_low_vars`, `with_high_vars`: the two tables are `eq` over `r[..L]` and `r[L..]`; `at(x)` is `eq(r, x)`.
- `interp(lo, hi, t) = (1 + t) lo + t hi`, and `interp_k` the same on `K` endpoints.
- `mle_eval(table, point)` is the multilinear extension `sum_x eq(point, x) table[x]` (`mle`) of the `K`-valued table, on both paths: folding the lowest variable (`fold_low_k`, then `fold_ladder`, by `lemma_mle_fold_low`), and from three variables the packed low `eq` table, one `dot_base` per row, then the ladder over the rows (`lemma_mle_blocks`).
- `window_denominator(2^log)` (and the table `DENOMINATORS` it reads, computed at compile time) is `(prod_{k=1}^{2^log - 1} φ₈(k))^(2^64 - 2)`, the inverse in `K` of the product of the window's nonzero nodes (`lemma_denominator_inverts`; the product is nonzero since the nodes are and `K` has no zero divisors).

### The univariate-skip domain (`src/skip_domain.rs`)

`SkipDomain` of `crates/flock/src/zerocheck/skip_domain.rs` is generic over `fiat_shamir::arith::Arith`; the copy is instantiated at `Native` (its trait methods and the defaults it inherits copied as inherent methods). The domain of `l = 2^k` nodes (`k < 8`) is `S = {s_i = φ₈(i)}`; `V_l(z) = prod_i (z + s_i)` (`vanishing_spec`) and `L_i(z) = prod_{k != i} (z + s_k) / prod_{k != i} (s_i + s_k)` (`lagrange_basis`), the textbook Lagrange basis, with `L_i(s_j) = [i = j]` (`lemma_lagrange_basis_at_nodes`).

- `vanishing_coefficients` returns the coefficients of `V_l` as a linearized polynomial, `V_l(x) = sum_j c_j x^(2^j)` for every `x`, and it is monic (production's `debug_assert!`); adding a basis element `a` takes `V` to `V(x)^2 + V(a) V(x)` (`lemma_lin_step`, `lemma_vanishing_double`). `vanishing(z)` is `V_l(z)`.
- Every node of a window sees the same `prod_{k != i} (s_i + s_k)`: `k -> i ^ k` permutes the window (`lemma_prod_xor`), so it is the product of the nonzero nodes, which `window_denominator` inverts (`lemma_weight_inverts`).
- `lagrange_at(z, V_l(z), values)` (through `lagrange_scale`, `inverses`, `lagrange_with`) is `sum_i values_i L_i(z)` (`lagrange_sum`), and `first_round_at(z, V_l(z), values)` is `sum_i values_i L_(l+i)(z)` over the window of `2l` nodes (`window_sum`): the interpolant of `values` on the coset `{s_l, .., s_(2l-1)}` and of zero on `S`, for every `z` off the nodes. At a node `s_j` production returns 0 (it divides by `z + s_j` with `1 / 0 = 0`) rather than the interpolant's value, as its documentation now says; `z` is the verifier's challenge, so this happens with probability at most `128 / 2^192`, where an honest proof would be rejected.

## Trust base and assumptions

- No `assume`, `admit`, `#[verifier::external_body]` or `assume_specification` appears in this crate.
- Verus and Z3 are trusted: Verus's encoding of Rust (machine integers, the truncating casts and shifts the code
  uses, arrays, `Vec`) and Z3's answers, in both its integer and its bit-vector modes.
- `vstd`'s specifications of what the copies call are trusted: integer `From`, the operator traits, `Vec` and
  slice indexing (by index and by range), `slice_to_vec`, `vec![x; n]`, `Vec::clone`, `Vec::truncate`,
  `Vec::as_mut_slice`, `split_at_mut`, `u64::trailing_zeros`, and its proven `pow2` and division lemmas.
- `src/ntt.rs` declares `global size_of usize == 8`: the NTT proofs are for 64-bit targets, which Verus checks
  when it compiles the crate.
- The copies equal the production functions by test, not by proof (see above). Two copies have no public production counterpart to run: `builder_step_message` (`Builder` is in `leanvm_core`'s private `rec` module) is tied by `rec::transcript::tests::the_circuit_replays_the_native_transcript`, the circuit's steps hashing to the native ones; `SkipDomain::first_round_at` (crate-private, run only inside a whole zerocheck) and `SkipDomain::new` are compared with the references production's own `skip_domain::tests` compare production with.
- `PHI_8_TABLE_192`, `DENOMINATORS` and `SkipDomain::FLOCK` are written in Verus's `exec static` / `exec const` form, which states what the initializer returns; Verus checks the initializer like a function body. The parallel pass of `fill_eq_table_uninit` is copied as a loop over the same rows in order.
- The two lemmas about SIMD reductions assume that the carry-less multiply instructions compute `clmul`. They
  are stated as lemmas over `clmul`; no SIMD code is verified.
- `src/bit_fold.rs` relies on `vstd`'s specification of `u8::trailing_zeros` (with its proven `axiom_u8_trailing_zeros`) and of `Vec::push`, `Vec::as_slice` and `Vec::as_mut_slice`.

## Not covered

- The SIMD arms (AVX-512, AVX2, GFNI, NEON, BMI2's `pdep` spread) are out of Verus's reach: they are intrinsic
  calls Verus has no model of. Each is tested against the portable path in production:
  - `K`: `field::gf2_64::tests::mul_and_square_match_the_reference` (PCLMULQDQ and PMULL products, `pdep` square),
    `neon_variants_match_software`.
  - `E`: `field::gf2_64x3::tests::products_match_software`, `batched_products_match_software`,
    `lane_products_match_software`, `register_products_match_software`, `batched_mixed_products_match_scalar`,
    `mixed_sums_match_software`, `planar_products_match_software` (added with this crate: the AVX-512
    `F192x8` kernels had no direct test).
  - `GF(2^8)`: `software_matches_neon`, `neon_gf8_mul_vec16_matches_scalar`, `avx2_gf8_mul_vec32_matches_scalar`,
    `neon_gf8_reduce_vec16_matches_scalar` (added with this crate: the reduction alone, on every 16-bit input,
    as its callers in flock use it).
  - Bit transposes: `bits::tests::every_arm_matches_reference`.
  - Bit folds and `F192Map`: `bit_fold::tests::fold_block_matches_definition`, `f192_map_matches_definition`, `composed_map_is_the_map_after_the_product`, `avx2_products_match_definition` (every AVX2 product, also on GFNI machines). The equivalence tests of this crate compare the verified portable copies with whatever arm the machine dispatches.
  - NTT butterflies: `ntt::additive_ntt_f64::tests::interleaved_parallel_matches_scalar` and the other driver
    tests (forward), `whir::induce::tests::blocked_and_gathered_transposes_match_layer_by_layer` (transposed).
  - flock's LDE table (`apply_v128` on NEON and SSE2, `apply_avx2`, `apply_avx512`/`apply_zmm`): `zerocheck::ntt::inv_table::tests::apply_simd_matches_apply_scalar`, and `tests/equivalence/flock_ntt.rs`, which compares the dispatched `apply` with the verified `apply_scalar` on every single-byte row and on random rows. The round-1 kernels that read the table through `data_ptr` and `apply_zmm` (`zerocheck/round1.rs`) are not covered.
- The NTT's parallel driver (`transform`, `gathered_pass`, `run_layers`, `fused_rows`, `replicate`,
  `transpose_lane_major`), which reorders and gathers rows through raw pointers, is not copied. The production
  tests compare it with the layer-by-layer reference this crate verifies.
- Bit folds (`crates/primitives/src/bit_fold.rs`): `BitFold::at_level`, which builds its weights with `multilinear::eq_table` (copied in `src/multilinear.rs`) and then calls `BitFold::new`, and `BitFold::fold_quads` (AVX-512 with GFNI only) are not copied. Only `out[..rows.len()]` of `fold_block` is documented and compared: past it the portable arm leaves `out` as it was (proven) and the SIMD arms store the fold of a zero row.
- Of `multilinear.rs`, the parallel `mle_eval_par`, `SplitEq::weighted_sum` and its SIMD variants, the high folds (`fold_high_k`, `fold_high_inplace`, `interp_into`), `barycentric_sum`, `skip_lagrange_weights`, `poly_eval` and the inner products are not copied.
- The circuit's constraints (that the hash row's wires carry the message `builder_step_message` computes) are not modeled; only the message is.

## Reproduce

Verus release `0.2026.10.04.426d8b0` (commit `426d8b01e7ffb910a36c15e1f870ff985bb61eef`, with its bundled Z3
4.16.0, built against Rust 1.98.1), and `vstd = "=0.0.0-2026-10-04-0306"` from crates.io, the `vstd` of that
release. From the repository root:

```bash
verification/verus/verify.sh                          # every proof; installs the pinned Verus under ~/.verus if missing
verification/verus/verify.sh gf2_64                   # one module
(cd verification/verus && cargo test --release)       # the verified copies against production
```

`verify.sh` downloads the release from GitHub (Linux x86-64), installs its Rust toolchain with `rustup`, and runs
`cargo verus verify`. Set `VERUS_HOME` to install elsewhere and `VERUS_THREADS` to change the solver's parallelism
(default 4). The whole crate verifies in about a minute and a half per configuration on one machine with two solver threads.
