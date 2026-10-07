# Verus proofs of the field arithmetic, bit transposes and additive NTT

This crate proves, with [Verus](https://verus-lang.github.io/verus/guide/overview.html), that the portable
(non-SIMD) code of `crates/primitives` (the fields `K = GF(2^64)`, `E = GF(2^192)` and `GF(2^8)`, the bit
transposes, the equality polynomial and multilinear evaluation) and of `crates/pcs/src/ntt` (the additive NTT), the
Fiat-Shamir step block of `crates/fiat_shamir` and the univariate-skip domain of `crates/flock` compute the
mathematics they are meant to.

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
are reached through the nearest public function that calls them (each test says which). An edit to one side
without the other fails these tests. CI's `Verus proofs` job runs both the proofs and these tests.

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

### The φ₈ table (`src/phi8_tower.rs`)

- `build_phi8_table_192` (and the static `PHI_8_TABLE_192`) holds at index `i` the XOR of the eight basis words selected by the bits of `i`, in `K` (`phi8`). So the table is `F_2`-linear in its index (`lemma_phi8_xor`) and zero only at index 0 (`lemma_phi8_nonzero`, one `by (compute_only)` over the 255 nonzero indices): its first `2^k` entries are a subspace of `K` of `2^k` distinct elements.

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
  slice indexing, `slice_to_vec`, and its proven `pow2` and division lemmas.
- `src/ntt.rs` declares `global size_of usize == 8`: the NTT proofs are for 64-bit targets, which Verus checks
  when it compiles the crate.
- The copies equal the production functions by test, not by proof (see above). Two copies have no public production counterpart to run: `builder_step_message` (`Builder` is in `leanvm_core`'s private `rec` module) is tied by `rec::transcript::tests::the_circuit_replays_the_native_transcript`, the circuit's steps hashing to the native ones; `SkipDomain::first_round_at` (crate-private, run only inside a whole zerocheck) and `SkipDomain::new` are compared with the references production's own `skip_domain::tests` compare production with.
- `PHI_8_TABLE_192`, `DENOMINATORS` and `SkipDomain::FLOCK` are written in Verus's `exec static` / `exec const` form, which states what the initializer returns; Verus checks the initializer like a function body. The parallel pass of `fill_eq_table_uninit` is copied as a loop over the same rows in order.
- `vstd`'s specifications of `vec!`, `Vec::truncate`, `Vec::as_mut_slice`, slice range indexing and `u64::trailing_zeros` (which stands in for `usize::trailing_zeros` in `window_denominator`).
- The two lemmas about SIMD reductions assume that the carry-less multiply instructions compute `clmul`. They
  are stated as lemmas over `clmul`; no SIMD code is verified.

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
  - NTT butterflies: `ntt::additive_ntt_f64::tests::interleaved_parallel_matches_scalar` and the other driver
    tests (forward), `whir::induce::tests::blocked_and_gathered_transposes_match_layer_by_layer` (transposed).
- The NTT's parallel driver (`transform`, `gathered_pass`, `run_layers`, `fused_rows`, `replicate`,
  `transpose_lane_major`), which reorders and gathers rows through raw pointers, is not copied. The production
  tests compare it with the layer-by-layer reference this crate verifies.
- `bit_fold` is not covered; of `phi8_tower.rs` only the table is (that `φ₈` is a field embedding, multiplicative, is not proven).
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
(default 4). The whole crate verifies in under two minutes on one machine with two solver threads.
