# Clean-authored production circuits

The 64-bit wrapping adder in `crates/flock/src/clean.rs` is generated from the Clean circuit `LeanVMCircuits.WrappingAdder.adder64`. `Load::circuit`, `Store::circuit`, and `Ld::circuit` in `crates/leanvm_core/src/rv/semantics/memory.rs` call this generated function. `Sd` shares the `Ld` circuit. The Flock reduction regression also uses the same production function, not another handwritten adder.

The same source also generates the 32-bit wrapping adder used by the production BLAKE2s circuit and the 64-bit carry-in/carry-out adder used by ALU, signed multiplication corrections, and division constraints. Division's conditional negation composes affine bit flipping with the exported carry adder. The former handwritten ripple-adder methods are removed. All optimized Rust word and packed witness kernels remain unchanged.

The complete RV shift circuit is authored in `LeanVMCircuits.Shift` and exported as `flock::clean::shift64`. The actual `Shift::circuit` in `crates/leanvm_core/src/rv/semantics/shift.rs` consumes it. This includes amount masking, word-operand extension, arithmetic fill, reversal for left shifts, all six barrel stages, and final word-result sign extension. The former handwritten shift gate construction and its unused reversal gadget are removed; the optimized native shift witness is unchanged.

These are Boolean circuits over `F2 = ZMod 2`, not Clean's prime-field `Addition32` gadget. Input and output vectors are little-endian bits; each element of `F2` is necessarily zero or one. Wrapping sums are modulo `2^64` or `2^32`, with 63 or 31 products in least-significant-bit order and no discarded-overflow product. The carry adder uses 64 ordered products and returns a 64-bit sum and one carry bit.

## Reproduce

The project pins Lean `v4.33.1`, Clean revision `b449bf590f93e13827c3c7e747e392d6969aa380`, and all transitive dependencies in `lake-manifest.json`. Regeneration uses Rust `1.97.0` with `rustfmt` and the repository's formatting configuration. Normal Rust builds use the checked-in generated file and require neither Lean nor a Clean checkout, network access, or a local filesystem dependency.

From this directory:

```sh
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 lake exe cache get Mathlib.Tactic
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 lake build
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 lake env lean Audit.lean
shopt -s globstar nullglob
for source in LeanVMCircuits/**/*.lean; do
  module="${source%.lean}"
  flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 lake env leanchecker "${module//\//.}"
done
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 lake env lean --run Generate.lean ../../crates/flock/src/clean.rs
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 lake env lean --run Generate.lean /tmp/clean-generated.rs
diff -u ../../crates/flock/src/clean.rs /tmp/clean-generated.rs
```

The `Clean circuits` workflow performs the proof build, axiom audit, serialized theorem kernel recheck, and deterministic regeneration check. The generator rejects unbound, forward, or duplicate product variables. The lowering accepts only affine GF(2) expressions and scalar witnesses immediately constrained to their defining products. Other witnesses, assertions, nested products in affine operands, lookups, interactions, and excessive subcircuit nesting return explicit errors rather than being ignored.

Kernel rechecks invoke stock `leanchecker` sequentially for every library source module, including intermediate modules. Its prefix command on the whole library starts concurrent replays, each with an imported environment. The workflow derives the complete module list from the source tree, fails on a missing compiled module, and separately enforces that the root contains only its module header and public imports, so it has no declarations left unchecked. Serialization bounds peak memory without introducing a custom checker or dropping proofs.

## What is proved

`FullAdder.soundness` proves the integer identity `sum + 2 * carry_out = x + y + carry_in` from the defining Boolean product constraint. Its completeness theorem checks the Clean witness generator. `Adder.circuit` composes those circuits with a proof of the full word identity. `WrappingAdder.circuit` removes the unused high carry product and proves the modular sum.

`Flock.lowerAffine_correct` and `Flock.lower_correct` prove evaluation and constraint equivalence for every assignment. `Flock.flatten_correct` proves that successful bounded flattening returns exactly Clean's flat operations; the bound is an explicit export error, not a silently truncated circuit. `Flock.adder64_source` identifies the exact checked artifact with lowering of the actual Clean source. `Flock.adder64_layout` checks 63 ordered product variables starting at 128 and 64 outputs. `Flock.adder64_soundness` proves that every assignment satisfying that artifact's product constraints has the correct modular output. It does not assume that an assignment was generated honestly.

`Flock.witness_exists` constructs satisfying assignments for acyclic product rows. `Flock.adder64_wellFormed` checks the concrete artifact's dependency order, and `Flock.adder64_complete` proves that every assignment of the 128 input bits extends to a satisfying assignment. Completeness therefore does not stop at an unfulfilled witness-generation premise.

`Flock.adder32_source`, `adder32_layout`, `adder32_soundness`, `adder32_wellFormed`, and `adder32_complete` establish the corresponding exact-artifact claims for the 32-bit wrapping adder. Its product variables are 64 through 94, after 64 input bits. `Flock.carryAdder64_source`, `carryAdder64_layout`, `carryAdder64_soundness`, `carryAdder64_wellFormed`, and `carryAdder64_complete` establish them for the carry adder. Its input variables 0 through 127 name the operand bits, input 128 names the carry-in, and product variables 129 through 192 name 64 ordered products. The 65 output bits represent the exact integer `x + y + carry_in`, so the theorem covers both the low sum and final carry. Each completeness theorem extends every input assignment to a satisfying assignment.

`Shift.assumptions_iff_legal_flags` identifies the semantic domain exactly with flag words `0, 1, 3, 4, 5, 7`: arithmetic shifts must shift right. The flags are Boolean because the source field is GF(2). The source specification uses direct indexed left or right shifts, zero or sign-bit fill, a six-bit or five-bit amount from `v2 XOR imm`, and final 32-bit sign extension. `Flock.Shift.source_eq` identifies the artifact with lowering of this actual source. `Flock.Shift.layout` checks its 579 products at source variables 195 through 773 and its 64 outputs. `Flock.Shift.soundness` proves the specified output for every satisfying assignment in that exact flag domain, not just honestly generated witnesses. `Flock.Shift.wellFormed` and `Flock.Shift.complete` prove that every assignment of the 195 input bits extends to a satisfying assignment. The circuit does not itself enforce flag legality; the semantic theorem exposes this instruction-class domain rather than assuming a security conclusion.

Artifact support, layout, and well-formedness are checked by `decide +kernel`, not `native_decide`. `Audit.lean` prints the transitive theorem axiom closures and fails on any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. No admitted theorem, native-decision axiom, or security premise is used.

## Rust interpretation and remaining trust

The generator consumes the checked `Flock.adder64`, `Flock.adder32`, `Flock.carryAdder64`, and `Flock.Shift.artifact` artifacts directly. Input variables name the function's operand bits and, for the carry variant, its `carry_in` argument. Shift inputs name `v1`, `v2`, and `imm` bits followed by the right, arithmetic, and word flags. Each later variable names the result of its ordered product. An affine zero or one becomes `Wire::ZERO` or `Wire::ONE`, affine addition becomes `Builder::xor`, and each row becomes `Builder::and`. Artifact outputs become the returned sum, carry, or shifted word wires. Generated common-subexpression reuse changes XOR gate ordering, not affine meaning or the order of products.

`Builder` places ports before its constant pin and product slots. For the `Ld`/`Sd` shape, input bits occupy 0 through 127, output bits occupy 128 through 191, the constant pin is 192, and the 63 product slots occupy 193 through 255. The source's product variable 128 plus its ordinal maps to the corresponding Builder product, not to output slot 128 plus that ordinal. Builder output rows tie the committed output ports to the returned affine expressions. Structural zeros and unused port bits retain Builder's existing forced-zero interpretation.

For the shift shape, Rust's four padded input words occupy slots 0 through 255, the output occupies 256 through 319, the constant pin is 320, and the 579 products occupy 321 through 899. Source variables 0 through 191 map to the three full operand words; source variables 192 through 194 map to the three live flag bits. Source product variable 195 plus its ordinal maps to Rust product slot 321 plus that ordinal, not to a flag or output slot. The other 61 flag-port bits and instance padding retain Builder's existing forced-zero interpretation.

The proven export boundary is the concrete Lean artifact and its GF(2) semantics. Lean's runtime execution, the Rust pretty-printer and formatter, the Rust compiler, and Builder's implementation of XOR, AND, constant pinning, output rows, and slot packing remain trusted parts of the Rust interpretation. Deterministic regeneration checks linkage and drift; it is not presented as a proof of these implementations. The existing packed native `address_rows` witness kernel is unchanged. Its correspondence to the generated circuit is exercised by the production memory witness regression and complete RV proof verification, but the Rust native word-arithmetic implementation itself is not formally verified here.

The RV regression `clean_adder_memory_addresses_wrap_and_carry` proves and verifies real `Ld`/`Sd` accesses through both a negative-immediate overflow and a long carry boundary, then rejects an altered output statement. The Flock reduction regression verifies honest batches and rejects mutations of input, output, constant, and product bits. This establishes exercised integration, not a cryptographic security proof of Flock, the PCS, Fiat-Shamir, or the whole VM. Other instruction circuits and protocol constraints are outside these adder and shift proofs.

`clean_carry_adder_arithmetic_boundaries` proves and verifies actual ALU overflow and unsigned comparison, signed division overflow, and signed high multiplication, then rejects an altered output statement. The existing BLAKE2s precompile proof regression exercises the generated 32-bit adder. These are integration checks: the complete ALU, division, multiplication, BLAKE2s, and conditional-negation semantics are not yet formally proved by the adder theorems alone.

`clean_shift_sign_and_mask_boundaries_prove_and_verify` exercises real RV shifts at signed and word boundaries and rejects an altered output statement. `clean_shift_proves_native_witnesses_and_rejects_false_outputs_and_products` uses the unchanged optimized witness in actual Flock proof verification, then rejects mutations of an output, the first and last products, and an unused flag-port bit. The existing shift regressions cover every legal flag word and all shift amounts against the production gate walk and reference semantics. These checks exercise the Rust interpretation and native witness; their implementations are not thereby formally verified.
