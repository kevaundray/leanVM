# Clean-authored production circuits

The 64-bit wrapping adder in `crates/flock/src/clean.rs` is generated from the Clean circuit `LeanVMCircuits.WrappingAdder.adder64`. `Load::circuit`, `Store::circuit`, and `Ld::circuit` in `crates/leanvm_core/src/rv/semantics/memory.rs` call this generated function. `Sd` shares the `Ld` circuit. The Flock reduction regression also uses the same production function, not another handwritten adder.

This is a Boolean circuit over `F2 = ZMod 2`. It is not Clean's prime-field `Addition32` gadget. Input and output vectors are little-endian bits; each element of `F2` is necessarily zero or one. The sum is modulo `2^64`, with 63 products in least-significant-bit order. The final carry is discarded without allocating a product.

## Reproduce

The project pins Lean `v4.33.1`, Clean revision `b449bf590f93e13827c3c7e747e392d6969aa380`, and all transitive dependencies in `lake-manifest.json`. Regeneration uses Rust `1.97.0` with `rustfmt` and the repository's formatting configuration. Normal Rust builds use the checked-in generated file and require neither Lean nor a Clean checkout, network access, or a local filesystem dependency.

From this directory:

```sh
lake exe cache get Mathlib.Tactic
lake build
lake env lean Audit.lean
lake env leanchecker LeanVMCircuits
lake env lean --run Generate.lean ../../crates/flock/src/clean.rs
lake env lean --run Generate.lean /tmp/clean-generated.rs
diff -u ../../crates/flock/src/clean.rs /tmp/clean-generated.rs
```

The `Clean circuits` workflow performs the proof build, axiom audit, serialized theorem kernel recheck, and deterministic regeneration check. The generator rejects unbound, forward, or duplicate product variables. The lowering accepts only affine GF(2) expressions and scalar witnesses immediately constrained to their defining products. Other witnesses, assertions, nested products in affine operands, lookups, interactions, and excessive subcircuit nesting return explicit errors rather than being ignored.

## What is proved

`FullAdder.soundness` proves the integer identity `sum + 2 * carry_out = x + y + carry_in` from the defining Boolean product constraint. Its completeness theorem checks the Clean witness generator. `Adder.circuit` composes those circuits with a proof of the full word identity. `WrappingAdder.circuit` removes the unused high carry product and proves the modular sum.

`Flock.lowerAffine_correct` and `Flock.lower_correct` prove evaluation and constraint equivalence for every assignment. `Flock.flatten_correct` proves that successful bounded flattening returns exactly Clean's flat operations; the bound is an explicit export error, not a silently truncated circuit. `Flock.adder64_source` identifies the exact checked artifact with lowering of the actual Clean source. `Flock.adder64_layout` checks 63 ordered product variables starting at 128 and 64 outputs. `Flock.adder64_soundness` proves that every assignment satisfying that artifact's product constraints has the correct modular output. It does not assume that an assignment was generated honestly.

`Flock.witness_exists` constructs satisfying assignments for acyclic product rows. `Flock.adder64_wellFormed` checks the concrete artifact's dependency order, and `Flock.adder64_complete` proves that every assignment of the 128 input bits extends to a satisfying assignment. Completeness therefore does not stop at an unfulfilled witness-generation premise.

Artifact support, layout, and well-formedness are checked by `decide +kernel`, not `native_decide`. `Audit.lean` prints the transitive theorem axiom closures and fails on any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. No admitted theorem, native-decision axiom, or security premise is used.

## Rust interpretation and remaining trust

The generator consumes `Flock.adder64` directly. An artifact variable below 128 names an input bit: 0 through 63 are `x`, and 64 through 127 are `y`. Each later variable names the result of its ordered product. An affine zero or one becomes `Wire::ZERO` or `Wire::ONE`, affine addition becomes `Builder::xor`, and each row becomes `Builder::and`. Artifact outputs become the returned 64 output wires. Generated common-subexpression reuse changes XOR gate ordering, not affine meaning or the order of products.

`Builder` places ports before its constant pin and product slots. For the `Ld`/`Sd` shape, input bits occupy 0 through 127, output bits occupy 128 through 191, the constant pin is 192, and the 63 product slots occupy 193 through 255. The source's product variable 128 plus its ordinal maps to the corresponding Builder product, not to output slot 128 plus that ordinal. Builder output rows tie the committed output ports to the returned affine expressions. Structural zeros and unused port bits retain Builder's existing forced-zero interpretation.

The proven export boundary is the concrete Lean artifact and its GF(2) semantics. Lean's runtime execution, the Rust pretty-printer and formatter, the Rust compiler, and Builder's implementation of XOR, AND, constant pinning, output rows, and slot packing remain trusted parts of the Rust interpretation. Deterministic regeneration checks linkage and drift; it is not presented as a proof of these implementations. The existing packed native `address_rows` witness kernel is unchanged. Its correspondence to the generated circuit is exercised by the production memory witness regression and complete RV proof verification, but the Rust native word-arithmetic implementation itself is not formally verified here.

The RV regression `clean_adder_memory_addresses_wrap_and_carry` proves and verifies real `Ld`/`Sd` accesses through both a negative-immediate overflow and a long carry boundary, then rejects an altered output statement. The Flock reduction regression verifies honest batches and rejects mutations of input, output, constant, and product bits. This establishes exercised integration, not a cryptographic security proof of Flock, the PCS, Fiat-Shamir, or the whole VM. Other instruction circuits and protocol constraints are outside this adder proof.
