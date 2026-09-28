# AGENTS.md

## What this is

A native RV64IM virtual machine and field-native recursive SNARK for signature aggregation. LeanDA commitments and execution checks are implemented, but native DA proving is explicitly deferred. Proofs are not zero knowledge.

- `doc/leanvm/` is the LaTeX project describing the machine ISA and the snark that proves it. Its root is `doc/leanvm/main.tex`; build it with `cd doc/leanvm && latexmk -pdf main.tex`, which writes to the gitignored `doc/leanvm/.build/`. Sections live in `doc/leanvm/body/`, numbered `01`..`10` plus the lettered annexes `a` (ring switching), `b` (the PCS), `c` (Flock), and `d` (novel basis and additive NTT), and every symbol is defined once in `doc/leanvm/preamble/macros.tex`. If latexmk fails oddly (a bibtex error, or a missing `main.log`) right after inputs are renamed or `refs.bib` is edited, remove `doc/leanvm/.build` and rerun; it has not reproduced on unchanged inputs. **Drafting one section:** each section file carries a `% !TeX root` comment pointing at its generated driver in `doc/leanvm/drafts/`, so the LaTeX build key (`F5`, or the extension's `cmd+alt+b`) compiles only that section, numbered as in the full document and with cross-references and citations resolved against `.build/main.aux`; in `main.tex` the same key builds everything. Run `doc/leanvm/make-drafts.sh` after adding, renaming or renumbering a section.
- `doc/xmss/` is the standalone XMSS specification; `crates/xmss` implements its hash inputs and signature verification.
- `doc/sphincs/` is the standalone specification of the concrete SPHINCS+ instance used where statelessness matters; its root is `doc/sphincs/main.tex`, built the same way as `doc/xmss`, and implemented by `crates/sphincs`. It uses the same BLAKE2s primitive and target-sum encoding shape as XMSS, with its own tweak layout, target sum, and signing search.
- `formal/xmss/` and `formal/sphincs/` are Lean 4 proofs (over VCVio) of the ideal schemes' classical random-oracle security, `xmss_has_127_bits_of_classical_security` and `sphincs_has_127_bits_of_classical_security`; `formal/sphincs/` also proves correctness and completeness, `sphincs_is_correct` and `sphincs_is_complete`, stated in `SphincsSecurity/Completeness.lean`. Each project's `Scheme.lean`, under `XmssSecurity/` or `SphincsSecurity/`, contains the concrete parameters, the byte layout of every hash input, and the three algorithms; `Statement.lean` imports it and defines the SUF-CMA game, hash-query budget, and security claim. `lake exe cache get` once, then `lake build`.
- The one hash function is BLAKE2s, in `primitives::hash`: scalar, streaming, keyed, and a lane-transposed batched form for the PCS Merkle tree. RV64IM exposes compression through a proof-checked ECALL; the native recursion circuit constrains compression through Flock. The byte counter and final-block flags are ordinary compression inputs, so repeated compressions hash arbitrary byte strings.
- Application guests are Rust `no_std` programs targeting `riscv64im-unknown-none-elf`. `crates/guest` provides the runtime and cryptographic ABI; `scripts/build-guests.sh` compiles the bundled guests with nightly Rust and `rust-src`.

Primary uses:

- Aggregate XMSS claims grouped by epoch and message, and SPHINCS claims carrying individual messages.
- Recursively aggregate child proofs, proving every published claim is supported by a raw input or verified child. TODO: native LeanDA circuits and authenticated row coverage; do not count ignored DA proving workflows as verified.

## Layout

Dependency order, leaves first:

| crate             | role                                                                   |
| ----------------- | ---------------------------------------------------------------------- |
| `parallel`        | thread pool (below)                                     |
| `zk_alloc`        | proving arena (below)                                    |
| `primitives`      | field kernels (NEON/AVX), bit transposes, multilinear helpers, streaming stores, `bench` |
| `fiat_shamir` | `FiatShamirState` and prover/verifier transcripts |
| `pcs`             | additive NTT, Merkle, ring switch, stacked WHIR                    |
| `flock`           | batched R1CS over GF(2) for BLAKE2s: zerocheck + lincheck               |
| `lean_vm` | shared tables, buses, GKR, constraints and proving infrastructure |
| `guest` | `no_std` RV64IM runtime, ECALLs and portable field/hash operations |
| `guest_claims` | portable XMSS, SPHINCS and LeanDA reference verification |
| `riscv` | RV64IM execution, strict ELF loading, register and byte-memory traces |
| `riscv_proof` | packed RV64IM constraints, host prover and portable verifier |
| `recursion` | field-native circuits, fixed-key proofs and complete recursive verification |
| `aggregation_guest` | canonical claim codec, raw verification, coverage and deferred child binding |
| `xmss`            | XMSS over BLAKE2s; an independent leaf, consumed only by `rec_aggregation` |
| `sphincs`         | the stateless SPHINCS+ instance of `doc/sphincs`; an independent leaf, consumed only by `rec_aggregation` |
| `lean_da` | additive Reed-Solomon blob encoding, commitments, and membership vectors |
| `rec_aggregation` | recursive signature and DA aggregation: the guest, public entry points, and benchmarks |

`src/lib.rs` is the host public API: every crate above is `publish = false`, so new host-facing items are re-exported there. Guest programs use the separate `leanvm_guest` SDK. `src/main.rs` is the benchmark CLI and `tests/api.rs` exercises the public API. The aggregation guest is `crates/aggregation_guest/examples/aggregate.rs`; its implementation is `crates/aggregation_guest/src/lib.rs`.

## Building / Testing / Formatting

- `.cargo/config.toml` applies `-C target-cpu=native` only to host architectures and denies rustdoc warnings.
- Always use `--release` for VM tests and benchmarks.
- Build actual guest executables with `scripts/build-guests.sh`. It uses `cargo +nightly` and `-Z build-std=core,alloc`; install nightly with its `rust-src` component. Do not leak host compiler wrappers or flags into this build.
- **One integration test binary per crate, not one per file.** Arena-lifetime regressions need their own binary (`rec_aggregation/tests/arena_prove.rs`, `recursion/tests/arena_proof.rs`). Phases are process-global; concurrent resets reclaim each other's `ArenaVec`s. Run proof-heavy suites with `--test-threads=1`, both for phase safety and memory use.

An x86-only arm never compiles on an Apple dev machine, so a typo in one ships. Type-check the other target before pushing anything `cfg`-gated:

```bash
CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512vl,+vpclmulqdq,+pclmulqdq,+gfni,+avx2,+aes" \
  cargo check --release --workspace --target x86_64-unknown-linux-gnu
```

It needs `rustup target add x86_64-unknown-linux-gnu` and nothing else, since `check` does not link. The `apple-m4 is not a recognized processor` and `x87` notes are the pinned `target-cpu=native` and the bare cross ABI, not findings. To confirm an arm is really being reached rather than silently skipped, drop a `compile_error!` in it and watch the check fail.

```bash
cargo testall -- --test-threads=1  # release workspace tests, sequential proving
cargo clippyall                   # clippy, -D warnings
cargo docall                      # rustdoc, -D warnings
cargo fmt --all                   # max_width = 120
ruff format --line-length 150 python-verifier/verifier.py   # and `ruff check` it
```

Heavy benches and measurement harnesses are `#[ignore]`d; run by name with `-- --ignored --nocapture --test-threads=1`: `hash_batch_prove_verify`, `pcs_throughput`, `aggregate_three_levels`, `aggregate_statement_binds`, `aggregate_rejects_a_bad_signature`, `print_whir_query_counts`, `encoding_grinding_bits`. The native backend's ignored tests prove full RISC verification, full native verification, and same-key zero/one/two-child composition. Confirm that a filter actually selects its test.

## Benchmarking

The benchmarks we care about:

- `cargo run --release -- aggregate --xmss 900 --log-inv-rate 1 --repeat 3`
- `cargo run --release -- aggregate --sphincs 220 --log-inv-rate 1 --repeat 3`
- `cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3`

`aggregate` takes a count per scheme, both defaulting to zero, so either alone or a mix is one command; `recursion --sphincs-per-leaf` likewise puts both schemes in one tree. The CLI reports application execution separately from the native recursive proof. Raw signatures currently use one-signature leaves and binary folding. `aggregate --blobs` and `recursion --blobs-per-leaf` remain exposed, but DA aggregate proving is deferred pending native DA circuits.

## The proving arena (`zk_alloc`)

One proof is one **phase**, opened by the execution or native-circuit prover through `zk_alloc::enter_phase`. `ArenaVec` bumps a per-thread slab, a small block's release is at most a cursor pop while a large one is recycled (below), and the next phase reclaims everything. Not a `#[global_allocator]`: `raw_dealloc` picks arena-vs-system by address range, so with no phase open `ArenaVec` is an ordinary system vector.

**The rule:** an `ArenaVec` allocated in a phase dies at the next `begin_phase()`. A reset neither clears nor unmaps, so a buffer that outlives its phase reads the previous proof's plausible bytes, so the symptom is a proof that stops verifying, never a crash. Anything outliving a phase (a `Proof`, a cache, a table) must be a plain `Vec`. And **`drop` means something**: a large released block is handed back out within the phase (a per-thread free list, see the crate docs), so dropping a big buffer where it dies is worth doing, and a use-after-free the bump arena used to mask now reads another buffer's live data. Run `ZK_ALLOC_POISON=1 cargo testall` after changing buffer lifetimes; it fills released blocks and fills what a phase used when it ends, turning a silent wrong answer into a loud failure. That covers both shapes: a buffer read after being dropped, and a buffer that outlives its phase.

`setup_prover_without_arena` (or `lean_vm::init_prover_pool` alone) leaves the arena disengaged, sending every `ArenaVec` to the system allocator. It is the escape hatch for a host where even the recycled peak does not fit; on one that it does fit, the arena is faster, since its pages stay faulted in across proofs.

## The thread pool (`parallel`)

No rayon. Every parallel site is "N independent items, each writing its own disjoint slice", so the pool is a claim counter, not a work-stealing deque: `NUM_THREADS-1` workers plus the dispatcher inline, no per-dispatch allocation. Primitives: `for_each{,_chunk}`, `chunks_mut{,2,_zip}`, `Chunks`, `fill`, `map_collect`, `map_reduce`, `fold_reduce`, `map_reduce_with_state`, `find_first`, `SendPtr`.

- **Nested dispatch panics**, because it would deadlock the dispatch lock.
- **Both core clusters share one queue** (P at `USER_INTERACTIVE`, E at `UTILITY`); guided self-scheduling means a slow core claims fewer batches. Do not add a second pool: that was `primitives::epool`, now deleted.
- **The default holds back one performance worker when efficiency workers exist.**

`LEANVM_NUM_THREADS` sets the **performance**-worker count, leaving E-workers in place. `1` = strictly sequential.

## Three verifiers, one protocol

The execution and native-circuit protocols each have three verification paths. Any protocol change must land in the host verifier, Python verifier and constrained recursive verifier.

1. **Rust:** `riscv_proof::verify` verifies execution proofs; `recursion::Key::verify` verifies native circuit proofs.
2. **Python:** `python-verifier/verifier.py` independently implements both protocols. Interoperability is exercised by `riscv_proof/tests/python_verifier.rs` and `recursion/tests/native_python.rs`.
3. **Recursive circuits:** `crates/recursion/src/risc_verifier.rs` and `native.rs` express complete verification over an opaque field context. The same program runs concretely to collect advice and symbolically to build constraints.

The aggregation application does not execute a SNARK verifier. Its RV64IM guest validates canonical statements, checks raw signatures and coverage, and binds exact ordered child metadata using `leanvm_guest::deferred`. Child records contain statements, key digests and heights, not proof or ELF bytes. Guest execution alone does not authenticate those children.

`recursion::Recursor` verifies the mandatory execution proof and up to two native children. The root derives its trusted key from the actual expected application ELF. Every child has the same authorized key and a smaller height; a node's height is zero without children and otherwise one plus the maximum child height, with checked arithmetic. No program/key digest fixed point or unresolved polynomial claim remains for a host shortcut.

XMSS claims are grouped by epoch and message, while SPHINCS claims are key/message pairs. Both schemes count claims, not distinct keys. Coverage may be narrowed, but every supplied raw signature and child proof is still verified. Conflicting XMSS messages are rejected even if omitted from the published statement. Host prechecks are diagnostics, not soundness.

`aggregate_one_signer` is a small application proof check. `aggregate_two_to_one` and `aggregate_mixed_two_to_one` exercise composition. `aggregate_statement_binds` tampers with public transport; `aggregate_witness_binds_raw_signatures_and_declared_claims` and `native_recursion_authenticates_complete_child_statements` bypass host prechecks to test witness and child binding. Execution capacity is checked from actual table counts before constructing a full trace; do not replace capacity failures with silently smaller workloads.

## Conventions that bite

- **The prover can be memory-bandwidth bound.** Reduce memory traffic before assuming that more workers or fewer instructions improve throughput. `primitives::stream::Stream` publishes a buffer without the read-for-ownership an ordinary store pays, but ONLY where nothing reads the destination again before it is evicted. Where a consumer follows in the same pass, the fetch it avoids becomes that consumer's miss: fold kernels earn it by building their round message from registers, or by folding into an L1 stage first (`whir::fold_and_msg_blocks`). That fetch is an x86 cost only: on Apple silicon a store-only fill already sustains what a read-only pass does and `STNP` measures identical to `STP`, so `Stream` is a plain copy there and the L1 stage earns its keep for the read locality alone, which is still better than writing through.
- **NEON is the width ceiling on Apple silicon**, so an AVX-512 win that is purely width has no counterpart: the M4 has no SVE, and its SME2 is streaming-mode matrix work with no polynomial multiply. What does port is *shape*. A fused NTT pass wants a butterfly at a time over whole rows, not the register-resident tile the AVX-512 arms use: they transpose anyway and want to pay for it once per pass, while NEON transposes nothing and a tile leaves only its own width of independent work to cover the reduction's dependent PMULL folds, where a row leaves the whole lane count. Measured both directions: the tile costs the extension NTT, and costs the base encode's `Commit` again.
- **A `[F192; N]` in a NEON kernel is a memory object, where on AVX-512 it is the register.** Four tower products are four independent PMULL chains wanting most of the 32 vector registers, so an array of them spills and the spill costs more than batching the products saves; the same array is free on AVX-512, where the quad IS one register. Keep the quad as a tuple or as named values and let arrays exist only inside the batched-product helper, on the target that wants them (`flock::zerocheck::multilinear`'s `mul_quad`). The symptom is indirect, so suspect the shape rather than the arithmetic: the products measure the same either way, destructuring the results changes nothing, and forcing the helper to inline recovers almost none of it.
- **On Zen 4, 512-bit cross-lane data movement is half-rate** (every 512-bit shuffle is two 256-bit uops), so packing scalars into vector lanes with `vpermi2q`/`vpermq` and extracting with `vextracti64x4` loses to the scalar moves it replaces. Widening the arithmetic still pays: `mul4` beats the same products issued one at a time. Prefer kernels where both qwords of every 128-bit lane carry a product and nothing crosses lanes.
- Use comments only when necessary: uncommented but readable and simple code is better than commented slop. And when you use comments, be concise.
- **Never put a measurement in a comment, a doc comment, or this file.** Timings, throughputs, percentages and speedup factors go stale the moment the code, the compiler or the host changes, and nothing ever rechecks them, so they end up asserting something false with the authority of a comment. The commit message is where they belong: it is dated, it is immutable, and it says what was true when the change landed. A comment may say which way a result went and why (that a tile lost to whole rows, that one reduction beat another), never by how much.
- Commit tests only that are useful in the future, to prevent regressions / failures. Don't add trivial tests that will always pass.
- Simpler is better.
- **Fiat-Shamir:** `add_scalar`/`next_scalar` bind into the Fiat-Shamir state as a side effect. The public statement seeds the transcript at construction; the transport exposes no separate observe operation. Never re-observe data that rode the stream, which silently desynchronizes the two sides.
- **Prover and verifier derive layouts identically** from authenticated metadata and announced sizes. Schema, placement and commitment-shape changes must agree across Rust, Python and circuit verification. Preserve typed public coefficient sources through packed constraints rather than baking instance-specific values into circuit topology.
- **The L0 lane fold binds the committed witness's TOP `INITIAL_FOLDING_FACTOR` variables**, because lane `l` of the interleaved commitment is stack block `q[l·2^(μ-k) ..)`. `whir::commit` encodes only `StackShape::n_lanes` live lanes. A leaf image still has `2^k` words; missing lanes contribute leading zeros, and whole zero-prefix blocks share `hash::zero_prefix_state`. Compact openings carry only live words, while expanded witnesses supplied to circuit and Python verification carry the full image. Fold challenges arrive in round order, while transparent weights use witness coordinates: rotate the terminal point left by `k` before evaluating those weights. Per-level induced weights and the residual remain in round order.
- A guest panic exits unsuccessfully. Interpreter faults report their PC; use the actual ELF and its disassembly to locate the instruction. Guest source is ordinary Rust, not zkDSL, and memory is mutable and byte-addressed.
- **One symbol, one meaning, across the whole leanVM document.** Define notation in `doc/leanvm/preamble/macros.tex` and check that its letter is free. Read Annex B's symbol table before renaming. A sumcheck challenge is `\fc`; `\rho` is the rate, and `r` is a claim point. A notation rename must also update the Rust prover/verifiers, Python verifier and native verifier circuits wherever their names follow that notation.
- **Doc labels are an API.** `crates/pcs` cites `thm:rbr` and `thm:mca-johnson` by name and several crates cite `doc/leanvm/main.tex` sections, so renaming a label breaks those pointers with nothing to catch it. `doc/leanvm/body/NN-*.tex` prefixes match section numbers, so inserting a section renumbers the rest.
- **No em-dashes or en-dashes in prose**, anywhere a human reads it: docs, LaTeX, comments, commit messages. Restructure with a comma, colon, parentheses, or two sentences.
- **Never hard-wrap prose in Markdown or LaTeX.** One paragraph is one line; let the editor wrap it. Artificial line breaks make every later edit a reflow, so diffs show rewrapped lines instead of changed words. Applies to `.md` and `.tex` alike; code blocks, tables and list items keep their own line.

## Soundness

- In the recursion program, the prover transmits advice to the verifier, called "hints". Hints are untrusted witness data and must be checked by the verifier; a malicious prover must not be able to prove an invalid witness.

## Env knobs

| var                                                                                                     | effect                                           |
| ------------------------------------------------------------------------------------------------------- | ------------------------------------------------ |
| `LEANVM_NUM_THREADS`                                                                                    | performance-worker count; `1` = sequential       |
| `LEANVM_PROFILE`                                                                                        | per-stage prover timings                         |
| `ZK_ALLOC_STATS`                                                                                        | arena peak/phase, high water, overflow           |
| `ZK_ALLOC_POISON`                                                                                       | fill released arena blocks, to catch use-after-free |
| `BENCH_REPEAT`, `BENCH_COOLDOWN`                                                                        | `--repeat`/`--cooldown` for `#[ignore]`d benches |
| `LEANVM_HASH_N` | hash-chain workload size |
| `FLOCK_N_LOG`, `FLOCK_PROVE_TRACE`, `FLOCK_ZC_TIMING`, `LINCHECK_TRACE`                                 | flock batch size, stage traces                   |
| `PCS_LOG_N`, `PCS_LOG_INV_RATE`, `PCS_MIN_MU`, `PCS_SAMPLES`                                            | PCS throughput bench                             |
| `WHIR_TRACE`, `WHIR_NUM_VARS`, `WHIR_LOG_INV_RATE`                                          | WHIR NTT/Merkle split                        |
| `LEANVM_GUEST_ELF`, `LEANVM_FIBONACCI_ELF`, `LEANVM_HASH_CHAIN_ELF` | trusted application ELF overrides; otherwise bundled images are used |

## Side notes

- Grinding chooses the smallest valid nonce, including in parallel. Randomized signature inputs can still make proofs differ between runs.
