# RV64IM migration status

## Status

The agreed leanISA replacement is implemented and verified: native RV64IM execution and proofs, Rust guest compilation, same-key field-native recursion, public aggregation APIs, and Rust/Python verification. Release workspace coverage was completed across the initial full run and targeted continuations/reruns after two fixes, not a single clean full-suite invocation. The heavy recursive/adversarial tests and actual CLI proof workflows passed. Proving performance remains a substantial limitation, quantified below.

The actual Rust target is `riscv64im-unknown-none-elf`. The user approved proof-checked cryptographic ECALLs, Rust `no_std` application guests, and dedicated GF(2^192) recursion circuits retaining BLAKE2s/Flock and WHIR.

**Explicitly deferred by the user:** native LeanDA circuits and authenticated row coverage. DA commitments and reference/execution checks remain available, but DA aggregate proving is not part of the current completion scope. DA proof regressions are explicitly ignored with that reason, rather than counted as passing. A DA-containing fixture in the final workspace run still failed capacity preflight at 28,043,507 cycles, requiring log 35 against a maximum of 28. No DA proof was produced.

## Implemented architecture

- `crates/riscv` implements RV64IM integer, multiplication, division and word instructions, strict ELF64 loading, sparse byte-addressed memory, register-zero semantics and instruction-fetch validation. The address space is 4 GiB, the initial stack pointer is its upper boundary, data accesses may be misaligned, and instruction addresses must be aligned.
- ECALLs provide exit, private witness input, fixed public input, BLAKE2s compression and F192 multiplication. The proof constrains cryptographic inputs and outputs. F192 multiplication uses registers `a0..a5` and returns three limbs in `a0..a2`; BLAKE2s uses its pointer ABI.
- `crates/riscv_proof` proves CPU, register, mutable byte-memory and tagged program-ROM consistency through packed GF(2) constraints, bus arguments, projection reductions, Flock, ring switching and WHIR. Its portable verifier is `no_std`. A counting pass rejects infeasible layouts before retaining a full trace or allocating witness tables.
- `crates/recursion` provides thirteen field-native table kinds, authenticated static wire identities and read counters, and separate fixed/private PCS commitments. Prepared keys and retained proofs use ordinary vectors so they survive arena resets. A native key is derived from the expected circuit, not accepted from the proof.
- Native verifier circuits constrain the complete GKR, table, Flock, ring-switch and WHIR verification protocols. One opaque-context program runs concretely to collect advice and symbolically to construct constraints. Inactive proof sources do not consume transcript data.
- `Recursor` verifies one mandatory RV64IM application proof and zero, one or two native child proofs. Nine public fields encode the statement digest, expected key digest and height. All children use the same authorized key. Height is zero without children and otherwise one plus their maximum height, with checked 32-bit arithmetic and strict descent.
- The aggregation guest binds its canonical statement and exact ordered child metadata through `leanvm_guest::deferred`. It checks raw signatures and claim coverage; it does not authenticate child proofs. Native recursion discharges those child claims, and the root verifier derives its expected key from the trusted actual application ELF. There is no host-verifier shortcut or program/key digest fixed point.
- The external fan-in remains sixteen; host folding produces binary internal nodes. Raw signature batching is conservative, one signature per leaf. Large complete proving benchmarks have not been measured by the capacity experiments below.

## Guest runtime and public cutover

- `crates/guest` contains the freestanding runtime, monotonic allocator, ECALL wrappers, streaming BLAKE2s and field arithmetic. `read_witness_vec` initializes allocated storage directly from the witness stream without an unnecessary zero-fill. Short reads cannot expose uninitialized bytes.
- The runtime supplies bounded RV64IM `memcpy` and `memcmp` implementations using the VM's misaligned word accesses. The compiled memory regression covers alignments, word/tail boundaries, unsigned ordering, destination guards, zero-length reads and truncated witness input.
- Canonical XMSS key arrays are encoded and decoded in bulk. Hashing consumes complete non-final blocks directly. Coverage borrows child data and scans sorted contributions instead of repeatedly searching copied claims. Canonical validation still occurs at every public boundary, including decoded guest input; private checked paths avoid repeating it.
- `scripts/build-guests.sh` builds the actual target with nightly Rust, `rust-src` and `-Z build-std=core,alloc`. It isolates host compiler/wrapper flags. `crates/rec_aggregation/build.rs` bundles the compiled guest ELFs.
- `EthereumProof` carries `recursion::NodeProof` at every level. Native node transport is `RVNODE01`; full and public-key-omitting aggregate transports are `RVAGG002` and `RVAGGO02`. Decoding is strict and does not replace verification. Old aggregate proofs are not accepted.
- `src/lib.rs` exports native execution through `leanvm::riscv`, direct execution proofs through `leanvm::proof`, and the migrated aggregation APIs. The Python verifier independently implements both execution and native circuit proof verification; native mode requires an expected key descriptor and public field values.
- Removed the zkDSL compiler, old CPU/ISA implementation, old recursive Python guest, and obsolete stacked-bytecode claim machinery. `lean_vm` remains shared proving infrastructure. Temporary proof and capacity profilers have been removed from the repository. `AGENTS.md` now describes the actual RV64IM/native-circuit architecture, build requirements and verification paths.

## Verified proof behavior

The final release validation confirmed these actual proof workflows:

- Native arithmetic/hash proofs and cached-key use across arena resets, including arena poisoning.
- A native proof of complete native-child verification: 2,926,568 wires, 27,605 BLAKE2s compressions, and rejection of an altered public claim.
- A native proof of complete RV64IM proof verification: 10,153,717 wires, 40,917 BLAKE2s compressions, and rejection of an altered public claim.
- Same-key zero-, one- and two-child proofs at heights zero, one and two, using private rates one and two. Altered statements, heights, proof scalars, missing/mismatched children, truncated encodings and trailing bytes were rejected.
- Compiled one-XMSS and one-SPHINCS aggregation leaves and a compiled two-child XMSS parent, through the actual benchmark CLI.
- Rust/Python interoperability for execution proofs and native proofs. Native coverage includes all thirteen schemas, extension-valued public fields, ring-free sparse commitments, and malformed public/key/proof/opening rejection.

The standalone heavy proof commands are:

```sh
ZK_ALLOC_POISON=1 cargo test --release -p recursion --lib -- --ignored --nocapture --test-threads=1
```

The aggregation statement-binding, invalid-signature and three-level regressions passed together: three tests, no failures. The raw-witness and complete-child-statement authentication regressions also passed, including an attack injecting an unpublished DA root without requiring DA proving. The non-DA public API workflow, no-arena proving, and retained-proof verification across poisoned arena resets passed.

## Large-parent capacity evidence

The latest throwaway experiment executed the compiled guest on canonical cached signer claims and counted the actual instruction, register and byte-memory tables. Child proofs were neither generated nor authenticated. These are execution/capacity results, not complete large aggregate proofs or throughput measurements.

| Parent claims | RV64IM cycles | Byte-memory events | Witness words | Required log |
|---|---:|---:|---:|---:|
| 900 XMSS | 189,609 | 494,267 | 114,442,096 | 27 |
| 1,800 XMSS | 374,922 | 955,169 | 228,590,448 | 28 |
| 220 SPHINCS | 246,847 | 676,141 | 219,259,376 | 28 |

All fit the existing maximum log 28. No PCS limit or soundness parameter was raised. Before these changes, the 900-XMSS parent required log 33; borrowed coverage, linear scans, bulk decoding/hashing and direct witness initialization removed that capacity failure.

The final workspace run also exposed a capacity regression in the unchanged 200,000-step wrapping-u64 Fibonacci workload: the guest required log 29. Advancing two terms per loop avoids register swaps while retaining all additions and the same result. The actual proof now uses 400,090 instruction cycles and 213,909,504 committed words, within log 28; proving and verification passed. Its boundary regression also checks an odd index after u64 overflow.

The obsolete architecture that executed a SNARK verifier inside RV64IM previously required log 38 for a one-child parent. That historical failure motivated the native recursion cutover; it is not a measurement of the current architecture.

## Repository validation

Passed after the relevant implementation changes:

- Guest hashing and coverage unit tests, including direct-block streaming/finalization and disjoint-child coverage regressions.
- The compiled memory-ABI regression.
- `cargo fmt --all` and `uvx ruff format --line-length 150 python-verifier/verifier.py`.
- `uvx ruff check python-verifier/verifier.py`.
- `cargo clippyall`.
- `cargo doc --release --workspace --no-deps --keep-going`, with warnings denied by repository configuration.
- The explicit x86 SIMD target configuration check.
- Full specification PDF generation with Tectonic, because `latexmk` is unavailable. The substantive layout overflows were fixed; bibliography underfull-box warnings remain.

The initial poisoned workspace run passed the non-DA public API and no-arena workflow, but stopped after two aggregation-crate failures. Both fixes passed targeted reruns: the child-authentication regression no longer requires a DA proof while still rejecting an injected unpublished DA root, and Fibonacci retains its original workload while fitting capacity. The aggregation library's other 27 tests passed in that initial run. Workspace coverage was then completed with the following passing commands; the excluded root package's integration workflows had already passed, and both excluded packages' doctests were checked separately:

```sh
ZK_ALLOC_POISON=1 cargo test --release -p rec_aggregation fibonacci -- --test-threads=1 --nocapture
ZK_ALLOC_POISON=1 cargo test --release -p rec_aggregation native_recursion_authenticates_complete_child_statements -- --test-threads=1 --nocapture
ZK_ALLOC_POISON=1 cargo test --release --workspace --exclude rec_aggregation --exclude leanvm -- --test-threads=1
ZK_ALLOC_POISON=1 cargo test --release -p rec_aggregation --test arena_prove -- --test-threads=1 --nocapture
cargo test --release -p leanvm -p rec_aggregation --doc -- --test-threads=1
ZK_ALLOC_POISON=1 cargo test --release -p recursion --lib -- --ignored --nocapture --test-threads=1
ZK_ALLOC_POISON=1 cargo test --release -p rec_aggregation --lib -- --ignored --nocapture --test-threads=1 aggregate_statement_binds aggregate_three_levels aggregate_rejects_a_bad_signature
```

Proof-heavy tests run sequentially because both memory use and the process-global proving arena make concurrent proving inappropriate here. A passing ignored-test filter must execute its named test, not merely report zero selected tests.

## Measured CLI proof performance

These actual CLI runs used the current implementation on the AMD Ryzen 9 7950X3D host, with one measured repetition after warmup. They are smoke measurements, not a statistically sampled comparison against leanISA. All resulting proofs verified.

| Workload | Private log inverse rate | Proving | Verification | Process peak memory |
|---|---:|---:|---:|---:|
| One XMSS signature | 1 | 50.624 s | 5.373 ms | 35.588 GiB |
| One SPHINCS signature | 1 | 167.169 s | 5.218 ms | 35.785 GiB |
| Two-child parent, one XMSS signature per child | 2 | 10.494 s | 4.927 ms | 40.880 GiB |

The parent timing excludes preparing its two child proofs; process peak memory does not. Signature proving includes the RV64IM execution proof and native wrapping. Commands:

```sh
cargo run --release -- aggregate --xmss 1 --log-inv-rate 1 --repeat 1
cargo run --release -- aggregate --sphincs 1 --log-inv-rate 1 --repeat 1
cargo run --release -- recursion --n 2 --xmss-per-leaf 1 --log-inv-rate 2 --repeat 1
```

Raw signatures currently use separate leaves, so workloads containing many signatures generate many execution and folding proofs. This is a functional migration, not a throughput-equivalent replacement. The initial aggregation-library validation took 11,755 seconds, and the three ignored adversarial/three-level tests took 2,775 seconds combined. These are test-batch wall times, not individual prover timings. The large-parent capacity experiment above does not establish complete large-workload proving throughput.

## Recursion research retained

The user selected field-native recursion after investigations of primary sources pinned to SP1 `9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b` (circuit version v6.1.0) and OpenVM `46df938dfd52e88e3ca8eeada6f8a2cecd761cac`.

- [SP1's recursion compiler](https://github.com/succinctlabs/sp1/blob/9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b/crates/prover/src/recursion.rs) generates a native-field recursion program rather than a RISC-V ELF, with static addresses/read multiplicities and authenticated preprocessed metadata.
- [OpenVM's recursion design](https://github.com/openvm-org/openvm/blob/46df938dfd52e88e3ca8eeada6f8a2cecd761cac/docs/crates/recursion/README.md) uses protocol-specific AIRs and buses for verification and authenticated preprocessing, rather than ordinary RV32IM execution.
- Both avoid generic register/byte-memory histories for every algebraic temporary. Their prime-field formulas and parameters were not copied into the binary-field protocol. No cross-system speedup factor was measured.

Static reviews did not identify a concrete soundness defect in their reviewed versions. They are not formal proofs and do not replace adversarial execution/proof tests.

## Remaining explicitly deferred work

TODO: implement native LeanDA circuits and authenticated row coverage while preserving existing commitments and the public API. Keep the deferred DA proof workflows distinguishable from verified signature aggregation.
