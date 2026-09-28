<h1 align="center">leanVM</h1>

<p align="center">
  <img src="./doc/images/banner.svg" alt="leanVM">
</p>

<h3 align="center">minimal hash-based zkVM, for post-quantum Ethereum</h3>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanVM.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
  <a href="./python-verifier/verifier.py"><img src="https://img.shields.io/badge/verifier-python-yellow?style=for-the-badge&logo=python&logoColor=white" alt="Python verifier"></a>
</p>

## Native RV64IM

leanVM proves execution of native RV64IM ELF programs compiled from Rust `no_std` guests. The machine has 32 integer registers, 64-bit integer arithmetic, and mutable byte RAM in `[0, 2^32)`. Native instruction decoding, executable fetch, register state, memory initialization, permissions, and chronological reads/writes are checked by the proof.

The proof system retains binary-field arithmetic, WHIR commitments, and Flock's BLAKE2s compression argument. Proof-field elements are not ISA words. Cryptographic ECALLs expose BLAKE2s compression and three-limb F192 multiplication with proof-checked inputs and outputs.

## Build

Install Rust through [rustup](https://rustup.rs/), including a nightly toolchain with the standard-library source:

```bash
rustup toolchain install nightly --component rust-src
./scripts/build-guests.sh
cargo build --release
```

The exact guest target is `riscv64im-unknown-none-elf`, a Tier 3 target. The script uses `cargo +nightly -Z build-std=core,alloc` with that target and the guest runtime/linker flags. It enables scalar unaligned-memory lowering because the VM supports misaligned data accesses; this does not add instructions outside RV64IM. There is no prebuilt target standard library to install as a replacement for `rust-src`. Do not substitute an `imac`, floating-point, or CSR-enabled target.

The workspace's default target remains the native host. Host Cargo builds can invoke the guest build script through their build integration; do not globally configure Cargo to build every crate for RISC-V.

## Rust guests

`crates/guest` provides the `leanvm_guest` SDK. A guest enables its `runtime` feature, uses `#![no_std]` and `#![no_main]`, links with `crates/guest/link.x`, and declares an entry with `leanvm_guest::entry!`. The entry function returns `u64`: zero exits successfully, while nonzero status or a panic fails.

The linker starts the image at `0x10000`, separates writable and executable segments, and reserves a 16 MiB stack below `2^32`. The bounded bump allocator does not reclaim allocations before exit. Calls use the RISC-V integer psABI.

| Service | `a7` | Arguments | Result |
| --- | --- | --- | --- |
| Exit | `0` | `a0`: status, required zero | Halt |
| Read witness | `1` | `a0`: destination; `a1`: byte length | Length |
| Read public input | `2` | `a0`: destination for 32 bytes | `32` |
| BLAKE2s compression | `0x100` | `a0`: 64-byte message; `a1`: 32-byte chaining value; `a2`: 16-byte metadata; `a3`: 32-byte output | `0` |
| F192 multiplication | `0x101` | `a0,a1,a2`: left operand limbs; `a3,a4,a5`: right operand limbs | Product limbs in `a0,a1,a2` |

All multibyte memory values use little-endian encoding. BLAKE2s inputs are read before output writes, including overlapping buffers. F192 multiplication uses registers only and returns the coefficients of `1, y, y²` in order. Witness bytes are untrusted: the guest must validate its application's claims before returning zero. Use the SDK's `Hasher` or `hash` for complete BLAKE2s hashing rather than treating compression as a complete hash API.

## Aggregation

The Rust aggregation guest verifies every raw signature and direct DA witness, checks coverage of the canonical declared statement, and binds the exact ordered child statements, authorized keys, and heights to its execution public input. Child proof verification runs in the dedicated field-native recursion circuit, not in the RV64IM guest. Supplied contributions are checked even when duplicated or omitted from the published statement.

### XMSS aggregation

XMSS claims group sorted public keys by epoch and message. Conflicting messages within one epoch are rejected. The signature parameters are specified in [XMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/XMSS.pdf), with a [ROM security proof in Lean 4](https://github.com/leanEthereum/leanMultisig/blob/main/formal/xmss/XmssSecurity/Statement.lean).

### SPHINCS aggregation

SPHINCS+ claims are sorted key/message pairs. The signature parameters are specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/SPHINCS.pdf), with a [ROM security proof in Lean 4](https://github.com/leanEthereum/leanMultisig/blob/main/formal/sphincs/SphincsSecurity/Statement.lean).

### Data availability

LeanDA uses additive Reed-Solomon encoding and a two-branch Merkle commitment. The guest checks the encoded matrix, derives its membership vector from the root, and checks every row's membership. Published statements retain the verified roots.

Native DA proving is deferred. The direct RV64IM DA computation currently exceeds the proof capacity, so blob aggregation does not yet produce a proof. TODO: add field-native DA circuits with authenticated row coverage, preserving the existing commitments and public API. DA verification/reference tests remain available; DA proof workflows are explicitly marked pending.

### Recursion

`crates/riscv_proof` contains the portable `no_std` execution verifier; `crates/recursion` implements `Recursor` and `NodeProof`. Every native node verifies one mandatory RV64IM execution proof and zero, one, or two native child proofs. Its nine public F192 fields encode four little-endian u64 words of the canonical statement digest, four words of the same authorized key digest, and a checked u32 height. Leaves have height zero; parents have one plus the maximum child height without overflow. The guest witness contains child metadata, not child proof bytes or ELF copies.

`Statement::digest()` hashes the statement domain and canonical encoding. `leanvm_guest::deferred` defines the public-field hash, ordered child-claim hash, and execution binding; `leanvm_aggregation_guest::public_input(&statement, &children)` constructs that binding. The root verifier builds `Recursor::new(&ProgramInfo)` from the trusted expected ELF. The resulting key authenticates the fixed circuit metadata and dataflow, rather than trusting a proof-provided circuit descriptor. Its digest is carried unchanged through children, so no program or key digest fixed point is required.

The native13 arithmetization has separate authenticated fixed and private WHIR commitments. It checks field-operation tables, dataflow, Flock matrix evaluations, ring switching, and complete authenticated openings. Each node completes the full execution verifier and each enabled child verifier in this circuit; host prechecks are diagnostics, not proof obligations discharged outside it.

The external `aggregate` API accepts at most 16 child aggregates and publishes at most 16 DA roots. Internal binary folding retains all intermediate claims before final selection, with capacity for 257 DA roots: 16 roots from each external child plus one direct whole-matrix commitment. Every duplicate or unpublished input remains checked, contribution and epoch bounds remain enforced, and a multi-row DA commitment is not split into different roots.

Execution proof transport remains `RV64PRF1`; native `NodeProof` transport uses `RVNODE01`. Aggregate transport uses `RVAGG002`, or `RVAGGO02` when public keys are supplied separately, with no legacy proof fallback. The guest input payload also uses `RVAGG002` but has its own witness codec. Parsing is not verification: malformed encodings, failed constraints, invalid openings, and unconsumed proof data are rejected.

## Security and status

leanVM is a research system and is not production ready. [Formal verification is in progress](https://github.com/Verified-zkEVM/leanerVM); this is not a claim of completed formal verification of the native RV64IM implementation.

The proof machinery targets 128-bit ROM soundness and 64-bit QROM soundness without a proximity-gap conjecture. These are design goals, not a substitute for an end-to-end security audit. Zero-knowledge support remains planned. BLAKE2s is the current hash function; alternatives are under consideration.

## SNARK machinery

- `GF(2^64)` commitment lanes and a degree-three, 192-bit binary extension field for challenges
- [WHIR](https://eprint.iacr.org/2024/1586) polynomial commitments
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching and M3 arithmetization influences, including [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504)

The [technical PDF](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanVM.pdf) is built from `doc/leanvm`. Prior to binary fields, leanVM used KoalaBear and Poseidon; that historical design is preserved on the [koalabear branch](https://github.com/leanEthereum/leanVM/tree/koalabear).
