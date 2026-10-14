<h1 align="center">leanVM</h1>

<p align="center">
  <img src="./doc/images/banner.svg" alt="leanVM">
</p>

<h3 align="center">minimal hash-based zkVM, for post-quantum Ethereum</h3>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanVM.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
  <a href="./python-verifier/verifier.py"><img src="https://img.shields.io/badge/verifier-python-yellow?style=for-the-badge&logo=python&logoColor=white" alt="Python verifier"></a>
</p>

<table align="center">
  <tr>
    <td><a href="#xmss-aggregation">leanXMSS aggregation</a></td>
    <td align="right"><b>1.65K/s</b></td>
  </tr>
  <tr>
    <td><a href="#sphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>295/s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">leanDA commitment</a></td>
    <td align="right"><b>2 MiB/s</b></td>
  </tr>
</table>
<table align="center">
  <tr>
    <td><a href="#recursion">2-to-1 recursion</a></td>
    <td align="right"><b>0.27s</b></td>
  </tr>
  <tr>
    <td><a href="#hashing">hash compressions</a></td>
    <td align="right"><b>480K/s</b></td>
  </tr>
  <tr>
    <td><a href="#fibonacci">cheap cycles</a></td>
    <td align="right"><b>6,2M/s</b></td>
  </tr>
</table>

## security

leanVM is designed for security:

 * 128-bit ROM (64-bit QROM) soundness
 * no proximity gap conjecture
 * end-to-end formal verification
 * a traditional hash function

**warning**: Formal verification is [in progress](https://github.com/Verified-zkEVM/leanerVM). leanVM is not (yet) production ready.

## work in progress

Expect leanVM to change significantly:

* **hash**: BLAKE2s is a placeholder. SHA2, SHA3, BLAKE3 are actively considered.
* **ISA**: A migration from leanISA to RISC-V (rv64im) is planned.
* **zk**: Support for zero-knowledge is planned.

**note**: Prior to binary fields leanVM used [KoalaBear](https://crates.io/crates/p3-koala-bear) and [Poseidon](https://eprint.iacr.org/2019/458). The historical design is in [this branch](https://github.com/leanEthereum/leanVM/tree/koalabear).

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM)

**note**: The Metal GPU was not used.

### XMSS aggregation

The XMSS parameters are specified in [XMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/XMSS.pdf), with a [(ROM) security proof in Lean 4](https://github.com/leanEthereum/leanMultisig/blob/main/formal/xmss/XmssSecurity/Statement.lean).

```bash
cargo run --release -- aggregate --xmss 900 --log-inv-rate 1 --repeat 3
```

```
aggregation, 900 XMSS signatures
  cycles (VM steps)           : 995,578 = 2^19.925
    details                   : DEREF 2^17.878 (24.2%)  MUL 2^17.689 (21.2%)  SET 2^17.425 (17.7%)  BLAKE2S 2^16.989 (13.1%)  XOR 2^16.979 (13.0%)  JUMP 2^16.722 (10.9%)  MEMORY 2^20.674  BYTECODE 2^17.737  TOTAL_COMMITTED 2^25.801
  proof size                  : 317.4 KiB
  proving time                : 0.545 s ± 1.5%      peak memory 7.385 GiB
  per signature               : 1,651.687 signatures/s
  verifying                   : 3.977 ms
```

### SPHINCS aggregation

The SPHINCS parameters are specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/SPHINCS.pdf), with a [(ROM) security proof in Lean 4](https://github.com/leanEthereum/leanMultisig/blob/main/formal/sphincs/SphincsSecurity/Statement.lean).

```bash
cargo run --release -- aggregate --sphincs 245 --log-inv-rate 1 --repeat 3
```

```
aggregation, 245 SPHINCS signatures
  cycles (VM steps)           : 2,131,611 = 2^21.024
    details                   : XOR 2^18.951 (23.8%)  MUL 2^18.93 (23.4%)  SET 2^18.845 (22.1%)  DEREF 2^18.711 (20.1%)  BLAKE2S 2^16.992 (6.1%)  JUMP 2^16.543 (4.5%)  MEMORY 2^21.46  BYTECODE 2^17.737  TOTAL_COMMITTED 2^26.301
  proof size                  : 299.9 KiB
  proving time                : 0.831 s ± 3.6%      peak memory 9.275 GiB
  per signature               : 294.783 signatures/s
  verifying                   : 3.644 ms
```

### data availability

```bash
cargo run --release -- aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 2,989,506 = 2^21.511
    details                   : MUL 2^19.899 (32.7%)  XOR 2^19.809 (30.7%)  DEREF 2^19.138 (19.3%)  JUMP 2^18.299 (10.8%)  SET 2^16.787 (3.8%)  BLAKE2S 2^16.295 (2.7%)  MEMORY 2^21.695  BYTECODE 2^17.737 TOTAL_COMMITTED 2^26.695
  proof size                  : 324.0 KiB
  proving time                : 0.986 s ± 11.1%      peak memory 12.534 GiB
  blob throughput             : 16.235 blobs/s, 2.029 MiB/s
  verifying                   : 6.573 ms
```

### recursion

```bash
cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 XMSS signatures
  cycles (VM steps)           : 562,737 = 2^19.102
    details                   : MUL 2^17.823 (41.2%)  DEREF 2^16.964 (22.7%)  XOR 2^16.728 (19.3%)  SET 2^15.77 (9.9%)  JUMP 2^14.486 (4.1%)  BLAKE2S 2^13.932 (2.8%)  MEMORY 2^19.481  BYTECODE 2^17.737  TOTAL_COMMITTED 2^24.086
  proof size                  : 190.2 KiB
  proving time                : 0.272 s ± 5.3%      peak memory 8.388 GiB
  verifying                   : 3.457 ms
```

### hashing

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo test --release --package flock --test batch_proving_hashes -- hash_batch_prove_verify --exact --nocapture --include-ignored
```

```
Flock BLAKE2s batch proving, 262,144 compressions (2^18 slots)
  setup (preprocessing, excluded) :      0.0 ms
  witness-gen                     :     34.8 ms ± 26.8%   6.1%
  commit                          :    102.2 ms ± 1.3%   17.8%
  zerocheck                       :    244.9 ms ± 7.5%   42.6%
  lincheck                        :     20.2 ms ± 3.4%    3.5%
  pcs opening                     :    172.3 ms ± 1.3%   30.0%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    539.7 ms ± 3.3%   93.9%
  verify                          :      2.0 ms
  throughput                      :        485,765 compressions/s ± 3.3%
  (~3327.2 XMSS/s equivalent at 146 compressions/signature)
```

### Fibonacci

```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,880
    details                   : MUL 2^20.944 (98.9%)  SET 2^13.288 (0.5%)  DEREF 2^12.967 (0.4%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.96  BYTECODE 2^11.352  TOTAL_COMMITTED 2^25.26
  proof size                  : 286.0 KiB
  proving                     : 0.344 s ± 4.6%   6,181,087 cycles/s      peak memory 5.199 GiB
  verifying                   : 2.218 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))

## Clean circuits with SPARK

[`examples/clean-spark`](examples/clean-spark) is a standalone circuit-to-proof example, separate from leanVM's binary-field prover. [`clean/Main.lean`](examples/clean-spark/clean/Main.lean) defines `y = x*x + x + 5` over the BN254 scalar field using [Clean](https://github.com/Verified-zkEVM/clean), with Lean-checked soundness and completeness proofs. Clean's existing Circom backend exports the constraints and a WASM witness generator; the Rust adapter imports those constraints rather than reconstructing the circuit.

Prerequisites: `elan`/Lake, `rustup`, Node.js and npm, and a native C/C++ build toolchain. The example pins Lean, Rust nightly, Clean, ProveKit, WHIR, and npm dependencies; the first build downloads and compiles their dependencies.

```bash
cd examples/clean-spark
npm ci --ignore-scripts
(cd clean && lake exe cache get)
bash run.sh 3
```

The run computes `y = 17`, checks the generated witness against the exported binary R1CS, proves and verifies the R1CS using ProveKit's Spartan/WHIR implementation, then proves and verifies its actual matrix-evaluation query using [SPARK](https://github.com/worldfnd/provekit/blob/35324c0dc699947d6872639b22f3ae96a42b2a09/provekit/spark/SPARK.md). It also checks that verification rejects a changed public output, changed SPARK query, and tampered SPARK proof. Pass any canonical decimal BN254 scalar instead of `3`; arithmetic is modulo the scalar-field modulus.

Generated files stay in `examples/clean-spark/artifacts/`: `circuit.json` (snarkjs R1CS JSON), `circuit.r1cs` (binary R1CS), `circuit.wasm` (witness generator), `input.json`, `witness.wtns`, and `witness.json`. The signal order is `[1, y, x, x*x]`; both `y` and `x` are public. The generic Rust importer consumes BN254 R1CS JSON plus the decimal-string witness array, with constant one at signal zero and public outputs followed by public inputs. It checks the field, signal bounds, public prefix, and witness satisfaction. Clean rejects lookups and channel interactions that cannot be exported as R1CS.

```bash
# From examples/clean-spark, use already-exported artifacts:
cargo run --release --locked -- artifacts/circuit.json artifacts/witness.json --self-check
cargo test --release --locked
```

This is an in-process proving/verification example, not a persisted proof/key format. Native verification still evaluates the full matrices; SPARK is an additional verified proof, not yet a replacement for that step in a succinct composed verifier. Its setup is derived from the loaded circuit, not supplied by the proof. Backend minimum domains require zero padding even for this small circuit. The Lean theorem covers the circuit semantics, not the exporter or Rust cryptographic implementation; this example makes no end-to-end formal verification or full zero-knowledge claim.
