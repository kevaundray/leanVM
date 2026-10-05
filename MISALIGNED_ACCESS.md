# Misaligned loads and stores in leanVM (issue #301)

Decision: stopped at the pricing gate (step 2). Nothing was implemented and no PR was opened. Built with `-C target-feature=+unaligned-scalar-mem`, every guest makes zero misaligned accesses at run time. They all run, prove and verify on today's leanVM, which traps on any misaligned access. On every tracked program the flag leaves the proven table heights and committed words exactly unchanged. Supporting misaligned access would cost leanVM a protocol change and save nothing on its workloads.

Baseline: `upstream/riscv-exploration` at `f774828d` (#478). Guests use their pinned `nightly-2026-10-03`.

## 1. How ZisK supports misaligned access

Source read at ZisK `main`, commit [`78179eb9`](https://github.com/0xPolygonHermez/zisk/commit/78179eb919f053b649daa367ba34223c7ed1a747).

**Transpilation and emulation.** The transpiler never branches on alignment. `ld` becomes one `copyb` with indirect width 8, `lw` one `signextend_w` with width 4, `sd` one `copyb` store with width 8 ([mapping](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/transpilers/riscv/src/riscv2zisk_context.rs#L217-L233), [builders](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/transpilers/riscv/src/riscv2zisk_context.rs#L1116-L1175)). The emulator reads and writes any in-range byte address on a byte buffer. For the proof trace it records the aligned word or words an access touches, and for a store their old values ([mem.rs](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/core/src/mem.rs#L337-L358), [read path](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/emulator/src/emu.rs#L598-L608), [store path](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/emulator/src/emu.rs#L1197-L1207)).

**Routing.** The main state machine sends `(op, byte address, step, width, value)` on the memory bus, with the width bound to the instruction ROM ([main.pil](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/main/pil/main.pil#L364-L398), [ROM binding](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/main/pil/main.pil#L583-L587)). In ZisK "aligned" means width 8 at an address divisible by 8. Only those accesses go straight to the aligned memory machine. Everything else, a naturally aligned `lw` or `sb` included, goes through the MemAlign machine, which consumes the main tuple and emits aligned width-8 tuples on the same permutation bus ([helpers](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/mem-common/src/mem_helpers.rs#L56-L79)).

**Cost per access** ([collector](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/mem/src/mem_align_collector.rs#L89-L117), [ROM programs](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/mem/src/mem_align_rom_sm.rs#L1-L20)):

| access | aligned memory operations | MemAlign rows |
|---|---:|---:|
| width 8 at a multiple of 8 | 1 | 0 |
| narrower, inside one word, read | 1 read | 2 (RV) |
| crossing two words, read | 2 reads | 3 (RVR) |
| narrower, inside one word, write | 1 read + 1 write | 3 (RWV) |
| crossing two words, write | 2 reads + 2 writes | 5 (RWVWR) |

Byte reads, and byte writes whose value has no high bits, take a one-row `MemAlignByte` variant instead ([routing](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/mem/src/mem_align_collector.rs#L68-L92), [byte AIR](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/mem/pil/mem_align_byte.pil#L57-L99)). The aligned memory machine packs several operations per physical row ([mem.pil](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/mem/pil/mem.pil#L43-L60), [configuration](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/pil/zisk.pil#L88-L106)), so the operation counts above are not physical rows.

**Soundness.** MemAlign range-checks eight byte columns, carries the selected bytes across adjacent rows, rebuilds both the aligned words and the requested value, zeroes the bytes beyond the width on a load, and keeps the untouched bytes of a store. A lookup into a fixed 256-row ROM binds `(pc, delta_pc, delta_addr, offset, width, flags)`. That lookup enforces the legal widths and offsets, the program's control flow, and the neighbouring word's address. An aligned write uses the read's step plus one ([mem_align.pil](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/mem/pil/mem_align.pil#L116-L262), [mem_align_rom.pil](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/mem/pil/mem_align_rom.pil#L4-L36)). The aligned memory AIR sorts the accesses and enforces read consistency ([mem.pil](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/mem/pil/mem.pil#L640-L698)). A misaligned access adds no main-machine step. Every main row still carries the indirect width, the width-bearing bus expression and its ROM binding, and the memory clock reserves four slots per main step, partly for the unaligned read-modify-write ([columns](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/main/pil/main.pil#L150-L158), [timestamps](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/state-machines/main/pil/main.pil#L237-L243)). ZisK's book documents the alignment classes ([profiling.md](https://github.com/0xPolygonHermez/zisk/blob/78179eb919f053b649daa367ba34223c7ed1a747/book/developer/profiling.md#L537-L548)).

So in ZisK every sub-word access already goes through MemAlign. A misaligned access is a different ROM program on hardware the machine pays for anyway, and its marginal price is low.

## 2. Other zkVMs

All four require natural alignment:

- **SP1** asserts natural alignment for `lh/lw/ld/sh/sw/sd` in its executor ([source](https://github.com/succinctlabs/sp1/blob/616af25c7efa08754bfbe1f836bf5409e18d010d/crates/core/executor/src/minimal/arch/portable/mod.rs#L1263-L1314)).
- **OpenVM**'s rv32im load/store supports only naturally aligned accesses and panics with "unaligned memory access not supported" otherwise ([source](https://github.com/openvm-org/openvm/blob/f08bf2836409f3c0a5f6b6cfe73eb177a8a3e8c8/extensions/rv32im/circuit/src/loadstore/core.rs#L376-L420)).
- **Jolt** proves alignment. `lw` expands with `assert_word_alignment`, and `sw`'s masked update asserts it too ([load](https://github.com/a16z/jolt/blob/c44bfd7dc0d0ea765fb064b8231d59c740789aaa/crates/jolt-program/src/expand/memory/shared.rs#L102-L128), [store](https://github.com/a16z/jolt/blob/c44bfd7dc0d0ea765fb064b8231d59c740789aaa/crates/jolt-program/src/expand/memory/sw.rs#L3-L16)).
- **RISC Zero** raises `LoadAddressMisaligned` and `StoreAddressMisaligned` ([source](https://github.com/risc0/risc0/blob/3bbcd44d6459b9ef6ac0df3846dc9215514934e8/risc0/circuit/rv32im/src/execute/rv32im.rs#L510-L576)).

## 3. What ere-guests #78 changed

[eth-act/ere-guests#78](https://github.com/eth-act/ere-guests/pull/78) adds `-C target-feature=+unaligned-scalar-mem` to `ERE_RUSTFLAGS` for the ZisK builds of the ethrex and reth stateless block validators ([workflow](https://github.com/eth-act/ere-guests/blob/ce4b8a4a51a00e56c76deec77b0ca036bc1a9911/.github/workflows/compile-and-release.yml#L25-L100)). Its "14%" is a `ziskemu` cost figure. The PR publishes no before or after numbers, input block or command.

The flag is LLVM's [`FeatureUnalignedScalarMem`](https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/RISCVFeatures.td#L2023-L2026): unaligned scalar loads and stores are fast. With it, LLVM lowers an access through a pointer of unknown alignment (a `u32::from_le_bytes` over a `&[u8]`, an inline `memcpy` of a byte slice) to one `lw`/`ld` instead of a sequence of `lbu`, shifts and `or`s. EVM code is byte-oriented throughout: Keccak over byte strings, RLP, big-endian `U256` from bytes, byte-slice copies. In ZisK each of those byte loads costs a main step plus a MemAlign row, so the flag pays off there. [INFERENCE: #78 does not say which routines the 14% came from.]

## 4. Pricing (the gate)

Method: built every guest twice into scratch target directories, once as upstream and once with the flag added to the eight identical `.cargo/config.toml` files. Ran `cargo leanvm bench --cycles-only` on each set with an uncommitted counter printing `Stats::base_counts` (exact rows per table). Added the four small guests at the verifiers tests' inputs: `blake2s` and `preimage` raised to 50,000 bytes, `fibonacci` 5,000, `numbers` as in `numbers_guest`.

**Run-time misaligned accesses: zero, in every guest.** The interpreter was left unmodified. It traps on any misaligned load or store (`Machine::cell`, `Trap::Misaligned`), and every flagged guest ran to completion. On the flagged ELF files, the three workload hosts' tests pass (guest output equals the native computation), and `verifiers` `guests::` passes 9 of 9 (fibonacci, blake2s, hash, preimage and numbers proven and verified, the block-boundary interpreter checks, and the ELF parsing tests). Free misaligned access would therefore change nothing: these binaries already have nothing misaligned to execute.

Static code: the instruction count changes by 0 to 8 per guest, except `blake2s` at 971 to 798.

Exact counts, upstream vs flag (rows per table are `base_counts`; proven rows and committed words as `bench` reports them):

| program | cycles | change | rows that change | proven rows | committed words |
|---|---:|---:|---|---:|---:|
| leanXMSS, 400 signatures | 799,582 to 798,374 | -1,208 (-0.15%) | LD -1,604, SD +397, ALU -1 | 983,112 = | 42,089,336 = |
| leanSPHINCS, 104 signatures | 973,297 to 973,089 | -208 (-0.02%) | ALU -208 | 1,212,488 = | 50,084,728 = |
| leanDA, 1 blob | 643,615 to 643,613 | -2 | ALU -2 | 852,608 = | 31,812,640 = |
| hash, 50,000 bytes | 703,470 to 703,468 | -2 | ALU -2 | 918,568 = | 39,788,984 = |
| Fibonacci asm, 2,000,000 | 2,004,006 | 0 | none | 2,097,328 = | 71,318,763 = |
| blake2s guest, 50,000 bytes | 3,278,388 to 3,147,007 | -131,381 (-4.0%) | LOAD -50,050, ALU -43,795, SHIFT -43,793, LD +6,257 | 3,997,728 = | 133,989,680 = |
| preimage, 50,000 bytes | 600,310 to 600,308 | -2 | ALU -2 | 762,936 = | 24,178,088 = |
| fibonacci guest, 5,000 | 30,130 | 0 | none | 32,944 = | 1,416,416 = |
| numbers | 6,049 | 0 | none | 7,664 = | 561,248 = |

The two leanXMSS-400 aggregation trees are unchanged too: a leaf's shape is its proven table heights, which are equal.

The only real change is in the `blake2s` guest, a plain-Rust BLAKE2s demo, not a workload. Its `compress` reads the message block with `u32::from_le_bytes(block[4 * i..4 * i + 4])` from `&[u8; 64]`. With the flag, LLVM turns the 64 `lbu` with their shifts and `or`s into 8 `ld` per block. The block happens to be word-aligned at run time, so not one of those `ld` is misaligned. Even this 4% does not cross a power of two in any table. The workloads already keep values as `u64` words, never byte arrays, as AGENTS.md prescribes, so the flag finds nothing to rewrite in them.

**What supporting it would cost.** The class is fixed per instruction in the public bytecode, but alignment is known only at run time. There are two ways to prove a misaligned access:

- **Let every memory row reach two cells.** LD/SD/LOAD/STORE rows would each carry a second RAM tuple (old value, new value for a store, previous timestamp), a wider clock stride, and byte split and merge logic in the circuit. LD's and SD's circuits are 2^8 bits per row today, against LOAD's 2^10. At leanXMSS 400, LD and SD are 2^18 rows each and account for 51.6% of its cycles, so each column added to both costs 2^19 = 524,288 committed words, 1.25% of its 42,089,336. Several columns and a larger circuit would add several percent of committed words to every workload, for a gain of zero.
- **A separate misaligned table** that a pc may take besides its own class. The bytecode lookup would have to admit one pc in two tables. The aligned rows would pay little, but the protocol would grow a table, a clock and a lookup path in the prover, both verifiers, the in-rows verifier and the spec, and the gain would still be zero.

## 5. Why ZisK's 14% does not transfer

- **The workloads.** ere-guests are EVM block validators: byte strings, RLP, Keccak, `U256` from bytes, unaligned `memcpy`. leanVM's guests are designed around `u64` words, with hashing through the `blake2s` precompile on word blocks. LLVM finds almost nothing to widen in them, and nothing it widens is misaligned at run time.
- **The cost models.** In ZisK every sub-word access already pays a MemAlign row, so turning eight byte loads into one wide load saves main steps and MemAlign rows, and a misaligned access reuses machinery that is paid for anyway. leanVM proves a byte load in the LOAD table, one row and one cell. It has no alignment machine to reuse, so a misaligned access would need new machinery.
- **The metric.** The 14% is `ziskemu` cost, an emulator-side estimate. leanVM's comparable figures, its proven table heights and committed words, are exactly unchanged here.

## 6. Decision and remaining notes

- No implementation, no measurement of proving time (the gate rules it out: the proven heights and committed words, which fix the prover's work, are identical), no PR. Branch `kw/misaligned-access` is kept local at `upstream/riscv-exploration` with no commits, and nothing was pushed.
- ACT4 is unchanged. Claiming misaligned support would mean setting the UDB's misaligned-access parameters in `conformance/act4/leanvm-rv64im.yaml` and `rvmodel_macros.h`, dropping the `Misalign` exclusion in `test_config.yaml`, and regenerating the ELF files with Docker (`conformance/act4/generate.sh`).
- Do not adopt the flag on the current VM. It permits LLVM to emit misaligned accesses, which leanVM traps on: no proof, never an unsound one. Today's guests happen never to do one, but nothing guarantees that for other inputs or other code. The flag's one visible gain, in the `blake2s` guest, comes just as well without it, by reading the block as words, as AGENTS.md prescribes.
- Suggested reply on #301: leanVM keeps trapping on misaligned access (no proof, never an unsound one). Guests should not be built with `+unaligned-scalar-mem`, since it saves nothing on word-oriented guests.
