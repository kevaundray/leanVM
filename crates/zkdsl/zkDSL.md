# The guest language (leanVM)

The guest, the recursive verifier the prover runs, is written in Lean, as a DSL embedded in Lean: a guest function is a term of the builder monad `B` (`formal/lean_vm/LeanVM/Dsl/Builder.lean`), and elaborating it gives the core IR the verified back end compiles (`formal/lean_vm/LeanVM/Compiler/`), with the allocation trace placement follows. There is no parser and no source text: what the zkDSL decided at compile time is Lean evaluation, and the end theorems are about the compiled bytecode. The target is the leanVM ISA: six instructions (`XOR`, `MUL`, `SET`, `DEREF`, `JUMP`, `KECCAK`) over the binary field GF(2^128), with write-once memory and all indices carried "in the exponent" as powers of a fixed generator. For the VM and the proving system, see [`doc/leanvm/main.tex`](../../doc/leanvm/main.tex).

Where things are:

- the guest: `formal/lean_vm/LeanVM/Guest/Program/`, one module per section, its configuration `Guest/Program/Config.lean` (each placeholder the prover computes, `crates/aggregation/src/placeholders.rs`'s `placeholder_map`, read from the generated `Guest/Data/Placeholders.lean`, and the guest's own constants), its function list `LeanVM.Guest.Program.program` (`Guest/Program.lean`);
- the builder: `LeanVM/Dsl/` (`Builder`, `Control`, `Mem`, `Hints`, `Keccak`, `Fold` for constant folding, `Notation` for the surface syntax), and `Dsl/Program.lean`, which elaborates a function list in the compiler's order (`assemble`);
- test programs: `formal/lean_vm/tests/LeanVMTests/Programs/` (`Basic.lean` the compiler's test programs with their public input and witness streams, `Vm.lean` the VM's and the prover's, `Chain.lean` the verifiers' fixture, `Snippets.lean` the aggregation tests' `main`s over guest functions), compiled by `lake exe guest-backend export programs|snippets` into `crates/zkdsl/tests/compiled/` (`<name>.txt`, `<name>.inputs`) and `crates/aggregation/snippets/`;
- this crate: the disassembler (`disassemble`, the `DBG_DISASM` workflow); its tests prove and run the compiled test programs on the stable prover.

After a change to the guest, `formal/lean_vm/scripts/regen-guest.sh` writes the compiled guest (`guests/lean_ethereum.compiled`, not committed), its core digest (`guests/lean_ethereum.digest`, committed: the prover refuses an artefact whose input digest does not match it) and every file derived from it (`formal/AGENTS.md`, "Changing the spec").

## The field, and indices in the exponent

`K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` and `E = K[y]/(y^2 + x*y + 1) = GF(2^128)`, a word `c0 + c1*y` with `c0, c1 ∈ K`.

Machine **words** (a memory cell, an immediate, a hashed value) are elements of `E`. **Addresses**, the program counter, the frame pointer, the `JUMP` condition and the read counters live in the subfield `K`. There are no runtime integers:

- `+` is field addition, bitwise **XOR** (`x + x == 0`); `*` is multiplication in `E`; `a / b` is one `MUL` whose quotient the prover solves for (`quotient · b == a`, so never divide where both can be zero);
- `GEN` is the generator `g = x` of `K^×`, and `GEN ^ k` the constant `g^k` (`Ex.g k`). A logical index `i` is carried as `g^i`: incrementing is one multiplication by `GEN`, and memory addresses are g-powers;
- a word literal is `litField n`, the word whose two limbs the bits of `n < 2^128` spell, so `5` is `1 + x^2` and `2^64` is `y`; `gpowE k` is `g^k` as a word.

Compile-time arithmetic is Lean's: a size, an offset, a loop count or a `Const` argument is a Lean `Nat`, folded by Lean, and a constant word is a Lean `E`. The zkDSL's two regimes (integer in an index, XOR in a value) are gone: a `Nat` is never a word unless the program says which word.

## Functions and programs

A function is a `GFn`: its name, its argument and return cell counts, and its body from the parameters' values to the returned ones. A compile-time parameter is a Lean argument: `verifyMerkleCap (depth : Nat) : GFn` is a family, one guest function per argument, named as the zkDSL named a specialization (`instName "verify_merkle_cap" [.L depth]`). What `@inline` was is an ordinary Lean function returning a `B` action, emitting into its caller's frame; `unroll` is a Lean `for`.

A program is a list `(name, functions)`: `main` first, each entry a function with the `Const` instances it reaches. `Dsl.Program.assemble` elaborates every listed function, orders them as the compiler's queue does (the listed ones, then each one's callees in the order its body names them), names each loop helper `__loop{k}` in that order, and fails on a callee nothing elaborates, a listed function nothing reaches, or two functions of one name. A function is called by name: `call f [a, b]`, `call1 f [a, b]` (one value), `callN f [a, b] n`, `B.dispatch x fs args n` (a fused `match` of calls).

## Public input

Memory cells `m[0]` and `m[1]` hold the two public-input words. A program publishes results by storing them through the pointer `g^0`, the write-once store asserting them against the public input (`publish` in `Programs/Support.lean`):

```lean
let p ← B.const (gpowE 0)
B.store p 0 a      -- m[0] = a
B.store p 1 b      -- m[1] = b
```

A test program declares its public input and streams as Lean data (`TestProgram.publicInput`, `streams`), written beside its compilation as `<name>.inputs`.

## Memory

All memory is **write-once**: a second write of the same value is a no-op, of a different value a proof failure, which turns stores into equality assertions. A cell nobody writes is unconstrained (zero in witness generation): don't read one. Witness generation runs forward, so a value must be written before it is used.

- `B.heap n` (`HeapBuf n`): a fresh heap region, its pointer a g-power; word `k` lives at `p · g^k`. `p[GEN ^ k]` (or `HeapBuf.get`, `B.load p k`) is one `DEREF`, the compile-time offset folded into the address; a runtime index `p[i]` costs one more `MUL` for `p · i`. `B.heapBufDyn size` takes its size in the exponent of a runtime value.
- `B.stackBuf n` (`StackBuf n`): `n` consecutive frame cells, read for free (`r[k]`) and written by one instruction (`r[k] := e`); slices `r[lo:hi]`. `B.addr r` names a run as a pointer, for runtime indexing.
- Heap slices for hints and Keccak are `HeapBuf.slice` or `.heap p lo len`; a runtime start `B.sliceRt p i off len` costs one `MUL`.

## Control flow

- **Loops in the exponent**: `B.loopConstF lo hi ncaps caps body` walks a counter from `g^lo` to the exclusive `g^hi`, `B.loopRtF lo hi …` to a runtime g-power bound (range-check it first, or the walk need not terminate). The body becomes a tail-recursive helper; its captured values (`caps`) are passed explicitly, by value, one argument each, and nothing else carries a value into or out of the loop: carry state through the heap.
- **Compile-time repetition**: a Lean `for`, with zero loop overhead.
- **Branches**: `B.ite c zero nonzero` on a value `c` in `K` (`zero` runs at `c = 0`), `B.ite0` with no other block; a test `a == b` is `c = a + b`, one `XOR` and one conditional `JUMP`. Each block is a scope of its own: a cell written only in a branch is not reused after the join.
- **`match`**: `B.match_ x targets arms` runs arm `j` at `x = g^j` through a jump table in `main`'s frame (3 cycles, whatever the arm count), each arm writing the target cells; arms cover `0 ..< n` with no default. Nothing bounds `x`: range-check a hinted scrutinee first. A `match` whose arms all call one family on the same arguments is `B.dispatch`, which builds the callee frame once and jumps into the selected instance.

## Assertions

| construct | cost | meaning |
|---|---|---|
| `assert a == b`, `B.assertEq` | 1 `MUL` | write-once double write |
| `assert a != b`, `B.assertNe` | 3, no branch | `x = a + b`, a hinted inverse, `x · inv = 1` |
| `assert log x < n`, `B.rangeCheck x n` | 3 (+1 `SET` per bound per frame) | `x = g^e`, `e < n`, by two `DEREF`s and the complement's `MUL` |
| `B.rangeCheckRt x b` | 4 | the same at a runtime bound `b = g^n`: check `b` itself first (`B.assertGpow`) |
| `B.assertInK a b` | 1 untaken `JUMP` | both words in `K` |
| `B.assertGpow x` | 1 `DEREF` | `x = g^e` with `e` below the memory size |

## Keccak

`B.keccak a b out (tail := …) (len := …) (padTail := …)` is one `KECCAK`, the Keccak-256 of at most 128 bytes (`a ‖ b ‖ tail`, the first `len` bytes); `B.keccakDuplex a b out cap` the Fiat-Shamir duplex step in overwrite mode; `B.keccakCells cells out (state := …) (len := …) (final := …)` a message of any compile-time length, one `KECCAK` a 136-byte block. Operands are words already computed (`.words [.cell v, .const c, .zero]`), frame runs (read in place) or heap slices (one `DEREF` a cell). `out` receives the first 1, 2 or 13 cells of the state; if it is already written, the hash becomes an assertion. The padding run `[0x01, 0, 0, 0, 0]` is set once per scope.

## Hints

Hinted values are **unconstrained**: the program must pin every one (asserts, range checks, hashes), and the builder types them `Hinted` until a check (`B.assertBit`) gives them a fact.

- `B.witness "name" dest`, `B.witnessCell "name"`: the next entry of a prover stream, at zero cycles;
- computed advice: `B.hintBits`, `B.hintBitsExpTo`, `B.hintDigitsExp`, `B.hintWindowsExp`, `B.hintLog2Ceil`, `B.hintLimbs`.

## Cost cheat sheet

| construct | instructions |
|---|---|
| a constant word, `GEN ^ k` | 1 `SET` (pooled: once per scope) |
| `a + b` | 1 `XOR` |
| `a * b`, `a / b` | 1 `MUL` |
| heap read or store | 1 `DEREF`; +1 `MUL` for a runtime index |
| frame read `r[k]` | 0; a store is 1 |
| `ite` | 3 (+2 to skip a non-empty other block; +2 per branching function for its frame pointer) |
| `match_` | about 7 with the join; `dispatch` arms just `SET` and `JUMP` |
| function call | about `n_args + n_returns + 4` |
| loop iteration | body + about 1 `MUL` + 1 `XOR` + the call |
| `keccak` | 1, plus the padding run once per frame, 1 `XOR` per nonzero cell of a later block, 1 `DEREF` per heap cell |
| a hint | 0 |

## Example

Fibonacci in the exponent (`fibonacci` in `Programs/Basic.lean`): `fib[g^k]` holds `g^F_k`, so one `MUL` is one step.

```lean
def fibonacci : TestProgram where
  name := "fibonacci"
  publicInput := [gp 89, gp 89]
  program := [("main", [mainOf do
    let fib ← B.heap 12
    fib.put 0 (← k (gp 0))
    fib.put 1 (← k (gp 1))
    B.loopConstF 0 10 1 (pure [fib.p.v]) fun i caps => do
      let q ← B.mul (cap caps 0) i
      B.store q 2 (← B.mul (← B.load q 0) (← B.load q 1))
    let out ← fib.get 11
    B.assertEq out (← k (gp 89))
    discard <| B.rangeCheck out 128
    publish out out])]
```
