import LeanVMTests.Programs.Support

/-!
# The verifiers' fixture program

`crates/stable_prover/lean_vm_core/tests/verifiers/fixture.rs` and the chain cases of
`scripts/export-rust.sh`: a two-block Keccak and a loop of field arithmetic, long enough that every
table and the Keccak reduction are exercised, at each step count its users take (`chain<steps>`).
Its public input is computed by `fixture.rs`.
-/

namespace LeanVMTests.Programs.Chain

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl LeanVMTests.Programs

/-- `mix(value, tag)`: `value` at `tag = 0`, else `value·g + value`. A jump's condition is in `K`,
here a `g`-power. -/
def mix : GFn where
  name := "mix"
  arity := 2
  rets := 1
  body := fun ps => do
    let value : Word := ⟨ps[0]!⟩
    let tag : Word := ⟨ps[1]!⟩
    B.ite0 tag (B.ret [.v value.v])
    return [.add (← B.mul value (← k (gp 1))).v value.v]

/-- The program at `n` loop steps: the digest of 160 bytes (two blocks, the second read in the
odd layout), then `chain[g^{j+1}] = mix(chain[g^j] + g^j, g^j) + g^j`; published: the chain's end
and `mix(digest[1], 1)`. -/
def chain (n : Nat) : TestProgram where
  name := s!"chain{n}"
  program := [("main", [mainOf do
    let digest ← B.stackBuf 2
    B.keccakCells (.words ((List.replicate 5 [lit 5, lit 7]).flatten.map .const)) (.frame digest)
    let ch ← B.heap (n + 1)
    B.store ch.p 0 (cell digest 0)
    B.loopConstF 0 n 1 (pure [ch.p.v]) fun index caps => do
      let q ← B.mul (cap caps 0) index
      let s ← B.add (← B.load q 0) index
      let m ← B.call "mix" [s.v, index.v] 1
      B.store q 1 (← B.add m[0]! index)
    let last ← B.load ch.p n
    let m ← B.call "mix" [(cell digest 1).v, (← k (gp 0)).v] 1
    publish last m[0]!]),
    ("mix", [mix])]

/-- The step counts: the fixture's own and `export-rust.sh`'s chain cases. -/
def steps : List Nat := [4, 16, 300, 1000, 5000, 16384]

/-- The fixture program at each step count. -/
def all : List TestProgram := steps.map chain

end LeanVMTests.Programs.Chain
