/-
  LeanVM.Dsl.Hints

  The hints the guest uses and the checks that turn a hinted value into a fact: `assert !=` with
  its hinted inverse, range checks at a constant or a runtime bound, `assert_in_k`,
  `assert_gpow`.
-/

module

public import LeanVM.Dsl.Control

/-!
# Hints and checks

A hint writes values the prover chooses into a destination (`Core.Dest`: frame cells, or a run of
heap words from a pointer); it is pending until the next instruction, as `Expand.emitHint`. A
hint's outputs carry no fact: what a function may assume of them comes from the checks it emits,
each an atom whose relation the program logic reads (`LeanVM.Dsl.Logic`).

Each hint takes its destination whole, as the zkDSL statement names it (`B.witness` of a
`StackBuf`, a `StackBuf` slice or a heap slice, `LeanVM.Dsl.Mem`), except `B.hintWindowsExp`,
which takes the destination from its first cell and the window offset `at`, recorded as the
`note` event `Expand` records.
-/

namespace LeanVM.Dsl

open LeanVM.Parameters LeanVM.Core LeanVM.Compiler

@[expose] public section

namespace B

/-! ## Hints -/

/-- `hint_witness(dest, "stream")`: the next entries of a witness stream into `d`. -/
def witness (stream : String) (d : Dest) : B Unit := hint (.witness stream d)

/-- `x = hint_witness("stream")`: the next entry of a witness stream, into a fresh cell. -/
def witnessCell (stream : String) : B Hinted := do
  let o ← fresh
  hint (.witness stream (.stack [o]))
  return ⟨o⟩

/-- `hint_decompose_bits(d, x, nbits, start)`: bits `start ..< start + nbits` of `x`. -/
def hintBits {τ : Ty} (d : Dest) (x : Var τ) (start nbits : Nat) : B Unit :=
  hint (.bits x.v start nbits d)

/-- `hint_decompose_bits_exponent(d, x, nbits)`: the `nbits` low bits of `log x`. -/
def hintBitsExpTo {τ : Ty} (d : Dest) (x : Var τ) (nbits : Nat) : B Unit :=
  hint (.bitsExp x.v nbits d)

/-- `hint_decompose_digits_exponent(d, x, nbits, ndigits, digitBits, start)`: `g^digit` for each
base-`2^digitBits` digit of `log x >> s`, `s` the constant `start` or, given `startCell = g^s`,
its exponent. -/
def hintDigitsExp {τ : Ty} (d : Dest) (x : Var τ) (nbits ndigits digitBits start : Nat)
    (startCell : Option Word := none) : B Unit :=
  hint (.digitsExp x.v nbits ndigits digitBits start (startCell.map (·.v)) d)

/-- `hint_windows_exponent(d, x, start, width, count, at)`: `g^w` for each of `count` windows of
`width` bits of `x` from bit `start`, into `d` from cell `skip` on (the statement's `at`); the
offset recorded as `note`. -/
def hintWindowsExp {τ : Ty} (d : Dest) (x : Var τ) (start width count skip : Nat) : B Unit := do
  let d' : Dest := match d with
    | .stack cells => .stack (cells.drop skip)
    | .heap p off len => .heap p (off + skip) (len - skip)
  event (.note skip)
  hint (.windowsExp x.v start width count d')

/-- `hint_log2_ceil(bits, nbits, floor)`: `g^max(⌈log₂ v⌉, floor)`, `v` the value of the `nbits`
bits at `bits`, into a fresh cell. -/
def hintLog2Ceil (bits : Dest) (nbits floor : Nat) : B Hinted := do
  let o ← fresh
  hint (.log2Ceil bits nbits floor o)
  return ⟨o⟩

/-- `hint_f128_limbs(cells, x)`: the first limbs of `x` into the frame cells `cells`. -/
def hintLimbs {τ : Ty} (x : Var τ) (cells : List V) : B Unit := hint (.limbs x.v cells)

/-! ## Checks -/

/-- `assert a != b` (`Expand.lowerAssertNe`): `x = a + b`, its inverse hinted, and `x · inv = 1`. -/
def assertNe {σ τ : Ty} (a : Var σ) (b : Var τ) : B Unit := do
  let x ← add a b
  let inv ← fresh
  hint (.inverse x.v inv)
  let p ← fresh
  atom (.assertNe x.v inv p)

/-- `assert log x < b` at a runtime bound `b = g^n` (`Expand.lowerAssertLt`): the check's operand
`b · g⁻¹`, then the check. -/
def rangeCheckRt {τ ρ : Ty} (x : Var τ) (b : Var ρ) : B Word := do
  let inv ← const (ofK gInv)
  let k ← mul b inv
  rangeCheckK x k

/-- `assert_in_k(a, b)`: both are in `K`. -/
def assertInK {σ τ : Ty} (a : Var σ) (b : Var τ) : B Unit := atom (.assertInK a.v b.v)

/-- `assert_gpow(x)`: a `DEREF` through `x` into a touch cell nothing reads, so `x` is in `K`. -/
def assertGpow {τ : Ty} (x : Var τ) : B (Var .inK) := do
  let t ← fresh
  atom (.touch t x.v)
  return ⟨x.v⟩

end B

end
end LeanVM.Dsl
