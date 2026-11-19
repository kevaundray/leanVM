module

public import NativeRustcArm.Spec.Keccak
public import NativeRustc.Xmss.Model

/-!
# The contract of `LeanXmssSignature::from_bytes`'s closure

`from_bytes`'s closure `layer` (`lean_xmss::scheme`), as `xmss_verify` calls it:
`layer(out, at, bytes)` (X0, X1, X2): the cursor `at`, a `usize` at `X1`, into the signature's
2404 bytes at `bytes`, with room for a layer (`at + 1200 ≤ 2404`). It writes the layer parsed
from byte `at` (`Xmss.takeLayer`) at `out` in rustc's layout (`Xmss.LayerSignature.memBytes`, 1200
bytes), advances the cursor by 1200 and changes no byte outside `out`, the cursor and its stack
(`fromBytesStack` bytes below SP, its frame; `memcpy` uses none).
-/

namespace NativeRustcArm

open NativeRustc

@[expose] public section

/-- The closure's symbol. -/
def fromBytesLabel : Label :=
  "_RNCNvMs0_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB7_17LeanXmssSignature10from_bytess_0B9_"

/-- The stack the closure uses: its frame. -/
def fromBytesStack : Nat := 64 + 1872

/-- The cursor's value. -/
def FromBytesPre.cursor (m : MachineData) : Nat := leNat (bytesOf m.dmem m.regs.X1.toBitVec 8)

/-- The signature's bytes. -/
def FromBytesPre.bytes (m : MachineData) : List UInt8 := bytesOf m.dmem m.regs.X2.toBitVec 2404

/-- A buffer of `n` bytes from `a`: data memory, not wrapping around, apart from the stack. -/
def FromBytesPre.Buf (m : MachineData) (a : BitVec 64) (n : Nat) : Prop :=
  Mapped m.dmem a n ∧ NoWrap a n ∧ Apart a n (stackBelow m fromBytesStack) fromBytesStack

/-- The closure's precondition. -/
def FromBytesPre (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let c := m.regs.X1.toBitVec; let b := m.regs.X2.toBitVec
  StackOk m fromBytesStack ∧ FromBytesPre.cursor m + 1200 ≤ 2404 ∧
    FromBytesPre.Buf m o 1200 ∧ FromBytesPre.Buf m c 8 ∧ FromBytesPre.Buf m b 2404 ∧
    Apart o 1200 c 8 ∧ Apart o 1200 b 2404 ∧ Apart c 8 b 2404

/-- The closure's postcondition. -/
def FromBytesPost (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let c := m.regs.X1.toBitVec
  BytesAt m'.dmem o
      (Xmss.takeLayer (FromBytesPre.bytes m) (FromBytesPre.cursor m)).1.memBytes ∧
    BytesAt m'.dmem c (LeanVM.Protocol.KeccakHash.wordBytes (FromBytesPre.cursor m + 1200).toUInt64) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange o 1200 p ∨ InRange c 8 p ∨
      InRange (stackBelow m fromBytesStack) fromBytesStack p) ∧ Saved m m'

end

end NativeRustcArm
