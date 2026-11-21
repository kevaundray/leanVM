module

public import NativeRustcX64.Spec.Keccak
public import NativeRustc.Xmss.Model

/-!
# The contract of `LeanXmssSignature::from_bytes`'s closure

`from_bytes`'s closure `layer` (`lean_xmss::scheme`), as `xmss_verify` calls it:
`layer(out, at, bytes)` (RDI, RSI, RDX): the cursor `at`, a `usize` at `RSI`, into the signature's
2404 bytes at `bytes`, with room for a layer (`at + 1200 ≤ 2404`). It writes the layer parsed
from byte `at` (`Xmss.takeLayer`) at `out` in rustc's layout (`Xmss.LayerSignature.memBytes`, 1200
bytes: the path, the chain values, the randomizer; the x86-64 code builds the same layout), advances
the cursor by 1200 and changes no byte outside `out`, the cursor and its stack (`fromBytesStack`
bytes below RSP: 5 pushes, a 1872-byte frame and `memcpy`'s return address).
-/

namespace NativeRustcX64

open NativeRustc

@[expose] public section


/-- The stack the closure uses: 5 pushes, its frame, `memcpy`'s return address. -/
def fromBytesStack : Nat := 40 + 1872 + 8

/-- The cursor's value. -/
def FromBytesPre.cursor (m : MachineData) : Nat := leNat (bytesOf m.dmem (reg m .rsi) 8)

/-- The signature's bytes. -/
def FromBytesPre.bytes (m : MachineData) : List UInt8 := bytesOf m.dmem (reg m .rdx) 2404

/-- A buffer of `n` bytes from `a`: data memory, not wrapping around, apart from the stack and the
return address. -/
def FromBytesPre.Buf (m : MachineData) (a : BitVec 64) (n : Nat) : Prop :=
  Mapped m.dmem a n ∧ NoWrap a n ∧ Apart a n (stackBelow m fromBytesStack) (fromBytesStack + 8)

/-- The closure's precondition. -/
def FromBytesPre (m : MachineData) : Prop :=
  let o := reg m .rdi; let c := reg m .rsi; let b := reg m .rdx
  StackOk m fromBytesStack ∧ FromBytesPre.cursor m + 1200 ≤ 2404 ∧
    FromBytesPre.Buf m o 1200 ∧ FromBytesPre.Buf m c 8 ∧ FromBytesPre.Buf m b 2404 ∧
    Apart o 1200 c 8 ∧ Apart o 1200 b 2404 ∧ Apart c 8 b 2404

/-- The closure's postcondition. -/
def FromBytesPost (m m' : MachineData) : Prop :=
  let o := reg m .rdi; let c := reg m .rsi
  BytesAt m'.dmem o
      (Xmss.takeLayer (FromBytesPre.bytes m) (FromBytesPre.cursor m)).1.memBytes ∧
    BytesAt m'.dmem c (LeanVM.Protocol.KeccakHash.wordBytes (FromBytesPre.cursor m + 1200).toUInt64) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange o 1200 p ∨ InRange c 8 p ∨
      InRange (stackBelow m fromBytesStack) fromBytesStack p) ∧ Saved m m'

end

end NativeRustcX64
