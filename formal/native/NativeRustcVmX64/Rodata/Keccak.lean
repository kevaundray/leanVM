module

public import NativeRustcVmX64.Rodata

/-!
# The round constants from the read-only data

The round constants `KECCAK_RC` the permuting functions read: 192 bytes at `rcLabel`, the item
`keccakRC` (`RcAt`, apart from the `n` bytes below RSP and the return address at RSP, as
`RodataAt`). `RodataAt m n` gives `RcAt m n` (`RodataAt.rcAt`).
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeRustcVm.Data

@[expose] public section

/-- The label of the round constants `KECCAK_RC` (192 bytes). -/
def rcLabel : Label := ".Lanon.a75d6d9e6a8990b4224ef13f18552af8.1"

section
variable [Labels]

/-- The address of the round constants. -/
def rcAddr : BitVec 64 := (label rcLabel).toBitVec

/-- The round constants are at their label, apart from the `n` bytes below RSP and the return
address at RSP. -/
def RcAt (m : MachineData) (n : Nat) : Prop :=
  NativeRustcVm.WordsAt m.dmem rcAddr LeanVM.Parameters.keccakRC ∧
    NativeRustcVm.NoWrap rcAddr 192 ∧ NativeRustcVm.Apart rcAddr 192 (stackBelow m n) (n + 8)

end

end

public section

variable [Labels]

theorem rcAddr_eq : rcAddr = rodataAddr .keccakRC := rfl

omit [Labels] in
theorem keccakRC_eq : NativeRustcVm.Data.keccakRC = LeanVM.Parameters.keccakRC := rfl

/-- **The round constants at their label**, from the read-only data. -/
theorem RodataAt.rcAt {m : MachineData} {n : Nat} (h : RodataAt m n) : RcAt m n := by
  have hl : (Item.bytes .keccakRC).length = 192 := by
    rw [Item.bytes, NativeRustcVm.length_wordsBytes, keccakRC_eq]; rfl
  refine ⟨?_, ?_, ?_⟩
  · have := h.bytesAt .keccakRC
    rw [Item.bytes, keccakRC_eq] at this
    exact this
  · have := h.noWrap .keccakRC
    rwa [hl] at this
  · have := h.apart .keccakRC
    rwa [hl] at this

end

end NativeRustcVmX64
