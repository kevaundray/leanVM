module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.Seed
public meta import NativeRustcVmX64.Code.Vm.Seed
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `seed`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 240-byte frame below the entry's RSP and the return address (R15, R14, RBX pushed at
offsets `232`, `224`, `216`; RSP at offset `8` in the body, the state from offset `16`, a callee's
return address at `0`). `entryS` at the entry (`b0`: the prologue, `keccak256_words`'s arguments,
`call`); `bodyS` after a call (`b1`: `memset`'s arguments for the frame's bytes 80 to 215;
`b3`: `memcpy`'s, from the state to the output; `b4`: the epilogue); `pubS` after `memset`, region
1 the public input at R15 (`b2`: its four words to the frame's bytes 48 to 79, `call keccak_f`).
-/

namespace NativeRustcVmX64.Top.Seed

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Seed NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(232, .r15), (224, .r14), (216, .rbx)]

def entryS : SState := init [248] [(.rsp, .ptr 0 240)]
def bodyS : SState := init [248] [(.rsp, .ptr 0 8)]
def pubS : SState := init [248, 32] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)]

/-- RDX after `b0`: `9 + 8 n` by three `lea`s. -/
def lenSym : Sym :=
  .bin .add .W64
    (.bin .add .W64
      (.bin .add .W64 (.bin .add .W64 (.reg .rdx) (.reg .rdx))
        (.bin .add .W64 (.reg .rdx) (.reg .rdx)))
      (.bin .add .W64 (.bin .add .W64 (.reg .rdx) (.reg .rdx))
        (.bin .add .W64 (.reg .rdx) (.reg .rdx))))
    (.lit 9)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 bodyS
sym_block run_b2 := exec b2 pubS
sym_block run_b3 := exec b3 bodyS
sym_block run_b4 := exec b4 bodyS

public theorem ok_b0 : ProOk 240 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 240) ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 16) ∧
    (after b0 entryS).reg .rsi = some (.bin .add .W64 (.reg .rdx) (.lit 2)) ∧
    (after b0 entryS).reg .rdx = some lenSym ∧
    (after b0 entryS).reg .rcx = some (.reg .rsi) ∧
    (after b0 entryS).reg .r8 = some (.reg .rdx) ∧
    (after b0 entryS).reg .rbx = some (.reg .rdi) ∧
    (after b0 entryS).reg .r14 = some (.ptr 0 16) ∧
    (after b0 entryS).reg .r15 = some (.reg .rcx) := by
  decide +kernel

public theorem ok_b1 : MidOk 240 0 slots (after b1 bodyS) = true ∧
    (∀ w ∈ (after b1 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b1 bodyS).reg .rdi = some (.ptr 0 80) ∧ (after b1 bodyS).reg .rdx = some (.lit 136) ∧
    (after b1 bodyS).reg .rsi = some (.lit 0) ∧ (after b1 bodyS).reg .rbx = some (.reg .rbx) ∧
    (after b1 bodyS).reg .r14 = some (.reg .r14) ∧ (after b1 bodyS).reg .r15 = some (.reg .r15) := by
  decide +kernel

public theorem ok_b2 : MidOk 240 0 slots (after b2 pubS) = true ∧
    (∀ w ∈ (after b2 pubS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 48 ≤ w.off ∧ w.off + w.n ≤ 80)) ∧
    (∀ q < 4, ∀ i < 8, findWrite 0 (48 + 8 * q + i) (after b2 pubS).mem =
      some (.load 1 (8 * q) 8, i)) ∧
    (after b2 pubS).reg .rdi = some (.reg .r14) ∧ (after b2 pubS).reg .rbx = some (.reg .rbx) ∧
    (after b2 pubS).reg .r14 = some (.reg .r14) := by
  decide +kernel

public theorem ok_b3 : MidOk 240 0 slots (after b3 bodyS) = true ∧
    (∀ w ∈ (after b3 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b3 bodyS).reg .rdi = some (.reg .rbx) ∧ (after b3 bodyS).reg .rsi = some (.reg .r14) ∧
    (after b3 bodyS).reg .rdx = some (.lit 200) := by
  decide +kernel

public theorem ok_b4 : EpiOk 240 slots (after b4 bodyS) = true ∧ (after b4 bodyS).mem = [] := by
  decide +kernel

end NativeRustcVmX64.Top.Seed
