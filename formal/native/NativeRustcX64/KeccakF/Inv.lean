module

public import NativeRustcX64.KeccakF.Bytes

/-!
# `keccak_f`'s loop invariant (x86-64)

The frame: the 248 bytes from 240 below the entry's RSP (`frame`): the red zone and locals
(offsets 0 to 191), the six pushed registers (RBX at 192, R12, R13, R14, R15, RBP at 232) and the
return address (240). In the loop RSP is `frame + 128`.

At the head of the round loop `.LKeccakF_1` after `i` rounds (`At m0 i m`, from the machine
state `m0` at `keccak_f`'s entry): RSP is `frame + 128`; the counter at offset 152 is `8 i`; the
state pointer at 160 is the entry's RDI; the 25 lanes of the state after `i` rounds (`stAfter`)
are in 7 registers (`laneRegs`) and 18 frame slots (`laneSlots`), its 5 column parities in
registers (`parRegs`); the pushed registers are the entry's (`savedSlots`); memory outside the
frame's first 240 bytes is the entry's, and every byte mapped at entry is mapped.

A write the executor leaves as the newest over 8 bytes is a word there (`wordAt_write`); 8 bytes
no write covers keep their word (`wordAt_keep`).
-/

namespace NativeRustcX64.KeccakF

open NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics

@[expose] public section

/-- The frame's base: 240 bytes below the entry's RSP. -/
def frame (m0 : MachineData) : BitVec 64 := stackBelow m0 keccakFStack

/-- The state after `i` rounds, from the 200 bytes at the entry's RDI. -/
def stAfter (m0 : MachineData) (i : Nat) : KeccakState :=
  roundsTo (stateOf (bytesOf m0.dmem (m0.regs.get64 .rdi) 200)) i

/-- The registers that hold lanes at the loop head, with the lanes' indices. -/
def laneRegs : List (Reg64 × Nat) :=
  [(.rdx, 6), (.r11, 10), (.r12, 12), (.r14, 20), (.rsi, 22), (.r10, 23), (.rbp, 24)]

/-- The frame slots that hold lanes at the loop head, with the lanes' indices. -/
def laneSlots : List (Nat × Nat) :=
  [(88, 0), (112, 1), (80, 2), (32, 3), (24, 4), (120, 5), (48, 7), (0, 8), (40, 9), (64, 11),
    (104, 13), (16, 14), (56, 15), (136, 16), (72, 17), (128, 18), (96, 19), (8, 21)]

/-- The first slots of `laneSlots`. -/
def laneSlotsA : List (Nat × Nat) :=
  [(88, 0), (112, 1), (80, 2), (32, 3), (24, 4), (120, 5), (48, 7), (0, 8), (40, 9)]

/-- The other slots of `laneSlots`. -/
def laneSlotsB : List (Nat × Nat) :=
  [(64, 11), (104, 13), (16, 14), (56, 15), (136, 16), (72, 17), (128, 18), (96, 19), (8, 21)]

/-- The registers that hold the column parities at the loop head, with the columns. -/
def parRegs : List (Reg64 × Nat) := [(.rdi, 0), (.r9, 1), (.rcx, 2), (.r15, 3), (.r8, 4)]

/-- The frame slots of the pushed registers. -/
def savedSlots : List (Nat × Reg64) :=
  [(192, .rbx), (200, .r12), (208, .r13), (216, .r14), (224, .r15), (232, .rbp)]

/-- **The loop invariant** after `i` rounds, from the entry's state `m0`. -/
structure At (m0 : MachineData) (i : Nat) (m : MachineData) : Prop where
  rsp : rspOf m = frame m0 + 128#64
  ctr : WordAt m.dmem (frame m0 + BitVec.ofNat 64 152) (BitVec.ofNat 64 (8 * i))
  ptr : WordAt m.dmem (frame m0 + BitVec.ofNat 64 160) (m0.regs.get64 .rdi)
  regs : AllOf (fun p : Reg64 × Nat =>
    m.regs.get64 p.1 = (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneRegs
  slots : AllOf (fun p : Nat × Nat => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneSlots
  par : AllOf (fun p : Reg64 × Nat =>
    m.regs.get64 p.1 = (par (stAfter m0 i) p.2).toBitVec) parRegs
  saved : AllOf (fun p : Nat × Reg64 => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (m0.regs.get64 p.2)) savedSlots
  same : SameOutside m0.dmem m.dmem (InRange (frame m0) keccakFStack)
  kept : Kept m0.dmem m.dmem

end

public section

theorem wordAt_of_eq {d : DataMem} {p v w : BitVec 64} (h : WordAt d p v) (hv : v = w) :
    WordAt d p w := hv ▸ h

theorem allOf_imp {α : Type} {P Q : α → Prop} {l : List α} (h : ∀ a ∈ l, P a → Q a)
    (hl : AllOf P l) : AllOf Q l := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    exact ⟨h a List.mem_cons_self hl.1, ih (fun b hb => h b (List.mem_cons_of_mem a hb)) hl.2⟩

theorem frame_toNat {m0 : MachineData} (h : StackOk m0 keccakFStack) :
    (frame m0).toNat = (rspOf m0).toNat - 240 := by
  have := h.1
  simp only [frame, stackBelow, keccakFStack] at this ⊢
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

/-- The frame and the return address do not wrap around. -/
theorem frame_noWrap {m0 : MachineData} (h : StackOk m0 keccakFStack) :
    NoWrap (frame m0) (keccakFStack + 8) := by
  have h1 := h.1
  have h2 := h.2.1
  simp only [NoWrap, frame_toNat h, keccakFStack] at h1 ⊢
  omega

theorem frame_add (m0 : MachineData) :
    frame m0 + BitVec.ofNat 64 240 = rspOf m0 := by
  simp only [frame, stackBelow, keccakFStack]
  exact BitVec.sub_add_cancel _ _

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **A word written**: where the newest write over the 8 bytes at `o` in region `r` is one
write of `v` there, they are `v`'s word. -/
theorem wordAt_write (hm : Match env S m) {r o sz : Nat} {b : BitVec 64}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) {v : Sym}
    (h : firstOverlap r o 8 S.mem = some ⟨r, o, 8, v⟩) :
    WordAt m.dmem (b + BitVec.ofNat 64 o) (v.eval env) :=
  hm.bytesAt_write hb hle fun i hi => by
    rw [findWrite_some h ⟨Nat.le_refl _, Nat.le_refl _⟩ (Nat.le_add_right o i) (by omega),
      Nat.add_sub_cancel_left]

/-- **A word kept**: 8 bytes in region `r` that no write covers keep their word. -/
theorem wordAt_keep (hm : Match env S m) {r o sz : Nat} {b : BitVec 64}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) {w : BitVec 64}
    (h : firstOverlap r o 8 S.mem = none) (h0 : WordAt env.mem0 (b + BitVec.ofNat 64 o) w) :
    WordAt m.dmem (b + BitVec.ofNat 64 o) w := by
  intro i hi
  rw [List.length_map, List.length_range] at hi
  rw [addr_add, hm.mem r b sz hb (o + i) (by omega)]
  unfold memByte
  rw [findWrite_none h (Nat.le_add_right o i) (by omega), ← addr_add]
  exact h0 i (by simp [hi])

/-- Where every write of a block is in the first `lim` bytes of region `r`, memory changes only
there. -/
theorem same_region (hm : Match env S m) (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz lim : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hall : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ lim)
    (hlim : lim ≤ sz) : SameOutside env.mem0 m.dmem (InRange b lim) := by
  refine fun p hp => hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ => hp ?_
  obtain ⟨hr, hle⟩ := hall w hw
  rw [hr, hb] at hb'
  cases hb'
  have := hwf.noWrap r b sz hb
  rw [inRange_iff (by omega)]
  omega

/-- Where every write of a block is in the first `lim` bytes of region `r` or in region `r'`,
memory changes only there. -/
theorem same_region2 (hm : Match env S m) (hwf : env.WF) {r r' : Nat} {b b' : BitVec 64}
    {sz sz' lim : Nat} (hb : env.regions[r]? = some (b, sz))
    (hb' : env.regions[r']? = some (b', sz')) (hlim : lim ≤ sz)
    (hall : ∀ w ∈ S.mem, (w.r = r ∧ w.off + w.n ≤ lim) ∨ (w.r = r' ∧ w.off + w.n ≤ sz')) :
    SameOutside env.mem0 m.dmem (fun p => InRange b lim p ∨ InRange b' sz' p) := by
  refine fun p hp => hm.get?_mem0 hwf fun ⟨w, hw, c, n, hc, h1, h2⟩ => hp ?_
  rcases hall w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
  · rw [hr, hb] at hc
    cases hc
    left
    have := hwf.noWrap r b sz hb
    rw [inRange_iff (by omega)]
    omega
  · rw [hr, hb'] at hc
    cases hc
    right
    rw [inRange_iff (hwf.noWrap r' b' sz' hb')]
    omega

end

end NativeRustcX64.KeccakF
