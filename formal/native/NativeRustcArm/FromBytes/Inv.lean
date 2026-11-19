module

public import NativeRustcArm.FromBytes.Glue
public import NativeRustcArm.Spec.FromBytes
public import NativeRustcArm.Code.Xmss.FromBytes

/-!
# `from_bytes`'s closure: the states of its proof

For an entry state `m₀`: the frame's base `frame m₀` (SP after the prologue, `fromBytesStack`
below the entry's SP), the output `out`, the cursor `cur`, the signature's bytes `sig`, the cursor's
value `pos` and the bytes `B` it parses; the bytes of the callee-saved registers the prologue saves
at the frame's top (`saveRegs`), the randomizer, the chain values and the path nodes of the layer
(`rand`, `chainSlot`, `pathSlot`). `Common m₀ m`: what holds from the loop over the chain values to
the last `memcpy`: the registers the code keeps (`X19` the output, `X20` the bytes, `X21` the
cursor, `X24` to `X28`, `X29` and SP the frame), memory as at entry but in the frame and the
cursor, the saved registers and the randomizer in the frame. `Pre`: facts of the precondition.
-/

namespace NativeRustcArm.Xmss.FromBytes

open NativeRustcArm.Sym

@[expose] public section

/-- The frame's base: SP after the prologue. -/
def frame (m₀ : MachineData) : BitVec 64 := stackBelow m₀ fromBytesStack

/-- The output. -/
def out (m₀ : MachineData) : BitVec 64 := m₀.regs.X0.toBitVec

/-- The cursor. -/
def cur (m₀ : MachineData) : BitVec 64 := m₀.regs.X1.toBitVec

/-- The signature's bytes. -/
def sig (m₀ : MachineData) : BitVec 64 := m₀.regs.X2.toBitVec

/-- The cursor's value. -/
def pos (m₀ : MachineData) : Nat := FromBytesPre.cursor m₀

/-- The callee-saved registers the prologue saves, in the order of their slots. -/
def saveRegs : List XReg := [.X29, .X30, .X28, .X23, .X22, .X21, .X20, .X19]

/-- The randomizer. -/
def rand (m₀ : MachineData) : List UInt8 := NativeRustc.slice (FromBytesPre.bytes m₀) (pos m₀) 16

/-- Chain value `j`. -/
def chainSlot (m₀ : MachineData) (j : Nat) : List UInt8 :=
  NativeRustc.slice (FromBytesPre.bytes m₀) (pos m₀ + 16 + 16 * j) 16

/-- Path node `j`. -/
def pathSlot (m₀ : MachineData) (j : Nat) : List UInt8 :=
  NativeRustc.slice (FromBytesPre.bytes m₀) (pos m₀ + 944 + 16 * j) 16

/-- The memory a run of the closure may change: the frame and the cursor. -/
def Scratch (m₀ : MachineData) (p : BitVec 64) : Prop :=
  InRange (frame m₀) fromBytesStack p ∨ InRange (cur m₀) 8 p

/-- What holds from the loop over the chain values to the last `memcpy`. -/
structure Common (m₀ m : MachineData) : Prop where
  x19 : (m.regs.getXReg .X19).toBitVec = out m₀
  x20 : (m.regs.getXReg .X20).toBitVec = sig m₀
  x21 : (m.regs.getXReg .X21).toBitVec = cur m₀
  keep : ∀ r ∈ [XReg.X24, .X25, .X26, .X27, .X28], m.regs.getXReg r = m₀.regs.getXReg r
  x29 : (m.regs.getXReg .X29).toBitVec = frame m₀ + BitVec.ofNat 64 1872
  sp : m.regs.SP.toBitVec = frame m₀
  same : SameOutside m₀.dmem m.dmem (Scratch m₀)
  kept : Kept m₀.dmem m.dmem
  save : ∀ j < 8, BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 (1872 + 8 * j))
    (regBytes (m₀.regs.getXReg (saveRegs.getD j .X0)).toBitVec)
  rand : BytesAt m.dmem (frame m₀) (rand m₀)

/-- At the head of the loop over the chain values, before value `i`. -/
structure LoopAt (m₀ m : MachineData) (i : Nat) : Prop where
  common : Common m₀ m
  x0 : (m.regs.getXReg .X0).toBitVec = BitVec.ofNat 64 (pos m₀ + 16 * i)
  x8 : (m.regs.getXReg .X8).toBitVec = sig m₀ + BitVec.ofNat 64 16
  x9 : (m.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 (32 + 16 * i)
  x10 : (m.regs.getXReg .X10).toBitVec = frame m₀ + BitVec.ofNat 64 944
  cursor : BytesAt m.dmem (cur m₀) (regBytes (BitVec.ofNat 64 (pos m₀ + 16 + 16 * i)))
  chain : ∀ j < i, BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 (944 + 16 * j)) (chainSlot m₀ j)

/-- The facts of the precondition the proof uses, as arithmetic on addresses. -/
structure Pre (m₀ : MachineData) : Prop where
  sp16 : m₀.regs.SP.toNat % 16 = 0
  spLe : fromBytesStack ≤ m₀.regs.SP.toNat
  frameNat : (frame m₀).toNat = m₀.regs.SP.toNat - fromBytesStack
  frameMapped : Mapped m₀.dmem (frame m₀) fromBytesStack
  pos : pos m₀ + 1200 ≤ 2404
  outMapped : Mapped m₀.dmem (out m₀) 1200
  curMapped : Mapped m₀.dmem (cur m₀) 8
  sigMapped : Mapped m₀.dmem (sig m₀) 2404
  outNW : (out m₀).toNat + 1200 ≤ 2 ^ 64
  curNW : (cur m₀).toNat + 8 ≤ 2 ^ 64
  sigNW : (sig m₀).toNat + 2404 ≤ 2 ^ 64
  outF : Apart (out m₀) 1200 (frame m₀) fromBytesStack
  curF : Apart (cur m₀) 8 (frame m₀) fromBytesStack
  sigF : Apart (sig m₀) 2404 (frame m₀) fromBytesStack
  outCur : Apart (out m₀) 1200 (cur m₀) 8
  outSig : Apart (out m₀) 1200 (sig m₀) 2404
  curSig : Apart (cur m₀) 8 (sig m₀) 2404

theorem pre_of {m₀ : MachineData} (h : FromBytesPre m₀) : Pre m₀ := by
  obtain ⟨⟨h16, hle, hmap⟩, hpos, ⟨ho1, ho2, ho3⟩, ⟨hc1, hc2, hc3⟩, ⟨hs1, hs2, hs3⟩, hoc, hos, hcs⟩ := h
  have hF : (frame m₀).toNat = m₀.regs.SP.toNat - fromBytesStack := by
    unfold frame stackBelow
    rw [BitVec.toNat_sub]
    have := m₀.regs.SP.toBitVec.isLt
    simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat] at *
    unfold fromBytesStack at *
    omega
  exact ⟨h16, hle, hF, hmap, hpos, ho1, hc1, hs1, ho2, hc2, hs2, ho3, hc3, hs3, hoc, hos, hcs⟩

theorem Pre.frameNW {m₀ : MachineData} (P : Pre m₀) : NoWrap (frame m₀) fromBytesStack := by
  have := m₀.regs.SP.toBitVec.isLt
  have := P.frameNat
  have := P.spLe
  unfold NoWrap
  simp only [UInt64.toNat_toBitVec] at *
  omega

theorem Pre.frame16 {m₀ : MachineData} (P : Pre m₀) : (frame m₀).toNat % 16 = 0 := by
  rw [P.frameNat]
  have := P.sp16
  have := P.spLe
  unfold fromBytesStack at *
  omega

/-- The signature's bytes are not scratch. -/
theorem Pre.sig_not_scratch {m₀ : MachineData} (P : Pre m₀) {x : Nat} (hx : x < 2404) :
    ¬Scratch m₀ (sig m₀ + BitVec.ofNat 64 x) := by
  rintro (h | h)
  · exact not_inRange_of_apart P.frameNW
      ((P.sigF.symm.sub_right P.sigNW (by omega) (by omega))) h
  · exact not_inRange_of_apart P.curNW ((P.curSig.sub_right P.sigNW (by omega) (by omega))) h

/-- After the loop over the chain values. -/
structure LoopDone (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  x22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 (pos m₀ + 928)
  x23 : (m.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 (pos m₀ + 944)
  cursor : BytesAt m.dmem (cur m₀) (regBytes (BitVec.ofNat 64 (pos m₀ + 944)))
  chain : ∀ j < 58, BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 (944 + 16 * j)) (chainSlot m₀ j)

theorem Pre.slice_length {m₀ : MachineData} (P : Pre m₀) {x : Nat} (hx : x + 16 ≤ 2404) :
    (NativeRustc.slice (FromBytesPre.bytes m₀) x 16).length = 16 := by
  have := P.pos
  simp [NativeRustc.slice, FromBytesPre.bytes, length_bytesOf]
  omega

theorem Pre.rand_length {m₀ : MachineData} (P : Pre m₀) : (rand m₀).length = 16 :=
  P.slice_length (by have := P.pos; omega)

theorem Pre.chainSlot_length {m₀ : MachineData} (P : Pre m₀) {j : Nat} (hj : j < 58) :
    (chainSlot m₀ j).length = 16 :=
  P.slice_length (by have := P.pos; omega)

theorem Pre.pathSlot_length {m₀ : MachineData} (P : Pre m₀) {j : Nat} (hj : j < 16) :
    (pathSlot m₀ j).length = 16 :=
  P.slice_length (by have := P.pos; omega)

/-- The chain values' bytes. -/
def chainBytes (m₀ : MachineData) : List UInt8 := ((List.range 58).map (chainSlot m₀)).flatten

/-- The path's bytes. -/
def pathBytes (m₀ : MachineData) : List UInt8 := ((List.range 16).map (pathSlot m₀)).flatten

/-- `Common` after a step that keeps the callee-saved registers and SP. -/
theorem common_of_saved {m₀ m m' : MachineData} (C : Common m₀ m) (hs : Saved m m')
    (hsame : SameOutside m₀.dmem m'.dmem (Scratch m₀))
    (hsave : ∀ j < 8, BytesAt m'.dmem (frame m₀ + BitVec.ofNat 64 (1872 + 8 * j))
      (regBytes (m₀.regs.getXReg (saveRegs.getD j .X0)).toBitVec))
    (hrand : BytesAt m'.dmem (frame m₀) (rand m₀)) : Common m₀ m' where
  x19 := by rw [hs.1 .X19 rfl]; exact C.x19
  x20 := by rw [hs.1 .X20 rfl]; exact C.x20
  x21 := by rw [hs.1 .X21 rfl]; exact C.x21
  keep r hr := by
    have := C.keep r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hs.1 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)]
    exact this
  x29 := by rw [hs.1 .X29 rfl]; exact C.x29
  sp := by rw [hs.2.1]; exact C.sp
  same := hsame
  kept := C.kept.trans hs.2.2
  save := hsave
  rand := hrand

/-- **What is kept across a call** that keeps the callee-saved registers and changes only scratch
bytes other than the saved registers and the randomizer. -/
theorem Common.transfer {m₀ m m' : MachineData} (P : Pre m₀) (C : Common m₀ m) (hs : Saved m m')
    {R : BitVec 64 → Prop} (hsame : SameOutside m.dmem m'.dmem R) (hR : ∀ p, R p → Scratch m₀ p)
    (hsave : ∀ j < 8, ∀ t < 8, ¬R (frame m₀ + BitVec.ofNat 64 (1872 + 8 * j) + BitVec.ofNat 64 t))
    (hrand : ∀ t < 16, ¬R (frame m₀ + BitVec.ofNat 64 t)) : Common m₀ m' where
  x19 := by rw [hs.1 .X19 rfl]; exact C.x19
  x20 := by rw [hs.1 .X20 rfl]; exact C.x20
  x21 := by rw [hs.1 .X21 rfl]; exact C.x21
  keep r hr := by
    have := C.keep r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hs.1 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)]
    exact this
  x29 := by rw [hs.1 .X29 rfl]; exact C.x29
  sp := by rw [hs.2.1]; exact C.sp
  same := (C.same.trans hsame).mono fun p hp => hp.elim id (hR p)
  kept := C.kept.trans hs.2.2
  save j hj := (C.save j hj).sameOutside hsame fun t ht =>
    hsave j hj t (by rw [length_regBytes] at ht; exact ht)
  rand := C.rand.sameOutside hsame fun t ht => hrand t (by rw [P.rand_length] at ht; exact ht)

/-- After the `memcpy` of the chain values. -/
structure MidAt (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  x22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 (pos m₀ + 928)
  x23 : (m.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 (pos m₀ + 944)
  cursor : BytesAt m.dmem (cur m₀) (regBytes (BitVec.ofNat 64 (pos m₀ + 944)))
  chain : BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 16) (chainBytes m₀)

/-- At the `memcpy` of the path to the output. -/
structure PathCall (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  x0 : (m.regs.getXReg .X0).toBitVec = out m₀
  x1 : (m.regs.getXReg .X1).toBitVec = frame m₀ + BitVec.ofNat 64 944
  x2 : (m.regs.getXReg .X2).toBitVec = BitVec.ofNat 64 256
  cursor : BytesAt m.dmem (cur m₀) (regBytes (BitVec.ofNat 64 (pos m₀ + 1200)))
  chain : BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 16) (chainBytes m₀)
  path : BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 944) (pathBytes m₀)

end

end NativeRustcArm.Xmss.FromBytes
