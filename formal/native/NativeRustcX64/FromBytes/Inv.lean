module

public import NativeRustcX64.FromBytes.Glue
public import NativeRustcX64.Spec.FromBytes
public import NativeRustcX64.Code.Xmss.FromBytes
public import NativeRustcX64.Got

/-!
# `from_bytes`'s closure: the states of its proof

For an entry state `m₀`: the stack's base `base m₀` (`fromBytesStack` below the entry's RSP; region
0 of the proof's environments is the 1928 bytes from it, the entry's return address included), the
output `out`, the cursor `cur`, the signature's bytes `sig`, the cursor's value `pos` and the
bytes `B` it parses. In that region: `memcpy`'s return address at `0`, the frame (RSP after the
prologue) at `8`, the randomizer at `8`, the chain values at `24` (in the loop) and `952` (after the
first `memcpy`), the path at `24`, the pushed registers `rbx, r12, r13, r14, r15` at `1880 + 8 j`
(`saveRegs`), the entry's return address at `1920`.

`Common m₀ m`: what holds from the prologue's end to the last `memcpy`: RSP the frame, R15 the
cursor, memory as at entry but in the stack and the cursor, the pushed registers and the
randomizer in the frame. `Pre`: facts of the precondition.
-/

namespace NativeRustcX64.Xmss.FromBytes

open NativeRustcX64.Sym

@[expose] public section

/-- The stack's base: `fromBytesStack` below the entry's RSP. -/
def base (m₀ : MachineData) : BitVec 64 := stackBelow m₀ fromBytesStack

/-- The output. -/
def out (m₀ : MachineData) : BitVec 64 := m₀.regs.get64 .rdi

/-- The cursor. -/
def cur (m₀ : MachineData) : BitVec 64 := m₀.regs.get64 .rsi

/-- The signature's bytes. -/
def sig (m₀ : MachineData) : BitVec 64 := m₀.regs.get64 .rdx

/-- The cursor's value. -/
def pos (m₀ : MachineData) : Nat := FromBytesPre.cursor m₀

/-- The callee-saved registers the prologue pushes, from the lowest slot. -/
def saveRegs : List Reg64 := [.rbx, .r12, .r13, .r14, .r15]

/-- The randomizer. -/
def rand (m₀ : MachineData) : List UInt8 := NativeRustc.slice (FromBytesPre.bytes m₀) (pos m₀) 16

/-- Chain value `j`. -/
def chainSlot (m₀ : MachineData) (j : Nat) : List UInt8 :=
  NativeRustc.slice (FromBytesPre.bytes m₀) (pos m₀ + 16 + 16 * j) 16

/-- Path node `j`. -/
def pathSlot (m₀ : MachineData) (j : Nat) : List UInt8 :=
  NativeRustc.slice (FromBytesPre.bytes m₀) (pos m₀ + 944 + 16 * j) 16

/-- The chain values' bytes. -/
def chainBytes (m₀ : MachineData) : List UInt8 := ((List.range 58).map (chainSlot m₀)).flatten

/-- The path's bytes. -/
def pathBytes (m₀ : MachineData) : List UInt8 := ((List.range 16).map (pathSlot m₀)).flatten

/-- The memory a run of the closure may change: the stack and the cursor. -/
def Scratch (m₀ : MachineData) (p : BitVec 64) : Prop :=
  InRange (base m₀) fromBytesStack p ∨ InRange (cur m₀) 8 p

/-- The loader's single GOT slot needed by the closure. -/
abbrev ParserGot [Labels] (m₀ : MachineData) : Prop :=
  GotAt m₀ fromBytesStack [(out m₀, 1200), (cur m₀, 8), (sig m₀, 2404)] ["memcpy"]

/-- What holds from the prologue's end to the last `memcpy`, RSP at stack offset `o`. -/
structure CommonAt (m₀ m : MachineData) (o : Nat) : Prop where
  r15 : m.regs.get64 .r15 = cur m₀
  rbp : m.regs.get64 .rbp = m₀.regs.get64 .rbp
  rsp : m.regs.get64 .rsp = base m₀ + BitVec.ofNat 64 o
  same : SameOutside m₀.dmem m.dmem (Scratch m₀)
  kept : Kept m₀.dmem m.dmem
  save : ∀ j < 5, BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (1880 + 8 * j))
    (regBytes (m₀.regs.get64 (saveRegs.getD j .rax)))
  rand : BytesAt m.dmem (base m₀ + BitVec.ofNat 64 8) (rand m₀)

/-- `CommonAt` with RSP the frame. -/
abbrev Common (m₀ m : MachineData) : Prop := CommonAt m₀ m 8

/-- At the head of the loop over the chain values, after `i` turns (`2 i` values). -/
structure LoopAt (m₀ m : MachineData) (i : Nat) : Prop where
  common : Common m₀ m
  lt : i < 29
  rbx : m.regs.get64 .rbx = out m₀
  r14 : m.regs.get64 .r14 = sig m₀
  rax : m.regs.get64 .rax = BitVec.ofNat 64 (32 * i)
  rdi : m.regs.get64 .rdi = BitVec.ofNat 64 (pos m₀)
  rcx : m.regs.get64 .rcx = sig m₀ + BitVec.ofNat 64 (pos m₀ + 32)
  rsi : m.regs.get64 .rsi = base m₀ + BitVec.ofNat 64 24
  cursor : BytesAt m.dmem (cur m₀) (regBytes (BitVec.ofNat 64 (pos m₀ + 16 + 32 * i)))
  chain : ∀ j < 2 * i, BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (24 + 16 * j)) (chainSlot m₀ j)

/-- After the loop over the chain values. -/
structure LoopDone (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  rbx : m.regs.get64 .rbx = out m₀
  r14 : m.regs.get64 .r14 = sig m₀
  rdi : m.regs.get64 .rdi = BitVec.ofNat 64 (pos m₀)
  rdx : m.regs.get64 .rdx = BitVec.ofNat 64 896
  rsi : m.regs.get64 .rsi = base m₀ + BitVec.ofNat 64 24
  cursor : BytesAt m.dmem (cur m₀) (regBytes (BitVec.ofNat 64 (pos m₀ + 944)))
  chain : ∀ j < 58, BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (24 + 16 * j)) (chainSlot m₀ j)

/-- After the `memcpy` of the chain values. -/
structure MidAt (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  rbx : m.regs.get64 .rbx = out m₀
  r14 : m.regs.get64 .r14 = sig m₀
  r12 : m.regs.get64 .r12 = BitVec.ofNat 64 (pos m₀ + 944)
  r13 : m.regs.get64 .r13 = BitVec.ofNat 64 (pos m₀ + 912)
  cursor : BytesAt m.dmem (cur m₀) (regBytes (BitVec.ofNat 64 (pos m₀ + 944)))
  chain : BytesAt m.dmem (base m₀ + BitVec.ofNat 64 952) (chainBytes m₀)

/-- At the `memcpy` of the path to the output (RSP below the frame, at the return address). -/
structure PathCall [Labels] (m₀ m : MachineData) : Prop where
  common : CommonAt m₀ m 0
  rbx : m.regs.get64 .rbx = out m₀
  rdi : m.regs.get64 .rdi = out m₀
  rsi : m.regs.get64 .rsi = base m₀ + BitVec.ofNat 64 24
  rdx : m.regs.get64 .rdx = BitVec.ofNat 64 256
  cursor : BytesAt m.dmem (cur m₀) (regBytes (BitVec.ofNat 64 (pos m₀ + 1200)))
  chain : BytesAt m.dmem (base m₀ + BitVec.ofNat 64 952) (chainBytes m₀)
  path : BytesAt m.dmem (base m₀ + BitVec.ofNat 64 24) (pathBytes m₀)
  r14 : m.regs.get64 .r14 = (Labels.label "memcpy").toBitVec

/-- The facts of the precondition the proof uses, as arithmetic on addresses. -/
structure Pre (m₀ : MachineData) : Prop where
  rspLe : fromBytesStack ≤ (rspOf m₀).toNat
  rspNW : (rspOf m₀).toNat + 8 ≤ 2 ^ 64
  baseNat : (base m₀).toNat = (rspOf m₀).toNat - fromBytesStack
  stackMapped : Mapped m₀.dmem (base m₀) 1928
  pos : pos m₀ + 1200 ≤ 2404
  outMapped : Mapped m₀.dmem (out m₀) 1200
  curMapped : Mapped m₀.dmem (cur m₀) 8
  sigMapped : Mapped m₀.dmem (sig m₀) 2404
  outNW : (out m₀).toNat + 1200 ≤ 2 ^ 64
  curNW : (cur m₀).toNat + 8 ≤ 2 ^ 64
  sigNW : (sig m₀).toNat + 2404 ≤ 2 ^ 64
  outF : Apart (out m₀) 1200 (base m₀) 1928
  curF : Apart (cur m₀) 8 (base m₀) 1928
  sigF : Apart (sig m₀) 2404 (base m₀) 1928
  outCur : Apart (out m₀) 1200 (cur m₀) 8
  outSig : Apart (out m₀) 1200 (sig m₀) 2404
  curSig : Apart (cur m₀) 8 (sig m₀) 2404

theorem pre_of [Labels] {m₀ : MachineData} (h : FromBytesPre m₀) : Pre m₀ := by
  obtain ⟨⟨hle, hnw, hmap⟩, hpos, ⟨ho1, ho2, ho3⟩, ⟨hc1, hc2, hc3⟩, ⟨hs1, hs2, hs3⟩, hoc, hos,
    hcs, _⟩ := h
  have hF : (base m₀).toNat = (rspOf m₀).toNat - fromBytesStack := by
    unfold base stackBelow
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (rspOf m₀).isLt
    unfold fromBytesStack at *
    omega
  exact ⟨hle, hnw, hF, hmap, hpos, ho1, hc1, hs1, ho2, hc2, hs2, ho3, hc3, hs3, hoc, hos, hcs⟩

theorem Pre.baseNW {m₀ : MachineData} (P : Pre m₀) : NoWrap (base m₀) 1928 := by
  have := P.baseNat
  have := P.rspLe
  have := P.rspNW
  unfold NoWrap
  unfold fromBytesStack at *
  omega

/-- The entry's RSP is the base plus `fromBytesStack`. -/
theorem Pre.rsp_eq {m₀ : MachineData} (P : Pre m₀) :
    rspOf m₀ = base m₀ + BitVec.ofNat 64 1920 := by
  apply BitVec.eq_of_toNat_eq
  have := P.baseNat
  have := P.rspLe
  have := P.baseNW
  unfold NoWrap fromBytesStack at *
  rw [toNat_add_ofNat _ _ (by omega)]
  omega

/-- The signature's bytes are not scratch. -/
theorem Pre.baseNW' {m₀ : MachineData} (P : Pre m₀) : NoWrap (base m₀) fromBytesStack := by
  have := P.baseNW
  unfold NoWrap fromBytesStack at *
  omega

/-- Neither parser scratch nor its output can overwrite the `memcpy` slot. -/
theorem Pre.got_not_changed [Labels] {m₀ : MachineData} (P : Pre m₀) (G : ParserGot m₀)
    {i : Nat} (hi : i < 8) :
    ¬(Scratch m₀ (gotAddr "memcpy" + BitVec.ofNat 64 i) ∨
      InRange (out m₀) 1200 (gotAddr "memcpy" + BitVec.ofNat 64 i)) := by
  have hg := G.1 "memcpy" (by simp)
  rintro ((h | h) | h)
  · have hs : Apart (gotAddr "memcpy") 8 (base m₀) fromBytesStack := by
      have hs := hg.2.2.1
      change Apart (gotAddr "memcpy") 8 (base m₀) (fromBytesStack + 8) at hs
      unfold Apart at hs ⊢
      omega
    exact hs.not_inRange hg.2.1 P.baseNW' hi h
  · exact (hg.2.2.2 (cur m₀, 8) (by simp)).not_inRange hg.2.1 P.curNW hi h
  · exact (hg.2.2.2 (out m₀, 1200) (by simp)).not_inRange hg.2.1 P.outNW hi h

/-- The GOT bytes in any parser state with the ordinary write footprint. -/
theorem Pre.got_byte [Labels] {m₀ m : MachineData} (P : Pre m₀) (G : ParserGot m₀)
    (hs : SameOutside m₀.dmem m.dmem (fun p => Scratch m₀ p ∨ InRange (out m₀) 1200 p))
    {i : Nat} (hi : i < 8) :
    m.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) =
      some (byteOf (Labels.label "memcpy").toBitVec i) := by
  rw [hs _ (P.got_not_changed G hi)]
  exact G.byte (by simp) hi

/-- The signature's bytes are not scratch. -/
theorem Pre.sig_not_scratch {m₀ : MachineData} (P : Pre m₀) {x : Nat} (hx : x < 2404) :
    ¬Scratch m₀ (sig m₀ + BitVec.ofNat 64 x) := by
  rintro (h | h)
  · refine not_inRange_of_apart P.baseNW' ?_ h
    have := (P.sigF.symm.sub_right P.sigNW (i' := x) (k' := 1) (by omega) (by omega))
    unfold Apart at this ⊢
    unfold fromBytesStack
    omega
  · exact not_inRange_of_apart P.curNW ((P.curSig.sub_right P.sigNW (by omega) (by omega))) h

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

/-- An address at offset `x < 1928` of the stack region. -/
theorem Pre.stack_toNat {m₀ : MachineData} (P : Pre m₀) {x : Nat} (hx : x < 1928) :
    (base m₀ + BitVec.ofNat 64 x).toNat = (base m₀).toNat + x :=
  toNat_addr P.baseNW hx

/-- An offset of the stack below `fromBytesStack` is scratch. -/
theorem Pre.stack_scratch {m₀ : MachineData} (P : Pre m₀) {o s : Nat} (hs : o + s ≤ 1920)
    {p : BitVec 64} (h : InRange (base m₀ + BitVec.ofNat 64 o) s p) : Scratch m₀ p :=
  Or.inl (inRange_sub P.baseNW' (by unfold fromBytesStack; omega) h)

/-- `Common` across steps that keep R15, RBP and the mapped bytes and leave RSP the frame, changing
only scratch bytes other than the pushed registers and the randomizer. -/
theorem CommonAt.transfer {m₀ m m' : MachineData} {o o' : Nat} (P : Pre m₀)
    (C : CommonAt m₀ m o)
    (h15 : m'.regs.get64 .r15 = m.regs.get64 .r15) (hbp : m'.regs.get64 .rbp = m.regs.get64 .rbp)
    (hk : Kept m.dmem m'.dmem) (hrsp : m'.regs.get64 .rsp = base m₀ + BitVec.ofNat 64 o')
    {R : BitVec 64 → Prop} (hsame : SameOutside m.dmem m'.dmem R) (hR : ∀ p, R p → Scratch m₀ p)
    (hsave : ∀ j < 5, ∀ t < 8, ¬R (base m₀ + BitVec.ofNat 64 (1880 + 8 * j) + BitVec.ofNat 64 t))
    (hrand : ∀ t < 16, ¬R (base m₀ + BitVec.ofNat 64 8 + BitVec.ofNat 64 t)) :
    CommonAt m₀ m' o' where
  r15 := h15.trans C.r15
  rbp := hbp.trans C.rbp
  rsp := hrsp
  same := (C.same.trans hsame).mono fun p hp => hp.elim id (hR p)
  kept := C.kept.trans hk
  save j hj := (C.save j hj).sameOutside hsame fun t ht =>
    hsave j hj t (by rw [length_regBytes] at ht; exact ht)
  rand := C.rand.sameOutside hsame fun t ht => hrand t (by rw [P.rand_length] at ht; exact ht)

end

end NativeRustcX64.Xmss.FromBytes
