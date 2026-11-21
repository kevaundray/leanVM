module

public import NativeRustcX64.Code.Common.Memcpy.Names

public import NativeRustcX64.FromBytes.Inv
meta import NativeRustcX64.FromBytes.Inv
meta import NativeRustcX64.Code.Xmss.FromBytes

/-!
# `from_bytes`'s closure: the `memcpy` of the chain values

Block 5 after the loop: `memcpy(frame + 944, frame + 16, 928)` (stack offsets 952 and 24) moves
the 58 chain values out of the path's way (`MidAt`), and sets `r12 = pos + 944`,
`r13 = pos + 912`. An environment with the stack as region 0 (for `memcpy`'s return address).
-/

namespace NativeRustcX64.Xmss.FromBytes

open NativeRustcX64.Sym

set_option Elab.async false

/-- The symbolic state of block 5: the stack, RSP the frame. -/
@[expose] public def stM : SState :=
  (init [1928, 8] [(.rsp, .ptr 0 8)] [] [] [(.gotSlot "memcpy", 1, 0)]).withKnownBytes
    1 0 8 (.label "memcpy")

sym_block b5_execM := exec b5 stM

/-- After block 5. -/
@[expose] public def stM1 : SState := ((exec b5 stM).getD (stM, .fall)).1

theorem stM1_regs : stM1.reg .rdi = some (.ptr 0 952) ∧ stM1.reg .rsi = some (.reg .rsi) ∧
    stM1.reg .rdx = some (.lit 928) ∧ stM1.reg .rsp = some (.ptr 0 0) ∧
    stM1.reg .r12 = some (.bin .add .W64 (.lit 48) (.bin .add .W64 (.reg .rdi) (.reg .rdx))) ∧
    stM1.reg .r13 = some (.bin .add .W64 (.lit 16) (.bin .add .W64 (.reg .rdi) (.reg .rdx))) ∧
    stM1.reg .r15 = some (.reg .r15) ∧ stM1.reg .rbp = some (.reg .rbp) ∧
    stM1.reg .rbx = some (.reg .rbx) ∧ stM1.reg .r14 = some (.reg .r14) ∧
    stM1.mem = [⟨0, 0, 8, .retAddr⟩] := by
  decide +kernel

/-- The chain values' slots hold their bytes. -/
theorem chainBytes_at {m₀ m : MachineData} (P : Pre m₀)
    (h : ∀ j < 58, BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (24 + 16 * j)) (chainSlot m₀ j)) :
    BytesAt m.dmem (base m₀ + BitVec.ofNat 64 24) (chainBytes m₀) :=
  bytesAt_flatten 58 (fun j hj => P.chainSlot_length hj)
    fun j hj => by rw [addr_add_addr]; exact h j hj

public theorem length_chainBytes {m₀ : MachineData} (P : Pre m₀) :
    (chainBytes m₀).length = 928 := by
  unfold chainBytes
  rw [List.length_flatten, List.map_map]
  have : ∀ n ≤ 58, ((List.range n).map (List.length ∘ chainSlot m₀)).sum = 16 * n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
      simp [P.chainSlot_length (j := n) (by omega)]
      omega
  exact this 58 le_rfl

/-- Stack offsets outside `[o, o + s)` are not in that range. -/
theorem Pre.not_stack {m₀ : MachineData} (P : Pre m₀) {o s x : Nat} (hs : o + s ≤ 1928)
    (hx : x < o ∨ o + s ≤ x) (hx' : x < 1928) :
    ¬InRange (base m₀ + BitVec.ofNat 64 o) s (base m₀ + BitVec.ofNat 64 x) := by
  rw [inRange_offsets P.baseNW hs hx']
  omega

/-- **The `memcpy` of the chain values.** -/
public theorem mid [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m₀ : MachineData} (P : Pre m₀)
    (G : ParserGot m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b5Offset)) (h : LoopDone m₀ st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b6Offset) → MidAt m₀ st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  have := P.pos
  have hB := P.baseNW
  unfold NoWrap at hB
  let env := Env.ofMachine st.data [(base m₀, 1928), (gotAddr "memcpy", 8)]
    (fun _ => 0) (Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b6Offset)).toBitVec
  have hg := G.1 "memcpy" (by simp)
  have hwf : env.WF := Env.wf_of
    ⟨⟨P.stackMapped.kept C.kept, P.baseNW⟩,
      ⟨(G.mapped (by simp)).kept C.kept, hg.2.1⟩, trivial⟩
    (List.pairwise_pair.mpr hg.2.2.1.symm)
  have hm : Match env stM st.data := by
    apply Match.withKnownBytes
    · apply match_ofMachine
      · exact ⟨rfl, rfl, trivial⟩
      · exact ⟨C.rsp.trans (by simp [Sym.eval]), trivial⟩
      · exact trivial
      · exact trivial
      · exact ⟨by simp [Sym.eval, Env.base, gotAddr], trivial⟩
    · intro i hi
      simpa [Sym.eval, Env.base, env] using
        P.got_byte G (C.same.mono fun _ => Or.inl) hi
  obtain ⟨hdi, hsi, hdx, hsp, h12, h13, h15, hbp, hbx, h14, hmem⟩ := stM1_regs
  refine call_step (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) b5_execM hwf rfl hpc hm
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ stM1 st₁.data at hm₁
  have hsame₁ : SameOutside st.data.dmem st₁.data.dmem (InRange (base m₀) 8) :=
    (hm₁.sameOutside_below hwf (rs := [(0, 8)]) (by unfold writesBelow; rw [hmem]; decide)).mono
      fun p ⟨rb, hrb, b, sz, hb, hin⟩ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
        subst hrb
        cases hb
        exact hin
  have hrdi : st₁.data.regs.get64 .rdi = base m₀ + BitVec.ofNat 64 952 :=
    (hm₁.regs .rdi _ hdi).trans (by simp [Sym.eval, env])
  have hrsi : st₁.data.regs.get64 .rsi = base m₀ + BitVec.ofNat 64 24 :=
    (hm₁.regs .rsi _ hsi).trans h.rsi
  have hrdx : (st₁.data.regs.get64 .rdx).toNat = 928 := by
    rw [hm₁.regs .rdx _ hdx]
    rfl
  have hrsp : rspOf st₁.data = base m₀ := (hm₁.regs .rsp _ hsp).trans (by simp [Sym.eval, env])
  have hk₁ : Kept m₀.dmem st₁.data.dmem := C.kept.trans (hm₁.kept hwf)
  have hpre : MemcpyPre st₁.data := by
    refine ⟨⟨by omega, by rw [hrsp]; omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [reg, hrdi, hrsi, hrdx, hrsp]
    · rw [BitVec.sub_zero]
      have := (P.stackMapped.sub (i := 0) (k := 8) (by omega)).kept hk₁
      simpa using this
    · exact (P.stackMapped.sub (by omega)).kept hk₁
    · exact (P.stackMapped.sub (by omega)).kept hk₁
    · exact P.baseNW.sub (by omega)
    · exact P.baseNW.sub (by omega)
    · exact apart_offsets P.baseNW (by omega) (by omega) (by omega) (by omega) (by omega)
    · have := apart_offsets (o := 952) (s := 928) (o' := 0) (s' := 8) P.baseNW (by omega) (by omega)
        (by omega) (by omega) (by omega)
      simpa using this
  refine call_then hpc₁ hmemcpy hpre fun st₂ hpc₂ hrsp₂ hpost => cont st₂ hpc₂ ?_
  obtain ⟨-, hcopy, hsame, hs₂⟩ := hpost
  simp only [reg, hrdi, hrsi, hrdx] at hcopy hsame
  have hcur : ∀ t < 8, ¬InRange (base m₀ + BitVec.ofNat 64 952) 928 (cur m₀ + BitVec.ofNat 64 t) :=
    fun t ht => not_inRange_of_apart (P.baseNW.sub (by omega))
      ((P.curF.symm.sub_left P.baseNW (by omega) (by omega)).sub_right P.curNW (by omega)
        (by omega))
  have hcur₁ : ∀ t < 8, ¬InRange (base m₀) 8 (cur m₀ + BitVec.ofNat 64 t) := by
    intro t ht
    have h1 := (P.curF.symm.sub_left (i := 0) (k := 8) P.baseNW (by omega) (by omega)).sub_right
      P.curNW (i' := t) (k' := 1) (by omega) (by omega)
    simp only [BitVec.add_zero] at h1
    exact not_inRange_of_apart (by unfold NoWrap; omega) h1
  have hstk : ∀ x, (8 ≤ x ∧ x < 952 ∨ 1880 ≤ x) → x < 1928 →
      ¬(InRange (base m₀) 8 (base m₀ + BitVec.ofNat 64 x) ∨
        InRange (base m₀ + BitVec.ofNat 64 952) 928 (base m₀ + BitVec.ofNat 64 x)) := by
    intro x hx hx'
    rintro (h' | h')
    · have := P.not_stack (o := 0) (s := 8) (x := x) (by omega) (by omega) hx'
      simp at this
      exact this h'
    · exact P.not_stack (by omega) (by omega) hx' h'
  have hsame' : SameOutside st.data.dmem st₂.data.dmem
      (fun p => InRange (base m₀) 8 p ∨ InRange (base m₀ + BitVec.ofNat 64 952) 928 p) :=
    hsame₁.trans hsame
  have hk₂ : Kept st.data.dmem st₂.data.dmem := (hm₁.kept hwf).trans hs₂.2
  refine ⟨C.transfer P ((hs₂.1 .r15 rfl).trans (hm₁.regs .r15 _ h15))
      ((hs₂.1 .rbp rfl).trans (hm₁.regs .rbp _ hbp)) hk₂
      (by rw [show st₂.data.regs.get64 .rsp = rspOf st₂.data from rfl, hrsp₂, hrsp]) hsame'
      (fun p hp => hp.elim (fun h => P.stack_scratch (o := 0) (s := 8) (by omega)
        (by simpa using h)) (P.stack_scratch (by omega)))
      (fun j hj t ht => by rw [addr_add_addr]; exact hstk _ (by omega) (by omega))
      (fun t ht => by rw [addr_add_addr]; exact hstk _ (by omega) (by omega)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs₂.1 .rbx rfl, hm₁.regs .rbx _ hbx]; exact h.rbx
  · rw [hs₂.1 .r14 rfl, hm₁.regs .r14 _ h14]; exact h.r14
  · rw [hs₂.1 .r12 rfl, hm₁.regs .r12 _ h12]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, env, Env.ofMachine_regs, h.rdi, h.rdx]
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, show 48 + (pos m₀ + 896) = pos m₀ + 944 by omega]
  · rw [hs₂.1 .r13 rfl, hm₁.regs .r13 _ h13]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, env, Env.ofMachine_regs, h.rdi, h.rdx]
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, show 16 + (pos m₀ + 896) = pos m₀ + 912 by omega]
  · exact h.cursor.sameOutside hsame' fun t ht h' => h'.elim (hcur₁ t (by
      rw [length_regBytes] at ht; exact ht)) (hcur t (by rw [length_regBytes] at ht; exact ht))
  · have hch := chainBytes_at P h.chain
    have hch₁ := hch.sameOutside hsame₁ fun t ht => by
      rw [length_chainBytes P] at ht
      rw [addr_add_addr]
      have := P.not_stack (o := 0) (s := 8) (x := 24 + t) (by omega) (by omega) (by omega)
      simpa using this
    have := hch₁.bytesOf
    rw [length_chainBytes P] at this
    rw [this] at hcopy
    exact hcopy

end NativeRustcX64.Xmss.FromBytes
