module

public import NativeRustcX64.Code.Common.Memcpy.Names

public import NativeRustcX64.FromBytes.Mid
public import NativeRustcX64.FromBytes.TailExec

/-!
# `from_bytes`'s closure: the output

From the call `memcpy(out, stack + 24, 256)` (the path, `PathCall`): block 23 stores the
randomizer at `out + 1184` and calls `memcpy(out + 256, stack + 952, 928)` (the chain values),
block 24 pops the callee-saved registers and returns (`tail`, to `FromBytesPost`).
-/

namespace NativeRustcX64.Xmss.FromBytes

open NativeRustcX64.Sym

set_option Elab.async false

/-- After the `memcpy` of the path. -/
structure TailAt [Labels] (m₀ m : MachineData) : Prop where
  rbx : m.regs.get64 .rbx = out m₀
  rbp : m.regs.get64 .rbp = m₀.regs.get64 .rbp
  rsp : m.regs.get64 .rsp = base m₀ + BitVec.ofNat 64 8
  same : SameOutside m₀.dmem m.dmem (fun p => Scratch m₀ p ∨ InRange (out m₀) 1200 p)
  kept : Kept m₀.dmem m.dmem
  save : ∀ j < 5, BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (1880 + 8 * j))
    (regBytes (m₀.regs.get64 (saveRegs.getD j .rax)))
  rand : BytesAt m.dmem (base m₀ + BitVec.ofNat 64 8) (rand m₀)
  cursor : BytesAt m.dmem (cur m₀) (regBytes (BitVec.ofNat 64 (pos m₀ + 1200)))
  chain : BytesAt m.dmem (base m₀ + BitVec.ofNat 64 952) (chainBytes m₀)
  path : BytesAt m.dmem (out m₀) (pathBytes m₀)
  r14 : m.regs.get64 .r14 = (Labels.label "memcpy").toBitVec

theorem length_pathBytes {m₀ : MachineData} (P : Pre m₀) : (pathBytes m₀).length = 256 := by
  unfold pathBytes
  rw [List.length_flatten, List.map_map]
  have : ∀ n ≤ 16, ((List.range n).map (List.length ∘ pathSlot m₀)).sum = 16 * n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
      simp [P.pathSlot_length (j := n) (by omega)]
      omega
  exact this 16 le_rfl

section
variable {m₀ : MachineData}

theorem out_apart_stack (P : Pre m₀) {o s x : Nat} (hs : o + s ≤ 1200) (hx : x < 1928)
    (h0 : 0 < s) : ¬InRange (out m₀ + BitVec.ofNat 64 o) s (base m₀ + BitVec.ofNat 64 x) :=
  not_inRange_of_apart (NoWrap.sub P.outNW hs)
    ((P.outF.sub_left P.outNW hs h0).sub_right P.baseNW (by omega) (by omega))

theorem out_apart_cur (P : Pre m₀) {o s x : Nat} (hs : o + s ≤ 1200) (hx : x < 8) (h0 : 0 < s) :
    ¬InRange (out m₀ + BitVec.ofNat 64 o) s (cur m₀ + BitVec.ofNat 64 x) :=
  not_inRange_of_apart (NoWrap.sub P.outNW hs)
    ((P.outCur.sub_left P.outNW hs h0).sub_right P.curNW (by omega) (by omega))

/-- The entry's return address is neither scratch nor output. -/
theorem not_scratch_ret (P : Pre m₀) {i : Nat} (hi : i < 8) :
    ¬(Scratch m₀ (base m₀ + BitVec.ofNat 64 (1920 + i)) ∨
      InRange (out m₀) 1200 (base m₀ + BitVec.ofNat 64 (1920 + i))) := by
  rintro ((h | h) | h)
  · have h' : ¬InRange (base m₀ + BitVec.ofNat 64 0) 1920
        (base m₀ + BitVec.ofNat 64 (1920 + i)) := by
      rw [inRange_offsets P.baseNW (by omega) (by omega)]
      omega
    have h2 : ¬InRange (base m₀) fromBytesStack (base m₀ + BitVec.ofNat 64 (1920 + i)) := by
      simpa [fromBytesStack] using h'
    exact h2 h
  · exact not_inRange_of_apart P.curNW (P.curF.sub_right P.baseNW (by omega) (by omega)) h
  · exact not_inRange_of_apart P.outNW (P.outF.sub_right P.baseNW (by omega) (by omega)) h

end

/-- The `memcpy` of the path. -/
theorem tailAt_of [Labels] {m₀ m m' : MachineData} (P : Pre m₀) (h : PathCall m₀ m)
    (hrsp : rspOf m' = rspOf m + 8#64) (hpost : MemcpyPost m m') : TailAt m₀ m' := by
  have C := h.common
  obtain ⟨-, hcopy, hsame, hs⟩ := hpost
  have hdx : (m.regs.get64 .rdx).toNat = 256 := by rw [h.rdx]; rfl
  simp only [reg, h.rdi, h.rsi, hdx] at hcopy hsame
  have hof : ∀ x < 1928, ¬InRange (out m₀) 256 (base m₀ + BitVec.ofNat 64 x) := fun x hx => by
    simpa using out_apart_stack (o := 0) P (by omega) hx (by omega)
  have hoc : ∀ x < 8, ¬InRange (out m₀) 256 (cur m₀ + BitVec.ofNat 64 x) := fun x hx => by
    simpa using out_apart_cur (o := 0) P (by omega) hx (by omega)
  refine ⟨by rw [hs.1 .rbx rfl]; exact h.rbx, by rw [hs.1 .rbp rfl]; exact C.rbp, ?_,
    (C.same.trans hsame).mono fun p hp => hp.elim Or.inl fun hp' => Or.inr ?_,
    C.kept.trans hs.2, fun j hj => (C.save j hj).sameOutside hsame fun t ht => ?_,
    C.rand.sameOutside hsame fun t ht => ?_,
    h.cursor.sameOutside hsame fun t ht => hoc t (by rw [length_regBytes] at ht; exact ht),
    h.chain.sameOutside hsame fun t ht => ?_, ?_, (hs.1 .r14 rfl).trans h.r14⟩
  · show rspOf m' = _
    rw [hrsp]
    show m.regs.get64 .rsp + _ = _
    rw [C.rsp, addr_add_addr]
  · unfold InRange at hp' ⊢
    omega
  · rw [addr_add_addr]
    exact hof _ (by rw [length_regBytes] at ht; omega)
  · rw [addr_add_addr]
    exact hof _ (by rw [P.rand_length] at ht; omega)
  · rw [addr_add_addr]
    exact hof _ (by rw [length_chainBytes P] at ht; omega)
  · have := h.path.bytesOf
    rw [length_pathBytes P] at this
    rw [this] at hcopy
    exact hcopy

theorem saveRegs_cases (r : Reg64) (hr : calleeSaved r = true) :
    r = .rbp ∨ ∃ j, j < 5 ∧ saveRegs.getD j .rax = r := by
  cases r <;> simp [calleeSaved] at hr <;> first
    | exact Or.inl rfl | exact Or.inr ⟨0, by decide, rfl⟩ | exact Or.inr ⟨1, by decide, rfl⟩
    | exact Or.inr ⟨2, by decide, rfl⟩ | exact Or.inr ⟨3, by decide, rfl⟩
    | exact Or.inr ⟨4, by decide, rfl⟩

theorem memBytes_takeLayer (m₀ : MachineData) :
    (NativeRustc.Xmss.takeLayer (FromBytesPre.bytes m₀) (FromBytesPre.cursor m₀)).1.memBytes =
      pathBytes m₀ ++ chainBytes m₀ ++ rand m₀ := by
  simp only [NativeRustc.Xmss.takeLayer, NativeRustc.Xmss.LayerSignature.memBytes, pathBytes,
    chainBytes, rand, pos]
  rfl

/-- **The output**: from the call of the path's `memcpy` to the return. -/
public theorem tail [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m₀ : MachineData} (P : Pre m₀)
    {st : MachineState} (hpc : st.pc = Labels.label NativeRustcX64.Common.Memcpy.entryLabel)
    (hret : retOf st.data = Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b23Offset)) (h : PathCall m₀ st.data) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧
      rspOf st'.data = rspOf m₀ + 8#64 ∧ FromBytesPost m₀ st'.data) st := by
  have C := h.common
  have hB := P.baseNW
  have hO := P.outNW
  unfold NoWrap at hB hO
  have hrsp0 : rspOf st.data = base m₀ := by
    show st.data.regs.get64 .rsp = _
    rw [C.rsp]
    simp
  have hpre : MemcpyPre st.data := by
    have hdx : (st.data.regs.get64 .rdx).toNat = 256 := by rw [h.rdx]; rfl
    refine ⟨⟨by omega, by rw [hrsp0]; omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [reg, h.rdi, h.rsi, hdx, hrsp0]
    · rw [BitVec.sub_zero]
      have := (P.stackMapped.sub (i := 0) (k := 8) (by omega)).kept C.kept
      simpa using this
    · have := (P.outMapped.sub (i := 0) (k := 256) (by omega)).kept C.kept
      simpa using this
    · exact (P.stackMapped.sub (by omega)).kept C.kept
    · unfold NoWrap; omega
    · exact P.baseNW.sub (by omega)
    · have := (P.outF.sub_left (i := 0) (k := 256) P.outNW (by omega) (by omega)).sub_right
        (i' := 24) (k' := 256) P.baseNW (by omega) (by omega)
      simpa using this
    · have := (P.outF.sub_left (i := 0) (k := 256) P.outNW (by omega) (by omega)).sub_right
        (i' := 0) (k' := 8) P.baseNW (by omega) (by omega)
      simpa using this
  refine NativeRustcX64.Eventually.bind (Spec.apply hmemcpy hpc hpre)
    fun st₁ ⟨hpc₁, hrsp₁, hpost₁⟩ => ?_
  rw [hret] at hpc₁
  have T := tailAt_of P h hrsp₁ hpost₁
  -- Block 23.
  let env₂ := Env.ofMachine st₁.data [(base m₀, 1928), (out m₀, 1200)]
    (fun _ => 0) (Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b24Offset)).toBitVec
  have hwf₂ : env₂.WF :=
    Env.wf_of ⟨⟨P.stackMapped.kept T.kept, P.baseNW⟩, ⟨P.outMapped.kept T.kept, P.outNW⟩,
      trivial⟩ (List.pairwise_pair.mpr P.outF.symm)
  have hm₁ : Match env₂ stT0 st₁.data := by
    apply match_ofMachine
    · exact ⟨rfl, rfl, trivial⟩
    · exact ⟨T.rsp.trans (by simp [Sym.eval]), T.rbx.trans (by simp [Sym.eval]), T.r14, trivial⟩
    · exact trivial
    · exact trivial
    · exact trivial
  obtain ⟨hdi, hsi, hdx, hsp, hbp, hwrites, hch, hsv, hpa⟩ := stT1_facts
  refine call_step (b23_in_code.trans hp.1 (List.cons_ne_nil _ _)) b23_execT hwf₂ rfl hpc₁ hm₁
    fun st₂ hpc₂ hm₂ => ?_
  change Match _ stT1 st₂.data at hm₂
  have hr0 : env₂.regions[0]? = some (base m₀, 1928) := rfl
  have hr1 : env₂.regions[1]? = some (out m₀, 1200) := rfl
  have hrdi : st₂.data.regs.get64 .rdi = out m₀ + BitVec.ofNat 64 256 :=
    (hm₂.regs .rdi _ hdi).trans (by simp [Sym.eval, env₂])
  have hrsi : st₂.data.regs.get64 .rsi = base m₀ + BitVec.ofNat 64 952 :=
    (hm₂.regs .rsi _ hsi).trans (by simp [Sym.eval, env₂])
  have hrdx : (st₂.data.regs.get64 .rdx).toNat = 928 := by
    rw [hm₂.regs .rdx _ hdx]
    rfl
  have hrsp₂ : rspOf st₂.data = base m₀ := (hm₂.regs .rsp _ hsp).trans (by simp [Sym.eval, env₂])
  have hk₂ : Kept m₀.dmem st₂.data.dmem := T.kept.trans (hm₂.kept hwf₂)
  have hpre₂ : MemcpyPre st₂.data := by
    refine ⟨⟨by omega, by rw [hrsp₂]; omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [reg, hrdi, hrsi, hrdx, hrsp₂]
    · rw [BitVec.sub_zero]
      have := (P.stackMapped.sub (i := 0) (k := 8) (by omega)).kept hk₂
      simpa using this
    · exact (P.outMapped.sub (by omega)).kept hk₂
    · exact (P.stackMapped.sub (by omega)).kept hk₂
    · exact NoWrap.sub P.outNW (by omega)
    · exact P.baseNW.sub (by omega)
    · exact (P.outF.sub_left P.outNW (by omega) (by omega)).sub_right P.baseNW (by omega)
        (by omega)
    · have := (P.outF.sub_left (i := 256) (k := 928) P.outNW (by omega) (by omega)).sub_right
        (i' := 0) (k' := 8) P.baseNW (by omega) (by omega)
      simpa using this
  refine call_then hpc₂ hmemcpy hpre₂ fun st₃ hpc₃ hrsp₃ hpost₃ => ?_
  obtain ⟨-, hcopy, hsame₃, hs₃⟩ := hpost₃
  simp only [reg, hrdi, hrsi, hrdx] at hcopy hsame₃
  -- Block 24.
  have hk₃ : Kept m₀.dmem st₃.data.dmem := hk₂.trans hs₃.2
  let env₄ := Env.ofMachine st₃.data [(base m₀, 1928)]
  have hwf₄ : env₄.WF :=
    Env.wf_of ⟨⟨P.stackMapped.kept hk₃, P.baseNW⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hsp₃ : st₃.data.regs.get64 .rsp = base m₀ + BitVec.ofNat 64 8 := by
    show rspOf st₃.data = _
    rw [hrsp₃, hrsp₂]
  have hm₃ : Match env₄ stE0 st₃.data := match_ofMachine ⟨rfl, trivial⟩
    ⟨hsp₃.trans (by simp [Sym.eval]), trivial⟩ trivial trivial trivial
  refine exec_at (b24_in_code.trans hp.1 (List.cons_ne_nil _ _)) b24_execE hwf₄
    (fun _ h => nomatch h) hpc₃ hm₃ fun st₄ hm₄ hpc₄ => ?_
  change Match _ stE1 st₄.data at hm₄
  obtain ⟨hmem₄, hsp₄, hld₄, hbp₄⟩ := stE1_facts
  have hd₄ : st₄.data.dmem = st₃.data.dmem := hm₄.dmem_eq hwf₄ hmem₄
  -- What changed.
  have hsameAll : SameOutside m₀.dmem st₃.data.dmem
      (fun p => Scratch m₀ p ∨ InRange (out m₀) 1200 p) := by
    refine ((T.same.trans (hm₂.sameOutside_below hwf₂ hwrites)).trans hsame₃).mono
      fun p hp => ?_
    rcases hp with (hp | ⟨rb, hrb, b, sz, hb, hin⟩) | hp
    · exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
      rcases hrb with rfl | rfl
      · cases hb
        exact Or.inl (P.stack_scratch (o := 0) (s := 8) (by omega) (by simpa using hin))
      · cases hb
        exact Or.inr hin
    · exact Or.inr (inRange_sub P.outNW (by omega) hp)
  -- The saved registers' slots.
  have hsave₃ : ∀ j < 5, BytesAt st₃.data.dmem (base m₀ + BitVec.ofNat 64 (1880 + 8 * j))
      (regBytes (m₀.regs.get64 (saveRegs.getD j .rax))) := fun j hj =>
    (hm₂.bytesAt_keep hr0 (by rw [length_regBytes]; omega)
      (by rw [length_regBytes]; exact hsv j hj) (T.save j hj)).sameOutside hsame₃ fun t ht => by
        rw [addr_add_addr]
        exact out_apart_stack P (by omega) (by rw [length_regBytes] at ht; omega) (by omega)
  have hreg : ∀ j < 5, st₄.data.regs.get64 (saveRegs.getD j .rax) =
      m₀.regs.get64 (saveRegs.getD j .rax) := fun j hj => by
    rw [hm₄.regs _ _ (hld₄ j hj)]
    simp only [Sym.eval]
    rw [Env.load_of_bytesAt (length_regBytes _) (by simpa [env₄] using hsave₃ j hj),
      ofBytes_regBytes]
    rfl
  have hsaved : Saved m₀ st₄.data := by
    refine ⟨fun r hr => ?_, hk₃.trans fun p hp => by rw [hd₄]; exact hp⟩
    rcases saveRegs_cases r hr with rfl | ⟨j, hj, rfl⟩
    · rw [hm₄.regs .rbp _ hbp₄]
      show st₃.data.regs.get64 .rbp = _
      rw [hs₃.1 .rbp rfl, hm₂.regs .rbp _ hbp]
      exact T.rbp
    · exact hreg j hj
  refine .done _ ⟨?_, ?_, ?_, ?_, ?_, hsaved⟩
  · -- The return.
    have hread := hm₃.read hwf₄ (r := 0) (o := 1920) (n := 8) rfl (by decide) (by decide)
    have hb : env₄.base 0 + BitVec.ofNat 64 1920 = rspOf m₀ := by
      rw [P.rsp_eq]
      rfl
    rw [hb, loadInt_congr (d := m₀.dmem) fun i hi => ?_] at hread
    · simp only [PcOk] at hpc₄
      rw [hpc₄]
      exact (retOf_of_loadInt hread).symm
    · rw [P.rsp_eq, addr_add_addr]
      exact hsameAll _ (not_scratch_ret P hi)
  · -- RSP.
    show st₄.data.regs.get64 .rsp = _
    rw [hm₄.regs .rsp _ hsp₄, P.rsp_eq, addr_add_addr]
    simp [Sym.eval, env₄]
  · -- The layer.
    show BytesAt st₄.data.dmem (out m₀)
      (NativeRustc.Xmss.takeLayer (FromBytesPre.bytes m₀) (FromBytesPre.cursor m₀)).1.memBytes
    rw [memBytes_takeLayer, hd₄]
    refine BytesAt.append (BytesAt.append ?_ ?_) ?_
    · have h1 := (hm₂.bytesAt_keep (o := 0) hr1 (by rw [length_pathBytes P]; omega)
        (by rw [length_pathBytes P]; exact hpa)
        (by show BytesAt st₁.data.dmem _ _; simpa using T.path)).sameOutside hsame₃
        fun t ht => by
          rw [length_pathBytes P] at ht
          rw [addr_add_addr, inRange_offsets P.outNW (by omega) (by omega)]
          omega
      exact bytesAt_add_zero h1
    · rw [length_pathBytes P]
      have := (hm₂.bytesAt_keep hr0 (by rw [length_chainBytes P]; omega)
        (by rw [length_chainBytes P]; exact hch) T.chain).bytesOf
      rw [length_chainBytes P] at this
      rwa [this] at hcopy
    · rw [List.length_append, length_pathBytes P, length_chainBytes P]
      intro t ht
      rw [P.rand_length] at ht
      have hnot : ¬InRange (out m₀ + BitVec.ofNat 64 256) 928
          (out m₀ + BitVec.ofNat 64 (1184 + t)) := by
        rw [inRange_offsets P.outNW (by omega) (by omega)]
        omega
      have hg := hm₂.get?_load hr1 (by omega) (stT1_rand t ht) (by omega) (le_refl 8)
      change st₃.data.dmem.get? (out m₀ + BitVec.ofNat 64 (256 + 928) + BitVec.ofNat 64 t) = _
      rw [addr_add_addr, show 256 + 928 + t = 1184 + t by omega, hsame₃ _ hnot, hg,
        show 8 + 8 * (t / 8) + t % 8 = 8 + t by omega]
      simp only [Env.base_ofMachine_eq, env₂, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some, Env.ofMachine_mem0]
      rw [← addr_add_addr, T.rand t (by rw [P.rand_length]; exact ht)]
      rfl
  · -- The cursor.
    show BytesAt st₄.data.dmem (cur m₀) _
    rw [hd₄]
    have h₂ := hm₂.bytesAt_outside (fun t ht => Env.outside_of_apart
      ⟨(P.curF.symm.sub_right P.curNW (by rw [length_regBytes] at ht; omega) (by omega)),
        (P.outCur.sub_right P.curNW (by rw [length_regBytes] at ht; omega) (by omega)),
        trivial⟩) T.cursor
    have h₃ := h₂.sameOutside hsame₃ fun t ht => out_apart_cur P (by omega)
      (by rw [length_regBytes] at ht; exact ht) (by omega)
    rw [regBytes_eq_wordBytes] at h₃
    exact h₃
  · -- What changed.
    rw [hd₄]
    refine hsameAll.mono fun p hp => ?_
    rcases hp with (hp | hp) | hp
    · exact Or.inr (Or.inr hp)
    · exact Or.inr (Or.inl hp)
    · exact Or.inl hp

end NativeRustcX64.Xmss.FromBytes
