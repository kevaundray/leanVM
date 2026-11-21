module

public import NativeRustcArm.Code.Xmss.FromBytes.Names

public import NativeRustcArm.XmssVerify.Frame

/-!
# `xmss_verify`: from the copied signature to the parsed layers

`parse`: blocks 3 and 4 and the two calls of `from_bytes`'s closure
(`NativeRustcArm.XmssVerify.Parse`), from `LoopAt 75` to `Parsed` at block 5.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeArm LeanVM.Protocol.KeccakHash

set_option Elab.async false

section
variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData}

omit [Labels] in
/-- The signature's bytes after the copy. -/
theorem sig_of (h : LoopAt w m₀ m 75) : BytesAt m.dmem (ad m₀ (fb + 44)) (sigB w) := by
  unfold sigB NativeRustc.Xmss.sigBytes
  rw [u32Bytes_toUInt32, wordsBytes_map]
  refine BytesAt.append h.li ?_
  rw [List.length_take, NativeRustc.length_wordBytes, ad_add]
  exact bytesAt_flatten 300 (fun _ _ => NativeRustc.length_wordBytes _) fun k hk => by
    rw [ad_add, show fb + 44 + min 4 8 + 8 * k = fb + 48 + 8 * k by simp]
    exact h.sig k (by omega)

omit [Labels] in
/-- The message's bytes after the copy. -/
theorem msg_of (h : LoopAt w m₀ m 75) : BytesAt m.dmem (ad m₀ (fb + 8)) (msgB w) := by
  unfold msgB NativeRustc.Xmss.messageBytes
  rw [wordsBytes_map]
  exact bytesAt_flatten 4 (fun _ _ => NativeRustc.length_wordBytes _) fun k hk => by
    rw [ad_add]
    exact h.msg k hk

/-- What a call of `from_bytes`'s closure with output and cursor in the frame may change. -/
def FromR (m₀ m : MachineData) (o oc : Nat) (p : BitVec 64) : Prop :=
  InRange (ad m₀ (fb + o)) 1200 p ∨ InRange (ad m₀ (fb + oc)) 8 p ∨
    InRange (stackBelow m fromBytesStack) fromBytesStack p

theorem fromR_lo (P : Pre w m₀) (C : Common m₀ m) {o oc : Nat} (ho : o + 1200 ≤ 5872)
    (hoc : oc + 8 ≤ 5872) : ∀ p, FromR m₀ m o oc p → InRange (lo m₀) 9200 p := by
  intro p hp
  rcases hp with hp | hp | hp
  · exact P.inRange_lo (by fbo) hp
  · exact P.inRange_lo (by fbo) hp
  · exact inRange_stack P C (by decide) hp

theorem not_fromR (P : Pre w m₀) (C : Common m₀ m) {o oc x : Nat} (ho : o + 1200 ≤ 5872)
    (hoc : oc + 8 ≤ 5872) (hx : x < 5872) (h1 : x < o ∨ o + 1200 ≤ x) (h2 : x < oc ∨ oc + 8 ≤ x) :
    ¬FromR m₀ m o oc (ad m₀ (fb + x)) := by
  intro hp
  rcases hp with hp | hp | hp
  · exact P.not_inRange_ad (by fbo) (by fbo) (by omega) hp
  · exact P.not_inRange_ad (by fbo) (by fbo) (by omega) hp
  · exact not_inRange_stack P C (by decide) (by omega) (by fbo) hp

theorem keep_fromR (P : Pre w m₀) (C : Common m₀ m) {o oc : Nat} (ho : o + 1200 ≤ 5872)
    (hoc : oc + 8 ≤ 5872) {d d' : DataMem} (hsame : SameOutside d d' (FromR m₀ m o oc)) {x : Nat}
    {bs : List UInt8} (h : BytesAt d (ad m₀ (fb + x)) bs) (hx : x + bs.length ≤ 5872)
    (h1 : x + bs.length ≤ o ∨ o + 1200 ≤ x) (h2 : x + bs.length ≤ oc ∨ oc + 8 ≤ x) :
    BytesAt d' (ad m₀ (fb + x)) bs :=
  keep_ad hsame h fun t ht => by
    rw [Nat.add_assoc]
    exact not_fromR P C ho hoc (by omega) (by omega) (by omega)

theorem Common.fromR (P : Pre w m₀) (C : Common m₀ m) {m' : MachineData} (hs : Saved m m')
    {o oc : Nat} (ho : o + 1200 ≤ 5776) (hoc : oc + 8 ≤ 5776)
    (hsame : SameOutside m.dmem m'.dmem (FromR m₀ m o oc)) : Common m₀ m' :=
  C.call hs hsame (fromR_lo P C (by omega) (by omega)) fun x hx hx' => by
    have := not_fromR P C (x := x - fb) (o := o) (oc := oc) (by omega) (by omega) (by fbo)
      (by fbo) (by fbo)
    rwa [show fb + (x - fb) = x by omega] at this

/-- `from_bytes`'s precondition at a call from the frame. -/
theorem fromBytesPre (P : Pre w m₀) (C : Common m₀ m) {o oc ob c : Nat}
    (h0 : m.regs.X0.toBitVec = ad m₀ o) (h1 : m.regs.X1.toBitVec = ad m₀ oc)
    (h2 : m.regs.X2.toBitVec = ad m₀ ob) (ho : fb ≤ o) (hoc : fb ≤ oc) (hob : fb ≤ ob)
    (h : o + 1200 ≤ 9200) (hc : oc + 8 ≤ 9200) (hb : ob + 2404 ≤ 9200)
    (hd1 : o + 1200 ≤ oc ∨ oc + 8 ≤ o) (hd2 : o + 1200 ≤ ob ∨ ob + 2404 ≤ o)
    (hd3 : oc + 8 ≤ ob ∨ ob + 2404 ≤ oc) (hcur : BytesAt m.dmem (ad m₀ oc) (wordBytes c.toUInt64))
    (hc' : c + 1200 ≤ 2404) : FromBytesPre m := by
  have hs : fromBytesStack ≤ fb := by decide
  refine ⟨C.stackOk P hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [FromBytesPre.cursor, FromBytesPre.Buf, h0, h1, h2]
  · rw [bytesOf_of hcur (NativeRustc.length_wordBytes _), leNat_wordBytes]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  · exact ⟨C.mapped P h, P.ad_nw h, apart_stack P C hs (by decide) ho h (by omega)⟩
  · exact ⟨C.mapped P hc, P.ad_nw hc, apart_stack P C hs (by decide) hoc hc (by omega)⟩
  · exact ⟨C.mapped P hb, P.ad_nw hb, apart_stack P C hs (by decide) hob hb (by omega)⟩
  · exact P.apart_ad hd1 h hc (by omega) (by omega)
  · exact P.apart_ad hd2 h hb (by omega) (by omega)
  · exact P.apart_ad hd3 hc hb (by omega) (by omega)

end

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **Parsing**: from the end of the copy to block 5. -/
public theorem parse {k : Nat} (hp : Placed code k)
    (hfb : Spec (label NativeRustcArm.Xmss.FromBytes.entryLabel) FromBytesPre FromBytesPost) (P : Pre w m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b3Offset)) (h : LoopAt w m₀ st.data 75)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b5Offset) → Parsed w m₀ st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  have hsig := sig_of h
  have hmsg := msg_of h
  -- Block 3.
  have hwf := frame_wf P C
  have hm0 := match_stF0 P C (known := []) trivial
  obtain ⟨h0, h1, h2, h19, h20, h24, h23, h29, hsp, hw, hsave, hov1, hov2⟩ := st3_facts
  refine call_step (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) b3_exec hwf hpc hm0
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ st3 st₁.data at hm₁
  have C₁ := Common.block P C hwf hm0 hm₁ hsp rfl h29 hw hsave
  have hx : ∀ {r : XReg} {o : Nat}, st3.reg r = some (.ptr 0 o) →
      (st₁.data.regs.getXReg r).toBitVec = ad m₀ (fb + o) := fun hr =>
    (hm₁.regs _ _ hr).trans (eval_ptr0 _)
  have hk : ∀ {r : XReg}, st3.reg r = some (.reg r) → st₁.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun hr => UInt64.toBitVec_inj.mp (hm₁.regs _ _ hr)
  have hcur₁ : BytesAt st₁.data.dmem (ad m₀ (fb + 5408)) (wordBytes (4 : Nat).toUInt64) := by
    have := frameWrite hm₁ (o := 5408) (by omega) st3_cursor
    rwa [regBytes_eq_wordBytes] at this
  have hpk₁ : BytesAt st₁.data.dmem (ad m₀ (fb + 2448)) (pkB w) := by
    unfold pkB NativeRustc.Xmss.pkBytes
    rw [wordsBytes_map]
    refine bytesAt_flatten 4 (fun _ _ => NativeRustc.length_wordBytes _) fun j hj => ?_
    have := frameWrite hm₁ (o := 2448 + 8 * j) (by omega) (st3_pk j hj)
    rw [ad_add, show fb + 2448 + 8 * j = fb + (2448 + 8 * j) by omega,
      show wordBytes (w j) = regBytes (w j).toBitVec from (regBytes_eq_wordBytes _).symm]
    convert this using 2
    simp only [Sym.eval, Env.ofMachine_regs]
    interval_cases j
    · exact congrArg UInt64.toBitVec h.x8.symm
    · exact congrArg UInt64.toBitVec h.x9.symm
    · exact congrArg UInt64.toBitVec h.x10.symm
    · exact congrArg UInt64.toBitVec h.x11.symm
  have hmsg₁ := frameKeep hm₁ (by rw [length_msgB]; omega) (by rw [length_msgB]; exact hov1) hmsg
  have hsig₁ := frameKeep hm₁ (by rw [length_sigB]; omega) (by rw [length_sigB]; exact hov2) hsig
  -- `from_bytes` for the bottom layer.
  have hpre₁ : FromBytesPre st₁.data :=
    fromBytesPre P C₁ (o := fb + 2492) (oc := fb + 5408) (ob := fb + 44) (hx h0) (hx h1) (hx h2) (by fbo) (by fbo) (by fbo) (by fbo) (by fbo) (by fbo)
      (by omega) (by omega) (by omega) hcur₁ (by omega)
  refine call_then hpc₁ hfb hpre₁ fun st₂ hpc₂ hpost₂ => ?_
  obtain ⟨hout₂, hcur₂, hsame₂, hs₂⟩ := hpost₂
  simp only [FromBytesPre.bytes, FromBytesPre.cursor] at hout₂ hcur₂
  have e0 : st₁.data.regs.X0.toBitVec = ad m₀ (fb + 2492) := hx h0
  have e1 : st₁.data.regs.X1.toBitVec = ad m₀ (fb + 5408) := hx h1
  have e2 : st₁.data.regs.X2.toBitVec = ad m₀ (fb + 44) := hx h2
  have hc4 : NativeRustc.leNat (bytesOf st₁.data.dmem (ad m₀ (fb + 5408)) 8) = 4 := by
    rw [bytesOf_of hcur₁ (NativeRustc.length_wordBytes _), leNat_wordBytes]
    rfl
  rw [e0, e1, e2, bytesOf_of hsig₁ (length_sigB w), hc4] at hout₂
  rw [e1, hc4] at hcur₂
  rw [e0, e1] at hsame₂
  change SameOutside _ _ (FromR m₀ st₁.data 2492 5408) at hsame₂
  have C₂ := C₁.fromR P hs₂ (by decide) (by decide) hsame₂
  have hpk₂ := keep_fromR P C₁ (by decide) (by decide) hsame₂ hpk₁ (by rw [length_pkB]; decide)
    (by rw [length_pkB]; decide) (by rw [length_pkB]; decide)
  have hmsg₂ := keep_fromR P C₁ (by decide) (by decide) hsame₂ hmsg₁ (by rw [length_msgB]; decide)
    (by rw [length_msgB]; decide) (by rw [length_msgB]; decide)
  have hsig₂ := keep_fromR P C₁ (by decide) (by decide) hsame₂ hsig₁ (by rw [length_sigB]; decide)
    (by rw [length_sigB]; decide) (by rw [length_sigB]; decide)
  -- Block 4.
  have hwf₃ := frame_wf P C₂
  have hm₃ := match_stF0 P C₂ (known := [(.X19, .ptr 0 2492)])
    ⟨(congrArg UInt64.toBitVec (hs₂.1 .X19 rfl)).trans ((hx h19).trans (eval_ptr0 _).symm), trivial⟩
  obtain ⟨g0, g1, g2, gmem, gsp, g19, gk, gw, gsave⟩ := st4_facts
  refine call_step (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) b4_exec hwf₃ (hpc₂.trans rfl)
    hm₃ fun st₃ hpc₃ hm₃' => ?_
  change Match _ st4 st₃.data at hm₃'
  have C₃ := Common.block P C₂ hwf₃ hm₃ hm₃' gsp rfl (gk .X29 (by simp)) gw gsave
  have hd₃ : st₃.data.dmem = st₂.data.dmem := hm₃'.dmem_eq hwf₃ gmem
  have hcur₃ : BytesAt st₃.data.dmem (ad m₀ (fb + 5408)) (wordBytes (1204 : Nat).toUInt64) := by
    rw [hd₃]; exact hcur₂
  have hpre₃ : FromBytesPre st₃.data :=
    fromBytesPre P C₃ (o := fb + 3692) (oc := fb + 5408) (ob := fb + 44) ((hm₃'.regs _ _ g0).trans (eval_ptr0 _)) ((hm₃'.regs _ _ g1).trans (eval_ptr0 _))
      ((hm₃'.regs _ _ g2).trans (eval_ptr0 _)) (by fbo) (by fbo) (by fbo) (by fbo) (by fbo) (by fbo)
      (by omega) (by omega) (by omega) hcur₃ (by omega)
  refine call_then hpc₃ hfb hpre₃ fun st₄ hpc₄ hpost₄ => cont st₄ (hpc₄.trans rfl) ?_
  obtain ⟨hout₄, -, hsame₄, hs₄⟩ := hpost₄
  simp only [FromBytesPre.bytes, FromBytesPre.cursor] at hout₄
  have f0 : st₃.data.regs.X0.toBitVec = ad m₀ (fb + 3692) := (hm₃'.regs _ _ g0).trans (eval_ptr0 _)
  have f1 : st₃.data.regs.X1.toBitVec = ad m₀ (fb + 5408) := (hm₃'.regs _ _ g1).trans (eval_ptr0 _)
  have f2 : st₃.data.regs.X2.toBitVec = ad m₀ (fb + 44) := (hm₃'.regs _ _ g2).trans (eval_ptr0 _)
  have hc1204 : NativeRustc.leNat (bytesOf st₃.data.dmem (ad m₀ (fb + 5408)) 8) = 1204 := by
    rw [bytesOf_of hcur₃ (NativeRustc.length_wordBytes _), leNat_wordBytes]
    rfl
  rw [f0, f1, f2, hd₃, bytesOf_of hsig₂ (length_sigB w), ← hd₃, hc1204] at hout₄
  rw [f0, f1] at hsame₄
  change SameOutside _ _ (FromR m₀ st₃.data 3692 5408) at hsame₄
  have C₄ := C₃.fromR P hs₄ (by decide) (by decide) hsame₄
  have hkeep : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 3692 →
      BytesAt st₂.data.dmem (ad m₀ (fb + o)) bs → BytesAt st₄.data.dmem (ad m₀ (fb + o)) bs :=
    fun h2 hb => keep_fromR P C₃ (by decide) (by decide) hsame₄ (hd₃ ▸ hb) (by omega)
      (Or.inl h2) (Or.inl (by omega))
  have hreg : ∀ r ∈ [XReg.X23, .X24], st₄.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have h3 : st₃.data.regs.getXReg .X23 = st₂.data.regs.getXReg .X23 :=
        UInt64.toBitVec_inj.mp (hm₃'.regs _ _ (gk .X23 (by simp)))
      rw [hs₄.1 _ rfl, h3, hs₂.1 _ rfl]
      exact hk h23
    · have h3 : st₃.data.regs.getXReg .X24 = st₂.data.regs.getXReg .X24 :=
        UInt64.toBitVec_inj.mp (hm₃'.regs _ _ (gk .X24 (by simp)))
      rw [hs₄.1 _ rfl, h3, hs₂.1 _ rfl]
      exact hk h24
  refine ⟨C₄, ?_, ?_, ?_, ?_, hkeep (by rw [length_msgB]; decide) hmsg₂,
    hkeep (by rw [length_pkB]; decide) hpk₂,
    hkeep (by rw [bottomL, length_memBytes (by rw [length_sigB]; decide)]) hout₂, ?_, ?_, ?_⟩
  · rw [hs₄.1 _ rfl]
    exact (hm₃'.regs _ _ g19).trans (eval_ptr0 _)
  · rw [hs₄.1 _ rfl]
    have h3 : st₃.data.regs.getXReg .X20 = st₂.data.regs.getXReg .X20 :=
      UInt64.toBitVec_inj.mp (hm₃'.regs _ _ (gk .X20 (by simp)))
    rw [h3, hs₂.1 _ rfl]
    exact hx h20
  · rw [hreg .X24 (by simp)]; exact h.x24
  · rw [toNat_X, hreg .X23 (by simp)]; exact h.x23
  · rw [show fb + 3692 = fb + 3692 from rfl]
    exact hout₄
  · rw [hs₄.1 _ rfl]
    have h3 : st₃.data.regs.getXReg .X21 = st₂.data.regs.getXReg .X21 :=
      UInt64.toBitVec_inj.mp (hm₃'.regs _ _ (gk .X21 (by simp)))
    rw [h3, hs₂.1 _ rfl, hk st3_x21]
    exact h.x21
  · rw [hs₄.1 _ rfl]
    exact (hm₃'.regs _ _ st4_x22).trans (eval_ptr0 _)

end NativeRustcArm.Xmss.XmssVerify
