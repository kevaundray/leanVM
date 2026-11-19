module

public import NativeRustcX64.XmssVerify.Parse

/-!
# `xmss_verify`: from the copied signature to the parsed layers (x86-64)

`parse`: blocks 3 and 4 and the two calls of `from_bytes`'s closure
(`NativeRustcX64.XmssVerify.Parse`), from `LoopAt 50` to `Parsed` at block 5.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc.Xmss

set_option Elab.async false

public section

section
variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData}

/-- What a call of `from_bytes`'s closure with output and cursor in the frame may change. -/
@[expose] def FromR (m₀ m : MachineData) (o oc : Nat) (p : BitVec 64) : Prop :=
  InRange (ad m₀ (fr + o)) 1200 p ∨ InRange (ad m₀ (fr + oc)) 8 p ∨
    InRange (stackBelow m fromBytesStack) fromBytesStack p

theorem not_fromR (P : Pre w m₀) (hrsp : rspOf m = ad m₀ (fr + 16)) {o oc x : Nat}
    (ho : o + 1200 ≤ 5816) (hoc : oc + 8 ≤ 5816) (hx16 : 16 ≤ x) (hx : x < 5816)
    (h1 : x < o ∨ o + 1200 ≤ x) (h2 : x < oc ∨ oc + 8 ≤ x) :
    ¬FromR m₀ m o oc (ad m₀ (fr + x)) := by
  rintro (hp | hp | hp)
  · exact P.not_inRange_ad (by fro) (by fro) (by omega) hp
  · exact P.not_inRange_ad (by fro) (by fro) (by omega) hp
  · exact not_stack P hrsp (by decide) hx16 hx hp

theorem keep_fromR (P : Pre w m₀) (hrsp : rspOf m = ad m₀ (fr + 16)) {o oc : Nat}
    (ho : o + 1200 ≤ 5816) (hoc : oc + 8 ≤ 5816) {d d' : DataMem}
    (hsame : SameOutside d d' (FromR m₀ m o oc)) {x : Nat} {bs : List UInt8}
    (h : BytesAt d (ad m₀ (fr + x)) bs) (hx16 : 16 ≤ x) (hx : x + bs.length ≤ 5816)
    (h1 : x + bs.length ≤ o ∨ o + 1200 ≤ x) (h2 : x + bs.length ≤ oc ∨ oc + 8 ≤ x) :
    BytesAt d' (ad m₀ (fr + x)) bs :=
  keep_ad hsame h fun t ht => by
    rw [Nat.add_assoc]
    exact not_fromR P hrsp ho hoc (by omega) (by omega) (by omega) (by omega)

theorem Common.fromR (P : Pre w m₀) (C : Common m₀ m) {m' : MachineData} (hs : Saved m m')
    (hrsp : rspOf m = ad m₀ (fr + 16)) {o oc : Nat} (ho : o + 1200 ≤ 5760)
    (hoc : oc + 8 ≤ 5760) (hsame : SameOutside m.dmem m'.dmem (FromR m₀ m o oc)) :
    Common m₀ m' :=
  C.call hs hsame
    (fun p hp => by
      rcases hp with hp | hp | hp
      · exact P.inRange_lo (by fro) hp
      · exact P.inRange_lo (by fro) hp
      · rw [stackBelow_at hrsp (by decide)] at hp
        exact P.inRange_lo (by decide) hp)
    fun x hx hx' => by
      have := not_fromR P hrsp (x := x - fr) (o := o) (oc := oc) (by omega) (by omega) (by fro)
        (by fro) (by fro) (by fro)
      rwa [show fr + (x - fr) = x by omega] at this

/-- `from_bytes`'s precondition at a call from the frame. -/
theorem fromBytesPre (P : Pre w m₀) (C : Common m₀ m) (hrsp : rspOf m = ad m₀ (fr + 16))
    {o oc ob c : Nat} (h0 : reg m .rdi = ad m₀ (fr + o)) (h1 : reg m .rsi = ad m₀ (fr + oc))
    (h2 : reg m .rdx = ad m₀ (fr + ob)) (ho : 24 ≤ o) (hoc : 24 ≤ oc) (hob : 24 ≤ ob)
    (h : o + 1200 ≤ 5816) (hc : oc + 8 ≤ 5816) (hb : ob + 2404 ≤ 5816)
    (hd1 : o + 1200 ≤ oc ∨ oc + 8 ≤ o) (hd2 : o + 1200 ≤ ob ∨ ob + 2404 ≤ o)
    (hd3 : oc + 8 ≤ ob ∨ ob + 2404 ≤ oc)
    (hcur : BytesAt m.dmem (ad m₀ (fr + oc)) (wordBytes c.toUInt64)) (hc' : c + 1200 ≤ 2404) :
    FromBytesPre m := by
  have hbuf : ∀ {x s : Nat}, 24 ≤ x → x + s ≤ 5816 → 0 < s →
      FromBytesPre.Buf m (ad m₀ (fr + x)) s := fun hx hs hs0 =>
    ⟨C.mapped P (by fro), P.ad_nw (by fro),
      apart_at P hrsp (by decide) (by fro) (by omega) (by fro) hs0⟩
  refine ⟨stackOk_at P C hrsp (by omega) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [FromBytesPre.cursor, h0, h1, h2]
  · have hb8 := hcur.bytesOf
    rw [NativeRustc.length_wordBytes] at hb8
    rw [hb8, leNat_wordBytes]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  · exact hbuf ho h (by omega)
  · exact hbuf hoc hc (by omega)
  · exact hbuf hob hb (by omega)
  · exact P.apart_ad (by omega) (by fro) (by fro) (by omega) (by omega)
  · exact P.apart_ad (by omega) (by fro) (by fro) (by omega) (by omega)
  · exact P.apart_ad (by omega) (by fro) (by fro) (by omega) (by omega)

end

end

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

set_option linter.unusedSimpArgs false in
/-- **Parsing**: from the end of the copy to block 5. -/
public theorem parse {k : Nat} (hp : Placed code k)
    (hfb : Spec (label fromBytesLabel) FromBytesPre FromBytesPost) (P : Pre w m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + 49)) (h : LoopAt w m₀ st.data 50)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + 66) → Parsed w m₀ st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  have hsig := sig_of h
  have hmsg := msg_of h
  -- Block 3.
  let env := Env.ofMachine st.data [frR m₀] (fun _ => 0) (Host.addrOf (k + 49 + b3.length)).toBitVec
  have hwf : env.WF := frame_wf P C.kept
  have hm0 : Match env st3 st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.rsp.trans (ad_int m₀ 24).symm, trivial⟩ trivial trivial
      trivial
  obtain ⟨h0, h1, h2, hsp, hbx, h15, hbp, h12, h13, hw, hov1, hov2, hov3⟩ := st3_facts
  refine call_step (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b3 hwf rfl hpc hm0
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ (after b3 st3) st₁.data at hm₁
  have C₁ := Common.block P C hwf hm₁ hw
  have hx : ∀ {r : Reg64} {o : Nat}, (after b3 st3).reg r = some (.ptr 0 o) →
      reg st₁.data r = ad m₀ (fr + o) := fun hr => (hm₁.regs _ _ hr).trans (eval_ptr0 _)
  have hrsp₁ : rspOf st₁.data = ad m₀ (fr + 16) := hx hsp
  have hcur₁ : BytesAt st₁.data.dmem (ad m₀ (fr + 184)) (wordBytes (4 : Nat).toUInt64) := by
    have := hm₁.bytesAt_write (r := 0) rfl (by omega) st3_cursor
    rw [ad_add] at this
    rw [← regBytes_eq_wordBytes]
    exact this
  have hpk₁ : BytesAt st₁.data.dmem (ad m₀ (fr + 40)) (pkB w) := by
    unfold pkB NativeRustc.Xmss.pkBytes
    rw [wordsBytes_map]
    refine bytesAt_flatten 4 (fun _ _ => NativeRustc.length_wordBytes _) fun j hj => ?_
    have := hm₁.bytesAt_write (r := 0) (o := 40 + 8 * j) rfl (by omega) (st3_pk j hj)
    rw [ad_add, show fr + (40 + 8 * j) = fr + 40 + 8 * j by omega] at this
    rw [ad_add]
    rw [show (wordBytes ∘ w) j = regBytes (w j).toBitVec from
      (regBytes_eq_wordBytes _).symm]
    convert this using 1
    unfold regBytes
    congr 2
    show (w j).toBitVec = reg st.data _
    interval_cases j
    · exact h.rax.symm
    · exact h.rcx.symm
    · exact h.rdx.symm
    · exact h.rsi.symm
  have hkeep₁ : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5816 →
      firstOverlap 0 o bs.length (after b3 st3).mem = none →
      BytesAt st.data.dmem (ad m₀ (fr + o)) bs → BytesAt st₁.data.dmem (ad m₀ (fr + o)) bs :=
    fun hle hov hb => by
      have := hm₁.bytesAt_keep (r := 0) rfl hle hov (by rw [← ad_add] at hb; exact hb)
      rwa [ad_add] at this
  have hmsg₁ := hkeep₁ (by rw [length_msgB]; omega) (by rw [length_msgB]; exact hov1) hmsg
  have hli₁ := hkeep₁ (by rw [length_regBytes]; omega) (by rw [length_regBytes]; exact hov2) h.li8
  have hsig₁ := hkeep₁ (by rw [length_sigB]; omega) (by rw [length_sigB]; exact hov3) hsig
  -- `from_bytes` for the bottom layer.
  have hpre₁ : FromBytesPre st₁.data :=
    fromBytesPre P C₁ hrsp₁ (o := 3356) (oc := 184) (ob := 952) (hx h0) (hx h1) (hx h2)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hcur₁ (by omega)
  refine call_then hpc₁ hfb hpre₁ fun st₂ hpc₂ hrsp₂ hpost₂ => ?_
  obtain ⟨hout₂, hcur₂, hsame₂, hs₂⟩ := hpost₂
  simp only [FromBytesPre.bytes, FromBytesPre.cursor] at hout₂ hcur₂
  have hc4 : NativeRustc.leNat (bytesOf st₁.data.dmem (ad m₀ (fr + 184)) 8) = 4 := by
    have hb8 := hcur₁.bytesOf
    rw [NativeRustc.length_wordBytes] at hb8
    rw [hb8, leNat_wordBytes]
    rfl
  have hsb := hsig₁.bytesOf
  rw [length_sigB] at hsb
  rw [hx h0, hx h1, hx h2, hsb, hc4] at hout₂
  rw [hx h1, hc4] at hcur₂
  rw [hx h0, hx h1] at hsame₂
  change SameOutside _ _ (FromR m₀ st₁.data 3356 184) at hsame₂
  have C₂ := C₁.fromR P hs₂ hrsp₁ (by decide) (by decide) hsame₂
  have hk₂ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₁.data.dmem (ad m₀ (fr + x)) bs →
      24 ≤ x → x + bs.length ≤ 3356 → (x + bs.length ≤ 184 ∨ 192 ≤ x) →
      BytesAt st₂.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb h24 hx1 hx2 => keep_fromR P hrsp₁ (by decide) (by decide) hsame₂ hb (by omega)
      (by omega) (Or.inl hx1) hx2
  have hpk₂ := hk₂ hpk₁ (by omega) (by rw [length_pkB]; omega) (by rw [length_pkB]; omega)
  have hmsg₂ := hk₂ hmsg₁ (by omega) (by rw [length_msgB]; omega) (by rw [length_msgB]; omega)
  have hli₂ := hk₂ hli₁ (by omega) (by rw [length_regBytes]; omega)
    (by rw [length_regBytes]; omega)
  have hsig₂ := hk₂ hsig₁ (by omega) (by simp [length_sigB]) (by simp [length_sigB])
  have hrsp₂' : rspOf st₂.data = ad m₀ (fr + 24) := by rw [hrsp₂, hrsp₁, ad_add]
  -- Block 4.
  let env₃ := Env.ofMachine st₂.data [frR m₀] (fun _ => 0)
    (Host.addrOf (k + 62 + b4.length)).toBitVec
  have hwf₃ : env₃.WF := frame_wf P C₂.kept
  have hm₃ : Match env₃ st4 st₂.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hrsp₂'.trans (ad_int m₀ 24).symm,
      ((hs₂.1 .rbx rfl).trans ((hx hbx).trans (eval_ptr0 _).symm)),
      ((hs₂.1 .r15 rfl).trans ((hx h15).trans (eval_ptr0 _).symm)), trivial⟩
      trivial trivial trivial
  obtain ⟨g0, g1, g2, gsp, gk, gw⟩ := st4_facts
  refine call_step (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b4 hwf₃ rfl
    (hpc₂.trans rfl) hm₃ fun st₃ hpc₃ hm₃' => ?_
  change Match _ (after b4 st4) st₃.data at hm₃'
  have C₃ := Common.block P C₂ hwf₃ hm₃' gw
  have hy : ∀ {r : Reg64} {o : Nat}, (after b4 st4).reg r = some (.ptr 0 o) →
      reg st₃.data r = ad m₀ (fr + o) := fun hr => (hm₃'.regs _ _ hr).trans (eval_ptr0 _)
  have hrsp₃ : rspOf st₃.data = ad m₀ (fr + 16) := hy gsp
  have hk₃ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₂.data.dmem (ad m₀ (fr + x)) bs →
      24 ≤ x → x + bs.length ≤ 5816 → BytesAt st₃.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb h24 hle => frame_keep P hwf₃ hm₃' gw hb h24 hle
  have hcur₃ := hk₃ (x := 184) hcur₂ (by omega) (by rw [NativeRustc.length_wordBytes]; omega)
  have hsig₃ := hk₃ (x := 952) hsig₂ (by omega) (by rw [length_sigB]; omega)
  have hpre₃ : FromBytesPre st₃.data :=
    fromBytesPre P C₃ hrsp₃ (o := 4556) (oc := 184) (ob := 952) (hy g0) (hy g1) (hy g2)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hcur₃ (by omega)
  refine call_then hpc₃ hfb hpre₃ fun st₄ hpc₄ hrsp₄ hpost₄ => cont st₄ (hpc₄.trans rfl) ?_
  obtain ⟨hout₄, -, hsame₄, hs₄⟩ := hpost₄
  simp only [FromBytesPre.bytes, FromBytesPre.cursor] at hout₄
  have hc1204 : NativeRustc.leNat (bytesOf st₃.data.dmem (ad m₀ (fr + 184)) 8) = 1204 := by
    have hb8 := hcur₃.bytesOf
    rw [NativeRustc.length_wordBytes] at hb8
    rw [hb8, leNat_wordBytes]
    rfl
  have hsb₃ := hsig₃.bytesOf
  rw [length_sigB] at hsb₃
  rw [hy g0, hy g1, hy g2, hsb₃, hc1204] at hout₄
  rw [hy g0, hy g1] at hsame₄
  change SameOutside _ _ (FromR m₀ st₃.data 4556 184) at hsame₄
  have C₄ := C₃.fromR P hs₄ hrsp₃ (by decide) (by decide) hsame₄
  have hk₄ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₂.data.dmem (ad m₀ (fr + x)) bs →
      24 ≤ x → x + bs.length ≤ 4556 → (x + bs.length ≤ 184 ∨ 192 ≤ x) →
      BytesAt st₄.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb h24 hx1 hx2 => keep_fromR P hrsp₃ (by decide) (by decide) hsame₄
      (hk₃ hb h24 (by omega)) (by omega) (by omega) (Or.inl hx1) hx2
  have hreg : ∀ r ∈ [Reg64.rbp, .r12, .r13], reg st₄.data r = reg st₂.data r := by
    intro r hr
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    have hcs : calleeSaved r = true := by rcases hr' with rfl | rfl | rfl <;> rfl
    exact (hs₄.1 r hcs).trans (hm₃'.regs _ _ (gk r hr))
  refine ⟨C₄, ?_, ?_, ?_, ?_, hk₄ hpk₂ (by omega) (by rw [length_pkB]; omega)
      (by rw [length_pkB]; omega),
    hk₄ hmsg₂ (by omega) (by rw [length_msgB]; omega) (by rw [length_msgB]; omega),
    hk₄ hli₂ (by omega) (by rw [length_regBytes]; omega) (by rw [length_regBytes]; omega),
    hk₄ hout₂ (by omega) (by rw [bottomL, length_memBytes (by rw [length_sigB]; omega)])
      (by rw [bottomL, length_memBytes (by rw [length_sigB]; omega)]; omega), hout₄⟩
  · rw [hrsp₄, hrsp₃, ad_add]
  · exact (hreg .rbp (by simp)).trans ((hs₂.1 .rbp rfl).trans (hx hbp))
  · exact (hreg .r12 (by simp)).trans ((hs₂.1 .r12 rfl).trans (hx h12))
  · exact (hreg .r13 (by simp)).trans ((hs₂.1 .r13 rfl).trans ((hm₁.regs _ _ h13).trans h.r13))

end NativeRustcX64.Xmss.XmssVerify
