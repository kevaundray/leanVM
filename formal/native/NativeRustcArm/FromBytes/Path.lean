module

public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.FromBytes.Mid
public import NativeRustcArm.FromBytes.PathExec

/-!
# `from_bytes`'s closure: the path

Blocks 5 to 21 (`NativeRustcArm.FromBytes.PathExec`): the bounds checks `pos + 928 < 2373` and
`pos + 928 ≤ 2356 - 16 j` hold (`pos ≤ 1204`), the 16 path nodes are copied from the signature to
the frame at `944`, the cursor becomes `pos + 1200`, and the code calls
`memcpy(out, frame + 944, 256)` (`PathCall`).
-/

namespace NativeRustcArm.Xmss.FromBytes

open NativeRustcArm.Sym NativeArm

set_option Elab.async false

/-- The environment at block 5. -/
def envP (m₀ m : MachineData) : Env :=
  Env.ofMachine m [(frame m₀, 1936), (cur m₀, 8), (sig m₀ + BitVec.ofNat 64 (pos m₀), 1200)]

theorem hs_false [Labels] {env : Env} {v N : Nat} (hx : env.regs .X22 = BitVec.ofNat 64 v) (h : v < N)
    (hN : N < 2 ^ 64) :
    (SBool.not (SBool.cmp .ult .W64 (.reg .X22) (.lit N))).eval env = false := by
  simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, hx]
  simp [BitVec.ult]
  omega

theorem hi_false [Labels] {env : Env} {v N : Nat} (hx : env.regs .X22 = BitVec.ofNat 64 v) (h : v ≤ N)
    (hN : N < 2 ^ 64) :
    (SBool.and (SBool.not (SBool.cmp .ult .W64 (.reg .X22) (.lit N)))
      (SBool.not (SBool.cmp .eq .W64 (.reg .X22) (.lit N)))).eval env = false := by
  simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, hx]
  by_cases hlt : v < N
  · simp [BitVec.ult]
    omega
  · have : v = N := by omega
    subst this
    simp

theorem ofNat_add_lit' (x c : Nat) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 c = BitVec.ofNat 64 (x + c) := (BitVec.ofNat_add x c).symm

section
variable {m₀ m : MachineData}

theorem envP_wf (P : Pre m₀) (C : Common m₀ m) : (envP m₀ m).WF := by
  have := P.pos
  exact Env.wf_of ⟨⟨P.frameMapped.kept C.kept, P.frameNW⟩, ⟨P.curMapped.kept C.kept, P.curNW⟩,
    ⟨(P.sigMapped.sub (by omega)).kept C.kept, NoWrap.sub P.sigNW (by omega)⟩, trivial⟩
    (pairwise3 P.curF.symm (P.sigF.symm.sub_right P.sigNW (by omega) (by omega))
      (P.curSig.sub_right P.sigNW (by omega) (by omega)))

theorem match_envP [Labels] (P : Pre m₀) (h : MidAt m₀ m) : Match (envP m₀ m) stP0 m := by
  have C := h.common
  unfold envP stP0
  apply match_ofMachine
  · exact And.intro rfl (And.intro (fun _ => P.frame16) (And.intro rfl (And.intro (by simp)
      (And.intro rfl (And.intro (by simp) trivial)))))
  · rw [C.sp]
    simp [Sym.eval]
  · exact ⟨C.x21.trans (by simp [Sym.eval]), trivial⟩
  · exact trivial
  · exact trivial
  · refine ⟨?_, allOf_map_range fun j hj => ?_⟩
    · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, C.x20, h.x23,
        Env.base_ofMachine_eq]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some, BitVec.ofInt_natCast, addr_add_addr]
    · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, C.x20, h.x22,
        Env.base_ofMachine_eq]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some, BitVec.ofInt_natCast, addr_add_addr]
      rw [ofNat_add_lit', show pos m₀ + 928 + (32 + 16 * j) = pos m₀ + (960 + 16 * j) by omega]

end

/-- The machine state at the `memcpy` of the path. -/
theorem pathCall [Labels] {m₀ m m' : MachineData} (P : Pre m₀) (h : MidAt m₀ m)
    (hm : Match (envP m₀ m) stP17 m') : PathCall m₀ m' := by
  have C := h.common
  have hwf := envP_wf P C
  have := P.pos
  have hs : Saved m m' := Match.saved (match_envP P h) hm hwf rfl stP17_keeps
  have hr0 : (envP m₀ m).regions[0]? = some (frame m₀, 1936) := rfl
  have hfr : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1936 →
      firstOverlap 0 o bs.length stP17.mem = none →
      BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 o) bs →
      BytesAt m'.dmem (frame m₀ + BitVec.ofNat 64 o) bs :=
    fun hle hc h0 => hm.bytesAt_keep hr0 hle hc h0
  refine ⟨common_of_saved C hs ?_ (fun j hj => hfr (by rw [length_regBytes]; omega)
      (by rw [length_regBytes]; exact stP17_save j hj) (C.save j hj))
      (bytesAt_add_zero (hfr (by rw [P.rand_length]; omega) (by rw [P.rand_length]; exact stP17_rand)
        (by simpa using C.rand))), ?_, ?_, ?_, ?_,
    hfr (by rw [length_chainBytes P]; omega) (by rw [length_chainBytes P]; exact stP17_chain) h.chain,
    ?_⟩
  · refine (C.same.trans (hm.sameOutside_in hwf stP17_writes)).mono fun p hp => ?_
    rcases hp with hp | ⟨r, hr, b, sz, hb, hin⟩
    · exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · cases hb
        exact Or.inl hin
      · cases hb
        exact Or.inr hin
  · exact (hm.regs .X0 (.reg .X19) stP17_regs.1).trans C.x19
  · exact (hm.regs .X1 (.ptr 0 944) stP17_regs.2.1).trans (by simp [Sym.eval, envP])
  · exact hm.regs .X2 (.lit 256) stP17_regs.2.2
  · have := bytesAt_add_zero (hm.bytesAt_write (r := 1) (o := 0) (n := 8) rfl (by omega)
      stP17_cursor)
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, envP, h.x22,
      ofNat_add_lit'] at this
    exact this
  · refine bytesAt_flatten 16 (fun j hj => P.pathSlot_length hj) fun j hj => ?_
    rw [addr_add_addr]
    refine bytesAt_slice (by omega) fun t ht => ?_
    rw [addr_add_addr]
    have hg := hm.get?_load (r := 0) hr0 (by omega) (stP17_path j hj t ht) (by omega) (le_refl 8)
    rw [hg, show 944 + 16 * j + 8 * (t / 8) + t % 8 = 944 + 16 * j + t by omega]
    simp only [Env.base_ofMachine_eq, envP, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some, Env.ofMachine_mem0, addr_add_addr]
    rw [C.same _ (P.sig_not_scratch (by omega)),
      show pos m₀ + (944 + 16 * j + t) = pos m₀ + 944 + 16 * j + t by omega]
    rfl

/-- **The path**: from block 5 to the call `memcpy(out, frame + 944, 256)`. -/
public theorem path [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData} (P : Pre m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.FromBytes.b5Offset)) (h : MidAt m₀ st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Labels.label NativeRustcArm.Common.Memcpy.entryLabel → retOf st'.data = Host.addrOf (k + NativeRustcArm.Xmss.FromBytes.b22Offset) →
      PathCall m₀ st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := envP_wf P h.common
  have := P.pos
  have hx22 : (envP m₀ st.data).regs .X22 = BitVec.ofNat 64 (pos m₀ + 928) := h.x22
  refine cond_step (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) b5_execP hwf hpc
    (match_envP P h) (hs_false hx22 (by omega) (by decide)) fun s1 hpc1 hm1 => ?_
  refine cond_step (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) b6_execP hwf
    (hpc1.trans rfl) hm1 (hi_false hx22 (by omega) (by decide)) fun s2 hpc2 hm2 => ?_
  refine cond_step (b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) b7_execP hwf
    (hpc2.trans rfl) hm2 (hi_false hx22 (by omega) (by decide)) fun s3 hpc3 hm3 => ?_
  refine cond_step (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) b8_execP hwf
    (hpc3.trans rfl) hm3 (hi_false hx22 (by omega) (by decide)) fun s4 hpc4 hm4 => ?_
  refine cond_step (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) b9_execP hwf
    (hpc4.trans rfl) hm4 (hi_false hx22 (by omega) (by decide)) fun s5 hpc5 hm5 => ?_
  refine cond_step (b10_in_code.trans hp.1 (List.cons_ne_nil _ _)) b10_execP hwf
    (hpc5.trans rfl) hm5 (hi_false hx22 (by omega) (by decide)) fun s6 hpc6 hm6 => ?_
  refine cond_step (b11_in_code.trans hp.1 (List.cons_ne_nil _ _)) b11_execP hwf
    (hpc6.trans rfl) hm6 (hi_false hx22 (by omega) (by decide)) fun s7 hpc7 hm7 => ?_
  refine cond_step (b12_in_code.trans hp.1 (List.cons_ne_nil _ _)) b12_execP hwf
    (hpc7.trans rfl) hm7 (hi_false hx22 (by omega) (by decide)) fun s8 hpc8 hm8 => ?_
  refine cond_step (b13_in_code.trans hp.1 (List.cons_ne_nil _ _)) b13_execP hwf
    (hpc8.trans rfl) hm8 (hi_false hx22 (by omega) (by decide)) fun s9 hpc9 hm9 => ?_
  refine cond_step (b14_in_code.trans hp.1 (List.cons_ne_nil _ _)) b14_execP hwf
    (hpc9.trans rfl) hm9 (hi_false hx22 (by omega) (by decide)) fun s10 hpc10 hm10 => ?_
  refine cond_step (b15_in_code.trans hp.1 (List.cons_ne_nil _ _)) b15_execP hwf
    (hpc10.trans rfl) hm10 (hi_false hx22 (by omega) (by decide)) fun s11 hpc11 hm11 => ?_
  refine cond_step (b16_in_code.trans hp.1 (List.cons_ne_nil _ _)) b16_execP hwf
    (hpc11.trans rfl) hm11 (hi_false hx22 (by omega) (by decide)) fun s12 hpc12 hm12 => ?_
  refine cond_step (b17_in_code.trans hp.1 (List.cons_ne_nil _ _)) b17_execP hwf
    (hpc12.trans rfl) hm12 (hi_false hx22 (by omega) (by decide)) fun s13 hpc13 hm13 => ?_
  refine cond_step (b18_in_code.trans hp.1 (List.cons_ne_nil _ _)) b18_execP hwf
    (hpc13.trans rfl) hm13 (hi_false hx22 (by omega) (by decide)) fun s14 hpc14 hm14 => ?_
  refine cond_step (b19_in_code.trans hp.1 (List.cons_ne_nil _ _)) b19_execP hwf
    (hpc14.trans rfl) hm14 (hi_false hx22 (by omega) (by decide)) fun s15 hpc15 hm15 => ?_
  refine cond_step (b20_in_code.trans hp.1 (List.cons_ne_nil _ _)) b20_execP hwf
    (hpc15.trans rfl) hm15 (hi_false hx22 (by omega) (by decide)) fun s16 hpc16 hm16 => ?_
  refine call_step (b21_in_code.trans hp.1 (List.cons_ne_nil _ _)) b21_execP hwf
    (hpc16.trans rfl) hm16 fun s hpc' hm => cont s (hpc'.1) (hpc'.2.trans rfl) ?_
  exact pathCall P h hm

end NativeRustcArm.Xmss.FromBytes
