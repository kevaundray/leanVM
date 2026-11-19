module

public import NativeRustcX64.KeccakF.RoundLanes

/-!
# One turn of `keccak_f`'s round loop (x86-64)

`round_step`: from the loop head after `i < 24` rounds (`At m0 i`), the machine inevitably reaches
the loop invariant after `i + 1` rounds, back at the loop head (`.LKeccakF_1`) or, after the 24th,
at the epilogue. The loop body runs in a fresh environment of the machine at the head (regions:
the frame and the round constants), computes the round (`body_lanes`, the lanes by `lane_round`,
the parities by `par_round`), advances the counter, and keeps the state pointer, the pushed
registers and memory outside the frame.
-/

namespace NativeRustcX64.KeccakF

open NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics LeanVM.Parameters

public section

theorem stAfter_succ (m0 : MachineData) {i : Nat} (hi : i < 24) :
    stAfter m0 (i + 1) = Keccak.round (stAfter m0 i) (keccakRC.getD i 0) :=
  roundsTo_succ _ hi

theorem b1_length : Common.KeccakF.b1.length = 250 := by decide +kernel

theorem length_rcBytes : rcBytes.length = 192 := by
  rw [show rcBytes = Native.Keccak.wordsBytes keccakRC from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  rfl

section
variable [Labels]

/-- At the loop head, the round constants are the entry's. -/
theorem rcAt_of_at {m0 m : MachineData} {i : Nat} (hpre : KeccakFPre m0) (hA : At m0 i m) :
    BytesAt m.dmem rcAddr rcBytes := by
  obtain ⟨hstk, ⟨hrc, hnw, hap⟩, -⟩ := hpre
  intro p hp
  rw [hA.same _ ?_]
  · exact hrc p hp
  have hf := frame_noWrap hstk
  rw [length_rcBytes] at hp
  rw [inRange_iff (by unfold NoWrap at hf; omega), toNat_add_ofNat _ _ (by unfold NoWrap at hnw; omega)]
  unfold Apart at hap
  unfold frame
  simp only [keccakFStack] at hap ⊢
  omega

end

variable [Host]

/-- **One round of the loop.** -/
theorem round_step {k : Nat} (hp : Placed Common.KeccakF.code k) {m0 : MachineData}
    (hpre : KeccakFPre m0) {i : Nat} (hi : i < 24) {m : MachineData} (hA : At m0 i m) :
    Eventually (step1 Host.exe) (fun st => At m0 (i + 1) st.data ∧
      st.pc = if i + 1 = 24 then Host.addrOf (k + 329) else Host.addrOf (k + 79))
      ⟨m, Host.addrOf (k + 79)⟩ := by
  have hstk := hpre.1
  have hrc := rcAt_of_at hpre hA
  have hnw := hpre.2.1.2.1
  have hap := hpre.2.1.2.2
  have hk : Common.KeccakF.b1.IsInfixAt Host.prog (k + 79) :=
    Common.KeccakF.b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine m [(frame m0, 248), (rcAddr, 192)]
  have hb0 : env.regions[0]? = some (frame m0, 248) := rfl
  have hwf : env.WF := by
    refine Env.wf_of ⟨⟨fun j hj => hA.kept _ (hstk.2.2 j hj), frame_noWrap hstk⟩,
      ⟨fun j hj => ?_, hnw⟩, trivial⟩ (List.pairwise_pair.mpr hap.symm)
    have := hrc j (by rw [length_rcBytes]; exact hj)
    show (m.dmem.get? _).isSome
    rw [this]
    rfl
  have hctr : env.load 0 152 8 = BitVec.ofNat 64 (8 * i) := load_of_wordAt (r := 0) hA.ctr
  have hm : Match env startBody m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨show rspOf m = _ from hA.rsp.trans rfl, trivial⟩ ⟨rfl, trivial⟩
      ⟨show (env.load 0 152 8).toNat < 185 by rw [hctr]; simp; omega, trivial⟩ trivial
  have hrcl : env.load 1 (env.load 0 152 8).toNat 8 = (keccakRC.getD i 0).toBitVec := by
    rw [hctr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact load_rc hrc hi
  refine exec_then hk body hwf nofun hm fun st hm' hpc => .done _ ⟨?_, ?_⟩
  · obtain ⟨hregs, hslots, hpar⟩ := body_lanes body hm' hb0 hA.regs
      (allOf_imp (fun p _ h => load_of_wordAt (r := 0) h) hA.slots) hA.par hrcl
    have hl : ∀ p ∈ laneRegs, p.2 < 25 := by decide
    have hs : ∀ p ∈ laneSlots, p.2 < 25 := by decide
    have hc : ∀ p ∈ parRegs, p.2 < 5 := by decide
    have hsv := hA.saved
    simp only [AllOf, savedSlots] at hsv
    obtain ⟨s0, s1, s2, s3, s4, s5, -⟩ := hsv
    refine ⟨(hm'.regs .rsp _ rfl).trans ?_, ?_, wordAt_keep hm' hb0 (by decide) rfl hA.ptr, ?_, ?_,
      ?_, ⟨wordAt_keep hm' hb0 (by decide) rfl s0, wordAt_keep hm' hb0 (by decide) rfl s1,
        wordAt_keep hm' hb0 (by decide) rfl s2, wordAt_keep hm' hb0 (by decide) rfl s3,
        wordAt_keep hm' hb0 (by decide) rfl s4, wordAt_keep hm' hb0 (by decide) rfl s5, trivial⟩,
      fun p hp => (same_region hm' hwf hb0 (by decide) (by decide) p hp).trans (hA.same p hp),
      fun p h => hm'.kept hwf p (hA.kept p h)⟩
    · rfl
    · refine wordAt_of_eq (wordAt_write hm' hb0 (by decide) rfl) ?_
      sym_simp
      rw [hctr, BitVec.ofNat_add_ofNat]
      rfl
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 hi, lane_round _ _ (hl p hp)]
        exact h) hregs
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 hi, lane_round _ _ (hs p hp)]
        exact h) hslots
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 hi, par_round _ _ (hc p hp)]
        exact h) hpar
  · have hlab : Labels.label ".LKeccakF_1" = Host.addrOf (k + 79) :=
      hp.label (j := 79) rfl
    simp only [PcOk] at hpc
    rw [hpc, hlab]
    sym_simp
    rw [hctr, b1_length]
    by_cases h : i + 1 = 24
    · obtain rfl : i = 23 := by omega
      rfl
    · have hne : BitVec.ofNat 64 (8 * i) + 8#64 ≠ 192#64 := by
        intro he
        have := congrArg BitVec.toNat he
        simp at this
        omega
      have hb : (BitVec.ofNat 64 (8 * i) + 8#64 == 192#64) = false := beq_false_of_ne hne
      simp only [hb, h, Bool.not_false, ↓reduceIte]

end

end NativeRustcX64.KeccakF
