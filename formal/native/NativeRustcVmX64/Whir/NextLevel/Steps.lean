module

public import NativeRustcVmX64.Whir.NextLevel.Frame

/-!
# `next_level`: blocks' bytes, the exits (x86-64)

Bytes of the frame a block does not write (`Ctx.bytes_blk`) or a call does not change
(`Ctx.bytes_call`); the environments of the body's blocks (`Ctx.wf0`, `Ctx.wf1`); the exit at
`.LNextLevel_14` (`exit_spec`: AL R15's low byte, the registers restored, `ret`), at
`.LNextLevel_13` (`fail_spec`: AL `0`), and the postcondition on a rejection (`post_none`).
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel

public section

/-- **Bytes of the frame a call does not change.** -/
theorem bytes_call {m0 d d' : MachineData} {o lo n : Nat}
    (hk : ∀ j, o + 8 ≤ j → j < 8192 → (j < lo ∨ lo + n ≤ j) →
      d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j))
    {j : Nat} {bs : List UInt8} (hj : o + 8 ≤ j) (hjn : j + bs.length ≤ 8192)
    (hmiss : j + bs.length ≤ lo ∨ lo + n ≤ j) (h : NativeRustcVm.BytesAt d.dmem (loc m0 j) bs) :
    NativeRustcVm.BytesAt d'.dmem (loc m0 j) bs := by
  intro i hi
  have := h i hi
  rw [off_add] at this ⊢
  rw [hk (j + i) (by omega) (by omega) (by omega)]
  exact this


theorem al_trunc (x : BitVec 64) : (UnOp.apply .trunc .W32 x).toNat % 256 = x.toNat % 256 := by
  simp only [UnOp.apply, ext, low, BitVec.toNat_setWidth]
  show x.toNat % 2 ^ 32 % 2 ^ 64 % 256 = _
  omega

theorem cAl_eval [Labels] (env : Env) :
    cAl.eval env = decide ((env.regs .rax).toNat % 256 = 0) := by
  simp only [cAl, SBool.eval, Sym.eval]
  exact testAl_eq _

theorem okWord_toNat (b : Bool) : (okWord b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s level w rounds m0)
include c

/-- The environment of a body block: the frame's region, then `rest`. -/
theorem wf0 {d : MachineData} (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} :
    (argEnv m0 d 8176 8 [] (fun _ ↦ 0) ret).WF :=
  argEnv_wf (c.region_ok hk) (by simp) (List.pairwise_singleton _ _)

/-- The environment of a body block with one more region `x` (`n` bytes), apart. -/
theorem wf1 {d : MachineData} (hk : Kept m0.dmem d.dmem) {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Mapped d.dmem x n) (hnw : x.toNat + n ≤ 2 ^ 64)
    (hap : x.toNat + n ≤ (rspOf m0).toNat - 8176 ∨ (rspOf m0).toNat + 16 ≤ x.toNat)
    {ret : BitVec 64} : (argEnv m0 d 8176 8 [(x, n)] (fun _ ↦ 0) ret).WF := by
  have hf := c.fa_toNat
  have := c.geo.hN
  refine argEnv_wf (c.region_ok hk) (fun y hy ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hy; subst hy; exact ⟨hx, hnw⟩
  · show (fa m0).toNat + (8176 + 8 + 8) ≤ x.toNat ∨ x.toNat + n ≤ (fa m0).toNat
    rw [hf]; omega

omit c in
/-- **Bytes of the frame a block does not write.** -/
theorem bytes_blk {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hwf : (argEnv m0 d 8176 8 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (argEnv m0 d 8176 8 rest (fun _ ↦ 0) ret) S d')
    (hin : writesIn S = true) {rs : List (Nat × Nat)} (hW : Wr rs S) {j : Nat} {bs : List UInt8}
    (hj : j + bs.length ≤ 8192) (hmiss : ∀ p ∈ rs, p.2 ≤ j ∨ j + bs.length ≤ p.1)
    (h : NativeRustcVm.BytesAt d.dmem (loc m0 j) bs) :
    NativeRustcVm.BytesAt d'.dmem (loc m0 j) bs := by
  intro i hi
  have := h i hi
  rw [off_add] at this ⊢
  rw [hm.get?_mem0 hwf (not_written0A hwf hm hin (by omega) fun w hw _ ↦ ?_)]
  · exact this
  · obtain ⟨-, p, hp, h1, h2⟩ := hW w hw
    rcases hmiss p hp with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end Ctx

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The exit** at `.LNextLevel_14`: AL R15's low byte, the registers restored, `ret`. -/
theorem exit_spec (hp : Placed code k) (c : Ctx a s level w rounds m0) {st : MachineState}
    (hf : Fr m0 72 st.data) (hpc : st.pc = Host.addrOf (k + 260)) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
        boolRet st'.data = (reg st.data .r15).toNat % 256 ∧ st'.data.dmem = st.data.dmem ∧
        Saved m0 st'.data) st := by
  have hwf := c.wf0 hf.frame.kept (ret := 0)
  have hm : Match (argEnv m0 st.data 8176 8 []) retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hf.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b27_in_code (by simp [b27]) hp) exit_b27 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := ok_b27
  obtain ⟨hsv, hrsp⟩ := Frame.epilogueA hf.frame hwf hm' hepi
  simp only [PcOk, Sym.eval] at hpc'
  refine .done _ ⟨hpc'.trans (Frame.load_retA hf.frame c.stack (by rw [stack_eq]; omega)), hrsp,
    ?_, hm'.dmem_eq hwf hmem, hsv⟩
  rw [boolRet, show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
  exact al_trunc _

/-- **A failure** at `.LNextLevel_13`: R15 cleared, then the exit; AL `0`. -/
theorem fail_spec (hp : Placed code k) (c : Ctx a s level w rounds m0) {st : MachineState}
    (hf : Fr m0 72 st.data) (hpc : st.pc = Host.addrOf (k + 258)) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
        boolRet st'.data = 0 ∧ st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hwf := c.wf0 hf.frame.kept (ret := 0)
  have hm : Match (argEnv m0 st.data 8176 8 []) retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hf.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b26_in_code (by simp [b26]) hp) exit_b26 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hr15⟩ := ok_b26
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  have hf1 : Fr m0 72 st1.data :=
    ⟨Frame.of_blockA hf.frame hwf hm1 hmid slots_le, by rw [Sm, hd]; exact hf.same⟩
  have h0 : reg st1.data .r15 = 0 := hm1.regs .r15 _ hr15
  simp only [PcOk] at hpc1
  exact Eventually.mono (exit_spec hp c hf1 hpc1) fun st' ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, by rw [h3, h0]; rfl, h4.trans hd, h5⟩

omit [Host] in
/-- The frame's changes are the contract's. -/
theorem changes_of {d : MachineData} (hs : Sm m0 d) :
    ChangesIn m0 d nextLevelStack [⟨pA m0, whirBytes⟩, ⟨tA m0, tstateBytes⟩] :=
  NativeRustcVm.SameOutside.mono hs fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact Or.inr hq
    · exact Or.inl ⟨_, List.mem_cons_self, hq⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩

/-- **A rejection**, from a state of the frame at `.LNextLevel_13`. -/
theorem none13 (hp : Placed code k) (c : Ctx a s level w rounds m0) {st : MachineState}
    (hf : Fr m0 72 st.data) (hpc : st.pc = Host.addrOf (k + 258))
    (hnone : runN level w rounds m0 s = none) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  simp only [runN] at hnone
  refine Eventually.mono (fail_spec hp c hf hpc) fun st' ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, ?_, ?_, ?_, ?_, h5⟩
  · show boolRet st'.data = _
    rw [h3, hnone]; rfl
  · intro x s' h; rw [hnone] at h; cases h
  · intro x s' h; rw [hnone] at h; cases h
  · unfold ChangesIn; rw [h4]; exact changes_of hf.same

/-- **A rejection**, from a state of the frame at `.LNextLevel_14` with R15 `0`. -/
theorem none14 (hp : Placed code k) (c : Ctx a s level w rounds m0) {st : MachineState}
    (hf : Fr m0 72 st.data) (hpc : st.pc = Host.addrOf (k + 260)) (h15 : reg st.data .r15 = 0)
    (hnone : runN level w rounds m0 s = none) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  simp only [runN] at hnone
  refine Eventually.mono (exit_spec hp c hf hpc) fun st' ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, ?_, ?_, ?_, ?_, h5⟩
  · show boolRet st'.data = _
    rw [h3, h15, hnone]; rfl
  · intro x s' h; rw [hnone] at h; cases h
  · intro x s' h; rw [hnone] at h; cases h
  · unfold ChangesIn; rw [h4]; exact changes_of hf.same

end

end NativeRustcVmX64.Whir.Levels.NL
