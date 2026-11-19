module

public import NativeRustcX64.FromBytes.Inv
meta import NativeRustcX64.FromBytes.Inv
meta import NativeRustcX64.Code.Xmss.FromBytes

/-!
# `from_bytes`'s closure: the prologue and the randomizer

Blocks 0 and 1 from the entry: the prologue pushes the callee-saved registers, reads the cursor
`pos`, stores `pos + 16` (the bounds check `pos < 2389` holds), copies the randomizer's 16 bytes to
the frame, and sets up the loop over the chain values (`LoopAt` before turn `0`). One environment:
region 0 the stack, 1 the cursor, 2 the randomizer; the address `rdx + pos` an alias of region 2.
-/

namespace NativeRustcX64.Xmss.FromBytes

open NativeRustcX64.Sym

set_option Elab.async false

/-- The symbolic state at the entry. -/
@[expose] public def stA : SState :=
  init [1928, 8, 16] [(.rsp, .ptr 0 1920), (.rsi, .ptr 1 0)] [] []
  [(.bin .add .W64 (.reg .rdx) (.load 1 0 8), (2, 0))]

sym_block b0_execA := exec b0 stA

/-- The symbolic state after block 0. -/
@[expose] public def stA1 : SState := ((exec b0 stA).getD (stA, .fall)).1

sym_block b1_execA := exec b1 stA1

/-- The symbolic state after block 1. -/
@[expose] public def stA2 : SState := ((exec b1 stA1).getD (stA, .fall)).1

theorem stA2_save : ∀ j < 5, ∀ i < 8,
    findWrite 0 (1880 + 8 * j + i) stA2.mem = some (.reg (saveRegs.getD j .rax), i) := by
  decide +kernel

theorem stA2_rand : ∀ t < 16,
    findWrite 0 (8 + t) stA2.mem = some (.load 2 (8 * (t / 8)) 8, t % 8) := by
  decide +kernel

theorem stA2_cursor : ∀ i < 8,
    findWrite 1 (0 + i) stA2.mem = some (.bin .add .W64 (.load 1 0 8) (.lit 16), i) := by
  decide +kernel

theorem stA2_writes : writesBelow stA2 [(0, 1920), (1, 8)] = true := by decide +kernel

theorem stA2_regs : stA2.reg .rax = some (.lit 0) ∧ stA2.reg .rbx = some (.reg .rdi) ∧
    stA2.reg .rcx = some (.bin .add .W64 (.lit 32) (.bin .add .W64 (.reg .rdx) (.load 1 0 8))) ∧
    stA2.reg .rsi = some (.ptr 0 24) ∧ stA2.reg .rdi = some (.load 1 0 8) ∧
    stA2.reg .rsp = some (.ptr 0 8) ∧ stA2.reg .rbp = some (.reg .rbp) ∧
    stA2.reg .r14 = some (.reg .rdx) ∧ stA2.reg .r15 = some (.ptr 1 0) := by
  decide +kernel

/-- The environment at the entry. -/
@[expose] public def envA (m₀ : MachineData) : Env :=
  Env.ofMachine m₀ [(base m₀, 1928), (cur m₀, 8), (sig m₀ + BitVec.ofNat 64 (pos m₀), 16)]

theorem envA_wf {m₀ : MachineData} (P : Pre m₀) : (envA m₀).WF :=
  Env.wf_of ⟨⟨P.stackMapped, P.baseNW⟩, ⟨P.curMapped, P.curNW⟩,
    ⟨P.sigMapped.sub (by have := P.pos; omega), NoWrap.sub P.sigNW (by have := P.pos; omega)⟩,
    trivial⟩
    (pairwise3 P.curF.symm (P.sigF.symm.sub_right P.sigNW (by have := P.pos; omega) (by omega))
      (P.curSig.sub_right P.sigNW (by have := P.pos; omega) (by omega)))

theorem envA_load {m₀ : MachineData} (P : Pre m₀) :
    (envA m₀).load 1 0 8 = BitVec.ofNat 64 (pos m₀) := by
  rw [Env.load_of_bytesAt (bs := bytesOf m₀.dmem (cur m₀) 8) (length_bytesOf _ _ _)
    (by simpa [envA, Env.base] using bytesAt_bytesOf P.curMapped), ofBytes_eq_leNat]
  rfl

theorem envA_ptr0 [Labels] (m₀ : MachineData) (o : Nat) :
    (Sym.ptr 0 o).eval (envA m₀) = base m₀ + BitVec.ofNat 64 o := by
  simp [Sym.eval, Env.base, envA]

theorem match_envA [Labels] {m₀ : MachineData} (P : Pre m₀) : Match (envA m₀) stA m₀ := by
  unfold envA stA
  apply match_ofMachine
  · exact ⟨rfl, rfl, rfl, trivial⟩
  · refine ⟨?_, ?_, trivial⟩
    · show m₀.regs.get64 .rsp = _
      rw [show m₀.regs.get64 .rsp = rspOf m₀ from rfl, P.rsp_eq]
      simp [Sym.eval, Env.base]
    · simp [Sym.eval, Env.base, cur]
  · exact trivial
  · exact trivial
  · refine ⟨?_, trivial⟩
    have h := envA_load P
    unfold envA at h
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h]
    simp [Env.base, sig]

/-- **The prologue and the randomizer**: from the entry to the loop's head before turn `0`. -/
public theorem head [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData}
    (hpre : FromBytesPre m₀) {R : MachineState → Prop}
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (k + 24) → LoopAt m₀ st.data 0 →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m₀, Host.addrOf k⟩ := by
  have P := pre_of hpre
  have hwf := envA_wf P
  have hnb :
      (SBool.not (SBool.cmp .ult .W64 (.load 1 0 8) (.lit 2389))).eval (envA m₀) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, envA_load P]
    have := P.pos
    simp [BitVec.ult]
    omega
  refine cond_step (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) b0_execA hwf rfl (match_envA P)
    hnb fun st₁ hpc₁ hm₁ => ?_
  refine fall_step (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) b1_execA hwf hpc₁ hm₁
    fun st₂ hpc₂ hm₂ => ?_
  change Match _ stA2 st₂.data at hm₂
  obtain ⟨hax, hbx, hcx, hsi, hdi, hsp, hbp, h14, h15⟩ := stA2_regs
  refine cont st₂ hpc₂ ⟨⟨?_, ?_, ?_, ?_, hm₂.kept hwf, ?_, ?_⟩, by omega, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, fun j hj => absurd hj (by omega)⟩
  · exact (hm₂.regs .r15 _ h15).trans (by simp [Sym.eval, Env.base, envA, cur])
  · exact hm₂.regs .rbp _ hbp
  · exact (hm₂.regs .rsp _ hsp).trans (envA_ptr0 m₀ 8)
  · exact (hm₂.sameOutside_below hwf stA2_writes).mono fun p ⟨rb, hrb, b, sz, hb, hin⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
      rcases hrb with rfl | rfl
      · simp only [envA, Env.ofMachine_regions] at hb
        cases hb
        exact Or.inl hin
      · simp only [envA, Env.ofMachine_regions] at hb
        cases hb
        exact Or.inr hin
  · exact fun j hj => hm₂.bytesAt_write (r := 0) rfl (by omega) (stA2_save j hj)
  · refine bytesAt_slice (by have := P.pos; omega) fun t ht => ?_
    rw [addr_add_addr,
      hm₂.get?_load (r := 0) rfl (by omega) (stA2_rand t ht) (by omega) (le_refl 8),
      show 8 * (t / 8) + t % 8 = t by omega]
    simp [Env.base, envA, addr_add_addr]
    rfl
  · exact hm₂.regs .rbx _ hbx
  · exact hm₂.regs .r14 _ h14
  · exact hm₂.regs .rax _ hax
  · exact (hm₂.regs .rdi _ hdi).trans (by simp only [Sym.eval]; exact envA_load P)
  · rw [hm₂.regs .rcx _ hcx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, envA_load P]
    rw [show (envA m₀).regs .rdx = sig m₀ from rfl, BitVec.add_comm, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  · exact (hm₂.regs .rsi _ hsi).trans (envA_ptr0 m₀ 24)
  · have := bytesAt_add_zero
      (hm₂.bytesAt_write (r := 1) (o := 0) (n := 8) rfl (by omega) stA2_cursor)
    have hv : (Sym.bin .add .W64 (.load 1 0 8) (.lit 16)).eval (envA m₀) =
        BitVec.ofNat 64 (pos m₀ + 16 + 32 * 0) := by
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, envA_load P]
      rw [show pos m₀ + 16 + 32 * 0 = pos m₀ + 16 by omega, BitVec.ofNat_add]
    rw [hv] at this
    simpa [envA, Env.base, cur, regBytes] using this

end NativeRustcX64.Xmss.FromBytes
