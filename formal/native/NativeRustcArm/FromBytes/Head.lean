module

public import NativeRustcArm.FromBytes.Inv
meta import NativeRustcArm.Code.Xmss.FromBytes

/-!
# `from_bytes`'s closure: the prologue and the randomizer

Blocks 0 and 1 from the entry: the prologue saves the callee-saved registers at the frame's top,
reads the cursor `pos`, stores `pos + 16` (the bounds check `pos < 2389` holds), copies the
randomizer's 16 bytes to the frame's base, and sets up the loop over the chain values (`LoopAt`
before value `0`). One environment: region 0 the frame, 1 the cursor, 2 the randomizer.
-/

namespace NativeRustcArm.Xmss.FromBytes

open NativeRustcArm.Sym NativeArm

set_option Elab.async false

/-- The symbolic state at the entry. -/
def stA : SState := init [(1936, true), (8, false), (16, false)] (.ptr 0 1936) [(.X1, .ptr 1 0)]
  (aliases := [(.bin .add .W64 (.reg .X2) (.load 1 0 8), (2, 0))])

sym_block b0_execA := exec b0 stA

/-- The symbolic state after block 0. -/
def stA1 : SState := ((exec b0 stA).getD (stA, .fall)).1

sym_block b1_execA := exec b1 stA1

/-- The symbolic state after block 1. -/
def stA2 : SState := ((exec b1 stA1).getD (stA, .fall)).1

theorem stA2_save : ∀ j < 8, ∀ i < 8,
    findWrite 0 (1872 + 8 * j + i) stA2.mem = some (.reg (saveRegs.getD j .X0), i) := by decide +kernel

theorem stA2_rand : ∀ t < 16, findWrite 0 t stA2.mem = some (.load 2 (8 * (t / 8)) 8, t % 8) := by
  decide

theorem stA2_cursor : ∀ i < 8,
    findWrite 1 (0 + i) stA2.mem = some (.bin .add .W64 (.load 1 0 8) (.lit 16), i) := by decide +kernel

theorem stA2_writes : writesIn stA2 [0, 1] = true := by decide +kernel

/-- The environment at the entry. -/
def envA (m₀ : MachineData) : Env :=
  Env.ofMachine m₀ [(frame m₀, 1936), (cur m₀, 8), (sig m₀ + BitVec.ofNat 64 (pos m₀), 16)]

theorem envA_wf {m₀ : MachineData} (P : Pre m₀) : (envA m₀).WF :=
  Env.wf_of ⟨⟨P.frameMapped, P.frameNW⟩, ⟨P.curMapped, P.curNW⟩,
    ⟨P.sigMapped.sub (by have := P.pos; omega), NoWrap.sub P.sigNW (by have := P.pos; omega)⟩,
    trivial⟩
    (pairwise3 P.curF.symm (P.sigF.symm.sub_right P.sigNW (by have := P.pos; omega) (by omega))
      (P.curSig.sub_right P.sigNW (by have := P.pos; omega) (by omega)))

theorem envA_load {m₀ : MachineData} (P : Pre m₀) :
    (envA m₀).load 1 0 8 = BitVec.ofNat 64 (pos m₀) := by
  rw [Env.load_of_bytesAt (bs := bytesOf m₀.dmem (cur m₀) 8) (length_bytesOf _ _ _)
    (by simpa [envA, Env.base] using bytesAt_bytesOf P.curMapped), ofBytes_eq_leNat]
  rfl

theorem match_envA [Labels] {m₀ : MachineData} (P : Pre m₀) : Match (envA m₀) stA m₀ := by
  unfold envA stA
  apply match_ofMachine
  · refine ⟨rfl, fun _ => ?_,
      And.intro rfl (And.intro (by simp) (And.intro rfl (And.intro (by simp) trivial)))⟩
    rw [P.frameNat]
    have := P.sp16
    have := P.spLe
    unfold fromBytesStack at *
    omega
  · simp only [Sym.eval, Env.base, frame, stackBelow, Env.ofMachine_regions]
    rw [show BitVec.ofNat 64 fromBytesStack = BitVec.ofInt 64 1936 from rfl]
    simp
  · exact ⟨by simp [Sym.eval, Env.base, cur]; rfl, trivial⟩
  · exact trivial
  · exact trivial
  · refine ⟨?_, trivial⟩
    have h := envA_load P
    unfold envA at h
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h]
    simp [Env.base, sig]
    rfl

theorem frame_add [Labels] (m₀ : MachineData) (o : Nat) :
    (Sym.ptr 0 o).eval (envA m₀) = frame m₀ + BitVec.ofNat 64 o := by
  simp [Sym.eval, Env.base, envA]

/-- **The prologue and the randomizer**: from the entry to the loop's head before value `0`. -/
public theorem head [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData}
    (hpre : FromBytesPre m₀) {R : MachineState → Prop}
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (k + 22) → LoopAt m₀ st.data 0 →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m₀, Host.addrOf k⟩ := by
  have P := pre_of hpre
  have hwf := envA_wf P
  refine exec_then (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) b0_execA hwf (match_envA P)
    fun st₁ hm₁ hpc₁ => ?_
  have hnb : (SBool.not (SBool.cmp .ult .W64 (.load 1 0 8) (.lit 2389))).eval (envA m₀) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, envA_load P]
    have := P.pos
    simp [BitVec.ult]
    omega
  simp only [PcOk, hnb, Bool.false_eq_true, ite_false] at hpc₁
  have hm₁' : Match (envA m₀) stA1 st₁.data := by unfold stA1; rw [b0_execA]; exact hm₁
  refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) b1_execA hwf hpc₁ hm₁'
    fun st₂ hm₂ hpc₂ => ?_
  have hm : Match (envA m₀) stA2 st₂.data := by unfold stA2; rw [b1_execA]; exact hm₂
  refine cont st₂ hpc₂ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.kept hwf, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_,
    fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  · exact hm.regs .X19 (.reg .X0) (by decide +kernel)
  · exact hm.regs .X20 (.reg .X2) (by decide +kernel)
  · exact (hm.regs .X21 (.ptr 1 0) (by decide +kernel)).trans (by simp [Sym.eval, Env.base, envA, cur])
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp (hm.regs _ (.reg _) (by decide +kernel))
  · exact (hm.regs .X29 (.ptr 0 1872) (by decide +kernel)).trans (frame_add m₀ 1872)
  · rw [hm.sp, show stA2.sp = .ptr 0 0 by decide]
    simp [Sym.eval, Env.base, envA]
  · exact (hm.sameOutside_in hwf stA2_writes).mono fun p ⟨r, hr, b, sz, hb, hin⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [envA, Env.ofMachine_regions] at hb
        cases hb
        exact Or.inl hin
      · simp only [envA, Env.ofMachine_regions] at hb
        cases hb
        exact Or.inr hin
  · exact fun j hj => hm.bytesAt_write (r := 0) rfl (by omega) (stA2_save j hj)
  · refine bytesAt_slice (by have := P.pos; omega) fun t ht => ?_
    rw [hm.get?_load (r := 0) rfl (by omega) (stA2_rand t ht) (by omega) (le_refl 8),
      show 8 * (t / 8) + t % 8 = t by omega]
    simp [Env.base, envA, addr_add_addr]
    rfl
  · exact (hm.regs .X0 (.load 1 0 8) (by decide +kernel)).trans (by simp [Sym.eval, envA_load P])
  · exact (hm.regs .X8 (.bin .add .W64 (.reg .X2) (.lit 16)) (by decide +kernel)).trans
      (by simp [Sym.eval, BinOp.apply, sig]; rfl)
  · exact hm.regs .X9 (.lit 32) (by decide +kernel)
  · exact (hm.regs .X10 (.ptr 0 944) (by decide +kernel)).trans (frame_add m₀ 944)
  · have := bytesAt_add_zero (hm.bytesAt_write (r := 1) (o := 0) (n := 8) rfl (by omega) stA2_cursor)
    have hv : (Sym.bin .add .W64 (.load 1 0 8) (.lit 16)).eval (envA m₀) =
        BitVec.ofNat 64 (pos m₀ + 16 + 16 * 0) := by
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, envA_load P]
      rw [show pos m₀ + 16 + 16 * 0 = pos m₀ + 16 by omega, BitVec.ofNat_add]
    rw [hv] at this
    exact this

end NativeRustcArm.Xmss.FromBytes
