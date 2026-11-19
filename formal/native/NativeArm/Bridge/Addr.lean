module

public import NativeArm.Bridge.Imm

/-!
# Addresses

The code of an address leaves, in the base register of its `LDR`/`STR` operand, a value from which
the operand names the address QM computes (`Runs.addr`), changing only the scratch registers X4
and X5.
-/

open Native

namespace NativeArm

public section

theorem Width.shl_lsl (x : BitVec 64) (w : Width) :
    x <<< w.lsl.toInt.toNat = x * w.bytes.toUInt64.toBitVec := by
  cases w <;> (rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl)

theorem Addr.toArm_check (a : Addr) (m : MachineData) (ok : Unit → Effects) :
    a.toArm.2.checkSPAlignment m ok = ok () := by
  unfold Addr.toArm
  split <;> rfl

variable [Labels] {is : List Instr} {m : MachineData} {Q : MachineData → Prop} {s : QState}

/-- The base of an address: `base + index · scale` in X4, or the base register itself. -/
theorem Runs.armBase (a : Addr) (hr : StateRel s m)
    (h : ∀ m₁, StateRel s m₁ → Keeps m m₁ → m₁.regs.getXReg .X6 = m.regs.getXReg .X6 →
      a.armBase.2 ≠ .X5 →
      (m₁.regs.getXReg a.armBase.2).toBitVec + a.disp.toBitVec = (a.eval s).toBitVec →
      Runs is m₁ Q) :
    Runs (a.armBase.1 ++ is) m Q := by
  obtain ⟨base, idx, disp⟩ := a
  cases idx with
  | none =>
    simp only [Addr.armBase] at h ⊢
    exact h m hr (Keeps.refl m) rfl (by simp) (by simp [Addr.eval, hr.get])
  | some p =>
    obtain ⟨r, w⟩ := p
    simp only [Addr.armBase, List.cons_append, List.nil_append] at h ⊢
    refine Runs.add ?_
    refine h _ (hr.setX_scratch rfl _) ((Keeps.refl m).setX rfl _) (by simp) (by decide) ?_
    simp only [sval, sr, ShiftRegExpr.interp, getRegOrZr_xr, Width.shl_lsl]
    simp [Addr.eval, hr.get]

/-- An address's code and operand: the operand names the address QM computes. -/
theorem Runs.addr (a : Addr) (hr : StateRel s m)
    (h : ∀ m₁, StateRel s m₁ → Keeps m m₁ → m₁.regs.getXReg .X6 = m.regs.getXReg .X6 →
      (∀ p, a.toArm.2.eval m₁ p = ((a.eval s).toBitVec, m₁)) → Runs is m₁ Q) :
    Runs (a.toArm.1 ++ is) m Q := by
  by_cases hf : dispFits a.disp
  · have e : a.toArm = (a.armBase.1, immOp a.armBase.2 a.disp) := by
      simp [Addr.toArm, hf]
    rw [e] at h ⊢
    exact Runs.armBase a hr fun m₁ hr1 hk1 h6 _ hv =>
      h m₁ hr1 hk1 h6 fun p => by rw [AddrExpr.eval_imm, hv]
  · have e : a.toArm =
        (a.armBase.1 ++ NativeArm.movImm .X5 a.disp.toUInt64, regOp a.armBase.2 .X5) := by
      simp [Addr.toArm, hf]
    rw [e] at h ⊢
    rw [List.append_assoc]
    exact Runs.armBase a hr fun m₁ hr1 hk1 h6 h5 hv =>
      Runs.movImm _ _ (h _ (hr1.setX_scratch rfl _) (hk1.setX rfl _) (by simp [h6])
        fun p => by
          rw [AddrExpr.eval_reg]
          simp [h5, Int64.toBitVec_toUInt64, hv])

/-! ## The scratch bank -/

omit [Labels] in
theorem getRegOrSp_sp (regs : Reg64s) : regs.getRegOrSp sp = regs.SP.toBitVec := by
  simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, BitVec.take]

omit [Labels] in
/-- An operand on SP passes the alignment check, SP 16-aligned. -/
theorem sp_check (m : MachineData) (h : m.regs.SP.toNat % 16 = 0) (off : AddrOff)
    (ok : Unit → Effects) : ({ base := sp, off := off } : AddrExpr).checkSPAlignment m ok = ok () := by
  have h0 : m.regs.SP.toBitVec % 16#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_umod, h]
  simp [AddrExpr.checkSPAlignment, getRegOrSp_sp, h0]

/-- The address of scratch word `k`. -/
theorem bankSlotOp_eval {k : Nat} (m : MachineData) (p : Std.Rco Int64) :
    (bankSlotOp k).eval m p = ((m.regs.SP + (8 * k).toUInt64).toBitVec, m) := by
  simp only [bankSlotOp, AddrExpr.eval, ConstExpr.interp, getRegOrSp_sp, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, ofInt_toInt64, UInt64.toBitVec_add]
  rfl

/-- The address of the scratch word a register names. -/
theorem bankIdxOp_eval (i : Reg64) (hr : StateRel s m) (p : Std.Rco Int64) :
    (bankIdxOp i).eval m p = ((m.regs.SP + (8 * (s.reg i).toNat).toUInt64).toBitVec, m) := by
  have hs : ((s.reg i).toNat : Int) <<< 3 = ((8 * (s.reg i).toNat : Nat) : Int) := by
    simp only [Int.shiftLeft_eq, Int.reducePow]
    omega
  simp only [bankIdxOp, AddrExpr.eval, MemExtRegExpr.interp, BitVec.apply_mem_extend, getRegOrSp_sp,
    BitVec.signed, BitVec.unsigned, RegOrZr.base, Reg64s.getRegOrZr64, hr.get, UInt64.toNat_toBitVec,
    hs, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_natCast, UInt64.toBitVec_add]
  rfl

end

end NativeArm
