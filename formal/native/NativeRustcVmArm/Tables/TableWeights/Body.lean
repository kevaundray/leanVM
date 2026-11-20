module

public import NativeRustcVmArm.Tables.TableWeights.Reads
public import NativeRustcVmArm.Tables.TableWeights.Mid

/-!
# `table_weights`: the blocks in the program, a block without a call

The blocks' places in the program (`hb<k>`) and the labels' addresses (`lbl_<n>`). After a block
run from a state of the body that writes only the frame, the frame's invariant (`frm_of_match`).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables NativeArm
open NativeRustcVmArm.Vm.TableWeights
open NativeRustcVm (wordOf)

public section

variable {m0 : MachineData}

/-- A byte a frame block writes is in the stack area. -/
theorem written_frame {m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hg : Geo m0) (hw : FrameWrites S 240) {p : BitVec 64}
    (h : Written (Env.ofMachine m ((fb m0, 240) :: rs)) S p) :
    StackArea (fb m0) ewMulStack 240 p := by
  obtain ⟨w, hwm, b, sz, hb, h1, h2⟩ := h
  have hw' := List.all_eq_true.mp hw w hwm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw'
  rw [hw'.1] at hb
  cases hb
  have := hg.lo
  have := hg.hi
  have hlo : (fb m0 - BitVec.ofNat 64 ewMulStack).toNat = (fb m0).toNat - ewMulStack :=
    NativeRustcVm.toNat_sub_ofNat hg.lo
  unfold StackArea
  rw [inRange_iff (by omega), hlo]
  omega

section
variable [Labels]

/-- **The frame's invariant after a frame block.** -/
theorem frm_of_match {m st : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hg : Geo m0) (hf : Frm m0 m) (hwf : (Env.ofMachine m ((fb m0, 240) :: rs)).WF)
    (hm : Match (Env.ofMachine m ((fb m0, 240) :: rs)) S st) (hsp : S.sp = .ptr 0 0)
    (hw : FrameWrites S 240) (hk : ∀ p ∈ koffs, loadSym S.mem 0 p 8 = .load 0 p 8) :
    Frm m0 st where
  sp := by rw [hm.sp, hsp]; simp [Sym.eval]
  slots p hp := by
    have hmem : p.1 ∈ koffs := by rw [← koffs_eq]; exact List.mem_map_of_mem hp
    have ho : p.1 + 8 ≤ 240 := by
      simp only [koffs, List.mem_cons, List.not_mem_nil, or_false] at hmem; omega
    rw [fw, match_wordOf hm hwf (r := 0) (b := fb m0) (sz := 240) rfl ho, hk _ hmem]
    show (Env.ofMachine m ((fb m0, 240) :: rs)).load 0 p.1 8 = _
    rw [load_fw]
    exact hf.slots p hp
  same p hp := by
    rw [hm.sameOutside hwf p fun h => hp (written_frame hg hw h)]
    exact hf.same p hp
  kept p h := hm.kept hwf p (hf.kept p h)

/-- A register a frame block keeps. -/
theorem rg_keep {m st : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((fb m0, 240) :: rs)) S st) {r : XReg}
    (h : S.reg r = some (.reg r)) : rg st r = rg m r :=
  hm.regs r _ h

/-- A place a frame block keeps. -/
theorem Pl.val_keep {m st : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hwf : (Env.ofMachine m ((fb m0, 240) :: rs)).WF)
    (hm : Match (Env.ofMachine m ((fb m0, 240) :: rs)) S st) {p : Pl} (hp : p.Ok)
    {v : Sym} (h : p.after S = some v) :
    p.val m0 st = v.eval (Env.ofMachine m ((fb m0, 240) :: rs)) := by
  cases p with
  | reg r => exact hm.regs r v h
  | slot o =>
    simp only [Pl.after, Option.some.injEq] at h
    rw [Pl.val, fw, match_wordOf hm hwf (r := 0) (b := fb m0) (sz := 240) rfl hp, h]

end

theorem len_b0 : b0.length = 11 := rfl
theorem len_b1 : b1.length = 22 := rfl
theorem len_b2 : b2.length = 4 := rfl
theorem len_b3 : b3.length = 10 := rfl
theorem len_b4 : b4.length = 10 := rfl
theorem len_b5 : b5.length = 10 := rfl
theorem len_b6 : b6.length = 10 := rfl
theorem len_b7 : b7.length = 10 := rfl
theorem len_b8 : b8.length = 9 := rfl
theorem len_b9 : b9.length = 6 := rfl
theorem len_b10 : b10.length = 6 := rfl
theorem len_b11 : b11.length = 3 := rfl
theorem len_b12 : b12.length = 11 := rfl

variable [Host] {k : Nat}

theorem addr_eq {a b : Nat} (h : a = b) : Host.addrOf a = Host.addrOf b := by rw [h]

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + 0) :=
  b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + 11) :=
  b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + 33) :=
  b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + 37) :=
  b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + 47) :=
  b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + 57) :=
  b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + 67) :=
  b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + 77) :=
  b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + 87) :=
  b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + 96) :=
  b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + 102) :=
  b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + 108) :=
  b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + 111) :=
  b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + 122) :=
  b13_in_code.trans hp.1 (List.cons_ne_nil _ _)

theorem lbl_entry (hp : Placed code k) : Labels.label tableWeightsLabel = Host.addrOf (k + 0) :=
  hp.label (j := 0) rfl
theorem lbl_2 (hp : Placed code k) : Labels.label ".LTableWeights_2" = Host.addrOf (k + 33) :=
  hp.label (j := 33) rfl
theorem lbl_3 (hp : Placed code k) : Labels.label ".LTableWeights_3" = Host.addrOf (k + 37) :=
  hp.label (j := 37) rfl
theorem lbl_4 (hp : Placed code k) : Labels.label ".LTableWeights_4" = Host.addrOf (k + 102) :=
  hp.label (j := 102) rfl
theorem lbl_6 (hp : Placed code k) : Labels.label ".LTableWeights_6" = Host.addrOf (k + 111) :=
  hp.label (j := 111) rfl
theorem lbl_7 (hp : Placed code k) : Labels.label ".LTableWeights_7" = Host.addrOf (k + 122) :=
  hp.label (j := 122) rfl

end

end NativeRustcVmArm.Tables.TableWeights
