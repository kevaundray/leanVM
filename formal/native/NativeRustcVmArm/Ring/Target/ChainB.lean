module

public import NativeRustcVmArm.Ring.Target.ChainA

/-!
# `ring_target`: the turns `p = 2 … 0`, the products

From `T_3` in X0, X1 (`b19`): `Z_p`, `P_p`, `T_p` for `p = 2, 1`, `Z_0` (`b25`), then the
products `M_p = f_p · T_p` for `p = 1 … 7` (`b26` to `b32`), `M_7` in X0, X1 before `b33`.
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeArm NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingTarget

public section

variable [Host] {k : Nat} {m0 : MachineData}

/-- **The turns `p = 2 … 0` and the products** (`b19` to `b32`). -/
theorem chainB (hp : Placed code k) (h : P m0)
    (hsq : Spec (Labels.label ewSqIterLabel) EWSqIterPre EWSqIterPost)
    (hpoly : Spec (Labels.label polyEvalLabel) PolyEvalPre PolyEvalPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) {m : MachineData}
    (hst : St m0 ((.reg .X0, tI 3) :: (.reg .X1, tI 3 + 1) :: K17) m) {R : MachineState → Prop}
    (cont : ∀ m', St m0 ((.reg .X0, mI 7) :: (.reg .X1, mI 7 + 1) :: K32) m' →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + 212)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + 127)⟩ := by
  refine sqStep h hsq (hb b19_in_code (by simp [b19]) hp) run_b19
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K19) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrZ 2 (by decide)) fun m hst ↦ ?_
  rw [show k + 127 + b19.length = k + 132 from rfl]
  refine polyStep h hpoly (hb b20_in_code (by simp [b20]) hp) run_b20
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K20) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (hrP 2 (by decide)) (E := []) nilE nilH fun m hst ↦ ?_
  rw [show k + 132 + b20.length = k + 140 from rfl]
  refine sqStep h hsq (hb b21_in_code (by simp [b21]) hp) run_b21
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K20) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrT 2 (by decide)) fun m hst ↦ ?_
  rw [show k + 140 + b21.length = k + 146 from rfl]
  refine sqStep h hsq (hb b22_in_code (by simp [b22]) hp) run_b22
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K22) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrZ 1 (by decide)) fun m hst ↦ ?_
  rw [show k + 146 + b22.length = k + 152 from rfl]
  refine polyStep h hpoly (hb b23_in_code (by simp [b23]) hp) run_b23
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K23) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (hrP 1 (by decide)) (E := []) nilE nilH fun m hst ↦ ?_
  rw [show k + 152 + b23.length = k + 160 from rfl]
  refine sqStep h hsq (hb b24_in_code (by simp [b24]) hp) run_b24
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K23) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrT 1 (by decide)) fun m hst ↦ ?_
  rw [show k + 160 + b24.length = k + 166 from rfl]
  refine sqStep h hsq (hb b25_in_code (by simp [b25]) hp) run_b25
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K25) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrZ 0 (by decide)) fun m hst ↦ ?_
  rw [show k + 166 + b25.length = k + 172 from rfl]
  refine mulStep h hmul (hb b26_in_code (by simp [b26]) hp) run_b26
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := K26) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hrM 1 (by decide)) fun m hst ↦ ?_
  rw [show k + 172 + b26.length = k + 180 from rfl]
  refine mulStep h hmul (hb b27_in_code (by simp [b27]) hp) run_b27
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := ((.reg .X21, fPtr) :: Ms27)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hrM 2 (by decide)) fun m hst ↦ ?_
  rw [show k + 180 + b27.length = k + 187 from rfl]
  refine mulStep h hmul (hb b28_in_code (by simp [b28]) hp) run_b28
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := ((.reg .X21, fPtr) :: Ms28)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hrM 3 (by decide)) fun m hst ↦ ?_
  rw [show k + 187 + b28.length = k + 192 from rfl]
  refine mulStep h hmul (hb b29_in_code (by simp [b29]) hp) run_b29
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := ((.reg .X21, fPtr) :: Ms29)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hrM 4 (by decide)) fun m hst ↦ ?_
  rw [show k + 192 + b29.length = k + 197 from rfl]
  refine mulStep h hmul (hb b30_in_code (by simp [b30]) hp) run_b30
    hst.ptr (hst.mid h (by decide)) rfl
    (by decide) (D' := ((.reg .X21, fPtr) :: Ms30)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hrM 5 (by decide)) fun m hst ↦ ?_
  rw [show k + 197 + b30.length = k + 202 from rfl]
  refine mulStep h hmul (hb b31_in_code (by simp [b31]) hp) run_b31
    hst.ptr (matchT2 hst.fr h) rfl
    (by decide) (D' := K31) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hrM 6 (by decide)) fun m hst ↦ ?_
  rw [show k + 202 + b31.length = k + 207 from rfl]
  refine mulStep h hmul (hb b32_in_code (by simp [b32]) hp) run_b32
    hst.ptr (matchT2 hst.fr h) rfl
    (by decide) (D' := K32) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hrM 7 (by decide)) fun m hst ↦ ?_
  rw [show k + 207 + b32.length = k + 212 from rfl]
  exact cont m hst

end

end NativeRustcVmArm.Ring.Target
