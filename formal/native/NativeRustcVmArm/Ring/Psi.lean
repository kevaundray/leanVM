module

public import NativeRustcVmArm.Ring.Psi.Ends

/-!
# `ring_psi`'s contract

rustc unrolled the loop over `g`'s 8 elements: the prologue and `g_0 · v` (`b0`), the sum and
`v²` (`b1`), then for `j = 1 … 6` the product `g_j · v^(2^j)` (`b2j`) and the sum and the next
square (`b(2j+1)`), the last product (`b14`), the last sum and the epilogue (`b15`).
-/

namespace NativeRustcVmArm.Ring.Psi

open NativeRustcArm NativeRustcArm.Sym NativeArm NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingPsi

public section

variable [Host] {k : Nat}

theorem hb {ds : List Directive} {j : Nat} (h : ds.IsInfixAt code j) (hne : ds ≠ [])
    (hp : Placed code k) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- **`ring_psi`'s contract.** -/
theorem ringPsi_spec (hp : Placed code k)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) :
    Spec (Labels.label ringPsiLabel) RingPsiPre RingPsiPost := by
  intro m0 hpre
  rw [show Labels.label ringPsiLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  refine stepEntry hpre hmul (hb (j := 0) b0_in_code (by simp [b0]) hp) fun m1 h1 ↦ ?_
  rw [show k + 0 + b0.length = k + 12 from rfl]
  refine stepFirst hpre hmul (hb b1_in_code (by simp [b1]) hp) run_b1 (by decide) rfl rfl h1
    fun m2 h2 ↦ ?_
  rw [show k + 12 + b1.length = k + 19 from rfl]
  refine stepEven hpre hmul (hb b2_in_code (by simp [b2]) hp) run_b2 (by decide) rfl rfl
    (by decide) h2 fun m h ↦ ?_
  rw [show k + 19 + b2.length = k + 26 from rfl]
  refine stepOdd hpre hmul (hb b3_in_code (by simp [b3]) hp) run_b3 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 26 + b3.length = k + 33 from rfl]
  refine stepEven hpre hmul (hb b4_in_code (by simp [b4]) hp) run_b4 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 33 + b4.length = k + 40 from rfl]
  refine stepOdd hpre hmul (hb b5_in_code (by simp [b5]) hp) run_b5 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 40 + b5.length = k + 47 from rfl]
  refine stepEven hpre hmul (hb b6_in_code (by simp [b6]) hp) run_b6 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 47 + b6.length = k + 54 from rfl]
  refine stepOdd hpre hmul (hb b7_in_code (by simp [b7]) hp) run_b7 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 54 + b7.length = k + 61 from rfl]
  refine stepEven hpre hmul (hb b8_in_code (by simp [b8]) hp) run_b8 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 61 + b8.length = k + 68 from rfl]
  refine stepOdd hpre hmul (hb b9_in_code (by simp [b9]) hp) run_b9 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 68 + b9.length = k + 75 from rfl]
  refine stepEven hpre hmul (hb b10_in_code (by simp [b10]) hp) run_b10 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 75 + b10.length = k + 82 from rfl]
  refine stepOdd hpre hmul (hb b11_in_code (by simp [b11]) hp) run_b11 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 82 + b11.length = k + 89 from rfl]
  refine stepEven hpre hmul (hb b12_in_code (by simp [b12]) hp) run_b12 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 89 + b12.length = k + 96 from rfl]
  refine stepOdd hpre hmul (hb b13_in_code (by simp [b13]) hp) run_b13 (by decide) rfl rfl
    (by decide) h fun m h ↦ ?_
  rw [show k + 96 + b13.length = k + 103 from rfl]
  refine stepLast hpre hmul (hb b14_in_code (by simp [b14]) hp) run_b14 (by decide) rfl rfl h
    fun m h ↦ ?_
  rw [show k + 103 + b14.length = k + 108 from rfl]
  exact stepExit hpre (hb b15_in_code (by simp [b15]) hp) h

end

end NativeRustcVmArm.Ring.Psi
