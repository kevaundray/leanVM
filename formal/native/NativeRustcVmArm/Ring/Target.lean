module

public import NativeRustcVmArm.Ring.Target.Copy

/-!
# `ring_target`'s contract

The prologue (`b0`), the images loop `Ψ(s_i)` (`b1`, `b2`), their copy (`b3`), the turns
`p = 7 … 0` and the products (`b4` to `b35`, `ChainA`, `ChainB`, `Ends`), the sum returned
(`b36`).
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeArm NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingTarget

public section

variable [Host] {k : Nat}

/-- **`ring_target`'s contract.** -/
theorem ringTarget_spec (hp : Placed code k)
    (hpsi : Spec (Labels.label ringPsiLabel) RingPsiPre RingPsiPost)
    (hmemcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hsq : Spec (Labels.label ewSqIterLabel) EWSqIterPre EWSqIterPost)
    (hpoly : Spec (Labels.label polyEvalLabel) PolyEvalPre PolyEvalPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) :
    Spec (Labels.label ringTargetLabel) RingTargetPre RingTargetPost := by
  intro m0 hpre
  have h := P.intro hpre
  rw [show Labels.label ringTargetLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  refine stepEntry h (hb b0_in_code (by simp [b0]) hp) fun m1 h1 ↦ ?_
  rw [show k + 0 + b0.length = k + 14 from rfl]
  refine images hp h hpsi h1 fun m2 h2 ↦ ?_
  refine stepCopy hp h hmemcpy h2 fun m3 h3 ↦ ?_
  refine chainA hp h hsq hpoly h3 fun m4 h4 ↦ ?_
  refine chainB hp h hsq hpoly hmul h4 fun m5 h5 ↦ ?_
  exact chainC hp h hsq hpoly hmul h5

end

end NativeRustcVmArm.Ring.Target
