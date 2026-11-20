module

public import NativeRustcVmArm.Top.Assembly.Layout
public import NativeRustcVmArm.Ring.Psi
public import NativeRustcVmArm.Ring.Coeff
public import NativeRustcVmArm.Ring.Target
public import NativeRustcVmArm.Ring.Switch
public import NativeRustcVmArm.Ring.Column
public import NativeRustcVmArm.Ring.Claim
public import NativeRustcVmArm.Ring.Weight

/-!
# Ring switching, placed in `leanvm_verify`'s program

Those of `ring.rs` proved so far, instantiated at their places in `Vm.code` with their callees'
instantiated contracts.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeArm.Host] (hP : NativeArm.Host.prog = Vm.code)
include hP

theorem ringPsi : Spec (label ringPsiLabel) RingPsiPre RingPsiPost :=
  Ring.Psi.ringPsi_spec (placed_RingPsi hP) (ewMul hP)

theorem ringCoefficients :
    Spec (label ringCoefficientsLabel) RingCoefficientsPre RingCoefficientsPost :=
  Ring.Coeff.ringCoefficients_spec (placed_RingCoefficients hP) (ewMul hP) (ewSqIter hP)

theorem ringTarget : Spec (label ringTargetLabel) RingTargetPre RingTargetPost :=
  Ring.Target.ringTarget_spec (placed_RingTarget hP) (ringPsi hP) (memcpy hP) (ewSqIter hP)
    (polyEval hP) (ewMul hP)

theorem ringSwitch : ∀ a s point,
    Spec (label ringSwitchLabel) (RingSwitchPre a s) (RingSwitchPost a s point) :=
  Ring.Switch.ringSwitch_spec (placed_RingSwitch hP) (grind hP) (sampleChallenges hP)
    (ringCoefficients hP) (ringTarget hP)

theorem columnWeight : Spec (label columnWeightLabel) ColumnWeightPre ColumnWeightPost :=
  Ring.Column.columnWeight_spec (placed_ColumnWeight hP) (stackPoint hP) (eqEval hP)

theorem ringWeight : Spec (label ringWeightLabel) RingWeightPre RingWeightPost :=
  Ring.Weight.ringWeight_spec (placed_RingWeight hP) (ewMul hP)

theorem ringClaimWeight :
    Spec (label ringClaimWeightLabel) RingClaimWeightPre RingClaimWeightPost :=
  Ring.Claim.ringClaimWeight_spec (placed_RingClaimWeight hP) (eqEvalFn hP) (ringWeight hP)
    (ewMul hP)

end

end NativeRustcVmArm.Assembly
