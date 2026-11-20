module

public import NativeRustcVmArm.Top.Assembly.Layout
public import NativeRustcVmArm.Top.Assembly.Sumcheck
public import NativeRustcVmArm.Bus.ComputedBytecodeValue
public import NativeRustcVmArm.Bus.Fingerprints
public import NativeRustcVmArm.Bus.FpClosure
public import NativeRustcVmArm.Bus.BlockForm
public import NativeRustcVmArm.Bus.GkrLayers
public import NativeRustcVmArm.Bus.VerifyGkr
public import NativeRustcVmArm.Bus.GkrStep
public import NativeRustcVmArm.Bus.BusLayout
public import NativeRustcVmArm.Bus.BytecodeShare
public import NativeRustcVmArm.Bus.VerifyBusBalance
public import NativeRustcVmArm.Bus.AccumulateSide

/-!
# The bus's functions, placed in `leanvm_verify`'s program

The functions of `bus.rs` and `gkr.rs`, instantiated at their places in `Vm.code` with their proved callees.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeArm.Host] (hP : NativeArm.Host.prog = Vm.code)
include hP

theorem computedBytecodeValue :
    Spec (label computedBytecodeValueLabel) ComputedBytecodeValuePre ComputedBytecodeValuePost :=
  Bus.ComputedBytecodeValue.computedBytecodeValue_spec (placed_ComputedBytecodeValue hP)
    (mleOfComputedBytecodeValue hP)

theorem fingerprints : Spec (label fingerprintsLabel) FingerprintsPre FingerprintsPost :=
  Bus.Fingerprints.fingerprints_spec (placed_Fingerprints hP) (kpow hP) (dot hP)
    (indexMleFrom hP)

theorem fpClosure : Spec (label fpClosureLabel) FpClosurePre FpClosurePost :=
  Bus.FpClosure.fpClosure_spec (placed_VerifyBusBalanceClosure0 hP) (fingerprints hP)

theorem blockForm : Spec (label blockFormLabel) BlockFormPre BlockFormPost :=
  Bus.BlockForm.blockForm_spec (placed_BlockForm hP) (formTerms hP) (formBufAddScaled hP)

theorem gkrStep : ∀ a s g, Spec (label gkrStepLabel) (GkrStepPre a s g) (GkrStepPost a s g) :=
  fun a _ _ ↦ Bus.GkrStep.gkrStep_spec (placed_GkrStep hP) (bitLength hP) (grind hP a)
    (squeeze hP) (polyEval hP) (sumcheckGkr hP a) (readScalars hP a) (prodE hP)
    (sampleChallenges hP a) (mleOfMultilinearEval hP)

theorem gkrLayers :
    ∀ a s g, Spec (label gkrLayersLabel) (GkrLayersPre a s g) (GkrLayersPost a s g) :=
  fun a _ _ ↦ Bus.GkrLayers.gkrLayers_spec (placed_GkrLayers hP) (gkrStep hP a)

theorem verifyGkr : ∀ a s, Spec (label verifyGkrLabel) (VerifyGkrPre a s) (VerifyGkrPost a s) :=
  fun a _ ↦ Bus.VerifyGkr.verifyGkr_spec (placed_VerifyGkrGrandProducts hP) (readScalar hP a)
    (gkrLayers hP a)

theorem busLayout : ∀ L bl, Spec (label busLayoutLabel) (BusLayoutPre L bl) (BusLayoutPost L bl) :=
  fun _ _ ↦ Bus.BusLayout.busLayout_spec (placed_BusLayout hP) (memset hP) (memcpy hP)
    (stackOffsets hP)

theorem bytecodeShare :
    ∀ a s, Spec (label bytecodeShareLabel) (BytecodeSharePre a s) (BytecodeSharePost a s) :=
  fun a _ ↦ Bus.BytecodeShare.bytecodeShare_spec (placed_BytecodeShare hP) (readScalar hP a)
    (sumcheckPlain hP a) (eqKernel hP) (dot hP) (ewMul hP)

theorem accumulateSide : ∀ L rows bl F SL, Spec (label accumulateSideLabel)
    (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL) :=
  fun _ _ _ _ _ ↦ Bus.AccumulateSide.accumulateSide_spec (placed_AccumulateSide hP)
    (eqEvalFn hP) (ewMul hP) (memcpy hP) (blockForm hP) (formBufAddScaled hP)
    (paddingWeight hP) (evaluate hP)

theorem verifyBusBalance :
    ∀ a s L, Spec (label verifyBusBalanceLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L) :=
  Bus.VerifyBusBalance.verifyBusBalance_spec (placed_VerifyBusBalance hP) (busLayout hP)
    (memcpy hP) (bitLength hP) (grind hP) (sampleChallenges hP) (squeeze hP) (verifyGkr hP)
    (readScalars hP) (readScalar hP) (pushClaim hP) (bytecodeShare hP)
    (computedBytecodeValue hP) (kpow hP) (accumulateSide hP) (bufEW63Extend hP) (fpClosure hP)

end

end NativeRustcVmArm.Assembly
