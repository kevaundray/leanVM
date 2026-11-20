module

public import NativeRustcVmX64.Top.Assembly.Layout
public import NativeRustcVmX64.Top.Assembly.Sumcheck
public import NativeRustcVmX64.Tables.TableWeights
public import NativeRustcVmX64.Tables.ColumnClaims
public import NativeRustcVmX64.Tables.TablePhase
public import NativeRustcVmX64.Tables.PublicInputPhase
public import NativeRustcVmX64.Tables.TableTerms
public import NativeRustcVmX64.Tables.TableSumcheck
public import NativeRustcVmX64.KeccakGkr.KeccakPi
public import NativeRustcVmX64.KeccakGkr.LinearTranspose
public import NativeRustcVmX64.KeccakGkr.InstanceWeights
public import NativeRustcVmX64.KeccakGkr.SlotWeights
public import NativeRustcVmX64.KeccakGkr.FirstClaim
public import NativeRustcVmX64.KeccakGkr.KeccakOpen
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak
public import NativeRustcVmX64.KeccakGkr.VerifyLayer

/-!
# Tables and Keccak helpers, placed in `leanvm_verify`'s program

The functions are instantiated at their places in `Vm.code` with their proved callees.
-/

namespace NativeRustcVmX64.Assembly

open NativeRustcX64 NativeRustcVmX64.Placement

public section

variable [Host] (hP : Host.prog = Vm.code)
include hP

theorem tableWeights : Spec (label tableWeightsLabel) TableWeightsPre TableWeightsPost :=
  Tables.TableWeights.table_weights_spec (placed_TableWeights hP) (ewMul hP)

theorem publicInputPhase :
    ∀ a s L pub cs, Spec (label publicInputPhaseLabel) (PublicInputPhasePre a s L pub cs)
      (PublicInputPhasePost a s L pub cs) :=
  fun _ _ _ _ _ ↦ Tables.PublicInputPhase.publicInputPhase_spec (placed_PublicInputPhase hP)
    (squeeze hP) (layoutWPlacement hP) (mleOfMultilinearEval hP) (pushClaim hP)

theorem tableColumnClaims : ∀ ev cs, Spec (label tableColumnClaimsLabel)
    (TableColumnClaimsPre ev cs) (TableColumnClaimsPost ev cs) :=
  fun _ _ ↦ Tables.ColumnClaims.tableColumnClaims_spec (placed_TableColumnClaims hP)
    (pushClaim hP)

theorem tableTerms : ∀ a s heights forms, Spec (label tableTermsLabel)
    (TableTermsPre a s heights forms) (TableTermsPost a s heights forms) :=
  fun _ _ _ _ ↦ Tables.TableTerms.tableTerms_spec (placed_TableTerms hP) (readScalars hP)
    (constraintsW hP) (dot hP) (evaluate hP) (bufEW30Extend hP) (ewMul hP)

theorem tableSumcheck :
    ∀ a s heights bus, Spec (label tableSumcheckLabel) (TableSumcheckPre a s heights bus)
      (TableSumcheckPost a s heights bus) :=
  fun _ _ _ _ ↦ Tables.TableSumcheck.tableSumcheck_spec (placed_TableSumcheck hP)
    (sumcheckPlain hP) (tableWeights hP) (tableTerms hP)

theorem tablePhase :
    ∀ a s L bus, Spec (label tablePhaseLabel) (TablePhasePre a s L bus)
      (TablePhasePost a s L bus) :=
  fun _ _ _ _ ↦ Tables.TablePhase.tablePhase_spec (placed_TablePhase hP) (bitLength hP)
    (grind hP) (squeeze hP) (powers hP) (dot hP) (tableSumcheck hP)

theorem keccakPi : Spec (label keccakPiLabel) KeccakPiPre KeccakPiPost :=
  KeccakGkr.KeccakPi.keccakPi_spec (placed_KeccakPi hP)

theorem linearTranspose : ∀ ws, Spec (label linearTransposeLabel)
    (LinearTransposePre ws) (LinearTransposePost ws) :=
  KeccakGkr.LinearTranspose.linearTranspose_spec (placed_LinearTranspose hP) (keccakPi hP)

theorem instanceWeights : Spec (label instanceWeightsLabel) InstanceWeightsPre InstanceWeightsPost :=
  KeccakGkr.InstanceWeights.instanceWeights_spec (placed_InstanceWeights hP) (powers hP) (memcpy hP)

theorem slotWeights : ∀ c, Spec (label slotWeightsLabel) (SlotWeightsPre c) (SlotWeightsPost c) :=
  KeccakGkr.SlotWeights.slotWeights_spec (placed_SlotWeights hP) (eqKernel hP) (ewMul hP)

theorem firstClaim : ∀ inst segment lanePoint output, Spec (label firstClaimLabel)
    (FirstClaimPre inst segment lanePoint output) (FirstClaimPost inst segment lanePoint output) :=
  KeccakGkr.FirstClaim.firstClaim_spec (placed_FirstClaim hP) (eqKernel hP) (ewMul hP)
    (dot hP) (bufEW30Extend hP) (memcpy hP)

theorem keccakOpen : ∀ a s c, Spec (label keccakOpenLabel) (KeccakOpenPre a s c)
    (KeccakOpenPost a s c) :=
  KeccakGkr.KeccakOpen.keccakOpen_spec (placed_KeccakOpen hP) (ewMul hP) (memcpy hP)
    (slotWeights hP) (sumcheckPlain hP)

theorem verifyLayer : ∀ a s c, Spec (label verifyLayerLabel) (VerifyLayerPre a s c)
    (VerifyLayerPost a s c) :=
  KeccakGkr.VerifyLayer.verifyLayer_spec (placed_VerifyLayer hP) (bitLength hP)
    (bufEW30Extend hP) (dot hP) (ewMul hP) (eqKernel hP) (instanceWeights hP)
    (linearTranspose hP) (memcpy hP) (polyEval hP) (squeeze hP) (sumE hP) (sumcheckPlain hP)
    (sumcheckLayer hP) (grind hP) (readScalars hP)

theorem verifyKeccak : ∀ a s cs inst output, Spec (label verifyKeccakLabel)
    (VerifyKeccakPre a s cs inst output) (VerifyKeccakPost a s cs inst output) :=
  KeccakGkr.VerifyKeccak.verifyKeccak_spec (placed_VerifyKeccak hP) (bitLength hP) (grind hP)
    (sampleChallenges hP) (readScalar hP) (readScalars hP) (firstClaim hP) (memcpy hP)
    (verifyLayer hP) (keccakOpen hP) (ewMul hP) (bufEW36Extend hP) (pushClaim hP)
    (sumcheckPlain hP) (mleOfMultilinearEval hP) (dot hP)

end

end NativeRustcVmX64.Assembly
