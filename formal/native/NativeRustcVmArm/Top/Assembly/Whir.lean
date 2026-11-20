module

public import NativeRustcVmArm.Top.Assembly.Sumcheck
public import NativeRustcVmArm.Top.Assembly.Ring
public import NativeRustcVmArm.Whir.BasisWEval
public import NativeRustcVmArm.Whir.VerifyStackedOpening
public import NativeRustcVmArm.Whir.NextLevel
public import NativeRustcVmArm.Whir.FinalLevel
public import NativeRustcVmArm.Whir.QueryBits
public import NativeRustcVmArm.Whir.SampleQueries
public import NativeRustcVmArm.Whir.SubspaceAtTable
public import NativeRustcVmArm.Whir.NovelEval
public import NativeRustcVmArm.Whir.FoldRow
public import NativeRustcVmArm.Whir.GluedEval
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Spec
public import NativeRustcVmArm.Whir.GlueLevel.Spec
public import NativeRustcVmArm.Whir.EachRowOfNextLevel.Spec
public import NativeRustcVmArm.Whir.InducedWeight
public import NativeRustcVmArm.Whir.FoldRound
public import NativeRustcVmArm.Whir.FoldRounds
public import NativeRustcVmArm.Whir.LanesOf
public import NativeRustcVmArm.Whir.SubspaceTable
public import NativeRustcVmArm.Whir.WhirLevels

/-!
# WHIR, placed in `leanvm_verify`'s program

Those of `whir.rs` proved so far, instantiated at their places in `Vm.code` with their callees'
instantiated contracts, the callees not yet proved as hypotheses.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeArm.Host] (hP : NativeArm.Host.prog = Vm.code)
include hP

theorem queryBits : Spec (label queryBitsLabel) QueryBitsPre QueryBitsPost :=
  Whir.QueryBits.queryBits_spec (placed_QueryBits hP)

theorem sampleQueries :
    ∀ a s, Spec (label sampleQueriesLabel) (SampleQueriesPre a s) (SampleQueriesPost a s) :=
  Whir.SampleQueries.sampleQueries_spec (placed_SampleQueries hP) (squeeze hP) (queryBits hP)

theorem subspaceAtTable :
    Spec (label subspaceAtTableLabel) SubspaceAtTablePre SubspaceAtTablePost :=
  Whir.SubspaceAtTable.subspaceAtTable_spec (placed_SubspaceAtTable hP) (kmul hP) (memset hP)
    (memcpy hP)

theorem novelEval : Spec (label novelEvalLabel) NovelEvalPre NovelEvalPost :=
  Whir.NovelEval.novelEval_spec (placed_NovelEval hP) (kmul hP) (memset hP)

theorem foldRow : Spec (label foldRowLabel) FoldRowPre FoldRowPost :=
  Whir.FoldRow.foldRow_spec (placed_FoldRow hP) (kmul hP) (ewMul hP)

theorem subspaceTable : Spec (label subspaceTableLabel) SubspaceTablePre SubspaceTablePost :=
  Whir.SubspaceTable.subspaceTable_spec (placed_SubspaceTable hP) (kmul hP) (kinv hP) (memset hP)
    (memcpy hP)

theorem inducedWeight : Spec (label inducedWeightLabel) InducedWeightPre InducedWeightPost :=
  Whir.InducedWeight.inducedWeight_spec (placed_InducedWeight hP) (subspaceTable hP) (memcpy hP)
    (subspaceAtTable hP) (kmul hP) (ewMul hP)

theorem gluedEval : ∀ g, Spec (label gluedEvalLabel) (GluedEvalPre g) (GluedEvalPost g) :=
  Whir.GluedEval.gluedEval_spec (placed_GluedEval hP) (eqEval hP) (inducedWeight hP)

theorem lanesOf : Spec (label lanesOfLabel) LanesOfPre LanesOfPost :=
  Whir.LanesOf.lanesOf_spec (placed_LanesOf hP)

theorem eachRowFinal :
    ∀ rows op, Spec (label eachRowFinalLabel) (EachRowFinalPre rows op) (EachRowFinalPost rows) :=
  fun rows op ↦ Whir.EachRowOfFinalLevel.eachRowFinal_spec (placed_EachRowOfFinalLevel hP)
    (subspaceTable hP) (memcpy hP) (lanesOf hP) (foldRow hP) (subspaceAtTable hP) (novelEval hP)
    rows op (rowsRow hP op rows)

theorem eachRowNext :
    ∀ rows op, Spec (label eachRowNextLabel) (EachRowNextPre rows op) (EachRowNextPost rows) :=
  fun rows op ↦ Whir.EachRowOfNextLevel.eachRowNext_spec (placed_EachRowOfNextLevel hP)
    (subspaceTable hP) (memcpy hP) (lanesOf hP) (foldRow hP) (subspaceAtTable hP) (novelEval hP)
    (kmul hP) (ewMul hP) rows op (rowsRow hP op rows)

theorem foldRound :
    ∀ a s w, Spec (label foldRoundLabel) (FoldRoundPre a s w) (FoldRoundPost a s w) :=
  Whir.FoldRound.foldRound_spec (placed_FoldRound hP) (readScalar hP) (grind hP) (squeeze hP)
    (ewMul hP)

theorem foldRounds :
    ∀ a s w, Spec (label foldRoundsLabel) (FoldRoundsPre a s w) (FoldRoundsPost a s w) :=
  Whir.FoldRounds.foldRounds_spec (placed_FoldRounds hP) (foldRound hP)

theorem glueLevel : ∀ s, Spec (label glueLevelLabel) (GlueLevelPre s) (GlueLevelPost s) :=
  Whir.GlueLevel.glueLevel_spec (placed_GlueLevel hP) (ewMul hP) (bufEW30Extend hP)
    (bufU64x230Extend hP) (bufEW230Extend hP)

theorem nextLevel : ∀ a s level w rounds, Spec (label nextLevelLabel)
    (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds) :=
  Whir.NextLevel.nextLevel_spec (placed_NextLevel hP) (eachRowNext hP) (glueLevel hP) (memcpy hP)
    (powers hP) (squeeze hP) (grind hP) (queryOpenings hP) (readCommitment hP) (readScalar hP)
    (readScalars hP) (sampleChallenges hP) (sampleQueries hP)

theorem whirLevels
    (hnl : ∀ a s level w rounds, Spec (label nextLevelLabel)
      (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds))
    (hfl : ∀ a s level ba b w rounds, Spec (label finalLevelLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds)) :
    ∀ a s levels ba b claim, Spec (label whirLevelsLabel) (WhirLevelsPre a s levels ba b claim)
      (WhirLevelsPost a s levels b claim) :=
  Whir.WhirLevels.whirLevels_spec (placed_WhirLevels hP) (foldRounds hP) hnl hfl

theorem basisWEval :
    ∀ ba b, Spec (label basisWEvalLabel) (BasisWEvalPre ba b) (BasisWEvalPost b) :=
  Whir.BasisWEval.basisWEval_spec (placed_BasisWEval hP) (layoutWPlacement hP)
    (ringClaimWeight hP) (columnWeight hP) (eqEval hP) (ewMul hP)

theorem finalLevel : ∀ a s level ba b w rounds, Spec (label finalLevelLabel)
    (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds) :=
  Whir.FinalLevel.finalLevel_spec (placed_FinalLevel hP) (readScalars hP) (grind hP)
    (sampleQueries hP) (queryOpenings hP) (eachRowFinal hP) (sumcheckPlain hP)
    (bufEW30Extend hP) (basisWEval hP) (gluedEval hP) (ewMul hP) (mleOfMultilinearEval hP)

theorem verifyStackedOpening
    (hnl : ∀ a s level w rounds, Spec (label nextLevelLabel)
      (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds))
    (hfl : ∀ a s level ba b w rounds, Spec (label finalLevelLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds)) :
    ∀ a s layout target coefficients point slices cs z value,
      Spec (label verifyStackedOpeningLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value) :=
  Whir.VerifyStackedOpening.verifyStackedOpening_spec (placed_VerifyStackedOpening hP)
    (squeeze hP) (powers hP) (ewMul hP) (ladder hP) (memcpy hP) (whirLevels hP hnl hfl)

end

end NativeRustcVmArm.Assembly
