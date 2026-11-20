module

public import NativeRustcVmArm.Top.Assembly.Base
public import NativeRustcVmArm.Layout.FormTerms
public import NativeRustcVmArm.Layout.ConstraintsW
public import NativeRustcVmArm.Layout.LayoutWPlacement
public import NativeRustcVmArm.Layout.StackPoint
public import NativeRustcVmArm.Layout.ColumnKappas
public import NativeRustcVmArm.Layout.Evaluate
public import NativeRustcVmArm.Layout.FormBufAddTerm
public import NativeRustcVmArm.Layout.FormBufAddScaled
public import NativeRustcVmArm.Layout.Ladder
public import NativeRustcVmArm.Layout.CommitStack
public import NativeRustcVmArm.Layout.PushClaim
public import NativeRustcVmArm.Layout.InsertionSort
public import NativeRustcVmArm.Layout.BuildLayout
public import NativeRustcVmArm.Layout.ReadAnnouncedSizes
public import NativeRustcVmArm.Layout.ReadOod
public import NativeRustcVmArm.Layout.StackOffsets
public import NativeRustcVmArm.Layout.PlacementsOf

/-!
# The layout's functions, placed in `leanvm_verify`'s program

Those of `layout.rs`, the forms, the stack ladder and commitment, and `push_claim`, instantiated at
their places in `Vm.code` with their callees' instantiated contracts.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeArm.Host] (hP : NativeArm.Host.prog = Vm.code)
include hP

theorem formTerms : Spec (label formTermsLabel) FormTermsPre FormTermsPost :=
  Layout.FormTerms.formTerms_spec (placed_FormTerms hP)

theorem constraintsW : Spec (label constraintsWLabel) ConstraintsWPre ConstraintsWPost :=
  Layout.ConstraintsW.constraintsW_spec (placed_ConstraintsW hP) (ewMul hP)

theorem layoutWPlacement :
    ∀ L, Spec (label layoutWPlacementLabel) (LayoutWPlacementPre L) (LayoutWPlacementPost L) :=
  Layout.LayoutWPlacement.layoutWPlacement_spec (placed_LayoutWPlacement hP)

theorem stackPoint : Spec (label stackPointLabel) StackPointPre StackPointPost :=
  Layout.StackPoint.stackPoint_spec (placed_StackPoint hP) (selectorPoint hP)

theorem columnKappas : Spec (label columnKappasLabel) ColumnKappasPre ColumnKappasPost :=
  Layout.ColumnKappas.columnKappas_spec (placed_ColumnKappas hP)

theorem evaluate : ∀ f, Spec (label evaluateLabel) (EvaluatePre f) (EvaluatePost f) :=
  fun _ ↦ Layout.Evaluate.evaluate_spec (placed_Evaluate hP) (ewMul hP)

theorem formBufAddTerm :
    ∀ f t, Spec (label formBufAddTermLabel) (FormBufAddTermPre f t) (FormBufAddTermPost f t) :=
  fun _ _ ↦ Layout.FormBufAddTerm.formBufAddTerm_spec (placed_FormBufAddTerm hP)

theorem formBufAddScaled : ∀ f o,
    Spec (label formBufAddScaledLabel) (FormBufAddScaledPre f o) (FormBufAddScaledPost f o) :=
  fun _ _ ↦ Layout.FormBufAddScaled.formBufAddScaled_spec (placed_FormBufAddScaled hP) (ewMul hP)
    (formBufAddTerm hP)

theorem ladder : Spec (label ladderLabel) LadderPre LadderPost :=
  Layout.Ladder.ladder_spec (placed_Ladder hP)

theorem commitStack :
    ∀ a s, Spec (label commitStackLabel) (CommitStackPre a s) (CommitStackPost a s) :=
  Layout.CommitStack.commitStack_spec (placed_CommitStack hP) (ladder hP) (readCommitment hP)

theorem pushClaim : ∀ cs, Spec (label pushClaimLabel) (PushClaimPre cs) (PushClaimPost cs) :=
  Layout.PushClaim.pushClaim_spec (placed_PushClaim hP) (bufEW36Extend hP)

theorem insertionSort : Spec (label insertionSortLabel) InsertionSortPre InsertionSortPost :=
  Layout.InsertionSort.insertionSort_spec (placed_InsertionSortOfStackOffsets hP)

theorem stackOffsets : Spec (label stackOffsetsLabel) StackOffsetsPre StackOffsetsPost :=
  Layout.StackOffsets.stackOffsets_spec (placed_StackOffsets hP) (memset hP) (insertionSort hP)
    (bitLength hP)

theorem placementsOf : Spec (label placementsOfLabel) PlacementsOfPre PlacementsOfPost :=
  Layout.PlacementsOf.placementsOf_spec (placed_PlacementsOf hP) (memset hP) (stackOffsets hP)

theorem buildLayout :
    ∀ bc, Spec (label buildLayoutLabel) (BuildLayoutPre bc) (BuildLayoutPost bc) :=
  fun _ ↦ Layout.BuildLayout.buildLayout_spec (placed_BuildLayout hP) (bitLength hP)
    (columnKappas hP) (placementsOf hP)

theorem readAnnouncedSizes :
    ∀ bc a s, Spec (label readAnnouncedSizesLabel) (ReadAnnouncedSizesPre bc a s)
      (ReadAnnouncedSizesPost bc a s) :=
  Layout.ReadAnnouncedSizes.readAnnouncedSizes_spec (placed_ReadAnnouncedSizes hP)
    (readScalars hP) (buildLayout hP)

theorem readOod : ∀ a s, Spec (label readOodLabel) (ReadOodPre a s) (ReadOodPost a s) :=
  Layout.ReadOod.readOod_spec (placed_ReadOod hP) (grind hP) (sampleChallenges hP)
    (readScalar hP)

end

end NativeRustcVmArm.Assembly
