module

public import NativeRustcVmArm.Placed.Nodup
public import NativeRustcVmArm.Code.Vm.Offsets

/-!
# Every function of `leanvm_verify`'s program placed

For each of the program's 137 functions `F`, `placed_F`: `Vm.F.code` sits in `Vm.code` at the index
`Code/Vm/Offsets.lean` gives (`F.code_at`), each of its labels the only one of its name
(`labels_nodup`), so `Placed Vm.F.code k` (`placed_of_nodup`).
-/

namespace NativeRustcVmArm.Placement

open NativeRustcArm

public section

variable [NativeArm.Host] (hP : NativeArm.Host.prog = Vm.code)
include hP

theorem placed_SumcheckOfSumcheckPlain : Placed Vm.SumcheckOfSumcheckPlain.code 0 :=
  placed_of_nodup hP labels_nodup Vm.SumcheckOfSumcheckPlain.code_at
theorem placed_SumcheckOfVerifyLayer : Placed Vm.SumcheckOfVerifyLayer.code 52 :=
  placed_of_nodup hP labels_nodup Vm.SumcheckOfVerifyLayer.code_at
theorem placed_SumcheckOfGkrStep : Placed Vm.SumcheckOfGkrStep.code 116 :=
  placed_of_nodup hP labels_nodup Vm.SumcheckOfGkrStep.code_at
theorem placed_EachRowOfNextLevel : Placed Vm.EachRowOfNextLevel.code 184 :=
  placed_of_nodup hP labels_nodup Vm.EachRowOfNextLevel.code_at
theorem placed_EachRowOfFinalLevel : Placed Vm.EachRowOfFinalLevel.code 448 :=
  placed_of_nodup hP labels_nodup Vm.EachRowOfFinalLevel.code_at
theorem placed_EqEvalFnOfEqAbove : Placed Vm.EqEvalFnOfEqAbove.code 680 :=
  placed_of_nodup hP labels_nodup Vm.EqEvalFnOfEqAbove.code_at
theorem placed_MultilinearEvalByOfMultilinearEval :
    Placed Vm.MultilinearEvalByOfMultilinearEval.code 714 :=
  placed_of_nodup hP labels_nodup Vm.MultilinearEvalByOfMultilinearEval.code_at
theorem placed_MultilinearEvalByOfComputedBytecodeValue :
    Placed Vm.MultilinearEvalByOfComputedBytecodeValue.code 904 :=
  placed_of_nodup hP labels_nodup Vm.MultilinearEvalByOfComputedBytecodeValue.code_at
theorem placed_Keccak256WordsOfHashWords : Placed Vm.Keccak256WordsOfHashWords.code 1096 :=
  placed_of_nodup hP labels_nodup Vm.Keccak256WordsOfHashWords.code_at
theorem placed_Keccak256WordsOfFiatShamirIv : Placed Vm.Keccak256WordsOfFiatShamirIv.code 1660 :=
  placed_of_nodup hP labels_nodup Vm.Keccak256WordsOfFiatShamirIv.code_at
theorem placed_InsertionSortOfStackOffsets : Placed Vm.InsertionSortOfStackOffsets.code 2325 :=
  placed_of_nodup hP labels_nodup Vm.InsertionSortOfStackOffsets.code_at
theorem placed_VerifyBusBalanceClosure0 : Placed Vm.VerifyBusBalanceClosure0.code 2382 :=
  placed_of_nodup hP labels_nodup Vm.VerifyBusBalanceClosure0.code_at
theorem placed_SpongeWAbsorbNonce : Placed Vm.SpongeWAbsorbNonce.code 2403 :=
  placed_of_nodup hP labels_nodup Vm.SpongeWAbsorbNonce.code_at
theorem placed_SpongeWDuplexInput : Placed Vm.SpongeWDuplexInput.code 2417 :=
  placed_of_nodup hP labels_nodup Vm.SpongeWDuplexInput.code_at
theorem placed_SpongeWAbsorb : Placed Vm.SpongeWAbsorb.code 2459 :=
  placed_of_nodup hP labels_nodup Vm.SpongeWAbsorb.code_at
theorem placed_SpongeWDuplex : Placed Vm.SpongeWDuplex.code 2487 :=
  placed_of_nodup hP labels_nodup Vm.SpongeWDuplex.code_at
theorem placed_SpongeWSqueeze : Placed Vm.SpongeWSqueeze.code 2496 :=
  placed_of_nodup hP labels_nodup Vm.SpongeWSqueeze.code_at
theorem placed_BufEW30Extend : Placed Vm.BufEW30Extend.code 2510 :=
  placed_of_nodup hP labels_nodup Vm.BufEW30Extend.code_at
theorem placed_BufEW36Extend : Placed Vm.BufEW36Extend.code 2540 :=
  placed_of_nodup hP labels_nodup Vm.BufEW36Extend.code_at
theorem placed_BufEW63Extend : Placed Vm.BufEW63Extend.code 2570 :=
  placed_of_nodup hP labels_nodup Vm.BufEW63Extend.code_at
theorem placed_BufEW230Extend : Placed Vm.BufEW230Extend.code 2600 :=
  placed_of_nodup hP labels_nodup Vm.BufEW230Extend.code_at
theorem placed_BufU64x230Extend : Placed Vm.BufU64x230Extend.code 2630 :=
  placed_of_nodup hP labels_nodup Vm.BufU64x230Extend.code_at
theorem placed_BasisWEval : Placed Vm.BasisWEval.code 2655 :=
  placed_of_nodup hP labels_nodup Vm.BasisWEval.code_at
theorem placed_ReaderLe : Placed Vm.ReaderLe.code 2799 :=
  placed_of_nodup hP labels_nodup Vm.ReaderLe.code_at
theorem placed_ReaderWords : Placed Vm.ReaderWords.code 2852 :=
  placed_of_nodup hP labels_nodup Vm.ReaderWords.code_at
theorem placed_ReaderDigest : Placed Vm.ReaderDigest.code 2885 :=
  placed_of_nodup hP labels_nodup Vm.ReaderDigest.code_at
theorem placed_EWMul : Placed Vm.EWMul.code 2928 :=
  placed_of_nodup hP labels_nodup Vm.EWMul.code_at
theorem placed_EWSqIter : Placed Vm.EWSqIter.code 3339 :=
  placed_of_nodup hP labels_nodup Vm.EWSqIter.code_at
theorem placed_DecodedPhaseCount : Placed Vm.DecodedPhaseCount.code 3356 :=
  placed_of_nodup hP labels_nodup Vm.DecodedPhaseCount.code_at
theorem placed_DecodedStreamElement : Placed Vm.DecodedStreamElement.code 3368 :=
  placed_of_nodup hP labels_nodup Vm.DecodedStreamElement.code_at
theorem placed_DecodedPhase : Placed Vm.DecodedPhase.code 3388 :=
  placed_of_nodup hP labels_nodup Vm.DecodedPhase.code_at
theorem placed_TStateNextScalar : Placed Vm.TStateNextScalar.code 3422 :=
  placed_of_nodup hP labels_nodup Vm.TStateNextScalar.code_at
theorem placed_TStateReadScalar : Placed Vm.TStateReadScalar.code 3456 :=
  placed_of_nodup hP labels_nodup Vm.TStateReadScalar.code_at
theorem placed_TStateReadScalars : Placed Vm.TStateReadScalars.code 3488 :=
  placed_of_nodup hP labels_nodup Vm.TStateReadScalars.code_at
theorem placed_TStateQueryOpenings : Placed Vm.TStateQueryOpenings.code 3520 :=
  placed_of_nodup hP labels_nodup Vm.TStateQueryOpenings.code_at
theorem placed_TStateReadCommitment : Placed Vm.TStateReadCommitment.code 3572 :=
  placed_of_nodup hP labels_nodup Vm.TStateReadCommitment.code_at
theorem placed_TStateSampleChallenges : Placed Vm.TStateSampleChallenges.code 3616 :=
  placed_of_nodup hP labels_nodup Vm.TStateSampleChallenges.code_at
theorem placed_TStateSumcheckRoundPoly : Placed Vm.TStateSumcheckRoundPoly.code 3633 :=
  placed_of_nodup hP labels_nodup Vm.TStateSumcheckRoundPoly.code_at
theorem placed_TStateGrind : Placed Vm.TStateGrind.code 3718 :=
  placed_of_nodup hP labels_nodup Vm.TStateGrind.code_at
theorem placed_FormBufAddScaled : Placed Vm.FormBufAddScaled.code 3750 :=
  placed_of_nodup hP labels_nodup Vm.FormBufAddScaled.code_at
theorem placed_FormBufAddTerm : Placed Vm.FormBufAddTerm.code 3785 :=
  placed_of_nodup hP labels_nodup Vm.FormBufAddTerm.code_at
theorem placed_LayoutWPlacement : Placed Vm.LayoutWPlacement.code 3844 :=
  placed_of_nodup hP labels_nodup Vm.LayoutWPlacement.code_at
theorem placed_RowsRow : Placed Vm.RowsRow.code 3855 :=
  placed_of_nodup hP labels_nodup Vm.RowsRow.code_at
theorem placed_FirstClaim : Placed Vm.FirstClaim.code 3871 :=
  placed_of_nodup hP labels_nodup Vm.FirstClaim.code_at
theorem placed_KeccakOpen : Placed Vm.KeccakOpen.code 4113 :=
  placed_of_nodup hP labels_nodup Vm.KeccakOpen.code_at
theorem placed_KeccakPhase : Placed Vm.KeccakPhase.code 4706 :=
  placed_of_nodup hP labels_nodup Vm.KeccakPhase.code_at
theorem placed_SlotWeights : Placed Vm.SlotWeights.code 4789 :=
  placed_of_nodup hP labels_nodup Vm.SlotWeights.code_at
theorem placed_VerifyLayer : Placed Vm.VerifyLayer.code 4987 :=
  placed_of_nodup hP labels_nodup Vm.VerifyLayer.code_at
theorem placed_VerifyKeccak : Placed Vm.VerifyKeccak.code 5688 :=
  placed_of_nodup hP labels_nodup Vm.VerifyKeccak.code_at
theorem placed_InstanceWeights : Placed Vm.InstanceWeights.code 6142 :=
  placed_of_nodup hP labels_nodup Vm.InstanceWeights.code_at
theorem placed_LinearTranspose : Placed Vm.LinearTranspose.code 6477 :=
  placed_of_nodup hP labels_nodup Vm.LinearTranspose.code_at
theorem placed_KeccakPi : Placed Vm.KeccakPi.code 6723 :=
  placed_of_nodup hP labels_nodup Vm.KeccakPi.code_at
theorem placed_OpenPhase : Placed Vm.OpenPhase.code 6738 :=
  placed_of_nodup hP labels_nodup Vm.OpenPhase.code_at
theorem placed_Climb : Placed Vm.Climb.code 6832 :=
  placed_of_nodup hP labels_nodup Vm.Climb.code_at
theorem placed_RingSwitch : Placed Vm.RingSwitch.code 6891 :=
  placed_of_nodup hP labels_nodup Vm.RingSwitch.code_at
theorem placed_RingTarget : Placed Vm.RingTarget.code 6956 :=
  placed_of_nodup hP labels_nodup Vm.RingTarget.code_at
theorem placed_RingCoefficients : Placed Vm.RingCoefficients.code 7205 :=
  placed_of_nodup hP labels_nodup Vm.RingCoefficients.code_at
theorem placed_RingPsi : Placed Vm.RingPsi.code 7332 :=
  placed_of_nodup hP labels_nodup Vm.RingPsi.code_at
theorem placed_BlockForm : Placed Vm.BlockForm.code 7446 :=
  placed_of_nodup hP labels_nodup Vm.BlockForm.code_at
theorem placed_BusLayout : Placed Vm.BusLayout.code 7504 :=
  placed_of_nodup hP labels_nodup Vm.BusLayout.code_at
theorem placed_Fingerprints : Placed Vm.Fingerprints.code 7727 :=
  placed_of_nodup hP labels_nodup Vm.Fingerprints.code_at
theorem placed_BytecodeShare : Placed Vm.BytecodeShare.code 7807 :=
  placed_of_nodup hP labels_nodup Vm.BytecodeShare.code_at
theorem placed_AccumulateSide : Placed Vm.AccumulateSide.code 7940 :=
  placed_of_nodup hP labels_nodup Vm.AccumulateSide.code_at
theorem placed_VerifyBusBalance : Placed Vm.VerifyBusBalance.code 8295 :=
  placed_of_nodup hP labels_nodup Vm.VerifyBusBalance.code_at
theorem placed_ComputedBytecodeValue : Placed Vm.ComputedBytecodeValue.code 8980 :=
  placed_of_nodup hP labels_nodup Vm.ComputedBytecodeValue.code_at
theorem placed_GkrLayers : Placed Vm.GkrLayers.code 8997 :=
  placed_of_nodup hP labels_nodup Vm.GkrLayers.code_at
theorem placed_VerifyGkrGrandProducts : Placed Vm.VerifyGkrGrandProducts.code 9051 :=
  placed_of_nodup hP labels_nodup Vm.VerifyGkrGrandProducts.code_at
theorem placed_GkrStep : Placed Vm.GkrStep.code 9095 :=
  placed_of_nodup hP labels_nodup Vm.GkrStep.code_at
theorem placed_FoldRound : Placed Vm.FoldRound.code 9408 :=
  placed_of_nodup hP labels_nodup Vm.FoldRound.code_at
theorem placed_GlueLevel : Placed Vm.GlueLevel.code 9526 :=
  placed_of_nodup hP labels_nodup Vm.GlueLevel.code_at
theorem placed_GluedEval : Placed Vm.GluedEval.code 9614 :=
  placed_of_nodup hP labels_nodup Vm.GluedEval.code_at
theorem placed_NextLevel : Placed Vm.NextLevel.code 9651 :=
  placed_of_nodup hP labels_nodup Vm.NextLevel.code_at
theorem placed_NovelEval : Placed Vm.NovelEval.code 9881 :=
  placed_of_nodup hP labels_nodup Vm.NovelEval.code_at
theorem placed_QueryBits : Placed Vm.QueryBits.code 9967 :=
  placed_of_nodup hP labels_nodup Vm.QueryBits.code_at
theorem placed_FinalLevel : Placed Vm.FinalLevel.code 10000 :=
  placed_of_nodup hP labels_nodup Vm.FinalLevel.code_at
theorem placed_FoldRounds : Placed Vm.FoldRounds.code 10486 :=
  placed_of_nodup hP labels_nodup Vm.FoldRounds.code_at
theorem placed_WhirLevels : Placed Vm.WhirLevels.code 10628 :=
  placed_of_nodup hP labels_nodup Vm.WhirLevels.code_at
theorem placed_InducedWeight : Placed Vm.InducedWeight.code 10800 :=
  placed_of_nodup hP labels_nodup Vm.InducedWeight.code_at
theorem placed_SampleQueries : Placed Vm.SampleQueries.code 10907 :=
  placed_of_nodup hP labels_nodup Vm.SampleQueries.code_at
theorem placed_SubspaceTable : Placed Vm.SubspaceTable.code 10998 :=
  placed_of_nodup hP labels_nodup Vm.SubspaceTable.code_at
theorem placed_SubspaceAtTable : Placed Vm.SubspaceAtTable.code 11171 :=
  placed_of_nodup hP labels_nodup Vm.SubspaceAtTable.code_at
theorem placed_VerifyStackedOpening : Placed Vm.VerifyStackedOpening.code 11220 :=
  placed_of_nodup hP labels_nodup Vm.VerifyStackedOpening.code_at
theorem placed_Ladder : Placed Vm.Ladder.code 11396 :=
  placed_of_nodup hP labels_nodup Vm.Ladder.code_at
theorem placed_FoldRow : Placed Vm.FoldRow.code 11495 :=
  placed_of_nodup hP labels_nodup Vm.FoldRow.code_at
theorem placed_LanesOf : Placed Vm.LanesOf.code 11761 :=
  placed_of_nodup hP labels_nodup Vm.LanesOf.code_at
theorem placed_ClimbLevel : Placed Vm.ClimbLevel.code 11863 :=
  placed_of_nodup hP labels_nodup Vm.ClimbLevel.code_at
theorem placed_WriteOpenings : Placed Vm.WriteOpenings.code 11971 :=
  placed_of_nodup hP labels_nodup Vm.WriteOpenings.code_at
theorem placed_Find : Placed Vm.Find.code 12203 :=
  placed_of_nodup hP labels_nodup Vm.Find.code_at
theorem placed_InsD : Placed Vm.InsD.code 12222 :=
  placed_of_nodup hP labels_nodup Vm.InsD.code_at
theorem placed_Decode : Placed Vm.Decode.code 12261 :=
  placed_of_nodup hP labels_nodup Vm.Decode.code_at
theorem placed_PhaseM : Placed Vm.PhaseM.code 12347 :=
  placed_of_nodup hP labels_nodup Vm.PhaseM.code_at
theorem placed_RdRows : Placed Vm.RdRows.code 12522 :=
  placed_of_nodup hP labels_nodup Vm.RdRows.code_at
theorem placed_BitLength : Placed Vm.BitLength.code 12639 :=
  placed_of_nodup hP labels_nodup Vm.BitLength.code_at
theorem placed_IndexMleFrom : Placed Vm.IndexMleFrom.code 12674 :=
  placed_of_nodup hP labels_nodup Vm.IndexMleFrom.code_at
theorem placed_PaddingWeight : Placed Vm.PaddingWeight.code 12719 :=
  placed_of_nodup hP labels_nodup Vm.PaddingWeight.code_at
theorem placed_SelectorPoint : Placed Vm.SelectorPoint.code 12777 :=
  placed_of_nodup hP labels_nodup Vm.SelectorPoint.code_at
theorem placed_Dot : Placed Vm.Dot.code 12833 :=
  placed_of_nodup hP labels_nodup Vm.Dot.code_at
theorem placed_Kinv : Placed Vm.Kinv.code 12869 :=
  placed_of_nodup hP labels_nodup Vm.Kinv.code_at
theorem placed_Kmul : Placed Vm.Kmul.code 12913 :=
  placed_of_nodup hP labels_nodup Vm.Kmul.code_at
theorem placed_Kpow : Placed Vm.Kpow.code 13027 :=
  placed_of_nodup hP labels_nodup Vm.Kpow.code_at
theorem placed_SumE : Placed Vm.SumE.code 13056 :=
  placed_of_nodup hP labels_nodup Vm.SumE.code_at
theorem placed_Powers : Placed Vm.Powers.code 13142 :=
  placed_of_nodup hP labels_nodup Vm.Powers.code_at
theorem placed_ProdE : Placed Vm.ProdE.code 13165 :=
  placed_of_nodup hP labels_nodup Vm.ProdE.code_at
theorem placed_EqEval : Placed Vm.EqEval.code 13191 :=
  placed_of_nodup hP labels_nodup Vm.EqEval.code_at
theorem placed_EqKernel : Placed Vm.EqKernel.code 13221 :=
  placed_of_nodup hP labels_nodup Vm.EqKernel.code_at
theorem placed_PolyEval : Placed Vm.PolyEval.code 13298 :=
  placed_of_nodup hP labels_nodup Vm.PolyEval.code_at
theorem placed_PushClaim : Placed Vm.PushClaim.code 13327 :=
  placed_of_nodup hP labels_nodup Vm.PushClaim.code_at
theorem placed_RingWeight : Placed Vm.RingWeight.code 13365 :=
  placed_of_nodup hP labels_nodup Vm.RingWeight.code_at
theorem placed_CommitStack : Placed Vm.CommitStack.code 13562 :=
  placed_of_nodup hP labels_nodup Vm.CommitStack.code_at
theorem placed_ColumnWeight : Placed Vm.ColumnWeight.code 13594 :=
  placed_of_nodup hP labels_nodup Vm.ColumnWeight.code_at
theorem placed_RingClaimWeight : Placed Vm.RingClaimWeight.code 13727 :=
  placed_of_nodup hP labels_nodup Vm.RingClaimWeight.code_at
theorem placed_ReadOod : Placed Vm.ReadOod.code 13778 :=
  placed_of_nodup hP labels_nodup Vm.ReadOod.code_at
theorem placed_KeccakF : Placed Vm.KeccakF.code 13813 :=
  placed_of_nodup hP labels_nodup Vm.KeccakF.code_at
theorem placed_HashPair : Placed Vm.HashPair.code 14031 :=
  placed_of_nodup hP labels_nodup Vm.HashPair.code_at
theorem placed_FormTerms : Placed Vm.FormTerms.code 14050 :=
  placed_of_nodup hP labels_nodup Vm.FormTerms.code_at
theorem placed_StackPoint : Placed Vm.StackPoint.code 14073 :=
  placed_of_nodup hP labels_nodup Vm.StackPoint.code_at
theorem placed_BuildLayout : Placed Vm.BuildLayout.code 14128 :=
  placed_of_nodup hP labels_nodup Vm.BuildLayout.code_at
theorem placed_ColumnKappas : Placed Vm.ColumnKappas.code 14235 :=
  placed_of_nodup hP labels_nodup Vm.ColumnKappas.code_at
theorem placed_ConstraintsW : Placed Vm.ConstraintsW.code 14368 :=
  placed_of_nodup hP labels_nodup Vm.ConstraintsW.code_at
theorem placed_PlacementsOf : Placed Vm.PlacementsOf.code 14419 :=
  placed_of_nodup hP labels_nodup Vm.PlacementsOf.code_at
theorem placed_StackOffsets : Placed Vm.StackOffsets.code 14549 :=
  placed_of_nodup hP labels_nodup Vm.StackOffsets.code_at
theorem placed_ReadAnnouncedSizes : Placed Vm.ReadAnnouncedSizes.code 14660 :=
  placed_of_nodup hP labels_nodup Vm.ReadAnnouncedSizes.code_at
theorem placed_Evaluate : Placed Vm.Evaluate.code 14738 :=
  placed_of_nodup hP labels_nodup Vm.Evaluate.code_at
theorem placed_TablePhase : Placed Vm.TablePhase.code 14807 :=
  placed_of_nodup hP labels_nodup Vm.TablePhase.code_at
theorem placed_TableTerms : Placed Vm.TableTerms.code 14857 :=
  placed_of_nodup hP labels_nodup Vm.TableTerms.code_at
theorem placed_TableWeights : Placed Vm.TableWeights.code 14996 :=
  placed_of_nodup hP labels_nodup Vm.TableWeights.code_at
theorem placed_TableSumcheck : Placed Vm.TableSumcheck.code 15138 :=
  placed_of_nodup hP labels_nodup Vm.TableSumcheck.code_at
theorem placed_PublicInputPhase : Placed Vm.PublicInputPhase.code 15266 :=
  placed_of_nodup hP labels_nodup Vm.PublicInputPhase.code_at
theorem placed_TableColumnClaims : Placed Vm.TableColumnClaims.code 15373 :=
  placed_of_nodup hP labels_nodup Vm.TableColumnClaims.code_at
theorem placed_VerifyExecution : Placed Vm.VerifyExecution.code 15570 :=
  placed_of_nodup hP labels_nodup Vm.VerifyExecution.code_at
theorem placed_Seed : Placed Vm.Seed.code 15671 :=
  placed_of_nodup hP labels_nodup Vm.Seed.code_at
theorem placed_Verify : Placed Vm.Verify.code 15703 :=
  placed_of_nodup hP labels_nodup Vm.Verify.code_at
theorem placed_IvWord : Placed Vm.IvWord.code 15806 :=
  placed_of_nodup hP labels_nodup Vm.IvWord.code_at
theorem placed_KinvSq : Placed Vm.KinvSq.code 15839 :=
  placed_of_nodup hP labels_nodup Vm.KinvSq.code_at
theorem placed_LeanvmVerify : Placed Vm.LeanvmVerify.code 15849 :=
  placed_of_nodup hP labels_nodup Vm.LeanvmVerify.code_at
theorem placed_Memcpy : Placed Vm.Memcpy.code 15937 :=
  placed_of_nodup hP labels_nodup Vm.Memcpy.code_at
theorem placed_Memset : Placed Vm.Memset.code 15961 :=
  placed_of_nodup hP labels_nodup Vm.Memset.code_at

end

end NativeRustcVmArm.Placement
