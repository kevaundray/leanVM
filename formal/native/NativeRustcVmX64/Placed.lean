module

public import NativeRustcVmX64.Placed.Nodup
public import NativeRustcVmX64.Code.Vm.Offsets

/-!
# Every function of `leanvm_verify`'s program placed

For each of the program's 137 functions `F`, `placed_F`: `Vm.F.code` sits in `Vm.code` at the index
`Code/Vm/Offsets.lean` gives (`F.code_at`), each of its labels the only one of its name
(`labels_nodup`), so `Placed Vm.F.code k` (`placed_of_nodup`).
-/

namespace NativeRustcVmX64.Placement

open NativeRustcX64

public section

variable [Host] (hP : Host.prog = Vm.code)
include hP

theorem placed_SumcheckOfSumcheckPlain : Placed Vm.SumcheckOfSumcheckPlain.code 0 :=
  placed_of_nodup hP labels_nodup Vm.SumcheckOfSumcheckPlain.code_at
theorem placed_SumcheckOfVerifyLayer : Placed Vm.SumcheckOfVerifyLayer.code 73 :=
  placed_of_nodup hP labels_nodup Vm.SumcheckOfVerifyLayer.code_at
theorem placed_SumcheckOfGkrStep : Placed Vm.SumcheckOfGkrStep.code 165 :=
  placed_of_nodup hP labels_nodup Vm.SumcheckOfGkrStep.code_at
theorem placed_EachRowOfNextLevel : Placed Vm.EachRowOfNextLevel.code 263 :=
  placed_of_nodup hP labels_nodup Vm.EachRowOfNextLevel.code_at
theorem placed_EachRowOfFinalLevel : Placed Vm.EachRowOfFinalLevel.code 435 :=
  placed_of_nodup hP labels_nodup Vm.EachRowOfFinalLevel.code_at
theorem placed_EqEvalFnOfEqAbove : Placed Vm.EqEvalFnOfEqAbove.code 564 :=
  placed_of_nodup hP labels_nodup Vm.EqEvalFnOfEqAbove.code_at
theorem placed_MultilinearEvalByOfMultilinearEval :
    Placed Vm.MultilinearEvalByOfMultilinearEval.code 615 :=
  placed_of_nodup hP labels_nodup Vm.MultilinearEvalByOfMultilinearEval.code_at
theorem placed_MultilinearEvalByOfComputedBytecodeValue :
    Placed Vm.MultilinearEvalByOfComputedBytecodeValue.code 737 :=
  placed_of_nodup hP labels_nodup Vm.MultilinearEvalByOfComputedBytecodeValue.code_at
theorem placed_Keccak256WordsOfHashWords : Placed Vm.Keccak256WordsOfHashWords.code 856 :=
  placed_of_nodup hP labels_nodup Vm.Keccak256WordsOfHashWords.code_at
theorem placed_Keccak256WordsOfFiatShamirIv : Placed Vm.Keccak256WordsOfFiatShamirIv.code 1324 :=
  placed_of_nodup hP labels_nodup Vm.Keccak256WordsOfFiatShamirIv.code_at
theorem placed_InsertionSortOfStackOffsets : Placed Vm.InsertionSortOfStackOffsets.code 1878 :=
  placed_of_nodup hP labels_nodup Vm.InsertionSortOfStackOffsets.code_at
theorem placed_VerifyBusBalanceClosure0 : Placed Vm.VerifyBusBalanceClosure0.code 1947 :=
  placed_of_nodup hP labels_nodup Vm.VerifyBusBalanceClosure0.code_at
theorem placed_SpongeWAbsorbNonce : Placed Vm.SpongeWAbsorbNonce.code 1976 :=
  placed_of_nodup hP labels_nodup Vm.SpongeWAbsorbNonce.code_at
theorem placed_SpongeWDuplexInput : Placed Vm.SpongeWDuplexInput.code 1991 :=
  placed_of_nodup hP labels_nodup Vm.SpongeWDuplexInput.code_at
theorem placed_SpongeWAbsorb : Placed Vm.SpongeWAbsorb.code 2051 :=
  placed_of_nodup hP labels_nodup Vm.SpongeWAbsorb.code_at
theorem placed_SpongeWDuplex : Placed Vm.SpongeWDuplex.code 2083 :=
  placed_of_nodup hP labels_nodup Vm.SpongeWDuplex.code_at
theorem placed_SpongeWSqueeze : Placed Vm.SpongeWSqueeze.code 2092 :=
  placed_of_nodup hP labels_nodup Vm.SpongeWSqueeze.code_at
theorem placed_BufEW30Extend : Placed Vm.BufEW30Extend.code 2106 :=
  placed_of_nodup hP labels_nodup Vm.BufEW30Extend.code_at
theorem placed_BufEW36Extend : Placed Vm.BufEW36Extend.code 2143 :=
  placed_of_nodup hP labels_nodup Vm.BufEW36Extend.code_at
theorem placed_BufEW63Extend : Placed Vm.BufEW63Extend.code 2180 :=
  placed_of_nodup hP labels_nodup Vm.BufEW63Extend.code_at
theorem placed_BufEW230Extend : Placed Vm.BufEW230Extend.code 2217 :=
  placed_of_nodup hP labels_nodup Vm.BufEW230Extend.code_at
theorem placed_BufU64x230Extend : Placed Vm.BufU64x230Extend.code 2254 :=
  placed_of_nodup hP labels_nodup Vm.BufU64x230Extend.code_at
theorem placed_BasisWEval : Placed Vm.BasisWEval.code 2282 :=
  placed_of_nodup hP labels_nodup Vm.BasisWEval.code_at
theorem placed_ReaderLe : Placed Vm.ReaderLe.code 2452 :=
  placed_of_nodup hP labels_nodup Vm.ReaderLe.code_at
theorem placed_ReaderWords : Placed Vm.ReaderWords.code 2486 :=
  placed_of_nodup hP labels_nodup Vm.ReaderWords.code_at
theorem placed_ReaderDigest : Placed Vm.ReaderDigest.code 2529 :=
  placed_of_nodup hP labels_nodup Vm.ReaderDigest.code_at
theorem placed_EWMul : Placed Vm.EWMul.code 2576 :=
  placed_of_nodup hP labels_nodup Vm.EWMul.code_at
theorem placed_EWSqIter : Placed Vm.EWSqIter.code 3260 :=
  placed_of_nodup hP labels_nodup Vm.EWSqIter.code_at
theorem placed_DecodedPhaseCount : Placed Vm.DecodedPhaseCount.code 3280 :=
  placed_of_nodup hP labels_nodup Vm.DecodedPhaseCount.code_at
theorem placed_DecodedStreamElement : Placed Vm.DecodedStreamElement.code 3292 :=
  placed_of_nodup hP labels_nodup Vm.DecodedStreamElement.code_at
theorem placed_DecodedPhase : Placed Vm.DecodedPhase.code 3317 :=
  placed_of_nodup hP labels_nodup Vm.DecodedPhase.code_at
theorem placed_TStateNextScalar : Placed Vm.TStateNextScalar.code 3353 :=
  placed_of_nodup hP labels_nodup Vm.TStateNextScalar.code_at
theorem placed_TStateReadScalar : Placed Vm.TStateReadScalar.code 3388 :=
  placed_of_nodup hP labels_nodup Vm.TStateReadScalar.code_at
theorem placed_TStateReadScalars : Placed Vm.TStateReadScalars.code 3423 :=
  placed_of_nodup hP labels_nodup Vm.TStateReadScalars.code_at
theorem placed_TStateQueryOpenings : Placed Vm.TStateQueryOpenings.code 3465 :=
  placed_of_nodup hP labels_nodup Vm.TStateQueryOpenings.code_at
theorem placed_TStateReadCommitment : Placed Vm.TStateReadCommitment.code 3527 :=
  placed_of_nodup hP labels_nodup Vm.TStateReadCommitment.code_at
theorem placed_TStateSampleChallenges : Placed Vm.TStateSampleChallenges.code 3575 :=
  placed_of_nodup hP labels_nodup Vm.TStateSampleChallenges.code_at
theorem placed_TStateSumcheckRoundPoly : Placed Vm.TStateSumcheckRoundPoly.code 3600 :=
  placed_of_nodup hP labels_nodup Vm.TStateSumcheckRoundPoly.code_at
theorem placed_TStateGrind : Placed Vm.TStateGrind.code 3707 :=
  placed_of_nodup hP labels_nodup Vm.TStateGrind.code_at
theorem placed_FormBufAddScaled : Placed Vm.FormBufAddScaled.code 3743 :=
  placed_of_nodup hP labels_nodup Vm.FormBufAddScaled.code_at
theorem placed_FormBufAddTerm : Placed Vm.FormBufAddTerm.code 3786 :=
  placed_of_nodup hP labels_nodup Vm.FormBufAddTerm.code_at
theorem placed_LayoutWPlacement : Placed Vm.LayoutWPlacement.code 3861 :=
  placed_of_nodup hP labels_nodup Vm.LayoutWPlacement.code_at
theorem placed_RowsRow : Placed Vm.RowsRow.code 3874 :=
  placed_of_nodup hP labels_nodup Vm.RowsRow.code_at
theorem placed_FirstClaim : Placed Vm.FirstClaim.code 3893 :=
  placed_of_nodup hP labels_nodup Vm.FirstClaim.code_at
theorem placed_KeccakOpen : Placed Vm.KeccakOpen.code 4179 :=
  placed_of_nodup hP labels_nodup Vm.KeccakOpen.code_at
theorem placed_KeccakPhase : Placed Vm.KeccakPhase.code 4766 :=
  placed_of_nodup hP labels_nodup Vm.KeccakPhase.code_at
theorem placed_SlotWeights : Placed Vm.SlotWeights.code 4880 :=
  placed_of_nodup hP labels_nodup Vm.SlotWeights.code_at
theorem placed_VerifyLayer : Placed Vm.VerifyLayer.code 4997 :=
  placed_of_nodup hP labels_nodup Vm.VerifyLayer.code_at
theorem placed_VerifyKeccak : Placed Vm.VerifyKeccak.code 5738 :=
  placed_of_nodup hP labels_nodup Vm.VerifyKeccak.code_at
theorem placed_InstanceWeights : Placed Vm.InstanceWeights.code 6231 :=
  placed_of_nodup hP labels_nodup Vm.InstanceWeights.code_at
theorem placed_LinearTranspose : Placed Vm.LinearTranspose.code 6786 :=
  placed_of_nodup hP labels_nodup Vm.LinearTranspose.code_at
theorem placed_KeccakPi : Placed Vm.KeccakPi.code 6985 :=
  placed_of_nodup hP labels_nodup Vm.KeccakPi.code_at
theorem placed_OpenPhase : Placed Vm.OpenPhase.code 7003 :=
  placed_of_nodup hP labels_nodup Vm.OpenPhase.code_at
theorem placed_Climb : Placed Vm.Climb.code 7115 :=
  placed_of_nodup hP labels_nodup Vm.Climb.code_at
theorem placed_RingSwitch : Placed Vm.RingSwitch.code 7205 :=
  placed_of_nodup hP labels_nodup Vm.RingSwitch.code_at
theorem placed_RingTarget : Placed Vm.RingTarget.code 7310 :=
  placed_of_nodup hP labels_nodup Vm.RingTarget.code_at
theorem placed_RingCoefficients : Placed Vm.RingCoefficients.code 7571 :=
  placed_of_nodup hP labels_nodup Vm.RingCoefficients.code_at
theorem placed_RingPsi : Placed Vm.RingPsi.code 7730 :=
  placed_of_nodup hP labels_nodup Vm.RingPsi.code_at
theorem placed_BlockForm : Placed Vm.BlockForm.code 7864 :=
  placed_of_nodup hP labels_nodup Vm.BlockForm.code_at
theorem placed_BusLayout : Placed Vm.BusLayout.code 7934 :=
  placed_of_nodup hP labels_nodup Vm.BusLayout.code_at
theorem placed_Fingerprints : Placed Vm.Fingerprints.code 8193 :=
  placed_of_nodup hP labels_nodup Vm.Fingerprints.code_at
theorem placed_BytecodeShare : Placed Vm.BytecodeShare.code 8285 :=
  placed_of_nodup hP labels_nodup Vm.BytecodeShare.code_at
theorem placed_AccumulateSide : Placed Vm.AccumulateSide.code 8463 :=
  placed_of_nodup hP labels_nodup Vm.AccumulateSide.code_at
theorem placed_VerifyBusBalance : Placed Vm.VerifyBusBalance.code 8776 :=
  placed_of_nodup hP labels_nodup Vm.VerifyBusBalance.code_at
theorem placed_ComputedBytecodeValue : Placed Vm.ComputedBytecodeValue.code 9215 :=
  placed_of_nodup hP labels_nodup Vm.ComputedBytecodeValue.code_at
theorem placed_GkrLayers : Placed Vm.GkrLayers.code 9235 :=
  placed_of_nodup hP labels_nodup Vm.GkrLayers.code_at
theorem placed_VerifyGkrGrandProducts : Placed Vm.VerifyGkrGrandProducts.code 9298 :=
  placed_of_nodup hP labels_nodup Vm.VerifyGkrGrandProducts.code_at
theorem placed_GkrStep : Placed Vm.GkrStep.code 9354 :=
  placed_of_nodup hP labels_nodup Vm.GkrStep.code_at
theorem placed_FoldRound : Placed Vm.FoldRound.code 9613 :=
  placed_of_nodup hP labels_nodup Vm.FoldRound.code_at
theorem placed_GlueLevel : Placed Vm.GlueLevel.code 9752 :=
  placed_of_nodup hP labels_nodup Vm.GlueLevel.code_at
theorem placed_GluedEval : Placed Vm.GluedEval.code 9855 :=
  placed_of_nodup hP labels_nodup Vm.GluedEval.code_at
theorem placed_NextLevel : Placed Vm.NextLevel.code 9899 :=
  placed_of_nodup hP labels_nodup Vm.NextLevel.code_at
theorem placed_NovelEval : Placed Vm.NovelEval.code 10169 :=
  placed_of_nodup hP labels_nodup Vm.NovelEval.code_at
theorem placed_QueryBits : Placed Vm.QueryBits.code 10265 :=
  placed_of_nodup hP labels_nodup Vm.QueryBits.code_at
theorem placed_FinalLevel : Placed Vm.FinalLevel.code 10293 :=
  placed_of_nodup hP labels_nodup Vm.FinalLevel.code_at
theorem placed_FoldRounds : Placed Vm.FoldRounds.code 10730 :=
  placed_of_nodup hP labels_nodup Vm.FoldRounds.code_at
theorem placed_WhirLevels : Placed Vm.WhirLevels.code 10888 :=
  placed_of_nodup hP labels_nodup Vm.WhirLevels.code_at
theorem placed_InducedWeight : Placed Vm.InducedWeight.code 10971 :=
  placed_of_nodup hP labels_nodup Vm.InducedWeight.code_at
theorem placed_SampleQueries : Placed Vm.SampleQueries.code 11099 :=
  placed_of_nodup hP labels_nodup Vm.SampleQueries.code_at
theorem placed_SubspaceTable : Placed Vm.SubspaceTable.code 11207 :=
  placed_of_nodup hP labels_nodup Vm.SubspaceTable.code_at
theorem placed_SubspaceAtTable : Placed Vm.SubspaceAtTable.code 11431 :=
  placed_of_nodup hP labels_nodup Vm.SubspaceAtTable.code_at
theorem placed_VerifyStackedOpening : Placed Vm.VerifyStackedOpening.code 11489 :=
  placed_of_nodup hP labels_nodup Vm.VerifyStackedOpening.code_at
theorem placed_Ladder : Placed Vm.Ladder.code 11735 :=
  placed_of_nodup hP labels_nodup Vm.Ladder.code_at
theorem placed_FoldRow : Placed Vm.FoldRow.code 11865 :=
  placed_of_nodup hP labels_nodup Vm.FoldRow.code_at
theorem placed_LanesOf : Placed Vm.LanesOf.code 11947 :=
  placed_of_nodup hP labels_nodup Vm.LanesOf.code_at
theorem placed_ClimbLevel : Placed Vm.ClimbLevel.code 12024 :=
  placed_of_nodup hP labels_nodup Vm.ClimbLevel.code_at
theorem placed_WriteOpenings : Placed Vm.WriteOpenings.code 12176 :=
  placed_of_nodup hP labels_nodup Vm.WriteOpenings.code_at
theorem placed_Find : Placed Vm.Find.code 12465 :=
  placed_of_nodup hP labels_nodup Vm.Find.code_at
theorem placed_InsD : Placed Vm.InsD.code 12489 :=
  placed_of_nodup hP labels_nodup Vm.InsD.code_at
theorem placed_Decode : Placed Vm.Decode.code 12563 :=
  placed_of_nodup hP labels_nodup Vm.Decode.code_at
theorem placed_PhaseM : Placed Vm.PhaseM.code 12653 :=
  placed_of_nodup hP labels_nodup Vm.PhaseM.code_at
theorem placed_RdRows : Placed Vm.RdRows.code 12854 :=
  placed_of_nodup hP labels_nodup Vm.RdRows.code_at
theorem placed_BitLength : Placed Vm.BitLength.code 12976 :=
  placed_of_nodup hP labels_nodup Vm.BitLength.code_at
theorem placed_IndexMleFrom : Placed Vm.IndexMleFrom.code 13015 :=
  placed_of_nodup hP labels_nodup Vm.IndexMleFrom.code_at
theorem placed_PaddingWeight : Placed Vm.PaddingWeight.code 13074 :=
  placed_of_nodup hP labels_nodup Vm.PaddingWeight.code_at
theorem placed_SelectorPoint : Placed Vm.SelectorPoint.code 13146 :=
  placed_of_nodup hP labels_nodup Vm.SelectorPoint.code_at
theorem placed_Dot : Placed Vm.Dot.code 13212 :=
  placed_of_nodup hP labels_nodup Vm.Dot.code_at
theorem placed_Kinv : Placed Vm.Kinv.code 13258 :=
  placed_of_nodup hP labels_nodup Vm.Kinv.code_at
theorem placed_Kmul : Placed Vm.Kmul.code 13320 :=
  placed_of_nodup hP labels_nodup Vm.Kmul.code_at
theorem placed_Kpow : Placed Vm.Kpow.code 13545 :=
  placed_of_nodup hP labels_nodup Vm.Kpow.code_at
theorem placed_SumE : Placed Vm.SumE.code 13579 :=
  placed_of_nodup hP labels_nodup Vm.SumE.code_at
theorem placed_Powers : Placed Vm.Powers.code 13631 :=
  placed_of_nodup hP labels_nodup Vm.Powers.code_at
theorem placed_ProdE : Placed Vm.ProdE.code 13666 :=
  placed_of_nodup hP labels_nodup Vm.ProdE.code_at
theorem placed_EqEval : Placed Vm.EqEval.code 13691 :=
  placed_of_nodup hP labels_nodup Vm.EqEval.code_at
theorem placed_EqKernel : Placed Vm.EqKernel.code 13733 :=
  placed_of_nodup hP labels_nodup Vm.EqKernel.code_at
theorem placed_PolyEval : Placed Vm.PolyEval.code 13830 :=
  placed_of_nodup hP labels_nodup Vm.PolyEval.code_at
theorem placed_PushClaim : Placed Vm.PushClaim.code 13866 :=
  placed_of_nodup hP labels_nodup Vm.PushClaim.code_at
theorem placed_RingWeight : Placed Vm.RingWeight.code 13907 :=
  placed_of_nodup hP labels_nodup Vm.RingWeight.code_at
theorem placed_CommitStack : Placed Vm.CommitStack.code 14139 :=
  placed_of_nodup hP labels_nodup Vm.CommitStack.code_at
theorem placed_ColumnWeight : Placed Vm.ColumnWeight.code 14172 :=
  placed_of_nodup hP labels_nodup Vm.ColumnWeight.code_at
theorem placed_RingClaimWeight : Placed Vm.RingClaimWeight.code 14220 :=
  placed_of_nodup hP labels_nodup Vm.RingClaimWeight.code_at
theorem placed_ReadOod : Placed Vm.ReadOod.code 14283 :=
  placed_of_nodup hP labels_nodup Vm.ReadOod.code_at
theorem placed_KeccakF : Placed Vm.KeccakF.code 14323 :=
  placed_of_nodup hP labels_nodup Vm.KeccakF.code_at
theorem placed_HashPair : Placed Vm.HashPair.code 14685 :=
  placed_of_nodup hP labels_nodup Vm.HashPair.code_at
theorem placed_FormTerms : Placed Vm.FormTerms.code 14710 :=
  placed_of_nodup hP labels_nodup Vm.FormTerms.code_at
theorem placed_StackPoint : Placed Vm.StackPoint.code 14735 :=
  placed_of_nodup hP labels_nodup Vm.StackPoint.code_at
theorem placed_BuildLayout : Placed Vm.BuildLayout.code 14806 :=
  placed_of_nodup hP labels_nodup Vm.BuildLayout.code_at
theorem placed_ColumnKappas : Placed Vm.ColumnKappas.code 14930 :=
  placed_of_nodup hP labels_nodup Vm.ColumnKappas.code_at
theorem placed_ConstraintsW : Placed Vm.ConstraintsW.code 15099 :=
  placed_of_nodup hP labels_nodup Vm.ConstraintsW.code_at
theorem placed_PlacementsOf : Placed Vm.PlacementsOf.code 15158 :=
  placed_of_nodup hP labels_nodup Vm.PlacementsOf.code_at
theorem placed_StackOffsets : Placed Vm.StackOffsets.code 15297 :=
  placed_of_nodup hP labels_nodup Vm.StackOffsets.code_at
theorem placed_ReadAnnouncedSizes : Placed Vm.ReadAnnouncedSizes.code 15427 :=
  placed_of_nodup hP labels_nodup Vm.ReadAnnouncedSizes.code_at
theorem placed_Evaluate : Placed Vm.Evaluate.code 15513 :=
  placed_of_nodup hP labels_nodup Vm.Evaluate.code_at
theorem placed_TablePhase : Placed Vm.TablePhase.code 15591 :=
  placed_of_nodup hP labels_nodup Vm.TablePhase.code_at
theorem placed_TableTerms : Placed Vm.TableTerms.code 15660 :=
  placed_of_nodup hP labels_nodup Vm.TableTerms.code_at
theorem placed_TableWeights : Placed Vm.TableWeights.code 15832 :=
  placed_of_nodup hP labels_nodup Vm.TableWeights.code_at
theorem placed_TableSumcheck : Placed Vm.TableSumcheck.code 16015 :=
  placed_of_nodup hP labels_nodup Vm.TableSumcheck.code_at
theorem placed_PublicInputPhase : Placed Vm.PublicInputPhase.code 16231 :=
  placed_of_nodup hP labels_nodup Vm.PublicInputPhase.code_at
theorem placed_TableColumnClaims : Placed Vm.TableColumnClaims.code 16374 :=
  placed_of_nodup hP labels_nodup Vm.TableColumnClaims.code_at
theorem placed_VerifyExecution : Placed Vm.VerifyExecution.code 16601 :=
  placed_of_nodup hP labels_nodup Vm.VerifyExecution.code_at
theorem placed_Seed : Placed Vm.Seed.code 16709 :=
  placed_of_nodup hP labels_nodup Vm.Seed.code_at
theorem placed_Verify : Placed Vm.Verify.code 16748 :=
  placed_of_nodup hP labels_nodup Vm.Verify.code_at
theorem placed_IvWord : Placed Vm.IvWord.code 16875 :=
  placed_of_nodup hP labels_nodup Vm.IvWord.code_at
theorem placed_KinvSq : Placed Vm.KinvSq.code 16906 :=
  placed_of_nodup hP labels_nodup Vm.KinvSq.code_at
theorem placed_LeanvmVerify : Placed Vm.LeanvmVerify.code 16919 :=
  placed_of_nodup hP labels_nodup Vm.LeanvmVerify.code_at
theorem placed_Memcpy : Placed Vm.Memcpy.code 17029 :=
  placed_of_nodup hP labels_nodup Vm.Memcpy.code_at
theorem placed_Memset : Placed Vm.Memset.code 17061 :=
  placed_of_nodup hP labels_nodup Vm.Memset.code_at

end

end NativeRustcVmX64.Placement
