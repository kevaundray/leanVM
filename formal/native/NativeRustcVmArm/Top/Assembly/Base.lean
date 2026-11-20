module

public import NativeRustcVmArm.Mem
public import NativeRustcVmArm.Placed
public import NativeRustcVmArm.Field
public import NativeRustcVmArm.Arrays
public import NativeRustcVmArm.Arrays.EqKernel
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfMultilinearEval
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfComputedBytecodeValue
public import NativeRustcVmArm.Keccak
public import NativeRustcVmArm.Transcript

/-!
# The call tree's leaves, placed in `leanvm_verify`'s program

Each proved contract of `field.rs`, the arrays, `keccak.rs`, `transcript.rs`/`input.rs`, `memcpy`
and `memset`, instantiated at its function's place in `Vm.code` (`Placement.placed_<Fn> hP`) and
with its callees' instantiated contracts, in the form its callers take it.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeArm.Host] (hP : NativeArm.Host.prog = Vm.code)
include hP

theorem memcpy : Spec (label "memcpy") MemcpyPre MemcpyPost :=
  Mem.memcpy_spec (placed_Memcpy hP)

theorem memset : Spec (label "memset") MemsetPre MemsetPost :=
  Mem.memset_spec (placed_Memset hP)

/-! ## `field.rs` -/

theorem kmul : Spec (label kmulLabel) KmulPre KmulPost :=
  Field.Kmul.kmul_spec (placed_Kmul hP)

theorem ewMul : Spec (label ewMulLabel) EWMulPre EWMulPost :=
  Field.EWMul.ewMul_spec (placed_EWMul hP)

theorem kinvSq : Spec (label kinvSqLabel) KinvSqPre KinvSqPost :=
  Field.KinvSq.kinvSq_spec (placed_KinvSq hP) (kmul hP)

theorem kinv : Spec (label kinvLabel) KinvPre KinvPost :=
  Field.Kinv.kinv_spec (placed_Kinv hP) (kmul hP) (kinvSq hP)

theorem kpow : Spec (label kpowLabel) KpowPre KpowPost :=
  Field.Kpow.kpow_spec (placed_Kpow hP) (kmul hP)

theorem ewSqIter : Spec (label ewSqIterLabel) EWSqIterPre EWSqIterPost :=
  Field.EWSqIter.ewSqIter_spec (placed_EWSqIter hP) (ewMul hP)

theorem bitLength : Spec (label bitLengthLabel) BitLengthPre BitLengthPost :=
  Field.BitLength.bitLength_spec (placed_BitLength hP)

/-! ## Arrays -/

theorem dot : Spec (label dotLabel) DotPre DotPost :=
  Arrays.Dot.dot_spec (placed_Dot hP) (ewMul hP)

theorem eqEval : Spec (label eqEvalLabel) EqEvalPre EqEvalPost :=
  Arrays.EqEval.eqEval_spec (placed_EqEval hP) (ewMul hP)

theorem eqEvalFn :
    Spec (label eqEvalFnOfEqAboveLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost :=
  Arrays.EqEvalFn.eqEvalFn_spec (placed_EqEvalFnOfEqAbove hP) (ewMul hP)

theorem polyEval : Spec (label polyEvalLabel) PolyEvalPre PolyEvalPost :=
  Arrays.PolyEval.polyEval_spec (placed_PolyEval hP) (ewMul hP)

theorem indexMleFrom : Spec (label indexMleFromLabel) IndexMleFromPre IndexMleFromPost :=
  Arrays.IndexMleFrom.indexMleFrom_spec (placed_IndexMleFrom hP) (ewMul hP)

theorem paddingWeight : Spec (label paddingWeightLabel) PaddingWeightPre PaddingWeightPost :=
  Arrays.PaddingWeight.paddingWeight_spec (placed_PaddingWeight hP) (ewMul hP)

theorem powers : Spec (label powersLabel) PowersPre PowersPost :=
  Arrays.Powers.powers_spec (placed_Powers hP) (ewMul hP)

theorem prodE : Spec (label prodELabel) ProdEPre ProdEPost :=
  Arrays.ProdE.prodE_spec (placed_ProdE hP) (ewMul hP)

theorem sumE : Spec (label sumELabel) SumEPre SumEPost :=
  Arrays.SumE.sumE_spec (placed_SumE hP)

theorem selectorPoint : Spec (label selectorPointLabel) SelectorPointPre SelectorPointPost :=
  Arrays.SelectorPoint.selectorPoint_spec (placed_SelectorPoint hP)

theorem bufEW30Extend :
    Spec (label bufEW30ExtendLabel) (BufEWExtendPre 30) (BufEWExtendPost 30) :=
  Arrays.BufEW30Extend.bufEW30Extend_spec (placed_BufEW30Extend hP)

theorem bufEW36Extend :
    Spec (label bufEW36ExtendLabel) (BufEWExtendPre 36) (BufEWExtendPost 36) :=
  Arrays.BufEW36Extend.bufEW36Extend_spec (placed_BufEW36Extend hP)

theorem bufEW63Extend :
    Spec (label bufEW63ExtendLabel) (BufEWExtendPre 63) (BufEWExtendPost 63) :=
  Arrays.BufEW63Extend.bufEW63Extend_spec (placed_BufEW63Extend hP)

theorem bufEW230Extend :
    Spec (label bufEW230ExtendLabel) (BufEWExtendPre 230) (BufEWExtendPost 230) :=
  Arrays.BufEW230Extend.bufEW230Extend_spec (placed_BufEW230Extend hP)

theorem bufU64x230Extend :
    Spec (label bufU64x230ExtendLabel) (BufU64ExtendPre 230) (BufU64ExtendPost 230) :=
  Arrays.BufU64x230Extend.bufU64x230Extend_spec (placed_BufU64x230Extend hP)

theorem eqKernel : Spec (label eqKernelLabel) EqKernelPre EqKernelPost :=
  Arrays.EqKernel.eqKernel_spec (placed_EqKernel hP) (ewMul hP)

theorem mleOfMultilinearEval :
    Spec (label mleOfMultilinearEvalLabel) MleOfMultilinearEvalPre MleOfMultilinearEvalPost :=
  Arrays.MleOfMultilinearEval.mleOfMultilinearEval_spec
    (placed_MultilinearEvalByOfMultilinearEval hP) (ewMul hP)

theorem mleOfComputedBytecodeValue : Spec (label mleOfComputedBytecodeValueLabel)
    MleOfComputedBytecodeValuePre MleOfComputedBytecodeValuePost :=
  Arrays.MleOfComputedBytecodeValue.mleOfComputedBytecodeValue_spec
    (placed_MultilinearEvalByOfComputedBytecodeValue hP) (ewMul hP)

/-! ## `keccak.rs` -/

theorem keccakF : Spec (label keccakFLabel) KeccakFPre KeccakFPost :=
  keccakF_spec (placed_KeccakF hP) (memcpy hP)

theorem keccak256WordsHash :
    Spec (label keccak256WordsHashLabel) Keccak256WordsHashPre Keccak256WordsHashPost :=
  keccak256WordsHash_spec (placed_Keccak256WordsOfHashWords hP) (memset hP) (keccakF hP)

theorem ivWord : Spec (label ivWordLabel) IvWordPre IvWordPost :=
  ivWord_spec (placed_IvWord hP)

theorem keccak256WordsIv :
    Spec (label keccak256WordsIvLabel) Keccak256WordsIvPre Keccak256WordsIvPost :=
  keccak256WordsIv_spec (placed_Keccak256WordsOfFiatShamirIv hP) (memset hP) (ivWord hP)
    (keccakF hP)

theorem hashPair : Spec (label hashPairLabel) HashPairPre HashPairPost :=
  hashPair_spec (placed_HashPair hP) (keccak256WordsHash hP)

/-! ## `transcript.rs`, `input.rs` -/

theorem duplexInput :
    ∀ sp, Spec (label duplexInputLabel) (DuplexInputPre sp) (DuplexInputPost sp) :=
  Transcript.DuplexInput.duplexInput_spec (placed_SpongeWDuplexInput hP)

theorem duplex : ∀ sp, Spec (label duplexLabel) (DuplexPre sp) (DuplexPost sp) :=
  Transcript.Duplex.duplex_spec (placed_SpongeWDuplex hP) (duplexInput hP) (keccakF hP)

theorem absorb : ∀ sp, Spec (label absorbLabel) (AbsorbPre sp) (AbsorbPost sp) :=
  Transcript.Absorb.absorb_spec (placed_SpongeWAbsorb hP) (duplex hP)

theorem squeeze : ∀ sp, Spec (label squeezeLabel) (SqueezePre sp) (SqueezePost sp) :=
  Transcript.Squeeze.squeeze_spec (placed_SpongeWSqueeze hP) (duplex hP)

theorem absorbNonce :
    ∀ sp, Spec (label absorbNonceLabel) (AbsorbNoncePre sp) (AbsorbNoncePost sp) :=
  Transcript.AbsorbNonce.absorbNonce_spec (placed_SpongeWAbsorbNonce hP) (absorb hP) (duplex hP)

theorem streamElement : ∀ a stream openings, Spec (label streamElementLabel)
    (StreamElementPre a stream openings) (StreamElementPost stream) :=
  Transcript.StreamElement.streamElement_spec (placed_DecodedStreamElement hP)

theorem phaseCount : ∀ a stream openings, Spec (label phaseCountLabel)
    (PhaseCountPre a stream openings) (PhaseCountPost openings) :=
  Transcript.PhaseCount.phaseCount_spec (placed_DecodedPhaseCount hP)

theorem phase : ∀ a stream openings, Spec (label phaseLabel) (PhasePre a stream openings)
    (PhasePost a openings) :=
  Transcript.Phase.phase_spec (placed_DecodedPhase hP) (phaseCount hP)

theorem nextScalar :
    ∀ a s, Spec (label nextScalarLabel) (NextScalarPre a s) (NextScalarPost a s) :=
  Transcript.NextScalar.nextScalar_spec (placed_TStateNextScalar hP) (streamElement hP)

theorem readScalar :
    ∀ a s, Spec (label readScalarLabel) (ReadScalarPre a s) (ReadScalarPost a s) :=
  Transcript.ReadScalar.readScalar_spec (placed_TStateReadScalar hP) (nextScalar hP) (absorb hP)

theorem readScalars :
    ∀ a s, Spec (label readScalarsLabel) (ReadScalarsPre a s) (ReadScalarsPost a s) :=
  Transcript.ReadScalars.readScalars_spec (placed_TStateReadScalars hP) (readScalar hP)

theorem sampleChallenges : ∀ a s, Spec (label sampleChallengesLabel)
    (SampleChallengesPre a s) (SampleChallengesPost a s) :=
  Transcript.SampleChallenges.sampleChallenges_spec (placed_TStateSampleChallenges hP)
    (squeeze hP)

theorem grind : ∀ a s, Spec (label grindLabel) (GrindPre a s) (GrindPost a s) :=
  Transcript.Grind.grind_spec (placed_TStateGrind hP) (nextScalar hP) (absorbNonce hP)

theorem readCommitment : ∀ a s, Spec (label readCommitmentLabel) (ReadCommitmentPre a s)
    (ReadCommitmentPost a s) :=
  Transcript.ReadCommitment.readCommitment_spec (placed_TStateReadCommitment hP) (readScalar hP)

end

end NativeRustcVmArm.Assembly
