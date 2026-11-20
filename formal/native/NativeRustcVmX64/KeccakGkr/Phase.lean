module

public import NativeRustcVmX64.KeccakGkr.KeccakPhase
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak

/-!
# Phase 6's entry on x86-64: `keccak_phase` (and `verify_keccak`)

The phase entry uses the proved `verify_keccak` contract. Its remaining hypotheses are precisely
the contracts of `verify_keccak`'s callees; no `verify_keccak` hypothesis remains.
-/

namespace NativeRustcVmX64.KeccakGkr

open NativeRustcX64 NativeVm.Model
open NativeRustcVm.Transcript (DecArea)

public section

variable [Host] {kp kv : Nat}

theorem keccakPhase_spec
    (hp : Placed NativeRustcVmX64.Vm.KeccakPhase.code kp)
    (hv : Placed NativeRustcVmX64.Vm.VerifyKeccak.code kv)
    (hbl : Spec (Labels.label bitLengthLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label grindLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label sampleChallengesLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrs : ∀ a s, Spec (Labels.label readScalarLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hrss : ∀ a s, Spec (Labels.label readScalarsLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hfc : ∀ inst segment lanePoint output, Spec (Labels.label firstClaimLabel)
      (FirstClaimPre inst segment lanePoint output) (FirstClaimPost inst segment lanePoint output))
    (hmemcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hvl : ∀ a s c, Spec (Labels.label verifyLayerLabel) (VerifyLayerPre a s c) (VerifyLayerPost a s c))
    (hko : ∀ a s c, Spec (Labels.label keccakOpenLabel) (KeccakOpenPre a s c) (KeccakOpenPost a s c))
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost)
    (hext : Spec (Labels.label bufEW36ExtendLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    (hpc : ∀ cs, Spec (Labels.label pushClaimLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hsp : ∀ a s, Spec (Labels.label sumcheckPlainLabel) (SumcheckPlainPre a s) (SumcheckPlainPost a s))
    (hmle : Spec (Labels.label mleOfMultilinearEvalLabel) MleOfMultilinearEvalPre MleOfMultilinearEvalPost)
    (hdot : Spec (Labels.label dotLabel) DotPre DotPost)
    (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (layout : LayoutW)
    (evals : Array (Array EW × Array EW)) :
    Spec (Labels.label keccakPhaseLabel) (KeccakPhasePre a s cs layout evals)
      (KeccakPhasePost a s cs layout evals) :=
  KeccakPhase.keccakPhase_spec hp hmemcpy
    (VerifyKeccak.verifyKeccak_spec hv hbl hgr hsc hrs hrss hfc hmemcpy hvl hko hmul hext hpc hsp hmle hdot)
    a s cs layout evals

end

end NativeRustcVmX64.KeccakGkr

/-- info: 'NativeRustcVmX64.KeccakGkr.keccakPhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.KeccakGkr.keccakPhase_spec
