module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.LayersFront
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Tail

/-!
# `verify_keccak` on x86-64

The function implements `VerifyKeccakPost` from its unchanged precondition, using only the
stated contracts of its callees. Both failure returns and the successful output are included.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeVm.Model NativeRustcVmX64.Vm.VerifyKeccak
open NativeRustcVm.Transcript
open NativeRustcVm.KeccakGkr (off)
open Back

public section

variable [Host] {k : Nat}

theorem verifyKeccak_spec (hp : Placed code k)
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
    (hmle : Spec (Labels.label mleOfMultilinearEvalLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    (hdot : Spec (Labels.label dotLabel) DotPre DotPost) :
    ∀ a s cs inst output, Spec (Labels.label verifyKeccakLabel)
      (VerifyKeccakPre a s cs inst output) (VerifyKeccakPost a s cs inst output) := by
  intro a s cs inst output m0 hpre
  have c := ctx_of hpre
  have hsize : inst.size = (reg m0 .rsi).toNat := hpre.2.2.2.2.2.2.2.2.2.1
  refine toB40 hp hpre hmemcpy hbl (hgr a) (hsc a) (hrs a) hfc (hvl a)
    fun st s1 first cl cm hat hts hcl hcw hf hfw hfirst hlast hmod ↦ ?_
  have hfitFirst : SegmentsFit (reg m0 .rsi).toNat first := by
    unfold SegmentsFit
    rw [hfirst, ← hsize]
    omega
  have hfit : SegmentsFit (reg m0 .rsi).toNat cl := fit_size hlast hfitFirst
  refine open1Step hp hpre (hko a) hat rfl rfl rfl hts hf hfw hfitFirst hmod
    fun st1 slot ws v s2 hat1 hr1 hv1 hslot1 hws1 hts1 hc1 hk1 ↦ ?_
  obtain ⟨h6, h64⟩ := open_weights_size hr1
  have hcl1 := Chg.claimF c hc1 (by decide) (by decide) (by decide) (by decide) hcl
  have hcw1 := Chg.wtsR c hc1 (by decide) (by decide) (by decide) (by decide) hcw
  refine wordStep hp hpre (hrs a) hmul hat1 hv1 h64 hws1 hts1
    (hmod.trans (restOpen_some hr1)) fun st2 w s3 hat2 hts2 hmod2 hc2 hk2 ↦ ?_
  have hslot2 := Chg.ewsF c hc2 (by decide) (by decide)
    (by rw [Array.length_toList, h6]; decide) (by rw [Array.length_toList, h6]; decide) hslot1
  have hcl2 := Chg.claimF c hc2 (by decide) (by decide) (by decide) (by decide) hcl1
  have hcw2 := Chg.wtsR c hc2 (by decide) (by decide) (by decide) (by decide) hcw1
  refine claimStep hp hpre hext hpc hat2 rfl rfl hslot2 h6 hts2 hcl2 hcw2
    fun st3 hat3 hts3 hcl3 hcw3 hcls3 ↦ ?_
  exact tailStep hp hpre (hsp a) (hko a) (hrss a) hmle hdot hmul hext
    hat3 hts3 hcl3 hcw3 hcls3 hfit hmod2

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak

/-- info: 'NativeRustcVmX64.KeccakGkr.VerifyKeccak.verifyKeccak_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.KeccakGkr.VerifyKeccak.verifyKeccak_spec
