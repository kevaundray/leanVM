module

public import NativeRustcVmX64.Bus.AccumulateSide.Exit

/-! # `accumulate_side`: entry-to-return contract (x86-64)

The known and framework loops, initialization, table loop and output epilogue compose without
additional entry assumptions. Callee contracts are discharged by the x86 assembly integration.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcVmX64.Transcript NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus

public section

variable [Host] {k : Nat}

 theorem accumulateSide_spec (hp : Placed code k)
    (hee : Spec (Labels.label eqEvalFnOfEqAboveLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost)
    (hmc : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hbf : Spec (Labels.label blockFormLabel) BlockFormPre BlockFormPost)
    (has : ∀ f g, Spec (Labels.label formBufAddScaledLabel) (FormBufAddScaledPre f g) (FormBufAddScaledPost f g))
    (hpw : Spec (Labels.label paddingWeightLabel) PaddingWeightPre PaddingWeightPost)
    (hev : ∀ f, Spec (Labels.label evaluateLabel) (EvaluatePre f) (EvaluatePost f)) :
    ∀ L rows bl Fm SL, Spec (Labels.label accumulateSideLabel)
      (AccumulateSidePre L rows bl Fm SL) (AccumulateSidePost L rows bl Fm SL) := by
  intro L rows bl Fm SL m0 hpre
  have h := pre_of hpre
  refine Eventually.bind (front hp h hee hmul (lpT L rows bl Fm SL m0 0)) fun st ⟨hpc, hst⟩ ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc hst
  subst hpc
  refine Eventually.bind (toTables hp h hmc hst) fun st ⟨hpc, hst⟩ ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc hst
  subst hpc
  refine Eventually.bind (tableLoop hp h hee hmul hbf has hpw hev (by have := h.blen; omega) hst)
    fun st ⟨hpc, hst⟩ ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc hst
  subst hpc
  exact finish hp h hst

end

end NativeRustcVmX64.Bus.AccumulateSide
