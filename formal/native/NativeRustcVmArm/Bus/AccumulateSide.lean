module

public import NativeRustcVmArm.Bus.AccumulateSide.Start
public import NativeRustcVmArm.Bus.AccumulateSide.Body

/-!
# `accumulate_side` on AArch64

The entry computes the framework's known part and selectors, the table loop updates the forms and padding sum, and the epilogue writes the result and restores the caller's frame.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeArm NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {k : Nat}

/-- The complete rustc-generated function meets its contract. -/
theorem accumulateSide_spec (hp : Placed code k)
    (hee : Spec (Labels.label eqEvalFnOfEqAboveLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost)
    (hmc : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hbf : Spec (Labels.label blockFormLabel) BlockFormPre BlockFormPost)
    (has : ∀ f g, Spec (Labels.label formBufAddScaledLabel) (FormBufAddScaledPre f g) (FormBufAddScaledPost f g))
    (hpw : Spec (Labels.label paddingWeightLabel) PaddingWeightPre PaddingWeightPost)
    (hev : ∀ f, Spec (Labels.label evaluateLabel) (EvaluatePre f) (EvaluatePost f))
    {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
    {Fm : Array (Array FormW)} {SL : BusLayoutW} :
    Spec (Labels.label accumulateSideLabel) (AccumulateSidePre L rows bl Fm SL)
      (AccumulateSidePost L rows bl Fm SL) := by
  intro m0 hpre
  have he : Labels.label accumulateSideLabel = Host.addrOf (k + 0) := hp.label (j := 0) rfl
  rw [he]
  have h := pre_of hpre
  exact start_spec hp h hee hmul hmc fun _ hs hf ↦ body_spec hp h hee hbf has hpw hmul hev hs hf

end

end NativeRustcVmArm.Bus.AccumulateSide
