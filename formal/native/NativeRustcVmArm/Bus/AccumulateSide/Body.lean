module

public import NativeRustcVmArm.Bus.AccumulateSide.TableLoop
public import NativeRustcVmArm.Bus.AccumulateSide.Exit

/-!
# `accumulate_side`: from the first table block through the function return
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeArm NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-- All table blocks are accumulated, the result is written, and the entry frame is restored. -/
theorem body_spec (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label eqEvalFnOfEqAboveLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    (hbf : Spec (Labels.label blockFormLabel) BlockFormPre BlockFormPost)
    (has : ∀ f g, Spec (Labels.label formBufAddScaledLabel) (FormBufAddScaledPre f g) (FormBufAddScaledPost f g))
    (hpw : Spec (Labels.label paddingWeightLabel) PaddingWeightPre PaddingWeightPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost)
    (hev : ∀ f, Spec (Labels.label evaluateLabel) (EvaluatePre f) (EvaluatePost f))
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) DL m)
    (hG : FormsAt m.dmem m0.regs.X1.toBitVec Fm) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ AccumulateSidePost L rows bl Fm SL m0 st.data)
      ⟨m, Host.addrOf (k + 233)⟩ := by
  have hstart : 0 < bl.length := by have := h.blen; omega
  have ht := tableLoop hp h hee hbf has hpw hmul hev (j := 0) (Nat.zero_le _) hst hG
    (fun _ hs hf ↦ exit_spec hp h hs hf)
  simpa only [hstart, ↓reduceIte] using ht

end

end NativeRustcVmArm.Bus.AccumulateSide
