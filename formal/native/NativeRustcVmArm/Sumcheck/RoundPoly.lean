module

public import NativeRustcVmArm.Sumcheck.RoundPoly.Entry

/-!
# `TState::sumcheck_round_poly`

**`roundPoly_spec`**: in equality mode (`some_entry`) or plain mode (`none_entry`), the round
polynomial `sumcheckRoundPoly count claim eq` at the message, the `TState` the next state
(`RoundPolyPost`).
-/

namespace NativeRustcVmArm.Sumcheck.RoundPoly

open NativeRustcArm NativeRustcVmArm.Vm.TStateSumcheckRoundPoly NativeArm
open NativeVm.Model NativeRustcVm.Transcript

public section

variable [Host] {k : Nat}

/-- **`sumcheck_round_poly`'s contract.** -/
theorem roundPoly_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label readScalarLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hrss : ∀ a s, Spec (Labels.label readScalarsLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hsum : Spec (Labels.label sumELabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label bitLengthLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label grindLabel) (GrindPre a s) (GrindPost a s))
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost)
    (a : DecArea) (s : TState) (e : Option EW) :
    Spec (Labels.label roundPolyLabel) (RoundPolyPre a s e) (RoundPolyPost a s e) := by
  intro m0 hpre
  rw [show Labels.label roundPolyLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  cases e with
  | none => exact none_entry hp hrs hrss hsum hbl hgr hpre
  | some ev => exact some_entry hp hrss hsum hbl hgr hmul hpre

end

end NativeRustcVmArm.Sumcheck.RoundPoly
