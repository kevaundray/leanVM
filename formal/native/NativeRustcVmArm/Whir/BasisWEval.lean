module

public import NativeRustcVmArm.Whir.BasisWEval.Tail

/-!
# `BasisW::eval`

The prologue saves the registers, calls `LayoutW::placement` on `QKECCAK` and takes the first
scale (`entry`); `ring_claim_weight` gives the ring-switched claim's weight (`ring_call`), times
the first scale (`first`); the column claims' loop adds each placed claim's `column_weight` times
its scale (`loop_run`); the out-of-domain claim's `eq_eval` times its scale ends the sum, stored
as `Some` at the output (`ood_scale`, `finish`). The sum is `BasisW.eval` (`eval_eq`).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeArm NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmArm.Vm.BasisWEval

public section

variable [Host] {k : Nat}

/-- **`BasisW::eval`'s contract.** -/
theorem basisWEval_spec (hp : Placed code k)
    (hpl : ∀ L, Spec (label layoutWPlacementLabel) (LayoutWPlacementPre L)
      (LayoutWPlacementPost L))
    (hrcw : Spec (label ringClaimWeightLabel) RingClaimWeightPre RingClaimWeightPost)
    (hcw : Spec (label columnWeightLabel) ColumnWeightPre ColumnWeightPost)
    (heq : Spec (label eqEvalLabel) EqEvalPre EqEvalPost)
    (hmul : Spec (label ewMulLabel) EWMulPre EWMulPost) (ba : BasisAddrs) (b : BasisW) :
    Spec (label basisWEvalLabel) (BasisWEvalPre ba b) (BasisWEvalPost b) := by
  intro m0 hpre
  obtain ⟨v, h⟩ := in_of_pre hpre
  rw [show Labels.label basisWEvalLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  have hend : ∀ st : MachineState, st.pc = Host.addrOf (k + 104) → End m0 ba b v st.data →
      Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ BasisWEvalPost b m0 s.data) st :=
    fun st hpc he ↦ ood_scale hp h hpc he fun st' hpc' ha ↦ finish hp h heq hmul hpc' ha
  exact entry hp h hpl fun st hpc ha ↦ ring_call hp h hrcw hpc ha fun st' hpc' hw hf hcs ↦
    first hp h hmul ha hpc' hw hf hcs
      (fun st'' hpc'' hl ↦ loop_run hp h hcw hmul hend rfl hpc'' hl) hend

end

end NativeRustcVmArm.Whir.BasisWEval
