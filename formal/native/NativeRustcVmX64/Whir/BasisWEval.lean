module

public import NativeRustcVmX64.Whir.BasisWEval.Tail

/-!
# `BasisW::eval` on x86-64

The prologue pushes the callee-saved registers, keeps the output's address, the point and the
layout's address in the 160-byte frame and calls `LayoutW::placement` on `QKECCAK`, then takes
the first scale (`entry`); `ring_claim_weight`, its two stack arguments the point, gives the
ring-switched claim's weight (`ring_call`), times the first scale (`first`); the column claims'
loop adds each placed claim's `column_weight` (`Some`: at most 36 coordinates and a stack of log
at most 30 fit its 66 slots) times its scale (`loop_run`); the out-of-domain claim's `eq_eval`
times its scale ends the sum, stored as `Some` at the output (`ood_scale`, `finish`). The sum is
`BasisW.eval` (`In.eval_eq`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeVm.Model NativeRustcVm.Whir NativeRustcVmX64.Vm.BasisWEval

public section

variable [Host] {k : Nat}

/-- **`BasisW::eval`'s contract.** -/
theorem basisWEval_spec (hp : Placed code k)
    (hpl : ∀ L, Spec (Labels.label layoutWPlacementLabel) (LayoutWPlacementPre L)
      (LayoutWPlacementPost L))
    (hrcw : Spec (Labels.label ringClaimWeightLabel) RingClaimWeightPre RingClaimWeightPost)
    (hcw : Spec (Labels.label columnWeightLabel) ColumnWeightPre ColumnWeightPost)
    (heq : Spec (Labels.label eqEvalLabel) EqEvalPre EqEvalPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) (ba : BasisAddrs) (b : BasisW) :
    Spec (Labels.label basisWEvalLabel) (BasisWEvalPre ba b) (BasisWEvalPost b) := by
  intro m0 hpre
  obtain ⟨v, h⟩ := in_of_pre hpre
  rw [show Labels.label basisWEvalLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  have hend : ∀ st : MachineState, st.pc = Host.addrOf (k + 127) → End m0 ba b v st.data →
      Eventually (step1 Host.exe) (Goal m0 b) st :=
    fun st hpc he ↦ ood_scale hp h hpc he fun st' hpc' ha ↦ finish hp h heq hmul hpc' ha
  exact entry hp h hpl fun st hpc ha ↦ ring_call hp h hrcw hpc ha fun st' hpc' ha' ↦
    first hp h hmul hpc' ha' (fun st'' hpc'' hm ↦ loop_run hp h hcw hmul hend rfl hpc'' hm) hend

end

end NativeRustcVmX64.Whir.BasisWEval

/-- info: 'NativeRustcVmX64.Whir.BasisWEval.basisWEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.BasisWEval.basisWEval_spec
