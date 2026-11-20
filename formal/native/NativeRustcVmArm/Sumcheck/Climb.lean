module

public import NativeRustcVmArm.Sumcheck.Climb.Loop

/-!
# `climb`

**`climb_spec`**: the entry, the loop over the path's levels, the exit; the output holds
`climb node q path` (`ClimbPost`).
-/

namespace NativeRustcVmArm.Sumcheck.Climb

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Climb NativeArm
open NativeVm.Model LeanVM.Protocol NativeRustcVm.Sumcheck

public section

variable [Host] {k : Nat}

/-- **`climb`'s contract.** -/
theorem climb_spec (hp : Placed code k)
    (hhp : Spec (Labels.label hashPairLabel) HashPairPre HashPairPost)
    (N : Digest) (P : Array Digest) :
    Spec (Labels.label climbLabel) (ClimbPre N P) (ClimbPost N P) := by
  intro m0 hpre
  rw [show Labels.label climbLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  have fin : ∀ (D : Digest), D = climb N m0.regs.X2 P → ∀ st : MachineState,
      st.pc = Host.addrOf (k + 49) → Frame m0 D st.data →
      Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ ClimbPost N P m0 st'.data) st := by
    intro D hD st hpc hfr
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc hD
    exact Eventually.mono (exit_spec hp hpre hfr) fun st' ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, h2, h3, h4⟩
  refine Eventually.bind (entry_spec hp hpre) fun st h ↦ ?_
  rcases h with ⟨hpc, h0, hfr⟩ | ⟨hpc, hinv⟩
  · refine fin N ?_ st hpc hfr
    rw [← climbTo_size, h0]
    rfl
  · obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    exact Eventually.bind (loop_spec hp hhp hpre hinv) fun st ⟨hpc, hfr⟩ ↦ fin _ rfl st hpc hfr

end

end NativeRustcVmArm.Sumcheck.Climb
