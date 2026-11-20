module

public import NativeRustcVmArm.Whir.WhirLevels.Entry

/-!
# `whir_levels` on AArch64

**`whirLevels_spec`**: X0 becomes `whirLevels logN laneFolds b 0 levels`'s `Some`/`None`, the
`TState` its next state, given `fold_rounds`', `next_level`'s and `final_level`'s contracts.
rustc unrolled the loop over the levels (a ladder has `3` to `6`): the prologue keeps the arguments
in X19 to X28 (`Regs`); each level runs its fold rounds (`fold_stage`), computes `μ` (`w_stage`),
then either jumps to `final_level` after the epilogue (a tail call whose contract ends the
function, `final_stage`) or calls `next_level` (`next_stage`) and goes on to the next level; a
`None` returns `0` (`exit_none`). Model: `whirLevels_single`, `whirLevels_cons_cons`.
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmArm.Vm.WhirLevels

public section

variable [Host] {k : Nat}

/-- **`whir_levels`' contract.** -/
theorem whirLevels_spec (hp : Placed code k)
    (hfr : ∀ a s w, Spec (label foldRoundsLabel) (FoldRoundsPre a s w) (FoldRoundsPost a s w))
    (hnl : ∀ a s level w rounds, Spec (label nextLevelLabel)
      (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds))
    (hfl : ∀ a s level ba b w rounds, Spec (label finalLevelLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds))
    (a : DecArea) (s : TState) (levels : List LeanVM.Parameters.Whir.Level) (ba : BasisAddrs)
    (b : BasisW) (claim : EW) :
    Spec (label whirLevelsLabel) (WhirLevelsPre a s levels ba b claim)
      (WhirLevelsPost a s levels b claim) := by
  intro m0 h
  obtain ⟨rate, c⟩ := Ctx.of_pre h
  rw [show Labels.label whirLevelsLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  exact entry hp ⟨hfr, hnl, hfl⟩ c

end

end NativeRustcVmArm.Whir.WhirLevels
