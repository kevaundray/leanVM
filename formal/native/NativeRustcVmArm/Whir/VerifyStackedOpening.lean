module

public import NativeRustcVmArm.Whir.VerifyStackedOpening.B34

/-!
# `verify_stacked_opening` on AArch64

**`verifyStackedOpening_spec`**: X0 becomes `verifyStackedOpening`'s `Some`/`None` over the stack
claims (the ring-switched claim, the placed column claims, the out-of-domain claim), the `TState`
its next state, memory changed in the `WhirW`, the scales, the `TState` and the stack only, given
`SpongeW::squeeze`'s, `powers`', `EW::mul`'s, `ladder`'s, `memcpy`'s and `whir_levels`' contracts.
The run: the prologue and the count of the placed claims (`entry_step`, `count_run`), the
batching challenge (`sample_b5`, `sample_b9`), the scales (`powers_b11`), the batched target term
by term (`first_b15`, `tgt_run`, `tail_b26`), the ladder (`ladder_b30`), the levels' copy
(`copy_b32`), WHIR's fresh state (`b34_step`), `whir_levels` and the return (`call_whir`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmArm.Vm.VerifyStackedOpening

public section

variable [Host] {k : Nat}

/-- **`verify_stacked_opening`'s contract.** -/
theorem verifyStackedOpening_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (label squeezeLabel) (SqueezePre sp) (SqueezePost sp))
    (hpow : Spec (label powersLabel) PowersPre PowersPost)
    (hmul : Spec (label ewMulLabel) EWMulPre EWMulPost)
    (hlad : Spec (label ladderLabel) LadderPre LadderPost)
    (hmemcpy : Spec (label "memcpy") MemcpyPre MemcpyPost)
    (hwl : ∀ a s levels ba b claim, Spec (label whirLevelsLabel)
      (WhirLevelsPre a s levels ba b claim) (WhirLevelsPost a s levels b claim)) :
    ∀ a s layout target coefficients point slices cs z value,
      Spec (label verifyStackedOpeningLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value) := by
  intro a s layout target coefficients point slices cs z value m0 hpre
  have h := parts hpre
  rw [show Labels.label verifyStackedOpeningLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  have after26 : ∀ st, AtB26 a s layout target cs value m0 st →
      Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0)
        ⟨st, Host.addrOf (k + 116)⟩ := fun st hb ↦
    tail_b26 hp h hmul (fun st hb ↦ ladder_b30 hp h hlad (fun st _ hb ↦ copy_b32 hp h hmemcpy
      (fun st hb ↦ b34_step hp h (fun st hc hpc ↦ call_whir hp h hwl hc hpc) hb) hb) hb) hb
  have after11 : ∀ st, AtB11 a s layout cs m0 st →
      Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0)
        ⟨st, Host.addrOf (k + 60)⟩ := fun st hb ↦
    powers_b11 hp h hpow (fun st hb ↦ first_b15 hp h hmul
      (fun st ht ↦ tgt_run hp h hmul after26 _ 0 st rfl ht) after26 hb) hb
  exact entry_step hp h (fun st hb hz ↦ sample_b9 hp h hsq after11 hb hz)
    fun st hc ↦ count_run hp h (fun st' h5 ↦ sample_b5 hp h hsq after11 h5) _ 0 st rfl hc

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
