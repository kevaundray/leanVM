module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Final

/-!
# `verify_stacked_opening` on x86-64

**`verifyStackedOpening_spec`**: AL becomes `verifyStackedOpening`'s `Some`/`None` over the stack
claims (the ring-switched claim, the placed column claims, the out-of-domain claim), the `TState`
its next state, memory changed in the `WhirW`, the scales, the `TState` and the stack only, given
`SpongeW::squeeze`'s, `powers`', `EW::mul`'s, `ladder`'s, `memcpy`'s and `whir_levels`'
contracts. The run: the prologue (`entry_b0`, `entry_step`), the count of the placed claims
(`count_loop`, `tail_b15`, `tail_b16`), the batching challenge (`sample_b20`, `sample_b3`), the
scales (`powers_b24`), the batched target term by term (`first_b25`, `tgt_run`, `ood_b38`), the
ladder (`ladder_b42`), the levels' copy (`copy_b44`), WHIR's fresh state (`whir_b48`),
`whir_levels` and the return (`call_whir`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.VerifyStackedOpening

public section

variable [Host] {k : Nat}

/-- **`verify_stacked_opening`'s contract.** -/
theorem verifyStackedOpening_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label squeezeLabel) (SqueezePre sp) (SqueezePost sp))
    (hpow : Spec (Labels.label powersLabel) PowersPre PowersPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost)
    (hlad : Spec (Labels.label ladderLabel) LadderPre LadderPost)
    (hmemcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hwl : ∀ a s levels ba b claim, Spec (Labels.label whirLevelsLabel)
      (WhirLevelsPre a s levels ba b claim) (WhirLevelsPost a s levels b claim)) :
    ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label verifyStackedOpeningLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value) := by
  intro a s layout target coefficients point slices cs z value m0 hpre
  have h := parts hpre
  rw [show Labels.label verifyStackedOpeningLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  have after38 : ∀ st : MachineState, st.pc = Host.addrOf (k + 173) →
      Acc a s layout target cs value m0 cs.size st.data →
      Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0) st :=
    fun st hpc hc ↦ ood_b38 h hp hmul hpc hc fun st hpc hA ↦
      ladder_b42 h hp hlad hpc hA fun _ st hpc hA ↦ copy_b44 h hp hmemcpy hpc hA fun st hpc hA ↦
        whir_b48 h hp hpc hA fun st hc hpc ↦ call_whir h hp hwl hc hpc
  have after24 : ∀ st : MachineState, st.pc = Host.addrOf (k + 104) →
      AtB24 a s layout cs m0 st.data →
      Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0) st :=
    fun st hpc hA ↦ powers_b24 h hp hpow hpc hA fun st hpc hA ↦
      first_b25 h hp hmul hpc hA (fun st hpc ht ↦ tgt_run h hp hmul after38 _ 0 st rfl hpc ht)
        after38
  exact entry_b0 h hp (fun st hpc hc hz ↦ sample_b3 h hp hsq hpc hc hz after24)
    fun st hpc hc hpos ↦ entry_step h hp hpc hc hpos
      (fun st hpc hA hodd ↦ tail_b16 h hp hpc hA hodd fun st hpc hA ↦
        sample_b20 h hp hsq hpc hA after24)
      fun st hpc hh ↦ count_loop h hp (fun st hpc hA ↦ tail_b15 h hp hpc hA fun st hpc hA ↦
        sample_b20 h hp hsq hpc hA after24) _ 0 st rfl hpc hh

end

/--
info: 'NativeRustcVmX64.Whir.VerifyStackedOpening.verifyStackedOpening_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms verifyStackedOpening_spec

end NativeRustcVmX64.Whir.VerifyStackedOpening
