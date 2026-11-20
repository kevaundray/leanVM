module

public import NativeRustcVmArm.Whir.NextLevel.Glue

/-!
# `next_level` on AArch64

**`nextLevel_spec`**: X0 becomes `nextLevelM`'s `Some`/`None`, the `TState` at X0 its next state,
the glued state at X6 (its rounds kept), given its callees' contracts. The prologue calls
`read_commitment` (`entry`); then `read_scalars` and `grind(t, 15)` (`head`), the out-of-domain
sample (`mid1`), `read_scalar` and `grind(t, 17)` (`mid2`), `sample_queries` and `squeeze`
(`qry`), the zeroing loop (`zero_loop`), `memcpy`, `powers` and `query_openings` (`ops`),
`each_row` (`rows`), `glue_level` and the epilogue (`glue`). Each `None` returns `0`.
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmArm.Vm.NextLevel

public section

variable [Host] {k : Nat}

/-- **`next_level`'s contract.** -/
theorem nextLevel_spec (hp : Placed code k)
    (her : ∀ rows op, Spec (Labels.label eachRowNextLabel) (EachRowNextPre rows op)
      (EachRowNextPost rows))
    (hgl : ∀ s, Spec (Labels.label glueLevelLabel) (GlueLevelPre s) (GlueLevelPost s))
    (hmc : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hpw : Spec (Labels.label powersLabel) PowersPre PowersPost)
    (hsqz : ∀ sp, Spec (Labels.label squeezeLabel) (SqueezePre sp) (SqueezePost sp))
    (hgr : ∀ a s, Spec (Labels.label grindLabel) (GrindPre a s) (GrindPost a s))
    (hqo : ∀ a s Q, Spec (Labels.label queryOpeningsLabel) (QueryOpeningsPre a s Q)
      (QueryOpeningsPost a s Q))
    (hrc : ∀ a s, Spec (Labels.label readCommitmentLabel) (ReadCommitmentPre a s)
      (ReadCommitmentPost a s))
    (hrs : ∀ a s, Spec (Labels.label readScalarLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hrss : ∀ a s, Spec (Labels.label readScalarsLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    (hsc : ∀ a s, Spec (Labels.label sampleChallengesLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hsq : ∀ a s, Spec (Labels.label sampleQueriesLabel) (SampleQueriesPre a s)
      (SampleQueriesPost a s)) :
    ∀ a s level w rounds, Spec (Labels.label nextLevelLabel) (NextLevelPre a s level w rounds)
      (NextLevelPost a s level w rounds) := by
  intro a s level w rounds m0 h
  rw [show Labels.label nextLevelLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  exact head hp h hrc hrss hgr fun _ _ _ hpc h7 hr3 ↦
    mid1 hp h hsc hpc h7 fun _ _ _ hf hR h21 h23 h26 hF hos hts hsc4 ↦
      mid2 hp h hrs hgr (hr3.trans (tail3_eq hsc4)) hf hR h21 h23 h26 hF h7.size hos hts
        fun _ _ _ hpc6 h13 hr6 ↦
        qry hp h hsq hsqz hpc6 h13 hr6 fun _ _ _ _ hpc8 h17 hr8 ↦
          Eventually.bind (zero_loop hp h (i := 0) (by decide) hpc8 h17) fun _ ⟨hpc9, h57⟩ ↦
            ops hp h hmc hpw hqo hpc9 h57 hr8 fun _ _ _ _ hpc10 h22 hr9 ↦
              rows hp h her hpc10 h22 fun _ hpc11 h24 ↦ glue hp h hgl hpc11 h24 hr9

end

end NativeRustcVmArm.Whir.NextLevel
