module

public import NativeRustcVmArm.Whir.FinalLevel.Glued
public import NativeRustcVmArm.Whir.FinalLevel.Rows
public import NativeRustcVmArm.Whir.FinalLevel.Sum

/-!
# `final_level` on AArch64

**`finalLevel_spec`**: X0 becomes `finalLevelM`'s `Some`/`None`, the `TState` at X0 its next state,
given its callees' contracts. The prologue reads the folded lane (`entry`); `grind` and
`sample_queries` (`queries`); `query_openings` and `each_row` (`rows`); `sumcheck_plain` (`sum`);
the point (`point`); the rotated point and `BasisW::eval` (`rotate`); the glued claims
(`glued`); `multilinear_eval`, the product and the end check (`finish`). Each `None` returns `0`.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmArm.Vm.FinalLevel

public section

variable [Host] {k : Nat}

/-- **`final_level`'s contract.** -/
theorem finalLevel_spec (hp : Placed code k)
    (hrsc : ∀ a s, Spec (Labels.label readScalarsLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    (hgr : ∀ a s, Spec (Labels.label grindLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ a s, Spec (Labels.label sampleQueriesLabel) (SampleQueriesPre a s)
      (SampleQueriesPost a s))
    (hqo : ∀ a s Q, Spec (Labels.label queryOpeningsLabel) (QueryOpeningsPre a s Q)
      (QueryOpeningsPost a s Q))
    (hrow : ∀ rows op, Spec (Labels.label eachRowFinalLabel) (EachRowFinalPre rows op)
      (EachRowFinalPost rows))
    (hsc : ∀ a s, Spec (Labels.label sumcheckPlainLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hext : Spec (Labels.label bufEW30ExtendLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hbw : ∀ ba b, Spec (Labels.label basisWEvalLabel) (BasisWEvalPre ba b) (BasisWEvalPost b))
    (hge : ∀ g, Spec (Labels.label gluedEvalLabel) (GluedEvalPre g) (GluedEvalPost g))
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost)
    (hmle : Spec (Labels.label mleOfMultilinearEvalLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost) :
    ∀ a s level ba b w rounds, Spec (label finalLevelLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds) := by
  intro a s level ba b w rounds m0 h
  have c := Ctx.of_pre h
  rw [show Labels.label finalLevelLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  exact entry hp c hrsc fun _ _ _ hpc hb h22 h24 h26 h23 h25 hsz hfd hts hrun ↦
    queries hp c hgr hsq hpc ⟨hb, h22, h24, h23, hsz, hfd⟩ h26 h25 hts hrun
      fun _ _ _ hpc hl h26 h29 hq hts hrun ↦
    rows hp c hqo hrow hpc hl h26 h29 hq hts hrun fun _ _ hpc hl hts hrun ↦
    sum hp c hsc hpc hl hts hrun fun _ _ _ _ hpc hc htn htl hcl hts hrun ↦
    point hp c hext hpc hc htn htl hcl hts fun _ hpc hc h22 h23 h24 htl hbuf hts ↦
    rotate hp c hext hbw hpc hc h22 h23 h24 htl hbuf hts
      fun _ hpc hc h22 h29 h23 h24 htl hpt hopt hts ↦
    glued hp c hge hmul hpc hc htn h22 h29 h23 h24 htl hpt hopt hts fun _ hpc hB h21 h23 ↦
    finish hp c hmul hmle hpc hB.fr hB.x19 hB.x20 h21 h23 hB.size hB.fold htn hB.tl hB.cl hB.ts
      hrun

end

end NativeRustcVmArm.Whir.FinalLevel
