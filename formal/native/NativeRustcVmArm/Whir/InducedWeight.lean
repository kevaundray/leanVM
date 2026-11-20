module

public import NativeRustcVmArm.Whir.InducedWeight.Start

/-!
# `induced_weight`

`b0` saves the callee-saved registers in its 1200-byte frame and calls `subspace_table`; for
`μ > 30` it stores `None` (`entry_a`). Else it copies the table into the frame and spills the
arguments; with no query the sum is `0`, else the queries' loop (`outer_step`, `sum_step`, by
`Sym.loop`) sums, query by query, the weight times the product of the factors
`1 + (1 ⊕ What_i)·r_i` (`inner_step`); `finish` stores `Some` of the sum, which is `inducedWeight`
(`totOf_cnt`).
-/

namespace NativeRustcVmArm.Whir.InducedWeight

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.InducedWeight NativeVm.Model
open NativeRustcVm.Whir NativeArm

public section

variable [Host] {k : Nat}

/-- **`induced_weight`'s contract.** -/
theorem inducedWeight_spec (hp : Placed code k)
    (htab : Spec (label subspaceTableLabel) SubspaceTablePre SubspaceTablePost)
    (hmemcpy : Spec (label "memcpy") MemcpyPre MemcpyPost)
    (hsat : Spec (label subspaceAtTableLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hkmul : Spec (label kmulLabel) KmulPre KmulPost)
    (hmul : Spec (label ewMulLabel) EWMulPre EWMulPost) :
    Spec (label inducedWeightLabel) InducedWeightPre InducedWeightPost := by
  intro m0 hpre
  rw [show Labels.label inducedWeightLabel = Host.addrOf (k + 0) from hp.label rfl]
  refine entry_a hp htab hmemcpy hpre fun st hA ↦ start hp hpre hA fun st' hO ↦ ?_
  have hloop := Sym.loop (tr := step1 Host.exe)
    (Q := fun s ↦ Done m0 s.data ∧ s.pc = Host.addrOf (k + 93))
    (fun n s ↦ ∃ j, n = cntOf m0 - j ∧ s.pc = Host.addrOf (k + 53) ∧ OInv m0 j s.data)
    (fun n s ⟨j, hn', hpc, hI⟩ ↦ by
      obtain ⟨d, pc⟩ := s
      simp only at hpc
      subst hpc
      refine (outer_step hp hsat hkmul hmul hpre hI).bind fun s ⟨hA', hpc⟩ ↦ ?_
      obtain ⟨d', pc'⟩ := s
      simp only at hpc
      subst hpc
      refine (sum_step hp hpre hA').mono fun s' h ↦ ?_
      rcases h with ⟨hI', hpc'⟩ | h
      · exact .inr ⟨cntOf m0 - (j + 1), by have := hI'.hj; omega, j + 1, rfl, hpc', hI'⟩
      · exact .inl h)
    (n := cntOf m0) (s := ⟨st', Host.addrOf (k + 53)⟩) ⟨0, by omega, rfl, hO⟩
  refine hloop.bind fun s ⟨hD, hpc⟩ ↦ ?_
  obtain ⟨d, pc⟩ := s
  simp only at hpc
  subst hpc
  exact finish hp hpre hA.mu hD

end

end NativeRustcVmArm.Whir.InducedWeight
