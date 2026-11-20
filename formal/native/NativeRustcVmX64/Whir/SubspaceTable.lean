module

public import NativeRustcVmX64.Whir.SubspaceTable.Start
public import NativeRustcVmX64.Whir.SubspaceTable.Finish

/-!
# `subspace_table` on x86-64

**`subspaceTable_spec`**: `SubspaceTable.entry` (the prologue, `memset` of the layer, `μ < 32`,
the layer's first `μ` words `2^(i+1)`) or, `μ ≥ 32`, tag `0` (`SubspaceTable.big`);
`SubspaceTable.first` pushes `(1, kinv 1)`; the turns (`turn`, by `Sym.loop`: `head`, the layer
loop of `inner`s, `push`) square and shift the layer by the last root and push the next root with
its inverse, until the table is done (`finish_done`: tag `1`, the table's `Buf` copied out) or
would get a 32nd root (`finish_none`, `μ = 31`: tag `0`). The table is `subspaceTable μ`
(`NativeRustcVm.Whir.subspaceTable_toList`).
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir

public section

variable [Host] {k : Nat}

/-- **Turn `t`**: from the turns' head, the next head, the copy or `None`. -/
theorem turn (hp : Placed code k) (hkmul : Spec (Labels.label kmulLabel) KmulPre KmulPost)
    (hkinv : Spec (Labels.label kinvLabel) KinvPre KinvPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) {t : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + 160)) (hO : OInv m0 t st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + 160) ∧ OInv m0 (t + 1) s.data) ∨
      (s.pc = Host.addrOf (k + 203) ∧ Done m0 s.data) ∨
      (s.pc = Host.addrOf (k + 212) ∧ NoneAt m0 s.data)) st := by
  refine (head hp hpre hpc hO).bind fun s ⟨hpc1, hI1⟩ ↦ ?_
  have hloop := Sym.loop (tr := step1 Host.exe)
    (Q := fun s ↦ s.pc = Host.addrOf (k + 185) ∧ PInv m0 t s.data)
    (fun n s ↦ ∃ j, n = muOf m0 - t - j ∧ s.pc = Host.addrOf (k + 171) ∧ IInv m0 t j s.data)
    (fun n s ⟨j, hn, hpc, hI⟩ ↦ by
      have := hI.ht
      refine (inner hp hkmul hpre hpc hI).mono fun s' h ↦ ?_
      rcases h with ⟨hpc', hI'⟩ | h
      · exact .inr ⟨_, by omega, j + 1, rfl, hpc', hI'⟩
      · exact .inl h) (n := muOf m0 - t - 0) ⟨0, rfl, hpc1, hI1⟩
  exact hloop.bind fun s ⟨hpc2, hP⟩ ↦ push hp hkinv hpre hpc2 hP

/-- **The turns**, from `OInv 0`. -/
theorem turns (hp : Placed code k) (hkmul : Spec (Labels.label kmulLabel) KmulPre KmulPost)
    (hkinv : Spec (Labels.label kinvLabel) KinvPre KinvPost)
    (hmemcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + 160)) (hO : OInv m0 0 st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hloop := Sym.loop (tr := step1 Host.exe)
    (Q := fun s ↦ (s.pc = Host.addrOf (k + 203) ∧ Done m0 s.data) ∨
      (s.pc = Host.addrOf (k + 212) ∧ NoneAt m0 s.data))
    (fun n s ↦ ∃ t, n = muOf m0 - t ∧ s.pc = Host.addrOf (k + 160) ∧ OInv m0 t s.data)
    (fun n s ⟨t, hn, hpc, hO⟩ ↦ by
      have := hO.ht
      refine (turn hp hkmul hkinv hpre hpc hO).mono fun s' h ↦ ?_
      rcases h with ⟨hpc', hO'⟩ | h
      · exact .inr ⟨_, by omega, t + 1, rfl, hpc', hO'⟩
      · exact .inl h) (n := muOf m0 - 0) ⟨0, rfl, hpc, hO⟩
  refine hloop.bind fun s h ↦ ?_
  rcases h with ⟨hpc', hD⟩ | ⟨hpc', hN⟩
  · exact finish_done hp hmemcpy hpre hpc' hD
  · exact finish_none hp hpre hpc' hN

/-- **`subspace_table` meets its contract.** -/
theorem subspaceTable_spec (hp : Placed code k)
    (hkmul : Spec (Labels.label kmulLabel) KmulPre KmulPost)
    (hkinv : Spec (Labels.label kinvLabel) KinvPre KinvPost)
    (hmemset : Spec (Labels.label "memset") MemsetPre MemsetPost)
    (hmemcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost) :
    Spec (Labels.label subspaceTableLabel) SubspaceTablePre SubspaceTablePost := by
  intro m0 hpre
  rw [show Labels.label subspaceTableLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  refine (entry hp hmemset hpre).bind fun s h ↦ ?_
  rcases h with ⟨hpc, hfr, hw, hbig⟩ | ⟨hpc, hI⟩
  · exact big hp hpre hpc hfr hw hbig
  refine (first hp hkinv hpre hpc hI).bind fun s h ↦ ?_
  rcases h with ⟨hpc', hO⟩ | ⟨hpc', hD⟩
  · exact turns hp hkmul hkinv hmemcpy hpre hpc' hO
  · exact finish_done hp hmemcpy hpre hpc' hD

end

end NativeRustcVmX64.Whir.SubspaceTable
