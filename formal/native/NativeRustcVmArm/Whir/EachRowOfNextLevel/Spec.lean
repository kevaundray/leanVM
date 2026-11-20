module

public import NativeRustcVmArm.Whir.EachRowOfNextLevel.IterA

/-!
# `each_row` with `next_level`'s closure meets its contract

`eachRowNext_spec`: placed anywhere in the program, given its callees' contracts
(`subspace_table`, `memcpy`, `Rows::row`, `lanes_of`, `fold_row`, `subspace_at_table`,
`novel_eval`, `kmul`, `EW::mul`), from its entry in a state satisfying `EachRowNextPre rows op` it
returns `1` with the batched value `batchedOf …` at `&mut batched`, memory changed in its stack and
the batched value only, the callee-saved registers and SP restored (`EachRowNextPost rows`). The
run: the table and its copy (`entry_a`), into the loop (`start_step`), the loop by induction on the
rows left (`iter_step`), the exit (`exit_step`).
-/

namespace NativeRustcVmArm.Whir.EachRowOfNextLevel

open NativeRustcArm NativeArm NativeVm.Model NativeRustcVmArm.Vm.EachRowOfNextLevel

public section

variable [Host] {k : Nat}

/-- **`each_row` with `next_level`'s closure meets its contract.** -/
theorem eachRowNext_spec (hp : Placed code k)
    (htab : Spec (label subspaceTableLabel) SubspaceTablePre SubspaceTablePost)
    (hmemcpy : Spec (label "memcpy") MemcpyPre MemcpyPost)
    (hlanes : Spec (label lanesOfLabel) LanesOfPre LanesOfPost)
    (hfold : Spec (label foldRowLabel) FoldRowPre FoldRowPost)
    (hsat : Spec (label subspaceAtTableLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hnov : Spec (label novelEvalLabel) NovelEvalPre NovelEvalPost)
    (hkmul : Spec (label kmulLabel) KmulPre KmulPost)
    (hmul : Spec (label ewMulLabel) EWMulPre EWMulPost)
    (rows : Array (Array UInt64)) (op : BitVec 64)
    (hrow : Spec (label rowsRowLabel) (RowsRowPre op rows) (RowsRowPost op rows)) :
    Spec (label eachRowNextLabel) (EachRowNextPre rows op) (EachRowNextPost rows) := by
  intro m0 hpre
  rw [show label eachRowNextLabel = Host.addrOf (k + 0) from hp.label rfl]
  have loop : ∀ n j m, rows.size - j = n → Inv rows m0 j m →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + 63)⟩ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j m hn h
      exact iter_step hp hrow hlanes hfold hsat hnov hkmul hmul hpre h fun m' h' ↦
        ih (rows.size - (j + 1)) (by have := h.hj; omega) (j + 1) m' rfl h'
  exact entry_a hp htab hmemcpy hpre fun m h3 ↦
    start_step hp hpre h3 fun m' h0 ↦ loop _ 0 m' rfl h0

end

end NativeRustcVmArm.Whir.EachRowOfNextLevel
