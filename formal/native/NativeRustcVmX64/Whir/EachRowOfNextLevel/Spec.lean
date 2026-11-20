module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.IterH

/-!
# `each_row` with `next_level`'s closure meets its contract (x86-64)

`eachRowNext_spec`: placed anywhere in the program, given its callees' contracts
(`subspace_table`, `memcpy`, `Rows::row`, `lanes_of`, `fold_row`, `subspace_at_table`,
`novel_eval`, `kmul`, `EW::mul`), from its entry in a state satisfying `EachRowNextPre rows op` it
returns `1` in AL with the batched value `batchedOf …` at `&mut batched`, memory changed in its
stack and the batched value only, the callee-saved registers and RSP restored
(`EachRowNextPost rows`). The run: the table and its copy (`entry_a`), into the loop
(`start_step`), the loop by induction on the rows left (`iter_a` to `iter_h`, `b8_step`), the
exits.
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeVm.Model NativeRustcVmX64.Vm.EachRowOfNextLevel

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
  have c := ctx hpre
  rw [show label eachRowNextLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  have loop : ∀ n j m, rows.size - j = n → Inv rows m0 j m →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + 82)⟩ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j m hn h
      exact iter_a hp c h fun m1 h1 ↦ iter_b hp hrow hlanes c h1 fun m2 h2 ↦
        iter_c hp hfold hsat c h2 fun m3 h3 ↦ iter_d hp hnov c h3 fun m4 h4 ↦
          iter_e hp hkmul c h4 fun m5 h5 ↦ iter_h hp hmul c h5 fun m6 h6 ↦
            ih (rows.size - (j + 1)) (by have := h.hj; omega) (j + 1) m6 rfl h6
  exact entry_a hp htab hmemcpy c fun m h3 ↦
    start_step hp c h3 fun m' h0 ↦ loop _ 0 m' rfl h0

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
