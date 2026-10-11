module
public import WhirAeneas.Generated.Merkle.Types
public import WhirAeneas.Std.Guards
public import WhirAeneas.Std.Merkle
public import WhirAeneas.Std.Replay
public import Mathlib.Data.Finset.Sort
@[expose] public section
open Aeneas Aeneas.Std Result

namespace MerkleSource

/-- `pcs::merkle::sorted_unique`: the queries with duplicates removed, ascending. Its body
    (`to_vec`, `sort_unstable`, `dedup`) is outside the backend's library; on `usize` an unstable
    sort followed by removing adjacent duplicates is the ascending list of the distinct values. -/
def merkle.sorted_unique (queries : Slice Std.Usize) : Result (alloc.vec.Vec Std.Usize) :=
  let l : List Std.Usize := ((queries.val.map (·.val)).toFinset.sort (· ≤ ·)).map
    fun n => ⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩
  .ok (.from l (by
    have h1 : l.length ≤ queries.val.length := by
      simp only [l, List.length_map, Finset.length_sort]
      exact (List.toFinset_card_le _).trans (by simp)
    have := queries.property
    omega))

/-- `pcs::merkle::hash_pairs`, the batched pair hash: the hash boundary, with no body here. Its
    content contract is `WhirAeneas.Merkle.PairHash`. -/
opaque merkle.hash_pairs :
    Slice (Array (Array Std.U8 32#usize) 2#usize) → alloc.vec.Vec (Array Std.U8 32#usize) →
      Result (alloc.vec.Vec (Array Std.U8 32#usize))

/-- `pcs::merkle::hash_rows`, the batched leaf hash: the hash boundary, with no body here. Its
    content contract is `WhirAeneas.Merkle.RowHash`. -/
opaque merkle.hash_rows :
    Slice primitives.field.gf2_64.F64 → Std.Usize → Std.Usize → Std.Usize →
      Result (alloc.vec.Vec (Array Std.U8 32#usize))

end MerkleSource
