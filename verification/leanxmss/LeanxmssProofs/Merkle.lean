import LeanxmssProofs.Hash

/-!
# The Merkle path

The guest's `merkle_root`, 32 unrolled `merkle_node`s on one template, is the specification's `computeRoot`.
-/

open Aeneas Aeneas.Std Result WP
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Proofs

open Bytes

/-- `merkle_root` folds a leaf up its path as the specification's `computeRoot` does, the leaf index's bits choosing
each node's side. -/
theorem merkle_root_spec (pp : Std.Array U64 2#usize) (leaf : Std.U32) (l : Std.Array U64 2#usize)
    (path : Std.Array (Std.Array U64 2#usize) 32#usize) :
    ∃ r, leanxmss.merkle_root pp leaf l path = ok r ∧
      Statement.digest r = computeRoot (Statement.digest pp) (u32 leaf)
        (Vector.ofFn fun i => Statement.digest (path.val.getD i.val default)) (Statement.digest l) := by
  sorry

end leanxmss.Proofs
