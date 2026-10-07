import LeanxmssProofs.Hash

/-!
# Chains and the one-time public key's leaf

The guest walks each chain from its digit to its end with `Chains::walk`, inside `wots_leaf`'s hash of the ends: the
leaf is the specification's `otsLeaf` of `otsRecover`.
-/

open Aeneas Aeneas.Std Result WP
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Proofs

open Bytes

/-- `verify`'s leaf, from the chains `Chains::new` makes and digits that are the specification's `x`, is the
specification's leaf of the public values `otsRecover` walks to from the signature's chain tips. -/
theorem wots_leaf_spec (pp : Std.Array U64 2#usize) (leaf : Std.U32) (sig : leanxmss.Signature)
    (d : leanxmss.Digits) (x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V)
    (hd : ∀ i : Std.Usize, (hi : i.val < Constants.V) → ∃ v, leanxmss.Digits.get d i = ok v ∧ v.val = (x[i.val]'hi).val) :
    ∃ chains, leanxmss.Chains.new pp leaf = ok chains ∧
      ∃ l, leanxmss.wots_leaf leanxmss.verify.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642 pp leaf
          (chains, d, sig) = ok l ∧
        Statement.digest l = otsLeaf (Statement.digest pp) (u32 leaf)
          (otsRecover (Statement.digest pp) (u32 leaf) (Statement.signature sig).chainElements x) := by
  sorry

end leanxmss.Proofs
