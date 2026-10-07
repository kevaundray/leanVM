import LeanxmssProofs.Hash

/-!
# The target-sum encoding

The guest's `encode` is the specification's `wotsEncode`: it rejects the same digests, and its digits are the
specification's.
-/

open Aeneas Aeneas.Std Result WP
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Proofs

open Bytes

/-- `encode` panics on no input, finds no encoding exactly where `wotsEncode` finds none, and otherwise gives digits
whose `Digits::get` is the specification's digit `i`, for each chain `i`. -/
theorem encode_spec (pp : Std.Array U64 2#usize) (leaf : Std.U32) (msg : Std.Array U64 4#usize)
    (rnd : Std.Array U64 3#usize) :
    match wotsEncode (Statement.digest pp) (Statement.message msg) (Statement.randomness rnd) (u32 leaf) with
    | none => leanxmss.encode pp leaf msg rnd = ok none
    | some x => ∃ d, leanxmss.encode pp leaf msg rnd = ok (some d) ∧
        ∀ i : Std.Usize, (hi : i.val < Constants.V) → ∃ v, leanxmss.Digits.get d i = ok v ∧ v.val = (x[i.val]'hi).val := by
  sorry

end leanxmss.Proofs
