import Whir.PCSBCSMerkleSourceRows

/-! Actual accepted Root0 transport rows agree with the executable full table,
in query occurrence order including duplicate queries. No ideal oracle is
passed to the runtime decoder; the table consists solely of frozen log data. -/
namespace Whir.PCSBCSMerkleSourceRows
open Concrete FiatShamirGame MerkleTransport MerkleTransport.Commitments
open MerkleQueryLogExtraction PCSBCSMerkleQueryLog PublicMerkleLog PublicMerkleBinding

theorem pruned_opened_table (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (root : Digest32) (proof : PrunedMerklePaths)
    (numLeaves occupied : Nat) (queries : List Nat) (output : List RawPath)
    (accepted : proof.open (hash C) root numLeaves queries occupied occupied = some output)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64) :
    List.Forall₂ (fun q p => (rawRoot0 log root numLeaves.log2 occupied)[q]! = p.leafData.toArray)
      queries output ∨ OpenPrimitiveBad C log root output := by
  have refined := open_refines (hash C) proof root numLeaves queries occupied occupied output accepted
  have conditions := ((open_spec (hash C) proof root numLeaves queries occupied occupied output).mp accepted).1
  rcases pruned_opened_rows C log auth root proof numLeaves occupied queries output accepted bounds with good | bad
  · left
    apply List.forall₂_of_length_eq_of_get refined.length_eq
    intro i hi ho
    obtain ⟨stored,hs,hw,hindex,hdata,hlen,hdepth,hroot⟩ := refined.get hi ho
    have hq := conditions.range (queries.get ⟨i,hi⟩) (List.get_mem _ _)
    have inside : queries.get ⟨i,hi⟩ < 2^numLeaves.log2 := by
      simpa only [conditions.power] using hq
    have tree := good (output.get ⟨i,ho⟩) (List.get_mem _ _)
    rw [hindex] at tree
    have table := fullRows_get occupied numLeaves.log2 (fromPublic log root numLeaves.log2)
      (queries.get ⟨i,hi⟩) inside
    simp only [Tree.row,tree,Option.getD_some,MerkleQueryLogExtraction.normalize,hlen,↓reduceIte] at table
    have bound : queries.get ⟨i,hi⟩ <
        (fullRows occupied numLeaves.log2 (fromPublic log root numLeaves.log2)).size := by
      simpa only [fullRows_size] using inside
    rw [Array.getElem?_eq_getElem bound] at table
    have result := Option.some.inj table
    rw [rawRoot0_eq_fullRows]
    simpa only [getElem!_pos
      (fullRows occupied numLeaves.log2 (fromPublic log root numLeaves.log2))
      (queries.get ⟨i,hi⟩) bound] using result
  · exact Or.inr bad

end Whir.PCSBCSMerkleSourceRows
