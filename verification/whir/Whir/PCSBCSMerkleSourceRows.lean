import Whir.PCSBCSMerkleQueryLog
import Whir.MerkleQueryLogExtractionRowsAgreement
import Whir.WHIRPhysicalRows
import Whir.SupportedCandidateExtraction

/-! PR600 source-width boundary: authenticated initial leaves contain occupied
lanes, not the generic model's leading zero-prefix encoding to the max fold
width. The source decoder consumes literal raw compact rows and internally uses
lanes-1-l. The verifier first fold reverses once and pads separately. These two
orders are never conflated. The Lean codecs are checked; Rust codec/asm/source
refinement remains an explicit external interface, not a security axiom here. -/
namespace Whir.PCSBCSMerkleSourceRows
open Concrete FiatShamirGame MerkleTransport MerkleTransport.Commitments
open MerkleQueryLogExtraction PCSBCSMerkleQueryLog PublicMerkleLog PublicMerkleBinding

/-- Exact agreement with `compactBaseOracle` at ACTUAL leafWords=occupied.
No claim is made for the legacy padded leafWords=max-fold-width convention. -/
theorem rawRoot0_eq_compactBaseOracle (C : DuplexModeGame.PrimitiveOracle)
    (log : PublicLog) (auth : AuthenticLog C log) (clean : ¬ OutputCollision log)
    (root : Digest32) (height occupied : Nat) :
    rawRoot0 log root height occupied =
      WHIRPhysicalRows.compactBaseOracle (hash C)
        ⟨recordDomain (records log),[]⟩ root height (2^height) occupied occupied := by
  have full := fullRows_eq_empty_snapshot canonicalCodec (hash C) (records log)
    (records_authentic C log auth) (fun bad => clean (reconstructed_collision C log auth bad))
    root height occupied
  simpa only [rawRoot0_eq_fullRows,fromPublic,WHIRPhysicalRows.compactBaseOracle,
    WHIRPhysicalRows.compactBaseRow,Nat.sub_self,List.drop_zero,baseOracle] using full

/-- The compiled extractor prepares the exact raw FullRoot shape, independently
of availability. Shape-default rows do NOT authenticate absent leaves. -/
theorem prepared_source_shape (log : PublicLog) (root : Digest32) (height occupied rows : Nat)
    (count : rows = 2^height) :
    (rawRoot0 log root height occupied).size = rows ∧
    ∀ row ∈ (rawRoot0 log root height occupied).toList, row.size = occupied := by
  subst rows
  exact rawRoot0_shape log root height occupied

/-- A coefficient-ascending view agrees with the decoder's intrinsic raw-row
lane access. This theorem does not reverse the oracle supplied to the decoder. -/
theorem coefficient_lane (raw : Array (Array K)) (occupied index lane : Nat)
    (inside : index < raw.size) (shape : raw[index].size = occupied) (live : lane < occupied) :
    ((root0CoefficientOrder raw)[index]!)[lane]! =
      SupportedCandidateExtraction.recordLane occupied raw[index] lane := by
  rw [show (root0CoefficientOrder raw)[index]! = raw[index].reverse by
    simpa only [getElem!_pos (root0CoefficientOrder raw) index (by simpa [root0CoefficientOrder_size] using inside)]
      using root0CoefficientOrder_raw raw index inside]
  simp only [SupportedCandidateExtraction.recordLane,live,↓reduceIte]
  rw [getElem!_pos _ lane (by simpa [shape] using live),Array.getElem_reverse]
  have reverseInside : occupied-1-lane < raw[index].size := by rw [shape]; omega
  simp only [shape]
  rw [getElem!_pos (raw[index]) (occupied-1-lane) reverseInside]

/-- Actual accepted flat transport supplies the fixed-depth Root0 paths.
The only failure branch is the existing observed compression game event. -/
theorem pruned_opened_rows (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (root : Digest32) (proof : PrunedMerklePaths)
    (numLeaves occupied : Nat) (queries : List Nat) (output : List RawPath)
    (accepted : proof.open (hash C) root numLeaves queries occupied occupied = some output)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64) :
    (∀ p ∈ output, (fromPublic log root numLeaves.log2).get
      (addressAbove p.leafIndex numLeaves.log2 []) = some p.leafData) ∨
      OpenPrimitiveBad C log root output := by
  have refined := open_refines (hash C) proof root numLeaves queries occupied occupied output accepted
  apply opened_rows C log auth root numLeaves.log2 output
  · intro p hp
    obtain ⟨q,hq,row,hr,hw,hi,hd,hl,hdepth,hroot⟩ := forall₂_mem_right refined hp
    exact hdepth
  · intro p hp
    obtain ⟨q,hq,row,hr,hw,hi,hd,hl,hdepth,hroot⟩ := forall₂_mem_right refined hp
    exact hroot
  · exact bounds

end Whir.PCSBCSMerkleSourceRows
