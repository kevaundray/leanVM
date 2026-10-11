import WhirAeneas.Merkle
import Lean.Util.CollectAxioms

/-! Axiom audit of the Merkle opening extraction and its proofs. Separate from the other audits
because the generated namespaces declare the same top-level instance names. -/

#print axioms MerkleSource.merkle.PrunedMerklePaths.from_hint
#print axioms MerkleSource.merkle.PrunedMerklePaths.open
#print axioms WhirAeneas.Merkle.from_hint_some
#print axioms WhirAeneas.Merkle.from_hint_none
#print axioms WhirAeneas.Merkle.pair_level_loop_eq
#print axioms WhirAeneas.Merkle.rebuild_eq
#print axioms WhirAeneas.Merkle.position_loop_eq
#print axioms WhirAeneas.Merkle.node_position_loop_eq

open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (declarationName, declarationInfo) in environment.constants.toList do
    if (`WhirAeneas.Merkle).isPrefixOf declarationName || (`MerkleSource).isPrefixOf declarationName then
      match declarationInfo with
      | .thmInfo _ =>
        let axioms ← collectAxioms declarationName
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unexpected axiom in {declarationName}: {axiomName}"
        count := count + 1
      | .axiomInfo _ => throwError "project declares an axiom: {declarationName}"
      | .defnInfo _ =>
        let axioms ← collectAxioms declarationName
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unexpected axiom in {declarationName}: {axiomName}"
      | _ => pure ()
  unless count > 0 do
    throwError "no Merkle theorems audited"
  logInfo m!"Audited {count} Merkle theorems; only propext, Classical.choice and Quot.sound permitted."
