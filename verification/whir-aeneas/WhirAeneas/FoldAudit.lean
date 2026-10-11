import WhirAeneas.Fold
import Lean.Util.CollectAxioms

/-! Axiom audit of the fold extraction. It is separate from the other audits because the
generated namespaces declare the same top-level instance names. -/

#print axioms FoldSource.whir.verify.Quad.eval
#print axioms FoldSource.whir.verify.Quad.fold
#print axioms FoldSource.ring_switch.RingMap.close
#print axioms FoldSource.whir.verify.OodCtx.term
#print axioms FoldSource.whir.verify.basis_product
#print axioms WhirAeneas.Fold.quad_eval
#print axioms WhirAeneas.Fold.quad_fold
#print axioms WhirAeneas.Fold.close_eq
#print axioms WhirAeneas.Fold.term_eq
#print axioms WhirAeneas.Fold.basis_product_eq

open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (declarationName, declarationInfo) in environment.constants.toList do
    if (`WhirAeneas.Fold).isPrefixOf declarationName ||
        (`FoldSource).isPrefixOf declarationName then
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
    throwError "no fold theorems audited"
  logInfo m!"Audited {count} fold theorems; only propext, Classical.choice and Quot.sound permitted."
