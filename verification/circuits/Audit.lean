import LeanVMCircuits

#print axioms LeanVMCircuits.FullAdder.soundness
#print axioms LeanVMCircuits.FullAdder.completeness
#print axioms LeanVMCircuits.Flock.lowerAffine_correct
#print axioms LeanVMCircuits.Flock.lower_correct
#print axioms LeanVMCircuits.Flock.flatten_correct
#print axioms LeanVMCircuits.Flock.adder64_source
#print axioms LeanVMCircuits.Flock.adder64_layout
#print axioms LeanVMCircuits.Flock.adder64_soundness
#print axioms LeanVMCircuits.Flock.adder64_wellFormed
#print axioms LeanVMCircuits.Flock.adder64_complete
#print axioms LeanVMCircuits.Flock.lookup_rejected
#print axioms LeanVMCircuits.Flock.interaction_rejected

#print axioms LeanVMCircuits.Flock.adder32_source
#print axioms LeanVMCircuits.Flock.adder32_soundness
#print axioms LeanVMCircuits.Flock.adder32_layout
#print axioms LeanVMCircuits.Flock.adder32_wellFormed
#print axioms LeanVMCircuits.Flock.adder32_complete
#print axioms LeanVMCircuits.Flock.carryAdder64_source
#print axioms LeanVMCircuits.Flock.carryAdder64_soundness
#print axioms LeanVMCircuits.Flock.carryAdder64_layout
#print axioms LeanVMCircuits.Flock.carryAdder64_wellFormed
#print axioms LeanVMCircuits.Flock.carryAdder64_complete

open Lean Elab Command in
run_cmd do
  for theoremName in #[
    ``LeanVMCircuits.FullAdder.soundness, ``LeanVMCircuits.FullAdder.completeness,
    ``LeanVMCircuits.Flock.lowerAffine_correct, ``LeanVMCircuits.Flock.lower_correct,
    ``LeanVMCircuits.Flock.flatten_correct, ``LeanVMCircuits.Flock.adder64_source,
    ``LeanVMCircuits.Flock.adder64_layout, ``LeanVMCircuits.Flock.adder64_soundness,
    ``LeanVMCircuits.Flock.adder64_wellFormed, ``LeanVMCircuits.Flock.adder64_complete,
    ``LeanVMCircuits.Flock.adder32_source, ``LeanVMCircuits.Flock.adder32_soundness,
    ``LeanVMCircuits.Flock.adder32_layout, ``LeanVMCircuits.Flock.adder32_wellFormed,
    ``LeanVMCircuits.Flock.adder32_complete, ``LeanVMCircuits.Flock.carryAdder64_source,
    ``LeanVMCircuits.Flock.carryAdder64_soundness, ``LeanVMCircuits.Flock.carryAdder64_layout,
    ``LeanVMCircuits.Flock.carryAdder64_wellFormed, ``LeanVMCircuits.Flock.carryAdder64_complete,
    ``LeanVMCircuits.Flock.lookup_rejected, ``LeanVMCircuits.Flock.interaction_rejected] do
    let axioms ← collectAxioms theoremName
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{theoremName} depends on unexpected axiom {axiomName}"
