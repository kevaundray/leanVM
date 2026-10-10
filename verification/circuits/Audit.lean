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

#print axioms LeanVMCircuits.Shift.assumptions_iff_legal_flags
#print axioms LeanVMCircuits.Flock.Shift.supported
#print axioms LeanVMCircuits.Flock.Shift.source_eq
#print axioms LeanVMCircuits.Flock.Shift.layout
#print axioms LeanVMCircuits.Flock.Shift.soundness
#print axioms LeanVMCircuits.Flock.Shift.wellFormed
#print axioms LeanVMCircuits.Flock.Shift.complete

#print axioms LeanVMCircuits.Gates.lower_correct
#print axioms LeanVMCircuits.Gates.lower_append
#print axioms LeanVMCircuits.Gates.lower_wellFormed
#print axioms LeanVMCircuits.Gates.witness_exists
#print axioms LeanVMCircuits.Gates.lowerCircuit_soundness
#print axioms LeanVMCircuits.Gates.lowerCircuit_completeness
#print axioms LeanVMCircuits.Blake2s.Rfc7693.abc
#print axioms LeanVMCircuits.Blake2s.program_correct
#print axioms LeanVMCircuits.Blake2s.program_valid
#print axioms LeanVMCircuits.Blake2s.Compress.soundness
#print axioms LeanVMCircuits.Blake2s.Compress.completeness
#print axioms LeanVMCircuits.Blake2s.Compress.lowered
#print axioms LeanVMCircuits.Blake2s.Export.soundness
#print axioms LeanVMCircuits.Blake2s.Export.completeness
#print axioms LeanVMCircuits.Blake2s.Export.adder31_source
#print axioms LeanVMCircuits.Blake2s.Export.adder31_soundness
#print axioms LeanVMCircuits.Blake2s.Export.adder31_layout
#print axioms LeanVMCircuits.Blake2s.Export.adder31_wellFormed
#print axioms LeanVMCircuits.Blake2s.Export.adder31_complete
#print axioms LeanVMCircuits.Blake2s.Export.adder32_canonical
#print axioms LeanVMCircuits.Blake2s.Export.adder31_canonical
#print axioms LeanVMCircuits.Blake2s.Export.adder32_call
#print axioms LeanVMCircuits.Blake2s.Export.adder31_call

#print axioms LeanVMCircuits.Rec.modulus_irreducible
#print axioms LeanVMCircuits.Rec.chain_squares
#print axioms LeanVMCircuits.Rec.cofactor_mul
#print axioms LeanVMCircuits.Rec.root_pow_two_pow_64
#print axioms LeanVMCircuits.Rec.root_pow_two_pow_32_sub_unit
#print axioms LeanVMCircuits.Rec.ev_mul
#print axioms LeanVMCircuits.Rec.toWord_ofWord
#print axioms LeanVMCircuits.Rec.toWord_injective
#print axioms LeanVMCircuits.Rec.toE_mul
#print axioms LeanVMCircuits.Rec.toE_add
#print axioms LeanVMCircuits.Rec.toE_smul
#print axioms LeanVMCircuits.Rec.toE_injective
#print axioms LeanVMCircuits.Rec.Form.eval_expr
#print axioms LeanVMCircuits.Rec.emul_spec
#print axioms LeanVMCircuits.Rec.exk_spec
#print axioms LeanVMCircuits.Rec.boolean_spec
#print axioms LeanVMCircuits.Rec.hash_mux
#print axioms LeanVMCircuits.Rec.split_spec
#print axioms LeanVMCircuits.Rec.Identity.eval_expr
#print axioms LeanVMCircuits.Rec.identities

#print axioms LeanVMCircuits.Rec.inverse_row
#print axioms LeanVMCircuits.Rec.add_row
#print axioms LeanVMCircuits.Rec.pack_row
#print axioms LeanVMCircuits.Rec.cast_views
#print axioms LeanVMCircuits.Rec.hash_outputs
#print axioms LeanVMCircuits.Rec.node_row

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
    ``LeanVMCircuits.Shift.assumptions_iff_legal_flags,
    ``LeanVMCircuits.Flock.Shift.supported, ``LeanVMCircuits.Flock.Shift.source_eq,
    ``LeanVMCircuits.Flock.Shift.layout, ``LeanVMCircuits.Flock.Shift.soundness,
    ``LeanVMCircuits.Flock.Shift.wellFormed, ``LeanVMCircuits.Flock.Shift.complete,
    ``LeanVMCircuits.Flock.lookup_rejected, ``LeanVMCircuits.Flock.interaction_rejected,
    ``LeanVMCircuits.Gates.lower_correct, ``LeanVMCircuits.Gates.lower_append,
    ``LeanVMCircuits.Gates.lower_wellFormed, ``LeanVMCircuits.Gates.witness_exists,
    ``LeanVMCircuits.Gates.lowerCircuit_soundness, ``LeanVMCircuits.Gates.lowerCircuit_completeness,
    ``LeanVMCircuits.Blake2s.Rfc7693.abc, ``LeanVMCircuits.Blake2s.program_correct,
    ``LeanVMCircuits.Blake2s.program_valid, ``LeanVMCircuits.Blake2s.Compress.soundness,
    ``LeanVMCircuits.Blake2s.Compress.completeness, ``LeanVMCircuits.Blake2s.Compress.lowered,
    ``LeanVMCircuits.Blake2s.Export.soundness, ``LeanVMCircuits.Blake2s.Export.completeness,
    ``LeanVMCircuits.Blake2s.Export.adder31_source, ``LeanVMCircuits.Blake2s.Export.adder31_soundness,
    ``LeanVMCircuits.Blake2s.Export.adder31_layout, ``LeanVMCircuits.Blake2s.Export.adder31_wellFormed,
    ``LeanVMCircuits.Blake2s.Export.adder31_complete, ``LeanVMCircuits.Blake2s.Export.adder32_canonical,
    ``LeanVMCircuits.Blake2s.Export.adder31_canonical, ``LeanVMCircuits.Blake2s.Export.adder32_call,
    ``LeanVMCircuits.Blake2s.Export.adder31_call,    ``LeanVMCircuits.Rec.modulus_irreducible, ``LeanVMCircuits.Rec.chain_squares,
    ``LeanVMCircuits.Rec.cofactor_mul, ``LeanVMCircuits.Rec.root_pow_two_pow_64,
    ``LeanVMCircuits.Rec.root_pow_two_pow_32_sub_unit, ``LeanVMCircuits.Rec.ev_mul,
    ``LeanVMCircuits.Rec.toWord_ofWord, ``LeanVMCircuits.Rec.toWord_injective,
    ``LeanVMCircuits.Rec.toE_mul, ``LeanVMCircuits.Rec.toE_add,
    ``LeanVMCircuits.Rec.toE_smul, ``LeanVMCircuits.Rec.toE_injective,
    ``LeanVMCircuits.Rec.Form.eval_expr, ``LeanVMCircuits.Rec.emul_spec,
    ``LeanVMCircuits.Rec.exk_spec, ``LeanVMCircuits.Rec.boolean_spec,
    ``LeanVMCircuits.Rec.hash_mux, ``LeanVMCircuits.Rec.split_spec,
    ``LeanVMCircuits.Rec.Identity.eval_expr, ``LeanVMCircuits.Rec.identities,
    ``LeanVMCircuits.Rec.inverse_row, ``LeanVMCircuits.Rec.add_row,
    ``LeanVMCircuits.Rec.pack_row, ``LeanVMCircuits.Rec.cast_views,
    ``LeanVMCircuits.Rec.hash_outputs, ``LeanVMCircuits.Rec.node_row] do
    let axioms ← collectAxioms theoremName
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{theoremName} depends on unexpected axiom {axiomName}"
