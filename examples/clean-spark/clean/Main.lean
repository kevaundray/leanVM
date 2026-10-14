module

public import Clean.Circuit
public import Clean.Backends.Circom.R1CS
public import Clean.Specs.Poseidon
public import Clean.Utils.Tactics.CircuitProofStart

@[expose] public section

namespace CleanSpark

abbrev Scalar := Specs.Poseidon.F

-- Witness IR supplies the value; the assertion, not the witness generator,
-- enforces the relation against an arbitrary prover's assignment.
def circuit : FormalCircuit Scalar field field where
  main x := do
    let y ← witness (.expr (x * x + x + 5))
    y === x * x + x + 5
    return y
  Spec x y := y = x * x + x + 5
  soundness := by circuit_proof_all
  completeness := by circuit_proof_all

-- Clean variable 0 is x; the single witness (variable 1) is output y.
-- The exporter moves y to signal 1, x to signal 2, and creates any
-- product intermediates after them. Signal 0 is the constant one.
def operations : List (Operation Scalar) :=
  (circuit.main (varFromOffset field 0)).operations 1

-- All three artifacts use exactly the same operations, public mapping,
-- scalar modulus, and four-limb field representation.
def artifacts : Except String (String × ByteArray × ByteArray) := do
  let prime := Specs.Poseidon.BN254_PRIME
  let ops := operations
  let json ← Backends.Circom.compileR1CS prime 1 ["x"] [1] ops 4
  let r1cs ← Backends.Circom.compileR1CSBin prime 1 ["x"] [1] ops 4
  let wasm ← Backends.Circom.compileModule prime 1 ["x"] [1] ops 4
  return (json, r1cs, wasm)

end CleanSpark

def main (args : List String) : IO Unit := do
  let [directory] := args
    | throw <| IO.userError "usage: clean_export <output-directory>"
  let (json, r1cs, wasm) ← match CleanSpark.artifacts with
    | .ok result => pure result
    | .error message => throw <| IO.userError s!"Clean export failed: {message}"
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "circuit.json") json
  IO.FS.writeBinFile (output / "circuit.r1cs") r1cs
  IO.FS.writeBinFile (output / "circuit.wasm") wasm
  IO.println s!"Exported Clean circuit to {output}"
