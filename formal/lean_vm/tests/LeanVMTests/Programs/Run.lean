import LeanVM.Core.Interp
import LeanVMTests.Programs.Basic
import LeanVMTests.Programs.Chain
import LeanVMTests.Programs.Vm

/-!
# The compiler's test programs, run

Every program of `LeanVMTests.Programs.Basic`, which the Rust prover proves and verifies on the
public input it declares, runs in the interpreter on its core IR with that public input and its
streams; changing the first public word makes every program that publishes one fail.
-/

open LeanVM.Parameters LeanVM.Core LeanVM.Core.Interp LeanVMTests.Programs

namespace LeanVMTests.Programs.Run

/-- `g^i ↦ i` below `2^14`, the interpreter's discrete logarithm. -/
def logs : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  let mut x : K := 1
  for i in List.range (2 ^ 14) do
    m := m.insert (keyOf x) i
    x := x * g
  return m

/-- Run `t`'s `main` on the public input `pi` and its streams. -/
def runTest (t : TestProgram) (pi : List E) : Except String Unit := do
  let fns ← t.elab
  let cfg : Cfg := {
    program := fns.map (·.1.core),
    initMem := fun a => if a == gpowK 0 then pi[0]? else if a == gpowK 1 then pi[1]? else none,
    dlog := fun a => logs[keyOf a]?,
    streams := t.streams }
  discard <| run cfg "main" []

def isOk {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/- The eighteen test programs, the fixture program at six step counts, the VM's thirty programs, `keccak_steps` at five
counts. -/
#guard Basic.all.length = 18 && Chain.all.length = 6 && Vm.all.length = 34

#guard Basic.all.all fun t => isOk (runTest t t.publicInput)

#guard (Basic.all.filter (·.name != "identities")).all fun t =>
  !isOk (runTest t [t.publicInput[0]! + 1, t.publicInput[1]!])

end LeanVMTests.Programs.Run
