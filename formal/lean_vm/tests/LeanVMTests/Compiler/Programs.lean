import LeanVM.Compiler.Invariants
import LeanVMTests.Programs.Basic

/-!
# The back end on the compiler's test programs

Every test program (`LeanVMTests.Programs.Basic`) elaborates and compiles, and the back end's
invariants hold of its traced elaboration (`Compiler.invariants`); and the sizes of the compiled
programs are pinned. The exports `lake exe guest-backend export programs` writes are what the
Rust tests prove, and the whole guest is `lake exe guest-backend check`.
-/

open LeanVM.Guest LeanVM.Core LeanVM.Compiler LeanVM.Semantics LeanVMTests.Programs

namespace LeanVMTests.Compiler.Programs

/-- The back end's invariants hold of the traced elaboration. -/
def checksPass (t : TestProgram) : Bool :=
  match t.elab with
  | .ok fns =>
      match invariants (withConstTable (fns.map (·.1))) with
      | .ok checks => checks.all (·.2)
      | .error _ => false
  | .error _ => false

#guard Basic.all.all checksPass

/-- A compiled program's instructions, padded size and `main` frame. -/
def shape (t : TestProgram) : Option (Nat × Nat × Nat) :=
  match t.elab.bind fun fns => compileTraced (fns.map (·.1)) with
  | .ok a => some (a.code.size, a.size, a.mainFrame)
  | .error _ => none

#guard Basic.all.map shape ==
  [(65, 128, 26), (57, 64, 23), (41, 64, 13), (1047, 2048, 19), (47, 64, 11), (23, 32, 21),
   (14, 16, 15), (16, 32, 15), (10, 16, 9), (22, 32, 17), (40, 64, 11), (67, 128, 25),
   (132, 256, 31), (81, 128, 14), (67, 128, 23), (37, 64, 29), (53, 64, 19), (116, 128, 34)].map some

/-- The code of a test program. -/
def codeOf (name : String) : Option (List OffsetInstruction) :=
  (Basic.all.find? (·.name == name)).bind fun t =>
    match t.elab.bind fun fns => compileTraced (fns.map (·.1)) with
    | .ok a => some a.code.toList
    | .error _ => none

-- `identities` whole: a pooled constant, a range check, an assertion (its two values one cell),
-- the `XOR` of `x` with itself and the halt.
#guard codeOf "identities" == some [
  .set 2 4 0, .set 2 4 0, .deref 2 0 4 .cell, .mul 2 3 2, .deref 3 0 5 .cell,
  .xor 2 2 6, .set 6 0 0, .set 7 1 0, .set 8 32768 0, .jump 7 8 7]

end LeanVMTests.Compiler.Programs
