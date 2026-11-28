/-
  LeanVM.Guest.Program.Checks

  The guest program against `Expand`: each listed function with the `Const` instances it reaches.
-/

import LeanVM.Guest.Program
import LeanVM.Guest.Program.Compare

/-!
# The guest program against `Expand`

`check` compares each entry of the program list (`LeanVM.Guest.Program.program`) with what `Expand` makes of the function's source (`Compare.sameProg`); `lake exe dsl-check` runs every check, compiled.
-/

namespace LeanVM.Guest.Program.Checks

open LeanVM.Dsl LeanVM.Guest.Program

/-- The program list, as `dsl-check` reads it. -/
def checks : List (String × List GFn) := program

/-- Whether the guest's function `n` elaborates to what `Expand` makes of its source. -/
def check (n : String) : Bool :=
  match checks.lookup n with
  | some fs => Compare.sameProg fs (Compare.expandedAll (Check.src n))
  | none => false

end LeanVM.Guest.Program.Checks
