import LeanVMCircuits.Bus.TableFlushes

/-!
`lake exe checkflushes <dump>`: check that a dump of the instruction tables' flushes (the Rust test
`the_flushes_are_the_lean_model_s` writes one where `LEANVM_FLUSH_DUMP` names, and checks the committed
`crates/leanvm_core/src/tables/flushes.txt`) is, line for line, `LeanVMCircuits.Bus.ClassTable.dump`: every table's
columns, slots, clock port columns and symbolic push and pull tuples as the Lean model builds them.
-/

open LeanVMCircuits.Bus.ClassTable

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: checkflushes <dump>"
      return 2
  let lines := (← IO.FS.lines path).toList
  if lines == dump then
    IO.println s!"{path}: the {all.length} tables' flushes ({dump.length} lines) are the model's"
    return 0
  let i := ((lines.zip dump).findIdx? fun (a, b) => a != b).getD (min lines.length dump.length)
  IO.eprintln s!"{path}: line {i + 1} is `{lines.getD i "<end>"}`, the model's is `{dump.getD i "<end>"}`"
  return 1
