import LeanVM.Dsl.Gen.Checks

/-!
# `dsl-check`: the translated guest against `Expand`, compiled

`lake exe dsl-check [NAME ...]` checks the translated guest against `Expand`, compiled: for each
function of `Checks.checks` (or those named), the elaboration of its translation and of the
instances it reaches against what `Expand` makes of its source (`Compare.sameProg`), printing the
first difference of each failure (`Compare.firstDiff`). Exits with `1` if any differs. It is the
check of the translated guest; nothing in the default `LeanVM` target runs it.
-/

open LeanVM.Dsl.Gen LeanVM.Dsl.Gen.Compare

def main (args : List String) : IO UInt32 := do
  let todo := Checks.checks.filter fun (n, _) => args.isEmpty || args.contains n
  let mut fails := 0
  for (n, fs) in todo do
    let t0 ← IO.monoMsNow
    let a := walk (elabAll fs)
    let b := walk (expandedAll (LeanVM.Dsl.Check.src n))
    let ok := a == b
    let t1 ← IO.monoMsNow
    IO.println s!"{if ok then "PASS" else "FAIL"} {n} ({a.length} functions, {t1 - t0} ms)"
    if !ok then
      fails := fails + 1
      IO.println ((firstDiff a b).getD "(no difference found)")
    (← IO.getStdout).flush
  IO.println s!"{todo.length - fails} of {todo.length} pass"
  return if fails == 0 then 0 else 1
