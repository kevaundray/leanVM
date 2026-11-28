/-
  LeanVM.Guest.Program.Compare

  The comparison of a translated function with what `Expand` makes of its source: both sides' core functions walked from the function through its callees, loop helpers named by that order, values numbered by first occurrence.
-/

import LeanVM.Dsl.Check
import LeanVM.Core.Interp
import Std.Data.HashSet

/-!
# Translated functions against `Expand`

A function `F` the guest's source defines, as `Expand` lowers it (`Expand.expandQueue` from `F`: its core function, its loop helpers, the `Const` instances it queues), against the elaboration of its translation and of the translations of the instances it reaches. Both lists are walked from `F` through the callees each holds, loop helpers renamed `__loop<k>` in the order the walk meets them, and every function renumbered (`Fn.renumber`: parameters first, then values in order of first occurrence). `sameProg` is their equality; `firstDiff` names the first function and line where they differ.
-/

namespace LeanVM.Guest.Program.Compare

open LeanVM.Core LeanVM.Dsl

/-- The callees of statements, in order. -/
partial def callees : List Core.Stmt → List String
  | [] => []
  | s :: ss => (match s with
      | .call f _ _ => [f]
      | .callIf _ f _ => [f]
      | .dispatch _ fs _ _ => fs
      | .ite _ z nz => callees z ++ callees nz
      | .match_ _ arms => arms.flatMap callees
      | _ => []) ++ callees ss

/-- Statements with their callees renamed. -/
partial def renameIn (g : String → String) : List Core.Stmt → List Core.Stmt
  | [] => []
  | s :: ss => (match s with
      | .call f a r => .call (g f) a r
      | .callIf x f a => .callIf x (g f) a
      | .dispatch x fs a r => .dispatch x (fs.map g) a r
      | .ite c z nz => .ite c (renameIn g z) (renameIn g nz)
      | .match_ x arms => .match_ x (arms.map (renameIn g))
      | s => s) :: renameIn g ss

/-- The functions of `fs` reached from the first, in order of first call, loop helpers named by that order, renumbered. -/
partial def walk (fs : List Core.Fn) : List Core.Fn := Id.run do
  let some root := fs.head? | return []
  let byName : Std.HashMap String Core.Fn := fs.foldl (fun m f => m.insert f.name f) {}
  let mut order : Array String := #[root.name]
  let mut seen : Std.HashSet String := ({} : Std.HashSet String).insert root.name
  let mut i := 0
  while i < order.size do
    if let some f := byName[order[i]!]? then
      for c in callees f.body do
        if !seen.contains c && byName.contains c then
          order := order.push c
          seen := seen.insert c
    i := i + 1
  let loops := order.filter (·.startsWith "__loop")
  let g := fun (n : String) => match loops.findIdx? (· == n) with
    | some k => s!"__loop{k}"
    | none => n
  return (order.toList.filterMap fun n => byName[n]?).map fun f =>
    Fn.renumber { f with name := g f.name, body := renameIn g f.body }

/-- Every core function the translations elaborate. -/
def elabAll (fs : List GFn) : List Core.Fn := fs.flatMap fun f => f.elab.map (·.1.core)

/-- The core functions `Expand` makes of `f` and queues, with room for every instance `main` reaches. -/
def expandedAll (f : Source.Func) : List Core.Fn :=
  match Expand.expandQueue LeanVM.Guest.Data.guest 100000 0 #[f] 0 #[] with
  | .ok a => a.toList.map (·.1.core)
  | .error _ => []

/-- The translation of a function against `Expand`'s functions for it. -/
def sameProg (fs : List GFn) (ex : List Core.Fn) : Bool := walk (elabAll fs) == walk ex

/-- Where two walked lists first differ: the function, and the first differing line of each side's text with the lines before it. -/
def firstDiff (a b : List Core.Fn) : Option String := Id.run do
  let na := a.map (·.name)
  let nb := b.map (·.name)
  for (fa, fb) in a.zip b do
    if fa == fb then continue
    let la := (Interp.showFn fa).splitOn "\n"
    let lb := (Interp.showFn fb).splitOn "\n"
    let mut k := 0
    while k < la.length && k < lb.length && la[k]! == lb[k]! do k := k + 1
    let ctx := fun (ls : List String) => "\n".intercalate ((ls.drop (k - 3)).take 4)
    return some s!"function {fa.name} / {fb.name}, line {k} of {la.length} / {lb.length}:\n-- translation:\n{ctx la}\n-- Expand:\n{ctx lb}"
  if na != nb then return some s!"functions: translation {na}, Expand {nb}"
  return none

end LeanVM.Guest.Program.Compare
