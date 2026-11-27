/-
  LeanVM.Dsl.Check

  The migration check: each ported function, elaborated, against what `Expand` makes of the
  zkDSL source it replaces, run on the exported guest.
-/

import LeanVM.Dsl.Guest
import LeanVM.Core.Expand
import LeanVM.Core.Renumber

/-!
# Elaboration against expansion

A ported function is checked against `Expand` on the guest's exported source
(`LeanVM.Guest.Data.guest`): the core functions, the ported one and those it makes (loop helpers,
`Const` specializations), are equal once their values are numbered by first occurrence (the
renumbering the guest's core data is written in, `Fn.numbering`) and the loop helpers carry the
expansion's names. Where they are equal the function's B1 proofs, stated on the renumbered core
data, hold of the ported function unchanged.

The checks are `#guard`s: the elaborator evaluates both sides, `Expand` included, which the kernel
would have to unfold through the field arithmetic of every constant. An improved form is checked
for what it changes against the faithful one (`eqPrefixChain'`, `daColumnOffsets'`).
-/

namespace LeanVM.Dsl.Check

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl LeanVM.Dsl.Guest

/-- The values of `f`, parameters first, then in order of first occurrence. -/
def canonTable (f : Core.Fn) : List V :=
  (f.params ++ Stmt.valsList f.body).foldl (fun t v => if t.contains v then t else t ++ [v]) []

/-- `f` with its values numbered by first occurrence. -/
def canon (f : Core.Fn) : Core.Fn :=
  let t := canonTable f
  f.rename fun v => V.n (t.idxOf v)

/-- The callee names of `f`'s statements at its top level, through `g`. -/
def renameCallees (g : String → String) (f : Core.Fn) : Core.Fn :=
  { f with
    name := g f.name
    body := f.body.map fun
      | .call c a r => .call (g c) a r
      | .callIf x c a => .callIf x (g c) a
      | s => s }

/-- The expansion's name of an elaborated loop helper: `__loop_<f>_<k>` is `__loop<k>`, the
expansion of one function counting its loops from zero. -/
def expansionName (f : String) (s : String) : String :=
  match s.dropPrefix? s!"__loop_{f}_" with
  | some k => s!"__loop{k}"
  | none => s

/-- The core functions `Expand` makes of `f` in the program `p`, with what it queues. -/
def expanded (p : Source.Program) (f : Source.Func) : List Core.Fn :=
  match Expand.expandQueue p 1000 0 #[f] 0 #[] with
  | .ok a => a.toList.map (·.1.core)
  | .error _ => []

/-- The core functions elaborated from `fs`, helpers named as the expansion names them. -/
def elaborated (fs : List GFn) : List Core.Fn :=
  fs.flatMap fun f => (f.elab.map (·.1.core)).map (renameCallees (expansionName f.name))

/-- Equal up to the numbering of values. -/
def sameCore (a b : List Core.Fn) : Bool := a.map canon == b.map canon

/-- The exported source of a function. -/
def src (name : String) : Source.Func :=
  (LeanVM.Guest.Data.guest.funcs.find? (·.name == name)).getD default

/-! ## The faithful ports -/

#guard sameCore (elaborated [selectorRunNibbles]) (expanded LeanVM.Guest.Data.guest (src "selector_run_nibbles"))

/-- A function calling the inline `is_child` at `k = 0` on a two-cell `StackBuf`. -/
def isChildCaller : Source.Func :=
  { name := "is_child_at0",
    params := [⟨"node", .runtime .scalar⟩, ⟨"kids", .runtime (.stackBuf 2)⟩,
      ⟨"bit", .runtime .scalar⟩],
    returnShapes := [], inline := false,
    body := [.mk 1 (.call "is_child" [.var "node", .var "kids", .lit 0, .var "bit"]),
      .mk 2 (.ret [])] }

#guard sameCore (elaborated [isChildAt0])
  (expanded { LeanVM.Guest.Data.guest with funcs := LeanVM.Guest.Data.guest.funcs ++ [isChildCaller] }
    isChildCaller)

#guard sameCore (elaborated (eqPrefixChain :: (List.range EQ_CHAIN_ARMS).map eqPrefixRun))
  (expanded LeanVM.Guest.Data.guest (src "eq_prefix_chain"))

#guard sameCore (elaborated [daColumnOffsets]) (expanded LeanVM.Guest.Data.guest (src "da_column_offsets"))

/-! ## The improved forms -/

/-- The statements of the elaborated functions. -/
def atoms (fs : List Core.Fn) : Nat := (fs.map fun f => (Stmt.valsList f.body).length).sum

-- `eq_prefix_chain` improved: every arm loses its `SET 0` and its return cell, the dispatch its
-- target.
#guard (elaborated [eqPrefixChain']).map (fun f => f.body.length) ==
  (elaborated [eqPrefixChain]).map (fun f => f.body.length)
#guard ((List.range EQ_CHAIN_ARMS).map fun n => ((eqPrefixRun' n).core.body.length + 1 ==
  (eqPrefixRun n).core.body.length)).all id

-- `da_column_offsets` improved: each loop loses its entry test and its bound parameter, and each
-- iteration one stepped counter.
#guard (elaborated [daColumnOffsets']).length == (elaborated [daColumnOffsets]).length
#guard atoms (elaborated [daColumnOffsets']) < atoms (elaborated [daColumnOffsets])

end LeanVM.Dsl.Check
