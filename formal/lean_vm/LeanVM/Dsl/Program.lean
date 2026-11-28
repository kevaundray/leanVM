/-
  LeanVM.Dsl.Program

  A program list of embedded functions, elaborated into the back end's input: every function the
  compiler lowers, in its order, with its trace and its source lines.
-/

module

public import LeanVM.Dsl.Builder
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# The program, elaborated

A program list (`LeanVM.Guest.Program.program` for the guest) names the functions a program lowers
whatever it runs: `main` first, then the others in the program's order, each with the `Const`
instances it reaches. `assemble` elaborates every one of them (`GFn.elab`: the function, then the
loop helpers it made) and orders them as the compiler's queue does: the listed functions, then,
walking the queue in order, each function's callees in the order its body names them, each the
first time it is named. A loop helper is renamed `__loop{k}`, `k` its place among the helpers in
that order, which is the compiler's numbering of its loops over the whole program (the back end
recognizes a helper by the prefix `__loop`); the calls naming it are renamed with it.

A callee no listed function elaborates, a listed function nothing reaches, and two different
functions of one name are errors: the list names exactly what the program runs.
-/

namespace LeanVM.Dsl.Program

open LeanVM.Core LeanVM.Compiler LeanVM.Dsl

@[expose] public section

/-- The functions statements call, in order: a branch's zero block before its other one, a
`match`'s arms in order. -/
partial def callees : List Core.Stmt → List String
  | [] => []
  | s :: ss => (match s with
      | .call f _ _ => [f]
      | .callIf _ f _ => [f]
      | .dispatch _ fs _ _ => fs
      | .ite _ z nz => callees z ++ callees nz
      | .match_ _ arms => arms.flatMap callees
      | _ => []) ++ callees ss

/-- Statements with the functions they call renamed by `g`. -/
partial def renameIn (g : String → String) : List Core.Stmt → List Core.Stmt
  | [] => []
  | s :: ss => (match s with
      | .call f a r => .call (g f) a r
      | .callIf x f a => .callIf x (g f) a
      | .dispatch x fs a r => .dispatch x (fs.map g) a r
      | .ite c z nz => .ite c (renameIn g z) (renameIn g nz)
      | .match_ x arms => .match_ x (arms.map (renameIn g))
      | s => s) :: renameIn g ss

/-- Whether `f` names a loop helper. -/
def isLoop (f : String) : Bool := f.startsWith "__loop"

/-- The program `prog` lists, elaborated: every function the compiler lowers, in its order, each
with its trace and its source lines. With `from_ := some f`, the program is the functions `f`
reaches, the others listed with it left out: a `main` over a library's functions. -/
def assemble (prog : List (String × List GFn)) (from_ : Option String := none) :
    Except String (List Elab) := do
  let mut byName : Std.HashMap String Elab := {}
  for (_, fs) in prog do
    for f in fs do
      for e in f.elab do
        let n := e.1.core.name
        match byName[n]? with
        | some old =>
            unless old.1.core == e.1.core do throw s!"two different functions are named `{n}`"
        | none => byName := byName.insert n e
  let roots : List String := match from_ with
    | some f => [f]
    | none => prog.filterMap fun (p : String × List GFn) => p.2.head?.map GFn.name
  let mut order : Array String := #[]
  let mut seen : Std.HashSet String := {}
  for r in roots do
    if seen.contains r then throw s!"`{r}` is listed twice"
    order := order.push r
    seen := seen.insert r
  let mut i := 0
  while h : i < order.size do
    let f := order[i]
    let some e := byName[f]? | throw s!"no listed function elaborates `{f}`"
    for c in callees e.1.core.body do
      unless seen.contains c do
        unless byName.contains c do
          throw s!"`{f}` calls `{c}`, which no listed function elaborates"
        order := order.push c
        seen := seen.insert c
    i := i + 1
  if from_.isNone then
    for (n, _) in byName.toList do
      unless seen.contains n do throw s!"`{n}` is listed or elaborated, and nothing reaches it"
  let loops : Std.HashMap String Nat :=
    (order.filter isLoop).zipIdx.foldl (fun m (n, k) => m.insert n k) {}
  let g := fun (n : String) => match loops[n]? with
    | some k => s!"__loop{k}"
    | none => n
  return order.toList.filterMap fun n => byName[n]?.map fun (tf, lines) =>
    ({ tf with core := { tf.core with name := g tf.core.name, body := renameIn g tf.core.body } },
      lines)

/-- The program `prog` lists, as the back end's input. -/
def traced (prog : List (String × List GFn)) : Except String (List TracedFn) :=
  (assemble prog).map (·.map (·.1))

/-- The program `prog` lists, its core functions. -/
def core (prog : List (String × List GFn)) : Except String Core.Program :=
  (traced prog).map (·.map (·.core))

end
end LeanVM.Dsl.Program
