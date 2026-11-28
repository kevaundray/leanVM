/-
  LeanVM.Dsl.Lines

  The source line of each statement of a program written in the builder, recorded by its `do` blocks: a failed `assert` in the compiled program names the Lean file and line it was written at.
-/

module

public meta import Lean.Elab.Do.Switch

/-!
# Source lines

A function written in the builder is a `do` block of `B`. `elabDo` elaborates such a block with a
line marker (`B.line l file`) before each of its statements and before each statement of the
blocks it nests (the arms of an `if` or a `match`, the body of a `for`), `l` and `file` where the
statement is written: so the program's author writes no markers, and every instruction of the
compiled program has the line of the statement that emitted it (`Compiler.Lines`). A `do` block
nested as a term (an argument of `B.ite`, the body of an `@inline` function) is elaborated on its
own, so it gets its markers once.

A marker is a line table entry and no event of the trace, so the compiled program is the same
with or without them. A program's namespace opts in by elaborating its `do` blocks with `elabDo`
(the guest's: `LeanVM.Guest.Program.Support`).
-/

public meta section

namespace LeanVM.Dsl.Lines

open Lean Elab Term

/-- The file being elaborated, from the repository's root: its path below the Lean package's root
(the nearest directory above it holding a `lakefile.toml`), which is `formal/lean_vm`; its name
alone outside a package. -/
def fileOf (path : System.FilePath) : IO String := do
  let mut rel := [path.fileName.getD ""]
  let mut dir := path.parent
  for _ in [0:64] do
    let some d := dir | break
    if ← (d / "lakefile.toml").pathExists then
      return "/".intercalate ("formal/lean_vm" :: rel)
    rel := d.fileName.getD "" :: rel
    dir := d.parent
  return path.fileName.getD ""

/-- The statements of a `do` sequence (`doSeqIndent`, `doSeqBracketed`): the position of its list of
items among the node's children. -/
def seqItems? (k : SyntaxNodeKind) : Option Nat :=
  if k == ``Lean.Parser.Term.doSeqIndent then some 0
  else if k == ``Lean.Parser.Term.doSeqBracketed then some 1
  else none

/-- The marker of a statement at line `l` of `file`. -/
def marker (file : String) (l : Nat) : Syntax :=
  .node .none ``Lean.Parser.Term.doSeqItem
    #[.node .none ``Lean.Parser.Term.doExpr
      #[Syntax.mkApp (mkCIdent `LeanVM.Dsl.B.line) #[Syntax.mkNumLit (toString l), Syntax.mkStrLit file]],
      mkNullNode]

/-- `stx` with a marker before each statement of every `do` sequence in it, but those of a nested
`do` term, which is elaborated on its own. -/
partial def mark (file : String) (fm : FileMap) : Syntax → Syntax
  | .node info kind args =>
      if kind == ``Lean.Parser.Term.do then .node info kind args
      else
        let args := args.map (mark file fm)
        match seqItems? kind with
        | some i =>
            let items := args[i]!.getArgs.foldl (init := #[]) fun acc item =>
              match item.getPos? with
              | some pos => (acc.push (marker file (fm.toPosition pos).line)).push item
              | none => acc.push item
            .node info kind (args.set! i (mkNullNode items))
        | none => .node info kind args
  | stx => stx

/-- A `do` block whose expected type is `B α`, elaborated with its statements' markers; any other
`do` block is left to Lean's own elaborator. -/
def elabDo (stx : Syntax) (ty : Expr) : TermElabM Expr := do
  tryPostponeIfMVar ty
  unless (← instantiateMVars ty).getAppFn.isConstOf `LeanVM.Dsl.B do throwUnsupportedSyntax
  let file ← fileOf (← getFileName)
  let fm ← getFileMap
  match stx with
  | .node info kind args => Lean.Elab.Term.elabDo (.node info kind (args.map (mark file fm))) ty
  | _ => throwUnsupportedSyntax

end LeanVM.Dsl.Lines
