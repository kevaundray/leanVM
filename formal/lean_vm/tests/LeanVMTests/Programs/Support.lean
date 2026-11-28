import LeanVM.Dsl.Control
import LeanVM.Dsl.Hints
import LeanVM.Dsl.Mem
import LeanVM.Dsl.Keccak
import LeanVM.Dsl.Program

/-!
# Test programs: what they are and the words they use

A test program is an embedded program (a program list, `Dsl.Program.assemble`), the public input
its run publishes and the witness streams its hints read. `lake exe guest-backend export programs`
compiles each one and writes `DIR/<name>.txt` (the program in the line format of
`crates/isa/src/text.rs`) and `DIR/<name>.inputs` (its public input and streams, `inputsText`),
which the Rust tests read.
-/

namespace LeanVMTests.Programs

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

/-- A test program: its name, its program list, the public input it publishes and its witness
streams, each stream a list of entries popped in order. -/
structure TestProgram where
  name : String
  program : List (String × List GFn)
  publicInput : List E := [0, 0]
  streams : List (String × List (List E)) := []
  /-- The function the program is what it reaches of (`Dsl.Program.assemble`), if not all. -/
  entry : Option String := none

/-- A test program elaborated (`Dsl.Program.assemble`). -/
def TestProgram.elab (t : TestProgram) : Except String (List Elab) :=
  LeanVM.Dsl.Program.assemble t.program t.entry

/-- The literal `n < 2^128` as a word, its two limbs the low and high 64 bits. -/
abbrev lit (n : Nat) : E := litField n

/-- `g^k` as a word. -/
abbrev gp (k : Nat) : E := gpowE k

/-- A word as the decimal integer its two limbs spell, the low limb first. -/
def wordText (x : E) : String :=
  let (c0, c1) := limbsOf x
  toString (c0 + c1 * 2 ^ 64)

/-- The `.inputs` text of a test program: `public A B`, then one `witness NAME W…` line per
entry of each stream, in order. -/
def inputsText (t : TestProgram) : String :=
  let pub := "public " ++ " ".intercalate (t.publicInput.map wordText) ++ "\n"
  pub ++ String.join (t.streams.flatMap fun (s, es) =>
    es.map fun e => "witness " ++ s ++ " " ++ " ".intercalate (e.map wordText) ++ "\n")

/-- A `main` with no parameters and nothing returned, running `body`. -/
def mainOf (body : B Unit) : GFn where
  name := "main"
  arity := 0
  rets := 0
  body := fun _ => do body; return []

/-- The pointer `g^0`, the public input's two words at offsets `0` and `1`. -/
def publicPtr : B Word := B.const (gpowE 0)

/-- Write the two public words: `a` at `g^0`, `b` at `g^1`. -/
def publish {σ τ : Ty} (a : Var σ) (b : Var τ) : B Unit := do
  let p ← publicPtr
  B.store p 0 a
  B.store p 1 b

/-- The constant word `c`. -/
abbrev k (c : E) : B Word := B.const c

/-- A runtime branch on `a == b`: `eq` when they are equal, `ne` else. -/
def ifEq {σ τ : Ty} (a : Var σ) (b : Var τ) (eq ne : B Unit) : B Unit := do
  let c ← B.add a b
  discard <| B.ite c eq ne

/-- Cell `i` of a frame run, as a word. -/
abbrev cell (r : List V) (i : Nat) : Word := ⟨r.getD i default⟩

/-- Capture `i` of a loop body, as a word. -/
abbrev cap (caps : List V) (i : Nat) : Word := ⟨caps.getD i default⟩

end LeanVMTests.Programs
