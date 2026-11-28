/-
  LeanVM.Dsl.Gen.Support

  The few names the translated guest (`LeanVM.Dsl.Gen.*`, written by `lake exe dsl-translate`)
  reads beside the builder: a source literal as a field word, a frame cell as a word, and the
  zkDSL's virtual bindings (a constant g-power, a shifted pointer) as Lean values.
-/

module

public import LeanVM.Dsl.Mem
public import LeanVM.Dsl.Keccak

/-!
# Support for the translated guest

The translator resolves every compile-time decision of the zkDSL (`Expand`'s readings) and writes
builder calls; what it cannot write as a builder call is a Lean value of one of the types below.
A name the zkDSL binds to a constant `g^k` without a value is a `GPow`, one bound to `p·g^k` a
`Shifted`: both turn into values only where they are used (`B.const (gpowE k)`, `B.shifted p k`),
as the zkDSL materializes them.
-/

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

/-- A source literal as the field word the zkDSL reads it as (`litField`). -/
abbrev lit (n : Nat) : E := litField n

/-- Cell `i` of a frame run, as a word. -/
def cellOf (r : List V) (i : Nat) : Word := ⟨r.getD i default⟩

/-- A value as a word. -/
def wordOf (v : V) : Word := ⟨v⟩

/-- The cell a hint wrote, read as the zkDSL reads it: unchecked. -/
def hinted (m : B Hinted) : B Word := do
  return ⟨(← m).v⟩

/-- A call of `f` returning one value. -/
def call1 (f : String) (args : List V) : B Word := do
  return (← B.call f args 1).headD default

/-- A constant `g^exp` bound to a name: no value until it is used. -/
structure GPow where
  exp : Nat
  deriving Inhabited

/-- A shifted pointer `base·g^exp` bound to a name: materialized where it is used
(`B.shifted`). -/
structure Shifted where
  base : Word
  exp : Nat
  deriving Inhabited

end
end LeanVM.Dsl.Gen
