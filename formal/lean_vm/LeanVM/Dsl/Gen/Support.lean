/-
  LeanVM.Dsl.Gen.Support

  The few names the translated guest (`LeanVM.Dsl.Gen.*`, written by `lake exe dsl-translate`)
  reads beside the builder: a source literal as a field word, a frame cell as a word, and the
  zkDSL's virtual bindings (a constant g-power, a shifted pointer) as Lean values.
-/

module

public import LeanVM.Dsl.Mem
public import LeanVM.Dsl.Keccak
public import LeanVM.Dsl.Fold

/-!
# Support for the translated guest

The translator resolves every compile-time decision of the zkDSL (`Expand`'s readings) and writes
builder calls; what it cannot write as a builder call is a Lean value of one of the types below.
A name the zkDSL binds to a constant `g^k` without a value is a `GPow`, one bound to `p·g^k` a
`Shifted`: both turn into values only where they are used (`B.const (gpowE k)`, `B.shifted p k`),
as the zkDSL materializes them.

## What a function author works with

One Lean definition per guest function: a `Const` parameter is a Lean `Nat` argument (a family
`Nat → GFn`, or an `@inline` function's argument), an `unroll` a Lean `for` over a `Nat` range, an
`if const(...)` a Lean `if` on `Nat`s or field constants. Four kinds of scalar:

* `Word`: a runtime value. Heap memory is read and written through a pointer word and a `Nat`
  offset (`B.load p off`, `B.store p off v`: the cell `p·g^off`); a frame run (`B.stackBuf n`) is a
  `List V` indexed by `Nat` (`cellOf r i`).
* `Shifted`: a pointer `base·g^exp` with `exp` a `Nat`, held without a value until it is used
  (`B.shifted p.base p.exp`; `B.load p.base (p.exp + off)` reads through it). A word is the pointer
  shifted by `0` (`Shifted.of`), and `B.shifted p 0` is `p` itself, so a name that is a word for some
  arguments and a shifted pointer for others is a `Shifted`.
* Field constants are `E`: `lit n` is the word of `n`, `gpowE k` is `g^k`, and `lit (2^k) = gpowE k`
  for `k < 64`. Integers known while elaborating (indices, counts, `Const` arguments, counters) are
  `Nat`.
* `FW` (`LeanVM.Dsl.Fold`): a scalar that is a constant for some arguments and a word for others.
  Arithmetic on one, and any arithmetic with a constant operand, is an `Ex`, written once for every
  argument: `Ex.lower` gives its value, `Ex.into d` writes it into the cell `d`, `Ex.bind` gives an
  `FW` again, `Ex.ret` a returned value. The builder folds `c op c`, `x + 0` and `x * 1`, and makes
  `x * g^k` the pointer `x·g^k` for a value `.w x` (a frame cell `.v x` stays a product); nothing
  else is rewritten, and the operands are lowered left to right.
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

/-- Its value. -/
def GPow.fe (g : GPow) : E := gpowE g.exp

/-- A shifted pointer `base·g^exp` bound to a name: materialized where it is used
(`B.shifted`). -/
structure Shifted where
  base : Word
  exp : Nat
  deriving Inhabited

/-- A word as a pointer shifted by `0`: where a name is a word in some instances and a shifted
pointer in others, it is written as the pointer (`B.shifted p 0` is `p`). -/
def Shifted.of (w : Word) : Shifted := ⟨w, 0⟩

end
end LeanVM.Dsl.Gen
