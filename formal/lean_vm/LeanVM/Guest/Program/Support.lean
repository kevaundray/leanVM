/-
  LeanVM.Guest.Program.Support

  What the guest's functions read beside the builder and its notation (`LeanVM.Dsl.Notation`): a source literal as a field word, a hint's output cell as a word.
-/

module

public import LeanVM.Dsl.Notation
public meta import LeanVM.Dsl.Lines

/-!
# Support for the guest's functions

The guest is one Lean definition per function of the guest program (`LeanVM.Guest.Program`), each written in the builder's notation (`LeanVM.Dsl.Notation`):

* A function is a `GFn`: its core name (`instName f [.L k]` for a member of a `Const` family, whose compile-time parameters are Lean `Nat` arguments), its argument and return cell counts, and its body from the parameters' values `ps`. An `@inline` function is a Lean function returning a `B` action, emitting into its caller's frame.
* Compile time is Lean: a compile-time parameter or loop counter is a `Nat`, an `unroll` a `for` over a `Nat` range, an `if` on them a Lean `if`.
* Runtime values are `Word`s. Arithmetic on them is an `Ex`, lowered where it is bound: `val e` for a word, `fold e` for an `FW` (a value that is a constant for some arguments: the builder folds it). `GEN ^ k` is the constant `g^k`, which shifts a pointer it multiplies; a `Shifted` is such a pointer held without a value.
* Memory: `r[i]` is cell `i` of a frame run `r : List V` (`B.stackBuf n`), `p[GEN ^ k]` the heap word at `p·g^k` (`B.heapBuf n`), `r[i] := e` and `p[GEN ^ k] := e` write them.
* `assert a == b`, `assert a != b`, `assert log x < n`; calls by core name (`call`, `call1`); a branch on a runtime value is `B.ite x zero nonzero`, a dispatch `B.dispatchInto`.
* Every `do` block of the builder in this namespace records its statements' source lines (`LeanVM.Dsl.Lines`), so a failed `assert` names the file and line of the guest it was written at.
-/

namespace LeanVM.Guest.Program

/-- A `do` block of the builder in the guest's namespace, with its statements' source lines. -/
scoped elab_rules : term <= ty
  | `(do $_) => do LeanVM.Dsl.Lines.elabDo (← Lean.getRef) ty

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

/-- A source literal as the field word the guest reads it as (`litField`). -/
abbrev lit (n : Nat) : E := litField n

/-- A value as a word. -/
def wordOf (v : V) : Word := ⟨v⟩

/-- The cell a hint wrote, read unchecked. -/
def hinted (m : B Hinted) : B Word := do
  return ⟨(← m).v⟩

end
end LeanVM.Guest.Program
