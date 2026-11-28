/-
  LeanVM.Guest.Program.FieldPacking

  The guest's section "field packing".
-/

module

public import LeanVM.Guest.Program.Support
public import LeanVM.Guest.Program.Config

/-!
# Field packing

A word is a cell, so a value a KECCAK hashes or a transcript absorbs needs no check of its own. Exposing a word's two K limbs is the one thing that does: the tower representation is unique, so proving that the exposed lanes are in K and weight back to the word is the whole check, no equality to make, one less hint to distrust.
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

def pack64x2 (a : Word) (b : Word) (dsts : List V) : B Unit := B.inline "pack64x2" do
  B.assertInK a b
  dsts[0] := a + Y_TOWER * b

/-- Hint the low limb and derive the quotient by Y. Requiring both in K proves `word = lo + Y*hi`, which binds them. -/
def splitLimbs (word : Word) : B (Word × Word) := B.inline "split_limbs" do
  let lo ← B.stackBuf 1
  B.hintLimbs word lo
  let hi ← val ((word + lo[0]) * Y_INV)
  B.assertInK lo[0] hi
  return (lo[0], hi)

/-- A challenge is the sponge's first two lanes, its first cell. -/
def challengeFromState (state : List V) : B Word := B.inline "challenge_from_state" do
  return state[0]

end
end LeanVM.Guest.Program
