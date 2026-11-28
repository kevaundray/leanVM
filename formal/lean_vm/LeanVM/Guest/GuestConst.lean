/-
  LeanVM.Guest.GuestConst

  `guest_const% C`: the value of the guest's constant `C`, as a literal.
-/

module

public meta import Lean.Elab.Term

/-!
# The guest's constants

The guest's configuration constants are Lean definitions, `LeanVM.Guest.Program.C : Nat` in
`Guest/Program/Config.lean`: a placeholder's value (`Guest/Data/Placeholders.lean`, generated) or
an expression over them. `guest_const% C` elaborates to the literal `C` reduces to, so a definition
that mirrors `C` (`abbrev levelOodGrind : ℕ := guest_const% OOD_GRIND_BITS`) reads exactly as a
hand copy of it, and a change to `C` in the guest reaches it by the regeneration alone. A module
using it imports the configuration privately: only the literal enters its terms.
-/

public meta section

namespace LeanVM.Guest.GuestConst

open Lean Elab Term Meta

/-- `guest_const% C`: the value of the guest's constant `C`, a natural number literal. -/
elab:max "guest_const% " c:ident : term => do
  let n := `LeanVM.Guest.Program ++ c.getId
  -- The configuration is imported privately: look it up and reduce it outside the exported view.
  withoutExporting do
    unless (← getEnv).contains n do
      throwErrorAt c "no guest constant {c.getId} ({n})"
    let v ← withTransparency .all <| whnf (mkConst n)
    match v.rawNatLit? <|> v.nat? with
    | some k => return mkNatLit k
    | none => throwErrorAt c "the guest constant {c.getId} reduces to {v}, not a literal"

end LeanVM.Guest.GuestConst
