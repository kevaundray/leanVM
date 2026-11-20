module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Code.Vm.FormTerms
public meta import NativeRustcVmArm.Code.Vm.FormTerms
public meta import NativeRustcVmArm.Layout.Common

/-!
# `form_terms`'s blocks, run by the symbolic executor

From `entryS`: region 0 `FORMS` (`593` spans of 16 bytes) at its label. `b0` compares the form
with `592`: above, `b2` returns the empty slice; else `b1` (`S1`, the form below `593`) loads its
span and returns `TERMS` plus `40` times its start and its length, or the empty slice when the span
leaves `TERMS`.
-/

namespace NativeRustcVmArm.Layout.FormTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FormTerms

@[expose] public section

/-- `FORMS`' label. -/
def formsLabel : Label := ".Lanon.a75d6d9e6a8990b4224ef13f18552af8.13"

/-- At the entry: `FORMS` (region 0) at its label. -/
def entryS : SState := init [(9488, false)] .sp [] [(formsLabel, 0)]

/-- After `b0` falls through: the form below `593`. -/
def S1 : SState := { after b0 entryS with bounds := [(.reg .X0, 593)] }

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 S1
sym_block run_b2 := exec b2 (after b0 entryS)

end NativeRustcVmArm.Layout.FormTerms
