module

public import NativeRustcVmArm.Whir.GlueLevel.Exit

/-!
# `glue_level` meets its contract

`glueLevel_spec`: `glue_level`, placed anywhere in the program, given `EW::mul`'s and the three
`Buf::extend`s' contracts, from its entry in a state satisfying `GlueLevelPre s` returns with X0 =
`1`, the state at X0 `glueLevel s λ μ oodPoint oodValue queries weights batched`, memory changed in
the state and its stack only, the callee-saved registers and SP restored (`GlueLevelPost s`). The
run: the products (`head_step`), the claim and the first glued claim (`first_step`), the second's
header and queries (`second_step`), its weights (`third_step`), the count and the return
(`exit_step`).
-/

namespace NativeRustcVmArm.Whir.GlueLevel

open NativeRustcArm NativeArm NativeVm.Model NativeRustcVmArm.Vm.GlueLevel

public section

variable [Host] {k : Nat}

/-- **`glue_level`'s contract.** -/
theorem glueLevel_spec (hp : Placed code k)
    (hmul : Spec (label ewMulLabel) EWMulPre EWMulPost)
    (hext30 : Spec (label bufEW30ExtendLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hextU : Spec (label bufU64x230ExtendLabel) (BufU64ExtendPre 230) (BufU64ExtendPost 230))
    (hext230 : Spec (label bufEW230ExtendLabel) (BufEWExtendPre 230) (BufEWExtendPost 230))
    (s : WhirStateW) : Spec (label glueLevelLabel) (GlueLevelPre s) (GlueLevelPost s) := by
  intro m0 hpre
  rw [show label glueLevelLabel = Host.addrOf (k + 0) from hp.label rfl]
  exact head_step hp hmul hpre fun _ h3 ↦ first_step hp hext30 hpre h3 fun _ h5 ↦
    second_step hp hextU hpre h5 fun _ h8 ↦ third_step hp hext230 hpre h8 fun _ h10 ↦
      exit_step hp hpre h10

end

end NativeRustcVmArm.Whir.GlueLevel
