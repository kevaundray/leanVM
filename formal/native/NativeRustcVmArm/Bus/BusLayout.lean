module

public import NativeRustcVmArm.Bus.BusLayout.SizesRun
public import NativeRustcVmArm.Bus.BusLayout.Offsets
public import NativeRustcVmArm.Bus.BusLayout.Loop
public import NativeRustcVmArm.Bus.BusLayout.Finish

/-!
# `bus_layout`

The sizes (`sizes_run`: the framework's, then each block's owner's log-height), the offsets
(`offsets_run`: `stack_offsets`), the placements (`place_run`), the layout copied out
(`finish`): `busLayout_spec`.
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout NativeArm
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {k : Nat}

/-- **`bus_layout` meets its contract.** -/
theorem busLayout_spec (hp : Placed code k)
    (hms : Spec (Labels.label "memset") MemsetPre MemsetPost)
    (hmc : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hso : Spec (Labels.label stackOffsetsLabel) StackOffsetsPre StackOffsetsPost)
    {L : LayoutW} {bl : List NativeRustcVm.Data.Block} :
    Spec (Labels.label busLayoutLabel) (BusLayoutPre L bl) (BusLayoutPost L bl) := by
  intro m0 hpre
  rw [show Labels.label busLayoutLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  exact Eventually.bind (sizes_run hp hms hpre) fun st hD ↦
    Eventually.bind (offsets_run hp hms hso hpre hD) fun st2 ⟨hpc2, hI⟩ ↦
      Eventually.bind (place_run hp hpre hpc2 hI) fun st3 ⟨hpc3, hE⟩ ↦
        finish hp hmc hpre hpc3 hE

end

end NativeRustcVmArm.Bus.BusLayout
