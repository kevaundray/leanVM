module

public import NativeRustcVmArm.Rodata
public import NativeRustcVmArm.Placed.Basic
public import NativeRustcVmArm.Code.Vm

/-!
# The bytes of each data label of the program

`dataAt l P`: the bytes of the `.byteArray` directives after the label `l` in `P`, up to the next
non-byte directive. The read-only data `Vm.rodata` holds exactly the items' labels
(`labels_rodata`).
-/

namespace NativeRustcVmArm.Rodata

open NativeRustcVm.Data

@[expose] public section

/-- The bytes of the `.byteArray` directives at the head of `ds`. -/
def collect : List Directive → List UInt8
  | .byteArray b :: ds => b.data.toList ++ collect ds
  | _ => []

/-- The bytes after the first label `l` of `P`. -/
def dataAt (l : Label) : List Directive → Option (List UInt8)
  | [] => none
  | .label l' :: ds => if l' = l then some (collect ds) else dataAt l ds
  | _ :: ds => dataAt l ds

end

set_option Elab.async false

/-- The read-only data's labels are the items', in order. -/
public theorem labels_rodata : Placement.labels Vm.rodata = Item.all.map itemLabel := by
  decide +kernel

end NativeRustcVmArm.Rodata
