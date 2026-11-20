module

public import NativeRustcVmArm.KeccakGkr.FirstClaim.Result

/-!
# `first_claim` meets its contract

The prologue (`prologue`: `eq_kernel` on the lane point into the frame's lanes), the bit weights'
loop (`w_loop`: lane `j / 64` times `1 << (j % 64)` by `EW::mul`), the segment's kernel, `last`
and the instance weights' kernel (`mid`: `eq_kernel`, `dot`, `EW::mul`, `eq_kernel`), the claim's
point (`tail`: two `Buf::extend`s), the result copied out and the return (`finish`: two
`memcpy`s) (`firstClaim_spec`).
-/

namespace NativeRustcVmArm.KeccakGkr.FirstClaim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeArm
open NativeRustcVmArm.Vm.FirstClaim NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck

public section

variable [NativeArm.Host] {k : Nat}

/-- **`first_claim` meets its contract**, given `eq_kernel`'s, `EW::mul`'s, `dot`'s,
`Buf<EW, 30>::extend`'s and `memcpy`'s. -/
theorem firstClaim_spec (hp : Placed code k)
    (heq : Spec (Labels.label eqKernelLabel) EqKernelPre EqKernelPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost)
    (hdot : Spec (Labels.label dotLabel) DotPre DotPost)
    (hext : Spec (Labels.label bufEW30ExtendLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hmemcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (inst segment lanePoint output : Array EW) :
    Spec (Labels.label firstClaimLabel) (FirstClaimPre inst segment lanePoint output)
      (FirstClaimPost inst segment lanePoint output) := by
  intro m0 hpre
  have hl : Labels.label firstClaimLabel = Host.addrOf (k + 0) := hp.label (j := 0) rfl
  rw [hl]
  exact (prologue hp hpre heq).bind fun _ ⟨hpc, hI⟩ ↦
    (w_loop hp hpre hmul hpc hI).bind fun _ ⟨hpc, hI⟩ ↦
    (mid hp hpre heq hmul hdot hpc hI).bind fun _ ⟨hpc, hI⟩ ↦
    (tail hp hpre hext hpc hI).bind fun _ ⟨hpc, hI⟩ ↦ finish hp hpre hmemcpy hpc hI

end

end NativeRustcVmArm.KeccakGkr.FirstClaim
