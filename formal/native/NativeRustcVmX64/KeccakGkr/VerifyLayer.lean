module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.CheckAHead
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back

/-!
# `verify_layer` meets its contract (x86-64)

From the entry to the first check passed (`toAfterA`: the product's read, its projection, ι's
segment kernel and bit weights, the first check), then the rest (`back_run`: the grind and `s`,
the instance weights, the two sumchecks, the values and the local kernel, the second check, the
grind and `β`, the layer's weights, their transpose and the new claim) (`verifyLayer_spec`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea)

public section

variable [Host] {k : Nat}

/-- **`verify_layer` meets its contract**, given `bit_length`'s, `Buf<EW, 30>::extend`'s, `dot`'s,
`EW::mul`'s, `eq_kernel`'s, `instance_weights`'s, `linear_transpose`'s, `memcpy`'s,
`poly_eval`'s, `squeeze`'s, `sum_e`'s, the two sumchecks', `grind`'s and `read_scalars`'s. -/
theorem verifyLayer_spec (hp : Placed code k)
    (hbl : Spec (Labels.label bitLengthLabel) BitLengthPre BitLengthPost)
    (hext : Spec (Labels.label bufEW30ExtendLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hdot : Spec (Labels.label dotLabel) DotPre DotPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost)
    (hek : Spec (Labels.label eqKernelLabel) EqKernelPre EqKernelPost)
    (hiw : Spec (Labels.label instanceWeightsLabel) InstanceWeightsPre InstanceWeightsPost)
    (hlt : ∀ ws, Spec (Labels.label linearTransposeLabel) (LinearTransposePre ws)
      (LinearTransposePost ws))
    (hmemcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hpe : Spec (Labels.label polyEvalLabel) PolyEvalPre PolyEvalPost)
    (hsq : ∀ sp, Spec (Labels.label squeezeLabel) (SqueezePre sp) (SqueezePost sp))
    (hsum : Spec (Labels.label sumELabel) SumEPre SumEPost)
    (hspl : ∀ a s, Spec (Labels.label sumcheckPlainLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hsl : ∀ a s pt, Spec (Labels.label sumcheckLayerLabel) (SumcheckLayerPre a s pt)
      (SumcheckLayerPost a s pt))
    (hgr : ∀ a s, Spec (Labels.label grindLabel) (GrindPre a s) (GrindPost a s))
    (hrs : ∀ a s, Spec (Labels.label readScalarsLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s)) :
    ∀ a s c, Spec (Labels.label verifyLayerLabel) (VerifyLayerPre a s c)
      (VerifyLayerPost a s c) := by
  intro a s c m0 h
  have hl : Labels.label verifyLayerLabel = Host.addrOf (k + 0) := hp.label (j := 0) rfl
  rw [hl]
  exact toAfterA hp (hrs a s) hmul hek hsum h fun p s1 d hA hrun ↦
    back_run hp hbl hext hdot hmul hek hiw hlt hmemcpy hpe hsq hsum hspl hsl hgr hrs h hA hrun

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer

/-- info: 'NativeRustcVmX64.KeccakGkr.VerifyLayer.verifyLayer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.KeccakGkr.VerifyLayer.verifyLayer_spec
