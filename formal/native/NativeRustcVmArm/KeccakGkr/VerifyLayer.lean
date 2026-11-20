module

public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontF
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Weights

/-!
# `verify_layer` meets its contract

The prologue and the product (`pro_run`), its projection (`proj_loop`), ι's segment kernel and
bit weights (`seg_run`), the first check, the grind and `s` (`check_run`), the instance weights
and the equality-mode sumcheck (`layer_run`), the plain sumcheck, the values and the local kernel
(`plain_run`), the second check (`check2_run`), the grind and `β` (`g_run`), the layer's weights,
their transpose and the new claim (`weights_run`) (`verifyLayer_spec`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeArm NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer

public section

variable [NativeArm.Host] {k : Nat}

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
  refine pro_run hp h (hrs a) fun st p s1 hr hpc hi hfm ↦ ?_
  refine proj_loop hp h hmul (st0 := st.data) (p := p) (fun st' hpc' hfb hs hk hkr hacc ↦ ?_)
    47 0 st rfl hpc hi (NativeRustcVm.SameOutside.refl _ _) (fun _ h' ↦ h') (fun _ _ ↦ rfl)
  have hai : AtI m0 a c p s1 st'.data :=
    ⟨hfb, hfm.bel h hk hs, (congrArg UInt64.toNat (kg hkr .X25)).trans hi.mi.x25,
      by rw [projected_eq]; exact hacc⟩
  have hrun1 : runL s c m0 = rest1 m0.regs.X1.toNat m0.regs.X2.toNat c p s1 := by
    have := run_rest m0.regs.X1.toNat m0.regs.X2.toNat c s
    rw [show LeanVM.Protocol.Verifier.productBits = 47 from rfl, hr] at this
    exact this
  refine seg_run hp h hek hpc' hai fun st2 hpc2 hj ↦ ?_
  refine check_run hp h hmul hsum hbl (hgr a) hsq hpc2 hj hrun1
    fun st3 ch s2 hpc3 hh hrun3 ↦ ?_
  refine layer_run hp h hiw hsum hpe (hsl a) hpc3 hh hrun3 fun st4 pt v s3 hpc4 hk4 hrun4 ↦ ?_
  refine plain_run hp h (hspl a) (hrs a) hek hpc4 hk4 hrun4
    fun st5 lp tv val s5 hpc5 hl5 hrun5 ↦ ?_
  refine check2_run hp h hdot hmul hpc5 hl5 hrun5 fun st6 hpc6 hg ↦ ?_
  exact Bus.Gkr.at_pc hpc6 (g_run hp h hbl (hgr a) hsq
    (fun st7 _ _ _ _ _ _ _ _ hpc7 hat ↦ weights_run hp h hlt hmul hmemcpy hext hpc7 hat) hg)

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
