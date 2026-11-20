module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Head

/-!
# `verify_bus_balance` (x86-64)

The three layouts (`head_spec`), the grind, the challenges and the GKR walk (`grind_spec`), the
scalars and the claims (`scal_spec`, `claimsA_spec`, `claimsB_spec`), the bytecode share
(`share_spec`), the three sides (`push_spec`, `pull_spec`, `count_spec`), the point and the totals
(`tail_spec`): `verifyBusBalance_spec`.
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Bus

public section

variable [Host] {k : Nat}

/-- **`verify_bus_balance` meets its contract.** -/
theorem verifyBusBalance_spec (hp : Placed code k)
    (hbl : ∀ L bl, Spec (Labels.label busLayoutLabel) (BusLayoutPre L bl) (BusLayoutPost L bl))
    (hmc : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hbit : Spec (Labels.label bitLengthLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label grindLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label sampleChallengesLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hsq : ∀ sp, Spec (Labels.label squeezeLabel) (SqueezePre sp) (SqueezePost sp))
    (hgkr : ∀ a s, Spec (Labels.label verifyGkrLabel) (VerifyGkrPre a s) (VerifyGkrPost a s))
    (hrss : ∀ a s, Spec (Labels.label readScalarsLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    (hrs : ∀ a s, Spec (Labels.label readScalarLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hpc : ∀ cs, Spec (Labels.label pushClaimLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hbs : ∀ a s, Spec (Labels.label bytecodeShareLabel) (BytecodeSharePre a s)
      (BytecodeSharePost a s))
    (hcbv : Spec (Labels.label computedBytecodeValueLabel) ComputedBytecodeValuePre
      ComputedBytecodeValuePost)
    (hkp : Spec (Labels.label kpowLabel) KpowPre KpowPost)
    (hfc : Spec (Labels.label fpClosureLabel) FpClosurePre FpClosurePost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label accumulateSideLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label bufEW63ExtendLabel) (BufEWExtendPre 63) (BufEWExtendPost 63)) :
    ∀ a s L, Spec (Labels.label verifyBusBalanceLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L) := by
  intro a s0 L m0 h
  rw [show Labels.label verifyBusBalanceLabel = Host.addrOf (k + 0) from hp.label (j := 0) rfl]
  exact head_spec hp h hbl hmc fun _ A ↦ grind_spec hp h hmc hbit (hgr a) (hsc a) hsq (hgkr a)
    (fun _ _ _ _ _ _ A' ↦ scal_spec hp h (hrss a) (hrs a) hpc (hbs a) hcbv hkp hfc hacc hext A') A

end

end NativeRustcVmX64.Bus.VerifyBusBalance
