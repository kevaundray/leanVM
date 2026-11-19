module

public import NativeRustcArm.XmssVerify.HeadRun
public import NativeRustcArm.XmssVerify.ParseRun
public import NativeRustcArm.XmssVerify.Final

/-!
# `xmss_verify` meets its contract

`xmssVerify_spec`: `xmss_verify`, placed anywhere in a program whose callees meet their contracts,
meets `XmssVerifyPre`/`XmssVerifyPost` (`NativeRustcArm.Spec.XmssVerify`): the prologue (`head`),
the copy of the signature's words (`copy`), the parsing of the key and the layers (`parse`), the
bottom and top layers and the comparison with the key's root (`layers`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeArm

/-- **`xmss_verify` meets its contract.** -/
public theorem xmssVerify_spec [Host] {k : Nat} (hp : Placed code k) {w : Nat → UInt64}
    (hmemset : Spec (label "memset") MemsetPre MemsetPost)
    (hmemcpy : Spec (label "memcpy") MemcpyPre MemcpyPost)
    (hupdate : Spec (label "_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update") UpdatePre UpdatePost)
    (hfinalize : Spec (label "_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize") FinalizePre
      FinalizePost)
    (hwots : Spec (label "_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf") WotsLeafPre WotsLeafPost)
    (hfb : Spec (label fromBytesLabel) FromBytesPre FromBytesPost) :
    Spec (label "xmss_verify") (XmssVerifyPre w) (XmssVerifyPost w) := by
  intro m₀ hpre
  have P := pre_of hpre
  have Cs : Callees := ⟨hmemset, hmemcpy, hupdate, hfinalize, hwots, hfb⟩
  rw [hp.label (j := 0) (by decide +kernel), Nat.add_zero]
  exact head hp hmemset P fun st hpc h =>
    Eventually.bind (copy hp P hpc h) fun st' ⟨hpc', h'⟩ =>
      parse hp hfb P hpc' h' fun st'' hpc'' h'' =>
        Eventually.mono (layers hp Cs P hpc'' h'') fun s ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩

end NativeRustcArm.Xmss.XmssVerify
