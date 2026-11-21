module

public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Xmss.FromBytes.Names

public import NativeRustcArm.FromBytes.Head
public import NativeRustcArm.FromBytes.Loop
public import NativeRustcArm.FromBytes.Path
public import NativeRustcArm.FromBytes.Tail

/-!
# `LeanXmssSignature::from_bytes`'s closure meets its contract

`fromBytes_spec`: the closure, placed anywhere in a program whose `memcpy` meets its contract,
meets `FromBytesPre`/`FromBytesPost` (`NativeRustcArm.Spec.FromBytes`): the prologue and the
randomizer (`head`), the loop over the chain values (`loop`), their `memcpy` (`mid`), the path
(`path`), the output's two `memcpy`s and the return (`tail`). The bounds checks never fail: the
cursor is at most `1204`.
-/

namespace NativeRustcArm.Xmss.FromBytes

open NativeArm

/-- **`from_bytes`'s closure meets its contract.** -/
public theorem fromBytes_spec [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (label NativeRustcArm.Xmss.FromBytes.entryLabel) FromBytesPre FromBytesPost := by
  intro m₀ hpre
  have P := pre_of hpre
  rw [hp.label NativeRustcArm.Xmss.FromBytes.entry_at, NativeRustcArm.Xmss.FromBytes.entryOffset, Nat.add_zero]
  exact head hp hpre fun st hpc h =>
    Eventually.bind (loop hp P hpc h) fun st' ⟨hpc', h'⟩ =>
      mid hp hmemcpy P hpc' h' fun st'' hpc'' h'' =>
        path hp P hpc'' h'' fun s hs hret hc => tail hp hmemcpy P hs hret hc

end NativeRustcArm.Xmss.FromBytes
