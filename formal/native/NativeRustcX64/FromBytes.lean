module

public import NativeRustcX64.FromBytes.Head
public import NativeRustcX64.FromBytes.Loop
public import NativeRustcX64.FromBytes.Path
public import NativeRustcX64.FromBytes.Tail

/-!
# `LeanXmssSignature::from_bytes`'s closure meets its contract

`fromBytes_spec`: rustc's x86-64 closure, placed anywhere in a program whose `memcpy` meets its
contract, meets `FromBytesPre`/`FromBytesPost` (`NativeRustcX64.Spec.FromBytes`): the pushes and
the randomizer (`head`), the loop over the chain values (`loop`), their `memcpy` (`mid`), the path
(`path`), the output's two `memcpy`s, the pops and the return (`tail`). The bounds checks never
fail: the cursor is at most `1204`. With Lean's three axioms only.
-/

namespace NativeRustcX64.Xmss.FromBytes

/-- **`from_bytes`'s closure meets its contract.** -/
public theorem fromBytes_spec [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (label "memcpy") MemcpyPre MemcpyPost) :
    Spec (label fromBytesLabel) FromBytesPre FromBytesPost := by
  intro m₀ hpre
  have P := pre_of hpre
  rw [hp.label (j := 0) (by decide +kernel), Nat.add_zero]
  exact head hp hpre fun st hpc h =>
    NativeRustcX64.Eventually.bind (loop hp P hpc h) fun st' ⟨hpc', h'⟩ =>
      mid hp hmemcpy P hpc' h' fun st'' hpc'' h'' =>
        path hp P hpc'' h'' fun s hs hret hc => tail hp hmemcpy P hs hret hc

/--
info: 'NativeRustcX64.Xmss.FromBytes.fromBytes_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fromBytes_spec

end NativeRustcX64.Xmss.FromBytes
