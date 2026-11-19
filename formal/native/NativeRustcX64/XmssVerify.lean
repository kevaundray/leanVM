module

public import NativeRustcX64.XmssVerify.HeadRun
public import NativeRustcX64.XmssVerify.ParseRun
public import NativeRustcX64.XmssVerify.Layers

/-!
# `xmss_verify` meets its contract (x86-64)

`xmssVerify_spec`: `xmss_verify`, placed anywhere in a program whose callees meet their contracts,
meets `XmssVerifyPre`/`XmssVerifyPost` (`NativeRustcX64.Spec.XmssVerify`): the prologue (`head`),
the copy of the signature's words (`copy`), the parsing of the key and the layers (`parse`), the
bottom and top layers and the comparison with the key's root (`layers`).
-/

namespace NativeRustcX64.Xmss.XmssVerify

/-- A word of words' bytes in memory. -/
public theorem words_at {d : DataMem} {a : BitVec 64} (f : Nat → UInt64) :
    ∀ n, BytesAt d a (Native.Keccak.wordsBytes ((List.range n).map f)) →
      ∀ i < n, BytesAt d (a + BitVec.ofNat 64 (8 * i)) (LeanVM.Protocol.KeccakHash.wordBytes (f i))
  | 0, _, i, hi => absurd hi (by omega)
  | n + 1, h, i, hi => by
    rw [wordsBytes_map, List.range_succ, List.map_append, List.flatten_append] at h
    have hl : (((List.range n).map (LeanVM.Protocol.KeccakHash.wordBytes ∘ f)).flatten).length =
        8 * n := by
      rw [← wordsBytes_map, Native.Keccak.Proof.length_wordsBytes]
      simp
    by_cases hin : i < n
    · refine words_at f n ?_ i hin
      rw [wordsBytes_map]
      intro t ht
      rw [h t (by rw [List.length_append]; omega), List.getElem_append_left ht]
    · obtain rfl : i = n := by omega
      refine bytesAt_sub h fun t ht => ?_
      rw [List.getElem?_append_right (by omega), hl]
      simp

/-- **`xmss_verify` meets its contract.** -/
public theorem xmssVerify_spec [Host] {k : Nat} (hp : Placed code k) {w : Nat → UInt64}
    (hset : Spec (label "memset") MemsetPre MemsetPost)
    (hcpy : Spec (label "memcpy") MemcpyPre MemcpyPost)
    (hupd : Spec (label updateLabel) UpdatePre UpdatePost)
    (hfin : Spec (label finalizeLabel) FinalizePre FinalizePost)
    (hwots : Spec (label wotsLeafLabel) WotsLeafPre WotsLeafPost)
    (hfb : Spec (label fromBytesLabel) FromBytesPre FromBytesPost) :
    Spec (label "xmss_verify") (XmssVerifyPre w) (XmssVerifyPost w) := by
  intro m₀ hpre
  have P := pre_of hpre
  rw [hp.label (j := 0) (by decide +kernel), Nat.add_zero]
  exact head hp hset P fun st hpc h =>
    Eventually.bind (copy hp P hpc h) fun _ ⟨hpc', h'⟩ =>
      parse hp hfb P hpc' h' fun _ hpc'' h'' =>
        Eventually.mono (layers hp hset hcpy hupd hfin hwots P hpc'' h'')
          fun _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩

end NativeRustcX64.Xmss.XmssVerify
