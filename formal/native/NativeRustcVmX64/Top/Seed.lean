module

public import NativeRustcVmX64.Top.Seed.Stage2

/-!
# `seed` on x86-64

**`seed_spec`**: rustc's `seed`, placed anywhere in the program, meets its contract (`SeedPre`,
`SeedPost`) given the contracts of `keccak256_words::<fiat_shamir_iv's closure>`, `memset`,
`keccak_f` and `memcpy`. Its 240-byte frame (R15, R14, RBX pushed at its bytes 216 to 239) holds the
state from its byte 16: the IV (`keccak256_words`), zeros (`memset`; `stage1`), the public input
(`b2`); `keccak_f` permutes it in place and `memcpy` copies it to the output, `b4` restores the
registers (`stage2`).
-/

namespace NativeRustcVmX64.Top.Seed

open NativeRustcX64 NativeRustcVmX64.Vm.Seed

public section

variable [Host] {k : Nat}

/-- **`seed` meets its contract.** -/
theorem seed_spec (hp : Placed code k)
    (hkiv : Spec (Labels.label keccak256WordsIvLabel) Keccak256WordsIvPre Keccak256WordsIvPost)
    (hmemset : Spec (Labels.label "memset") MemsetPre MemsetPost)
    (hkf : Spec (Labels.label keccakFLabel) KeccakFPre KeccakFPost)
    (hmemcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost) :
    Spec (Labels.label seedLabel) SeedPre SeedPost := by
  intro m0 hpre
  unfold seedLabel
  rw [hp.label (j := 0) rfl]
  exact Eventually.bind (stage1 hp hkiv hmemset hpre) fun st ⟨hpc, hS1⟩ ↦
    stage2 hp hkf hmemcpy hpre hpc hS1

end

end NativeRustcVmX64.Top.Seed
