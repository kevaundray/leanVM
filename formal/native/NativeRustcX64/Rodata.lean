module

public import NativeRustcX64.Code.Sphincs.Names
public import NativeRustcX64.Code.Xmss.Names

public import NativeRustcX64.Data
public import NativeRustcX64.Code.Xmss
public import NativeRustcX64.Code.Sphincs
public import NativeRustcX64.Spec.Keccak
public import NativeRustcX64.SphincsVerify.Basic

/-!
# The read-only data the signature verifiers' end theorems assume

`XmssVerifier.verify_correct` assumes the round constants `rcBytes` at `NativeRustcX64.Xmss.Symbols.rodata0Label` (`RcAt`), and
`SphincsVerifier.verify_correct` those and `LAYER_HEIGHTS`' `lhBytes` at `NativeRustcX64.Sphincs.Symbols.rodata7Label`. These are the
bytes the ingested programs' data hold at those labels, so a loader placing the program's data
there meets the assumption.
-/

namespace NativeRustcX64

set_option Elab.async false

public theorem Xmss.rc_data : dataAt NativeRustcX64.Xmss.Symbols.rodata0Label Xmss.rodata = some rcBytes := by
  decide +kernel

public theorem Sphincs.rc_data : dataAt NativeRustcX64.Xmss.Symbols.rodata0Label Sphincs.rodata = some rcBytes := by
  decide +kernel

public theorem Sphincs.lh_data :
    dataAt NativeRustcX64.Sphincs.Symbols.rodata7Label Sphincs.rodata = some SphincsVerifyProof.lhBytes := by
  decide +kernel

end NativeRustcX64
