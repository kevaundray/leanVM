module

public import NativeRustcX64.Data
public import NativeRustcX64.Code.Xmss
public import NativeRustcX64.Code.Sphincs
public import NativeRustcX64.Spec.Keccak
public import NativeRustcX64.SphincsVerify.Basic

/-!
# The read-only data the signature verifiers' end theorems assume

`XmssVerifier.verify_correct` assumes the round constants `rcBytes` at `rcLabel` (`RcAt`), and
`SphincsVerifier.verify_correct` those and `LAYER_HEIGHTS`' `lhBytes` at `lhLabel`. These are the
bytes the ingested programs' data hold at those labels, so a loader placing the program's data
there meets the assumption.
-/

namespace NativeRustcX64

set_option Elab.async false

public theorem Xmss.rc_data : dataAt rcLabel Xmss.rodata = some rcBytes := by
  decide +kernel

public theorem Sphincs.rc_data : dataAt rcLabel Sphincs.rodata = some rcBytes := by
  decide +kernel

public theorem Sphincs.lh_data :
    dataAt SphincsVerifyProof.lhLabel Sphincs.rodata = some SphincsVerifyProof.lhBytes := by
  decide +kernel

end NativeRustcX64
