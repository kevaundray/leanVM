module

public import NativeRustcX64.Sym.Basic

/-!
# The frame's symbolic state (x86-64)

`frameS k`: region 0 the frame with the return address (29392 bytes, RSP its base), region 1 the
16 bytes below it where `call` and `push` write (`ptr 0 (-8)`, `ptr 0 (-16)`, as
`Run.frameAliases`), the registers `k` known.
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustcX64.Sym

@[expose] public section

/-- The frame's symbolic state: RSP its base, the registers `k`. -/
def frameS (k : List (Reg64 × Sym)) : SState :=
  init [29392, 16] ((.rsp, .ptr 0 0) :: k) [] [] [(.ptr 0 (-8), 1, 8), (.ptr 0 (-16), 1, 0)]

end

end NativeRustcX64.SphincsVerifyProof.Digest
