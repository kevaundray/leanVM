module

public import NativeRustcX64.Sym

/-!
# The frame's symbolic state

`frameS k`: the frame with the return address and the stack arguments (region 0, 2784 bytes from
the base), the 8 bytes below it where a call pushes its return address (region 1, reached by the
alias `ptr 0 (-8)`), RSP the base, the registers `k` known. Kept apart so the executor's runs can
use it at compile time.
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustcX64.Sym

@[expose] public section

/-- The frame (region 0) and the call's return slot (region 1), RSP the base, the registers `k`,
the `extra` regions, bounds and aliases. -/
def frameS (k : List (Reg64 × Sym)) (extra : List Nat := []) (bounds : List (Sym × Nat) := [])
    (aliases : List (Sym × Nat × Int) := []) : SState :=
  init (2784 :: 8 :: extra) ((.rsp, .ptr 0 0) :: k) [] bounds ((.ptr 0 (-8), (1, 0)) :: aliases)

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

end

end NativeRustcX64.WotsLeafProof
