module

public import NativeRustcArm.FromBytes.Inv
meta import NativeRustcArm.Code.Xmss.FromBytes

/-!
# `from_bytes`'s closure: the path's blocks, symbolically

Blocks 5 to 21 from one symbolic state (`stP0`): region 0 the frame (SP its base), 1 the cursor
(`X21`), 2 the layer's 1200 bytes of the signature from the cursor's value `pos`; the addresses of
the path nodes, `X20 + X23` and `X20 + (X22 + 32 + 16 j)`, are aliases into region 2 (`X22` is
`pos + 928`, `X23` is `pos + 944`). The states after each block (`stP1` to `stP17`) and what the
last one holds: the 16 path nodes in the frame from `944`, the cursor `X22 + 272`, the call
`memcpy(X19, frame + 944, 256)`, no write over the chain values, the saved registers or the
randomizer.
-/

namespace NativeRustcArm.Xmss.FromBytes

open NativeRustcArm.Sym

set_option Elab.async false

@[expose] public section

/-- The path nodes' addresses as aliases into the layer's bytes. -/
def pathAliases : List (Sym × Nat × Int) :=
  (.bin .add .W64 (.reg .X20) (.reg .X23), (2, ((944 : Nat) : Int))) :: (List.range 15).map fun j =>
    (.bin .add .W64 (.reg .X20) (.bin .add .W64 (.reg .X22) (.lit (32 + 16 * j))),
      (2, ((960 + 16 * j : Nat) : Int)))

/-- The symbolic state at block 5. -/
def stP0 : SState := init [(1936, true), (8, false), (1200, false)] (.ptr 0 0) [(.X21, .ptr 1 0)]
  (aliases := pathAliases)

sym_block b5_execP := exec b5 stP0

/-- The symbolic state after block 5. -/
def stP1 : SState := ((exec b5 stP0).getD (stP0, .fall)).1

sym_block b6_execP := exec b6 stP1

/-- The symbolic state after block 6. -/
def stP2 : SState := ((exec b6 stP1).getD (stP1, .fall)).1

sym_block b7_execP := exec b7 stP2

/-- The symbolic state after block 7. -/
def stP3 : SState := ((exec b7 stP2).getD (stP2, .fall)).1

sym_block b8_execP := exec b8 stP3

/-- The symbolic state after block 8. -/
def stP4 : SState := ((exec b8 stP3).getD (stP3, .fall)).1

sym_block b9_execP := exec b9 stP4

/-- The symbolic state after block 9. -/
def stP5 : SState := ((exec b9 stP4).getD (stP4, .fall)).1

sym_block b10_execP := exec b10 stP5

/-- The symbolic state after block 10. -/
def stP6 : SState := ((exec b10 stP5).getD (stP5, .fall)).1

sym_block b11_execP := exec b11 stP6

/-- The symbolic state after block 11. -/
def stP7 : SState := ((exec b11 stP6).getD (stP6, .fall)).1

sym_block b12_execP := exec b12 stP7

/-- The symbolic state after block 12. -/
def stP8 : SState := ((exec b12 stP7).getD (stP7, .fall)).1

sym_block b13_execP := exec b13 stP8

/-- The symbolic state after block 13. -/
def stP9 : SState := ((exec b13 stP8).getD (stP8, .fall)).1

sym_block b14_execP := exec b14 stP9

/-- The symbolic state after block 14. -/
def stP10 : SState := ((exec b14 stP9).getD (stP9, .fall)).1

sym_block b15_execP := exec b15 stP10

/-- The symbolic state after block 15. -/
def stP11 : SState := ((exec b15 stP10).getD (stP10, .fall)).1

sym_block b16_execP := exec b16 stP11

/-- The symbolic state after block 16. -/
def stP12 : SState := ((exec b16 stP11).getD (stP11, .fall)).1

sym_block b17_execP := exec b17 stP12

/-- The symbolic state after block 17. -/
def stP13 : SState := ((exec b17 stP12).getD (stP12, .fall)).1

sym_block b18_execP := exec b18 stP13

/-- The symbolic state after block 18. -/
def stP14 : SState := ((exec b18 stP13).getD (stP13, .fall)).1

sym_block b19_execP := exec b19 stP14

/-- The symbolic state after block 19. -/
def stP15 : SState := ((exec b19 stP14).getD (stP14, .fall)).1

sym_block b20_execP := exec b20 stP15

/-- The symbolic state after block 20. -/
def stP16 : SState := ((exec b20 stP15).getD (stP15, .fall)).1

sym_block b21_execP := exec b21 stP16

/-- The symbolic state after block 21. -/
def stP17 : SState := ((exec b21 stP16).getD (stP16, .fall)).1

theorem stP17_path : ∀ j < 16, ∀ t < 16, findWrite 0 (944 + 16 * j + t) stP17.mem =
    some (.load 2 (944 + 16 * j + 8 * (t / 8)) 8, t % 8) := by decide +kernel

theorem stP17_cursor : ∀ t < 8,
    findWrite 1 (0 + t) stP17.mem = some (.bin .add .W64 (.reg .X22) (.lit 272), t) := by
  decide +kernel

theorem stP17_chain : firstOverlap 0 16 928 stP17.mem = none := by decide +kernel

theorem stP17_save : ∀ j < 8, firstOverlap 0 (1872 + 8 * j) 8 stP17.mem = none := by decide +kernel

theorem stP17_rand : firstOverlap 0 0 16 stP17.mem = none := by decide +kernel

theorem stP17_writes : writesIn stP17 [0, 1] = true := by decide +kernel

theorem stP17_keeps : keeps stP0 stP17 = true := by decide +kernel

theorem stP17_regs : stP17.reg .X0 = some (.reg .X19) ∧ stP17.reg .X1 = some (.ptr 0 944) ∧
    stP17.reg .X2 = some (.lit 256) := by decide +kernel

end

end NativeRustcArm.Xmss.FromBytes
