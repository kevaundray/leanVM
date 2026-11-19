module

public import NativeRustcX64.FromBytes.Inv
meta import NativeRustcX64.FromBytes.Inv
meta import NativeRustcX64.Code.Xmss.FromBytes

/-!
# `from_bytes`'s closure: the path's blocks, symbolically

Blocks 6 to 22 from one symbolic state (`stP0`): region 0 the stack (RSP its offset 8), 1 the
cursor (R15), 2 the layer's 1200 bytes of the signature from the cursor's value `pos`; the
addresses of the path nodes, `r14 + r12` and `r14 + (r13 + 48 + 16 j)`, are aliases into region 2
(`r12` is `pos + 944`, `r13` is `pos + 912`). The states after each block (`stP1` to `stP17`) and
what the last one holds: the 16 path nodes in the frame from stack offset 24, the cursor
`r13 + 288`, the call `memcpy(rbx, stack + 24, 256)` with its return address at stack offset 0, no
write over the chain values, the pushed registers or the randomizer.
-/

namespace NativeRustcX64.Xmss.FromBytes

open NativeRustcX64.Sym

set_option Elab.async false

/-- The aliases of the path nodes' addresses. -/
@[expose] public def pathAliases : List (Sym × Nat × Int) :=
  (.bin .add .W64 (.reg .r14) (.reg .r12), (2, 944)) ::
    (List.range 15).map fun j =>
      (.bin .add .W64 (.reg .r14) (.bin .add .W64 (.reg .r13) (.lit (48 + 16 * j))),
        (2, (960 + 16 * j : Nat)))

/-- The symbolic state after the first `memcpy`. -/
@[expose] public def stP0 : SState :=
  init [1928, 8, 1200] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)] [] [] pathAliases

sym_block b6_execP := exec b6 stP0

/-- After block 6. -/
@[expose] public def stP1 : SState := ((exec b6 stP0).getD (stP0, .fall)).1

sym_block b7_execP := exec b7 stP1

/-- After block 7. -/
@[expose] public def stP2 : SState := ((exec b7 stP1).getD (stP1, .fall)).1

sym_block b8_execP := exec b8 stP2

/-- After block 8. -/
@[expose] public def stP3 : SState := ((exec b8 stP2).getD (stP2, .fall)).1

sym_block b9_execP := exec b9 stP3

/-- After block 9. -/
@[expose] public def stP4 : SState := ((exec b9 stP3).getD (stP3, .fall)).1

sym_block b10_execP := exec b10 stP4

/-- After block 10. -/
@[expose] public def stP5 : SState := ((exec b10 stP4).getD (stP4, .fall)).1

sym_block b11_execP := exec b11 stP5

/-- After block 11. -/
@[expose] public def stP6 : SState := ((exec b11 stP5).getD (stP5, .fall)).1

sym_block b12_execP := exec b12 stP6

/-- After block 12. -/
@[expose] public def stP7 : SState := ((exec b12 stP6).getD (stP6, .fall)).1

sym_block b13_execP := exec b13 stP7

/-- After block 13. -/
@[expose] public def stP8 : SState := ((exec b13 stP7).getD (stP7, .fall)).1

sym_block b14_execP := exec b14 stP8

/-- After block 14. -/
@[expose] public def stP9 : SState := ((exec b14 stP8).getD (stP8, .fall)).1

sym_block b15_execP := exec b15 stP9

/-- After block 15. -/
@[expose] public def stP10 : SState := ((exec b15 stP9).getD (stP9, .fall)).1

sym_block b16_execP := exec b16 stP10

/-- After block 16. -/
@[expose] public def stP11 : SState := ((exec b16 stP10).getD (stP10, .fall)).1

sym_block b17_execP := exec b17 stP11

/-- After block 17. -/
@[expose] public def stP12 : SState := ((exec b17 stP11).getD (stP11, .fall)).1

sym_block b18_execP := exec b18 stP12

/-- After block 18. -/
@[expose] public def stP13 : SState := ((exec b18 stP12).getD (stP12, .fall)).1

sym_block b19_execP := exec b19 stP13

/-- After block 19. -/
@[expose] public def stP14 : SState := ((exec b19 stP13).getD (stP13, .fall)).1

sym_block b20_execP := exec b20 stP14

/-- After block 20. -/
@[expose] public def stP15 : SState := ((exec b20 stP14).getD (stP14, .fall)).1

sym_block b21_execP := exec b21 stP15

/-- After block 21. -/
@[expose] public def stP16 : SState := ((exec b21 stP15).getD (stP15, .fall)).1

sym_block b22_execP := exec b22 stP16

/-- After block 22. -/
@[expose] public def stP17 : SState := ((exec b22 stP16).getD (stP16, .fall)).1

public theorem stP17_regs : stP17.reg .rdi = some (.reg .rbx) ∧ stP17.reg .rsi = some (.ptr 0 24) ∧
    stP17.reg .rdx = some (.lit 256) ∧ stP17.reg .rsp = some (.ptr 0 0) ∧
    stP17.reg .rbx = some (.reg .rbx) ∧ stP17.reg .r15 = some (.ptr 1 0) ∧
    stP17.reg .rbp = some (.reg .rbp) := by decide +kernel

public theorem stP17_path : ∀ t < 256,
    findWrite 0 (24 + t) stP17.mem = some (.load 2 (944 + 8 * (t / 8)) 8, t % 8) := by
  decide +kernel

public theorem stP17_cursor : ∀ t < 8,
    findWrite 1 (0 + t) stP17.mem = some (.bin .add .W64 (.reg .r13) (.lit 288), t) := by
  decide +kernel

public theorem stP17_writes : writesBelow stP17 [(0, 280), (1, 8)] = true := by decide +kernel

public theorem stP17_rand : firstOverlap 0 8 16 stP17.mem = none := by decide +kernel

public theorem stP17_chain : firstOverlap 0 952 928 stP17.mem = none := by decide +kernel

public theorem stP17_save : ∀ j < 5, firstOverlap 0 (1880 + 8 * j) 8 stP17.mem = none := by
  decide +kernel

public theorem stP17_keeps : stP17.reg .r15 = some (.ptr 1 0) ∧ stP17.reg .rbp = some (.reg .rbp) ∧
    stP17.reg .rbx = some (.reg .rbx) := by decide +kernel

public theorem stP17_retAddr : ∀ t < 8, findWrite 0 (0 + t) stP17.mem = some (.retAddr, t) := by
  decide +kernel

end NativeRustcX64.Xmss.FromBytes
