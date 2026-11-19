module

public import NativeRustcX64.FromBytes.Inv
meta import NativeRustcX64.FromBytes.Inv
meta import NativeRustcX64.Code.Xmss.FromBytes

/-!
# `from_bytes`'s closure: the last blocks, symbolically

Block 23 (`stT0` to `stT1`; region 0 the stack, RSP its offset 8, region 1 the output, RBX its
start): the randomizer to `out + 1184`, the call `memcpy(out + 256, stack + 952, 928)`. Block 24
(`stE0` to `stE1`; region 0 the stack): the pops of the callee-saved registers and the return to
the address at stack offset 1920.
-/

namespace NativeRustcX64.Xmss.FromBytes

open NativeRustcX64.Sym

set_option Elab.async false

/-- The symbolic state at block 23. -/
@[expose] public def stT0 : SState := init [1928, 1200] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

sym_block b23_execT := exec b23 stT0

/-- After block 23. -/
@[expose] public def stT1 : SState := ((exec b23 stT0).getD (stT0, .fall)).1

public theorem stT1_facts : stT1.reg .rdi = some (.ptr 1 256) ∧
    stT1.reg .rsi = some (.ptr 0 952) ∧ stT1.reg .rdx = some (.lit 928) ∧
    stT1.reg .rsp = some (.ptr 0 0) ∧ stT1.reg .rbp = some (.reg .rbp) ∧
    writesBelow stT1 [(0, 8), (1, 1200)] = true ∧ firstOverlap 0 952 928 stT1.mem = none ∧
    (∀ j < 5, firstOverlap 0 (1880 + 8 * j) 8 stT1.mem = none) ∧
    firstOverlap 1 0 256 stT1.mem = none := by decide +kernel

public theorem stT1_rand : ∀ t < 16,
    findWrite 1 (1184 + t) stT1.mem = some (.load 0 (8 + 8 * (t / 8)) 8, t % 8) := by
  decide +kernel

/-- The symbolic state at block 24. -/
@[expose] public def stE0 : SState := init [1928] [(.rsp, .ptr 0 8)]

sym_block b24_execE := exec b24 stE0

/-- After block 24. -/
@[expose] public def stE1 : SState := ((exec b24 stE0).getD (stE0, .fall)).1

public theorem stE1_facts : stE1.mem = [] ∧ stE1.reg .rsp = some (.ptr 0 1928) ∧
    (∀ j < 5, stE1.reg (saveRegs.getD j .rax) = some (.load 0 (1880 + 8 * j) 8)) ∧
    stE1.reg .rbp = some (.reg .rbp) := by decide +kernel

end NativeRustcX64.Xmss.FromBytes
