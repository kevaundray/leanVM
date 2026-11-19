module

public import NativeRustcX64.Sym
public import NativeRustcX64.Code.Common.KeccakF
public import NativeRustcX64.Spec.Keccak
public meta import NativeRustcX64.Code.Common.KeccakF
public meta import NativeRustcX64.Spec.Keccak

/-!
# `keccak_f`'s blocks, run by the symbolic executor (x86-64)

The three blocks of `keccak_f` (`NativeRustcX64.Common.KeccakF`), each run from a symbolic state
whose region 0 is the 248-byte frame from 240 below the entry's RSP (its last 8 bytes the return
address):

- the prologue `b0` (`prologue`), from the entry: RSP the frame's offset 240, RDI the state
  (region 1, 200 bytes); it pushes the callee-saved registers, loads the lanes into registers and
  frame slots and XORs the column parities;
- the round loop's body `b1` (`body`), from its head: RSP the frame's offset 128, the round counter
  at offset 152 (below 185), the round constants at their label (region 1);
- the epilogue `b2` (`epilogue`), from the loop's exit: RSP the frame's offset 128, the state
  pointer the frame's offset 160 holds the base of region 1 (the state).
-/

namespace NativeRustcX64.KeccakF

open NativeRustcX64.Sym

set_option Elab.async false

@[expose] public section

/-- The prologue's start. -/
def startPro : SState := init [248, 200] [(.rsp, .ptr 0 240), (.rdi, .ptr 1 0)]

/-- The loop head's. -/
def startBody : SState :=
  init [248, 192] [(.rsp, .ptr 0 128)] [(rcLabel, 1)] [(.load 0 152 8, 185)]

/-- The loop exit's. -/
def startEpi : SState := init [248, 200] [(.rsp, .ptr 0 128)] [] [] [(.load 0 160 8, 1, 0)]

end

sym_block prologue := exec Common.KeccakF.b0 startPro

sym_block body := exec Common.KeccakF.b1 startBody

sym_block epilogue := exec Common.KeccakF.b2 startEpi

end NativeRustcX64.KeccakF
