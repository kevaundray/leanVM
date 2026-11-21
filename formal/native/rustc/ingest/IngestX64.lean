module

import IngestCore
import Kraken.X64.Parser

/-!
# `ingest-x64`

`ingest-x64 OUT SCHEME=FILE.s ...`: rustc's x86-64 assembly as the modules `NativeRustcX64.Code.*`
(`IngestCore`): raw for the signature verifiers, and for the leanVM verifier as `rustc/x86-postpass.py`
rewrites it (`rustc/vm/out/vm-x86_64.post.s`) until its proofs move to the raw assembly. Loop
alignment inside a function, `.p2align n`, is kept as Kraken's `.align 2^n` (padding that is never run
but moves what follows); the panic entries become `ud2`.
-/

open Ingest

/-- x86-64. -/
def x64 : Arch Instr ConstExpr where
  ns := "NativeRustcX64"
  syntaxModule := "Kraken.X64.Syntax"
  infixModule := "NativeRustcArm.Code.Infix"
  parse := Kraken.X64.Parser.parse
  labelConst := .label
  endsBlock
    | .regular _ _ (.jcc _ _) | .regular _ _ (.jmp _) | .regular _ _ (.call _) | .regular _ _ .ret => true
    | _ => false
  comment := "#"
  bodyDirective l :=
    if l.startsWith ".cfi_" then pure none
    else match l.splitOn " " with
      | [".p2align", n] => match n.toNat? with
        | some k => pure (some s!".align {2 ^ k}")
        | none => throw s!"unexpected directive {l}"
      | _ => throw s!"unexpected directive {l}"
  trap := #[0x0f, 0x0b]
  trapAsm := "ud2"
  dataSize d := match d with
    | ".byte" => some 1 | ".short" | ".value" | ".word" => some 2 | ".long" => some 4 | ".quad" => some 8
    | _ => none
  wordDirective n := match n with | 1 => ".byte" | 2 => ".short" | 4 => ".long" | _ => ".quad"

public def main (args : List String) : IO UInt32 := run x64 args
