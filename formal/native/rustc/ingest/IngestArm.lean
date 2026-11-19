module

import IngestCore
import Kraken.AArch64.Parser

/-!
# `ingest-arm`

`ingest-arm OUT SCHEME=FILE.s ...`: rustc's AArch64 assembly (`rustc/out/<scheme>-aarch64.s`) as the
modules `NativeRustcArm.Code.*` (`IngestCore`). The panic entries become `udf #0`.
-/

open Ingest

/-- AArch64. -/
def arm : Arch Instr ConstExpr where
  ns := "NativeRustcArm"
  syntaxModule := "Kraken.AArch64.Syntax"
  infixModule := "NativeRustcArm.Code.Infix"
  parse := Kraken.AArch64.Parser.parse
  labelConst := .label
  endsBlock i := match i.operation_size, i.operation with
    | _, .B _ | _, .B_cond _ _ | _, .BL _ | _, .BLR _ | _, .BR _ | _, .RET _
    | _, .CBZ _ _ | _, .CBNZ _ _ | _, .TBZ _ _ _ | _, .TBNZ _ _ _ => true
    | _, _ => false
  comment := "//"
  bodyDirective l :=
    if l.startsWith ".cfi_" then pure none else throw s!"unexpected directive {l}"
  trap := #[0, 0, 0, 0]
  trapAsm := "udf #0"
  dataSize d := match d with
    | ".byte" => some 1 | ".hword" => some 2 | ".word" => some 4 | ".xword" => some 8 | _ => none
  wordDirective n := match n with | 1 => ".byte" | 2 => ".hword" | 4 => ".word" | _ => ".xword"

public def main (args : List String) : IO UInt32 := run arm args
