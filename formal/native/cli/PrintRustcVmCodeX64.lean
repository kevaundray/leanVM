module

import Kraken.X64.PrintATT
import NativeRustcVmX64.Code.Vm

/-!
# `print-rustc-vm-code-x64`

`lake exe print-rustc-vm-code-x64 vm FILE.s` writes the ingested rustc program of the leanVM verifier
for x86-64 (`NativeRustcVmX64.Vm.code`) as an assembly file, each directive printed by Kraken's AT&T
printer (`Kraken.X64.ATT.directive`), as `print-rustc-code-x64` does the signature verifiers'. Only sections are added: each function (a label
not starting with `.L`) opens a section `.text.<name>`, as rustc's do, and each data label of `rodata`
a section `.rodata.<label>` of its own. `rustc/ingest/faithful.sh` assembles the file and compares it
with rustc's assembly, assembled. (AArch64's is `print-rustc-code`, a separate executable: Kraken's two
architectures declare the same root names.)
-/

/-- The directives printed, each label for which `opens` gives a section directive opening it. -/
def printWithSections (ds : Program) (opens : String → Option String) : Except String String := do
  let mut out := ""
  let mut opened := false
  for d in ds do
    if let .label l := d then
      if let some s := opens l then
        out := out ++ s
        opened := true
    unless opened do throw "a directive before the first section"
    let indent := match d with | .label _ => "" | _ => "\t"
    out := out ++ indent ++ Kraken.X64.ATT.directive d ++ "\n"
  return out

/-- The assembly of `code`, whose last directives are `rodata`: a section `.text.<f>` at each label `f`
not starting with `.L` before `rodata`, a section `.rodata.<l>` at each label `l` of `rodata`. -/
def asmFile (code rodata : Program) : Except String String := do
  let n := code.length - rodata.length
  unless code.drop n == rodata do throw "the program does not end with its data"
  let text ← printWithSections (code.take n) fun l =>
    if l.startsWith ".L" then none else some s!"\t.section .text.{l},\"ax\",@progbits\n\t.p2align 4\n"
  let data ← printWithSections rodata fun l => some s!"\t.section .rodata.{l},\"a\",@progbits\n"
  return text ++ data

public def main (args : List String) : IO UInt32 := do
  let prog? : Option (Program × Program) := match args with
    | ["vm", _] => some (NativeRustcVmX64.Vm.code, NativeRustcVmX64.Vm.rodata)
    | _ => none
  match prog?, args with
  | some (code, rodata), [_, path] =>
    match asmFile code rodata with
    | .ok s => IO.FS.writeFile path s; return 0
    | .error e => IO.eprintln e; return 1
  | _, _ =>
    IO.eprintln "usage: print-rustc-vm-code-x64 vm FILE.s"
    return 2
