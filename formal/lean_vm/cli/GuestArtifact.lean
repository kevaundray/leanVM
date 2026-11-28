import LeanVM.Dsl.Gen.Checks
import LeanVM.Dsl.Program
import LeanVM.Guest.Data.Placeholders
import LeanVM.Compiler.Lines
import LeanVM.Core.Text
import Statement.Keccak
import Statement.LeanVmVerifier

/-!
# `guest-artifact`: the guest the Rust prover loads

Run from `lean_vm`.

* `lake exe guest-artifact FILE` elaborates the guest (the program list
  `LeanVM.Guest.Program.program`, `Dsl.Program.assemble`, its constants read from the placeholders
  at `Placeholders.bytecodeLog`), compiles it with `Compiler.compileTraced` and writes `FILE`, the
  repository's `guests/lean_ethereum.compiled`: an `input` line, the digest of what it was compiled
  from (`inputDigest`); an `iv` line, the program's Fiat-Shamir IV (`fiatShamirIv` of its
  `bytecodeWords`, the statement's `deployedSeed`); then the program in the line format of
  `crates/isa/src/text.rs` (`Compiler.render`), and the source line of each instruction (`L` lines,
  `Compiler.renderLines`, from the line pass `Compiler.Lines.compileLines`).
  `crates/aggregation/src/guest.rs` loads it and checks both header lines against what it
  compiles and proves.
* `lake exe guest-artifact FILE --digest DIGEST` also writes the program's core digest
  (`Text.coreDigest`, in hexadecimal) to `DIGEST`, the repository's committed
  `guests/lean_ethereum.digest`, which `guest.rs` includes; `scripts/regen-guest.sh` passes it,
  `crates/aggregation/build.rs` does not, so a build after a change to the guest that was not
  regenerated refuses the artefact.
* With `--check` it writes nothing and fails when `FILE` (or `DIGEST`) differs.

The input digest is Keccak-256 of the program's core digest and the placeholders'
(`Placeholders.digest`), each 32 bytes, as `guest.rs`'s `input_digest` computes it from the
committed core digest and its own placeholders: so the prover refuses an artefact compiled from
another guest, or at other placeholders, than the committed digest and its configuration name.

The guest is compiled at the fixed point on its own size: its placeholders are computed for a log
size, and the program must have that many slots. When it does not, nothing is written or checked,
the program's log size is printed as `log size N`, and the exit code is `3`;
`scripts/guest-artifact` then exports the placeholders at that size and runs this again.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest
  LeanVM.Compiler LeanVM.Core

namespace GuestArtifact

/-- The bytes a string of hexadecimal digits spells, two digits each. -/
def unhex (s : String) : List UInt8 :=
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
  let rec go : List Char → List UInt8
    | a :: b :: rest => (digit a * 16 + digit b).toUInt8 :: go rest
    | _ => []
  go s.toList

/-- The input digest of the program `P`: Keccak-256 of its core digest and the placeholders'. -/
def inputDigest (P : Core.Program) : String :=
  Text.hex (KeccakHash.digestBytes
    (keccak256 (KeccakHash.digestBytes (Text.coreDigest P) ++ unhex Placeholders.digest)))

/-- The Fiat-Shamir IV of the program of `2^logSize` slots holding `c`'s code, padded. -/
def iv (c : Assembled) (logSize : Nat) (h : logSize ≤ maxLogBytecode) : Digest :=
  let code : Array LeanIsaInstruction := Array.ofFn fun i : Fin (2 ^ logSize) ↦
    (c.code.getD i.val .padding).toLeanIsaInstruction
  fiatShamirIv (bytecodeWords ⟨logSize, h, fun i ↦ code[i.val]'(by simp [code])⟩)

/-- A file's text, `""` when there is none. -/
def readOr (file : String) : IO String := do
  if ← System.FilePath.pathExists file then IO.FS.readFile file else pure ""

def run (file : String) (digestFile : Option String) (checkOnly : Bool) : IO UInt32 := do
  let fns ← match Dsl.Program.assemble LeanVM.Dsl.Gen.Checks.checks with
    | .ok fns => pure fns
    | .error e => throw (IO.userError s!"the guest does not elaborate: {e}")
  let (c, lines) ← match Lines.compileLines fns with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"the guest does not compile: {e}")
  let logSize := c.size.log2
  if c.size != 2 ^ Placeholders.bytecodeLog then
    IO.println s!"log size {logSize}"
    IO.eprintln s!"not at the fixed point: compiled with the placeholders at 2^{Placeholders.bytecodeLog}, \
      the guest has {c.size} slots; export the placeholders at {logSize} (`scripts/guest-artifact` does)"
    return 3
  if h : logSize > maxLogBytecode then
    throw (IO.userError s!"the guest's {c.size} slots exceed the ISA's")
  else
  let core := fns.map (·.1.core)
  let text := s!"input {inputDigest core}\n\
    iv {Text.hex (iv c logSize (Nat.le_of_not_gt h)).toBytes.toList}\n" ++ render c ++ renderLines lines
  let digest := Text.hex (KeccakHash.digestBytes (Text.coreDigest core)) ++ "\n"
  let outputs := (file, text) :: digestFile.toList.map (·, digest)
  if checkOnly then
    let mut ok := true
    for (path, t) in outputs do
      if (← readOr path) == t then IO.println s!"{path} is current"
      else
        IO.eprintln s!"{path} is stale: run `scripts/guest-artifact --digest`"
        ok := false
    return if ok then 0 else 1
  -- Unchanged, nothing is written again: a build that watches it (`crates/aggregation/build.rs`) reruns only on a change.
  for (path, t) in outputs do
    if (← readOr path) != t then IO.FS.writeFile path t
  IO.println s!"{file}: {c.code.size} instructions in {c.fns.size} functions, size 2^{logSize}, \
    main frame {c.mainFrame}"
  return 0

end GuestArtifact

def main (args : List String) : IO UInt32 := do
  let checkOnly := args.contains "--check"
  match args.filter (· != "--check") with
  | [file] => GuestArtifact.run file none checkOnly
  | [file, "--digest", digest] => GuestArtifact.run file (some digest) checkOnly
  | _ =>
      IO.eprintln "usage: guest-artifact FILE [--digest DIGEST] [--check]"
      return 2
