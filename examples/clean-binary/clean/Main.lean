module

public import Gf2.R1CS
public import Gf2.Inputs
public import Gf2.Xmss.Inputs
public import Gf2.Xmss.Witness
-- Keeps the reference-vector checks in the executable's build.
public import Gf2.Check
public import Gf2.Xmss.Check

@[expose] public section

open Gf2

def usage : String :=
  "usage: clean_export r1cs <out.r1cs>\n" ++
  "       clean_export witness <inputs.json> <out.bin>\n" ++
  "       clean_export xmss-r1cs <out.r1cs>\n" ++
  "       clean_export xmss-witness <inputs.json> <out.bin>"

def orFail {α : Type} (context : String) : Except String α → IO α
  | .ok a => pure a
  | .error msg => throw (IO.userError s!"{context}: {msg}")

def printStats (out : String) (s : R1CS.Stats) : IO Unit :=
  IO.println s!"{out}: {s.constraints} constraints, {s.signals} signals, \
    nnz A {s.nnzA}, B {s.nnzB}, C {s.nnzC}"

def main (args : List String) : IO Unit := do
  match args with
  | ["r1cs", out] =>
    let ex ← orFail "export" (R1CS.toCLB1 Blake2s.nPublic Blake2s.ops)
    IO.FS.writeBinFile out ex.body
    printStats out ex.stats
  | ["witness", inputs, out] =>
    let instances ← orFail s!"invalid {inputs}" (Inputs.parse (← IO.FS.readFile inputs))
    let ops := Blake2s.ops
    let signals := 1 + Operations.localLength ops
    IO.FS.withFile out .write fun h => do
      h.write (R1CS.witnessHeader signals instances.size)
      for x in instances do
        h.write (R1CS.packWitness (witgen (Blake2s.inputHint (Blake2s.inputBits x.h x.m)) ops))
    IO.println s!"{out}: {instances.size} instances, {signals} signals"
  | ["xmss-r1cs", out] =>
    let _ ← orFail "xmss block" Xmss.Block.build
    let ex ← orFail "export" (R1CS.toCLB2 0 Xmss.Block.links Xmss.Block.ops)
    IO.FS.writeBinFile out ex.body
    printStats out ex.stats
    IO.println s!"{out}: {Xmss.Block.links.size} link pairs, {Xmss.Block.nRoles} roles"
  | ["xmss-witness", inputs, out] =>
    let groups ← orFail s!"invalid {inputs}" (Xmss.Inputs.parse (← IO.FS.readFile inputs))
    let _ ← orFail "xmss block" Xmss.Block.build
    let ss := Xmss.Witness.steps groups
    let signals := 1 + Operations.localLength Xmss.Block.ops
    let nSigs := groups.foldl (· + ·.signers.size) 0
    let bad ← IO.FS.withFile out .write fun h => do
      h.write (R1CS.witnessHeader signals ss.size)
      Xmss.Witness.foldWitnesses ss 0 fun bad _ _ w => do
        h.write (R1CS.packWitness w)
        return if (Xmss.Witness.violations w).isEmpty then bad else bad + 1
    IO.println s!"{out}: {ss.size} instances ({nSigs} signatures, {groups.size} groups), \
      {signals} signals"
    unless bad == 0 do IO.eprintln s!"{out}: {bad} instances violate a constraint"
  | _ => throw (IO.userError usage)
