module

public import Gf2.Inputs
public import Gf2.Xmss.Spec

/-!
Parsing of the XMSS `inputs.json` written by `binary-spartan gen-xmss`:
`{"groups":[{"leaf_index":u32,"message":"<64 hex>","signers":[{"root":"<32 hex>","pp":"<32 hex>",
"randomness":"<48 hex>","chain_tips":["<32 hex>" x42],"merkle_proof":["<32 hex>" x32]}]}]}`.
-/

@[expose] public section

namespace Gf2.Xmss.Inputs
open Lean (Json)
open Gf2.Inputs (hexDigit? key? array?)

def bytes? (path : String) (len : ℕ) (j : Json) : Except String ByteArray := do
  let .str s := j | throw s!"{path}: expected a string"
  let cs := s.toList
  unless cs.length == 2 * len do throw s!"{path}: expected {2 * len} hex digits"
  let digits ← cs.mapM fun c => (hexDigit? c).elim (throw s!"{path}: \"{s}\" is not hex") pure
  return ⟨((List.range len).map fun i => (16 * digits[2 * i]! + digits[2 * i + 1]!).toUInt8).toArray⟩

def list? (path : String) (n len : ℕ) (j : Json) : Except String (Array ByteArray) := do
  let xs ← array? path j
  unless xs.size == n do throw s!"{path}: expected {n} entries, got {xs.size}"
  xs.mapIdxM fun i x => bytes? s!"{path}[{i}]" len x

def signer? (path : String) (j : Json) : Except String Signer := do
  return {
    root := ← bytes? s!"{path}.root" 16 (← key? path j "root")
    pp := ← bytes? s!"{path}.pp" 16 (← key? path j "pp")
    randomness := ← bytes? s!"{path}.randomness" 24 (← key? path j "randomness")
    tips := ← list? s!"{path}.chain_tips" V 16 (← key? path j "chain_tips")
    proof := ← list? s!"{path}.merkle_proof" LOG_LIFETIME 16 (← key? path j "merkle_proof") }

def group? (path : String) (j : Json) : Except String Group := do
  let leaf ← (← key? path j "leaf_index").getNat?.mapError fun _ => s!"{path}.leaf_index: expected a u32"
  unless leaf < 2 ^ 32 do throw s!"{path}.leaf_index: {leaf} is not a u32"
  let signers ← array? s!"{path}.signers" (← key? path j "signers")
  if signers.isEmpty then throw s!"{path}.signers: empty"
  return {
    leaf
    message := ← bytes? s!"{path}.message" 32 (← key? path j "message")
    signers := ← signers.mapIdxM fun i x => signer? s!"{path}.signers[{i}]" x }

def parse (text : String) : Except String (Array Group) := do
  let j ← Json.parse text
  let groups ← array? "groups" (← key? "inputs" j "groups")
  if groups.isEmpty then throw "groups: empty"
  groups.mapIdxM fun i x => group? s!"groups[{i}]" x

end Gf2.Xmss.Inputs
