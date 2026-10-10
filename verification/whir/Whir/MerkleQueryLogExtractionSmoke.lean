import Whir.PCSBCSMerkleRootCache

/-! Native executable smoke: actual BLAKE2s compression records, including a
multiblock occupied row, repeated registration, tampering, absence, malformed
bytes, and an explicit inconsistent-output record set. No native_decide proof. -/
namespace Whir.MerkleQueryLogExtractionSmoke
open Concrete FiatShamirGame DuplexModeGame PublicMerkleLog
open MerkleQueryLogExtraction PCSBCSMerkleQueryLog

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def smoke : IO Unit := do
  let left : List K := (List.range 9).map fun n => UInt64.ofNat (n+1)
  let right : List K := (List.range 9).map fun n => UInt64.ofNat (n+21)
  let lb := ByteCodec.wordsBytes left
  let rb := ByteCodec.wordsBytes right
  let ld := hashBlake2s lb
  let rd := hashBlake2s rb
  let pb := List.ofFn (ByteCodec.pairBytes (ld,rd))
  let root := hashBlake2s pb
  let honest := plan blake2sOracle lb ++ plan blake2sOracle rb ++ plan blake2sOracle pb
  let table := rawRoot0 honest root 1 9
  require (table.toList.map Array.toList == [left,right]) "honest full Root0 rows differ"
  require ((root0Consumer 9 16 table)[0]!.toList == left.reverse ++ List.replicate 7 0)
    "separate first-fold occupied-lane reversal/padding differs"
  let missing := plan blake2sOracle rb ++ plan blake2sOracle pb
  let mt := fromPublic missing root 1
  require (mt.get [false] == none && mt.get [true] == some right)
    "missing preimage was forged or available sibling was lost"
  require ((rawRoot0 missing root 1 9).toList.map Array.toList ==
    [List.replicate 9 0,right]) "explicit absence default or full table order differs"
  require ((rawRoot0 honest root 1 8).toList.map Array.toList ==
    [List.replicate 8 0,List.replicate 8 0]) "malformed width was not defaulted"
  let registry := PCSBCSMerkleRootCache.register ∅ honest root ⟨1,9⟩
  let repeated := PCSBCSMerkleRootCache.register registry missing root ⟨0,8⟩
  require ((repeated[key root]?).map (fun frozen => frozen.raw.toList.map Array.toList) ==
    some [left,right]) "first root registration was recomputed or replaced"
  let tampered : PublicLog := honest.map fun e =>
    if e.1 = node DuplexCompression.parameterIV 0 pb true then (e.1,ld) else e
  require ((fromPublic tampered root 1).get [false] == none)
    "tampered final root answer was accepted"
  require (decodeWords [0] == none && parsePair [0] == none)
    "malformed leaf/pair bytes were accepted"
  let collisionRecords : MerkleTransport.Commitments.Records := [(lb,ld),(rb,ld)]
  let indexed := build collisionRecords
  require (indexed[key ld]? == some lb) "first collision registration was not retained"
  require ((register indexed rb ld)[key ld]? == some lb) "cached registration was overwritten"
  require ((extract canonicalCodec indexed 0 ld).get [] == some left)
    "collision case was not deterministic"
  require ((fromPublic honest root 0).get [] != some left)
    "untagged digest depth was silently erased"
  IO.println "Merkle query-log extraction smoke PASS (honest/tampered/missing/malformed/collision/lane-order)"

end Whir.MerkleQueryLogExtractionSmoke

def main : IO Unit := Whir.MerkleQueryLogExtractionSmoke.smoke
