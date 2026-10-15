module

public import Gf2.Blake2s

/-!
Native reference for leanVM main's `crates/xmss` (verification only) and the signer-set digest of
`SIGNER_SET_AGGREGATION.md` §1.3, written from the byte strings the Rust code hashes, independently
of the circuit. Every hash is standard BLAKE2s-256 (`blake2s`), each compression of it
`Blake2s.compress`.
-/

@[expose] public section

namespace Gf2.Xmss

open Gf2.Blake2s (compress IV)

/-- BLAKE2s-256's initial chaining value: `IV` with the parameter block (32-byte digest, no key). -/
def IV0 : Array UInt32 := IV.set! 0 (IV[0]! ^^^ 0x01010020)

def byteAt (d : ByteArray) (i : ℕ) : UInt8 := if h : i < d.size then d[i] else 0

/-- Bit `i` of a byte string, LSB first within each byte. -/
def bitAt (d : ByteArray) (i : ℕ) : Bool := (byteAt d (i / 8) >>> (i % 8).toUInt8) &&& 1 == 1

/-- The 16 little-endian words of the 64-byte block at `off`, zero past the end. -/
def blockWords (d : ByteArray) (off : ℕ) : Array UInt32 :=
  Array.ofFn (n := 16) fun w => (List.range 4).foldl
    (fun x k => x ||| ((byteAt d (off + 4 * w.val + k)).toUInt32 <<< (8 * k).toUInt32)) 0

def le32 (x : ℕ) : ByteArray := ⟨Array.ofFn (n := 4) fun k => (x >>> (8 * k.val)).toUInt8⟩

def le64 (x : ℕ) : ByteArray := ⟨Array.ofFn (n := 8) fun k => (x >>> (8 * k.val)).toUInt8⟩

def wordsBytes (ws : Array UInt32) : ByteArray := ws.foldl (fun b w => b ++ le32 w.toNat) .empty

def zeros (n : ℕ) : ByteArray := ⟨Array.replicate n 0⟩

/-- Standard BLAKE2s-256: every block but the last at counter `64 (i + 1)`, the last (zero
padded, a single zero block for the empty string) final at the input length. -/
def blake2s (d : ByteArray) : ByteArray :=
  let blocks := max 1 ((d.size + 63) / 64)
  wordsBytes <| (List.range blocks).foldl (fun h b =>
    let last := b + 1 == blocks
    compress h (blockWords d (64 * b)) (if last then d.size.toUInt64 else (64 * (b + 1)).toUInt64)
      (if last then 0xFFFFFFFF else 0) 0) IV0

-- Scheme constants (`crates/xmss/src/lib.rs`, `hash.rs`).
def V : ℕ := 42
def CHAIN_LENGTH : ℕ := 8
def TARGET_SUM : ℕ := 195
def LOG_LIFETIME : ℕ := 32
def TWEAK_CHAIN : UInt8 := 1
def TWEAK_WOTS_PK : UInt8 := 2
def TWEAK_MERKLE : UInt8 := 3
def TWEAK_ENCODING : UInt8 := 4

/-- `[0 | type | 0 | 0 | sub_position (LE) | 0 0 0 0 | index (LE)]`. -/
def tweak (ty : UInt8) (sub index : ℕ) : ByteArray :=
  ⟨#[0, ty, 0, 0]⟩ ++ le32 sub ++ zeros 4 ++ le32 index

/-- BLAKE2s of `tweak | pp | payload`, truncated to 16 bytes. -/
def tweakHash (pp : ByteArray) (ty : UInt8) (sub index : ℕ) (payload : ByteArray) : ByteArray :=
  (blake2s (tweak ty sub index ++ pp ++ payload)).extract 0 16

structure Signer where
  root : ByteArray
  pp : ByteArray
  randomness : ByteArray
  tips : Array ByteArray
  proof : Array ByteArray
  deriving Inhabited

structure Group where
  leaf : ℕ
  message : ByteArray
  signers : Array Signer
  deriving Inhabited

/-- The encoding digest `D` of `wots_encode`. -/
def encodingDigest (msg : ByteArray) (leaf : ℕ) (pp rand : ByteArray) : ByteArray :=
  tweakHash pp TWEAK_ENCODING 0 leaf (msg ++ rand ++ zeros 8)

/-- Digit `i` of `D`: bits `3i` of word 0 for `i < 21`, bits `3 (i - 21)` of word 1 otherwise. -/
def digit (d : ByteArray) (i : ℕ) : ℕ :=
  let base := 64 * (i / 21) + 3 * (i % 21)
  (List.range 3).foldl (fun x b => if bitAt d (base + b) then x + 2 ^ b else x) 0

def digits (d : ByteArray) : Array ℕ := Array.ofFn (n := V) fun i => digit d i.val

/-- `wots_encode`: the digits, if both leftover top bits are zero and the digits sum to 195. -/
def encode (msg : ByteArray) (leaf : ℕ) (pp rand : ByteArray) : Option (Array ℕ) :=
  let d := encodingDigest msg leaf pp rand
  let e := digits d
  if !bitAt d 63 && !bitAt d 127 && e.foldl (· + ·) 0 == TARGET_SUM then some e else none

def chainStep (pp : ByteArray) (leaf c p : ℕ) (value : ByteArray) : ByteArray :=
  tweakHash pp TWEAK_CHAIN (CHAIN_LENGTH * c + p) leaf value

/-- Chain `c` walked from position `p` to `CHAIN_LENGTH - 1`. -/
def chainEnd (pp : ByteArray) (leaf c p : ℕ) (value : ByteArray) : ByteArray :=
  (List.range (CHAIN_LENGTH - 1 - p)).foldl (fun v k => chainStep pp leaf c (p + k) v) value

def merkleNode (pp : ByteArray) (level index : ℕ) (left right : ByteArray) : ByteArray :=
  tweakHash pp TWEAK_MERKLE level index (left ++ right)

/-- The Merkle root the signature reaches (`None` if the encoding is invalid). -/
def recoverRoot (leaf : ℕ) (msg : ByteArray) (s : Signer) : Option ByteArray := do
  let e ← encode msg leaf s.pp s.randomness
  let ends := (List.range V).foldl (fun b c => b ++ chainEnd s.pp leaf c e[c]! s.tips[c]!) .empty
  let pk := tweakHash s.pp TWEAK_WOTS_PK 0 leaf ends
  return (List.range LOG_LIFETIME).foldl (fun cur l =>
    let sib := s.proof[l]!
    let (left, right) := if (leaf >>> l) % 2 == 0 then (cur, sib) else (sib, cur)
    merkleNode s.pp (l + 1) (leaf >>> (l + 1)) left right) pk

/-- `xmss::verify` for the key `(s.root, s.pp)`. -/
def verify (leaf : ℕ) (msg : ByteArray) (s : Signer) : Bool :=
  s.tips.size == V && s.proof.size == LOG_LIFETIME && recoverRoot leaf msg s == some s.root

/-- `key_list(keys)`: BLAKE2s of the keys, each `root | pp`. -/
def keyList (g : Group) : ByteArray := blake2s (g.signers.foldl (fun b s => b ++ s.root ++ s.pp) .empty)

/-- The bytes `signer_set` hashes: header block, then two blocks per group. -/
def signerSetBytes (gs : Array Group) : ByteArray :=
  let head := "signers1".toUTF8 ++ le64 gs.size ++ le64 0 ++ le64 0 ++ blake2s .empty
  gs.foldl (fun b g => b ++ le64 g.leaf ++ le64 g.signers.size ++ g.message ++ zeros 16 ++
    keyList g ++ zeros 32) head

def signerSet (gs : Array Group) : ByteArray := blake2s (signerSetBytes gs)

def hex (d : ByteArray) : String :=
  d.foldl (fun s b => s ++ (if b < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 b.toNat)) ""

end Gf2.Xmss
