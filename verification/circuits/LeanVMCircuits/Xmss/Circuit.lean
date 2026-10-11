module

public import LeanVMCircuits.Rec.Builder

@[expose] public section

/-!
# The leanXMSS verifier on the recursion machine

The circuit that verifies `n` leanXMSS signatures in one recursion proof, written against the model of the builder
(`LeanVMCircuits.Rec.Model`). `crates/leanvm_core/src/rec/xmss.rs` makes the same calls in the same order, and
`CheckXmss` checks that the circuit it builds is this one.

Every hash of the scheme is BLAKE2s-256 over `tweak || parameter || payload`, whole 64-bit words, so each is one
`chain` of words, its digest truncated to its first two words. A 16-byte digest travels as an `E` wire whose first
two limbs are its words (the third limb is never read), so that a selection between two digests is arithmetic in `E`.

Per signature, the statement is five `E` words, exposed in this order: the public parameter `[p0, p1, 0]`, the
message's first and last two words `[m0, m1, 0]` and `[m2, m3, 0]`, the epoch `[e, 0, 0]` (`e < 2^32`), and last
the Merkle root `[r0, r1, 0]`. The signature is the prover's: 42 chain elements, the randomness and 32 siblings.

* The encoding hashes `tweak(4, 0, e) || p || m || rho || 0`, two blocks. Bit 63 of both digest words is zero, and
  digit `i` is bits `3r .. 3r+2` of word `i / 21`, `r = i % 21`. The digits sum to 195: the product over every digit
  bit `b` of weight `2^k` of `X^(2^k)` to the power `b` is `X^195` in `K`, and `X` has order above 294.
* A chain's first step (position 0) is needed only when its digit is zero, and at most fourteen digits are: the
  others, each at most 7, sum to 195. So a pool of fourteen entries hashes `tweak(1, 0, e) || p || t` under a tweak
  word `w` the prover names, an entry being its output's two words and `w` as an `E` wire. A network of five stages,
  shifting by 16, 8, 4, 2 and 1, moves the entries (then zeros) to the 42 chains: at a stage each position keeps its
  wire or takes the one `sh` before it, by a bit, so each output is an entry or zero.
* Chain `i` hashes six steps at positions `8i + s`, `1 ≤ s < 7`. Step 1's input is the network's output for chain `i`
  plus `[0, 0, tweak0(1, 8i)]` when the digit is zero and the chain element otherwise; its third word is zero, so the
  output it took has tweak word `tweak0(1, 8i)` (zero has none). The input of step `s > 1` is the chain element when
  the digit is `s` and the previous step's output otherwise: the indicator of digit `s` is a product of three factors
  `b` or `1 + b`. The chain's end is the chain element when the digit is 7, the last output otherwise.
* The leaf hashes `tweak(2, 0, e) || p || end_0 || .. || end_41`, eleven blocks.
* Level `l` of the path hashes `tweak(3, l + 1, e >> (l + 1)) || p || left || right`, the current node on the side
  bit `l` of the epoch names: `left = cur + b·(cur + sib)`, `right = left + cur + sib`.
-/

namespace LeanVMCircuits.Xmss.Circuit

open LeanVMCircuits.Rec.Model

/-- A tweak's first word: the domain separator zero, the tweak's type in byte 1, its position in bytes 4 to 7. -/
def tweak0 (ty pos : ℕ) : ℕ := ty * 2 ^ 8 + pos * 2 ^ 32

/-- `X^195` in `K` as a word: the product the digits' bits must reach. -/
def targetWord : ℕ := 0xedb8

/-- Words `0` and `1` of an `E` wire (a digest's), and its word `2`. -/
def words (e : ℕ) : M (ℕ × ℕ × ℕ) := do
  let ks ← eToK e
  pure (ks.getD 0 0, ks.getD 1 0, ks.getD 2 0)

/-- A statement word exposed, its words; `zeros` of its words past the first `3 - zeros` are held to zero. -/
def statementWords (zeros : ℕ) : M (List ℕ) := do
  let w ← wire
  let _ ← expose w
  let ks ← eToK w
  for k in ks.drop (3 - zeros) do
    eqConstK k 0
  pure (ks.take (3 - zeros))

/-- The index word `e >> shift` in bytes 12 to 15 of a tweak, from the epoch's bits. -/
def indexWord (bits : List ℕ) (shift : ℕ) : M ℕ := do
  let z ← kConst 0
  pack (List.replicate 32 z ++ (bits.take 32).drop shift)

/-- The digest wire of the hash of `tweak0 || index || p || payload`. -/
def tweakHash (ty pos idx : ℕ) (pp payload : List ℕ) : M ℕ := do
  let tw ← kConst (tweak0 ty pos)
  chain ([tw, idx] ++ pp ++ payload)

/-- The digit bits' product: for each bit `b` of weight `2^k`, times `X^(2^k)` when `b` is one. -/
def digitProduct (bits : List ℕ) : M ℕ := do
  let mut acc ← one
  let z ← zero
  for i in List.range 42 do
    for k in List.range 3 do
      let b := bits.getD (3 * i + k) 0
      -- `X^(2^k) + 1` as a word, `X` being the word 2.
      let t ← mulConstAdd acc (2 ^ (2 ^ k) + 1) 0 0 z
      acc ← mulKAdd t b acc
  pure acc

/-- The indicators of the eight values of a digit's bits `a0, a1, a2`, low first: `e v` is one exactly when the digit
is `v`. -/
def indicators (a0 a1 a2 : ℕ) : M (List ℕ) := do
  let o ← one
  let z ← zero
  let mut level := [o]
  for a in [a0, a1, a2] do
    let mut next := []
    for v in List.range (2 * level.length) do
      let p := level.getD (v % level.length) 0
      -- The new bit is bit `log2 level.length` of `v`: a factor `1 + a` where it is zero, `a` where it is one.
      let q ← if v < level.length then mulKAdd p a p else mulKAdd p a z
      next := next ++ [q]
    level := next
  pure level

/-- The pool's size: at most fourteen digits are zero, as the others, each at most 7, sum to 195. -/
def pool : ℕ := 14

/-- The network's shifts, largest first: an entry moves at most 28 positions on to its chain. -/
def shifts : List ℕ := [16, 8, 4, 2, 1]

/-- A pool entry: the hash of `w || idx || p || t0 || t1` under a tweak word `w` and element `t0, t1` the prover names,
as its output's two words and `w`, an `E` wire. -/
def poolEntry (idx : ℕ) (pp : List ℕ) : M ℕ := do
  let w ← wire
  let t0 ← wire
  let t1 ← wire
  let d ← chain ([w, idx] ++ pp ++ [t0, t1])
  let ks ← dToK d
  kToE (ks.getD 0 0) (ks.getD 1 0) w

/-- `x` when the bit `b` is zero and `y` when it is one: `x + b·(x + y)`, the sum `y·1 + x` made in `EXK` by a one
`one'` other than the unit wire. -/
def sel (one' b x y : ℕ) : M ℕ := do
  let diff ← mulKAdd y one' x
  mulKAdd diff b x

/-- A stage of the network: position `p ≥ sh` keeps its wire or takes the one at `p - sh` by bit `p - sh` of `bits`,
the others keep theirs. -/
def stage (one' sh : ℕ) (bits arr : List ℕ) : M (List ℕ) :=
  (List.range arr.length).mapM fun p =>
    if sh ≤ p then sel one' (bits.getD (p - sh) 0) (arr.getD p 0) (arr.getD (p - sh) 0) else pure (arr.getD p 0)

/-- The network: the entries, then zeros up to the 42 chains, through every stage, stage `sh` taking the next
`42 - sh` bits. -/
def network (one' : ℕ) (bits entries : List ℕ) : M (List ℕ) := do
  let z ← zero
  let mut arr := entries ++ List.replicate (42 - entries.length) z
  let mut off := 0
  for sh in shifts do
    arr ← stage one' sh (bits.drop off) arr
    off := off + (42 - sh)
  pure arr

/-- Chain `i` from its element `tip` and the network's output `ent` for it (`E` wires) under the digit's indicators
`ind`: its end's two words. -/
def chainEnd (i idx tip ent : ℕ) (pp ind : List ℕ) : M (ℕ × ℕ) := do
  let third ← eConst 0 0 1
  let tw ← kConst (tweak0 1 (8 * i))
  let ent' ← mulKAdd third tw ent
  let diff ← add ent' tip
  let m ← mulAdd (ind.getD 0 0) diff tip
  let (v0, v1, v2) ← words m
  eqConstK v2 0
  let d ← tweakHash 1 (8 * i + 1) idx pp [v0, v1]
  let (o, _) ← dToEAndK d
  let mut cur := o
  for s in List.range' 2 5 do
    let diff ← add tip cur
    let m ← mulAdd (ind.getD s 0) diff cur
    let (v0, v1, _) ← words m
    let d ← tweakHash 1 (8 * i + s) idx pp [v0, v1]
    let (o, _) ← dToEAndK d
    cur := o
  let diff ← add tip cur
  let e ← mulAdd (ind.getD 7 0) diff cur
  let (n0, n1, _) ← words e
  pure (n0, n1)

/-- One level of the Merkle path: the parent of `node` (a digest wire) and the sibling, the epoch's bit `bit` naming
the side of `node`. -/
def level (l idx bit node : ℕ) (pp : List ℕ) : M ℕ := do
  let (cur, _) ← dToEAndK node
  let sib ← wire
  let diff ← add cur sib
  let left ← mulKAdd diff bit cur
  let right ← add left diff
  let (l0, l1, _) ← words left
  let (r0, r1, _) ← words right
  tweakHash 3 (l + 1) idx pp [l0, l1, r0, r1]

/-- One signature's verification. -/
def signature : M Unit := do
  let pp ← statementWords 1
  let mlo ← statementWords 1
  let mhi ← statementWords 1
  let ep ← statementWords 2
  let z ← kConst 0
  let bits ← split (ep.getD 0 0)
  for k in (bits.drop 32) do
    eqConstK k 0
  let idx ← indexWord bits 0
  -- The encoding.
  let rho ← wire
  let (r0, r1, r2) ← words rho
  let d ← tweakHash 4 0 idx pp (mlo ++ mhi ++ [r0, r1, r2, z])
  let ks ← dToK d
  let lo ← split (ks.getD 0 0)
  let hi ← split (ks.getD 1 0)
  eqConstK (lo.getD 63 0) 0
  eqConstK (hi.getD 63 0) 0
  let digitBits := lo.take 63 ++ hi.take 63
  let prod ← digitProduct digitBits
  eqConstE prod targetWord 0 0
  -- The pool, the network's one and bits, and the network.
  let mut entries := []
  for _ in List.range pool do
    let ent ← poolEntry idx pp
    entries := entries ++ [ent]
  let one' ← wire
  eqConstK one' 1
  let mut netBits := []
  for _ in List.range 3 do
    let w ← wire
    let bs ← split w
    netBits := netBits ++ bs
  let routed ← network one' netBits entries
  -- The chains.
  let mut ends := []
  for i in List.range 42 do
    let tip ← wire
    let ind ← indicators (digitBits.getD (3 * i) 0) (digitBits.getD (3 * i + 1) 0) (digitBits.getD (3 * i + 2) 0)
    let (n0, n1) ← chainEnd i idx tip (routed.getD i 0) pp ind
    ends := ends ++ [n0, n1]
  -- The leaf and the path.
  let mut node ← tweakHash 2 0 idx pp ends
  for l in List.range 32 do
    let ix ← indexWord bits (l + 1)
    node ← level l ix (bits.getD l 0) node pp
  let rs ← dToK node
  let root ← kToE (rs.getD 0 0) (rs.getD 1 0) z
  let _ ← expose root

/-- The circuit verifying `n` signatures. -/
def circuit (n : ℕ) : M Unit := do
  for _ in List.range n do
    signature

end LeanVMCircuits.Xmss.Circuit
