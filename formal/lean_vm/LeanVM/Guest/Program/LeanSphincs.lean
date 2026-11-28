/-
  LeanVM.Guest.Program.LeanSphincs

  The guest's section "leanSPHINCS signature verification".
-/

module

public import LeanVM.Guest.Program.LeanXmss

/-!
# LeanSPHINCS signature verification
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- The integer whose n bytes, low first, are hinted in the exponent at marks[k]: each range checked and read off `byte_bits` as the bits it spells. -/
def spFromBytes (byteBits : Word) (marks : List V) (n : Nat) : B Word := B.inline "sp_from_bytes" do
  let mut value : Word := default
  for t in [0:n] do
    let k := n - 1 - t
    assert log marks[k] < SP_BYTE_VALUES
    if t = 0 then
      value ← val byteBits[marks[k]]
    else
      value ← val (byteBits[marks[k]] + value * GEN ^ 8)
  return value

/-- Bit p of the digest read most significant first, as base_2b reads it: bit 7 - p % 8 of byte p // 8, from the bit runs of the first call's two cells. -/
def spMdBit (bits0 : List V) (bits1 : List V) (p : Nat) : B Word := B.inline "sp_md_bit" do
  let mut b := bits0[(8 * (p / 8) + 7 - p % 8) % SP_CELL_BITS]
  if p / SP_CELL_BITS = 1 then
    b := bits1[8 * (p / 8) + 7 - p % 8 - SP_CELL_BITS]
  return b

/-- FORS tree c's leaf, the digest's SP_FORS_HEIGHT bits from bit SP_FORS_HEIGHT c, and its right shifts, each with tree c's place across the trees: vals[SP_FORS_HEIGHT c + z] is the FIPS 205 tree index of the leaf's ancestor at height z, c 2^(height - z) plus its index in tree c. -/
def spForsField (bits0 : List V) (bits1 : List V) (vals : List V) (c : Nat) : B Unit := B.inline "sp_fors_field" do
  let t0 ← spMdBit bits0 bits1 (SP_FORS_HEIGHT * c)
  vals[SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - 1] := t0 + lit (2 * c)
  for r in [1:SP_FORS_HEIGHT] do
    let t1 ← spMdBit bits0 bits1 (SP_FORS_HEIGHT * c + r)
    vals[SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - 1 - r] := t1 + GEN * Ex.v vals[SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - r]

/-- Digest byte i < SP_MD_BYTES where its cell holds it, from the shifts of field c, the one its first bit is in, and of c + 1 if it reaches it. A byte inside c is c shifted past the bits after the byte, masked to eight bits; a byte across both is c's low bits raised past c + 1's high ones. It keeps the trees' places vals carries, which the caller takes out. -/
def spMdByte (vals : List V) (i : Nat) : B Word := B.inline "sp_md_byte" do
  let c := 8 * i / SP_FORS_HEIGHT
  let mut v : Word := default
  if c = (8 * i + 7) / SP_FORS_HEIGHT then
    v := vals[SP_FORS_HEIGHT * (2 * c + 1) - 8 * i - 8]
    if 8 * i ≠ SP_FORS_HEIGHT * c then
      v ← val (v + Ex.v vals[SP_FORS_HEIGHT * (2 * c + 1) - 8 * i] * GEN ^ 8)
    v ← val (v * lit (2 ^ (8 * (i % 16))))
  else
    v ← val ((vals[SP_FORS_HEIGHT * c] + Ex.v vals[SP_FORS_HEIGHT * (2 * c + 1) - 8 * i] * GEN ^ (SP_FORS_HEIGHT * (c + 1) - 8 * i)) * lit (2 ^ (8 * (i % 16) + 8 * i + 8 - SP_FORS_HEIGHT * (c + 1))))
    v ← val (v + vals[SP_FORS_HEIGHT * (2 * c + 3) - 8 * i - 8] * lit (2 ^ (8 * (i % 16))))
  return v

/-- Bit b of the three layers' leaves one after the other, bottom first, which the digest's last four bytes hold: the bottom leaf the last byte (the second call's byte 1), the middle one the byte before (its byte 0), and the top one the tree index's high bits (the first call's byte 31, then the low two bits of 30). -/
def spLeafBit (bits1 : List V) (bits2 : List V) (b : Nat) : B Word := B.inline "sp_leaf_bit" do
  let mut x := bits2[(b + 8) % (8 * SP_TAIL_BYTES)]
  if b / 8 = SP_TOP / 8 then
    x := bits1[b - SP_TOP + SP_TREE_MID_BIT]
  if b / 8 = SP_TOP / 8 + 1 then
    x := bits1[b - SP_TOP - 8 + SP_TREE_HI_BIT]
  return x

/-- The leaf of n bits from leaf bit `off` and its right shifts: lvals[off + z] is the index of its ancestor at height z. -/
def spLeafShifts (bits1 : List V) (bits2 : List V) (lvals : List V) (off : Nat) (n : Nat) : B Unit := B.inline "sp_leaf_shifts" do
  let t0 ← spLeafBit bits1 bits2 (off + n - 1)
  lvals[off + n - 1] := t0
  for r in [1:n] do
    let t1 ← spLeafBit bits1 bits2 (off + n - 1 - r)
    lvals[off + n - 1 - r] := t1 + GEN * Ex.v lvals[off + n - r]

/-- The n-bit value vals[at] as the last two bytes of an A1 word, big endian: its low byte masked and placed last, its high bits before it. -/
def spBe16 (vals : List V) (at' : Nat) (n : Nat) : B Word := B.inline "sp_be16" do
  let mut v : Word := default
  if (n + 7) / 8 = 2 then
    v ← val (vals[at'] * lit SP_WORD3_MUL_0 + vals[at' + 8] * (GEN ^ 8 * lit SP_WORD3_MUL_0 + lit SP_WORD3_MUL_1))
  else
    v ← val (vals[at'] * lit SP_WORD3_MUL_0)
  return v

/-- The A1 of tree c's node at height z on the opened leaf's path, `a1` being the trees' with neither: z, then the node's tree index across the trees in the word's last two bytes, big endian. vals holds the index below the root, whose high byte is c's part alone from height SP_FORS_HEIGHT - 8 on, a constant added first so that trees sharing it share the sum; at the root the index is c. -/
def spForsAt (a1 : Word) (vals : List V) (c : Nat) (z : Nat) : B Word := B.inline "sp_fors_at" do
  let mut at' ← val (a1 + lit (z * SP_WORD2_MUL))
  if z = SP_FORS_HEIGHT then
    at' ← val (at' + lit (c * SP_WORD3_MUL_0))
  else if z / (SP_FORS_HEIGHT - 8) = 0 then
    let t0 ← spBe16 vals (SP_FORS_HEIGHT * c + z) 16
    at' ← val (at' + t0)
  else
    at' ← val (at' + lit (c / 2 ^ (z - (SP_FORS_HEIGHT - 8))) * (GEN ^ 8 * lit SP_WORD3_MUL_0 + lit SP_WORD3_MUL_1))
    let t0 ← spBe16 vals (SP_FORS_HEIGHT * c + z) 8
    at' ← val (at' + t0)
  return at'

/-- FORS tree c: its leaf, hashed from the hinted secret, then climbed up the hinted ordered pairs to its root, into roots[c]. -/
def spForsTree (pp : Word) (a0 : Word) (a1 : Word) (bits0 : List V) (bits1 : List V) (vals : List V) (roots : List V) (c : Nat) : B Unit := B.inline "sp_fors_tree" do
  let secret ← hinted (B.witnessCell "sp_fors_secrets")
  let held ← B.stackBuf 1
  let t0 ← spForsAt a1 vals c 0
  B.keccak [pp, a0] [t0, secret] held
  let mut cur := held[0]
  let mut parent : List V := default
  for z in [0:SP_FORS_HEIGHT] do
    -- The two children, then three cells the compiler sets to the padding, so the node's hash reads the right child in place (`pad_tail=1`).
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack kids[0:2])
    let t1 ← spMdBit bits0 bits1 (SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - 1 - z)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt a1 vals c (z + 1)
    if z + 1 = SP_FORS_HEIGHT then
      B.keccak (a := .words [.cell pp.v, .cell a0.v]) (b := .words [.cell nodeAt.v, .cell kids[0].v]) (tail := some (.cells (.frame kids[1:5]))) (len := some 80) (padTail := true) (out := .frame roots[c:c + 1])
    else
      parent ← B.stackBuf 1
      B.keccak (a := .words [.cell pp.v, .cell a0.v]) (b := .words [.cell nodeAt.v, .cell kids[0].v]) (tail := some (.cells (.frame kids[1:5]))) (len := some 80) (padTail := true) (out := .frame parent)
      cur := parent[0]

/-- Word j of a T_l input: PK.seed, the address, then the values, value i at run[first + stride i] (the FORS roots, or a one-time key's chain tips). -/
def spWord (pp : Word) (a0 : Word) (a1 : Word) (run : List V) (first : Nat) (stride : Nat) (j : Nat) : B Word := B.inline "sp_word" do
  let mut w := pp
  if j = 1 then
    w := a0
  if j = 2 then
    w := a1
  if j / 3 ≠ 0 then
    w := run[first + stride * (j - 3)]
  return w

set_option maxHeartbeats 4000000 in
/-- The leaf of the one-time key whose address is (a0, a1), a1 of type WOTS_HASH and so its key pair alone, and whose encoding digest is `encoding`. The codeword: DIGIT_GROUP digits at a time, hinted in the exponent and range checked, every group first, then the groups' dispatches back to back (each arm entering the next dispatch, as in verify_lean_xmss), the arm walking every chain's remaining steps and folding its digits in: their sums into a product that must be the target sum, and the digits, each group where the digest holds it, into the digest. One function for the three layers.
-/
def spWots : GFn where
  name := "sp_wots"
  arity := 4
  rets := 1
  body ps := do
    let pp := ps[0]
    let a0 := ps[1]
    let a1 := ps[2]
    let encoding := ps[3]
    let t0 ← B.stackBuf 2
    t0[0] := a0
    t0[1] := a1
    let at' := t0
    let walks ← B.stackBuf 192
    let powers ← B.stackBuf 10
    for s in [0:3 * 3 + 1] do
      powers[s] := GEN ^ s
    let mut digitProduct : FW := FW.c (lit 1)
    let mut encoded : FW := FW.c (lit 0)
    -- A leanSPHINCS chain index rides its step's address, so the chain-index table a leanXMSS walk reads is unused here and `powers` stands in for it. The last group is the chain the others leave over: its table is as wide as theirs (one unrolled `match`), its range check keeping it to one digit.
    let groups ← B.stackBuf 22
    for p in [0:SP_V / DIGIT_GROUP + 1] do
      B.witness "digits" (.stack groups[p:p + 1])
    for p in [0:SP_V / DIGIT_GROUP] do
      assert log groups[p] < DIGIT_GROUPS
      pure ()
    assert log groups[SP_V / DIGIT_GROUP] < CHAIN_LENGTH
    for p in [0:SP_V / DIGIT_GROUP + 1] do
      let t1 ← B.targets [none, none]
      if p + 1 < SP_V / DIGIT_GROUP + 1 then
        B.chain
      if p = 0 then
        Keccak.inlineArms
      let _ ← B.matchArms groups[p] ((List.range 64).map fun arm => do
        walkGroup at' pp walks powers (DIGIT_GROUP * p) (DIGIT_GROUP - (DIGIT_GROUP - 1) * (p / (64 / DIGIT_GROUP))) arm 0 powers digitProduct encoded [t1[0].v, t1[1].v])
      digitProduct := FW.w t1[0]
      encoded := FW.w t1[1]
    assert encoded == encoding
    assert digitProduct == GEN ^ SP_TARGET_SUM
    let leaf ← B.stackBuf 1
    let pkAt ← val (a1 + lit SP_WOTS_PK)
    let t2 ← spWord pp a0 pkAt walks (3 - 1) 3 0
    let t3 ← spWord pp a0 pkAt walks (3 - 1) 3 1
    let t4 ← spWord pp a0 pkAt walks (3 - 1) 3 2
    let t5 ← spWord pp a0 pkAt walks (3 - 1) 3 3
    let t6 ← spWord pp a0 pkAt walks (3 - 1) 3 4
    let t7 ← spWord pp a0 pkAt walks (3 - 1) 3 5
    let t8 ← spWord pp a0 pkAt walks (3 - 1) 3 6
    let t9 ← spWord pp a0 pkAt walks (3 - 1) 3 7
    let t10 ← spWord pp a0 pkAt walks (3 - 1) 3 8
    let t11 ← spWord pp a0 pkAt walks (3 - 1) 3 9
    let t12 ← spWord pp a0 pkAt walks (3 - 1) 3 10
    let t13 ← spWord pp a0 pkAt walks (3 - 1) 3 11
    let t14 ← spWord pp a0 pkAt walks (3 - 1) 3 12
    let t15 ← spWord pp a0 pkAt walks (3 - 1) 3 13
    let t16 ← spWord pp a0 pkAt walks (3 - 1) 3 14
    let t17 ← spWord pp a0 pkAt walks (3 - 1) 3 15
    let t18 ← spWord pp a0 pkAt walks (3 - 1) 3 16
    let t19 ← spWord pp a0 pkAt walks (3 - 1) 3 17
    let t20 ← spWord pp a0 pkAt walks (3 - 1) 3 18
    let t21 ← spWord pp a0 pkAt walks (3 - 1) 3 19
    let t22 ← spWord pp a0 pkAt walks (3 - 1) 3 20
    let t23 ← spWord pp a0 pkAt walks (3 - 1) 3 21
    let t24 ← spWord pp a0 pkAt walks (3 - 1) 3 22
    let t25 ← spWord pp a0 pkAt walks (3 - 1) 3 23
    let t26 ← spWord pp a0 pkAt walks (3 - 1) 3 24
    let t27 ← spWord pp a0 pkAt walks (3 - 1) 3 25
    let t28 ← spWord pp a0 pkAt walks (3 - 1) 3 26
    let t29 ← spWord pp a0 pkAt walks (3 - 1) 3 27
    let t30 ← spWord pp a0 pkAt walks (3 - 1) 3 28
    let t31 ← spWord pp a0 pkAt walks (3 - 1) 3 29
    let t32 ← spWord pp a0 pkAt walks (3 - 1) 3 30
    let t33 ← spWord pp a0 pkAt walks (3 - 1) 3 31
    let t34 ← spWord pp a0 pkAt walks (3 - 1) 3 32
    let t35 ← spWord pp a0 pkAt walks (3 - 1) 3 33
    let t36 ← spWord pp a0 pkAt walks (3 - 1) 3 34
    let t37 ← spWord pp a0 pkAt walks (3 - 1) 3 35
    let t38 ← spWord pp a0 pkAt walks (3 - 1) 3 36
    let t39 ← spWord pp a0 pkAt walks (3 - 1) 3 37
    let t40 ← spWord pp a0 pkAt walks (3 - 1) 3 38
    let t41 ← spWord pp a0 pkAt walks (3 - 1) 3 39
    let t42 ← spWord pp a0 pkAt walks (3 - 1) 3 40
    let t43 ← spWord pp a0 pkAt walks (3 - 1) 3 41
    let t44 ← spWord pp a0 pkAt walks (3 - 1) 3 42
    let t45 ← spWord pp a0 pkAt walks (3 - 1) 3 43
    let t46 ← spWord pp a0 pkAt walks (3 - 1) 3 44
    let t47 ← spWord pp a0 pkAt walks (3 - 1) 3 45
    let t48 ← spWord pp a0 pkAt walks (3 - 1) 3 46
    let t49 ← spWord pp a0 pkAt walks (3 - 1) 3 47
    let t50 ← spWord pp a0 pkAt walks (3 - 1) 3 48
    let t51 ← spWord pp a0 pkAt walks (3 - 1) 3 49
    let t52 ← spWord pp a0 pkAt walks (3 - 1) 3 50
    let t53 ← spWord pp a0 pkAt walks (3 - 1) 3 51
    let t54 ← spWord pp a0 pkAt walks (3 - 1) 3 52
    let t55 ← spWord pp a0 pkAt walks (3 - 1) 3 53
    let t56 ← spWord pp a0 pkAt walks (3 - 1) 3 54
    let t57 ← spWord pp a0 pkAt walks (3 - 1) 3 55
    let t58 ← spWord pp a0 pkAt walks (3 - 1) 3 56
    let t59 ← spWord pp a0 pkAt walks (3 - 1) 3 57
    let t60 ← spWord pp a0 pkAt walks (3 - 1) 3 58
    let t61 ← spWord pp a0 pkAt walks (3 - 1) 3 59
    let t62 ← spWord pp a0 pkAt walks (3 - 1) 3 60
    let t63 ← spWord pp a0 pkAt walks (3 - 1) 3 61
    let t64 ← spWord pp a0 pkAt walks (3 - 1) 3 62
    let t65 ← spWord pp a0 pkAt walks (3 - 1) 3 63
    let t66 ← spWord pp a0 pkAt walks (3 - 1) 3 64
    let t67 ← spWord pp a0 pkAt walks (3 - 1) 3 65
    let t68 ← spWord pp a0 pkAt walks (3 - 1) 3 66
    B.keccakCells [t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68] leaf
    return [.v leaf[0].v]

/-- The path from `node` up the tree whose address is a0, the leaf's bits from leaf bit `off` and its ancestors' indices in lvals, the two children of each node hinted in order, the root into out. -/
def spPath (node : Word) (pp : Word) (a0 : FW) (bits1 : List V) (bits2 : List V) (lvals : List V) (out : List V) (off : Nat) (height : Nat) : B Unit := B.inline "sp_path" do
  let mut cur := node
  for z in [0:height] do
    -- The two children, then three cells the compiler pads (as in sp_fors_tree).
    let kids ← B.stackBuf 5
    B.witness "siblings" (.stack kids[0:2])
    let t0 ← spLeafBit bits1 bits2 (off + z)
    isChild cur kids 0 t0
    -- The parent's height, then its index, none at the root.
    let mut nodeAt : FW := FW.c (lit (SP_TREE + (z + 1) * SP_WORD2_MUL))
    let mut parent : List V := default
    if z + 1 = height then
      parent := out
    else
      let t1 ← spBe16 lvals (off + z + 1) (height - z - 1)
      nodeAt ← fold (t1 + nodeAt)
      parent ← B.stackBuf 1
    B.keccak (a := .words [.cell pp.v, (← a0.msg)]) (b := .words [(← nodeAt.msg), .cell kids[0].v]) (tail := some (.cells (.frame kids[1:5]))) (len := some 80) (padTail := true) (out := .frame parent)
    cur := parent[0]

/-- One layer: the key at (a0, key), `key` its key pair as A1 holds it, signs `signed`, its counter rebuilt from four bytes, then the path to its tree's root into out. -/
def spLayer (pp : Word) (a0 : FW) (key : Word) (signed : Word) (byteBits : Word) (bits1 : List V) (bits2 : List V) (lvals : List V) (out : List V) (off : Nat) (height : Nat) : B Unit := B.inline "sp_layer" do
  let ctr ← B.stackBuf SP_COUNTER_BYTES
  B.witness "sp_counter" (.stack ctr)
  let counter ← spFromBytes byteBits ctr SP_COUNTER_BYTES
  let enc ← B.stackBuf 1
  let encAt ← val (key + lit SP_WOTS_ENC)
  B.keccak (a := .words [.cell pp.v, (← a0.msg)]) (b := .words [.cell encAt.v, .cell signed.v]) (tail := some (.words [.cell counter.v, .zero, .zero, .zero])) (len := some SP_ENCODING_BYTES) (out := .frame enc)
  let leaf ← call1 "sp_wots" [pp, a0, key, enc[0]]
  spPath leaf pp a0 bits1 bits2 lvals out off height

set_option maxHeartbeats 4000000 in
/-- `signer` is one 4-cell entry of the leanSPHINCS coverage table: the pubkey's PK.seed and PK.root, then the message THAT signer signed, the two bound together by the scheme's claim-list digest, as for leanXMSS. -/
def verifySigLeanSphincs : GFn where
  name := "verify_sig_lean_sphincs"
  arity := 2
  rets := 0
  body ps := do
    let signer := ps[0]
    let byteBits := ps[1]
    let pp ← val signer[GEN ^ 0]
    let pkRoot ← val signer[GEN ^ 1]
    -- ---- H_msg, which picks the index and every FORS leaf ---- H(R | PK.seed | PK.root | M | BE_32(i)) for i = 0, 1, M the claim's two cells.
    let m0 ← val signer[GEN ^ 2]
    let m1 ← val signer[GEN ^ 3]
    let rho ← hinted (B.witnessCell "sp_rand")
    let d0 ← B.stackBuf 2
    let d1 ← B.stackBuf 1
    B.keccak (a := .words [.cell rho.v, .cell pp.v]) (b := .words [.cell pkRoot.v, .cell m0.v]) (tail := some (.words [.cell m1.v, .zero, .zero, .zero])) (len := some SP_HMSG_LEN) (out := .frame d0)
    B.keccak (a := .words [.cell rho.v, .cell pp.v]) (b := .words [.cell pkRoot.v, .cell m0.v]) (tail := some (.words [.cell m1.v, .cell (← val (lit SP_COUNTER_ONE)).v, .zero, .zero])) (len := some SP_HMSG_LEN) (out := .frame d1)
    -- The digest's bits are advice pinned Boolean, and the digest is rebuilt from them:
    -- byte by byte from the FORS leaves' values, which their shifts give, then the tree index and the bottom leaf from the layers' leaves, the six bits the tree index leaves from their own bits, and the second call's unused bytes as hinted bytes (sp_from_bytes). Its high lane is what the rest leaves, checked to be a lane.
    let bits0 ← B.stackBuf SP_CELL_BITS
    let bits1 ← B.stackBuf SP_CELL_BITS
    let bits2 ← B.stackBuf 16
    B.hintBits (.stack bits0[0:SP_CELL_BITS]) d0[0] 0 SP_CELL_BITS
    B.hintBits (.stack bits1[0:SP_CELL_BITS]) d0[1] 0 SP_CELL_BITS
    B.hintBits (.stack bits2[0:8 * SP_TAIL_BYTES]) d1[0] 0 (8 * SP_TAIL_BYTES)
    for b_k in [0:SP_CELL_BITS] do
      bits0[b_k] := bits0[b_k] * bits0[b_k]
      bits1[b_k] := bits1[b_k] * bits1[b_k]
    for b_k in [0:8 * SP_TAIL_BYTES] do
      bits2[b_k] := bits2[b_k] * bits2[b_k]
    let vals ← B.stackBuf 240
    for c_k in [0:SP_FORS_TREES] do
      spForsField bits0 bits1 vals c_k
    let lvals ← B.stackBuf SP_H
    spLeafShifts bits1 bits2 lvals 0 SP_HEIGHT_0
    spLeafShifts bits1 bits2 lvals 8 8
    spLeafShifts bits1 bits2 lvals SP_TOP SP_HEIGHT_2
    let mut md0 ← spMdByte vals 0
    for i in [1:16] do
      let t0 ← spMdByte vals i
      md0 ← val (md0 + t0)
    let mut md1 ← spMdByte vals 16
    for i in [17:SP_MD_BYTES] do
      let t1 ← spMdByte vals i
      md1 ← val (md1 + t1)
    -- vals carries each tree's place across the trees (sp_fors_field), which the digest's bytes do not: take it out again, a constant per byte.
    let mut corr0 : FW := FW.c (lit 0)
    let mut corr1 : FW := FW.c (lit 0)
    for i in [0:SP_MD_BYTES] do
      let fc := 8 * i / SP_FORS_HEIGHT
      let mut pc : FW := FW.c (lit 0)
      if fc ≠ (8 * i + 7) / SP_FORS_HEIGHT then
        pc ← fold (lit ((fc + 1) * 2 ^ (8 * i + 8 - SP_FORS_HEIGHT * (fc + 1))) * lit (2 ^ (8 * (i % 16))))
      else if 8 * i = SP_FORS_HEIGHT * fc then
        pc ← fold (lit (fc * 256) * lit (2 ^ (8 * (i % 16))))
      if i / 16 = 0 then
        corr0 ← fold (corr0 + pc)
      else
        corr1 ← fold (corr1 + pc)
    -- The tree index's middle byte, the top leaf's low byte; its high byte holds the top leaf's two high bits, then six unused ones.
    let treeMid ← val (lvals[SP_TOP] + Ex.v lvals[SP_TOP + 8] * GEN ^ 8)
    let mut pad := bits1[SP_TREE_HI_BIT + 7]
    for b_k in [1:SP_PAD_BITS] do
      pad ← val (bits1[SP_TREE_HI_BIT + 7 - b_k] + GEN * pad)
    d0[0] := md0 + corr0
    d0[1] := md1 + corr1 + (lvals[SP_TOP + 8] + pad * GEN ^ 2) * lit (2 ^ SP_TREE_HI_BIT) + treeMid * lit (2 ^ SP_TREE_MID_BIT)
    let unusedBytes ← B.stackBuf SP_UNUSED_BYTES
    B.witness "sp_unused" (.stack unusedBytes)
    let unused ← spFromBytes byteBits unusedBytes SP_UNUSED_BYTES
    let high ← val ((d1[0] + lvals[8] + Ex.v lvals[0] * GEN ^ 8 + unused * GEN ^ 16) * Y_INV)
    B.assertInK high unused
    -- ---- FORS: each tree's opening climbed to its root, then T_k over the roots ---- The FORS addresses are the bottom key's: its layer and tree, its leaf the key pair.
    let a0B ← val (lvals[8] * lit SP_TREE_MUL_0 + treeMid * lit SP_TREE_MUL_1 + lvals[SP_TOP + 8] * lit SP_TREE_MUL_2)
    let keyB ← val (lvals[0] * lit SP_KEY_MUL_0)
    let roots ← B.stackBuf SP_FORS_TREES
    let forsAt ← val (keyB + lit SP_FORS_TREE)
    for c_k in [0:SP_FORS_TREES] do
      spForsTree pp a0B forsAt bits0 bits1 vals roots c_k
    let forsPk ← B.stackBuf 1
    let rootsAt ← val (keyB + lit SP_FORS_ROOTS)
    let t2 ← spWord pp a0B rootsAt roots 0 1 0
    let t3 ← spWord pp a0B rootsAt roots 0 1 1
    let t4 ← spWord pp a0B rootsAt roots 0 1 2
    let t5 ← spWord pp a0B rootsAt roots 0 1 3
    let t6 ← spWord pp a0B rootsAt roots 0 1 4
    let t7 ← spWord pp a0B rootsAt roots 0 1 5
    let t8 ← spWord pp a0B rootsAt roots 0 1 6
    let t9 ← spWord pp a0B rootsAt roots 0 1 7
    let t10 ← spWord pp a0B rootsAt roots 0 1 8
    let t11 ← spWord pp a0B rootsAt roots 0 1 9
    let t12 ← spWord pp a0B rootsAt roots 0 1 10
    let t13 ← spWord pp a0B rootsAt roots 0 1 11
    let t14 ← spWord pp a0B rootsAt roots 0 1 12
    let t15 ← spWord pp a0B rootsAt roots 0 1 13
    let t16 ← spWord pp a0B rootsAt roots 0 1 14
    let t17 ← spWord pp a0B rootsAt roots 0 1 15
    let t18 ← spWord pp a0B rootsAt roots 0 1 16
    let t19 ← spWord pp a0B rootsAt roots 0 1 17
    let t20 ← spWord pp a0B rootsAt roots 0 1 18
    let t21 ← spWord pp a0B rootsAt roots 0 1 19
    let t22 ← spWord pp a0B rootsAt roots 0 1 20
    let t23 ← spWord pp a0B rootsAt roots 0 1 21
    let t24 ← spWord pp a0B rootsAt roots 0 1 22
    let t25 ← spWord pp a0B rootsAt roots 0 1 23
    let t26 ← spWord pp a0B rootsAt roots 0 1 24
    let t27 ← spWord pp a0B rootsAt roots 0 1 25
    let t28 ← spWord pp a0B rootsAt roots 0 1 26
    B.keccakCells [t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28] forsPk
    -- ---- the hypertree: each layer's one-time key signs what the layer below gives ---- The bottom key is in the digest's tree at its leaf; the middle key in that tree's top bits at its low byte; the top key in tree zero at the tree's top bits.
    let rootB ← B.stackBuf 1
    spLayer pp (FW.w a0B) keyB forsPk[0] byteBits bits1 bits2 lvals rootB 0 SP_HEIGHT_0
    let a0M ← val (lit SP_LAYER_MUL + treeMid * lit SP_TREE_MUL_0 + lvals[SP_TOP + 8] * lit SP_TREE_MUL_1)
    let keyM ← val (lvals[SP_MID] * lit SP_KEY_MUL_0)
    let rootM ← B.stackBuf 1
    spLayer pp (FW.w a0M) keyM rootB[0] byteBits bits1 bits2 lvals rootM 8 8
    let a0T := 2 * SP_LAYER_MUL
    let keyT ← val (treeMid * lit SP_KEY_MUL_0 + lvals[SP_TOP + 8] * lit SP_KEY_MUL_1)
    let root ← B.stackBuf 1
    spLayer pp (FW.c (lit a0T)) keyT rootM[0] byteBits bits1 bits2 lvals root (8 + 8) SP_HEIGHT_2
    assert root[0] == pkRoot
    return []

end
end LeanVM.Guest.Program
