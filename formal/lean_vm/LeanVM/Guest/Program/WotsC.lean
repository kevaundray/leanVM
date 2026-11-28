/-
  LeanVM.Guest.Program.WotsC

  The guest's section "WOTS+C, both schemes".
-/

module

public import LeanVM.Guest.Program.InnerProofVerification

/-!
# WOTS+C, both schemes

Every addressed hash input is P | A | M with P, each value of M and each half of A 16 bytes (A is one cell in leanXMSS, two in leanSPHINCS), so each is one cell: a hash's output feeds the next hash where it lands, and a hinted value needs no check of its own, every cell being a 16-byte value. A chain's steps land in fixed slots of a `walks` run, so its tip is one cell whatever the digit, read there by the leaf's hash.
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- A node is not ordered against its sibling: the two children are hinted in order, at kids[k] and kids[k + 1], and `node` is checked to be the one `bit` names, the left one at 0, the right one at 1. One product, stored where the left child's difference already is, which is the assert. -/
def isChild (node : Word) (kids : List V) (k : Nat) (bit : Word) : B Unit := B.inline "is_child" do
  let check ← B.stackBuf 1
  check[0] := node + kids[k]
  check[0] := bit * (kids[k] + kids[k + 1])

/-- Chain i's tip, in the last of its CHAIN_STEPS slots of `walks`. -/
def chainTip (walks : List V) (i : Nat) : B Word := B.inline "chain_tip" do
  let tip := walks[(i + 1) * CHAIN_STEPS - 1]
  return tip

/-- Walk chain i from position k to its end, the step leaving position s landing in chain i's slot s of `walks`, so the tip is chain_tip(walks, i) whatever k is. A leanSPHINCS step's address is at[0] and at[1] with i and s added, the value last; a leanXMSS one carries only s, at[s] computed once per key, i riding after the value, read off a cell set outside the dispatch (the zero cell, `powers` or `tags`), so an arm names it rather than setting it again. -/
def walk (at' : List V) (pp : Word) (walks : List V) (tags : List V) (powers : List V) (i : Nat) (k : Nat) (lx : Nat) : B Unit := B.inline "walk" do
  let mut tag : FW := default
  if lx = 1 then
    if i = 0 then
      tag := FW.c (lit 0)
    else if arrInt LX_TAG_SLOT i = 0 then
      tag := FW.w powers[arrInt LX_TAG_LOG i]
    else
      tag := FW.w tags[arrInt LX_TAG_SLOT i - 1]
  if k = CHAIN_STEPS then
    B.witness "chain_starts" (.stack walks[(i + 1) * CHAIN_STEPS - 1:(i + 1) * CHAIN_STEPS])
  else
    let mut value ← hinted (B.witnessCell "chain_starts")
    for s in [k:CHAIN_STEPS] do
      let o := CHAIN_STEPS * i + s
      if lx = 1 then
        B.keccak (.words [.cell pp.v, .cell at'[s].v]) (.words [.cell value.v, (← tag.msg)]) walks[o:o + 1]
      else
        B.keccak (.words [.cell pp.v, .cell at'[0].v]) (.words [.cell (← val (at'[1] + lit (i * SP_WORD2_MUL + s * SP_WORD3_MUL_0))).v, .cell value.v]) walks[o:o + 1]
      value := walks[o]

/-- The n chains from `first` on, at the digits of k (its low n), one dispatch for all of them. Folds the digits' sum into `product`, in the exponent (`powers[s]` is GEN ** s), and the digits into `encoded`, where the encoding digest holds them: leanXMSS's low first, leanSPHINCS's most significant first in each byte (base_2b).
-/
def walkGroup (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : FW) (encoded : FW) (dsts : List V) : B Unit := B.inline "walk_group" do
  for r in [0:n] do
    walk at' pp walks tags powers (first + r) (k / CHAIN_LENGTH ^ r % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := k % CHAIN_LENGTH ^ n * CHAIN_LENGTH ^ first
  else
    digits := 0
    for r in [0:n] do
      digits := digits + k / 4 ^ r % 4 * 2 ^ (8 * ((first + r) / 4) + 2 * (4 - 1 - (first + r) % 4))
  dsts[0] := product * Ex.v powers[arrInt DIGIT_SUMS (k % CHAIN_LENGTH ^ n)]
  dsts[1] := encoded + digits

/-- Word j of a one-time leaf's input: the prefix (p0, p1), then the chain tips. -/
def leafWord (p0 : Word) (p1 : Word) (walks : List V) (j : Nat) : B Word := B.inline "leaf_word" do
  let mut w := p0
  if j = 1 then
    w := p1
  if j ≠ 0 then
    if j ≠ 1 then
      w ← chainTip walks (j - 2)
  return w

/-- The hash of the prefix (p0, p1) and the n chain tips, each read where its walk left it. -/
def wotsLeaf (p0 : Word) (p1 : Word) (walks : List V) (n : Nat) (leaf : List V) : B Unit := B.inline "wots_leaf" do
  let t0 ← leafWord p0 p1 walks 0
  let t1 ← leafWord p0 p1 walks 1
  let t2 ← leafWord p0 p1 walks 2
  let t3 ← leafWord p0 p1 walks 3
  let t4 ← leafWord p0 p1 walks 4
  let t5 ← leafWord p0 p1 walks 5
  let t6 ← leafWord p0 p1 walks 6
  let t7 ← leafWord p0 p1 walks 7
  let t8 ← leafWord p0 p1 walks 8
  let t9 ← leafWord p0 p1 walks 9
  let t10 ← leafWord p0 p1 walks 10
  let t11 ← leafWord p0 p1 walks 11
  let t12 ← leafWord p0 p1 walks 12
  let t13 ← leafWord p0 p1 walks 13
  let t14 ← leafWord p0 p1 walks 14
  let t15 ← leafWord p0 p1 walks 15
  let t16 ← leafWord p0 p1 walks 16
  let t17 ← leafWord p0 p1 walks 17
  let t18 ← leafWord p0 p1 walks 18
  let t19 ← leafWord p0 p1 walks 19
  let t20 ← leafWord p0 p1 walks 20
  let t21 ← leafWord p0 p1 walks 21
  let t22 ← leafWord p0 p1 walks 22
  let t23 ← leafWord p0 p1 walks 23
  let t24 ← leafWord p0 p1 walks 24
  let t25 ← leafWord p0 p1 walks 25
  let t26 ← leafWord p0 p1 walks 26
  let t27 ← leafWord p0 p1 walks 27
  let t28 ← leafWord p0 p1 walks 28
  let t29 ← leafWord p0 p1 walks 29
  let t30 ← leafWord p0 p1 walks 30
  let t31 ← leafWord p0 p1 walks 31
  let t32 ← leafWord p0 p1 walks 32
  let t33 ← leafWord p0 p1 walks 33
  let t34 ← leafWord p0 p1 walks 34
  let t35 ← leafWord p0 p1 walks 35
  let t36 ← leafWord p0 p1 walks 36
  let t37 ← leafWord p0 p1 walks 37
  let t38 ← leafWord p0 p1 walks 38
  let t39 ← leafWord p0 p1 walks 39
  let t40 ← leafWord p0 p1 walks 40
  let t41 ← leafWord p0 p1 walks 41
  let t42 ← leafWord p0 p1 walks 42
  let t43 ← leafWord p0 p1 walks 43
  let t44 ← leafWord p0 p1 walks 44
  let t45 ← leafWord p0 p1 walks 45
  let t46 ← leafWord p0 p1 walks 46
  let t47 ← leafWord p0 p1 walks 47
  let t48 ← leafWord p0 p1 walks 48
  let t49 ← leafWord p0 p1 walks 49
  let t50 ← leafWord p0 p1 walks 50
  let t51 ← leafWord p0 p1 walks 51
  let t52 ← leafWord p0 p1 walks 52
  let t53 ← leafWord p0 p1 walks 53
  let t54 ← leafWord p0 p1 walks 54
  let t55 ← leafWord p0 p1 walks 55
  let t56 ← leafWord p0 p1 walks 56
  let t57 ← leafWord p0 p1 walks 57
  let t58 ← leafWord p0 p1 walks 58
  let t59 ← leafWord p0 p1 walks 59
  B.keccakCells [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59] leaf

end
end LeanVM.Guest.Program
