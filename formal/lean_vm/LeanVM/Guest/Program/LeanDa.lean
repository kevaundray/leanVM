/-
  LeanVM.Guest.Program.LeanDa

  The guest's section "LeanDA".
-/

module

public import LeanVM.Guest.Program.StatementsAndClaimLists

/-!
# LeanDA

Hash the encoded rows and build the membership vector from the challenge, then check their inner products. The external verifier derives the challenge from the root; recursion preserves both.
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- Returns the commitment H(tree root, n), two cells, and the membership challenge, one. The matrix always has DA_MAX_ROWS rows: a padding row's root is a constant, which the gap loop writes without hashing anything. -/
def daVerify : GFn where
  name := "da_verify"
  arity := 1
  rets := 3
  body ps := do
    let byteBits := ps[0]
    let nBlobG ← hinted (B.witnessCell "da_n_blobs")
    let gapG ← call1 "da_padding" [nBlobG]
    -- The challenge, hashed below as its two lanes and two zero ones.
    let z ← hinted (B.witnessCell "da_challenge")
    let t0 ← callN "da_vector" [z] 4
    let zs := t0[0]!
    let topLeaves := t0[1]!
    let cellFactors := t0[2]!
    let offsets := t0[3]!
    -- A blob's region: its tree, then its running sum, a fresh write-once cell per column.
    let blobs ← B.heapBufDyn (← val (nBlobG ^ DA_REGION))
    let rowbase ← B.heapBufDyn nBlobG
    B.loopRtF 0 (pure nBlobG) 2 (pure ([blobs.v, rowbase.v])) fun xi caps => do
      let blobs := caps[0]
      let rowbase := caps[1]
      let base ← val (blobs * xi ^ DA_REGION)
      rowbase[xi] := base
      base[GEN ^ DA_SUM] := 0
    B.loopConstF 0 DA_CELLS 6 (pure ([nBlobG.v, rowbase.v, zs.v, topLeaves.v, cellFactors.v, offsets.v])) fun xb caps => do
      let nBlobG := caps[0]
      let rowbase := caps[1]
      let zs := caps[2]
      let topLeaves := caps[3]
      let cellFactors := caps[4]
      let offsets := caps[5]
      call "da_verify_column" [xb, nBlobG, rowbase, zs, topLeaves, cellFactors, offsets]
      pure ()
    let roots ← B.heapBufDyn (← val (GEN ^ 128))
    B.loopRtF 0 (pure nBlobG) 2 (pure ([rowbase.v, roots.v])) fun xi caps => do
      let rowbase := caps[0]
      let roots := caps[1]
      let base ← val rowbase[xi]
      assert base[GEN ^ 640] == 0
      let t0 ← callN (instName "da_levels" [.L DA_CELLS, .L DA_BLOCK_BITS]) [base] 2
      let b0 := t0[0]!
      let b1 := t0[1]!
      let slot ← val (roots * xi ^ 2)
      slot[GEN ^ 0] := b0
      slot[GEN ^ 1] := b1
    B.loopRtF 0 (pure gapG) 2 (pure ([roots.v, nBlobG.v])) fun xd caps => do
      let roots := caps[0]
      let nBlobG := caps[1]
      let pad ← val (roots * nBlobG ^ 2 * xd ^ 2)
      pad[GEN ^ 0] := lit DA_PAD_BLOB_0
      pad[GEN ^ 1] := lit DA_PAD_BLOB_1
    let t1 ← callN (instName "da_levels" [.L DA_MAX_ROWS, .L DA_LOG_MAX_ROWS]) [roots] 2
    let r0 := t1[0]!
    let r1 := t1[1]!
    let commitment ← B.stackBuf 2
    B.keccak [r0, r1] (.words [.cell (← val byteBits[nBlobG]).v, .zero]) commitment
    return [.v commitment[0].v, .v commitment[1].v, .v z.v]

/-- g^(DA_MAX_ROWS - n) padding rows, for n_blob_g = g^n with 1 <= n <= DA_MAX_ROWS. -/
def daPadding : GFn where
  name := "da_padding"
  arity := 1
  rets := 1
  body ps := do
    let nBlobG := ps[0]
    assert nBlobG != 1
    assert log nBlobG < 33
    let t0 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val (GEN ^ DA_MAX_ROWS / nBlobG))
    return [.into t0]

/-- Column log(xb) of every blob: its weights expand the tree inside a cell from the column's leaf of the tree above; a cell's digest is leaf log(xb) of its blob's tree, and its inner product with the weights joins its blob's running sum. -/
def daVerifyColumn : GFn where
  name := "da_verify_column"
  arity := 7
  rets := 0
  body ps := do
    let xb := ps[0]
    let nBlobG := ps[1]
    let rowbase := ps[2]
    let zs := ps[3]
    let topLeaves := ps[4]
    let cellFactors := ps[5]
    let offsets := ps[6]
    let lvals ← call1 (instName "da_expand" [.L (LOG_CELL_SYMBOLS - 1), .L LOG_CELL_SYMBOLS]) [topLeaves[xb], cellFactors, zs, offsets * xb ^ LOG_CELL_SYMBOLS]
    let xb2 ← val (xb * xb)
    B.loopRtF 0 (pure nBlobG) 4 (pure ([lvals.v, rowbase.v, xb.v, xb2.v])) fun xi caps => do
      let lvals := caps[0]
      let rowbase := caps[1]
      let xb := caps[2]
      let xb2 := caps[3]
      let t0 ← callN "da_verify_cell" [lvals] 3
      let d0 := t0[0]!
      let d1 := t0[1]!
      let s := t0[2]!
      let base ← val rowbase[xi]
      let chain ← val (base * xb)
      chain[GEN ^ 513] := chain[GEN ^ DA_SUM] + s
      let leaf ← val (base * xb2)
      leaf[GEN ^ 0] := d0
      leaf[GEN ^ 1] := d1
    return []

/-- A symbol is a word of E, so the hash and the inner product read the hinted cell as is. -/
def daVerifyCell : GFn where
  name := "da_verify_cell"
  arity := 1
  rets := 3
  body ps := do
    let lvals := ps[0]
    let sym ← B.stackBuf DA_CELL
    B.witness "da_symbols" (.stack sym)
    let mut s : FW := FW.c (lit 0)
    for e in [0:DA_CELL] do
      s ← fold (s + lvals[GEN ^ e] * sym[e])
    let st ← B.stackBuf 2
    B.keccakCells sym st
    return [.v st[0].v, .v st[1].v, Ex.ret s]

/-- The internal levels of a Merkle tree whose leaves already sit at level 0 of `tree` (2 cells a node, level lvl at 4n - 4n//2**lvl). Returns the root pair. -/
def daLevels (n : Nat) (logN : Nat) : GFn where
  name := instName "da_levels" [.L n, .L logN]
  arity := 1
  rets := 2
  body ps := do
    let tree := ps[0]
    for lvl in [0:logN] do
      B.loopRtF 0 (B.const (gpowE (n / (2 ^ (lvl + 1))))) 1 (pure ([tree.v])) fun xp caps => do
        let tree := caps[0]
        let a ← val (tree * GEN ^ (4 * n - 4 * n / 2 ^ lvl) * xp ^ 4)
        let b ← val (tree * GEN ^ (4 * n - 4 * n / 2 ^ (lvl + 1)) * (xp * xp))
        B.keccak (.cells (.heap a.v 0 2)) (.cells (.heap a.v 2 (4 - 2))) (.heap b.v 0 2)
    return [.load tree.v (4 * n - 4), .load tree.v (4 * n - 3)]

/-- L(x) = prod_(j < LOG_BLOB_SYMBOLS) (1 + z_j Vhat_j(x)), z_j = z^(2^j), as a binary tree over x's bits from the top down: factor j depends only on the bits from j up, so a node is its parent times one factor. The tree over the cell index runs once; each column expands the tree inside a cell from its leaf, its factors shifted by the cell index's part of each Vhat_j (da_column_offsets). -/
def daVector : GFn where
  name := "da_vector"
  arity := 1
  rets := 4
  body ps := do
    let z := ps[0]
    let zs ← B.heapBuf DA_LOG_M
    let mut zj := z
    for j in [0:LOG_BLOB_SYMBOLS] do
      zs[GEN ^ j] := zj
      zj ← val (zj * zj)
    zs[GEN ^ LOG_BLOB_SYMBOLS] := 0  -- the top bit splits without a factor: the degree bound
    let aboveTop ← B.heapBuf DA_LOG_M  -- nothing sits above the tree over the cell index
    for j in [LOG_CELL_SYMBOLS:DA_LOG_M] do
      aboveTop[GEN ^ j] := 0
    let topFactors ← call1 (instName "da_factors" [.L LOG_BLOB_SYMBOLS, .L DA_BLOCK_BITS, .L 0]) [zs]
    let topLeaves ← call1 (instName "da_expand" [.L LOG_BLOB_SYMBOLS, .L DA_BLOCK_BITS]) [1, topFactors, zs, aboveTop]
    let cellFactors ← call1 (instName "da_factors" [.L (LOG_CELL_SYMBOLS - 1), .L LOG_CELL_SYMBOLS, .L DA_CELLS]) [zs]
    let offsets ← call1 "da_column_offsets" [zs]
    return [.v zs.v, .v topLeaves.v, .v cellFactors.v, .v offsets.v]

/-- 1 + z_j Vhat_j(x) for each parent node n of a product tree over bits top, top - 1, ..., in heap order: j the bit n splits and x the point its path's bits make, DA_VHAT[at + n]. -/
def daFactors (top : Nat) (depth : Nat) (at' : Nat) : GFn where
  name := instName "da_factors" [.L top, .L depth, .L at']
  arity := 1
  rets := 1
  body ps := do
    let zs := ps[0]
    let factors ← B.heapBuf DA_CELL  -- the deepest tree's parents, the one inside a cell
    for d in [0:depth] do
      let z ← val zs[GEN ^ (top - d)]
      for y in [0:2 ^ d] do
        factors[GEN ^ (2 ^ d + y)] := z * arrWord DA_VHAT (at' + 2 ^ d + y) + 1
    return [.v factors.v]

/-- The product tree below `root` over bits top, top - 1, ..., in heap order: node n's children 2n and 2n + 1 are n times its factor at the two values of the bit j it splits, factors[n] + shifts[j] and that plus z_j. Returns a pointer to its leaves. -/
def daExpand (top : Nat) (depth : Nat) : GFn where
  name := instName "da_expand" [.L top, .L depth]
  arity := 4
  rets := 1
  body ps := do
    let root := ps[0]
    let factors := ps[1]
    let zs := ps[2]
    let shifts := ps[3]
    let nodes ← B.stackBuf 256  -- the deepest tree's, the one inside a cell
    nodes[1] := root
    for d in [0:depth] do
      let z ← val zs[GEN ^ (top - d)]
      let shift ← val shifts[GEN ^ (top - d)]
      for y in [0:2 ^ d] do
        nodes[2 ^ (d + 1) + 2 * y] := nodes[2 ^ d + y] * (factors[GEN ^ (2 ^ d + y)] + shift)
        nodes[2 ^ (d + 1) + 2 * y + 1] := nodes[2 ^ (d + 1) + 2 * y] + nodes[2 ^ d + y] * z
    let leaves ← B.addr nodes
    return [Ex.ret (leaves * GEN ^ (2 ^ depth))]

/-- offsets[LOG_CELL_SYMBOLS * h + j] = z_j Vhat_j at the cell index h's bits, for each factor j inside a cell: zero at h = 0, then one doubling per bit of h. -/
def daColumnOffsets : GFn where
  name := "da_column_offsets"
  arity := 1
  rets := 1
  body ps := do
    let zs := ps[0]
    let offsets ← B.heapBuf 896
    for j in [0:LOG_CELL_SYMBOLS] do
      offsets[GEN ^ j] := 0
    for b in [0:DA_BLOCK_BITS] do
      let steps ← B.heapBuf LOG_CELL_SYMBOLS
      for j in [0:LOG_CELL_SYMBOLS] do
        steps[GEN ^ j] := zs[GEN ^ j] * arrWord DA_VHAT_COLUMN (LOG_CELL_SYMBOLS * b + j)
      B.loopRtF 0 (B.const (gpowE (2 ^ b))) 2 (pure ([offsets.v, steps.v])) fun xh caps => do
        let offsets := caps[0]
        let steps := caps[1]
        let src ← val (offsets * xh ^ LOG_CELL_SYMBOLS)
        let dst : Shifted := ⟨src, LOG_CELL_SYMBOLS * 2 ^ b⟩
        for j in [0:LOG_CELL_SYMBOLS] do
          dst[GEN ^ j] := src[GEN ^ j] + steps[GEN ^ j]
    return [.v offsets.v]

end
end LeanVM.Guest.Program
