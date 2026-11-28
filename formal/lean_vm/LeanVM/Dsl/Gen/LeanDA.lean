/-
  LeanVM.Dsl.Gen.LeanDA

  The guest's section `LeanDA`, translated.
-/

module

public import LeanVM.Dsl.Gen.Inline

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

set_option linter.unusedVariables false in
/-- `da_verify` (`guests/lean_ethereum.py`, line 4545):

```
def da_verify(byte_bits):
    # Returns the commitment H(tree root, n), two cells, and the membership challenge, one.
    # The matrix always has DA_MAX_ROWS rows: a padding row's root is a constant, which
    # the gap loop writes without hashing anything.
    n_blob_g = hint_witness("da_n_blobs")
    gap_g = da_padding(n_blob_g)

    # The challenge, hashed below as its two lanes and two zero ones.
    z = hint_witness("da_challenge")
    zs, top_leaves, cell_factors, offsets = da_vector(z)

    # A blob's region: its tree, then its running sum, a fresh write-once cell per column.
    blobs = HeapBuf(n_blob_g ** DA_REGION)
    rowbase = HeapBuf(n_blob_g)
    for xi in mul_range(1, n_blob_g):
        base = blobs * (xi ** DA_REGION)
        rowbase[xi] = base
        base[GEN ** DA_SUM] = 0

    for xb in mul_range(1, GEN ** DA_CELLS):
        da_verify_column(xb, n_blob_g, rowbase, zs, top_leaves, cell_factors, offsets)

    roots = HeapBuf(GEN ** (4 * DA_MAX_ROWS))
    for xi in mul_range(1, n_blob_g):
        base = rowbase[xi]
        assert base[GEN ** (DA_SUM + DA_CELLS)] == 0
        b0, b1 = da_levels(base, DA_CELLS, DA_BLOCK_BITS)
        slot = roots * (xi ** 2)
        slot[1] = b0
        slot[GEN] = b1
    for xd in mul_range(1, gap_g):
        pad = roots * (n_blob_g ** 2) * (xd ** 2)
        pad[1] = DA_PAD_BLOB_0
        pad[GEN] = DA_PAD_BLOB_1
    r0, r1 = da_levels(roots, DA_MAX_ROWS, DA_LOG_MAX_ROWS)
    commitment = StackBuf(2)
    keccak([r0, r1], [byte_bits[n_blob_g], 0], commitment)
    return commitment[0], commitment[1], z
```
-/
def daVerify : GFn where
  name := "da_verify"
  arity := 1
  rets := 3
  body ps := do
    let byteBits := cellOf ps 0
    let nBlobG ← hinted (B.witnessCell "da_n_blobs")
    let gapG ← call1 "da_padding" [nBlobG.v]
    let z ← hinted (B.witnessCell "da_challenge")
    let t0 ← B.call "da_vector" [z.v] 4
    let zs := t0[0]!
    let topLeaves := t0[1]!
    let cellFactors := t0[2]!
    let offsets := t0[3]!
    let blobs ← B.heapBufDyn (← B.pow nBlobG DA_REGION)
    let rowbase ← B.heapBufDyn nBlobG
    B.loopRtF 0 (pure nBlobG) 2 (pure ([blobs.v, rowbase.v])) fun xi caps => do
      let blobs := cellOf caps 0
      let rowbase := cellOf caps 1
      let base ← B.mul blobs (← B.pow xi DA_REGION)
      B.store (← B.mul rowbase xi) 0 base
      B.store base DA_SUM (← B.const 0)
    B.loopConstF 0 DA_CELLS 6 (pure ([nBlobG.v, rowbase.v, zs.v, topLeaves.v, cellFactors.v, offsets.v])) fun xb caps => do
      let nBlobG := cellOf caps 0
      let rowbase := cellOf caps 1
      let zs := cellOf caps 2
      let topLeaves := cellOf caps 3
      let cellFactors := cellOf caps 4
      let offsets := cellOf caps 5
      let _ ← B.call "da_verify_column" [xb.v, nBlobG.v, rowbase.v, zs.v, topLeaves.v, cellFactors.v, offsets.v] 0
      pure ()
    let roots ← B.heapBufDyn (← B.const (gpowE 128))
    B.loopRtF 0 (pure nBlobG) 2 (pure ([rowbase.v, roots.v])) fun xi caps => do
      let rowbase := cellOf caps 0
      let roots := cellOf caps 1
      let base ← B.load (← B.mul rowbase xi) 0
      B.assertEq (← B.load base 640) (← B.const 0)
      let t0 ← B.call (instName "da_levels" [.L DA_CELLS, .L DA_BLOCK_BITS]) [base.v] 2
      let b0 := t0[0]!
      let b1 := t0[1]!
      let slot ← B.mul roots (← B.pow xi 2)
      B.store slot 0 b0
      B.store slot 1 b1
    B.loopRtF 0 (pure gapG) 2 (pure ([roots.v, nBlobG.v])) fun xd caps => do
      let roots := cellOf caps 0
      let nBlobG := cellOf caps 1
      let pad ← B.mul (← B.mul roots (← B.pow nBlobG 2)) (← B.pow xd 2)
      B.store pad 0 (← B.const (lit DA_PAD_BLOB_0))
      B.store pad 1 (← B.const (lit DA_PAD_BLOB_1))
    let t1 ← B.call (instName "da_levels" [.L DA_MAX_ROWS, .L DA_LOG_MAX_ROWS]) [roots.v] 2
    let r0 := t1[0]!
    let r1 := t1[1]!
    let commitment ← B.stackBuf 2
    B.keccak (a := (.words [.cell r0.v, .cell r1.v])) (b := (.words [.cell (← B.load (← B.mul byteBits nBlobG) 0).v, .zero])) (out := (.frame commitment))
    return [.v (cellOf commitment 0).v] ++ [.v (cellOf commitment 1).v] ++ [.v z.v]

set_option linter.unusedVariables false in
/-- `da_padding` (`guests/lean_ethereum.py`, line 4585):

```
def da_padding(n_blob_g):
    # g^(DA_MAX_ROWS - n) padding rows, for n_blob_g = g^n with 1 <= n <= DA_MAX_ROWS.
    assert n_blob_g != 1
    assert log(n_blob_g) < DA_MAX_ROWS + 1
    return GEN ** DA_MAX_ROWS / n_blob_g
```
-/
def daPadding : GFn where
  name := "da_padding"
  arity := 1
  rets := 1
  body ps := do
    let nBlobG := cellOf ps 0
    B.assertNe nBlobG (← B.const 1)
    let _ ← B.rangeCheck nBlobG 33
    let t0 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.fdiv (← B.const (gpowE DA_MAX_ROWS)) nBlobG)
    return [.into t0]

set_option linter.unusedVariables false in
/-- `da_verify_column` (`guests/lean_ethereum.py`, line 4592):

```
def da_verify_column(xb, n_blob_g, rowbase, zs, top_leaves, cell_factors, offsets):
    # Column log(xb) of every blob: its weights expand the tree inside a cell from the
    # column's leaf of the tree above; a cell's digest is leaf log(xb) of its blob's tree,
    # and its inner product with the weights joins its blob's running sum.
    lvals = da_expand(top_leaves[xb], cell_factors, zs, offsets * xb ** LOG_CELL_SYMBOLS, LOG_CELL_SYMBOLS - 1, LOG_CELL_SYMBOLS)
    xb2 = xb * xb
    for xi in mul_range(1, n_blob_g):
        d0, d1, s = da_verify_cell(lvals)
        base = rowbase[xi]
        chain = base * xb
        chain[GEN ** (DA_SUM + 1)] = chain[GEN ** DA_SUM] + s
        leaf = base * xb2
        leaf[1] = d0
        leaf[GEN] = d1
    return
```
-/
def daVerifyColumn : GFn where
  name := "da_verify_column"
  arity := 7
  rets := 0
  body ps := do
    let xb := cellOf ps 0
    let nBlobG := cellOf ps 1
    let rowbase := cellOf ps 2
    let zs := cellOf ps 3
    let topLeaves := cellOf ps 4
    let cellFactors := cellOf ps 5
    let offsets := cellOf ps 6
    let lvals ← call1 (instName "da_expand" [.L (LOG_CELL_SYMBOLS - 1), .L LOG_CELL_SYMBOLS]) [(← B.load (← B.mul topLeaves xb) 0).v, cellFactors.v, zs.v, (← B.mul offsets (← B.pow xb LOG_CELL_SYMBOLS)).v]
    let xb2 ← B.mul xb xb
    B.loopRtF 0 (pure nBlobG) 4 (pure ([lvals.v, rowbase.v, xb.v, xb2.v])) fun xi caps => do
      let lvals := cellOf caps 0
      let rowbase := cellOf caps 1
      let xb := cellOf caps 2
      let xb2 := cellOf caps 3
      let t0 ← B.call "da_verify_cell" [lvals.v] 3
      let d0 := t0[0]!
      let d1 := t0[1]!
      let s := t0[2]!
      let base ← B.load (← B.mul rowbase xi) 0
      let chain ← B.mul base xb
      B.store chain 513 (← B.add (← B.load chain DA_SUM) s)
      let leaf ← B.mul base xb2
      B.store leaf 0 d0
      B.store leaf 1 d1
    return []

set_option linter.unusedVariables false in
/-- `da_verify_cell` (`guests/lean_ethereum.py`, line 4609):

```
def da_verify_cell(lvals):
    # A symbol is a word of E, so the hash and the inner product read the hinted cell as is.
    sym = StackBuf(DA_CELL)
    hint_witness(sym, "da_symbols")
    s = 0
    for e in unroll(0, DA_CELL):
        s = s + lvals[GEN ** e] * sym[e]
    st = StackBuf(2)
    keccak_cells(sym, st)
    return st[0], st[1], s
```
-/
def daVerifyCell : GFn where
  name := "da_verify_cell"
  arity := 1
  rets := 3
  body ps := do
    let lvals := cellOf ps 0
    let sym ← B.stackBuf DA_CELL
    B.witness "da_symbols" (.stack sym)
    let s := 0
    let mut s_word : Word := default
    let e_k := 0
    s_word ← B.mul (← B.load lvals e_k) (cellOf sym e_k)
    for e_k in [1:DA_CELL] do
      s_word ← B.add s_word (← B.mul (← B.load lvals e_k) (cellOf sym e_k))
    let st ← B.stackBuf 2
    B.keccakCells (cells := (.cells (.frame sym))) (out := (.frame st))
    return [.v (cellOf st 0).v] ++ [.v (cellOf st 1).v] ++ [.v s_word.v]

set_option linter.unusedVariables false in
/-- `da_vector` (`guests/lean_ethereum.py`, line 4632):

```
def da_vector(z):
    # L(x) = prod_(j < LOG_BLOB_SYMBOLS) (1 + z_j Vhat_j(x)), z_j = z^(2^j), as a binary tree over
    # x's bits from the top down: factor j depends only on the bits from j up, so a node
    # is its parent times one factor. The tree over the cell index runs once; each column
    # expands the tree inside a cell from its leaf, its factors shifted by the cell
    # index's part of each Vhat_j (da_column_offsets).
    zs = HeapBuf(DA_LOG_M)
    zj = z
    for j in unroll(0, LOG_BLOB_SYMBOLS):
        zs[GEN ** j] = zj
        zj = zj * zj
    zs[GEN ** LOG_BLOB_SYMBOLS] = 0  # the top bit splits without a factor: the degree bound
    above_top = HeapBuf(DA_LOG_M)  # nothing sits above the tree over the cell index
    for j in unroll(LOG_CELL_SYMBOLS, DA_LOG_M):
        above_top[GEN ** j] = 0
    top_factors = da_factors(zs, LOG_BLOB_SYMBOLS, DA_BLOCK_BITS, 0)
    top_leaves = da_expand(1, top_factors, zs, above_top, LOG_BLOB_SYMBOLS, DA_BLOCK_BITS)
    cell_factors = da_factors(zs, LOG_CELL_SYMBOLS - 1, LOG_CELL_SYMBOLS, DA_CELLS)
    offsets = da_column_offsets(zs)
    return zs, top_leaves, cell_factors, offsets
```
-/
def daVector : GFn where
  name := "da_vector"
  arity := 1
  rets := 4
  body ps := do
    let z := cellOf ps 0
    let zs ← B.heapBuf DA_LOG_M
    let mut zj := z
    for j_k in [0:LOG_BLOB_SYMBOLS] do
      B.store zs j_k zj
      zj ← B.mul zj zj
    B.store zs LOG_BLOB_SYMBOLS (← B.const 0)
    let aboveTop ← B.heapBuf DA_LOG_M
    for j_k in [LOG_CELL_SYMBOLS:DA_LOG_M] do
      B.store aboveTop j_k (← B.const 0)
    let topFactors ← call1 (instName "da_factors" [.L LOG_BLOB_SYMBOLS, .L DA_BLOCK_BITS, .L 0]) [zs.v]
    let topLeaves ← call1 (instName "da_expand" [.L LOG_BLOB_SYMBOLS, .L DA_BLOCK_BITS]) [(← B.const 1).v, topFactors.v, zs.v, aboveTop.v]
    let cellFactors ← call1 (instName "da_factors" [.L (LOG_CELL_SYMBOLS - 1), .L LOG_CELL_SYMBOLS, .L DA_CELLS]) [zs.v]
    let offsets ← call1 "da_column_offsets" [zs.v]
    return [.v zs.v] ++ [.v topLeaves.v] ++ [.v cellFactors.v] ++ [.v offsets.v]

set_option linter.unusedVariables false in
/-- `da_column_offsets` (`guests/lean_ethereum.py`, line 4681):

```
def da_column_offsets(zs):
    # offsets[LOG_CELL_SYMBOLS * h + j] = z_j Vhat_j at the cell index h's bits, for each factor
    # j inside a cell: zero at h = 0, then one doubling per bit of h.
    offsets = HeapBuf(LOG_CELL_SYMBOLS * DA_CELLS)
    for j in unroll(0, LOG_CELL_SYMBOLS):
        offsets[GEN ** j] = 0
    for b in unroll(0, DA_BLOCK_BITS):
        steps = HeapBuf(LOG_CELL_SYMBOLS)
        for j in unroll(0, LOG_CELL_SYMBOLS):
            steps[GEN ** j] = zs[GEN ** j] * DA_VHAT_COLUMN[LOG_CELL_SYMBOLS * b + j]
        for xh in mul_range(1, GEN ** (2 ** b)):
            src = offsets * xh ** LOG_CELL_SYMBOLS
            dst = src * GEN ** (LOG_CELL_SYMBOLS * 2 ** b)
            for j in unroll(0, LOG_CELL_SYMBOLS):
                dst[GEN ** j] = src[GEN ** j] + steps[GEN ** j]
    return offsets
```
-/
def daColumnOffsets : GFn where
  name := "da_column_offsets"
  arity := 1
  rets := 1
  body ps := do
    let zs := cellOf ps 0
    let offsets ← B.heapBuf 896
    for j_k in [0:LOG_CELL_SYMBOLS] do
      B.store offsets j_k (← B.const 0)
    for b_k in [0:DA_BLOCK_BITS] do
      let steps ← B.heapBuf LOG_CELL_SYMBOLS
      for j_k in [0:LOG_CELL_SYMBOLS] do
        B.store steps j_k (← B.mul (← B.load zs j_k) (← B.const (arrWord DA_VHAT_COLUMN ((LOG_CELL_SYMBOLS * b_k) + j_k))))
      B.loopRtF 0 (B.const (gpowE (2 ^ b_k))) 2 (pure ([offsets.v, steps.v])) fun xh caps => do
        let offsets := cellOf caps 0
        let steps := cellOf caps 1
        let src ← B.mul offsets (← B.pow xh LOG_CELL_SYMBOLS)
        let dst : Shifted := ⟨src, LOG_CELL_SYMBOLS * (2 ^ b_k)⟩
        for j_k in [0:LOG_CELL_SYMBOLS] do
          B.store dst.base (dst.exp + j_k) (← B.add (← B.load src j_k) (← B.load steps j_k))
    return [.v offsets.v]

set_option linter.unusedVariables false in
/-- `da_levels`, a `Const` family (`guests/lean_ethereum.py`, line 4621):

```
def da_levels(tree, n: Const, log_n: Const):
    # The internal levels of a Merkle tree whose leaves already sit at level 0 of
    # `tree` (2 cells a node, level lvl at 4n - 4n//2**lvl). Returns the root pair.
    for lvl in unroll(0, log_n):
        for xp in mul_range(1, GEN ** (n // 2 ** (lvl + 1))):
            a = tree * (GEN ** (4 * n - 4 * n // 2 ** lvl)) * (xp ** 4)
            b = tree * (GEN ** (4 * n - 4 * n // 2 ** (lvl + 1))) * (xp * xp)
            keccak(a[0:2], a[2:4], b[0:2])
    return tree[GEN ** (4 * n - 4)], tree[GEN ** (4 * n - 3)]
```
-/
def daLevels (n : Nat) (logN : Nat) : GFn where
  name := instName "da_levels" [.L n, .L logN]
  arity := 1
  rets := 2
  body ps := do
    let tree := cellOf ps 0
    let lvl_k := 0
    B.loopRtF 0 (B.const (gpowE (n / (2 ^ (lvl_k + 1))))) 1 (pure ([tree.v])) fun xp caps => do
      let tree := cellOf caps 0
      let a ← B.mul tree (← B.pow xp 4)
      let b ← B.mul (← B.shifted tree ((4 * n) - ((4 * n) / (2 ^ (lvl_k + 1))))) (← B.mul xp xp)
      B.keccak (a := (.cells (.heap a.v 0 2))) (b := (.cells (.heap a.v 2 (4 - 2)))) (out := (.heap b.v 0 2))
    for lvl_k in [1:logN] do
      B.loopRtF 0 (B.const (gpowE (n / (2 ^ (lvl_k + 1))))) 1 (pure ([tree.v])) fun xp caps => do
        let tree := cellOf caps 0
        let a ← B.mul (← B.shifted tree ((4 * n) - ((4 * n) / (2 ^ lvl_k)))) (← B.pow xp 4)
        let b ← B.mul (← B.shifted tree ((4 * n) - ((4 * n) / (2 ^ (lvl_k + 1))))) (← B.mul xp xp)
        B.keccak (a := (.cells (.heap a.v 0 2))) (b := (.cells (.heap a.v 2 (4 - 2)))) (out := (.heap b.v 0 2))
    return [.load tree.v ((4 * n) - 4)] ++ [.load tree.v ((4 * n) - 3)]

set_option linter.unusedVariables false in
/-- `da_expand`, a `Const` family (`guests/lean_ethereum.py`, line 4665):

```
def da_expand(root, factors, zs, shifts, top: Const, depth: Const):
    # The product tree below `root` over bits top, top - 1, ..., in heap order: node n's
    # children 2n and 2n + 1 are n times its factor at the two values of the bit j it
    # splits, factors[n] + shifts[j] and that plus z_j. Returns a pointer to its leaves.
    nodes = StackBuf(2 * DA_CELL)  # the deepest tree's, the one inside a cell
    nodes[1] = root
    for d in unroll(0, depth):
        z = zs[GEN ** (top - d)]
        shift = shifts[GEN ** (top - d)]
        for y in unroll(0, 2 ** d):
            nodes[2 ** (d + 1) + 2 * y] = nodes[2 ** d + y] * (factors[GEN ** (2 ** d + y)] + shift)
            nodes[2 ** (d + 1) + 2 * y + 1] = nodes[2 ** (d + 1) + 2 * y] + nodes[2 ** d + y] * z
    leaves = addr(nodes)
    return leaves * GEN ** (2 ** depth)
```
-/
def daExpand (top : Nat) (depth : Nat) : GFn where
  name := instName "da_expand" [.L top, .L depth]
  arity := 4
  rets := 1
  body ps := do
    let root := cellOf ps 0
    let factors := cellOf ps 1
    let zs := cellOf ps 2
    let shifts := cellOf ps 3
    let nodes ← B.stackBuf 256
    B.copy (cellOf nodes 1) root
    let d_k := 0
    let z ← B.load zs (top - d_k)
    let shift ← B.load shifts (top - d_k)
    let y_k := 0
    B.mulInto (cellOf nodes ((2 ^ (d_k + 1)) + (2 * y_k))) (cellOf nodes ((2 ^ d_k) + y_k)) (← B.add (← B.load factors ((2 ^ d_k) + y_k)) shift)
    B.addInto (cellOf nodes (((2 ^ (d_k + 1)) + (2 * y_k)) + 1)) (cellOf nodes ((2 ^ (d_k + 1)) + (2 * y_k))) (← B.mul (cellOf nodes ((2 ^ d_k) + y_k)) z)
    for d_k in [1:depth] do
      let z ← B.load zs (top - d_k)
      let shift ← B.load shifts (top - d_k)
      for y_k in [0:2 ^ d_k] do
        B.mulInto (cellOf nodes ((2 ^ (d_k + 1)) + (2 * y_k))) (cellOf nodes ((2 ^ d_k) + y_k)) (← B.add (← B.load factors ((2 ^ d_k) + y_k)) shift)
        B.addInto (cellOf nodes (((2 ^ (d_k + 1)) + (2 * y_k)) + 1)) (cellOf nodes ((2 ^ (d_k + 1)) + (2 * y_k))) (← B.mul (cellOf nodes ((2 ^ d_k) + y_k)) z)
    let leaves ← B.addr nodes
    let t0 : V → B Unit := fun rc => do
      B.mulInto (wordOf rc) leaves (← B.const (gpowE (2 ^ depth)))
    return [.into t0]

set_option linter.unusedVariables false in
/-- `da_factors`, a `Const` family (`guests/lean_ethereum.py`, line 4654):

```
def da_factors(zs, top: Const, depth: Const, at: Const):
    # 1 + z_j Vhat_j(x) for each parent node n of a product tree over bits top, top - 1, ...,
    # in heap order: j the bit n splits and x the point its path's bits make, DA_VHAT[at + n].
    factors = HeapBuf(DA_CELL)  # the deepest tree's parents, the one inside a cell
    for d in unroll(0, depth):
        z = zs[GEN ** (top - d)]
        for y in unroll(0, 2 ** d):
            factors[GEN ** (2 ** d + y)] = z * DA_VHAT[at + 2 ** d + y] + 1
    return factors
```
-/
def daFactors (top : Nat) (depth : Nat) (at' : Nat) : GFn where
  name := instName "da_factors" [.L top, .L depth, .L at']
  arity := 1
  rets := 1
  body ps := do
    let zs := cellOf ps 0
    let factors ← B.heapBuf DA_CELL
    let d_k := 0
    let z ← B.load zs (top - d_k)
    let y_k := 0
    B.store factors ((2 ^ d_k) + y_k) (← B.add (← B.mul z (← B.const (arrWord DA_VHAT ((at' + (2 ^ d_k)) + y_k)))) (← B.const 1))
    for d_k in [1:depth] do
      let z ← B.load zs (top - d_k)
      for y_k in [0:2 ^ d_k] do
        B.store factors ((2 ^ d_k) + y_k) (← B.add (← B.mul z (← B.const (arrWord DA_VHAT ((at' + (2 ^ d_k)) + y_k)))) (← B.const 1))
    return [.v factors.v]

end
end LeanVM.Dsl.Gen
