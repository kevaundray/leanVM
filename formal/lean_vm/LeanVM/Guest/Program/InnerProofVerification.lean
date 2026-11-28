/-
  LeanVM.Guest.Program.InnerProofVerification

  The guest's section "inner-proof verification".
-/

module

public import LeanVM.Guest.Program.StackedWhirOpening

/-!
# Inner-proof verification

The phases of `verify_sub`, in the order it runs them. Each takes and returns the Fiat-Shamir state pair and the stream cursor, so the sequence is what binds them.
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- The trees' claims batched by powers of the combiner, tree t at lam^t. -/
def gkrCombine (vals : List V) (lam : Word) : B Word := B.inline "gkr_combine" do
  let mut claim := vals[N_GKR_TREES - 1]
  for i in [1:N_GKR_TREES] do
    claim ← val (vals[N_GKR_TREES - 1 - i] + lam * claim)
  return claim

/-- Every tree's n children, tree by tree, nothing waiting before them. Returns the sponge, the rate left waiting (its last one to four scalars) and the cursor. -/
def gkrChildren (sp : List V) (cursor : Shifted) (evals : List V) (n : Nat) : B (List V × List V × Shifted) := B.inline "gkr_children" do
  let mut rate ← B.stackBuf 8
  let mut sp := sp
  let mut cursor := cursor
  for i in [0:N_GKR_TREES * n] do
    if i % 4 = 0 then
      if i ≠ 0 then
        sp ← fsPerm sp rate 4
        rate ← B.stackBuf 8
    let (t0, t1) ← fsNext rate (i % 4) cursor
    let ev := t0
    cursor := t1
    evals[i] := ev
  return (sp, rate, cursor)

/-- The layer's sumcheck claim is the combined product of each tree's n children. -/
def gkrProductCheck (evals : List V) (lam : Word) (claim : Word) (n : Nat) : B Unit := B.inline "gkr_product_check" do
  let mut combined : FW := FW.c (lit 0)
  for i in [0:N_GKR_TREES] do
    let tree := N_GKR_TREES - 1 - i  -- Horner in lam, so the top tree lands last
    let mut product := evals[n * tree]
    for j in [1:n] do
      product ← val (product * evals[n * tree + j])
    combined ← fold (product + lam * combined)
  assert claim == combined

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- ONE GKR grand product over the N_GKR_TREES trees (push, pull, then count), batched by powers of a combiner. Push and pull have equal depth (matched blocks) and the count tree is padded with identity leaves up to it (product unchanged), so a single sumcheck serves them all. Radix four contracts two binary levels per layer, each batched by a fresh combiner drawn after a grind. All the trees reduce to the one shared point `zeta`, which this fills, returning their leaf values with the walked Fiat-Shamir state and stream cursor. The root-most layer, which has no rounds and finds the roots waiting in the sponge, runs on its own: a binary layer for an odd depth, else a radix-four one. It is never the last, the depth being at least BUS_MIN_MU (`verify_sub`). -/
def verifyBusGkr : GFn where
  name := "verify_bus_gkr"
  arity := 9
  rets := 7
  body ps := do
    let fs0 := ps[0]
    let fs1 := ps[1]
    let fs2 := ps[2]
    let fs3 := ps[3]
    let fs4 := ps[4]
    let cursor : Shifted := Shifted.of ps[5]
    let gBusMu := ps[6]
    let zeta := ps[7]
    let tabs := ps[8]
    assert log gBusMu < COUNT_BITS
    let sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let rate ← B.stackBuf 8
    -- Push and pull's one root, then the count's.
    let vals ← B.stackBuf N_GKR_TREES
    let (root, cursor) ← fsNext rate 0 cursor
    vals[PUSH_SIDE] := root
    vals[PULL_SIDE] := root
    let (rootCount, cursor) ← fsNext rate 1 cursor
    vals[COUNT_SIDE] := rootCount
    assert rootCount != 0  -- count-tree root nonzero: no read count self-cancels
    let (sp, lam, cursor) ← fsGrindSqueeze sp rate 2 cursor (Shifted.of tabs) GKR_COMBINER_GRIND_BITS
    let claim ← gkrCombine vals lam
    -- k % 4 and its carry into k // 4 as layer k becomes k + 1, by g^(k % 4).
    let kModNext ← B.heapBuf 8
    for r in [0:4] do
      kModNext[GEN ^ r] := GEN ^ ((r + 1) % 4)
      kModNext[GEN ^ (4 + r)] := GEN ^ ((r + 1) / 4)
    -- Past the root-most layer, (depth - 1) // 2 radix-four layers; and g exactly when the depth is odd.
    let loopBounds ← B.heapBuf COUNT_BITS
    let depthOdd ← B.heapBuf COUNT_BITS
    loopBounds[GEN ^ 0] := GEN ^ 0
    depthOdd[GEN ^ 0] := GEN ^ 0
    for depth in [1:COUNT_BITS] do
      loopBounds[GEN ^ depth] := GEN ^ ((depth - 1) / 2)
      depthOdd[GEN ^ depth] := GEN ^ (depth % 2)
    -- The round records' extent: radix-four layer k past the root runs 2k + odd rounds, its records filling 2k + odd + 1 positions from 0, so n_quads = (depth - 1) // 2 layers fill n_quads^2 + n_quads + n_quads (1 - odd), ROUND_SLOTS cells each.
    let roundsLen ← B.heapBuf COUNT_BITS
    roundsLen[GEN ^ 0] := GEN ^ ROUND_SLOTS
    for depth in [1:COUNT_BITS] do
      let nQ := (depth - 1) / 2
      roundsLen[GEN ^ depth] := GEN ^ (ROUND_SLOTS * (nQ * nQ + nQ + nQ * (1 - depth % 2)))
    let nQuads ← val loopBounds[gBusMu]
    -- A layer record per radix-four layer, the root's at 0; a point row per layer past the root's, MU_CAP apart, the last holding all mu coordinates.
    let layers ← B.heapBufDyn (← val ((nQuads * GEN) ^ LAYER_SLOTS))
    let rounds ← B.heapBufDyn (← val roundsLen[gBusMu])
    let gkrPts ← B.heapBufDyn (← val ((nQuads * GEN ^ 2) ^ MU_CAP))
    let oddG ← val depthOdd[gBusMu]
    let mut lastLayer : Word := default
    if 0 ≠ 0 then
      -- g^1 at the last layer, whose start leaves two binary levels, else g^0.
      lastLayer ← B.heapBuf COUNT_BITS
      for depth in [0:COUNT_BITS] do
        if depth = 2 then
          lastLayer[GEN ^ depth] := GEN
        else
          lastLayer[GEN ^ depth] := GEN ^ 0
    let nextrow : Shifted := ⟨gkrPts, MU_CAP⟩
    let t7 ← val (oddG + 1)
    let _ ← B.ite t7
      (do
        -- The radix-four root layer: four children a tree, y two coordinates.
        let evals ← B.stackBuf 12
        let (sp, rate, cursor) ← gkrChildren sp cursor evals 4
        gkrProductCheck evals lam claim 4
        let (sp, c0, cursor) ← fsGrindSqueeze sp rate ((4 * N_GKR_TREES + 3) % 4 + 1) cursor (Shifted.of tabs) GKR_Y_GRIND_BITS
        let noRate ← B.stackBuf 8
        let (sp, c1) ← squeeze sp noRate 0
        nextrow[GEN ^ 0] := c0
        nextrow[GEN ^ 1] := c1
        let nxt : Shifted := Shifted.of layers
        fsStore nxt LAYER_FS 1 sp
        nxt[GEN ^ LAYER_CURSOR] := cursor
        let mut lo : Word := default
        let mut hi : Word := default
        for t in [0:N_GKR_TREES] do
          lo ← val (evals[4 * t] + c0 * (evals[4 * t] + evals[4 * t + 1]))
          hi ← val (evals[4 * t + 2] + c0 * (evals[4 * t + 2] + evals[4 * t + 3]))
          nxt[GEN ^ (LAYER_VALS + t)] := lo + c1 * (lo + hi)
        nxt[GEN ^ LAYER_ROW] := nextrow
        nxt[GEN ^ LAYER_POS] := GEN ^ 0
        nxt[GEN ^ LAYER_HALF] := GEN ^ 0
        nxt[GEN ^ LAYER_PARITY] := GEN)
      (do
        -- The binary root layer: two children a tree, y one coordinate.
        let evals ← B.stackBuf 6
        let (sp, rate, cursor) ← gkrChildren sp cursor evals 2
        gkrProductCheck evals lam claim 2
        let (sp, c0, cursor) ← fsGrindSqueeze sp rate ((2 * 3 + 3) % 4 + 1) cursor (Shifted.of tabs) GKR_Y1_GRIND_BITS
        nextrow[GEN ^ 0] := c0
        let nxt : Shifted := Shifted.of layers
        fsStore nxt LAYER_FS 1 sp
        nxt[GEN ^ LAYER_CURSOR] := cursor
        for t in [0:N_GKR_TREES] do
          nxt[GEN ^ (LAYER_VALS + t)] := evals[2 * t] + c0 * (evals[2 * t] + evals[2 * t + 1])
        nxt[GEN ^ LAYER_ROW] := nextrow
        nxt[GEN ^ LAYER_POS] := GEN ^ 0
        nxt[GEN ^ LAYER_HALF] := GEN ^ 0
        nxt[GEN ^ LAYER_PARITY] := GEN ^ 0)
    -- Radix-four layer k (from 1 for an even depth) sits at binary layer 2k + odd and runs that many rounds; its record is the k-th.
    let startG ← val (GEN ^ 2 / oddG)
    B.loopRtF 0 (pure nQuads) 8 (pure ([startG.v, layers.v, tabs.v, rounds.v, claim.v, oddG.v, gBusMu.v, kModNext.v])) fun xPair caps => do
      let startG := caps[0]
      let layers := caps[1]
      let tabs := caps[2]
      let rounds := caps[3]
      let claim := caps[4]
      let oddG := caps[5]
      let gBusMu := caps[6]
      let kModNext := caps[7]
      let sq ← val (xPair * xPair)
      let xLayer ← val (sq * startG)
      let layer ← val (layers * xPair ^ LAYER_SLOTS)
      let layerCap ← fsLoad layer LAYER_FS 1
      let layerRate ← B.stackBuf 8
      let (layerSp, layerLam, layerCur) ← fsGrindSqueeze layerCap layerRate 0 (Shifted.of (← val layer[GEN ^ LAYER_CURSOR])) (Shifted.of tabs) 0
      let layerVals ← B.stackBuf N_GKR_TREES
      for t in [0:N_GKR_TREES] do
        layerVals[t] := layer[GEN ^ (LAYER_VALS + t)]
      let pointRow ← val layer[GEN ^ LAYER_ROW]
      let roundPos ← val layer[GEN ^ LAYER_POS]  -- g^(ROUND_SLOTS pos)
      let nextrow : Shifted := ⟨pointRow, MU_CAP⟩
      -- Round i's record is the ROUND_SLOTS cells from rounds * g^(ROUND_SLOTS i).
      let head ← val (rounds * roundPos)
      fsStore (Shifted.of head) ROUND_FS 1 layerSp
      head[GEN ^ ROUND_CURSOR] := layerCur
      let t3 ← gkrCombine layerVals layerLam
      head[GEN ^ ROUND_CLAIM] := t3
      -- 2k rounds, or 2k + 1 when the depth is odd: eight a loop step, the state between them staying in the frame, then 2 (k % 4), then the odd one.
      let half ← val layer[GEN ^ LAYER_HALF]
      let parity ← val layer[GEN ^ LAYER_PARITY]
      B.loopRtF 0 (pure half) 3 (pure ([head.v, pointRow.v, tabs.v])) fun x8 caps => do
        let head := caps[0]
        let pointRow := caps[1]
        let tabs := caps[2]
        let step ← val (x8 ^ 8)
        let rd ← val (head * step ^ ROUND_SLOTS)
        let pt ← val (pointRow * step)
        let mut roundSp ← fsLoad rd ROUND_FS 1
        let mut cur : Shifted ← Shifted.of <$> val rd[GEN ^ ROUND_CURSOR]
        let mut claim ← val rd[GEN ^ ROUND_CLAIM]
        for q in [0:8] do
          -- As in gkr_rounds.
          let rate ← B.stackBuf 8
          let (t0, t1) ← fsNext rate 0 cur
          let c1 := t0
          cur := t1
          let (t2, t3) ← fsNext rate 1 cur
          let c2 := t2
          cur := t3
          let (t4, t5) ← fsNext rate 2 cur
          let c3 := t4
          cur := t5
          let (t6, t7) ← fsNext rate 3 cur
          let c4 := t6
          cur := t7
          let (t8, t9, t10) ← fsGrindSqueeze roundSp rate 4 cur (Shifted.of tabs) ROUND5_GRIND_BITS
          roundSp := t8
          let rk := t9
          cur := t10
          let c0 ← val (claim + pt[GEN ^ q] * (c1 + c2 + c3 + c4))
          pt[GEN ^ (MU_CAP + 2 + q)] := rk  -- nextrow[round * g^2]
          claim ← val (c0 + rk * (c1 + rk * (c2 + rk * (c3 + rk * c4))))
        let rdNext : Shifted := ⟨rd, 56⟩
        fsStore rdNext ROUND_FS 1 roundSp
        rdNext[GEN ^ ROUND_CURSOR] := cur
        rdNext[GEN ^ ROUND_CLAIM] := claim
      let octet ← val (half ^ 8)
      let remHead ← val (head * octet ^ ROUND_SLOTS)
      let remRow ← val (pointRow * octet)
      let t4 ← B.targets [none]
      B.dispatchInto parity ((List.range 4).map (fun arm => instName "gkr_rounds" [.L (2 * arm)])) [remHead.v, remRow.v, tabs.v] t4
      let done := t4[0]
      let t5 ← val (oddG + 1)
      let _ ← B.ite t5
        (do
          pure ())
        (do
          let done ← call1 (instName "gkr_rounds" [.L 1]) [head * sq ^ ROUND_SLOTS, pointRow * sq, tabs]
          pure ())
      let layerSpan ← val (xLayer ^ ROUND_SLOTS)
      let tail ← val (head * layerSpan)
      let tailSp ← fsLoad tail ROUND_FS 1
      let tcur : Shifted ← Shifted.of <$> val tail[GEN ^ ROUND_CURSOR]
      let evals ← B.stackBuf 12  -- the four children of each tree, in tree order
      let (t6, t7, t8) ← gkrChildren tailSp tcur evals 4
      let mut tailSp := t6
      let rate := t7
      let mut tcur : Shifted := t8
      gkrProductCheck evals layerLam (← val tail[GEN ^ ROUND_CLAIM]) 4
      -- y's grind: the last layer's coordinates are also zeta's, which the table sumcheck's zerocheck reads, so its numerator doubles.
      let mut c0 : Word := default
      if GKR_Y_GRIND_BITS = GKR_Y_LAST_GRIND_BITS then
        let (t9, t10, t11) ← fsGrindSqueeze tailSp rate ((4 * N_GKR_TREES + 3) % 4 + 1) tcur (Shifted.of tabs) GKR_Y_GRIND_BITS
        tailSp := t9
        c0 := t10
        tcur := t11
      else
        -- Unreachable: `GKR_Y_GRIND_BITS = GKR_Y_LAST_GRIND_BITS` in every configuration, so no instance takes this branch. The zkDSL guest dispatched here on the last layer to `gkr_y_grind`, which was never written in Lean.
        pure ()
      let noRate ← B.stackBuf 8
      let (t9, t10) ← squeeze tailSp noRate 0
      tailSp := t9
      let c1 := t10
      nextrow[GEN ^ 0] := c0
      nextrow[GEN ^ 1] := c1
      let nxt : Shifted := ⟨layer, LAYER_SLOTS⟩
      fsStore nxt LAYER_FS 1 tailSp
      nxt[GEN ^ LAYER_CURSOR] := tcur
      for t in [0:N_GKR_TREES] do
        let lo ← val (evals[4 * t] + c0 * (evals[4 * t] + evals[4 * t + 1]))
        let hi ← val (evals[4 * t + 2] + c0 * (evals[4 * t + 2] + evals[4 * t + 3]))
        nxt[GEN ^ (LAYER_VALS + t)] := lo + c1 * (lo + hi)
      nxt[GEN ^ LAYER_ROW] := nextrow
      nxt[GEN ^ LAYER_POS] := roundPos * layerSpan * GEN ^ ROUND_SLOTS
      nxt[GEN ^ LAYER_HALF] := half * kModNext[GEN ^ 4 * parity]
      nxt[GEN ^ LAYER_PARITY] := kModNext[parity]
    let last ← val (layers * nQuads ^ LAYER_SLOTS)
    let cursor : Shifted ← Shifted.of <$> val last[GEN ^ LAYER_CURSOR]
    let finalPointRow ← val last[GEN ^ LAYER_ROW]
    B.loopRtF 0 (pure gBusMu) 2 (pure ([zeta.v, finalPointRow.v])) fun xt caps => do
      let zeta := caps[0]
      let finalPointRow := caps[1]
      let t0 ← val finalPointRow[xt]  -- the ONE shared point
      zeta[xt] := t0
    let leaves ← B.heapBuf N_GKR_TREES
    for t in [0:N_GKR_TREES] do
      leaves[GEN ^ t] := last[GEN ^ (LAYER_VALS + t)]
    let t22 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val cursor)
    return [.load last.v LAYER_FS, .load last.v 1, .load last.v 2, .load last.v 3, .load last.v 4, .into t22, .v leaves.v]

/-- The Index coordinate's MLE over the block's n = κ low coords: prod_t (1 + zeta_t * (1 + g^(2^t))).
-/
def indexMle (n : Nat) : GFn where
  name := instName "index_mle" [.L n]
  arity := 1
  rets := 1
  body ps := do
    let zeta := ps[0]
    let mut v : FW := FW.c (gpowE 0)
    for t in [0:n] do
      if t = 0 then
        v ← fold (1 + zeta[GEN ^ t] * arrWord INDEX_MLE_FACTORS t)
      else
        v ← fold (v * (1 + zeta[GEN ^ t] * arrWord INDEX_MLE_FACTORS t))
    return [Ex.ret v]

/-- The eq tables over coordinates z[0..t] for t < width, level t at 2^(t+1) - 2, coordinate t being index bit t; z1 = 1 + z. -/
def selEqNibble (out : Word) (z : Word) (z1 : Word) (width : Nat) : B Unit := B.inline "sel_eq_nibble" do
  let levels ← B.stackBuf SEL_EQ_STRIDE
  levels[0] := z1[GEN ^ 0]
  levels[1] := z[GEN ^ 0]
  for t in [1:width] do
    let r ← val z[GEN ^ t]
    let r1 ← val z1[GEN ^ t]
    for i in [0:2 ^ t] do
      levels[2 ^ (t + 1) - 2 + i] := levels[2 ^ t - 2 + i] * r1
      levels[2 ^ (t + 1) - 2 + 2 ^ t + i] := levels[2 ^ t - 2 + i] * r
  for i in [0:2 ^ (width + 1) - 2] do
    out[GEN ^ i] := levels[i]

/-- out[u] = prod_t gs[t]^(bit t of u) for u < 2^width. -/
def selGNibble (out : Word) (gs : Word) (width : Nat) : B Unit := B.inline "sel_g_nibble" do
  let vals ← B.stackBuf 16
  vals[0] := 1
  vals[1] := gs[GEN ^ 0]
  for t in [1:width] do
    let gT ← val gs[GEN ^ t]
    for i in [0:2 ^ t] do
      vals[2 ^ t + i] := vals[i] * gT
  for i in [0:2 ^ width] do
    out[GEN ^ i] := vals[i]

def selPartialNibble (width : Nat) : GFn where
  name := instName "sel_partial_nibble" [.L width]
  arity := 5
  rets := 1
  body ps := do
    let eqOut := ps[0]
    let gOut := ps[1]
    let z := ps[2]
    let z1 := ps[3]
    let gs := ps[4]
    if width ≠ 0 then
      selEqNibble eqOut z z1 width
      selGNibble gOut gs width
    return [.c 0]

/-- A selector run of length n = 4q + r, r < 4, split into its q full nibbles (coordinates 4j..4j+3 past κ) and a last one r wide. The split is advice, each bit pinned and the whole tied back to len_g. Returns g^q. -/
def selectorRunNibbles : GFn where
  name := "selector_run_nibbles"
  arity := 1
  rets := 1
  body ps := do
    let lenG := ps[0]
    let nb ← B.stackBuf 6
    B.hintBitsExpTo (.stack nb[0:6]) lenG 6
    for k in [0:6] do
      let b := nb[k]
      nb[k] := b * b
    let rG ← val ((1 + nb[0] * (1 + GEN)) * (1 + nb[1] * (1 + GEN ^ 2)))
    let mut qG : FW := FW.c (gpowE 0)
    for k in [2:6] do
      qG ← fold (qG * (1 + nb[k] * (1 + GEN ^ (2 ^ (k - 2)))))
    let q4 ← val (qG ^ 4)
    assert q4 * rG == lenG
    return [Ex.ret qG]

/-- Per nibble j of a selector run of length n = 4q + r split by selector_run_nibbles (q_g = g^q), the eq tables over its low 1..4 coordinates and the g-powers of its indices' offset shares, into the caller's tables of q + 1 nibbles, SEL_TAB_EQ_STRIDE and 16 cells a nibble. -/
def sharedSelectorTables : GFn where
  name := "shared_selector_tables"
  arity := 7
  rets := 0
  body ps := do
    let eqTab := ps[0]
    let gTab := ps[1]
    let zetaHi := ps[2]
    let zeta1Hi := ps[3]
    let gsqHi := ps[4]
    let lenG := ps[5]
    let qG := ps[6]
    let q4 ← val (qG ^ 4)
    let rG ← val (lenG / q4)
    B.loopRtF 0 (pure qG) 5 (pure ([eqTab.v, zetaHi.v, zeta1Hi.v, gTab.v, gsqHi.v])) fun xq caps => do
      let eqTab := caps[0]
      let zetaHi := caps[1]
      let zeta1Hi := caps[2]
      let gTab := caps[3]
      let gsqHi := caps[4]
      let x4 ← val (xq ^ 4)
      let x16 ← val (x4 ^ 4)
      selEqNibble (← val (eqTab * x16 * x16)) (← val (zetaHi * x4)) (← val (zeta1Hi * x4)) 4
      selGNibble (← val (gTab * x16)) (← val (gsqHi * x4)) 4
    let q16 ← val (q4 ^ 4)
    -- r_g = g^r with r < 4 as a range check: the back end's selector analysis bounds the match's selector by it (it cannot bound a quotient).
    assert log rG < 4
    let t0 ← B.targets [none]  -- a match needs a target
    let t1 ← val (eqTab * q16 * q16)
    let t2 ← val (gTab * q16)
    let t3 ← val (zetaHi * q4)
    let t4 ← val (zeta1Hi * q4)
    let t5 ← val (gsqHi * q4)
    B.dispatchInto rG ((List.range 4).map (fun arm => instName "sel_partial_nibble" [.L arm])) [t1.v, t2.v, t3.v, t4.v, t5.v] t0
    let done := t0[0]
    return []

/-- d = g^u with u < 2^width: three cycles, no XOR. -/
def assertDigit (d : Word) (width : Nat) : B Unit := B.inline "assert_digit" do
  if width = 1 then
    assert log d < 2
    pure ()
  if width = 2 then
    assert log d < 4
    pure ()
  if width = 3 then
    assert log d < 8
    pure ()
  if width = 4 then
    assert log d < 16
    pure ()

/-- block_selector off the shared tables: per nibble, a hinted g-power digit g^u, range-checked below the nibble's table size, reads its eq factor and its share of g^offset. The caller pins the shares' product to the certified offset, which makes every digit the offset's own (a base-16 representation is unique). -/
def blockSelectorTab (n : Nat) : GFn where
  name := instName "block_selector_tab" [.L n]
  arity := 3
  rets := 2
  body ps := do
    let digits := ps[0]
    let eqTab := ps[1]
    let gTab := ps[2]
    let mut eq : FW := FW.c (gpowE 0)
    let mut rebuilt : FW := FW.c (gpowE 0)
    for j in [0:(n + 3) / 4] do
      let mut width := 4
      if j = n / 4 then
        width := n - 4 * j
      let d ← val digits[GEN ^ j]
      assertDigit d width
      if j = 0 then
        eq ← fold eqTab[GEN ^ (SEL_TAB_EQ_STRIDE * j + 2 ^ width - 2) * d]
        rebuilt ← fold gTab[GEN ^ (16 * j) * d]
      else
        eq ← fold (eq * eqTab[GEN ^ (SEL_TAB_EQ_STRIDE * j + 2 ^ width - 2) * d])
        rebuilt ← fold (rebuilt * gTab[GEN ^ (16 * j) * d])
    return [Ex.ret eq, Ex.ret rebuilt]

/-- A bus block's eq over its n = mu - κ selector bits, the offset's bits above κ, each boolean-pinned, and g^offset rebuilt from those bits alone (weights g^(2^(κ+k)) = idxc_hi[k] + 1), which the caller pins to the certified offset. -/
def blockSelector (n : Nat) : GFn where
  name := instName "block_selector" [.L n]
  arity := 3
  rets := 2
  body ps := do
    let selBits := ps[0]
    let zeta1Hi := ps[1]
    let idxcHi := ps[2]
    let mut eq : FW := FW.c (gpowE 0)
    let mut rebuilt : FW := FW.c (gpowE 0)
    for k in [0:n] do
      let sbit ← val selBits[GEN ^ k]
      selBits[GEN ^ k] := sbit * sbit  -- booleanity as a write-once pin
      if k = 0 then
        eq ← fold (sbit + zeta1Hi[GEN ^ k])  -- eq over GF(2) is 1 + b + z
        rebuilt ← fold (1 + sbit * idxcHi[GEN ^ k])
      else
        eq ← fold (eq * (sbit + zeta1Hi[GEN ^ k]))
        rebuilt ← fold (rebuilt * (1 + sbit * idxcHi[GEN ^ k]))
    return [Ex.ret eq, Ex.ret rebuilt]

/-- pad_n(zeta[..tau]) for n = rows <= 2^tau (doc lem:suffix). The advice is the bits of n + (2^tau - 1): the complements of n's low bits, as the step reads them, then n's bit tau, set only alone. -/
def paddingWeight (tau : Nat) : GFn where
  name := instName "padding_weight" [.L tau]
  arity := 2
  rets := 3
  body ps := do
    let rows := ps[0]
    let zeta := ps[1]
    let word ← val (rows + lit (2 ^ tau - 1))
    let bits ← B.stackBuf N_COLUMN_LOGS
    B.hintBits (.stack bits[0:tau + 1]) word 0 (tau + 1)
    let mut pad : FW := FW.c (lit 1)
    for k in [0:tau] do
      let c := bits[k]
      bits[k] := c * c
      let z ← val zeta[GEN ^ k]
      pad ← fold (c * z + (c + z) * pad)
    let top := bits[tau]
    bits[tau] := top * top
    -- tau is the least height holding n iff lead == 1 and rest != 0: n's highest bit is tau - 1 with more below it, or n = 2^tau.
    let mut low : FW := default
    let mut lead : FW := default
    let mut rest : FW := default
    if tau = 0 then
      low := FW.c (lit 0)
      lead := FW.c (lit 1)
      rest := FW.c (lit 1)
    else
      -- The bits below bit tau - 1, by Horner from their high end: one constant, 2.
      let mut below : FW := FW.c (lit 0)
      for k in [1:tau] do
        below ← fold (below * 2 + bits[tau - 1 - k])
      low ← fold (below + bits[tau - 1] * 2 ^ (tau - 1))
      lead ← fold (top + 1 + bits[tau - 1])
      rest ← fold (top + below + lit (2 ^ (tau - 1) - 1))
    assert low + top * 2 ^ tau == word
    assert top * (low + lit (2 ^ tau - 1)) == 0
    return [Ex.ret ((1 + top) * pad), Ex.ret lead, Ex.ret rest]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Settle the bus against the six tables, in four steps: certify each side's leaf-cube tiling, decompose the sides' GKR leaf values over it, run the ONE table sumcheck they all reduce to, and bind the public input. Pooled claims land in claim_pool, the reduced point in `chi` and the bytecode sumcheck's in `bc_point`; the batch's round count g^n, the bytecode value there (the deferred claim) and the PI point come back.

Bus-leaf packing offsets, for the selector certification. Each side's blocks tile its leaf cube, block b at offset_b, and offsets accumulate as g^offset = Π_{earlier} g^(2^κ). The hinted order is certified to be the native one, as certify_placement does for the columns: descending κ, then ascending block index, the guest's per-side block order being the native verifier's (framework blocks, then each table's in table order). The decompose below pins each block's selector bits against this offset, forcing κ-alignment. Pull's blocks mirror push's and share zeta, so only push and count need offsets (pull's slots go unread).
-/
def verifyTables : GFn where
  name := "verify_tables"
  arity := 20
  rets := 10
  body ps := do
    let fs0 := ps[0]
    let fs1 := ps[1]
    let fs2 := ps[2]
    let fs3 := ps[3]
    let fs4 := ps[4]
    let mut cursor : Shifted := Shifted.of ps[5]
    let pi0 := ps[6]
    let pi1 := ps[7]
    let zeta := ps[8]
    let gBusMu := ps[9]
    let dimsG := ps[10]
    let tableRows := ps[11]
    let gSquares := ps[12]
    let fpW := ps[13]
    let beta := ps[14]
    let claimPool := ps[15]
    let chi := ps[16]
    let gkrLeaves := ps[17]
    let tabs := ps[18]
    let bcPoint := ps[19]
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut rate ← B.stackBuf 8
    let kb ← B.stackBuf 8  -- kappa_base, in the frame
    kb[0] := 1
    for t_k in [0:N_TABLES + 1] do
      kb[1 + t_k] := dimsG[GEN ^ t_k]
    -- A block group, a run of a side's blocks sharing one kappa source, is consecutive in its side's order, so a hinted order of the groups, certified strictly descending in its rank key (descending κ, then ascending first index: a side's blocks share one base, so the native ascending index), places every block.
    let groupSideTab : Shifted := ⟨gSquares, SIDE_TAB_AT⟩  -- group -> its side (exponent_tables)
    let rankKeys : Shifted := ⟨gSquares, RANK_KEYS_AT⟩
    let groupKey ← B.heapBuf N_BLOCK_GROUPS
    let groupSize ← B.heapBuf N_BLOCK_GROUPS
    let groupBase ← B.heapBuf N_BLOCK_GROUPS
    let groupOrder ← B.heapBuf N_BLOCK_GROUPS
    B.witness "block_group_order" (.heap groupOrder.v 0 N_BLOCK_GROUPS)
    let blockOff ← B.stackBuf N_BLOCKS  -- g^offset per push and count block
    let mut s : Nat := default
    let mut b0 : Nat := default
    let mut kappaG : Word := default
    let mut gi : Word := default
    let mut key : Word := default
    let mut prevKey : Word := default
    let mut step : Word := default
    for cert in [0:2] do
      s := COUNT_SIDE * cert  -- PUSH_SIDE (0), then COUNT_SIDE (2)
      for gi_k in [arrInt SIDE_GROUP_START s:arrInt SIDE_GROUP_START (s + 1)] do
        b0 := arrInt BLOCK_GROUP_START gi_k
        kappaG ← val (Ex.v kb[arrInt BLOCK_KAPPA_SRC b0] * GEN ^ (arrInt BLOCK_KAPPA_ADJ b0))
        groupKey[GEN ^ gi_k] := rankKeys[kappaG] * INV_GEN ^ b0
        groupSize[GEN ^ gi_k] := gSquares[kappaG] ^ (arrInt BLOCK_GROUP_START (gi_k + 1) - b0)
      let mut gOff : FW := FW.c (gpowE 0)
      for r in [arrInt SIDE_GROUP_START s:arrInt SIDE_GROUP_START (s + 1)] do
        gi ← val groupOrder[GEN ^ r]
        assert log gi < N_BLOCK_GROUPS  -- a valid group...
        let t0 ← val (lit s)  -- ...of THIS side
        groupSideTab[gi] := t0
        key ← val groupKey[gi]
        if r ≠ arrInt SIDE_GROUP_START s then
          assert log (prevKey / key * INV_GEN) < RANK_KEY_BOUND
          pure ()
        -- write-once: a repeat collides (g_off has grown since), so the side's ranks name as many distinct groups of the side as it has, omitting none
        let t1 ← val gOff
        groupBase[gi] := t1
        gOff ← fold (gOff * groupSize[gi])
        prevKey := key
      for gi_k in [arrInt SIDE_GROUP_START s:arrInt SIDE_GROUP_START (s + 1)] do
        b0 := arrInt BLOCK_GROUP_START gi_k
        step ← val gSquares[GEN ^ (arrInt BLOCK_KAPPA_ADJ b0) * kb[arrInt BLOCK_KAPPA_SRC b0]]
        blockOff[b0] := groupBase[GEN ^ gi_k]
        for b_k in [b0 + 1:arrInt BLOCK_GROUP_START (gi_k + 1)] do
          blockOff[b_k] := blockOff[b_k - 1] * step
    -- ---- the leaf decomposition (claims pooled; bytecode Public DEFERRED) ---- Reconstruct Ṽ₀(ζ) per side and assert it equals the GKR leaf value. The committed-coordinate values ride the stream (observed, pooled); Index coordinates use the factored index MLE; and the program's whole share of a bytecode leaf, its slots being aligned with the tuple, is ONE sum over the slots of the stacked polynomial at ζ_lo, which rides the stream after the framework values and a sumcheck reduces to one evaluation, the deferred claim (doc sec:e2e-bc).
    --
    -- Pull's blocks mirror push's (same kappas, same offsets, generator-asserted pairing) and share zeta, so each pull block REUSES its push twin's eq_hi and Index-MLE value instead of recomputing them; its column values are mostly deduped pool reads (COORD_FRESH). The identity check against pull's own GKR claim still binds everything. Each table's padding rows: their weight on a claim at zeta[..tau], dispatched on its hinted log height tau, which this certifies: the least holding its rows, or its floor. A table is at most the stack, so tau has an arm.
    let padWeight ← B.stackBuf N_TABLES
    let mut tauG : Word := default
    for t_k in [0:N_TABLES] do
      tauG := kb[2 + t_k]
      assert log tauG < N_COLUMN_LOGS
      let rows ← val tableRows[GEN ^ t_k]
      let t2 ← B.targets [some padWeight[t_k].v, none, none]
      B.dispatchInto tauG ((List.range N_COLUMN_LOGS).map (fun arm => instName "padding_weight" [.L arm])) [rows.v, zeta.v] t2
      let lead := t2[1]
      let rest := t2[2]
      if arrInt FLOORS t_k = 0 then
        assert lead == 1
        assert rest != 0
      else
        assert log (tauG / GEN ^ (arrInt FLOORS t_k)) < N_COLUMN_LOGS
        let t4 ← val (tauG + GEN ^ (arrInt FLOORS t_k))
        let _ ← B.ite t4
          (do
            pure ())
          (do
            assert lead == 1
            assert rest != 0)
        pure ()
    let idxcTab ← B.heapBuf SIZE_BITS  -- INDEX_MLE_FACTORS[t] = 1 + g^(2^t)
    for t_k in [0:SIZE_BITS] do
      idxcTab[GEN ^ t_k] := arrWord INDEX_MLE_FACTORS t_k
    let zeta1 ← B.heapBufDyn gBusMu  -- 1 + zeta, so an eq factor 1 + b + z is one XOR
    let t3 ← B.targets [none]  -- a match needs a target
    B.dispatchInto gBusMu ((List.range SIZE_BITS).map (fun arm => instName "plus_one_run" [.L arm])) [zeta1.v, zeta.v] t3
    let zeta1Done := t3[0]
    -- A block sized by table t's tau (kappa source 2 + t, unadjusted) has block_kappa = kappa_base[2 + t] = dims_g[t + 1] (verify_sub), so all of one table's blocks walk the same selector run and read the same tables.
    let sharedLen ← B.stackBuf N_TABLES
    let sharedEq ← B.stackBuf N_TABLES
    let sharedG ← B.stackBuf N_TABLES
    for t_k in [0:N_TABLES] do
      tauG := kb[2 + t_k]
      B.copy sharedLen[t_k] (← val (gBusMu / tauG))
      assert log sharedLen[t_k] < SIZE_BITS
      -- Each table sized to its run, q + 1 nibbles of SEL_TAB_EQ_STRIDE and 16 cells.
      let qG ← call1 "selector_run_nibbles" [sharedLen[t_k]]
      let gLen ← val ((qG * GEN) ^ 16)
      let eqT ← B.heapBufDyn (← val (gLen * gLen))
      let gT ← B.heapBufDyn gLen
      call "shared_selector_tables" [eqT, gT, zeta * tauG, zeta1 * tauG, gSquares * tauG, sharedLen[t_k], qG]
      sharedEq[t_k] := eqT
      sharedG[t_k] := gT
    let blockEqHi ← B.stackBuf N_BLOCKS  -- every block's eq_hi, reused below
    let blockIndexMle ← B.heapBuf N_BLOCKS  -- per push block with an Index coord
    -- A framework coordinate's value at zeta, and a table coordinate's at the table sumcheck's point (a pull one's less its push twin's), by coordinate index.
    let coordVals ← B.stackBuf N_COORDS
    let selectorSums ← B.stackBuf N_GKR_SIDES  -- per side, its blocks' eq_hi summed
    let publicEqs ← B.stackBuf N_GKR_SIDES  -- per side, the eq_hi of its blocks with public slots
    let mut blockHasPublic : Nat := default
    let mut shared : Nat := default
    let mut selLenG : Word := default
    let mut offsetBits : Word := default
    let mut selBits : Word := default
    let mut zeta1Hi : Word := default
    let mut idxcHi : Word := default
    let mut eqHi : Word := default
    let mut goff : Word := default
    let mut ci : Nat := default
    let mut coordVal : Word := default
    let mut rawv : Word := default
    let mut t : Nat := default
    let mut digits : Word := default
    let mut lenG : Word := default
    let mut tabEq : Word := default
    let mut tabG : Word := default
    for s_k in [0:N_GKR_SIDES] do
      let mut selectorSum : FW := FW.c (lit 0)
      let mut publicEq : FW := FW.c (lit 0)
      for b_k in [arrInt SIDE_BLOCK_START s_k:arrInt SIDE_BLOCK_START (s_k + 1)] do
        blockHasPublic := 0
        kappaG ← val (Ex.v kb[arrInt BLOCK_KAPPA_SRC b_k] * GEN ^ (arrInt BLOCK_KAPPA_ADJ b_k))
        -- Every certified log is under SIZE_BITS (log_mem below COUNT_BITS, a tau below N_COLUMN_LOGS), so only an adjusted one needs bounding.
        if arrInt BLOCK_KAPPA_SRC b_k ≠ 0 then
          if arrInt BLOCK_KAPPA_ADJ b_k ≠ 0 then
            assert log kappaG < SIZE_BITS
            pure ()
        if s_k = PULL_SIDE then
          eqHi := blockEqHi[b_k - arrInt SIDE_BLOCK_START PULL_SIDE]
        else
          -- eq_hi over the ζ coords above κ against the selector bits, whose run is mu_s − κ = g^mu_s / g^κ long. Selector bits = offset >> κ:
          -- advice-decompose the offset and read it shifted by κ. Rebuilding g^offset from those high bits alone (weights g^(2^(κ+k))) and asserting it equals block_off_g pins the bits AND the κ-alignment in one shot; the low κ bit cells are written but never read.
          shared := 0
          if arrInt BLOCK_KAPPA_SRC b_k / 2 ≠ 0 then
            if arrInt BLOCK_KAPPA_ADJ b_k = 0 then
              shared := 1
          if shared = 1 then
            t := arrInt BLOCK_KAPPA_SRC b_k - 2
            digits ← B.heapBuf SEL_TAB_NIBBLES
            B.hintDigitsExp (.heap digits.v 0 SEL_TAB_NIBBLES) blockOff[b_k] SIZE_BITS SEL_TAB_NIBBLES 4 0 (startCell := some kb[2 + t])
            lenG := sharedLen[t]
            tabEq := sharedEq[t]
            tabG := sharedG[t]
            let t4 ← B.targets [none, none]
            B.dispatchInto lenG ((List.range SIZE_BITS).map (fun arm => instName "block_selector_tab" [.L arm])) [digits.v, tabEq.v, tabG.v] t4
            eqHi := t4[0]
            goff := t4[1]
          else
            selLenG ← val (gBusMu / kappaG)  -- g^(mu - κ)
            assert log selLenG < SIZE_BITS
            offsetBits ← B.heapBufDyn (← val (GEN ^ SIZE_BITS))
            B.hintBitsExpTo (.heap offsetBits.v 0 SIZE_BITS) blockOff[b_k] SIZE_BITS
            selBits ← val (offsetBits * kappaG)
            zeta1Hi ← val (zeta1 * kappaG)
            idxcHi ← val (idxcTab * kappaG)
            let t4 ← B.targets [none, none]
            B.dispatchInto selLenG ((List.range SIZE_BITS).map (fun arm => instName "block_selector" [.L arm])) [selBits.v, zeta1Hi.v, idxcHi.v] t4
            eqHi := t4[0]
            goff := t4[1]
          assert goff == blockOff[b_k]  -- bits == offset >> κ, κ-aligned
        selectorSum ← fold (selectorSum + eqHi)
        blockEqHi[b_k] := eqHi
        -- A TABLE's block streams no value here: the table sumcheck settles its fingerprint from that table's column evaluations. Only the framework blocks (boundary, memory, bytecode) still decompose.
        if arrInt BLOCK_TABLE b_k = NO_TABLE then
          for i in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := arrInt BLOCK_COORD_OFF b_k + i  -- a compile-time index, so `ci` costs nothing
            if arrInt COORD_TYPE ci = COORD_KIND_CONST then
              coordVals[ci] := arrWord COORD_CONST ci
            if arrInt COORD_TYPE ci = COORD_KIND_COL then
              if arrInt COORD_FRESH ci = 1 then
                if arrInt COORD_FRESH_POS ci % 4 = 0 then
                  if arrInt COORD_FRESH_POS ci ≠ 0 then
                    sp ← fsPerm sp rate 4
                    rate ← B.stackBuf 8
                let (t4, t5) ← fsNext rate (arrInt COORD_FRESH_POS ci % 4) cursor
                coordVal := t4
                cursor := t5
                claimPool[GEN ^ (arrInt COORD_CLAIM_SLOT ci)] := coordVal
              else
                coordVal ← val claimPool[GEN ^ (arrInt COORD_CLAIM_SLOT ci)]
              coordVals[ci] := coordVal
            if arrInt COORD_TYPE ci = COORD_KIND_GCOL then
              if arrInt COORD_FRESH ci = 1 then
                if arrInt COORD_FRESH_POS ci % 4 = 0 then
                  if arrInt COORD_FRESH_POS ci ≠ 0 then
                    sp ← fsPerm sp rate 4
                    rate ← B.stackBuf 8
                let (t4, t5) ← fsNext rate (arrInt COORD_FRESH_POS ci % 4) cursor
                rawv := t4
                cursor := t5
                claimPool[GEN ^ (arrInt COORD_CLAIM_SLOT ci)] := rawv
              else
                rawv ← val claimPool[GEN ^ (arrInt COORD_CLAIM_SLOT ci)]
              coordVals[ci] := arrWord COORD_CONST ci * rawv
            if arrInt COORD_TYPE ci = COORD_KIND_INDEX then
              if s_k = PULL_SIDE then
                coordVals[ci] := blockIndexMle[GEN ^ (b_k - arrInt SIDE_BLOCK_START PULL_SIDE)]
              else
                let t4 ← B.targets [none]
                B.dispatchInto kappaG ((List.range SIZE_BITS).map (fun arm => instName "index_mle" [.L arm])) [zeta.v] t4
                coordVal := t4[0]
                coordVals[ci] := coordVal
                if s_k = PUSH_SIDE then
                  blockIndexMle[GEN ^ b_k] := coordVal
            if arrInt COORD_TYPE ci = COORD_KIND_PUBLIC then
              -- The public slots carry no value of their own here: their weighted sum IS bc_share, added once per block below (push and pull share zeta, so both get the same one).
              coordVals[ci] := 0
              blockHasPublic := 1
          if blockHasPublic = 1 then
            publicEq ← fold (publicEq + eqHi)
      selectorSums[s_k] := selectorSum
      publicEqs[s_k] := publicEq
    -- ---- the bytecode's share (verifier::bus) ---- S = sum_x fp_w[x] P(ζ_lo, x) over the stacked bytecode P's slots x, after the framework values, then a sumcheck over x, low bit first, of degree two: each round sends c0 and c2, and the first round's two join S in the rate.
    let bcMsg ← B.stackBuf 3  -- S, then the first round's c0 and c2
    for j in [0:3] do
      if (4 + j) % 4 = 0 then
        sp ← fsPerm sp rate 4
        rate ← B.stackBuf 8
      let (t4, t5) ← fsNext rate ((4 + j) % 4) cursor
      let bcWord := t4
      cursor := t5
      bcMsg[j] := bcWord
    let bcShare := bcMsg[0]
    let (t6, t7, t8) ← fsGrindSqueeze sp rate ((4 + 2) % 4 + 1) cursor (Shifted.of tabs) ROUND2_GRIND_BITS
    sp := t6
    let bcR := t7
    cursor := t8
    bcPoint[GEN ^ 0] := bcR
    let mut bcClaim ← val (bcMsg[1] + bcR * (bcShare + (1 + bcR) * bcMsg[2]))
    let mut bfs0 := sp[8]
    let mut bfs1 := sp[9]
    let mut bfs2 := sp[10]
    let mut bfs3 := sp[11]
    let mut bfs4 := sp[12]
    for x in [1:N_TUPLE_BITS] do
      let t9 ← callN "opening_tail_round" [bfs0, bfs1, bfs2, bfs3, bfs4, cursor, bcClaim, tabs] 8
      bfs0 := t9[0]!
      bfs1 := t9[1]!
      bfs2 := t9[2]!
      bfs3 := t9[3]!
      bfs4 := t9[4]!
      cursor := Shifted.of t9[5]!
      bcClaim := t9[6]!
      let bcR := t9[7]!
      bcPoint[GEN ^ x] := bcR
    -- It ends on fp_w's multilinear at bc_point times P(ζ_lo, bc_point), the value read next, which the deferred claim pins. fp_w folds a round at a time: round j's 2^(3 - j) values from offset N_TUPLE_SLOTS - 2^(4 - j).
    sp ← fsCap bfs0 bfs1 bfs2 bfs3 bfs4
    rate ← B.stackBuf 8
    let (t10, t11) ← fsNext rate 0 cursor
    let bcValue := t10
    cursor := t11
    let wFold ← B.stackBuf 15
    let r0 ← val bcPoint[GEN ^ 0]
    let mut wLo : Word := default
    for i in [0:N_TUPLE_SLOTS / 2] do
      wLo ← val fpW[GEN ^ (2 * i)]
      wFold[i] := wLo + r0 * (wLo + fpW[GEN ^ (2 * i + 1)])
    let mut wHi : Word := default
    for j in [1:N_TUPLE_BITS] do
      let rj ← val bcPoint[GEN ^ j]
      for i in [0:2 ^ (N_TUPLE_BITS - 1 - j)] do
        wLo := wFold[N_TUPLE_SLOTS - 2 ^ (N_TUPLE_BITS + 1 - j) + 2 * i]
        wHi := wFold[N_TUPLE_SLOTS - 2 ^ (N_TUPLE_BITS + 1 - j) + 2 * i + 1]
        wFold[N_TUPLE_SLOTS - 2 ^ (N_TUPLE_BITS - j) + i] := wLo + rj * (wLo + wHi)
    assert bcClaim == wFold[N_TUPLE_SLOTS - 2] * bcValue
    -- ---- the sides' framework decomposition ---- Per side, what its tables' blocks owe: its GKR leaf value less the framework blocks' fingerprints and the padding mass. DERIVED, not read: a transmitted total would be a free value in its own check. The table sumcheck's target pins it below. Pull's padding is push's (same blocks, same padding tuples), and the count side weighs its counts alone, at beta = 0.
    let busTableTotal ← B.stackBuf N_GKR_SIDES
    let beta1 ← val (beta + 1)
    let mut innerSum : FW := default
    let mut paddingSum : FW := default
    let mut tableSum : FW := default
    let mut coeff : FW := default
    let mut pushPadding : Word := default
    for s_k in [0:N_GKR_SIDES] do
      let mut acc : FW := FW.c (lit 0)
      for b_k in [arrInt SIDE_BLOCK_START s_k:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if arrInt BLOCK_TABLE b_k = NO_TABLE then
          innerSum := FW.c (lit 0)
          for i in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := arrInt BLOCK_COORD_OFF b_k + i
            if arrInt COORD_TYPE ci ≠ COORD_KIND_PUBLIC then
              if s_k = COUNT_SIDE then
                innerSum ← fold (innerSum + coordVals[ci])
              else
                innerSum ← fold (innerSum + fpW[GEN ^ i] * coordVals[ci])
          if s_k = COUNT_SIDE then
            acc ← fold (acc + Ex.v blockEqHi[b_k] * innerSum)
          else
            acc ← fold (acc + blockEqHi[b_k] * (beta + innerSum))
      if s_k ≠ COUNT_SIDE then
        acc ← fold (acc + Ex.v publicEqs[s_k] * bcShare)
      -- The table sumcheck sums a table block's form phi over every row, padding rows included, whose leaves are 1 instead: the difference, (1 - phi(p_j)) times the table's pad_weight, is public and joins the padding mass.
      if s_k = PULL_SIDE then
        acc ← fold (acc + pushPadding)
      else
        paddingSum := FW.c (lit 0)
        for t_k in [0:N_TABLES] do
          tableSum := FW.c (lit 0)
          for b_k in [arrInt SIDE_BLOCK_START s_k:arrInt SIDE_BLOCK_START (s_k + 1)] do
            if arrInt BLOCK_TABLE b_k = t_k then
              if s_k = COUNT_SIDE then
                coeff := FW.c (lit 1)
              else
                coeff := FW.w beta1
              for i in [0:arrInt BLOCK_COORD_COUNT b_k] do
                ci := arrInt BLOCK_COORD_OFF b_k + i
                if arrInt COORD_PADDING ci ≠ 0 then
                  if s_k = COUNT_SIDE then
                    coeff ← fold (coeff + arrWord COORD_PADDING ci)
                  else
                    coeff ← fold (coeff + fpW[GEN ^ i] * arrWord COORD_PADDING ci)
              tableSum ← fold (tableSum + Ex.v blockEqHi[b_k] * coeff)
          paddingSum ← fold (paddingSum + Ex.v padWeight[t_k] * tableSum)
        acc ← fold (acc + paddingSum)
        if s_k = PUSH_SIDE then
          pushPadding ← val paddingSum
      acc ← fold (acc + (1 + selectorSums[s_k]))
      busTableTotal[s_k] := acc + gkrLeaves[GEN ^ s_k]
    let mut claimIdx := N_BUS_CLAIMS  -- the table and public-input claims follow the deduped bus claims
    -- ---- ONE table sumcheck for all six tables ---- Mirrors crates/verifier's table_sumcheck. zc_xi ONCE, each table folding its own identities with a DISJOINT range of its powers (ETA_OFFSET[t]); one shared point zeta (the bus GKR's); n = max_t tau_t rounds. Rounds bind the HIGHEST variable first, so a 2^tau table sits out the first n - tau and joins carrying the challenges it sat out, weighing cprod[n - tau] * peq[tau] where peq[tau] = eq(zeta[..tau], chi[..tau]); the zc_xi-powers are inside constraint_eval.
    --
    -- g^n is hinted, then pinned exactly: the range-checked division slacks force it to dominate every certified tau and the product identity forces it to BE one.
    let gZcN ← hinted (B.witnessCell "zc_tau_max")
    let mut zcIsATau : FW := FW.c (lit 1)
    for t_k in [0:N_TABLES] do
      tauG := kb[2 + t_k]
      assert log (gZcN / tauG) < COUNT_BITS
      zcIsATau ← fold (zcIsATau * (gZcN + tauG))
    assert zcIsATau == 0
    -- n <= mu, the `Error::Truncated` of constraints.rs. Every table pushes at kappa = tau, so it holds structurally, but zc_peq below reads zeta[..n] and zeta only holds mu coords: unwritten heap there is prover-chosen.
    assert log (gBusMu / gZcN) < COUNT_BITS
    -- xi, after its grind, the bytecode value waiting: the batch is of degree N_ETA_POWS - 1 in it.
    let (t14, t15, t16) ← fsGrindSqueeze sp rate 1 cursor (Shifted.of tabs) XI_GRIND_BITS
    sp := t14
    let zcXi := t15
    cursor := t16
    let zcXiPows ← B.stackBuf N_ETA_POWS
    zcXiPows[0] := 1
    for k in [1:N_ETA_POWS] do
      zcXiPows[k] := zcXiPows[k - 1] * zcXi
    -- The eq point is the bus GKR's zeta, NOT a fresh one, which is what lets the batch settle the bus forms alongside the constraints. It is also why no target is read: what the three sides' tables owe, each in its own shared power of zc_xi, IS the sum the batch must reach, and zc_xi is squeezed after those totals are fixed, so hitting one number forces all three side equations.
    let mut busTarget : FW := FW.c (lit 0)
    for sd in [0:N_GKR_SIDES] do
      busTarget ← fold (busTarget + zcXiPows[ETA_FORM_BASE + sd] * busTableTotal[sd])
    -- n vanilla sumcheck rounds: the round polynomial arrives whole, so a round is `h(0) + h(1) == claim` and a fold, with no eq to reapply. The tables still waiting ride inside h, so nothing here is indexed by height; the heights enter only the per-table weights below.
    let zcRounds ← B.heapBufDyn (← val ((gZcN * GEN) ^ ROUND_SLOTS))
    let zcCprod ← B.heapBufDyn (← val (gZcN * GEN))  -- the challenges bound so far, multiplied
    fsStore (Shifted.of zcRounds) ROUND_FS 1 sp
    zcRounds[GEN ^ ROUND_CURSOR] := cursor
    zcRounds[GEN ^ ROUND_CLAIM] := busTarget
    zcCprod[GEN ^ 0] := 1
    B.loopRtF 0 (pure gZcN) 5 (pure ([zcRounds.v, tabs.v, chi.v, gZcN.v, zcCprod.v])) fun xk caps => do
      let zcRounds := caps[0]
      let tabs := caps[1]
      let chi := caps[2]
      let gZcN := caps[3]
      let zcCprod := caps[4]
      let rd ← val (zcRounds * xk ^ ROUND_SLOTS)
      let t0 ← callN "sumcheck_round4" [rd, rd[GEN ^ ROUND_CURSOR], rd[GEN ^ ROUND_CLAIM], tabs] 3
      let ncur := t0[0]!
      let nclaim := t0[1]!
      let rk := t0[2]!
      chi[GEN ^ 0 * (gZcN * INV_GEN / xk)] := rk  -- g^(n-1-j): the variable round j binds
      let nxt : Shifted := ⟨rd, ROUND_SLOTS⟩
      nxt[GEN ^ ROUND_CURSOR] := ncur
      nxt[GEN ^ ROUND_CLAIM] := nclaim
      -- cprod is the weight of a table that joins here; peq below is the rest
      let t1 ← val (zcCprod[xk] * rk)
      zcCprod[GEN ^ 1 * xk] := t1
    let zcLast ← val (zcRounds * gZcN ^ ROUND_SLOTS)
    sp ← fsLoad zcLast ROUND_FS 1
    rate ← B.stackBuf 8
    cursor ← Shifted.of <$> val zcLast[GEN ^ ROUND_CURSOR]
    let claim ← val zcLast[GEN ^ ROUND_CLAIM]
    -- peq[g^tau] = eq(zeta[..tau], chi[..tau]), as a prefix chain.
    let zcPeq ← B.heapBufDyn (← val (gZcN * GEN))
    call "eq_prefix_chain" [zcPeq, 1, chi, zeta1, gZcN]
    -- Per table: every committed column's evaluation (pooled), its AIR constraint at its own reduced point chi[..tau_t], weighted into the batch's final claim.
    let mut airAcc : FW := FW.c (lit 0)
    -- The column evaluations stay where the stream holds them, N_COL_EVALS consecutive words that fs_next bound: the pool's slots from N_BUS_CLAIMS on are read there rather than copied.
    let colEvalWords : Shifted := cursor
    let mut e : Word := default
    let mut c : Word := default
    let mut b : Word := default
    let mut nTerms : Nat := default
    let mut first : Nat := default
    let mut cv : FW := default
    let mut tj : Nat := default
    let mut form : FW := default
    let mut inner : FW := default
    let mut pushForm : Word := default
    for t_k in [0:N_TABLES] do
      tauG := kb[2 + t_k]
      let colEvals ← B.stackBuf TABLE_COLS_CAP
      for pos in [arrInt TABLE_COL_BASE t_k:arrInt TABLE_COL_BASE t_k + arrInt N_TABLE_COLS t_k] do
        if pos % 4 = 0 then
          if pos ≠ 0 then
            sp ← fsPerm sp rate 4
            rate ← B.stackBuf 8
        let (t17, t18) ← fsNext rate (pos % 4) cursor
        e := t17
        cursor := t18
        colEvals[pos - arrInt TABLE_COL_BASE t_k] := e
        claimIdx := claimIdx + 1
      -- The table's AIR constraint at the final point (col_evals is indexed by local column index; the formulas mirror tables.rs Table::constraint). Every value relation now rides the bus as a degree-2 coordinate, so only JUMP's is-nonzero indicator is left with an identity of its own.
      let mut constraintEval : FW := FW.c (lit 0)
      if t_k = TABLE_JUMP then
        -- `b = c*w` and `c*(b+1) = 0`. The condition is K-valued, its memory read carrying literal zeros above the low limb, so both identities are single-lane (tables.rs JumpTable::constraint). Local columns: v_cond at 5, w at 12, the indicator b at 13.
        c := colEvals[5]
        b := colEvals[13]
        constraintEval ← fold (zcXiPows[arrInt ETA_OFFSET t_k] * (b + c * Ex.v colEvals[12]))
        constraintEval ← fold (constraintEval + zcXiPows[arrInt ETA_OFFSET t_k + 1] * (c * (b + 1)))
      -- The table's bus coordinates, evaluated at the SAME column evaluations, each the sum of its terms over this table's column evaluations (a product term, an address or an arithmetic result, is degree 2, which the batch's round polynomial already allows); a pull coordinate as its difference from its push twin's, where the two differ. This is what replaces opening those columns at ζ.
      for b_k in [0:N_BLOCKS] do
        if arrInt BLOCK_TABLE b_k = t_k then
          for i in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := arrInt BLOCK_COORD_OFF b_k + i  -- a compile-time index, so `ci` costs nothing
            if arrInt BLOCK_SIDE b_k = PULL_SIDE then
              nTerms := arrInt COORD_DIFF_COUNT ci
              first := arrInt COORD_DIFF_OFF ci
            else
              nTerms := arrInt COORD_TERM_COUNT ci
              first := arrInt COORD_TERM_OFF ci
            if nTerms ≠ 0 then
              cv := FW.c (lit 0)
              for j in [0:nTerms] do
                tj := first + j
                if arrInt TERM_TYPE tj = COORD_KIND_CONST then
                  cv ← fold (cv + arrWord TERM_CONST tj)
                if arrInt TERM_TYPE tj = COORD_KIND_COL then
                  cv ← fold (cv + colEvals[arrInt TERM_COL_A tj])
                if arrInt TERM_TYPE tj = COORD_KIND_GCOL then
                  cv ← fold (cv + arrWord TERM_CONST tj * colEvals[arrInt TERM_COL_A tj])
                if arrInt TERM_TYPE tj = COORD_KIND_PROD then
                  cv ← fold (cv + arrWord TERM_CONST tj * (colEvals[arrInt TERM_COL_A tj] * colEvals[arrInt TERM_COL_B tj]))
              coordVals[ci] := cv
      -- Its forms, one a side: Σ_b eq_hi(b) · (β + Σ_i w(i) · coord_i). A pull block shares its push twin's eq_hi, so a pull form is push's plus the coordinates where the two differ.
      for sd in [0:N_GKR_SIDES] do
        form := FW.c (lit 0)
        for b_k in [arrInt SIDE_BLOCK_START sd:arrInt SIDE_BLOCK_START (sd + 1)] do
          if arrInt BLOCK_TABLE b_k = t_k then
            inner := FW.c (lit 0)
            for i in [0:arrInt BLOCK_COORD_COUNT b_k] do
              ci := arrInt BLOCK_COORD_OFF b_k + i
              if sd = PULL_SIDE then
                nTerms := arrInt COORD_DIFF_COUNT ci
              else
                nTerms := arrInt COORD_TERM_COUNT ci
              if nTerms ≠ 0 then
                if sd = COUNT_SIDE then
                  inner ← fold (inner + coordVals[ci])
                else
                  inner ← fold (inner + fpW[GEN ^ i] * coordVals[ci])
            if sd = PUSH_SIDE then
              form ← fold (form + blockEqHi[b_k] * (beta + inner))
            else
              form ← fold (form + Ex.v blockEqHi[b_k] * inner)
        if sd = PUSH_SIDE then
          pushForm ← val form
        if sd = PULL_SIDE then
          form ← fold (pushForm + form)
        constraintEval ← fold (constraintEval + Ex.v zcXiPows[ETA_FORM_BASE + sd] * form)
      airAcc ← fold (airAcc + zcCprod[GEN ^ 0 * (gZcN / tauG)] * zcPeq[tauG] * constraintEval)  -- cprod[n - tau] * peq[tau]
    assert airAcc == claim
    -- ---- public-input binding claim: one per MEM limb, read off no stream ---- The VM's bind_pi_claim claims each committed MEM limb at [rm, 0..] equals that limb's line through the public words, lo_0 + rm*(lo_0 + lo_1) and so on, which the statement alone determines. split_limbs binds each word's limbs (doc sec:e2e-pi).
    let (t19, t20) ← squeeze sp rate ((N_COL_EVALS + 3) % 4 + 1)
    sp := t19
    let rm := t20
    let (lo0, hi0) ← splitLimbs pi0
    let (lo1, hi1) ← splitLimbs pi1
    claimPool[GEN ^ claimIdx] := lo0 + rm * (lo0 + lo1)
    claimIdx := claimIdx + 1
    claimPool[GEN ^ claimIdx] := hi0 + rm * (hi0 + hi1)
    claimIdx := claimIdx + 1
    let t25 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val cursor)
    let t26 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val colEvalWords)
    return [.v sp[8].v, .v sp[9].v, .v sp[10].v, .v sp[11].v, .v sp[12].v, .into t25, .v gZcN.v, .v bcValue.v, .v rm.v, .into t26]

/-- Extend every t-bit prefix p of r by bit t of r, to p and p + 2^t: c0[p], c1[p] weigh the carry 0 and 1 into bit t, and e_t, u_t, v_t are bit t's weights for (x, y) equal, (1, 0) and (0, 1). The zero prefix never carries. -/
def carryStep (c0 : List V) (c1 : List V) (n0 : List V) (n1 : List V) (eT : Word) (uT : Word) (vT : Word) (t : Nat) : B Unit := B.inline "carry_step" do
  for p in [0:2 ^ t] do
    if p = 0 then
      n0[0] := c0[0] * eT
      n0[2 ^ t] := c0[0] * uT
      n1[2 ^ t] := c0[0] * vT
    else
      n0[p] := c0[p] * eT + c1[p] * uT
      n1[p] := c1[p] * vT
      n0[p + 2 ^ t] := c0[p] * uT
      n1[p + 2 ^ t] := c0[p] * vT + c1[p] * eT

/-- carry_step's last bit, the carry out dropped: u_t + v_t = s_t weighs it either way. -/
def carryWrap (c0 : List V) (c1 : List V) (out : List V) (eT : Word) (sT : Word) (t : Nat) : B Unit := B.inline "carry_wrap" do
  for p in [0:2 ^ t] do
    if p = 0 then
      out[0] := c0[0] * eT
      out[2 ^ t] := c0[0] * sT
    else
      out[p] := c0[p] * eT + c1[p] * sT
      out[p + 2 ^ t] := c0[p] * sT + c1[p] * eT

/-- shifts[r] for every used r: the multilinear extension of "x = y + r mod 64" at (a, b), a ripple of the carry over the six bits. Split r = rl + 8 rh: the low three bits leave a carry c into the high three, which then add rh + c, so shifts[r] = L0[rl] H[rh] + L1[rl] H[rh + 1] over tables of eight. -/
def keccakShiftsEq (a : Word) (b : Word) (shifts : List V) : B Unit := B.inline "keccak_shifts_eq" do
  let wEq ← B.stackBuf KECCAK_Z_BITS
  let wSum ← B.stackBuf KECCAK_Z_BITS
  let wUp ← B.stackBuf KECCAK_Z_BITS
  let wDown ← B.stackBuf KECCAK_Z_BITS
  -- Bits 0 and 3 start the two tables: their weights are the first level itself.
  let lo0 ← B.stackBuf 2
  let lo1 ← B.stackBuf 2
  let hi0 ← B.stackBuf 2
  let hi1 ← B.stackBuf 2
  -- As products, (1 + a)(1 + b) + ab, a(1 + b) and (1 + a)b, trading XORs for MULs; b's 1 + b_t is the local sumcheck's, already in the frame.
  for t in [0:KECCAK_Z_BITS] do
    let aT ← val a[GEN ^ t]
    let bT ← val b[GEN ^ t]
    let aT1 ← val (1 + aT)
    let bT1 ← val (1 + bT)
    if t = 0 then
      lo0[0] := aT1 * bT1 + aT * bT
      lo0[1] := aT * bT1
      lo1[1] := aT1 * bT
    else if t = 3 then
      hi0[0] := aT1 * bT1 + aT * bT
      hi0[1] := aT * bT1
      hi1[1] := aT1 * bT
    else if t + 1 = KECCAK_Z_BITS then
      wEq[t] := aT1 * bT1 + aT * bT
      wSum[t] := aT + bT
    else
      wEq[t] := aT1 * bT1 + aT * bT
      wUp[t] := aT * bT1
      wDown[t] := aT1 * bT
  let mid0 ← B.stackBuf 4
  let mid1 ← B.stackBuf 4
  carryStep lo0 lo1 mid0 mid1 wEq[1] wUp[1] wDown[1] 1
  let low0 ← B.stackBuf 8
  let low1 ← B.stackBuf 8
  carryStep mid0 mid1 low0 low1 wEq[2] wUp[2] wDown[2] 2
  let hmid0 ← B.stackBuf 4
  let hmid1 ← B.stackBuf 4
  carryStep hi0 hi1 hmid0 hmid1 wEq[4] wUp[4] wDown[4] 1
  let high ← B.stackBuf 8
  carryWrap hmid0 hmid1 high wEq[5] wSum[5] 2
  for r in [0:64] do
    if arrInt KECCAK_SHIFT_USED r = 1 then
      if r % 8 = 0 then
        shifts[r] := low0[0] * high[r / 8]
      else
        shifts[r] := low0[r % 8] * high[r / 8] + low1[r % 8] * high[(r / 8 + 1) % 8]

/-- x0 + a (x0 + x1) as (1 + a) x0 + a x1: a MUL for an XOR, the scarcer row. -/
def foldNode (src : List V) (dst : List V) (aT : Word) (aT1 : Word) (p : Nat) (b : Nat) (t : Nat) : B Unit := B.inline "fold_node" do
  let n := 2 ^ (KECCAK_Z_BITS - t)
  for k in [0:n / 2] do
    let x0 := src[p * n + (2 * k + (n - 1) * b) % n]
    let x1 := src[p * n + (2 * k + 1 + (n - 1) * b) % n]
    dst[(p + 2 ^ t * b) * (n / 2) + k] := aT1 * x0 + aT * x1

/-- One level of sum_w eq(a, w) V[w - r] for every used r at once, LSB first: node p of depth t is the vector for the residue p of r mod 2^t, 2^(6 - t) cells at p 2^(6 - t). Folding bit t splits it by bit t of r, b: V[w - r] pairs the parent's cells 2k - b and 2k + 1 - b. -/
def foldShifts (src : List V) (dst : List V) (aT : Word) (t : Nat) : B Unit := B.inline "fold_shifts" do
  let aT1 ← val (1 + aT)
  for p in [0:2 ^ t] do
    for b in [0:2] do
      if t + 1 = KECCAK_Z_BITS then
        if arrInt KECCAK_SHIFT_USED (p + 2 ^ t * b) = 1 then
          foldNode src dst aT aT1 p b t
      else
        foldNode src dst aT aT1 p b t

/-- <L^T(E), f> for theta, rho, pi's transpose L^T, on weights that factor as lane times slice: E = lanes (x) eZ and f = f_lanes (x) fZ, the slices entering only through shifts[r] = sum_z fZ[z] eZ[(z + r) % 64]. f_lanes are frame cells from f_off. -/
def keccakForm (lanes : Word) (shifts : List V) (fLanes : List V) (fOff : Nat) : B FW := B.inline "keccak_form" do
  let mut total : FW := FW.c (lit 0)
  let column ← B.stackBuf 5
  let columnNext ← B.stackBuf 5
  let fColumn ← B.stackBuf 5
  let mut laneWeight : Word := default
  let mut moved : Word := default
  let mut fWeight : Word := default
  for x in [0:5] do
    let mut acc : FW := FW.c (lit 0)
    let mut accNext : FW := FW.c (lit 0)
    let mut fAcc : FW := FW.c (lit 0)
    for y in [0:5] do
      laneWeight ← val lanes[GEN ^ (arrInt KECCAK_PI (x + 5 * y))]
      moved ← val (laneWeight * shifts[arrInt KECCAK_RHO (x + 5 * y)])
      fWeight := fLanes[fOff + x + 5 * y]
      total ← fold (total + fWeight * moved)
      acc ← fold (acc + moved)
      accNext ← fold (accNext + laneWeight * Ex.v shifts[(arrInt KECCAK_RHO (x + 5 * y) + 1) % 64])
      fAcc ← fold (fAcc + fWeight)
    column[x] := acc
    columnNext[x] := accNext
    fColumn[x] := fAcc
  for x in [0:5] do
    total ← fold (total + fColumn[x] * (column[(x + 1) % 5] + columnNext[(x + 4) % 5]))
  return total

/-- eq(local, z) from the five-coordinate tree `slices` and the top coordinate. -/
def sliceWeight (slices : List V) (top : Word) (top1 : Word) (z : Nat) : B Word := B.inline "slice_weight" do
  let mut w : Word := default
  if z / 32 = 1 then
    w ← val (slices[2 ^ (KECCAK_Z_BITS - 1) - 2 + z % 32] * top)
  else
    w ← val (slices[2 ^ (KECCAK_Z_BITS - 1) - 2 + z % 32] * top1)
  return w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- One layer (verifier::keccak::verify_layer): the claim on the states after a round becomes one on the states before it. A claim's position weights are never written out: they are the transpose of the linear layer applied to a lane table times the eq table of six slice coordinates, which is all the record keeps, and what `keccak_form` evaluates them from. The first layer starts with the committed outputs' value waiting in the sponge, its two rate cells p0 and p1. -/
def keccakLayer (first : Nat) : GFn where
  name := instName "keccak_layer" [.L first]
  arity := 15
  rets := 6
  body ps := do
    let fs0 := ps[0]
    let fs1 := ps[1]
    let fs2 := ps[2]
    let fs3 := ps[3]
    let fs4 := ps[4]
    let p0 := ps[5]
    let p1 := ps[6]
    let cursor : Shifted := Shifted.of ps[7]
    let yG := ps[8]
    let stepG := ps[9]
    let remG := ps[10]
    let claim := ps[11]
    let out := ps[12]
    let iota := ps[13]
    let tabs := ps[14]
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut rate ← B.stackBuf 8
    if first = 1 then
      rate[0] := p0
      rate[1] := p1
    -- Each product coefficient's reader, a straight line of sums over the instance weights.
    let readers ← B.stackBuf KECCAK_PROJ_CELLS
    for i in [0:KECCAK_PACK] do
      readers[i] := claim[GEN ^ (KC_MU + i)]
    for t in [0:KECCAK_PROJ_A.length] do
      readers[KECCAK_PACK + t] := readers[arrInt KECCAK_PROJ_A t] + readers[arrInt KECCAK_PROJ_B t]
    -- The product polynomial carries the claim.
    let product ← B.stackBuf KECCAK_PROD_BITS
    let mut projected : FW := FW.c (lit 0)
    for pos in [first:first + KECCAK_PROD_BITS] do
      -- fs_next, the word read straight into its cell, k = pos - first.
      product[pos - first] := cursor[GEN ^ (pos - first)]
      let coefficient := product[pos - first]
      if pos % 4 = 0 then
        if pos ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
      fsPack rate (pos % 4) (FW.w coefficient) DS_OBSERVE
      projected ← fold (projected + Ex.v readers[arrInt KECCAK_PROJ_OUT (pos - first)] * coefficient)
    let cursor : Shifted := ⟨cursor.base, cursor.exp + KECCAK_PROD_BITS⟩
    assert projected + iota * claim[GEN ^ KC_KAPPA] == claim[GEN ^ KC_VALUE]
    -- At a random point a pack is one field element, after a grind: the polynomial has degree KECCAK_PROD_BITS - 1.
    let (t0, t1, t2) ← fsGrindSqueeze sp rate ((first + KECCAK_PROD_BITS + 3) % 4 + 1) cursor (Shifted.of tabs) 3
    sp := t0
    let s := t1
    let cursor : Shifted := t2
    -- mu[i] = emb_i(s), each embedding a product of small irreducible factors.
    let sPowers ← B.stackBuf KECCAK_FAC_DEG
    sPowers[0] := 1
    sPowers[1] := s
    for b in [2:KECCAK_FAC_DEG] do
      sPowers[b] := sPowers[b - 1] * s
    let factors ← B.stackBuf KECCAK_EMB_CELLS
    for f in [0:KECCAK_FAC_N] do
      let mut acc : FW := FW.c (lit 0)
      for t in [arrInt KECCAK_FAC_START f:arrInt KECCAK_FAC_START (f + 1)] do
        acc ← fold (acc + sPowers[arrInt KECCAK_FAC_IDX t])
      factors[f] := acc
    for t in [0:KECCAK_EMB_A.length] do
      factors[KECCAK_FAC_N + t] := factors[arrInt KECCAK_EMB_A t] * factors[arrInt KECCAK_EMB_B t]
    let mut kappa : FW := FW.c (lit 0)  -- the sum of the weights
    for i in [0:KECCAK_PACK] do
      out[GEN ^ (KC_MU + i)] := factors[arrInt KECCAK_EMB_OUT i]
      kappa ← fold (kappa + factors[arrInt KECCAK_EMB_OUT i])
    out[GEN ^ KC_KAPPA] := kappa
    let mut value := product[KECCAK_PROD_BITS - 1]
    for k in [1:KECCAK_PROD_BITS] do
      value ← val (value * s + product[KECCAK_PROD_BITS - 1 - k])
    -- The pack and the segment, a runtime number of rounds: KR_STEP step_g, KR_STEP a loop step, then rem_g, one a loop step (a loop rather than an unrolled arm per remainder, whose shared frame would grow every layer's).
    let prevPoint ← val claim[GEN ^ KC_POINT]
    let point ← B.heapBufDyn yG
    let rounds ← B.heapBuf 77
    fsStore (Shifted.of rounds) KR_FS KR_CAP sp
    rounds[GEN ^ 55] := cursor
    rounds[GEN ^ 66] := value
    B.loopRtF 0 (pure stepG) 4 (pure ([rounds.v, prevPoint.v, point.v, tabs.v])) fun xs caps => do
      let rounds := caps[0]
      let prevPoint := caps[1]
      let point := caps[2]
      let tabs := caps[3]
      let rd ← val (rounds * xs)
      let pp ← val (prevPoint * xs ^ KR_STEP)
      let pt ← val (point * xs ^ KR_STEP)
      let mut roundSp ← fsLoad rd KR_FS KR_CAP
      let mut curI : Shifted ← Shifted.of <$> val rd[GEN ^ 55]
      let mut run ← val rd[GEN ^ 66]
      for q in [0:KR_STEP] do
        -- q has degree two with the eq factor pulled out, and the prover sends its coefficients c1 and c2 (g_1, g_2), c0 being fixed by the claim. With r the round's coordinate and c its challenge, q(c) = claim + (r + c) c1 + (r + c^2) c2, which is the next normalized claim. The round grinds for degree three, the eq factor included.
        let rEq ← val pp[GEN ^ q]
        let rate ← B.stackBuf 8
        let (t0, t1) ← fsNext rate 0 curI
        let g1 := t0
        curI := t1
        let (t2, t3) ← fsNext rate 1 curI
        let g2 := t2
        curI := t3
        let (t4, t5, t6) ← fsGrindSqueeze roundSp rate 2 curI (Shifted.of tabs) ROUND3_GRIND_BITS
        roundSp := t4
        let challenge := t5
        curI := t6
        pt[GEN ^ q] := challenge
        let gap ← val (rEq + challenge)
        run ← val (run + gap * g1 + (rEq + challenge * challenge) * g2)
      let nxt : Shifted := ⟨rd, 1⟩
      fsStore nxt KR_FS KR_CAP roundSp
      nxt[GEN ^ 55] := curI
      nxt[GEN ^ 66] := run
    let remRounds ← val (rounds * stepG)
    let remPrev ← val (prevPoint * stepG ^ KR_STEP)
    let remPoint ← val (point * stepG ^ KR_STEP)
    B.loopRtF 0 (pure remG) 4 (pure ([remRounds.v, remPrev.v, tabs.v, remPoint.v])) fun x1 caps => do
      let remRounds := caps[0]
      let remPrev := caps[1]
      let tabs := caps[2]
      let remPoint := caps[3]
      let rd ← val (remRounds * x1)
      let rEq ← val remPrev[x1]
      let roundSp ← fsLoad rd KR_FS KR_CAP
      let curI : Shifted ← Shifted.of <$> val rd[GEN ^ 55]
      let rate ← B.stackBuf 8
      let (g1, curI) ← fsNext rate 0 curI
      let (g2, curI) ← fsNext rate 1 curI
      let (roundSp, challenge, curI) ← fsGrindSqueeze roundSp rate 2 curI (Shifted.of tabs) ROUND3_GRIND_BITS
      remPoint[x1] := challenge
      let gap ← val (rEq + challenge)
      let nxt : Shifted := ⟨rd, 1⟩
      fsStore nxt KR_FS KR_CAP roundSp
      nxt[GEN ^ 55] := curI
      nxt[GEN ^ 66] := rd[GEN ^ 66] + gap * g1 + (rEq + challenge * challenge) * g2
    let last ← val (remRounds * remG)
    sp ← fsLoad last KR_FS KR_CAP
    let mut cursor : Shifted ← Shifted.of <$> val last[GEN ^ 55]
    value ← val last[GEN ^ 66]
    -- The bit position: degree three, the weights being one more multilinear factor.
    let local' ← B.heapBuf KECCAK_LOCAL_BITS
    for i in [0:KECCAK_LOCAL_BITS] do
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      let c0 := t3
      cursor := t4
      let (t5, t6) ← fsNext rate 1 cursor
      let c2 := t5
      cursor := t6
      let (t7, t8) ← fsNext rate 2 cursor
      let c3 := t7
      cursor := t8
      let (t9, t10, t11) ← fsGrindSqueeze sp rate 3 cursor (Shifted.of tabs) ROUND3_GRIND_BITS
      sp := t9
      let challenge := t10
      cursor := t11
      local'[GEN ^ i] := challenge
      -- c1 = value + c2 + c3, so h(c) = c0 + c (value + (1 + c) (c2 + (1 + c) c3)).
      let challenge1 ← val (1 + challenge)
      value ← val (c0 + challenge * (value + challenge1 * (c2 + challenge1 * c3)))
    rate ← B.stackBuf 8
    let (t12, t13) ← fsNext rate 0 cursor
    let t0 := t12
    cursor := t13
    let (t14, t15) ← fsNext rate 1 cursor
    let t1 := t14
    cursor := t15
    let (t16, t17) ← fsNext rate 2 cursor
    let t2 := t16
    cursor := t17
    -- The claim's weights at the local point.
    let fLanes ← B.stackBuf 62
    eqtreeFrame ⟨local', KECCAK_Z_BITS⟩ fLanes KECCAK_LANE_BITS KECCAK_LANES
    let prevLanes ← val claim[GEN ^ KC_LANES]
    let weightAtLocal ← B.stackBuf 1
    if first = 1 then
      -- The first claim weighs a lane table times the bits of a word, x^z.
      let mut lanesEq : FW := FW.c (lit 0)
      for lane in [0:KECCAK_LANES] do
        lanesEq ← fold (lanesEq + fLanes[LANE_OFF + lane] * prevLanes[GEN ^ lane])
      for t in [0:KECCAK_Z_BITS] do
        lanesEq ← fold (lanesEq * (1 + local'[GEN ^ t] * (1 + GEN ^ (2 ^ t))))
      weightAtLocal[0] := lanesEq
    else
      let shifts ← B.stackBuf 64
      keccakShiftsEq (← val claim[GEN ^ KC_LOCAL]) local' shifts
      let t18 ← keccakForm prevLanes shifts fLanes LANE_OFF
      weightAtLocal[0] := t18
    assert weightAtLocal[0] * (kappa * t0 + (kappa + t1) * t2) == value
    -- t[k] = sum_j eq[j] T[j + k]: one claim on the state before chi, quadratic in beta.
    let (t18, t19, t20) ← fsGrindSqueeze sp rate 3 cursor (Shifted.of tabs) KECCAK_BETA_GRIND_BITS
    sp := t18
    let beta := t19
    cursor := t20
    out[GEN ^ KC_VALUE] := t0 + beta * (t1 + beta * t2)
    out[GEN ^ KC_POINT] := point
    out[GEN ^ KC_LOCAL] := local'
    let lanes ← B.heapBuf KECCAK_LANES
    for y in [0:5] do
      for x in [0:5] do
        lanes[GEN ^ (x + 5 * y)] := fLanes[LANE_OFF + x + 5 * y] + beta * (fLanes[LANE_OFF + (x + 4) % 5 + 5 * y] + beta * fLanes[LANE_OFF + (x + 3) % 5 + 5 * y])
    out[GEN ^ KC_LANES] := lanes
    -- The next layer's iota term: for every i, the new claim's weight on slice 2^i - 1 of lane 0, through the linear layer's transpose, from its lane and slice weights. The slice weights are an eq tree on the low five coordinates, times the top one's factor where a weight is read.
    let slices ← B.stackBuf 62
    eqtreeFrame (Shifted.of local') slices (KECCAK_Z_BITS - 1) (2 ^ (KECCAK_Z_BITS - 1))
    let top ← val local'[GEN ^ 5]
    let top1 ← val (1 + top)
    let flips ← B.heapBuf KECCAK_IOTA_BITS
    for i in [0:KECCAK_IOTA_BITS] do
      let t22 ← val lanes[GEN ^ (arrInt KECCAK_PI 0)]
      let t21 ← sliceWeight slices top top1 ((2 ^ i - 1 + arrInt KECCAK_RHO 0) % 64)
      let mut flipped ← val (t22 * t21)
      for y in [0:5] do
        let t24 ← val lanes[GEN ^ (arrInt KECCAK_PI (1 + 5 * y))]
        let t23 ← sliceWeight slices top top1 ((2 ^ i - 1 + arrInt KECCAK_RHO (1 + 5 * y)) % 64)
        flipped ← val (flipped + t24 * t23)
        let t26 ← val lanes[GEN ^ (arrInt KECCAK_PI (4 + 5 * y))]
        let t25 ← sliceWeight slices top top1 ((2 ^ i + arrInt KECCAK_RHO (4 + 5 * y)) % 64)
        flipped ← val (flipped + t26 * t25)
      flips[GEN ^ i] := flipped
    out[GEN ^ KC_FLIPS] := flips
    let t27 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val cursor)
    return [.v sp[8].v, .v sp[9].v, .v sp[10].v, .v sp[11].v, .v sp[12].v, .into t27]

/-- n rounds of a degree-2 sumcheck with no equality factor, each grinding for its degree. With k0 = 1 one scalar already waits in the sponge, rate cells p0 and p1, and the first round's words join it. -/
def keccakPlainRounds (n : Nat) (k0 : Nat) : GFn where
  name := instName "keccak_plain_rounds" [.L n, .L k0]
  arity := 11
  rets := 7
  body ps := do
    let fs0 := ps[0]
    let fs1 := ps[1]
    let fs2 := ps[2]
    let fs3 := ps[3]
    let fs4 := ps[4]
    let p0 := ps[5]
    let p1 := ps[6]
    let mut cursor : Shifted := Shifted.of ps[7]
    let mut value := ps[8]
    let point := ps[9]
    let tabs := ps[10]
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    for i in [0:n] do
      let rate ← B.stackBuf 8
      let mut c0 : Word := default
      let mut c2 : Word := default
      let mut challenge : Word := default
      if i = 0 then
        if k0 = 1 then
          rate[0] := p0
          rate[1] := p1
          let (t0, t1) ← fsNext rate 1 cursor
          c0 := t0
          cursor := t1
          let (t2, t3) ← fsNext rate 2 cursor
          c2 := t2
          cursor := t3
          let (t4, t5, t6) ← fsGrindSqueeze sp rate 3 cursor (Shifted.of tabs) ROUND2_GRIND_BITS
          sp := t4
          challenge := t5
          cursor := t6
        else
          let (t0, t1) ← fsNext rate 0 cursor
          c0 := t0
          cursor := t1
          let (t2, t3) ← fsNext rate 1 cursor
          c2 := t2
          cursor := t3
          let (t4, t5, t6) ← fsGrindSqueeze sp rate 2 cursor (Shifted.of tabs) ROUND2_GRIND_BITS
          sp := t4
          challenge := t5
          cursor := t6
      else
        let (t0, t1) ← fsNext rate 0 cursor
        c0 := t0
        cursor := t1
        let (t2, t3) ← fsNext rate 1 cursor
        c2 := t2
        cursor := t3
        let (t4, t5, t6) ← fsGrindSqueeze sp rate 2 cursor (Shifted.of tabs) ROUND2_GRIND_BITS
        sp := t4
        challenge := t5
        cursor := t6
      let c1 ← val (value + c2)
      point[GEN ^ i] := challenge
      value ← val (c0 + challenge * (c1 + challenge * c2))
    let t0 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val cursor)
    return [.v sp[8].v, .v sp[9].v, .v sp[10].v, .v sp[11].v, .v sp[12].v, .into t0, .v value.v]

/-- The weight an opening's slot point puts on each lane, into the frame cells out[0..25): the states it speaks of start at `first`, one per segment, for the first `count` segments. -/
def keccakSlotLanes (slot : Word) (segmentPoint : Word) (out : List V) (first : Nat) (count : Nat) : B Unit := B.inline "keccak_slot_lanes" do
  let slotWeights ← B.stackBuf 126
  eqtreeFrame (Shifted.of slot) slotWeights QKECCAK_SLOT_LOG (KECCAK_LANES * KECCAK_SEGMENTS)
  let segWeights ← B.stackBuf 2
  eqtreeFrame (Shifted.of segmentPoint) segWeights KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
  for lane in [0:KECCAK_LANES] do
    let mut laneAcc : FW := FW.c (lit 0)
    for m in [0:count] do
      laneAcc ← fold (laneAcc + segWeights[2 ^ KECCAK_SEG_LOG - 2 + m] * slotWeights[2 ^ QKECCAK_SLOT_LOG - 2 + KECCAK_LANES * (first + m) + lane])
    out[lane] := laneAcc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- KECCAK validity (verifier::keccak::verify_keccak): a random claim on every segment's output, KECCAK_DEPTH layers down to the committed inputs, every segment at once. The last segment's output is the permutation's: the table's claims on its output lanes, `output_lanes`, at the table's point chi[..tau], give that part of the claim, and the prover sends the committed outputs' part. It leaves two openings of q_keccak, at the two points written to `z_vals` (tau + QKECCAK_SLOT_LOG coordinates each, QKECCAK_VARS_CAP apart): the committed outputs as words at the first, returned, and the 64 `slices` at the second. tau >= FLOORS[TABLE_KECCAK] is certified, so the pack count is a real count. The ring-switching map's challenges are drawn after it, by the caller, under the batch grind. -/
def verifyKeccak : GFn where
  name := "verify_keccak"
  arity := 12
  rets := 7
  body ps := do
    let fs0 := ps[0]
    let fs1 := ps[1]
    let fs2 := ps[2]
    let fs3 := ps[3]
    let fs4 := ps[4]
    let cursor : Shifted := Shifted.of ps[5]
    let tauG := ps[6]
    let chi := ps[7]
    let outputLanes := ps[8]
    let zVals := ps[9]
    let slices := ps[10]
    let tabs := ps[11]
    let sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let noRate ← B.stackBuf 8
    let packG ← val (tauG * INV_GEN ^ KECCAK_PACK_LOG)
    let yG : Shifted := ⟨packG, KECCAK_SEG_LOG⟩
    -- A layer runs y = log(y_g) rounds KR_STEP at a time: y_g = step_g^KR_STEP rem_g, from y's bits, pinned boolean and tied back (y = tau - 3 < 2^5 as tau < COUNT_BITS).
    let yBits ← B.stackBuf 5
    B.hintBitsExpTo (.stack yBits[0:5]) (← val yG) 5
    for j in [0:5] do
      let bit := yBits[j]
      yBits[j] := bit * bit
    let mut stepG : FW := FW.c (gpowE 0)
    for j in [KR_STEP_LOG:5] do
      stepG ← fold (stepG * (1 + yBits[j] * (1 + GEN ^ (2 ^ (j - KR_STEP_LOG)))))
    let mut remG : FW := FW.c (gpowE 0)
    for j in [0:KR_STEP_LOG] do
      remG ← fold (remG * (1 + yBits[j] * (1 + GEN ^ (2 ^ j))))
    assert stepG ^ KR_STEP * remG == yG
    let outPoint := zVals
    let inPoint : Shifted := ⟨zVals, QKECCAK_VARS_CAP⟩
    for i in [0:KECCAK_PACK_LOG] do
      outPoint[GEN ^ i] := chi[GEN ^ i]
    -- The claim's point: chi's pack coordinates, then a fresh segment.
    let point ← B.heapBufDyn (← val yG)
    let chiPack : Shifted := ⟨chi, KECCAK_PACK_LOG⟩
    B.loopRtF 0 (pure packG) 2 (do return [point.v, (← B.shifted chiPack.base chiPack.exp).v]) fun xt caps => do
      let point := caps[0]
      let chiPack : Shifted := Shifted.of caps[1]
      let t0 ← val chiPack[xt]
      point[xt] := t0
    -- One message, the segment then the lane, after its grind: the first claim is multilinear in them.
    let segment ← val (point * packG)
    let (t0, t1, t2) ← fsGrindSqueeze sp noRate 0 cursor (Shifted.of tabs) 0
    let mut sp := t0
    let r := t1
    let cursor : Shifted := t2
    segment[GEN ^ 0] := r
    let rLane ← B.heapBuf KECCAK_LANE_BITS
    for i in [0:KECCAK_LANE_BITS] do
      let (t3, t4) ← squeeze sp noRate 0
      sp := t3
      let r := t4
      rLane[GEN ^ i] := r
    -- The committed outputs' value waits in the sponge until the first layer's words.
    let valueRate ← B.stackBuf 8
    let (t5, t6) ← fsNext valueRate 0 cursor
    let value := t5
    let mut cursor : Shifted := t6
    let mut fs0 := sp[8]
    let mut fs1 := sp[9]
    let mut fs2 := sp[10]
    let mut fs3 := sp[11]
    let mut fs4 := sp[12]
    -- The first claim combines the output lanes as words: instance weights eq(chi_low), position weights eq(r_lane) on the lane times x^z on the bit.
    let claims ← B.heapBuf 286
    claims[GEN ^ 1] := 1
    claims[GEN ^ KC_POINT] := point
    let muTree ← B.heapBuf 30
    eqtree (Shifted.of outPoint) muTree KECCAK_PACK_LOG
    for i in [0:KECCAK_PACK] do
      claims[GEN ^ (KC_MU + i)] := muTree[GEN ^ (2 ^ KECCAK_PACK_LOG - 2 + i)]
    let laneTree ← B.heapBuf 62
    eqtree (Shifted.of rLane) laneTree KECCAK_LANE_BITS
    let firstLanes : Shifted := ⟨laneTree, 30⟩
    claims[GEN ^ KC_LANES] := firstLanes
    -- `value` is the committed outputs' part; the last segment's is the table's.
    let segmentTree ← B.heapBuf 2
    eqtree (Shifted.of segment) segmentTree KECCAK_SEG_LOG
    let mut output : FW := FW.c (lit 0)
    for lane in [0:KECCAK_LANES] do
      output ← fold (output + firstLanes[GEN ^ lane] * outputLanes[GEN ^ lane])
    claims[GEN ^ KC_VALUE] := value + segmentTree[GEN ^ 1] * output
    let mut used : Nat := default
    let mut claimFlips : Word := default
    let mut flipped : FW := default
    for step in [0:KECCAK_DEPTH] do
      let claim : Shifted := ⟨claims, step * KC_SIZE⟩
      -- iota flips known positions of lane 0, per segment a different round's.
      let claimPoint ← val claim[GEN ^ KC_POINT]
      let segmentTree_run ← B.stackBuf 2
      eqtreeFrame (Shifted.of (← val (claimPoint * packG))) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
      -- The claim's weights where iota can flip, slice 2^i - 1 of lane 0, for the i this step's round constants set: the first claim's are a word's, x^(2^i - 1) on lane 0; a later claim's come from its lane and slice weights through the linear layer's transpose.
      let flips ← B.stackBuf KECCAK_IOTA_BITS
      for i in [0:KECCAK_IOTA_BITS] do
        used := 0
        for t in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step):arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step + KECCAK_SEGMENTS)] do
          if arrInt KECCAK_IOTA_IDX t = i then
            used := 1
        if used = 1 then
          if step = 0 then
            flips[i] := firstLanes[GEN ^ 0] * GEN ^ (2 ^ i - 1)
          else
            claimFlips ← val claim[GEN ^ KC_FLIPS]
            flips[i] := claimFlips[GEN ^ i]
      let mut iota : FW := FW.c (lit 0)
      for m in [0:KECCAK_SEGMENTS] do
        flipped := FW.c (lit 0)
        for t in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step + m):arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step + m + 1)] do
          flipped ← fold (flipped + flips[arrInt KECCAK_IOTA_IDX t])
        iota ← fold (iota + Ex.v segmentTree_run[2 ^ KECCAK_SEG_LOG - 2 + m] * flipped)
      if step = 0 then
        let t7 ← callN (instName "keccak_layer" [.L 1]) [fs0, fs1, fs2, fs3, fs4, valueRate[0], valueRate[1], cursor, yG, stepG, remG, claim, claim * GEN ^ KC_SIZE, iota, tabs] 6
        fs0 := t7[0]!
        fs1 := t7[1]!
        fs2 := t7[2]!
        fs3 := t7[3]!
        fs4 := t7[4]!
        cursor := Shifted.of t7[5]!
      else
        let t7 ← callN (instName "keccak_layer" [.L 0]) [fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, yG, stepG, remG, claim, claim * GEN ^ KC_SIZE, iota, tabs] 6
        fs0 := t7[0]!
        fs1 := t7[1]!
        fs2 := t7[2]!
        fs3 := t7[3]!
        fs4 := t7[4]!
        cursor := Shifted.of t7[5]!
    -- ---- the outputs, whose instance weights are an eq already ---- Their position weights are a word's, so the 64 slices are only needed as the word they add up to: q_keccak itself at the point.
    let outSlot ← val (outPoint * tauG)
    let t7 ← callN (instName "keccak_plain_rounds" [.L QKECCAK_SLOT_LOG, .L 0]) [fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, value, outSlot, tabs] 7
    fs0 := t7[0]!
    fs1 := t7[1]!
    fs2 := t7[2]!
    fs3 := t7[3]!
    fs4 := t7[4]!
    cursor := Shifted.of t7[5]!
    let outValue := t7[6]!
    let wordRate ← B.stackBuf 8
    let (t8, t9) ← fsNext wordRate 0 cursor
    let word := t8
    cursor := t9
    let outLanes ← B.stackBuf KECCAK_LANES
    keccakSlotLanes outSlot (← val (point * packG)) outLanes 1 (KECCAK_SEGMENTS - 1)
    let mut lanesSum : FW := FW.c (lit 0)
    for lane in [0:KECCAK_LANES] do
      lanesSum ← fold (lanesSum + outLanes[lane] * firstLanes[GEN ^ lane])
    assert lanesSum * word == outValue
    let outPack : Shifted := ⟨outPoint, KECCAK_PACK_LOG⟩
    B.loopRtF 0 (pure packG) 2 (do return [(← B.shifted outPack.base outPack.exp).v, point.v]) fun xt caps => do
      let outPack : Shifted := Shifted.of caps[0]
      let point := caps[1]
      let t0 ← val point[xt]
      outPack[xt] := t0
    -- ---- the inputs: the instances of a pack first, then the slot ----
    let last : Shifted := ⟨claims, 264⟩
    let t10 ← callN (instName "keccak_plain_rounds" [.L KECCAK_PACK_LOG, .L 1]) [fs0, fs1, fs2, fs3, fs4, wordRate[0], wordRate[1], cursor, last[GEN ^ 0], inPoint, tabs] 7
    fs0 := t10[0]!
    fs1 := t10[1]!
    fs2 := t10[2]!
    fs3 := t10[3]!
    fs4 := t10[4]!
    cursor := Shifted.of t10[5]!
    let lowValue := t10[6]!
    let lowTree ← B.heapBuf 30
    eqtree inPoint lowTree KECCAK_PACK_LOG
    let mut muAtLow : FW := FW.c (lit 0)
    for i in [0:KECCAK_PACK] do
      muAtLow ← fold (muAtLow + lowTree[GEN ^ (2 ^ KECCAK_PACK_LOG - 2 + i)] * last[GEN ^ (KC_MU + i)])
    let inSlot ← val (inPoint * tauG)
    let t11 ← callN (instName "keccak_plain_rounds" [.L QKECCAK_SLOT_LOG, .L 0]) [fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, lowValue, inSlot, tabs] 7
    fs0 := t11[0]!
    fs1 := t11[1]!
    fs2 := t11[2]!
    fs3 := t11[3]!
    fs4 := t11[4]!
    cursor := Shifted.of t11[5]!
    let inValue := t11[6]!
    sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut rate ← B.stackBuf 8
    for z in [0:BASE_FIELD_BITS] do
      if z % 4 = 0 then
        if z ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
      let (t12, t13) ← fsNext rate (z % 4) cursor
      let w := t12
      cursor := t13
      slices[GEN ^ z] := w
    sp ← fsPerm sp rate 4
    let lastPoint ← val last[GEN ^ KC_POINT]
    let inLanes ← B.stackBuf KECCAK_LANES
    keccakSlotLanes inSlot (← val (lastPoint * packG)) inLanes 0 KECCAK_SEGMENTS
    -- shifts[r] = sum_z slices[z] eq(a, z + r), a the last layer's slice point:
    -- folded a bit at a time for every r at once.
    let lastLocal ← val last[GEN ^ KC_LOCAL]
    let mut level ← B.stackBuf 64
    for z in [0:BASE_FIELD_BITS] do
      level[z] := slices[GEN ^ z]
    for t in [0:KECCAK_Z_BITS] do
      let folded ← B.stackBuf 64
      foldShifts level folded (← val lastLocal[GEN ^ t]) t
      level := folded
    let shifts := level
    let lastLanes ← val last[GEN ^ KC_LANES]
    let t14 ← keccakForm lastLanes shifts inLanes 0
    assert muAtLow * t14 == inValue
    let inPack : Shifted := ⟨inPoint.base, inPoint.exp + KECCAK_PACK_LOG⟩
    B.loopRtF 0 (pure packG) 2 (do return [(← B.shifted inPack.base inPack.exp).v, lastPoint.v]) fun xt caps => do
      let inPack : Shifted := Shifted.of caps[0]
      let lastPoint := caps[1]
      let t0 ← val lastPoint[xt]
      inPack[xt] := t0
    let t15 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val cursor)
    return [.v sp[8].v, .v sp[9].v, .v sp[10].v, .v sp[11].v, .v sp[12].v, .into t15, .v word.v]

/-- out[r] = Psi(v) = sum_b g_b v^(2^b), the inner stage: 7 squarings and 8 products. -/
def ringPsi (out : List V) (r : Nat) (v : Word) (g : List V) : B Unit := B.inline "ring_psi" do
  let mut psi ← val (g[0] * v)
  let mut v := v
  for b in [1:RING_MAP_WIDTH - 1] do
    v ← val (v * v)
    psi ← val (psi + g[b] * v)
  v ← val (v * v)
  out[r] := psi + g[RING_MAP_WIDTH - 1] * v

/-- T = sum_i x^i Phi(s_i) = sum_p f_p (sum_i z_p^i Psi(s_i))^(2^(8p)), z_p = x^(2^(64 - 8p)) in K, so a slice takes Psi alone. The eight sums run Horner over the slices from the bottom, RS_CHUNK an iteration, in w_p = 1/z_p: they come out as sum_i w_p^(63 - i) Psi(s_i), and the final x^63 = (z_p^63)^(2^(8p)) restores them all. -/
def ringSwitchTarget : GFn where
  name := "ring_switch_target"
  arity := 2
  rets := 1
  body ps := do
    let slices := ps[0]
    let mapChallenges := ps[1]
    let rsChain ← B.heapBuf 72
    for p in [0:RING_MAP_WIDTH] do
      rsChain[GEN ^ p] := 0
    B.loopConstF 0 RS_CHUNK 3 (pure ([mapChallenges.v, slices.v, rsChain.v])) fun xRound caps => do
      let mapChallenges := caps[0]
      let slices := caps[1]
      let rsChain := caps[2]
      let g ← B.stackBuf RING_MAP_WIDTH  -- read once an iteration, not once a row
      for b in [0:RING_MAP_WIDTH] do
        g[b] := mapChallenges[GEN ^ (RING_MAP_WIDTH + b)]
      let rows ← val (slices * xRound ^ RS_CHUNK)
      let psi ← B.stackBuf RS_CHUNK
      for r in [0:RS_CHUNK] do
        ringPsi psi r (← val rows[GEN ^ r]) g
      let row ← val (rsChain * xRound ^ RING_MAP_WIDTH)
      for p in [0:RING_MAP_WIDTH] do
        let mut acc ← val row[GEN ^ p]
        for r in [0:RS_CHUNK] do
          acc ← val (acc * arrWord RING_W p + psi[r])
        row[GEN ^ (RING_MAP_WIDTH + p)] := acc
    let sums ← val (rsChain * (GEN ^ 8) ^ 8)
    let mut total ← val (mapChallenges[GEN ^ 0] * sums[GEN ^ 0])
    for p in [1:RING_MAP_WIDTH] do
      let mut h ← val sums[GEN ^ p]
      for _ in [0:RING_MAP_WIDTH * p] do
        h ← val (h * h)
      total ← val (total + mapChallenges[GEN ^ p] * h)
    return [Ex.ret (total * GEN ^ 63)]

/-- One ring-switched claim's transparent weight at the opening point. -/
def ringSwitchWeight : GFn where
  name := "ring_switch_weight"
  arity := 4
  rets := 1
  body ps := do
    let zVals := ps[0]
    let point1 := ps[1]
    let cTable := ps[2]
    let qkeccakvG := ps[3]
    let prodFinal ← call1 "rs_eq_run" [zVals, point1, qkeccakvG]
    let mut rsWeight : FW := FW.c (lit 0)
    for k in [0:BASE_FIELD_BITS] do
      rsWeight ← fold (rsWeight + cTable[GEN ^ k] * prodFinal[GEN ^ k])
    return [Ex.ret rsWeight]

/-- Certify the native order (descending kappa, then ascending column index) group by group: a column group, a run of columns sharing one kappa source, is consecutive in it, so a hinted order of the groups, certified strictly descending in its rank key, places every column. Returns g^(sum 2^kappa) and each column's g^offset. -/
def certifyPlacement : GFn where
  name := "certify_placement"
  arity := 2
  rets := 2
  body ps := do
    let kappaBase := ps[0]
    let gSquares := ps[1]
    let kb ← B.stackBuf 8
    for i in [0:N_TABLES + 2] do
      kb[i] := kappaBase[GEN ^ i]
    let rankKeys : Shifted := ⟨gSquares, RANK_KEYS_AT⟩
    let groupKey ← B.heapBuf N_COL_GROUPS
    let groupSize ← B.heapBuf N_COL_GROUPS
    let mut c0 : Nat := default
    for gi_k in [0:N_COL_GROUPS] do
      c0 := arrInt COL_GROUP_START gi_k
      let kappaG ← val (Ex.v kb[arrInt COL_KAPPA_SRC c0] * GEN ^ (arrInt COL_KAPPA_ADJ c0))
      -- g_squares spans SIZE_BITS, and every kappa is under it: a certified log <= 30 (log_mem or a tau), the baked bytecode log, or q_keccak's tau_5 + QKECCAK_SLOT_LOG.
      assert log kappaG < SIZE_BITS
      -- Descending kappa, then the group's first (compact, native-order) index ascending.
      groupKey[GEN ^ gi_k] := rankKeys[kappaG] * INV_GEN ^ c0
      groupSize[GEN ^ gi_k] := gSquares[kappaG] ^ (arrInt COL_GROUP_START (gi_k + 1) - c0)
    let groupOrder ← B.heapBuf N_COL_GROUPS
    B.witness "col_group_order" (.heap groupOrder.v 0 N_COL_GROUPS)
    let groupBase ← B.heapBuf N_COL_GROUPS
    let mut gTotal : FW := FW.c (gpowE 0)
    let mut gi : Word := default
    let mut prevKey : Word := default
    for rank in [0:N_COL_GROUPS] do
      gi ← val groupOrder[GEN ^ rank]
      assert log gi < N_COL_GROUPS
      let key ← val groupKey[gi]
      -- A negative step wraps around the order of GEN and cannot pass this check.
      if rank ≠ 0 then
        assert log (prevKey / key * INV_GEN) < RANK_KEY_BOUND
        pure ()
      let t0 ← val gTotal  -- write-once: a repeated group collides
      groupBase[gi] := t0
      gTotal ← fold (gTotal * groupSize[gi])
      prevKey := key
    let colOffG ← B.heapBuf N_COMMITTED_COLS
    for gi_k in [0:N_COL_GROUPS] do
      c0 := arrInt COL_GROUP_START gi_k
      let step ← val gSquares[GEN ^ (arrInt COL_KAPPA_ADJ c0) * kb[arrInt COL_KAPPA_SRC c0]]
      let mut off ← val groupBase[GEN ^ gi_k]
      for c_k in [c0:arrInt COL_GROUP_START (gi_k + 1)] do
        colOffG[GEN ^ c_k] := off
        if c_k + 1 ≠ arrInt COL_GROUP_START (gi_k + 1) then
          off ← val (off * step)
    return [Ex.ret gTotal, .v colOffG.v]

/-- The column's selector at the complete opening point, from hinted g-power digits of its offset's nibbles at and above kappa // 4, each range-checked below 16. Pinning their weighted product to the certified offset makes them its own nibbles (a base-16 representation is unique), and that offset is 2^kappa-aligned (certify_placement orders kappa descending), so the lowest digit, kappa's own nibble, is a multiple of 2^(4 - width): the strided level-width table holds it. Both offset and point are zero above m, so extending to 4 * SEL_NIBBLES adds only factors eq(0, 0) = 1. -/
def columnSelector (kappa : Nat) : GFn where
  name := instName "column_selector" [.L kappa]
  arity := 3
  rets := 1
  body ps := do
    let offset := ps[0]
    let selEq := ps[1]
    let selG := ps[2]
    let digits ← B.stackBuf SEL_NIBBLES
    B.hintDigitsExp (.stack digits[0:SEL_NIBBLES - kappa / 4]) offset (4 * SEL_NIBBLES) (SEL_NIBBLES - kappa / 4) 4 (4 * (kappa / 4))
    let mut selector : FW := default
    let mut rebuilt : FW := default
    if kappa / 4 = SEL_NIBBLES then
      selector := FW.c (gpowE 0)
      rebuilt := FW.c (gpowE 0)
    for j in [kappa / 4:SEL_NIBBLES] do
      let mut width := 4
      if j = kappa / 4 then
        width := 4 * j + 4 - kappa
      let d := digits[j - kappa / 4]
      assert log d < 16
      if j = kappa / 4 then
        selector ← fold selEq[GEN ^ (SEL_EQ_STRIDE * j + 16 * (width - 1)) * d]
        rebuilt ← fold selG[GEN ^ (16 * j) * d]
      else
        selector ← fold (selector * selEq[GEN ^ (SEL_EQ_STRIDE * j + 16 * (width - 1)) * d])
        rebuilt ← fold (rebuilt * selG[GEN ^ (16 * j) * d])
    assert rebuilt == offset
    return [Ex.ret selector]

/-- Per nibble j of the selector bits, the eq tables over its top 1..4 coordinates, the level-w one at 16 (w - 1), strided: entry u, a multiple of 2^(4 - w), holds the eq of bit t of u against coordinate 4j + t for t >= 4 - w. -/
def selectorTables : GFn where
  name := "selector_tables"
  arity := 2
  rets := 1
  body ps := do
    let point := ps[0]
    let point1 := ps[1]
    let selEq ← B.heapBuf 512
    let mut r : Word := default
    let mut r1 : Word := default
    let mut e : Nat := default
    for j in [0:SEL_NIBBLES] do
      let levels ← B.stackBuf 64
      levels[0] := point1[GEN ^ (4 * j + 3)]
      levels[8] := point[GEN ^ (4 * j + 3)]
      for w in [1:4] do
        r ← val point[GEN ^ (4 * j + 3 - w)]
        r1 ← val point1[GEN ^ (4 * j + 3 - w)]
        for i in [0:2 ^ w] do
          e := i * 2 ^ (4 - w)
          levels[16 * w + e] := levels[16 * (w - 1) + e] * r1
          levels[16 * w + e + 2 ^ (3 - w)] := levels[16 * (w - 1) + e] * r
      for w in [0:4] do
        for i in [0:2 ^ (w + 1)] do
          e := i * 2 ^ (3 - w)
          selEq[GEN ^ (SEL_EQ_STRIDE * j + 16 * w + e)] := levels[16 * w + e]
    return [.v selEq.v]

set_option maxHeartbeats 4000000 in
/-- Evaluate each transparent weight at the complete point in witness order. A claim is its low point followed by the certified column's selector bits; a q_keccak lane puts its slot's bits between the two. point1 = 1 + point holds each coordinate's eq factor against a zero bit. -/
def checkOpeningTerminal : GFn where
  name := "check_opening_terminal"
  arity := 20
  rets := 0
  body ps := do
    let gSquares := ps[0]
    let zeta := ps[1]
    let chi := ps[2]
    let rm := ps[3]
    let gBusMu := ps[4]
    let gZcN := ps[5]
    let gLogMem := ps[6]
    let tauKeccakG := ps[7]
    let kappaBase := ps[8]
    let lamCl := ps[9]
    let colOffsets := ps[10]
    let zVals := ps[11]
    let cTable := ps[12]
    let point := ps[13]
    let point1 := ps[14]
    let innerTotal := ps[15]
    let yrAtTail := ps[16]
    let sumcheckTarget := ps[17]
    let oodZ := ps[18]
    let gmv := ps[19]
    let zetaEqChain ← B.heapBuf 35
    call "eq_prefix_chain" [zetaEqChain, 1, zeta, point1, gBusMu]
    let chiEqChain ← B.heapBuf 35
    call "eq_prefix_chain" [chiEqChain, 1, chi, point1, gZcN]
    let slotPoint ← val (point * tauKeccakG)
    let slotPoint1 ← val (point1 * tauKeccakG)
    let piChain ← B.heapBuf 35
    piChain[GEN ^ 0] := 1
    piChain[GEN ^ 1] := rm + point1[GEN ^ 0]
    B.loopRtF 1 (pure gLogMem) 2 (pure ([piChain.v, point1.v])) fun xk caps => do
      let piChain := caps[0]
      let point1 := caps[1]
      let t0 ← val (piChain[xk] * point1[xk])
      piChain[GEN ^ 1 * xk] := t0
    let piEq ← val piChain[gLogMem]
    -- Every low dimension here is a certified log at a baked kappa source, as certify_placement derives the columns'.
    let kb ← B.stackBuf 8
    for i in [0:N_TABLES + 2] do
      kb[i] := kappaBase[GEN ^ i]
    let selEq ← call1 "selector_tables" [point, point1]
    let selG : Shifted := ⟨gSquares, SIZE_BITS⟩  -- exponent_tables' constant nibble shares
    let selectors ← B.stackBuf N_COMMITTED_COLS
    for c_k in [0:N_COMMITTED_COLS] do
      let offset ← val colOffsets[GEN ^ c_k]
      let kappaG ← val (Ex.v kb[arrInt COL_KAPPA_SRC c_k] * GEN ^ (arrInt COL_KAPPA_ADJ c_k))
      let t0 ← B.targets [some selectors[c_k].v]
      let t1 ← val selG
      B.dispatchInto kappaG ((List.range N_COLUMN_LOGS).map (fun arm => instName "column_selector" [.L arm])) [offset.v, selEq.v, t1.v] t0
    let mut innerSum := innerTotal
    let mut lamPow := lamCl  -- the pool's powers, as verify_sub batched it
    let mut col : Nat := default
    let mut cplenG : Word := default
    let mut nlowAdj : Nat := default
    let mut lowEq : Word := default
    let mut slotEq : FW := default
    let mut k : Nat := default
    let mut slotFactor : Word := default
    for j in [0:N_CLAIMS] do
      if arrInt CLAIM_POINT_BUF j ≠ POINT_BUF_KECCAK_OUT then
        col := arrInt CLAIM_COMMITTED_COL j
        cplenG ← val (Ex.v kb[arrInt CLAIM_KAPPA_SRC j] * GEN ^ (arrInt CLAIM_KAPPA_ADJ j))
        nlowAdj := arrInt CLAIM_KAPPA_ADJ j
        if arrInt CLAIM_POINT_BUF j = POINT_BUF_PI then
          lowEq := piEq
        if arrInt CLAIM_POINT_BUF j = POINT_BUF_ZETA then
          lowEq ← val zetaEqChain[cplenG]
        if arrInt CLAIM_POINT_BUF j = POINT_BUF_RHO then
          lowEq ← val chiEqChain[cplenG]
        if arrInt CLAIM_POINT_BUF j = POINT_BUF_QKECCAK_RHO then
          -- Top bit first, so claims sharing high slot bits share partial products.
          slotEq := FW.c (gpowE 0)
          for kk in [0:QKECCAK_SLOT_LOG] do
            k := QKECCAK_SLOT_LOG - 1 - kk
            if arrInt CLAIM_QKECCAK_SLOT_BITS (QKECCAK_SLOT_LOG * j + k) = 1 then
              slotFactor ← val slotPoint[GEN ^ k]
            else
              slotFactor ← val slotPoint1[GEN ^ k]
            if kk = 0 then
              slotEq := FW.w slotFactor
            else
              slotEq ← fold (slotEq * slotFactor)
          lowEq ← val (slotEq * chiEqChain[cplenG])
          nlowAdj := arrInt CLAIM_KAPPA_ADJ j + QKECCAK_SLOT_LOG
        -- The claim's low dimension is its column's kappa: by construction when the two share a kappa source, else checked.
        if arrInt CLAIM_KAPPA_SRC j ≠ arrInt COL_KAPPA_SRC col then
          assert Ex.v kb[arrInt CLAIM_KAPPA_SRC j] * GEN ^ nlowAdj == Ex.v kb[arrInt COL_KAPPA_SRC col] * GEN ^ (arrInt COL_KAPPA_ADJ col)
        else if nlowAdj ≠ arrInt COL_KAPPA_ADJ col then
          assert Ex.v kb[arrInt CLAIM_KAPPA_SRC j] * GEN ^ nlowAdj == Ex.v kb[arrInt COL_KAPPA_SRC col] * GEN ^ (arrInt COL_KAPPA_ADJ col)
        innerSum ← val (innerSum + lamPow * lowEq * selectors[col])
        lamPow ← val (lamPow * lamCl)
    let lamOut := lamPow
    -- The Keccak reduction's two claims on q_keccak, each over the whole column:
    -- the ring-switched one leads the batch at lam_cl^0, the plain one closes it. A lane claim's low point is tau_keccak long, the kappa check above holding it to this column.
    let qkeccakvG : Shifted := ⟨tauKeccakG, QKECCAK_SLOT_LOG⟩
    if arrInt COL_KAPPA_SRC QKECCAK_COMMITTED_COL ≠ TABLE_KECCAK + 2 then
      assert qkeccakvG == Ex.v kb[arrInt COL_KAPPA_SRC QKECCAK_COMMITTED_COL] * GEN ^ (arrInt COL_KAPPA_ADJ QKECCAK_COMMITTED_COL)
    else if arrInt COL_KAPPA_ADJ QKECCAK_COMMITTED_COL ≠ QKECCAK_SLOT_LOG then
      assert qkeccakvG == Ex.v kb[arrInt COL_KAPPA_SRC QKECCAK_COMMITTED_COL] * GEN ^ (arrInt COL_KAPPA_ADJ QKECCAK_COMMITTED_COL)
    let outEqChain ← B.heapBuf 41
    call "eq_prefix_chain" [outEqChain, 1, zVals, point1, qkeccakvG]
    let rsWeight ← call1 "ring_switch_weight" [zVals * GEN ^ QKECCAK_VARS_CAP, point1, cTable, qkeccakvG]
    innerSum ← val (innerSum + (rsWeight + lamOut * outEqChain[GEN ^ qkeccakvG.exp * qkeccakvG.base]) * selectors[QKECCAK_COMMITTED_COL])
    -- The OOD sample's claim, after the output word's: eq(z, .) over the stack's m variables.
    let oodChain ← B.heapBuf 31
    call "eq_prefix_chain" [oodChain, lamOut * lamCl, oodZ, point1, gmv]
    assert (innerSum + oodChain[gmv]) * yrAtTail == sumcheckTarget
    return []

/-- The bus's grind at a push depth of BUS_MIN_MU + d. -/
def busGrindCheck (d : Nat) : GFn where
  name := instName "bus_grind_check" [.L d]
  arity := 2
  rets := 1
  body ps := do
    let word := ps[0]
    let tabs := ps[1]
    call (instName "grind_check" [.L (arrInt BUS_GRIND_BITS (BUS_MIN_MU + d))]) [word, tabs]
    return [.c 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- In-circuit verification of ONE inner proof for the statement (pi_0, pi_1), mirroring `crates/verifier` step for step; the `# ---- ... ----` headers below run in that order. All proof data is hinted HERE, so each call pops the next sub-proof's entry of every witness stream and the body lowers once. The exponent tables are shared read-only; the deferred claim goes to `defer_out`.

The pool holds every committed-coordinate claim's value in decompose order (the points are the GKR zetas, resolvable from the baked block structure) and its certified low dimension, which the terminal pins its lengths against.
-/
def verifySub : GFn where
  name := "verify_sub"
  arity := 6
  rets := 0
  body ps := do
    let pi0 := ps[0]
    let pi1 := ps[1]
    let seed0 := ps[2]
    let seed1 := ps[3]
    let gSquares := ps[4]
    let deferOut := ps[5]
    let claimPool ← B.heapBuf N_CLAIMS
    let tabs : Shifted := ⟨gSquares, WIN_TAB_AT⟩
    -- ---- seed (statement pre-bound: hinted sub pi + baked program digest) ---- The sponge's first permutation takes the program digest and the statement as its rate, from the zero state.
    let mut sp ← B.stackBuf KECCAK_STATE
    B.keccakCells (cells := .words [.cell seed0.v, .cell seed1.v, .cell pi0.v, .cell pi1.v]) (final := false) (out := .frame sp)
    let stream ← B.heapBuf STREAM_CAP
    B.witness "stream" (.heap stream.v 0 STREAM_CAP)
    let mut cursor : Shifted := Shifted.of stream  -- the proof stream, replayed word by word (advance = * g)
    -- ---- announced layout and PCS rate (observed, then certified) ---- The stream announces the memory's log size and each table's row count as integer WORDS; the shape-generic phases need logs as G-POWERS (loop bounds, match scrutinees). log_mem is reassembled from its advice-decomposed bits, with no hint and no g^j -> j lookup. A table's log height is advice, which verify_tables certifies to be the least holding its rows, above its floor.
    let tableRows ← B.heapBuf N_TABLES
    let mut rate ← B.stackBuf 8
    let mut x : Word := default
    let mut logMemWord : Word := default
    for i in [0:N_TABLES + 1] do
      if i % 4 = 0 then
        if i ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
      let (t0, t1) ← fsNext rate (i % 4) cursor
      x := t0
      cursor := t1
      if i = 0 then
        logMemWord := x
      else
        tableRows[GEN ^ (i - 1)] := x
    if (N_TABLES + 1) % 4 = 0 then
      sp ← fsPerm sp rate 4
      rate ← B.stackBuf 8
    let (t2, t3) ← fsNext rate ((N_TABLES + 1) % 4) cursor
    let logInvRate := t2
    cursor := t3
    let rateSel ← val (call1 "g_power_of_word" [logInvRate] / GEN)
    assert log rateSel < LIG_N_RATES
    let dimsG ← B.heapBuf 7  -- [g^log_mem, g^tau_0 .. g^tau_{N_TABLES-1}]
    let gLogMem ← call1 "g_power_of_word" [logMemWord]
    assert log gLogMem < 31  -- native log_mem <= MAX_LOG_MEM
    assert log (gLogMem / GEN ^ MIN_LOG_MEM) < COUNT_BITS  -- native MIN_LOG_MEM <= log_mem
    dimsG[GEN ^ 0] := gLogMem
    B.witness "table_logs" (.heap dimsG.v 1 (1 + N_TABLES - 1))  -- certified in verify_tables
    -- kappa_base maps a kappa source index to its certified log (source 0 = const via the baked adj). Each block's kappa then DERIVES from its structural source as a compile-time offset off a certified log: no hint, and nothing left free.
    let kappaBase ← B.heapBuf 8
    let kb ← B.stackBuf 8  -- the same, in the frame
    kb[0] := 1
    kb[1] := gLogMem
    for t in [0:N_TABLES] do
      kb[2 + t] := dimsG[GEN ^ (t + 1)]
    for i in [0:N_TABLES + 2] do
      kappaBase[GEN ^ i] := kb[i]
    -- The ONE bus depth, COMPUTED (not hinted): mu = log2_ceil(Σ_b 2^κ_b) over PUSH's blocks; pull matches by pairing, the count tree is padded to it.
    let mut pushTotal : FW := FW.c (gpowE 0)
    for b in [arrInt SIDE_BLOCK_START PUSH_SIDE:arrInt SIDE_BLOCK_START (PUSH_SIDE + 1)] do
      pushTotal ← fold (pushTotal * gSquares[GEN ^ (arrInt BLOCK_KAPPA_ADJ b) * kb[arrInt BLOCK_KAPPA_SRC b]])  -- g^(sum of 2^kappa)
    let gBusMu ← call1 (instName "log2_ceil_in_the_exponent" [.L 0, .L SIZE_BITS]) [pushTotal, gSquares]
    let zeta ← B.heapBufDyn gBusMu  -- the ONE shared GKR point: exactly mu coords
    -- ---- commitment root (2 words), kept for the opening phase ---- The announcement's N_TABLES + 2 words, then the root's two, wait as one run.
    if (N_TABLES + 2) % 4 = 0 then
      sp ← fsPerm sp rate 4
      rate ← B.stackBuf 8
    let (t5, t6) ← fsNext rate ((N_TABLES + 2) % 4) cursor
    let commitRoot0 := t5
    cursor := t6
    if (N_TABLES + 3) % 4 = 0 then
      sp ← fsPerm sp rate 4
      rate ← B.stackBuf 8
    let (t7, t8) ← fsNext rate ((N_TABLES + 3) % 4) cursor
    let commitRoot1 := t7
    cursor := t8
    -- ---- the committed size: placement, then g^m, m = max(log2_ceil(sum_cols 2^kappa), PCS_MIN_MU) ---- g_total is g^(sum 2^kappa) from the certified placement walk.
    let t9 ← callN "certify_placement" [kappaBase, gSquares] 2
    let gTotal := t9[0]!
    let colOffsets := t9[1]!
    let gmv ← call1 (instName "log2_ceil_in_the_exponent" [.L PCS_MIN_MU, .L SIZE_BITS]) [gTotal, gSquares]  -- g^m
    let sizeSel ← val (gmv * LIG_MIN_SHIFT_INV)  -- g^(m - MIN)
    assert log sizeSel < LIG_N_LOG_SIZES
    -- ---- the level-0 OOD sample (verifier read_ood) ---- A grind, then z of the stack's m variables, the first drawn by the grind's permutation, then the stack's value at z.
    let (t10, t11, t12) ← fsGrindSqueeze sp rate ((N_TABLES + 3) % 4 + 1) cursor tabs OOD_GRIND_BITS
    sp := t10
    let zFirst := t11
    cursor := t12
    let oodZ ← B.heapBuf MAX_STACK_LOG
    let t13 ← B.targets [none, none, none, none, none]
    B.dispatchInto sizeSel ((List.range 11).map (fun arm => instName "squeeze_point_from" [.L (LIG_MIN_LOG_SIZE + arm)])) [sp[8].v, sp[9].v, sp[10].v, sp[11].v, sp[12].v, zFirst.v, oodZ.v] t13
    let fs0 := t13[0]
    let fs1 := t13[1]
    let fs2 := t13[2]
    let fs3 := t13[3]
    let fs4 := t13[4]
    let oodValue ← B.heapBuf 1
    -- The bus's grind nonce joins the value: its permutation draws the first weight.
    let t14 ← callN (instName "opening_message" [.L 1, .L 1]) [fs0, fs1, fs2, fs3, fs4, cursor, oodValue] 8
    let word0 := t14[0]!
    let powWord := t14[1]!
    let fs0 := t14[2]!
    let fs1 := t14[3]!
    let fs2 := t14[4]!
    let fs3 := t14[5]!
    let fs4 := t14[6]!
    cursor := Shifted.of t14[7]!
    -- ---- bus challenges ---- They fail with probability at most 2^mu / |E| (verifier::bus), so a grind of BUS_GRIND_BITS[mu] comes first, mu the push side's depth: at least BUS_MIN_MU, its least over executions of this bytecode. A tuple is fingerprinted linearly: slot x weighs its own challenge fp_w[x] (doc sec:gp).
    let busGrind ← val (gBusMu * INV_GEN ^ BUS_MIN_MU)
    assert log busGrind < BUS_GRIND_ARMS
    let t15 ← B.targets [none]  -- a match needs a target
    let t16 ← val tabs
    B.dispatchInto busGrind ((List.range BUS_GRIND_ARMS).map (fun arm => instName "bus_grind_check" [.L arm])) [powWord.v, t16.v] t15
    let done := t15[0]
    sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let noRate ← B.stackBuf 8
    let fpW ← B.heapBuf N_TUPLE_SLOTS
    fpW[GEN ^ 0] := word0
    for x_k in [1:N_TUPLE_SLOTS] do
      let (t17, t18) ← squeeze sp noRate 0
      sp := t17
      let wx := t18
      fpW[GEN ^ x_k] := wx
    let (t19, t20) ← squeeze sp noRate 0
    sp := t19
    let beta := t20
    -- ---- ONE GKR grand product: every tree batched ----
    let t21 ← callN "verify_bus_gkr" [sp[8], sp[9], sp[10], sp[11], sp[12], cursor, gBusMu, zeta, tabs] 7
    let fs0 := t21[0]!
    let fs1 := t21[1]!
    let fs2 := t21[2]!
    let fs3 := t21[3]!
    let fs4 := t21[4]!
    cursor := Shifted.of t21[5]!
    let gkrLeaves := t21[6]!
    -- ---- the bus leaves, the table sumcheck, and the public-input claim ----
    let chi ← B.heapBuf SIZE_BITS  -- chi[i] = the challenge that bound variable i
    let bcPoint ← B.heapBuf N_TUPLE_BITS
    let t22 ← callN "verify_tables" [fs0, fs1, fs2, fs3, fs4, cursor, pi0, pi1, zeta, gBusMu, dimsG, tableRows, gSquares, fpW, beta, claimPool, chi, gkrLeaves, tabs, bcPoint] 10
    let fs0 := t22[0]!
    let fs1 := t22[1]!
    let fs2 := t22[2]!
    let fs3 := t22[3]!
    let fs4 := t22[4]!
    cursor := Shifted.of t22[5]!
    let gZcN := t22[6]!
    let bcValue := t22[7]!
    let rm := t22[8]!
    let colEvalWords := t22[9]!
    -- ---- KECCAK validity, by GKR over the rounds ----
    let tauKeccakG ← val dimsG[GEN ^ 6]  -- the KECCAK table's certified tau
    let zVals ← B.heapBuf 78
    let slices ← B.heapBuf BASE_FIELD_BITS
    let t23 ← callN "verify_keccak" [fs0, fs1, fs2, fs3, fs4, cursor, tauKeccakG, chi, colEvalWords * GEN ^ 101, zVals, slices, tabs] 7
    let fs0 := t23[0]!
    let fs1 := t23[1]!
    let fs2 := t23[2]!
    let fs3 := t23[3]!
    let fs4 := t23[4]!
    cursor := Shifted.of t23[5]!
    let keccakWord := t23[6]!
    sp ← fsCap fs0 fs1 fs2 fs3 fs4
    -- ---- stacked mixed opening: ring-switch front + claim combination ---- The input opening's slices were read and bound above; this block only binds them to the commitment. Phi(v) = sum_p f_p Psi(v)^(2^(8p)), Psi(v) = sum_b g_b v^(2^b):
    -- its expansion has all 64 Frobenius terms soundness needs. One grind covers the map's challenges and the batching challenge lam_cl, drawn next: one verifier message.
    rate ← B.stackBuf 8
    let ch ← B.stackBuf 16  -- f_0 .. f_7, then g_0 .. g_7
    let (t24, t25, t26) ← fsGrindSqueeze sp rate 0 cursor tabs BATCH_GRIND_BITS
    sp := t24
    let mapFirst := t25
    cursor := t26
    ch[0] := mapFirst
    for i in [1:2 * RING_MAP_WIDTH] do
      let (t27, t28) ← squeeze sp rate 0
      sp := t27
      let mapChallenge := t28
      ch[i] := mapChallenge
    let mapChallenges ← B.heapBuf 16
    for i in [0:2 * RING_MAP_WIDTH] do
      mapChallenges[GEN ^ i] := ch[i]
    -- The same map as a Frobenius sum, for the transparent weight: c_(8p+b) = f_p g_b^(2^(8p)).
    let cTable ← B.heapBuf BASE_FIELD_BITS
    for b in [0:RING_MAP_WIDTH] do
      let mut power := ch[RING_MAP_WIDTH + b]
      for p in [0:RING_MAP_WIDTH] do
        cTable[GEN ^ (RING_MAP_WIDTH * p + b)] := ch[p] * power
        if p + 1 ≠ RING_MAP_WIDTH then
          for _ in [0:RING_MAP_WIDTH] do
            power ← val (power * power)
    let targetIn ← call1 "ring_switch_target" [slices, mapChallenges]
    -- ONE batching challenge for the whole pool: N_CLAIMS - 1 fewer Fiat-Shamir hashes than a challenge per claim, and none for the values themselves, `fs_next` having bound every one it read and the public-input ones deriving from the seeded statement and rm, so `lam_cl` already depends on all of them. Disjoint power ranges, as for the zc_xi-powers above:
    -- the ring-switch claim takes lam_cl^0, the pool lam_cl^1 onward (bar the output lanes' claims, which the Keccak reduction consumed), and the Keccak reduction's claim on its committed outputs the power after the pool's last.
    let (t29, t30) ← squeeze sp rate 0
    sp := t29
    let lamCl := t30
    let mut target := targetIn
    let mut lamPow := lamCl
    for j in [0:N_CLAIMS] do
      if arrInt CLAIM_POINT_BUF j ≠ POINT_BUF_KECCAK_OUT then
        if j / N_BUS_CLAIMS = 0 then
          target ← val (target + lamPow * claimPool[GEN ^ j])
        else if (j - N_BUS_CLAIMS) / N_COL_EVALS = 0 then
          target ← val (target + lamPow * colEvalWords[GEN ^ (j - N_BUS_CLAIMS)])
        else
          target ← val (target + lamPow * claimPool[GEN ^ j])
        lamPow ← val (lamPow * lamCl)
    target ← val (target + lamPow * keccakWord)
    -- The OOD sample's claim closes the batch.
    target ← val (target + lamPow * lamCl * oodValue[GEN ^ 0])
    -- One arm per size, the rate passed on. Both are transcript-bound and range-checked above, so a single compiled guest dispatches independently for every inner proof in a mixed-rate batch.
    let t31 ← B.targets [none, none, none, none, none]
    let t32 ← val cursor
    let t33 ← val tabs
    B.dispatchInto sizeSel ((List.range 11).map (fun arm => instName "open_stacked" [.L arm])) [rateSel.v, sp[8].v, sp[9].v, sp[10].v, sp[11].v, sp[12].v, target.v, commitRoot0.v, commitRoot1.v, t32.v, t33.v] t31
    let sumcheckTarget := t31[0]
    let point := t31[1]
    let point1 := t31[2]
    let innerTotal := t31[3]
    let yrAtTail := t31[4]
    -- `stream` is a fixed-capacity witness transport. The shape fixes the exact consumed prefix, whose every word is transcript-bound; the unused suffix is outside the recursively verified proof and intentionally unconstrained. ---- generalized eval_b terminal (runtime claim shapes) ----
    call "check_opening_terminal" [gSquares, zeta, chi, rm, gBusMu, gZcN, gLogMem, tauKeccakG, kappaBase, lamCl, colOffsets, zVals, cTable, point, point1, innerTotal, yrAtTail, sumcheckTarget, oodZ, gmv]
    -- ---- export this sub-proof's deferred-claim data to the caller (FRESH_*) ----
    for k in [0:BYTECODE_LOG] do
      deferOut[GEN ^ k] := zeta[GEN ^ k]
    for k in [0:LOG2_BYTECODE_COLS] do
      deferOut[GEN ^ (BYTECODE_LOG + k)] := bcPoint[GEN ^ k]
    deferOut[GEN ^ FRESH_BC_VALUE] := bcValue
    return []

end
end LeanVM.Guest.Program
