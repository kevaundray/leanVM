/-
  LeanVM.Guest.Program.StackedWhirOpening

  The guest's section "the stacked WHIR opening".
-/

module

public import LeanVM.Guest.Program.MerklePaths

/-!
# The stacked WHIR opening

A level's rounds fold its lanes by the affine combiner G + (alpha + beta X) F of [CWYZ26], the claim carried by four scalars a round and the weight folded at alpha, so the alphas are the weight's point (verifier::whir::verify_whir). A non-final level then commits the folded lane's low part, sends its high part, and glues its OOD claim and its queries, each opened row folded as the lanes were and corrected by the high part. The final level sends the whole folded lane, checks the queries against it, and closes with a sumcheck over the low part.
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- One fold round: the four scalars [u0, w, c0, c1], grind, then alpha, beta. The row folds read alpha, beta at coefs[0..2]; alpha is also the point's coordinate. -/
def openingRound : GFn where
  name := "opening_round"
  arity := 10
  rets := 7
  body ps := do
    let fs0 := ps[0]
    let fs1 := ps[1]
    let fs2 := ps[2]
    let fs3 := ps[3]
    let fs4 := ps[4]
    let cursor : Shifted := Shifted.of ps[5]
    let claim := ps[6]
    let tabs := ps[7]
    let alphas := ps[8]
    let coefs := ps[9]
    let sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let msg ← B.stackBuf 8
    let (u0, cursor) ← fsNext msg 0 cursor
    let (w, cursor) ← fsNext msg 1 cursor
    let (c0, cursor) ← fsNext msg 2 cursor
    let (c1, cursor) ← fsNext msg 3 cursor
    let (sp, alpha, cursor) ← fsGrindSqueeze sp msg 4 cursor (Shifted.of tabs) FOLD_GRIND_BITS
    let rate ← B.stackBuf 8
    let (sp, beta) ← squeeze sp rate 0
    alphas[GEN ^ 0] := alpha
    coefs[GEN ^ 0] := alpha
    coefs[GEN ^ 1] := beta
    -- u0 + alpha (u0 + claim) + alpha^2 w + beta c0 + alpha beta (c0 + c1)
    let out ← val (u0 + beta * c0 + alpha * (u0 + claim + alpha * w + beta * (c0 + c1)))
    let t13 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val cursor)
    return [.v sp[8].v, .v sp[9].v, .v sp[10].v, .v sp[11].v, .v sp[12].v, .into t13, .v out.v]

/-- n stream words into out, then, with `nonce`, a grinding nonce, then the permutation the next challenge comes from. Returns that output's first cell (the challenge), its second (where the proof of work is), its capacity and the cursor. -/
def openingMessage (n : Nat) (nonce : Nat) : GFn where
  name := instName "opening_message" [.L n, .L nonce]
  arity := 7
  rets := 8
  body ps := do
    let fs0 := ps[0]
    let fs1 := ps[1]
    let fs2 := ps[2]
    let fs3 := ps[3]
    let fs4 := ps[4]
    let mut cursor : Shifted := Shifted.of ps[5]
    let out := ps[6]
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut rate ← B.stackBuf 8
    for pos in [0:n] do
      if pos % 4 = 0 then
        if pos ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
      let (t0, t1) ← fsNext rate (pos % 4) cursor
      let value := t0
      cursor := t1
      out[GEN ^ pos] := value
    if nonce = 1 then
      if n % 4 = 0 then
        if n ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
      sp ← fsAbsorbNonce sp rate (n % 4) (← val cursor[GEN ^ 0])
      cursor := ⟨cursor.base, cursor.exp + 1⟩
    else if n = 0 then
      sp ← fsPerm sp rate 0
    else
      sp ← fsPerm sp rate ((n + 3) % 4 + 1)
    let t2 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val cursor)
    return [.v sp[0].v, .v sp[1].v, .v sp[8].v, .v sp[9].v, .v sp[10].v, .v sp[11].v, .v sp[12].v, .into t2]

/-- n challenges whose first, `first`, a permutation already drew, the sponge its capacity: the other n - 1 are fresh squeezes. -/
def squeezePointFrom (n : Nat) : GFn where
  name := instName "squeeze_point_from" [.L n]
  arity := 7
  rets := 5
  body ps := do
    let fs0 := ps[0]
    let fs1 := ps[1]
    let fs2 := ps[2]
    let fs3 := ps[3]
    let fs4 := ps[4]
    let first := ps[5]
    let point := ps[6]
    point[GEN ^ 0] := first
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut out : List V := default
    if n / 2 = 0 then
      out := sp
    else
      let noRate ← B.stackBuf 8
      for x in [1:n] do
        let (t0, t1) ← squeeze sp noRate 0
        sp := t0
        let r := t1
        point[GEN ^ x] := r
      let t2 ← B.stackBuf 5
      t2[0] := sp[8]
      t2[1] := sp[9]
      t2[2] := sp[10]
      t2[3] := sp[11]
      t2[4] := sp[12]
      out := t2
    return [.v out[0].v, .v out[1].v, .v out[2].v, .v out[3].v, .v out[4].v]

/-- One round of the closing sumcheck: h(0) + h(1) == claim fixes h's linear coefficient, so c0 and c2 are sent and h(r) = c0 + r (claim + (1 + r) c2). Then the round's grind. -/
def openingTailRound : GFn where
  name := "opening_tail_round"
  arity := 8
  rets := 8
  body ps := do
    let fs0 := ps[0]
    let fs1 := ps[1]
    let fs2 := ps[2]
    let fs3 := ps[3]
    let fs4 := ps[4]
    let cursor : Shifted := Shifted.of ps[5]
    let claim := ps[6]
    let tabs := ps[7]
    let sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let rate ← B.stackBuf 8
    let (c0, cursor) ← fsNext rate 0 cursor
    let (c2, cursor) ← fsNext rate 1 cursor
    let (sp, r, cursor) ← fsGrindSqueeze sp rate 2 cursor (Shifted.of tabs) ROUND2_GRIND_BITS
    let t7 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val cursor)
    return [.v sp[8].v, .v sp[9].v, .v sp[10].v, .v sp[11].v, .v sp[12].v, .into t7, Ex.ret (c0 + r * (claim + (1 + r) * c2)), .v r.v]

/-- Levels lvl0..lvl0+width of a Merkle path, whose order bits are k's: each hashes the running node with the sibling on the other side of its hinted pair, which binds the link. -/
def walkWindow (n0 : Word) (n1 : Word) (path : List V) (lvl0 : Nat) (width : Nat) (k : Nat) (dsts : List V) : B Unit := B.inline "walk_window" do
  let mut n0 := n0
  let mut n1 := n1
  for r in [0:width] do
    let lvl := lvl0 + r
    let nxt ← B.stackBuf 2
    if k / 2 ^ r % 2 = 0 then
      B.keccak [n0, n1] path[4 * lvl + 2:4 * lvl + 4] nxt
    else
      B.keccak path[4 * lvl:4 * lvl + 2] [n0, n1] nxt
    n0 := nxt[0]
    n1 := nxt[1]
  dsts[0] := n0
  dsts[1] := n1

/-- The path, a window of QW levels a dispatch (`decode_query_windows`): each arm knows its levels' order bits, so it hashes the running node against the sibling its hinted pair holds. -/
def walkPath (pathDepth : Nat) (capDepth : Nat) : GFn where
  name := instName "walk_path" [.L pathDepth, .L capDepth]
  arity := 5
  rets := 0
  body ps := do
    let mut n0 := ps[0]
    let mut n1 := ps[1]
    let wins := ps[2]
    let cap := ps[3]
    let flags := ps[4]
    let path ← B.stackBuf LIG_PATH_CAP
    B.witness "merkle_children" (.stack path[0:4 * pathDepth])
    for i in [0:(pathDepth + QW - 1) / QW] do
      let mut width : Nat := default
      if QW * i + QW = QW * ((pathDepth + QW - 1) / QW) then
        width := pathDepth - QW * i
      else
        width := QW
      let w ← val wins[GEN ^ i]
      if width = 6 then
        let t0 ← B.targets [none, none]
        Keccak.inlineArms
        let _ ← B.matchArms w ((List.range 64).map fun arm => do
          walkWindow n0 n1 path (6 * i) 6 arm [t0[0].v, t0[1].v])
        n0 := t0[0]
        n1 := t0[1]
      else if width = 5 then
        let t0 ← B.targets [none, none]
        Keccak.inlineArms
        let _ ← B.matchArms w ((List.range 32).map fun arm => do
          walkWindow n0 n1 path (QW * i) 5 arm [t0[0].v, t0[1].v])
        n0 := t0[0]
        n1 := t0[1]
      else if width = 4 then
        let t0 ← B.targets [none, none]
        Keccak.inlineArms
        let _ ← B.matchArms w ((List.range 16).map fun arm => do
          walkWindow n0 n1 path (QW * i) 4 arm [t0[0].v, t0[1].v])
        n0 := t0[0]
        n1 := t0[1]
      else if width = 3 then
        let t0 ← B.targets [none, none]
        Keccak.inlineArms
        let _ ← B.matchArms w ((List.range 8).map fun arm => do
          walkWindow n0 n1 path (QW * i) 3 arm [t0[0].v, t0[1].v])
        n0 := t0[0]
        n1 := t0[1]
      else if width = 2 then
        let t0 ← B.targets [none, none]
        Keccak.inlineArms
        let _ ← B.matchArms w ((List.range 4).map fun arm => do
          walkWindow n0 n1 path (QW * i) 2 arm [t0[0].v, t0[1].v])
        n0 := t0[0]
        n1 := t0[1]
      else
        let t0 ← B.targets [none, none]
        Keccak.inlineArms
        let _ ← B.matchArms w ((List.range 2).map fun arm => do
          walkWindow n0 n1 path (QW * i) 1 arm [t0[0].v, t0[1].v])
        n0 := t0[0]
        n1 := t0[1]
    -- The reached cap leaf is node 2*parent + bit at cells 2*node, 2*node + 1, where parent = 2^(cap_depth-1) + q: the child bit and q are the last two windows, g^bit and g^q, the constant parts folded into the address immediates. Every cap is at least two levels deep (`decode_query_windows` gives q cap_depth - 1 bits).
    let wb ← val wins[GEN ^ ((pathDepth + QW - 1) / QW)]
    let q ← val wins[GEN ^ ((pathDepth + QW - 1) / QW + 1)]
    let flagsQ ← val (flags * q)
    flagsQ[GEN ^ (2 ^ (capDepth - 1))] := 1  -- the cap check propagates this obligation to the root
    let q2 ← val (q * q)
    let leaf ← val (cap * q2 * q2 * (wb * wb))
    leaf[GEN ^ (2 ^ (capDepth + 1))] := n0
    leaf[GEN ^ (2 ^ (capDepth + 1) + 1)] := n1
    return []

/-- sum_(c < n) coefs[c] prod_(i: c_i = 1) ws[i], the novel basis at a point whose What_i normalizers the coefficients already carry: folded the lowest bit first, out[m] = in[2m] + ws[i] in[2m + 1], level i of `buf` at 2^(nbits+1) - 2^(nbits+1-i). -/
def novelEval (coefs : Word) (ws : List V) (n : Nat) (nbits : Nat) : B Word := B.inline "novel_eval" do
  let mut buf : List V := default
  if nbits / 4 = 0 then
    buf ← B.stackBuf 16
  else if nbits = 4 then
    buf ← B.stackBuf 32
  else if nbits = 5 then
    buf ← B.stackBuf 64
  else
    buf ← B.stackBuf 128
  let mut out : Word := default
  if nbits = 0 then
    out ← val coefs[GEN ^ 0]
  else
    let mut lo : Word := default
    let mut hi : Word := default
    let mut src : Nat := default
    for i in [0:nbits] do
      let nIn := (n + 2 ^ i - 1) / 2 ^ i
      let at' := 2 ^ (nbits + 1) - 2 ^ (nbits + 1 - i)
      for m in [0:(nIn + 1) / 2] do
        if i = 0 then
          lo ← val coefs[GEN ^ (2 * m)]
          if (2 * m + 1) / nIn = 0 then
            hi ← val coefs[GEN ^ (2 * m + 1)]
        else
          src := 2 ^ (nbits + 1) - 2 ^ (nbits + 2 - i)
          lo := buf[src + 2 * m]
          if (2 * m + 1) / nIn = 0 then
            hi := buf[src + 2 * m + 1]
        if (2 * m + 1) / nIn = 0 then
          buf[at' + m] := lo + ws[i] * hi
        else
          buf[at' + m] := lo
    out := buf[2 ^ (nbits + 1) - 4]
  return out

/-- One query: hash the hinted row up its Merkle path into the shared cap, then fold it at its point x round by round as the prover folded the lanes. A row is one hinted word a lane: a K lane at level 0, whose leaf image lists the lanes from the top down, an E word deeper, which is already the leaf's cell. At a non-final level the fold is returned (its high part's share is taken out in open_stacked's residual pass); at the final level it must be P_final(x). -/
def openingQuery (cap : Word) (flags : Word) (coefs : Word) (hs : Word) (x : Word) (wins : Word) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : B FW := B.inline "opening_query" do
  let interleave := 2 ^ folds
  let mut row : List V := default
  let mut acc : List V := default
  if folds / 5 = 0 then
    row ← B.stackBuf 16
    acc ← B.stackBuf 16
  else
    row ← B.stackBuf LIG_ROW_CAP
    acc ← B.stackBuf LIG_ROW_CAP
  B.witness "merkle_leaf_rows" (.stack row[0:interleave])
  let leafHashState ← B.stackBuf 2
  if base = 1 then
    -- Packing proves each hinted lane is in K before hashing or folding it.
    let packedRow ← B.stackBuf LIG_PACKED_ROW_CAP
    for jb in [0:interleave / 2] do
      pack64x2 row[2 * jb] row[2 * jb + 1] [packedRow[jb].v]
    B.keccakCells packedRow[0:leafCells] leafHashState
  else
    B.keccakCells row[0:leafCells] leafHashState
  call (instName "walk_path" [.L (depth - capDepth), .L capDepth]) [leafHashState[0], leafHashState[1], wins, cap, flags]
  -- Round j takes the lane pairs (F, G) to G + t F, t = alpha + beta x.
  let mut src : Nat := default
  for j in [0:folds] do
    let t ← val (coefs[GEN ^ (2 * j)] + coefs[GEN ^ (2 * j + 1)] * x)
    let nOut := 2 ^ (folds - 1 - j)
    for m in [0:nOut] do
      if j = 0 then
        if base = 1 then
          acc[m] := row[interleave - 2 - 2 * m] + t * row[interleave - 1 - 2 * m]
        else
          acc[m] := row[2 * m + 1] + t * row[2 * m]
      else
        src := interleave - 4 * nOut
        acc[interleave - 2 * nOut + m] := acc[src + 2 * m + 1] + t * acc[src + 2 * m]
  let value := acc[interleave - 2]
  let mut out : FW := default
  if final = 1 then
    -- The unnormalized W_i(x) for i <= mu, W_(i+1) = W_i (W_i + W_i(beta_i)).
    let ws ← B.stackBuf 6
    ws[0] := x
    for i in [1:mu + 1] do
      ws[i] := ws[i - 1] * (ws[i - 1] + arrWord VANISH_BY_COLS (vanish + i - 1))
    let t0 ← novelEval hs ws nHs hsBits
    assert value == t0
    out := FW.c (lit 0)
  else
    out := FW.w value
  return out

/-- Specialize by row and path shape so opening configurations share query code. Base-field rows (level 0) run two queries an iteration, sharing the loop overhead and the challenge reads; an odd count runs its first query alone, ahead of the pairs. Extension rows run one query an iteration. Query k is weighted lam^k: the chain runs h <- (h + v_k) / lam, ending at sum_k lam^(k - n) v_k, which the caller scales by lam^n. The final level's queries are checks, with nothing to sum. -/
def openingQueries (odd : Nat) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : GFn where
  name := instName "opening_queries" [.L odd, .L base, .L folds, .L leafCells, .L depth, .L capDepth, .L mu, .L vanish, .L nHs, .L hsBits, .L final]
  arity := 8
  rets := 1
  body ps := do
    let cap := ps[0]
    let flags := ps[1]
    let lamInv := ps[2]
    let coefs := ps[3]
    let hs := ps[4]
    let positions := ps[5]
    let queryWinPtrs := ps[6]
    let nItersG := ps[7]
    let chain ← B.heapBufDyn (← val (nItersG * GEN))
    if odd = 1 then
      let t0 ← openingQuery cap flags coefs hs (← val positions[GEN ^ 0]) (← val queryWinPtrs[GEN ^ 0]) base folds leafCells depth capDepth mu vanish nHs hsBits final
      chain[GEN ^ 0] := t0 * lamInv
    else
      chain[GEN ^ 0] := 0
    B.loopRtF 0 (pure nItersG) 8 (pure ([positions.v, queryWinPtrs.v, cap.v, flags.v, coefs.v, hs.v, chain.v, lamInv.v])) fun xi caps => do
      let positions := caps[0]
      let queryWinPtrs := caps[1]
      let cap := caps[2]
      let flags := caps[3]
      let coefs := caps[4]
      let hs := caps[5]
      let chain := caps[6]
      let lamInv := caps[7]
      if base = 1 then
        let pairPos ← val (positions * xi * xi)
        let pairWins ← val (queryWinPtrs * xi * xi)
        let d0 : FW ← openingQuery cap flags coefs hs (← val pairPos[GEN ^ odd]) (← val pairWins[GEN ^ odd]) base folds leafCells depth capDepth mu vanish nHs hsBits final
        let d1 : FW ← openingQuery cap flags coefs hs (← val pairPos[GEN ^ (odd + 1)]) (← val pairWins[GEN ^ (odd + 1)]) base folds leafCells depth capDepth mu vanish nHs hsBits final
        if final = 0 then
          let t0 ← val (((chain[xi] + d0) * lamInv + d1) * lamInv)
          chain[GEN ^ 1 * xi] := t0
      else
        let d : FW ← openingQuery cap flags coefs hs (← val positions[xi]) (← val queryWinPtrs[xi]) base folds leafCells depth capDepth mu vanish nHs hsBits final
        if final = 0 then
          let t0 ← val ((chain[xi] + d) * lamInv)
          chain[GEN ^ 1 * xi] := t0
    let mut total : FW := default
    if final = 0 then
      total ← fold chain[nItersG]
    else
      total := FW.c (lit 0)
    return [Ex.ret total]

/-- prod_t (d_t + chain_t) over one query's message-column coordinates, chain_t = W_t(x), x the query position; then the high part's share of the query's fold, What_mu(x) sum_j p_(2^mu + j) X_j(x), its normalizers in hs. -/
def residualQuery (basisChain : Word) (rowD : Word) (hs : Word) (nCols : Nat) (nHs : Nat) (hsBits : Nat) : B (Word × Word) := B.inline "residual_query" do
  let ws ← B.stackBuf HIGH_BITS_CAP
  ws[0] := basisChain
  let mut prefixEq ← val (rowD[GEN ^ 0] + basisChain)
  let mut basisChain := basisChain
  for t in [1:nCols + 1] do
    -- subspace-vanishing recurrence for the novel-basis point, a function of n_cols alone
    if t / HIGH_BITS_CAP = 0 then
      ws[t] := basisChain * (basisChain + arrWord VANISH_BY_COLS (nCols * (nCols + 1) / 2 + t - 1))
      basisChain := ws[t]
    else
      basisChain ← val (basisChain * (basisChain + arrWord VANISH_BY_COLS (nCols * (nCols + 1) / 2 + t - 1)))
    if t ≠ nCols then
      prefixEq ← val (prefixEq * (rowD[GEN ^ t] + basisChain))
  let t0 ← novelEval hs ws nHs hsBits
  let t1 ← val (basisChain * t0)
  return (prefixEq, t1)

/-- A non-final level's residual chains at the terminal point, RES_BATCH queries an iteration sharing the row's reads and constants, then the rest one at a time. Query q is weighted lam^q: each chain runs h <- (h + term_q) * lam_inv, ending at lam^-n * sum_q lam^q term_q. -/
def levelResidual (nQueries : Nat) (nCols : Nat) (nHs : Nat) (hsBits : Nat) : GFn where
  name := instName "level_residual" [.L nQueries, .L nCols, .L nHs, .L hsBits]
  arity := 4
  rets := 2
  body ps := do
    let positions := ps[0]
    let rowD := ps[1]
    let hs := ps[2]
    let lamInv := ps[3]
    let chain ← B.heapBufDyn (← val (GEN ^ (2 * (nQueries / RES_BATCH + 1))))
    chain[GEN ^ 0] := 0
    chain[GEN ^ 1] := 0
    B.loopRtF 0 (B.const (gpowE (nQueries / RES_BATCH))) 5 (pure ([positions.v, chain.v, rowD.v, hs.v, lamInv.v])) fun xr caps => do
      let positions := caps[0]
      let chain := caps[1]
      let rowD := caps[2]
      let hs := caps[3]
      let lamInv := caps[4]
      let batch ← val (positions * xr ^ RES_BATCH)
      let rec' : Shifted ← Shifted.of <$> val (chain * xr * xr)
      let mut h ← val rec'[GEN ^ 0]
      let mut hHigh ← val rec'[GEN ^ 1]
      for k in [0:RES_BATCH] do
        let (eqQ, highQ) ← residualQuery (← val batch[GEN ^ k]) rowD hs nCols nHs hsBits
        h ← val ((h + eqQ) * lamInv)
        hHigh ← val ((hHigh + highQ) * lamInv)
      rec'[GEN ^ 2] := h
      rec'[GEN ^ 3] := hHigh
    let rec' : Shifted := ⟨chain, 2 * (nQueries / RES_BATCH)⟩
    let mut h ← val rec'[GEN ^ 0]
    let mut hHigh ← val rec'[GEN ^ 1]
    if nQueries % RES_BATCH ≠ 0 then
      let rest ← B.heapBufDyn (← val (GEN ^ (2 * (nQueries % RES_BATCH + 1))))
      rest[GEN ^ 0] := h
      rest[GEN ^ 1] := hHigh
      let tail ← val (positions * (GEN ^ (nQueries / RES_BATCH)) ^ RES_BATCH)
      B.loopRtF 0 (B.const (gpowE (nQueries % RES_BATCH))) 5 (pure ([rest.v, tail.v, rowD.v, hs.v, lamInv.v])) fun xq caps => do
        let rest := caps[0]
        let tail := caps[1]
        let rowD := caps[2]
        let hs := caps[3]
        let lamInv := caps[4]
        let rq ← val (rest * xq * xq)
        let (eqQ, highQ) ← residualQuery (← val tail[xq]) rowD hs nCols nHs hsBits
        rq[GEN ^ 2] := (rq[GEN ^ 0] + eqQ) * lamInv
        rq[GEN ^ 3] := (rq[GEN ^ 1] + highQ) * lamInv
      let end' : Shifted := ⟨rest, 2 * (nQueries % RES_BATCH)⟩
      h ← val end'[GEN ^ 0]
      hHigh ← val end'[GEN ^ 1]
    return [.v h.v, .v hHigh.v]

/-- A level's query positions, FIELD_BITS // depth a word: the first word, word0, drawn by the query nonce's permutation, the rest one squeeze each. Row k of sqz is the capacity of the permutation that drew word k - 1; returns the last one. -/
def levelPositions (squeezes : Nat) (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "level_positions" [.L squeezes, .L depth, .L capDepth]
  arity := 9
  rets := 5
  body ps := do
    let word0 := ps[0]
    let fs0 := ps[1]
    let fs1 := ps[2]
    let fs2 := ps[3]
    let fs3 := ps[4]
    let fs4 := ps[5]
    let positions := ps[6]
    let winPtrs := ps[7]
    let tabs := ps[8]
    let sqz ← B.heapBufDyn (← val ((GEN ^ (squeezes + 1)) ^ FS_CELLS))
    sqz[GEN ^ FS_CELLS] := fs0
    sqz[GEN ^ 6] := fs1
    sqz[GEN ^ 7] := fs2
    sqz[GEN ^ 8] := fs3
    sqz[GEN ^ 9] := fs4
    call (instName "decode_query_windows" [.L depth, .L capDepth]) [word0, positions, winPtrs, tabs]
    B.loopRtF 1 (B.const (gpowE squeezes)) 4 (pure ([sqz.v, positions.v, winPtrs.v, tabs.v])) fun xs caps => do
      let sqz := caps[0]
      let positions := caps[1]
      let winPtrs := caps[2]
      let tabs := caps[3]
      let row ← val (sqz * xs ^ FS_CELLS)
      let rowCap ← fsLoad row 0 1
      let noRate ← B.stackBuf 8
      let (rowSp, packedWord) ← squeeze rowCap noRate 0
      fsStore ⟨row, FS_CELLS⟩ 0 1 rowSp
      let queryPtr ← val (xs ^ (FIELD_BITS / depth))
      call (instName "decode_query_windows" [.L depth, .L capDepth]) [packedWord, positions * queryPtr, winPtrs * queryPtr, tabs]
      pure ()
    let sp ← fsLoad (← val (sqz * (GEN ^ squeezes) ^ FS_CELLS)) 0 1
    return [.v sp[0].v, .v sp[1].v, .v sp[2].v, .v sp[3].v, .v sp[4].v]

/-- A level's Merkle cap, hinted and checked up to its root, and the level's query batch walked into it. Returns the root, the batch's sum, and lam^n_queries. At level 0 a leaf image lists its lanes from the top down: the lanes a padding-free commitment leaves out are its LEADING words, whose whole blocks the committer hashes once for all leaves. The flip is a compile-time index. -/
def levelQueries (nQueries : Nat) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : GFn where
  name := instName "level_queries" [.L nQueries, .L base, .L folds, .L leafCells, .L depth, .L capDepth, .L mu, .L nHs, .L hsBits, .L final]
  arity := 6
  rets := 4
  body ps := do
    let lam := ps[0]
    let lamInv := ps[1]
    let coefs := ps[2]
    let hs := ps[3]
    let positions := ps[4]
    let winPtrs := ps[5]
    let cap ← B.heapBufDyn (← val (GEN ^ (4 * 2 ^ capDepth)))
    B.witness "merkle_caps" (.heap cap.v 0 (4 * 2 ^ capDepth))
    let flags ← B.heapBufDyn (← val (GEN ^ (2 ^ capDepth)))
    B.witness "merkle_cap_active" (.heap flags.v 0 (2 ^ capDepth))
    let t0 ← callN (instName "verify_merkle_cap" [.L capDepth]) [cap, flags] 2
    let root0 := t0[0]!
    let root1 := t0[1]!
    let mut pairs : Nat := default
    let mut odd : Nat := default
    if base = 1 then
      pairs := nQueries / 2
      odd := nQueries % 2
    else
      pairs := nQueries
      odd := 0
    let batched ← call1 (instName "opening_queries" [.L odd, .L base, .L folds, .L leafCells, .L depth, .L capDepth, .L mu, .L (mu * (mu + 1) / 2), .L nHs, .L hsBits, .L final]) [cap, flags, lamInv, coefs, hs, positions, winPtrs, GEN ^ pairs]
    return [.v root0.v, .v root1.v, .v batched.v, Ex.ret (lam ^ nQueries)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The stacked WHIR opening, one specialization per committed log-size m_idx, the rate g^rate_sel dispatched per level by a `match` into `level_positions`, `level_queries` and `level_residual`, which read the tables a rate changes (query counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders` checks does not vary by rate. Only the executed arm pops the opening's hint streams. The opening's scalars (round tables, level roots, high parts, OOD values, nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.

Returns the closing claim, the point in witness order (and 1 + it), the glued claims' weights at it, and the final lane's low part at the closing point.
-/
def openStacked (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := ps[0]
    let mut fs0 := ps[1]
    let mut fs1 := ps[2]
    let mut fs2 := ps[3]
    let mut fs3 := ps[4]
    let mut fs4 := ps[5]
    let target := ps[6]
    let commitRoot0 := ps[7]
    let commitRoot1 := ps[8]
    let mut cursor : Shifted := Shifted.of ps[9]
    let tabs := ps[10]
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx  -- the final level, n_levels - 1
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    -- The final lane, its low part then its high part, read from the stream.
    let finalMsg ← B.heapBufDyn (← val (GEN ^ (yrLen + arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS + last))))
    -- Each cap root is checked against its transcript-bound level root.
    let levelRoots ← B.heapBufDyn (← val (GEN ^ (2 * nLevels)))
    levelRoots[GEN ^ 0] := commitRoot0
    levelRoots[GEN ^ 1] := commitRoot1
    -- The alphas in round order, the point's fold coordinates, and each round's alpha, beta for the row folds.
    let foldChallenges ← B.heapBufDyn (← val (GEN ^ nFolds))
    let roundCoefs ← B.heapBufDyn (← val (GEN ^ (2 * nFolds)))
    -- Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1. A level's high part (its folds' coefficients, normalizers in) sits at its folds' offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    let levelScales ← B.heapBufDyn (← val (GEN ^ nLevels))
    let levelLamInvs ← B.heapBufDyn (← val (GEN ^ nLevels))
    let levelHs ← B.heapBufDyn (← val (GEN ^ nFolds))
    let mut colsTotal := 0
    for cl in [0:last] do
      colsTotal := colsTotal + arrInt LIG_LOG_MSG_COLS (mIdx * LIG_MAX_LEVELS + cl)
    let oodZ ← B.heapBufDyn (← val (GEN ^ colsTotal))
    let oodScalars ← B.heapBufDyn (← val (GEN ^ nLevels))
    -- A level's query positions, the most any rate draws there, follow the previous levels' (LIG_POS_OFF).
    let queryPositions ← B.heapBufDyn (← val (GEN ^ (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← val (GEN ^ (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Shifted := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut noRate : List V := default
    let mut lam : FW := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Shifted := default
    let mut sc : FW := default
    let mut scale : Word := default
    for lvl in [0:nLevels] do
      ml := mIdx * LIG_MAX_LEVELS + lvl
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := mu * (mu + 1) / 2
      for j in [0:folds] do
        let t0 ← callN "opening_round" [fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, foldChallenges * GEN ^ (foldsOff + j), roundCoefs * GEN ^ (2 * (foldsOff + j))] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := Shifted.of t0[5]!
        claim := t0[6]!
      let mut oodY : Word := default
      let mut word0 : Word := default
      let mut pow0 : Word := default
      if lvl = last then
        let t1 ← callN (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0, fs1, fs2, fs3, fs4, cursor, finalMsg] 8
        word0 := t1[0]!
        pow0 := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := Shifted.of t1[7]!
      else
        -- The next level's root and this level's high part, then the OOD nonce, whose permutation draws the OOD point's first coordinate, then its value and the query nonce.
        sent ← B.heapBufDyn (← val (GEN ^ (2 + folds)))
        let t1 ← callN (instName "opening_message" [.L (2 + folds), .L 1]) [fs0, fs1, fs2, fs3, fs4, cursor, sent] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := Shifted.of t1[7]!
        call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod, tabs]
        levelRoots[GEN ^ (2 * lvl + 2)] := sent[GEN ^ 0]
        levelRoots[GEN ^ (2 * lvl + 3)] := sent[GEN ^ 1]
        oodRow := ⟨oodZ, colsOff⟩
        let t2 ← callN (instName "squeeze_point_from" [.L mu]) [fs0, fs1, fs2, fs3, fs4, zFirst, oodRow] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor := t4
        sp ← fsAbsorbNonce sp rate 1 (← val cursor[GEN ^ 0])
        cursor := ⟨cursor.base, cursor.exp + 1⟩
        word0 := sp[0]
        pow0 := sp[1]
        fs0 := sp[8]
        fs1 := sp[9]
        fs2 := sp[10]
        fs3 := sp[11]
        fs4 := sp[12]
      -- The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above; its permutation draws the first query word, word0.
      call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0, tabs]
      let t1 ← B.targets [none, none, none, none, none]
      let t2 ← val (queryPositions * GEN ^ posOff)
      let t3 ← val (queryWinPtrs * GEN ^ posOff)
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map (fun arm => instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + arm * LIG_RATE_STRIDE)), .L (arrInt LIG_TREE_DEPTH (ml + arm * LIG_RATE_STRIDE)), .L (arrInt LIG_CAP_DEPTH (ml + arm * LIG_RATE_STRIDE))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t2.v, t3.v, tabs.v] t1
      fs0 := t1[0]
      fs1 := t1[1]
      fs2 := t1[2]
      fs3 := t1[3]
      fs4 := t1[4]
      let mut lamInv : FW := default
      if lvl ≠ last then
        -- The level's batching challenge, the query message's last squeeze.
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t4, t5) ← squeeze sp noRate 0
        sp := t4
        lam := FW.w t5
        lamInv ← fold (1 / lam)
        fs0 := sp[8]
        fs1 := sp[9]
        fs2 := sp[10]
        fs3 := sp[11]
        fs4 := sp[12]
      else
        lam := FW.c (lit 0)
        lamInv := FW.c (lit 0)
      -- The sent coefficients scaled by the What_i normalizers of their basis elements, so a query evaluates them at the unnormalized W_i(x): at the final level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the high part alone, What_mu folded in, for the residual pass.
      if lvl = last then
        nHs := yrLen + folds
        hsBits := yrLog + 1
        hs ← Shifted.of <$> B.heapBufDyn (← val (GEN ^ nHs))
        for c_k in [0:nHs] do
          sc := FW.c (lit 1)
          for i in [0:hsBits] do
            if c_k / 2 ^ i % 2 = 1 then
              sc ← fold (sc * arrWord VANISH_INVS_BY_COLS (vanish + i))
          hs[GEN ^ c_k] := finalMsg[GEN ^ c_k] * sc
      else
        nHs := 0  -- the queries take no high part here
        hsBits := 0
        hs := ⟨levelHs, foldsOff⟩
        for c_k in [0:folds] do
          sc := FW.c (arrWord VANISH_INVS_BY_COLS (vanish + mu))
          for i in [0:arrInt LIG_HIGH_BITS ml] do
            if c_k / 2 ^ i % 2 = 1 then
              sc ← fold (sc * arrWord VANISH_INVS_BY_COLS (vanish + i))
          hs[GEN ^ c_k] := sent[GEN ^ (2 + c_k)] * sc
      let mut root0 : Word := default
      let mut root1 : Word := default
      let mut batched : Word := default
      let mut lamPow : Word := default
      if lvl = last then
        let t4 ← B.targets [none, none, none, none]
        let t5 ← val lam
        let t6 ← val lamInv
        let t7 ← val (roundCoefs * GEN ^ (2 * foldsOff))
        let t8 ← val hs
        let t9 ← val (queryPositions * GEN ^ posOff)
        let t10 ← val (queryWinPtrs * GEN ^ posOff)
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map (fun arm => instName "level_queries" [.L (arrInt LIG_QUERIES (ml + arm * LIG_RATE_STRIDE)), .L (1 / (lvl + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + arm * LIG_RATE_STRIDE)), .L (arrInt LIG_CAP_DEPTH (ml + arm * LIG_RATE_STRIDE)), .L mu, .L nHs, .L hsBits, .L 1])) [t5.v, t6.v, t7.v, t8.v, t9.v, t10.v] t4
        root0 := t4[0]
        root1 := t4[1]
        batched := t4[2]
        lamPow := t4[3]
      else
        let t4 ← B.targets [none, none, none, none]
        let t5 ← val lam
        let t6 ← val lamInv
        let t7 ← val (roundCoefs * GEN ^ (2 * foldsOff))
        let t8 ← val hs
        let t9 ← val (queryPositions * GEN ^ posOff)
        let t10 ← val (queryWinPtrs * GEN ^ posOff)
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map (fun arm => instName "level_queries" [.L (arrInt LIG_QUERIES (ml + arm * LIG_RATE_STRIDE)), .L (1 / (lvl + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + arm * LIG_RATE_STRIDE)), .L (arrInt LIG_CAP_DEPTH (ml + arm * LIG_RATE_STRIDE)), .L 0, .L 0, .L 0, .L 0])) [t5.v, t6.v, t7.v, t8.v, t9.v, t10.v] t4
        root0 := t4[0]
        root1 := t4[1]
        batched := t4[2]
        lamPow := t4[3]
      levelRoots[GEN ^ (2 * lvl)] := root0
      levelRoots[GEN ^ (2 * lvl + 1)] := root1
      if lvl ≠ last then
        -- The OOD claim takes lam, the query batch lam^2 times its own powers of lam. A query's value is its fold plus the high part's share, which enters the claim linearly: the residual pass adds it, scaled by every alpha and tail challenge drawn after this level, the claim's factor from here on.
        oodScalars[GEN ^ (lvl + 1)] := lam
        claim ← val (claim + lam * oodY)
        scale ← val (lam * lam * lamPow)
        claim ← val (claim + scale * batched)
        levelScales[GEN ^ lvl] := scale
        levelLamInvs[GEN ^ lvl] := lamInv
      colsOff := colsOff + mu
    -- ---- the closing sumcheck over the final lane's low part ----
    let tailChallenges ← B.heapBufDyn (← val (GEN ^ YR_LOG_CAP))
    let mut tailC : Word := default
    for j in [0:yrLog] do
      let t4 ← callN "opening_tail_round" [fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs] 8
      fs0 := t4[0]!
      fs1 := t4[1]!
      fs2 := t4[2]!
      fs3 := t4[3]!
      fs4 := t4[4]!
      cursor := Shifted.of t4[5]!
      claim := t4[6]!
      tailC := t4[7]!
      tailChallenges[GEN ^ j] := tailC
    for j in [yrLog:YR_LOG_CAP] do
      tailChallenges[GEN ^ j] := 0
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg, tailChallenges]
    -- ---- the same point, indexed by committed-witness coordinate ---- The alphas bind coordinates in ROUND order, and level 0's are the lane fold, binding the witness's TOP k coordinates: lane l of the commitment is the stack block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole lanes for the committer to leave out of the encode. Every transparent weight downstream is written in witness coordinates, so rotate the point left by those k rounds here, while the level shape is still compile-time. Padding is zero so shared prefix chains may compute unused entries above m without reading uninitialized cells.
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    -- point1 = 1 + point, the form every eq factor reads.
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j in [0:foldHead] do
      point[GEN ^ j] := foldChallenges[GEN ^ (laneFolds + j)]
      point1[GEN ^ j] := 1 + foldChallenges[GEN ^ (laneFolds + j)]
    for j in [0:yrLog] do
      point[GEN ^ (foldHead + j)] := tailChallenges[GEN ^ j]
      point1[GEN ^ (foldHead + j)] := 1 + tailChallenges[GEN ^ j]
    for j in [0:laneFolds] do
      point[GEN ^ (foldHead + yrLog + j)] := foldChallenges[GEN ^ j]
      point1[GEN ^ (foldHead + yrLog + j)] := 1 + foldChallenges[GEN ^ j]
    for j in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      point[GEN ^ j] := 0
      point1[GEN ^ j] := 1
    -- ---- each non-final level's glued query batch, at the terminal point ---- Every query of a level runs the SAME product shape over its message-column coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    -- 1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t a coordinate's two coefficients depend on the challenge and the baked vanishing inverse alone, so they hoist out of the query loop (one row a level, alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply a coordinate, and the level's product of the b_t scales its sum once. A zero challenge makes b_t zero and the division unsatisfiable, which rejects rather than accepts.
    let mut basisTotal := 0
    for bl in [0:last] do
      basisTotal := basisTotal + arrInt LIG_RESIDUAL_PREFIX_LEN (mIdx * LIG_MAX_LEVELS + bl) + yrLog
    let basisD ← B.heapBufDyn (← val (GEN ^ basisTotal))
    let levelScale ← B.heapBufDyn (← val (GEN ^ nLevels))
    let levelAfter ← B.heapBufDyn (← val (GEN ^ nLevels))  -- the product of the challenges after the level
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    for lvl in [0:last] do
      ml := mIdx * LIG_MAX_LEVELS + lvl
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := arrInt LIG_LOG_MSG_COLS ml * (arrInt LIG_LOG_MSG_COLS ml + 1) / 2
      scale ← val levelScales[GEN ^ lvl]
      let mut after : FW := FW.c (gpowE 0)
      for t in [0:prefixLen] do
        foldC ← val foldChallenges[GEN ^ (arrInt LIG_RESIDUAL_FOLD_OFF ml + t)]
        coefB ← val (foldC * arrWord VANISH_INVS_BY_COLS (vanish + t))
        basisD[GEN ^ (basisOff + t)] := (1 + foldC) / coefB
        scale ← val (scale * coefB)
        after ← fold (after * foldC)
      for j in [0:yrLog] do
        tailC ← val tailChallenges[GEN ^ j]
        coefB ← val (tailC * arrWord VANISH_INVS_BY_COLS (vanish + prefixLen + j))
        basisD[GEN ^ (basisOff + prefixLen + j)] := (1 + tailC) / coefB
        scale ← val (scale * coefB)
        after ← fold (after * tailC)
      levelScale[GEN ^ lvl] := scale
      levelAfter[GEN ^ lvl] := after
      basisOff := basisOff + prefixLen + yrLog
    -- Per level: the glued weights' sum, then the claim's correction.
    let innerChain ← B.heapBufDyn (← val (GEN ^ (2 * nLevels)))
    innerChain[GEN ^ 0] := 0
    innerChain[GEN ^ 1] := claim
    let mut resBasis := 0
    for lvl in [0:last] do
      ml := mIdx * LIG_MAX_LEVELS + lvl
      -- level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
      let t5 ← B.targets [none, none]
      let t6 ← val (queryPositions * GEN ^ (arrInt LIG_POS_OFF ml))
      let t7 ← val (basisD * GEN ^ resBasis)
      let t8 ← val (levelHs * GEN ^ (arrInt LIG_FOLDS_OFF ml))
      let t9 ← val levelLamInvs[GEN ^ lvl]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map (fun arm => instName "level_residual" [.L (arrInt LIG_QUERIES (ml + arm * LIG_RATE_STRIDE)), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t6.v, t7.v, t8.v, t9.v] t5
      let h := t5[0]
      let hHigh := t5[1]
      resBasis := resBasis + arrInt LIG_RESIDUAL_PREFIX_LEN ml + yrLog
      -- accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total, and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
      let acc : Shifted := ⟨innerChain, 2 * lvl⟩
      acc[GEN ^ 2] := acc[GEN ^ 0] + levelScale[GEN ^ lvl] * h
      acc[GEN ^ 3] := acc[GEN ^ 1] + levelScales[GEN ^ lvl] * levelAfter[GEN ^ lvl] * hHigh
    -- The OOD claims' eq weights at the same terminal point, each glued with its level's lam.
    let mut oodInner : FW := FW.c (lit 0)
    let mut oodOff := 0
    for oodLvl in [1:nLevels] do
      ml := mIdx * LIG_MAX_LEVELS + oodLvl
      let zFolded := arrInt LIG_LOG_MSG_COLS (ml - 1) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + arrInt LIG_LOG_MSG_COLS (ml - 1)
      let mut scalar ← val oodScalars[GEN ^ oodLvl]
      for t in [0:zFolded] do
        scalar ← val (scalar * (1 + oz[GEN ^ t] + foldChallenges[GEN ^ (risStart + t)]))
      for t in [0:yrLog] do
        scalar ← val (scalar * (1 + oz[GEN ^ (zFolded + t)] + tailChallenges[GEN ^ t]))
      oodInner ← fold (oodInner + scalar)
    let total : Shifted := ⟨innerChain, 2 * last⟩
    return [.load total.base.v (total.exp + 1), .v point.v, .v point1.v, Ex.ret (total[GEN ^ 0] + oodInner), .v yrAtTail.v]

end
end LeanVM.Guest.Program
