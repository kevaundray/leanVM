/-
  LeanVM.Guest.Program.MultilinearPrimitives

  The guest's section "multilinear primitives".
-/

module

public import LeanVM.Guest.Program.BitsLogsAndTheExponent

/-!
# Multilinear primitives
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- The eq tensor of the n_coords challenges at point_ptr[0..n_coords), built by doubling into out (size 2^(n_coords+1) - 2); the final 2^n_coords values start at offset 2^n_coords - 2. -/
def eqtree (pointPtr : Shifted) (out : Word) (nCoords : Nat) : B Unit := B.inline "eqtree" do
  let r0 ← val pointPtr[GEN ^ 0]
  out[GEN ^ 0] := 1 + r0
  out[GEN ^ 1] := r0
  let mut pw : Word := default
  for t in [1:nCoords] do
    let rt ← val pointPtr[GEN ^ t]
    let onePlusRt ← val (1 + rt)
    for i in [0:2 ^ t] do
      pw ← val out[GEN ^ (2 ^ t - 2 + i)]
      out[GEN ^ (2 ^ (t + 1) - 2 + i)] := pw * onePlusRt
      out[GEN ^ (2 ^ (t + 1) - 2 + 2 ^ t + i)] := pw * rt

/-- eqtree into frame cells, in the same layout, the last level cut at `count` (which must exceed half of it). -/
def eqtreeFrame (pointPtr : Shifted) (out : List V) (nCoords : Nat) (count : Nat) : B Unit := B.inline "eqtree_frame" do
  let r0 ← val pointPtr[GEN ^ 0]
  out[0] := 1 + r0
  out[1] := r0
  let mut pw : Word := default
  for t in [1:nCoords] do
    let rt ← val pointPtr[GEN ^ t]
    let onePlusRt ← val (1 + rt)
    for i in [0:2 ^ t] do
      pw := out[2 ^ t - 2 + i]
      out[2 ^ (t + 1) - 2 + i] := pw * onePlusRt
      if t + 1 = nCoords then
        if (2 ^ t + i) / count = 0 then
          out[2 ^ (t + 1) - 2 + 2 ^ t + i] := pw * rt
      else
        out[2 ^ (t + 1) - 2 + 2 ^ t + i] := pw * rt

/-- Prefix products of eq(a_k, b_k) = a_k + b1_k, b1 = 1 + b, from `seed`, so a reader picks the partial product up at its own certified length. Entry t is written from inputs with index < t only, so a garbage tail past a buffer's written extent cannot corrupt any shorter prefix. -/
def eqPrefixChain : GFn where
  name := "eq_prefix_chain"
  arity := 5
  rets := 0
  body ps := do
    let chain := ps[0]
    let seed := ps[1]
    let a := ps[2]
    let b1 := ps[3]
    let countG := ps[4]
    assert log countG < EQ_CHAIN_ARMS
    let t0 ← B.targets [none]  -- a match needs a target
    B.dispatchInto countG ((List.range EQ_CHAIN_ARMS).map (fun arm => instName "eq_prefix_run" [.L arm])) [chain.v, seed.v, a.v, b1.v] t0
    let done := t0[0]
    return []

def eqPrefixRun (n : Nat) : GFn where
  name := instName "eq_prefix_run" [.L n]
  arity := 4
  rets := 1
  body ps := do
    let chain := ps[0]
    let seed := ps[1]
    let a := ps[2]
    let b1 := ps[3]
    chain[GEN ^ 0] := seed
    let mut v := seed
    for k in [0:n] do
      v ← val (v * (a[GEN ^ k] + b1[GEN ^ k]))
      chain[GEN ^ (k + 1)] := v
    return [.c 0]

def plusOneRun (n : Nat) : GFn where
  name := instName "plus_one_run" [.L n]
  arity := 2
  rets := 1
  body ps := do
    let out := ps[0]
    let src := ps[1]
    for k in [0:n] do
      out[GEN ^ k] := 1 + src[GEN ^ k]
    return [.c 0]

/-- Coordinates 0..n of zs/ps multiply rows 0..64 of `row` into the next row, row k by prod_i (zs_i^(2^k) + ps_i), the Frobenius powers walked inside. -/
def rsEqRows (n : Nat) : GFn where
  name := instName "rs_eq_rows" [.L n]
  arity := 3
  rets := 1
  body ps := do
    let row := ps[0]
    let zs := ps[1]
    let ps' := ps[2]
    let mut nxt : Shifted := ⟨row, BASE_FIELD_BITS⟩
    if n = 0 then
      nxt := Shifted.of row
    else
      let zv ← B.stackBuf 512  -- zv[64 i + k] = zs_i^(2^k)
      let a ← B.stackBuf RS_CHUNK
      for i in [0:n] do
        zv[BASE_FIELD_BITS * i] := zs[GEN ^ i]
        a[i] := ps'[GEN ^ i]
      for k in [0:BASE_FIELD_BITS] do
        let mut acc ← val row[GEN ^ k]
        for i in [0:n] do
          acc ← val (acc * (zv[BASE_FIELD_BITS * i + k] + a[i]))
          if k ≠ BASE_FIELD_BITS - 1 then
            zv[BASE_FIELD_BITS * i + k + 1] := zv[BASE_FIELD_BITS * i + k] * zv[BASE_FIELD_BITS * i + k]
        nxt[GEN ^ k] := acc
    let t0 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val nxt)
    return [.into t0]

/-- One run of the telescoped ring-switch product E = sum_k c_k * prod_j (z_j^(2^k) + 1 + ris_j): coordinate x multiplies row k by (z^(2^k) + 1 + point_x), z evolving by squaring per row. The runtime coordinates walk OUTSIDE and the fixed Frobenius powers inside, so nothing stores a z-power table. Coordinates go RS_CHUNK an iteration, so a row is read and written once per chunk; count = RS_CHUNK q + r is pinned from advice bits, and the r left over run after the loop. The chain holds the starting row of ones and a row per chunk, q + 2 rows at most. Returns the final row. -/
def rsEqRun : GFn where
  name := "rs_eq_run"
  arity := 3
  rets := 1
  body ps := do
    let zVals := ps[0]
    let point1 := ps[1]
    let countG := ps[2]
    let bits ← B.stackBuf RS_COUNT_BITS
    B.hintBitsExpTo (.stack bits[0:RS_COUNT_BITS]) countG RS_COUNT_BITS
    let mut rG : FW := FW.c (gpowE 0)
    let mut qG : FW := FW.c (gpowE 0)
    for k in [0:RS_COUNT_BITS] do
      let b := bits[k]
      bits[k] := b * b
      if k / RS_CHUNK_BITS = 0 then
        rG ← fold (rG * (1 + b * (1 + GEN ^ (2 ^ k))))
      else
        qG ← fold (qG * (1 + b * (1 + GEN ^ (2 ^ (k - RS_CHUNK_BITS)))))
    assert qG ^ RS_CHUNK * rG == countG
    let chain ← B.heapBufDyn (← val ((qG * GEN ^ 2) ^ BASE_FIELD_BITS))
    for k in [0:BASE_FIELD_BITS] do
      chain[GEN ^ k] := 1
    B.loopRtF 0 (FW.val qG) 3 (pure ([chain.v, zVals.v, point1.v])) fun xq caps => do
      let chain := caps[0]
      let zVals := caps[1]
      let point1 := caps[2]
      let base ← val (xq ^ RS_CHUNK)
      let done ← call1 (instName "rs_eq_rows" [.L RS_CHUNK]) [chain * xq ^ BASE_FIELD_BITS, zVals * base, point1 * base]
      pure ()
    let base ← val (qG ^ RS_CHUNK)
    let row ← val (chain * qG ^ BASE_FIELD_BITS)
    let t0 ← B.targets [none]
    let t1 ← val (zVals * base)
    let t2 ← val (point1 * base)
    B.dispatchInto (← val rG) ((List.range RS_CHUNK).map (fun arm => instName "rs_eq_rows" [.L arm])) [row.v, t1.v, t2.v] t0
    let last := t0[0]
    return [.v last.v]

def foldFinalMsg (logLen : Nat) : GFn where
  name := instName "fold_final_msg" [.L logLen]
  arity := 2
  rets := 1
  body ps := do
    let msg := ps[0]
    let point := ps[1]
    let weights ← B.stackBuf 10
    for j in [0:logLen] do
      weights[2 * j] := 1 + point[GEN ^ j]
      weights[2 * j + 1] := point[GEN ^ j]
    -- Weighted fold of the final_msg multilinear over 2^log_len values (log_len is the candidate's yr_log_n; the frame buffers use the global max size).
    let l0 ← B.stackBuf 32
    for t in [0:2 ^ logLen / 2] do
      l0[t] := weights[0] * msg[GEN ^ (2 * t)] + weights[1] * msg[GEN ^ (2 * t + 1)]
    let mut cursor := l0
    let mut n := 2 ^ logLen / 2
    for j in [1:logLen] do
      let nxt ← B.stackBuf 32
      for t in [0:n / 2] do
        nxt[t] := weights[2 * j] * cursor[2 * t] + weights[2 * j + 1] * cursor[2 * t + 1]
      cursor := nxt
      n := n / 2
    return [.v cursor[0].v]

/-- One PLAIN sumcheck round, from the sponge of round record `rd` into the next record's. The prover sends the round polynomial's coefficients bar the one the split h(0) + h(1) == claim fixes, so the verifier derives that one and reads h at the challenge by Horner. Nothing is reapplied: no eq factor, no separate term for the tables still waiting, and the eq point is not read here at all. -/
def sumcheckRound4 : GFn where
  name := "sumcheck_round4"
  arity := 4
  rets := 3
  body ps := do
    let rd := ps[0]
    let msgCursor : Shifted := Shifted.of ps[1]
    let claim := ps[2]
    let tabs := ps[3]
    let sp ← fsLoad rd ROUND_FS 1
    let rate ← B.stackBuf 8
    let (c0, msgCursor) ← fsNext rate 0 msgCursor
    let (c2, msgCursor) ← fsNext rate 1 msgCursor
    let (c3, msgCursor) ← fsNext rate 2 msgCursor
    -- The split identity fixes c1 = claim + c2 + c3, so it is neither sent nor bound, and h(y) = c0 + y (claim + (1 + y) (c2 + (1 + y) c3)). Then the round's grind.
    let (sp, y, msgCursor) ← fsGrindSqueeze sp rate 3 msgCursor (Shifted.of tabs) ROUND3_GRIND_BITS
    fsStore ⟨rd, ROUND_SLOTS⟩ ROUND_FS 1 sp
    let y1 ← val (1 + y)
    let t9 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← val msgCursor)
    let t10 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) c0 (← val (y * (claim + y1 * (c2 + y1 * c3))))
    return [.into t9, .into t10, .v y.v]

/-- n GKR rounds, from the round record at `rd` (ROUND_SLOTS consecutive fields) to the one n further. The prover sends every coefficient but c0, which the round's pulled-out eq factor leaves fixed: c0 + r (c1 + ... + c4) == claim, r being the previous point's coordinate pt[q], then the round's grind; the challenge goes to pt[MU_CAP + 2 + q]. -/
def gkrRounds (n : Nat) : GFn where
  name := instName "gkr_rounds" [.L n]
  arity := 3
  rets := 1
  body ps := do
    let rd := ps[0]
    let pt := ps[1]
    let tabs := ps[2]
    if n ≠ 0 then
      let mut sp ← fsLoad rd ROUND_FS 1
      let mut cur : Shifted ← Shifted.of <$> val rd[GEN ^ ROUND_CURSOR]
      let mut claim ← val rd[GEN ^ ROUND_CLAIM]
      for q in [0:n] do
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
        let (t8, t9, t10) ← fsGrindSqueeze sp rate 4 cur (Shifted.of tabs) ROUND5_GRIND_BITS
        sp := t8
        let rk := t9
        cur := t10
        let c0 ← val (claim + pt[GEN ^ q] * (c1 + c2 + c3 + c4))
        pt[GEN ^ (MU_CAP + 2 + q)] := rk
        claim ← val (c0 + rk * (c1 + rk * (c2 + rk * (c3 + rk * c4))))
      let rdNext : Shifted := ⟨rd, ROUND_SLOTS * n⟩
      fsStore rdNext ROUND_FS 1 sp
      rdNext[GEN ^ ROUND_CURSOR] := cur
      rdNext[GEN ^ ROUND_CLAIM] := claim
    return [.c 0]

/-- The rounds of a claim-batching sumcheck: two hinted values per round (g(1) and g(inf)) and the degree-two round's nonce, if any, the split fixing the third against the running claim, and the challenges collected into `point`. -/
def batchSumcheck (nRounds : Nat) : GFn where
  name := instName "batch_sumcheck" [.L nRounds]
  arity := 9
  rets := 6
  body ps := do
    let fs0 := ps[0]
    let fs1 := ps[1]
    let fs2 := ps[2]
    let fs3 := ps[3]
    let fs4 := ps[4]
    let msgs := ps[5]
    let mut running := ps[6]
    let point := ps[7]
    let tabs := ps[8]
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    for rd in [0:nRounds] do
      let rate ← B.stackBuf 8
      let (msgG1, c) ← fsNext rate 0 ⟨msgs, BC_ROUND_WORDS * rd⟩
      let (msgGinf, c) ← fsNext rate 1 c
      let (t4, t5, t6) ← fsGrindSqueeze sp rate 2 c (Shifted.of tabs) ROUND2_GRIND_BITS
      sp := t4
      let rv := t5
      let c : Shifted := t6
      point[GEN ^ rd] := rv
      let gZero ← val (running + msgG1)
      let cOne ← val (gZero + msgG1 + msgGinf)
      running ← val ((msgGinf * rv + cOne) * rv + gZero)  -- fold the degree-2 round at rv
    return [.v sp[8].v, .v sp[9].v, .v sp[10].v, .v sp[11].v, .v sp[12].v, .v running.v]

end
end LeanVM.Guest.Program
