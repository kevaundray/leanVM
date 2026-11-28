/-
  LeanVM.Guest.Program.AggregationNode

  The guest's section "the aggregation node".
-/

module

public import LeanVM.Guest.Program.LeanDa

/-!
# The aggregation node
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

set_option maxHeartbeats 4000000 in
/-- One node of an aggregation tree: n_raw_lean_xmss leanXMSS signatures, n_raw_lean_sphincs leanSPHINCS signatures and n_children sub-proofs OF THIS SAME BYTECODE. A claim of either scheme is a pubkey and the message it signed, and each signature is verified against the claim in its own coverage slot; a leanXMSS signature carries its own leaf index. It publishes at most one DA digest: that of the blob matrix it checks, or one of its children's, or none.

The declared lists are what the node publishes; the duplicate slots absorb claims a child covers that the set does not declare. The coverage table is one region per scheme, each its declared claims then its own duplicates:

[leanXMSS: declared | dup][leanSPHINCS: declared | dup]

so one range check per write keeps each writer inside its own region: that is what makes the statement's split mean which scheme verified which claim. A slot is four cells, a pubkey and the message that pubkey signed.
-/
def main : GFn where
  name := "main"
  arity := 0
  rets := 0
  body ps := do
    let meta' ← B.stackBuf 8
    B.witness "meta" (.stack meta')  -- every count in the exponent
    let nLxG := meta'[0]
    let nXdupG := meta'[1]
    let nRawXG := meta'[2]
    let nLeanSphincsG := meta'[3]
    let nSdupG := meta'[4]
    let nRawSG := meta'[5]
    let nChildrenG := meta'[6]
    let nDirectDaG := meta'[7]
    let _ ← B.assertGpow nLxG
    let _ ← B.assertGpow nXdupG
    let _ ← B.assertGpow nRawXG
    let _ ← B.assertGpow nLeanSphincsG
    let _ ← B.assertGpow nSdupG
    let _ ← B.assertGpow nRawSG
    assert log nChildrenG < 17
    assert log nDirectDaG < 2
    let lxSlotsG ← val (nLxG * nXdupG)
    let leanSphincsSlotsG ← val (nLeanSphincsG * nSdupG)
    -- The sum of both regions bounds the coverage indices, so it is what has to be a memory address: its log is then below 2^30 and the runtime bounds below mean what they say. An honest node holds its coverage table in memory, so it fits.
    let nTotalG ← val (lxSlotsG * leanSphincsSlotsG)
    let _ ← B.assertGpow nTotalG
    -- The proving environment (the proof system's version and this bytecode) as one digest. It rides the statement rather than the bytecode, so nothing here has to know its own hash; the outer verifier pins it, and every child statement rebuilt below copies it, which is what keeps a whole tree on one bytecode.
    let fsSeed ← B.stackBuf 2
    B.witness "fs_seed" (.stack fsSeed)
    let seed0 := fsSeed[0]
    let seed1 := fsSeed[1]
    -- ---- the claim lists ----
    let gSquares ← call1 "exponent_tables" []
    -- One table per scheme: its declared list (strictly sorted, checked by the outer verifier, which holds it) followed by its own duplicate slots. The coverage indices below run over one space: leanXMSS, then leanSPHINCS.
    --
    -- Each list's digest is a plain hash of its claims, 64 bytes a claim, its padding binding its length; the statement carries the two digests side by side.
    let lxTable ← B.heapBufDyn (← val (lxSlotsG ^ 4))
    let leanSphincsTable ← B.heapBufDyn (← val (leanSphincsSlotsG ^ 4))
    let t0 ← callN "claim_list_digest" [lxTable, nLxG] 2
    let xd0 := t0[0]!
    let xd1 := t0[1]!
    let t1 ← callN "claim_list_digest" [leanSphincsTable, nLeanSphincsG] 2
    let sd0 := t1[0]!
    let sd1 := t1[1]!
    -- The duplicate slots ride the same tables but outside the hashed prefixes.
    B.loopRtF 0 (pure nXdupG) 2 (pure ([lxTable.v, nLxG.v])) fun xd caps => do
      let lxTable := caps[0]
      let nLxG := caps[1]
      let dup ← val (lxTable * (nLxG * xd) ^ 4)
      B.witness "dup_claims" (.heap dup.v 0 4)
    B.loopRtF 0 (pure nSdupG) 2 (pure ([leanSphincsTable.v, nLeanSphincsG.v])) fun xd caps => do
      let leanSphincsTable := caps[0]
      let nLeanSphincsG := caps[1]
      let dup ← val (leanSphincsTable * (nLeanSphincsG * xd) ^ 4)
      B.witness "dup_claims" (.heap dup.v 0 4)
    -- ---- coverage ---- Every one of the n_total slots is written exactly once: write-once memory rejects a second write (each writer's marks lie in its own range of counts, and a gap-walked child list never revisits a slot, so two writes to one slot disagree), and the count below rejects a missed one. So every declared claim is covered by a direct check of its own kind or by a verified child. Each writer is confined to its own region.
    let cover ← B.heapBufDyn nTotalG
    let spCover ← val (cover * lxSlotsG)  -- the leanSPHINCS region
    -- byte_bits[g^v] = v, read at a hinted byte's exponent (sp_from_bytes, da_verify).
    let byteBits ← B.heapBuf SP_BYTE_VALUES
    for v_k in [0:SP_BYTE_VALUES] do
      byteBits[GEN ^ v_k] := lit v_k
    -- The chain indices a leanXMSS chain step hashes after its value, those no other cell holds (`walk`), set once here and carried through the signature loop.
    let lxTags ← B.stackBuf LX_N_TAGS
    for i in [1:LX_V] do
      if arrInt LX_TAG_SLOT i ≠ 0 then
        lxTags[arrInt LX_TAG_SLOT i - 1] := lit i
    B.loopRtF 0 (pure nRawXG) 54 (pure ([lxSlotsG.v, cover.v, lxTable.v] ++ lxTags)) fun xi caps => do
      let lxSlotsG := caps[0]
      let cover := caps[1]
      let lxTable := caps[2]
      let lxTags := caps[3:3 + 51]
      let idx ← hinted (B.witnessCell "raw_index")
      -- The runtime bound is small by `assert_gpow(n_total_g)` above (its log below the memory size). Without it this degenerates to what DEREF alone gives and an index could reach past `cover`, which is the whole bijection. The bound is the leanXMSS region, so a raw leanXMSS signature covers no leanSPHINCS claim.
      let t0 ← val (lxSlotsG * ofK gInv)
      let _ ← B.rangeCheckK idx t0
      cover[idx] := xi
      verifyLeanXmss (← val (lxTable * idx ^ 4)) lxTags
    B.loopRtF 0 (pure nRawSG) 5 (pure ([leanSphincsSlotsG.v, spCover.v, nRawXG.v, leanSphincsTable.v, byteBits.v])) fun xj caps => do
      let leanSphincsSlotsG := caps[0]
      let spCover := caps[1]
      let nRawXG := caps[2]
      let leanSphincsTable := caps[3]
      let byteBits := caps[4]
      let offHint ← hinted (B.witnessCell "sp_raw_index")
      let t0 ← val (leanSphincsSlotsG * ofK gInv)
      let _ ← B.rangeCheckK offHint t0
      let t1 ← val (nRawXG * xj)
      spCover[offHint] := t1
      call "verify_sig_lean_sphincs" [leanSphincsTable * offHint ^ 4, byteBits]
      pure ()
    -- ---- data availability ---- One DA digest per child, read off its statement below, then the node's own:
    -- H(root, challenge) of its blob matrix, or zeros without blobs.
    let daDigests ← B.heapBufDyn (← val ((nChildrenG * GEN) ^ 2))
    let ownDa ← val (daDigests * nChildrenG ^ 2)
    let t2 ← val (nDirectDaG + GEN)
    let _ ← B.ite t2
      (do
        let t3 ← callN "da_verify" [byteBits] 3
        let root0 := t3[0]!
        let root1 := t3[1]!
        let z := t3[2]!
        B.keccak [root0, root1] (.words [.cell z.v, .zero]) (.heap ownDa.v 0 2))
      (do
        ownDa[GEN ^ 0] := 0
        ownDa[GEN ^ 1] := 0)
    -- ---- children ----
    let childPi ← B.heapBufDyn (← val (nChildrenG * nChildrenG))
    let childFresh ← B.heapBufDyn (← val (nChildrenG ^ DEFER_SIZE))
    let childCarried ← B.heapBufDyn (← val (nChildrenG ^ DEFER_STMT_CELLS))
    let written ← B.heapBufDyn (← val (nChildrenG * GEN))  -- loop-carried write count, one per child
    written[GEN ^ 0] := nRawXG * nRawSG
    B.loopRtF 0 (pure nChildrenG) 14 (pure ([written.v, lxTable.v, cover.v, lxSlotsG.v, leanSphincsTable.v, spCover.v, leanSphincsSlotsG.v, childCarried.v, daDigests.v, seed0.v, seed1.v, childPi.v, gSquares.v, childFresh.v])) fun xc caps => do
      let written := caps[0]
      let lxTable := caps[1]
      let cover := caps[2]
      let lxSlotsG := caps[3]
      let leanSphincsTable := caps[4]
      let spCover := caps[5]
      let leanSphincsSlotsG := caps[6]
      let childCarried := caps[7]
      let daDigests := caps[8]
      let seed0 := caps[9]
      let seed1 := caps[10]
      let childPi := caps[11]
      let gSquares := caps[12]
      let childFresh := caps[13]
      let base ← val written[xc]
      -- The child's two list lengths, then its two lists, rebuilt from THIS node's tables through hinted indices: everything hinted there is pinned by the list digests, which the child's statement carries, so a lie about any of it changes the public input its proof has to satisfy.
      let childMeta ← B.stackBuf 2
      B.witness "child_meta" (.stack childMeta)  -- n_lean_xmss, n_lean_sphincs
      let nsubXG := childMeta[0]
      let nsubSG := childMeta[1]
      let _ ← B.assertGpow nsubXG
      let _ ← B.assertGpow nsubSG
      let nsubG ← val (nsubXG * nsubSG)
      let t0 ← callN "child_claim_list_digest" [lxTable, cover, base, lxSlotsG, nsubXG] 2
      let cx0 := t0[0]!
      let cx1 := t0[1]!
      let t1 ← callN "child_claim_list_digest" [leanSphincsTable, spCover, base * nsubXG, leanSphincsSlotsG, nsubSG] 2
      let cs0 := t1[0]!
      let cs1 := t1[1]!
      let carried ← val (childCarried * xc ^ DEFER_STMT_CELLS)
      B.witness "child_defer" (.heap carried.v 0 DEFER_STMT_CELLS)
      let childDa ← val (daDigests * xc ^ 2)
      B.witness "child_da" (.heap childDa.v 0 2)
      let t2 ← callN "statement_digest" [seed0, seed1, cx0, cx1, cs0, cs1, childDa[GEN ^ 0], childDa[GEN ^ 1], carried] 2
      let pi0 := t2[0]!
      let pi1 := t2[1]!
      let pi ← val (xc * xc)
      childPi[pi] := pi0
      childPi[GEN ^ 1 * pi] := pi1
      call "verify_sub" [pi0, pi1, seed0, seed1, gSquares, childFresh * xc ^ DEFER_SIZE]
      let t3 ← val (base * nsubG)
      written[GEN ^ 1 * xc] := t3
    assert written[nChildrenG] == nTotalG
    -- The published DA digest: a child's or the node's own, its own if it has blobs.
    let daPick ← hinted (B.witnessCell "da_pick")
    let t4 ← B.shifted nChildrenG (1 - 1)
    let _ ← B.rangeCheckK daPick t4
    assert (daPick + nChildrenG) * (nDirectDaG + 1) == 0
    let da ← val (daDigests * daPick ^ 2)
    -- ---- this node's own deferred claim ----
    let deferStmt ← B.heapBuf DEFER_STMT_CELLS
    let t5 ← val (nChildrenG + 1)
    let _ ← B.ite t5
      (do
        -- A leaf has nothing to batch, so it defers the bytecode at the all-zeros point. The value rides a hint and is checked nowhere here: the outer verifier recomputes it and rebuilds the statement, so a lie changes the public input rather than the claim.
        let leafValue ← hinted (B.witnessCell "leaf_defer")
        for k in [0:BYTECODE_VARS] do
          deferStmt[GEN ^ k] := 0
        deferStmt[GEN ^ DEFER_STMT_BC_VALUE] := leafValue)
      (do
        call "aggregate_claims" [nChildrenG, childPi, childFresh, childCarried, deferStmt, gSquares * GEN ^ WIN_TAB_AT]
        pure ())
    let t6 ← callN "statement_digest" [seed0, seed1, xd0, xd1, sd0, sd1, da[GEN ^ 0], da[GEN ^ 1], deferStmt] 2
    let own0 := t6[0]!
    let own1 := t6[1]!
    let pubPtr : GPow := ⟨0⟩
    assert B.load (← val (GEN ^ pubPtr.exp)) 0 == own0
    assert B.load (← B.mul (← val (GEN ^ pubPtr.exp)) (← val GEN)) 0 == own1
    return []

set_option maxHeartbeats 4000000 in
/-- Every child contributes two claims on the stacked bytecode: the one IT deferred (carried in its statement) and the fresh one raised by verifying its proof. A fresh transcript binds all of them, samples the batching coefficient, and one sumcheck reduces the lot to one claim, which is what the node then defers in its own statement. -/
def aggregateClaims : GFn where
  name := "aggregate_claims"
  arity := 6
  rets := 0
  body ps := do
    let nChildrenG := ps[0]
    let childPi := ps[1]
    let childFresh := ps[2]
    let childCarried := ps[3]
    let deferStmt := ps[4]
    let tabs := ps[5]
    let bcMsgs ← B.heapBuf 47  -- the batching challenge's nonce, then a round's words
    B.witness "bc_sumcheck_msgs" (.heap bcMsgs.v 0 (BC_LAM_WORDS + BC_ROUND_WORDS * BYTECODE_VARS))
    let bytecodeStar ← hinted (B.witnessCell "bc_star_hint")
    -- ---- one transcript over every child's statement and both its claim sets ---- The count, padded to a full rate, then each child's words, padded likewise: a child starts by permuting the full rate the previous one left waiting, which every record carries (PEND_SLOTS) beside its capacity.
    let freshRow ← B.heapBufDyn nChildrenG
    let carriedRow ← B.heapBufDyn nChildrenG
    let t0 ← B.stackBuf 5
    t0[0] := lit AGG_SEED_0
    t0[1] := lit AGG_SEED_1
    t0[2] := lit AGG_SEED_2
    t0[3] := lit AGG_SEED_3
    t0[4] := lit AGG_SEED_4
    let seed := t0
    let rate ← B.stackBuf 8
    fsPack rate 0 (FW.w nChildrenG) DS_OBSERVE
    for j in [1:4] do
      fsPack rate j (FW.c (lit 0)) DS_OBSERVE
    let absorb ← B.heapBufDyn (← val ((nChildrenG * GEN) ^ PEND_SLOTS))
    for j in [0:FS_CELLS] do
      absorb[GEN ^ j] := seed[j]
    for j in [0:8] do
      absorb[GEN ^ (FS_CELLS + j)] := rate[j]
    B.loopRtF 0 (pure nChildrenG) 6 (pure ([absorb.v, childFresh.v, freshRow.v, childCarried.v, carriedRow.v, childPi.v])) fun xc caps => do
      let absorb := caps[0]
      let childFresh := caps[1]
      let freshRow := caps[2]
      let childCarried := caps[3]
      let carriedRow := caps[4]
      let childPi := caps[5]
      let row ← val (absorb * xc ^ PEND_SLOTS)
      let rowCap ← fsLoad row 0 1
      let mut st ← fsPermPending rowCap row FS_CELLS
      let mut rate ← B.stackBuf 8
      let pi ← val (xc * xc)
      let fresh ← val (childFresh * xc ^ DEFER_SIZE)
      freshRow[xc] := fresh
      let carried ← val (childCarried * xc ^ DEFER_STMT_CELLS)
      carriedRow[xc] := carried
      for pos in [0:AGG_CHILD_WORDS + AGG_CHILD_PAD] do
        if pos % 4 = 0 then
          if pos ≠ 0 then
            st ← fsPerm st rate 4
            rate ← B.stackBuf 8
        if pos / 2 = 0 then
          fsPack rate (pos % 4) (← fold childPi[GEN ^ pos * pi]) DS_OBSERVE
        if pos / 2 ≠ 0 then
          if (pos - 2) / DEFER_SIZE = 0 then
            fsPack rate (pos % 4) (← fold fresh[GEN ^ (pos - 2)]) DS_OBSERVE
          if (pos - 2) / DEFER_SIZE ≠ 0 then
            if (pos - 2 - 24) / 24 = 0 then
              fsPack rate (pos % 4) (← fold carried[GEN ^ (pos - 2 - DEFER_SIZE)]) DS_OBSERVE
            if (pos - 2 - 24) / 24 ≠ 0 then
              fsPack rate (pos % 4) (FW.c (lit 0)) DS_OBSERVE
      let nxt : Shifted := ⟨row, PEND_SLOTS⟩
      fsStore nxt 0 1 st
      for j in [0:8] do
        nxt[GEN ^ (FS_CELLS + j)] := rate[j]
    let absorbed ← val (absorb * nChildrenG ^ PEND_SLOTS)
    -- ---- the batching sumcheck (BYTECODE_VARS variables, 2 claims per child) ---- One challenge lam, after a grind whose nonce follows the last full rate: child i's fresh claim takes lam^(2i), its carried one lam^(2i+1). Fresh and carried share one layout (point, then value), so the two differ only in which buffer they come from. Each record holds the child's power of lam^2, then the running value.
    let absorbedCap ← fsLoad absorbed 0 1
    let full ← fsPermPending absorbedCap absorbed FS_CELLS
    let mut st : List V := default
    if BATCH_LAM_GRIND_BITS = 0 then
      st := full
    else
      let nonceRate ← B.stackBuf 8
      st ← fsAbsorbNonce full nonceRate 0 (← val bcMsgs[GEN ^ 0])
      call (instName "grind_check" [.L BATCH_LAM_GRIND_BITS]) [st[1], tabs]
      pure ()
    let lam := st[0]
    let lamSq ← val (lam * lam)
    let bcChain ← B.heapBufDyn (← val ((nChildrenG * GEN) ^ PAIR_SLOTS))
    bcChain[GEN ^ 0] := 1
    bcChain[GEN ^ 1] := 0
    B.loopRtF 0 (pure nChildrenG) 5 (pure ([bcChain.v, freshRow.v, carriedRow.v, lamSq.v, lam.v])) fun xc caps => do
      let bcChain := caps[0]
      let freshRow := caps[1]
      let carriedRow := caps[2]
      let lamSq := caps[3]
      let lam := caps[4]
      let row ← val (bcChain * xc ^ PAIR_SLOTS)
      let lamPow ← val row[GEN ^ 0]
      let fresh ← val freshRow[xc]
      let carried ← val carriedRow[xc]
      let nxt : Shifted := ⟨row, PAIR_SLOTS⟩
      nxt[GEN ^ 0] := lamPow * lamSq
      nxt[GEN ^ 1] := row[GEN ^ 1] + lamPow * (fresh[GEN ^ 23] + lam * carried[GEN ^ 23])
    let bcEnd ← val (bcChain * nChildrenG ^ PAIR_SLOTS)
    let bcRunning ← val bcEnd[GEN ^ 1]
    let bcPoint ← B.heapBuf BYTECODE_VARS
    let t1 ← callN (instName "batch_sumcheck" [.L BYTECODE_VARS]) [st[8], st[9], st[10], st[11], st[12], bcMsgs * GEN ^ BC_LAM_WORDS, bcRunning, bcPoint, tabs] 6
    let fs0 := t1[0]!
    let fs1 := t1[1]!
    let fs2 := t1[2]!
    let fs3 := t1[3]!
    let fs4 := t1[4]!
    let bcRunning := t1[5]!
    let bcPoint1 ← B.heapBuf BYTECODE_VARS  -- 1 + bc_point, so an eq factor is one XOR
    for k in [0:BYTECODE_VARS] do
      bcPoint1[GEN ^ k] := 1 + bcPoint[GEN ^ k]
    let bcWsum ← B.heapBufDyn (← val (nChildrenG * GEN))
    bcWsum[GEN ^ 0] := 0
    B.loopRtF 0 (pure nChildrenG) 6 (pure ([freshRow.v, carriedRow.v, bcPoint1.v, bcChain.v, bcWsum.v, lam.v])) fun xc caps => do
      let freshRow := caps[0]
      let carriedRow := caps[1]
      let bcPoint1 := caps[2]
      let bcChain := caps[3]
      let bcWsum := caps[4]
      let lam := caps[5]
      let fresh ← val freshRow[xc]
      let carried ← val carriedRow[xc]
      let mut eqFresh : Word := default
      let mut eqCarried : Word := default
      for k in [0:BYTECODE_VARS] do
        let rk1 ← val bcPoint1[GEN ^ k]
        if k = 0 then
          eqFresh ← val (fresh[GEN ^ k] + rk1)
          eqCarried ← val (carried[GEN ^ k] + rk1)
        else
          eqFresh ← val (eqFresh * (fresh[GEN ^ k] + rk1))
          eqCarried ← val (eqCarried * (carried[GEN ^ k] + rk1))
      let row ← val (bcChain * xc ^ PAIR_SLOTS)
      let t0 ← val (bcWsum[xc] + row[GEN ^ 0] * (eqFresh + lam * eqCarried))
      bcWsum[GEN ^ 1 * xc] := t0
    assert bcRunning == bytecodeStar * bcWsum[nChildrenG]
    for k in [0:BYTECODE_VARS] do
      deferStmt[GEN ^ k] := bcPoint[GEN ^ k]
    deferStmt[GEN ^ DEFER_STMT_BC_VALUE] := bytecodeStar
    return []

end
end LeanVM.Guest.Program
