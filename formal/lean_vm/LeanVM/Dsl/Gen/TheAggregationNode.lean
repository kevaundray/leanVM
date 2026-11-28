/-
  LeanVM.Dsl.Gen.TheAggregationNode

  The guest's section `TheAggregationNode`, translated.
-/

module

public import LeanVM.Dsl.Gen.Inline

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

set_option linter.unusedVariables false in
/-- `main` (`guests/lean_ethereum.py`, line 4702):

```
def main():
    # One node of an aggregation tree: n_raw_lean_xmss leanXMSS signatures, n_raw_lean_sphincs
    # leanSPHINCS signatures and n_children sub-proofs OF THIS SAME BYTECODE. A claim of
    # either scheme is a pubkey and the message it signed, and each signature is
    # verified against the claim in its own coverage slot; a leanXMSS signature carries
    # its own leaf index. It publishes at most one DA digest: that of the blob matrix it
    # checks, or one of its children's, or none.
    #
    # The declared lists are what the node publishes; the duplicate slots absorb claims a
    # child covers that the set does not declare. The coverage table is one region
    # per scheme, each its declared claims then its own duplicates:
    #
    #   [leanXMSS: declared | dup][leanSPHINCS: declared | dup]
    #
    # so one range check per write keeps each writer inside its own region: that is
    # what makes the statement's split mean which scheme verified which claim. A
    # slot is four cells, a pubkey and the message that pubkey signed.
    meta = StackBuf(8)
    hint_witness(meta, "meta")  # every count in the exponent
    n_lx_g = meta[0]
    n_xdup_g = meta[1]
    n_raw_x_g = meta[2]
    n_lean_sphincs_g = meta[3]
    n_sdup_g = meta[4]
    n_raw_s_g = meta[5]
    n_children_g = meta[6]
    n_direct_da_g = meta[7]
    assert_gpow(n_lx_g)
    assert_gpow(n_xdup_g)
    assert_gpow(n_raw_x_g)
    assert_gpow(n_lean_sphincs_g)
    assert_gpow(n_sdup_g)
    assert_gpow(n_raw_s_g)
    assert log(n_children_g) < MAX_RECURSIONS + 1
    assert log(n_direct_da_g) < 2
    lx_slots_g = n_lx_g * n_xdup_g
    lean_sphincs_slots_g = n_lean_sphincs_g * n_sdup_g
    # The sum of both regions bounds the coverage indices, so it is what has to be a
    # memory address: its log is then below 2^30 and the runtime bounds below mean
    # what they say. An honest node holds its coverage table in memory, so it fits.
    n_total_g = lx_slots_g * lean_sphincs_slots_g
    assert_gpow(n_total_g)

    # The proving environment (the proof system's version and this bytecode) as one
    # digest. It rides the statement rather than the bytecode, so nothing here has to
    # know its own hash; the outer verifier pins it, and every child statement rebuilt
    # below copies it, which is what keeps a whole tree on one bytecode.
    fs_seed = StackBuf(2)
    hint_witness(fs_seed, "fs_seed")
    seed_0 = fs_seed[0]
    seed_1 = fs_seed[1]

    # ---- the claim lists ----
    g_squares = exponent_tables()

    # One table per scheme: its declared list (strictly sorted, checked by the outer
    # verifier, which holds it) followed by its own duplicate slots. The coverage
    # indices below run over one space: leanXMSS, then leanSPHINCS.
    #
    # Each list's digest is a plain hash of its claims, 64 bytes a claim, its padding
    # binding its length; the statement carries the two digests side by side.
    lx_table = HeapBuf(lx_slots_g ** 4)
    lean_sphincs_table = HeapBuf(lean_sphincs_slots_g ** 4)
    xd_0, xd_1 = claim_list_digest(lx_table, n_lx_g)
    sd_0, sd_1 = claim_list_digest(lean_sphincs_table, n_lean_sphincs_g)
    # The duplicate slots ride the same tables but outside the hashed prefixes.
    for xd in mul_range(1, n_xdup_g):
        dup = lx_table * ((n_lx_g * xd) ** 4)
        hint_witness(dup[0:4], "dup_claims")
    for xd in mul_range(1, n_sdup_g):
        dup = lean_sphincs_table * ((n_lean_sphincs_g * xd) ** 4)
        hint_witness(dup[0:4], "dup_claims")

    # ---- coverage ----
    # Every one of the n_total slots is written exactly once: write-once memory
    # rejects a second write (each writer's marks lie in its own range of counts, and a
    # gap-walked child list never revisits a slot, so two writes to one slot disagree),
    # and the count below rejects a missed one. So every
    # declared claim is covered by a direct check of its own kind or by a verified
    # child. Each writer is confined to its own region.
    cover = HeapBuf(n_total_g)
    sp_cover = cover * lx_slots_g  # the leanSPHINCS region
    # byte_bits[g^v] = v, read at a hinted byte's exponent (sp_from_bytes, da_verify).
    byte_bits = HeapBuf(SP_BYTE_VALUES)
    for v in unroll(0, SP_BYTE_VALUES):
        byte_bits[GEN ** v] = v
    # The chain indices a leanXMSS chain step hashes after its value, those no other
    # cell holds (`walk`), set once here and carried through the signature loop.
    lx_tags = StackBuf(LX_N_TAGS)
    for i in unroll(1, LX_V):
        if const(LX_TAG_SLOT[i] != 0):
            lx_tags[LX_TAG_SLOT[i] - 1] = i
    for xi in mul_range(1, n_raw_x_g):
        idx = hint_witness("raw_index")
        # The runtime bound is small by `assert_gpow(n_total_g)` above (its log below
        # the memory size). Without it this degenerates to what DEREF alone gives and an
        # index could reach past `cover`, which is the whole bijection. The bound is the
        # leanXMSS region, so a raw leanXMSS signature covers no leanSPHINCS claim.
        assert log(idx) < log(lx_slots_g)
        cover[idx] = xi
        verify_lean_xmss(lx_table * (idx ** 4), lx_tags)
    for xj in mul_range(1, n_raw_s_g):
        off_hint = hint_witness("sp_raw_index")
        assert log(off_hint) < log(lean_sphincs_slots_g)
        sp_cover[off_hint] = n_raw_x_g * xj
        verify_sig_lean_sphincs(lean_sphincs_table * (off_hint ** 4), byte_bits)

    # ---- data availability ----
    # One DA digest per child, read off its statement below, then the node's own:
    # H(root, challenge) of its blob matrix, or zeros without blobs.
    da_digests = HeapBuf((n_children_g * GEN) ** 2)
    own_da = da_digests * n_children_g ** 2
    if n_direct_da_g == GEN:
        root_0, root_1, z = da_verify(byte_bits)
        keccak([root_0, root_1], [z, 0], own_da[0:2])
    else:
        own_da[1] = 0
        own_da[GEN] = 0

    # ---- children ----
    child_pi = HeapBuf(n_children_g * n_children_g)
    child_fresh = HeapBuf(n_children_g ** DEFER_SIZE)
    child_carried = HeapBuf(n_children_g ** DEFER_STMT_CELLS)
    written = HeapBuf(n_children_g * GEN)  # loop-carried write count, one per child
    written[GEN ** 0] = n_raw_x_g * n_raw_s_g
    for xc in mul_range(1, n_children_g):
        base = written[xc]
        # The child's two list lengths, then its two lists, rebuilt from THIS node's
        # tables through hinted indices: everything hinted there is pinned by the
        # list digests, which the child's statement carries, so a lie about any of it
        # changes the public input its proof has to satisfy.
        child_meta = StackBuf(2)
        hint_witness(child_meta, "child_meta")  # n_lean_xmss, n_lean_sphincs
        nsub_x_g = child_meta[0]
        nsub_s_g = child_meta[1]
        assert_gpow(nsub_x_g)
        assert_gpow(nsub_s_g)
        nsub_g = nsub_x_g * nsub_s_g
        cx_0, cx_1 = child_claim_list_digest(lx_table, cover, base, lx_slots_g, nsub_x_g)
        cs_0, cs_1 = child_claim_list_digest(lean_sphincs_table, sp_cover, base * nsub_x_g, lean_sphincs_slots_g, nsub_s_g)
        carried = child_carried * xc ** DEFER_STMT_CELLS
        hint_witness(carried[0:DEFER_STMT_CELLS], "child_defer")
        child_da = da_digests * xc ** 2
        hint_witness(child_da[0:2], "child_da")
        pi_0, pi_1 = statement_digest(seed_0, seed_1, cx_0, cx_1, cs_0, cs_1, child_da[1], child_da[GEN], carried)
        pi = xc * xc
        child_pi[pi] = pi_0
        child_pi[pi * GEN] = pi_1
        verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, child_fresh * xc ** DEFER_SIZE)
        written[xc * GEN] = base * nsub_g
    assert written[n_children_g] == n_total_g

    # The published DA digest: a child's or the node's own, its own if it has blobs.
    da_pick = hint_witness("da_pick")
    assert log(da_pick) < log(n_children_g * GEN)
    assert (da_pick + n_children_g) * (n_direct_da_g + 1) == 0
    da = da_digests * da_pick ** 2

    # ---- this node's own deferred claim ----
    defer_stmt = HeapBuf(DEFER_STMT_CELLS)
    if n_children_g == 1:
        # A leaf has nothing to batch, so it defers the bytecode at the all-zeros
        # point. The value rides a hint and is checked nowhere here: the outer
        # verifier recomputes it and rebuilds the statement, so a lie changes the
        # public input rather than the claim.
        leaf_value = hint_witness("leaf_defer")
        for k in unroll(0, BYTECODE_VARS):
            defer_stmt[GEN ** k] = 0
        defer_stmt[GEN ** DEFER_STMT_BC_VALUE] = leaf_value
    else:
        aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt, g_squares * GEN ** WIN_TAB_AT)

    own_0, own_1 = statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da[1], da[GEN], defer_stmt)
    pub_ptr = GEN ** 0
    assert pub_ptr[1] == own_0
    assert pub_ptr[GEN] == own_1
    return
```
-/
def main : GFn where
  name := "main"
  arity := 0
  rets := 0
  body ps := do
    let meta' ← B.stackBuf 8
    B.witness "meta" (.stack meta')
    let nLxG := cellOf meta' 0
    let nXdupG := cellOf meta' 1
    let nRawXG := cellOf meta' 2
    let nLeanSphincsG := cellOf meta' 3
    let nSdupG := cellOf meta' 4
    let nRawSG := cellOf meta' 5
    let nChildrenG := cellOf meta' 6
    let nDirectDaG := cellOf meta' 7
    let _ ← B.assertGpow nLxG
    let _ ← B.assertGpow nXdupG
    let _ ← B.assertGpow nRawXG
    let _ ← B.assertGpow nLeanSphincsG
    let _ ← B.assertGpow nSdupG
    let _ ← B.assertGpow nRawSG
    let _ ← B.rangeCheck nChildrenG 17
    let _ ← B.rangeCheck nDirectDaG 2
    let lxSlotsG ← B.mul nLxG nXdupG
    let leanSphincsSlotsG ← B.mul nLeanSphincsG nSdupG
    let nTotalG ← B.mul lxSlotsG leanSphincsSlotsG
    let _ ← B.assertGpow nTotalG
    let fsSeed ← B.stackBuf 2
    B.witness "fs_seed" (.stack fsSeed)
    let seed0 := cellOf fsSeed 0
    let seed1 := cellOf fsSeed 1
    let gSquares ← call1 "exponent_tables" []
    let lxTable ← B.heapBufDyn (← B.pow lxSlotsG 4)
    let leanSphincsTable ← B.heapBufDyn (← B.pow leanSphincsSlotsG 4)
    let t0 ← B.call "claim_list_digest" [lxTable.v, nLxG.v] 2
    let xd0 := t0[0]!
    let xd1 := t0[1]!
    let t1 ← B.call "claim_list_digest" [leanSphincsTable.v, nLeanSphincsG.v] 2
    let sd0 := t1[0]!
    let sd1 := t1[1]!
    B.loopRtF 0 (pure nXdupG) 2 (pure ([lxTable.v, nLxG.v])) fun xd caps => do
      let lxTable := cellOf caps 0
      let nLxG := cellOf caps 1
      let dup ← B.mul lxTable (← B.pow (← B.mul nLxG xd) 4)
      B.witness "dup_claims" (.heap dup.v 0 4)
    B.loopRtF 0 (pure nSdupG) 2 (pure ([leanSphincsTable.v, nLeanSphincsG.v])) fun xd caps => do
      let leanSphincsTable := cellOf caps 0
      let nLeanSphincsG := cellOf caps 1
      let dup ← B.mul leanSphincsTable (← B.pow (← B.mul nLeanSphincsG xd) 4)
      B.witness "dup_claims" (.heap dup.v 0 4)
    let cover ← B.heapBufDyn nTotalG
    let spCover ← B.mul cover lxSlotsG
    let byteBits ← B.heapBuf SP_BYTE_VALUES
    for v_k in [0:SP_BYTE_VALUES] do
      B.store byteBits v_k (← B.const (lit v_k))
    let lxTags ← B.stackBuf LX_N_TAGS
    for i_k in [1:LX_V] do
      if (arrInt LX_TAG_SLOT i_k) ≠ 0 then
        B.constInto (cellOf lxTags ((arrInt LX_TAG_SLOT i_k) - 1)) (lit i_k)
      else
        pure ()
    B.loopRtF 0 (pure nRawXG) 54 (pure ([lxSlotsG.v, cover.v, lxTable.v] ++ lxTags)) fun xi caps => do
      let lxSlotsG := cellOf caps 0
      let cover := cellOf caps 1
      let lxTable := cellOf caps 2
      let lxTags := (caps.drop 3).take 51
      let idx ← hinted (B.witnessCell "raw_index")
      let t0 ← B.mul lxSlotsG (← B.const (ofK gInv))
      let _ ← B.rangeCheckK idx t0
      B.store (← B.mul cover idx) 0 xi
      verifyLeanXmss (← B.mul lxTable (← B.pow idx 4)) lxTags
    B.loopRtF 0 (pure nRawSG) 5 (pure ([leanSphincsSlotsG.v, spCover.v, nRawXG.v, leanSphincsTable.v, byteBits.v])) fun xj caps => do
      let leanSphincsSlotsG := cellOf caps 0
      let spCover := cellOf caps 1
      let nRawXG := cellOf caps 2
      let leanSphincsTable := cellOf caps 3
      let byteBits := cellOf caps 4
      let offHint ← hinted (B.witnessCell "sp_raw_index")
      let t0 ← B.mul leanSphincsSlotsG (← B.const (ofK gInv))
      let _ ← B.rangeCheckK offHint t0
      let t1 ← B.mul nRawXG xj
      B.store (← B.mul spCover offHint) 0 t1
      let _ ← B.call "verify_sig_lean_sphincs" [(← B.mul leanSphincsTable (← B.pow offHint 4)).v, byteBits.v] 0
      pure ()
    let daDigests ← B.heapBufDyn (← B.pow (← B.shifted nChildrenG 1) 2)
    let ownDa ← B.mul daDigests (← B.pow nChildrenG 2)
    let t2 ← B.add nDirectDaG (← B.const (gpowE 1))
    let _ ← B.ite t2
      (do
        let t3 ← B.call "da_verify" [byteBits.v] 3
        let root0 := t3[0]!
        let root1 := t3[1]!
        let z := t3[2]!
        B.keccak (a := (.words [.cell root0.v, .cell root1.v])) (b := (.words [.cell z.v, .zero])) (out := (.heap ownDa.v 0 2)))
      (do
        B.store ownDa 0 (← B.const 0)
        B.store ownDa 1 (← B.const 0))
    let childPi ← B.heapBufDyn (← B.mul nChildrenG nChildrenG)
    let childFresh ← B.heapBufDyn (← B.pow nChildrenG DEFER_SIZE)
    let childCarried ← B.heapBufDyn (← B.pow nChildrenG DEFER_STMT_CELLS)
    let written ← B.heapBufDyn (← B.shifted nChildrenG 1)
    B.store written 0 (← B.mul nRawXG nRawSG)
    B.loopRtF 0 (pure nChildrenG) 14 (pure ([written.v, lxTable.v, cover.v, lxSlotsG.v, leanSphincsTable.v, spCover.v, leanSphincsSlotsG.v, childCarried.v, daDigests.v, seed0.v, seed1.v, childPi.v, gSquares.v, childFresh.v])) fun xc caps => do
      let written := cellOf caps 0
      let lxTable := cellOf caps 1
      let cover := cellOf caps 2
      let lxSlotsG := cellOf caps 3
      let leanSphincsTable := cellOf caps 4
      let spCover := cellOf caps 5
      let leanSphincsSlotsG := cellOf caps 6
      let childCarried := cellOf caps 7
      let daDigests := cellOf caps 8
      let seed0 := cellOf caps 9
      let seed1 := cellOf caps 10
      let childPi := cellOf caps 11
      let gSquares := cellOf caps 12
      let childFresh := cellOf caps 13
      let base ← B.load (← B.mul written xc) 0
      let childMeta ← B.stackBuf 2
      B.witness "child_meta" (.stack childMeta)
      let nsubXG := cellOf childMeta 0
      let nsubSG := cellOf childMeta 1
      let _ ← B.assertGpow nsubXG
      let _ ← B.assertGpow nsubSG
      let nsubG ← B.mul nsubXG nsubSG
      let t0 ← B.call "child_claim_list_digest" [lxTable.v, cover.v, base.v, lxSlotsG.v, nsubXG.v] 2
      let cx0 := t0[0]!
      let cx1 := t0[1]!
      let t1 ← B.call "child_claim_list_digest" [leanSphincsTable.v, spCover.v, (← B.mul base nsubXG).v, leanSphincsSlotsG.v, nsubSG.v] 2
      let cs0 := t1[0]!
      let cs1 := t1[1]!
      let carried ← B.mul childCarried (← B.pow xc DEFER_STMT_CELLS)
      B.witness "child_defer" (.heap carried.v 0 DEFER_STMT_CELLS)
      let childDa ← B.mul daDigests (← B.pow xc 2)
      B.witness "child_da" (.heap childDa.v 0 2)
      let t2 ← B.call "statement_digest" [seed0.v, seed1.v, cx0.v, cx1.v, cs0.v, cs1.v, (← B.load childDa 0).v, (← B.load childDa 1).v, carried.v] 2
      let pi0 := t2[0]!
      let pi1 := t2[1]!
      let pi ← B.mul xc xc
      B.store (← B.mul childPi pi) 0 pi0
      B.store (← B.mul childPi pi) 1 pi1
      let _ ← B.call "verify_sub" [pi0.v, pi1.v, seed0.v, seed1.v, gSquares.v, (← B.mul childFresh (← B.pow xc DEFER_SIZE)).v] 0
      let t3 ← B.mul base nsubG
      B.store (← B.mul written xc) 1 t3
    B.assertEq (← B.load (← B.mul written nChildrenG) 0) nTotalG
    let daPick ← hinted (B.witnessCell "da_pick")
    let t4 ← B.shifted nChildrenG (1 - 1)
    let _ ← B.rangeCheckK daPick t4
    B.assertEq (← B.mul (← B.add daPick nChildrenG) (← B.add nDirectDaG (← B.const 1))) (← B.const 0)
    let da ← B.mul daDigests (← B.pow daPick 2)
    let deferStmt ← B.heapBuf DEFER_STMT_CELLS
    let t5 ← B.add nChildrenG (← B.const 1)
    let _ ← B.ite t5
      (do
        let leafValue ← hinted (B.witnessCell "leaf_defer")
        for k_k in [0:BYTECODE_VARS] do
          B.store deferStmt k_k (← B.const 0)
        B.store deferStmt DEFER_STMT_BC_VALUE leafValue)
      (do
        let _ ← B.call "aggregate_claims" [nChildrenG.v, childPi.v, childFresh.v, childCarried.v, deferStmt.v, (← B.shifted gSquares WIN_TAB_AT).v] 0
        pure ())
    let t6 ← B.call "statement_digest" [seed0.v, seed1.v, xd0.v, xd1.v, sd0.v, sd1.v, (← B.load da 0).v, (← B.load da 1).v, deferStmt.v] 2
    let own0 := t6[0]!
    let own1 := t6[1]!
    let pubPtr : GPow := ⟨0⟩
    B.assertEq (← B.load (← B.const (gpowE pubPtr.exp)) 0) own0
    B.assertEq (← B.load (← B.mul (← B.const (gpowE pubPtr.exp)) (← B.const (gpowE 1))) 0) own1
    return []

set_option linter.unusedVariables false in
/-- `aggregate_claims` (`guests/lean_ethereum.py`, line 4881):

```
def aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt, tabs):
    # Every child contributes two claims on the stacked bytecode: the one IT
    # deferred (carried in its statement) and the fresh one raised by verifying its
    # proof. A fresh transcript binds all of them, samples the batching
    # coefficient, and one sumcheck reduces the lot to one claim, which is what the
    # node then defers in its own statement.
    bc_msgs = HeapBuf(BC_LAM_WORDS + BC_ROUND_WORDS * BYTECODE_VARS)  # the batching challenge's nonce, then a round's words
    hint_witness(bc_msgs[0:BC_LAM_WORDS + BC_ROUND_WORDS * BYTECODE_VARS], "bc_sumcheck_msgs")
    bytecode_star = hint_witness("bc_star_hint")

    # ---- one transcript over every child's statement and both its claim sets ----
    # The count, padded to a full rate, then each child's words, padded likewise: a
    # child starts by permuting the full rate the previous one left waiting, which
    # every record carries (PEND_SLOTS) beside its capacity.
    fresh_row = HeapBuf(n_children_g)
    carried_row = HeapBuf(n_children_g)
    seed = [AGG_SEED_0, AGG_SEED_1, AGG_SEED_2, AGG_SEED_3, AGG_SEED_4]
    rate = StackBuf(8)
    fs_pack(rate, 0, n_children_g, DS_OBSERVE)
    for j in unroll(1, 4):
        fs_pack(rate, j, 0, DS_OBSERVE)
    absorb = HeapBuf((n_children_g * GEN) ** PEND_SLOTS)
    for j in unroll(0, FS_CELLS):
        absorb[GEN ** j] = seed[j]
    for j in unroll(0, 8):
        absorb[GEN ** (FS_CELLS + j)] = rate[j]
    for xc in mul_range(1, n_children_g):
        row = absorb * xc ** PEND_SLOTS
        row_cap = fs_load(row, 0, 1)
        st = fs_perm_pending(row_cap, row, FS_CELLS)
        rate = StackBuf(8)
        pi = xc * xc
        fresh = child_fresh * xc ** DEFER_SIZE
        fresh_row[xc] = fresh
        carried = child_carried * xc ** DEFER_STMT_CELLS
        carried_row[xc] = carried
        for pos in unroll(0, AGG_CHILD_WORDS + AGG_CHILD_PAD):
            if pos % 4 == 0:
                if pos != 0:
                    st = fs_perm(st, rate, 4)
                    rate = StackBuf(8)
            if const(pos // 2 == 0):
                fs_pack(rate, pos % 4, child_pi[pi * GEN ** pos], DS_OBSERVE)
            if const(pos // 2 != 0):
                if const((pos - 2) // DEFER_SIZE == 0):
                    fs_pack(rate, pos % 4, fresh[GEN ** (pos - 2)], DS_OBSERVE)
                if const((pos - 2) // DEFER_SIZE != 0):
                    if const((pos - 2 - DEFER_SIZE) // DEFER_STMT_CELLS == 0):
                        fs_pack(rate, pos % 4, carried[GEN ** (pos - 2 - DEFER_SIZE)], DS_OBSERVE)
                    if const((pos - 2 - DEFER_SIZE) // DEFER_STMT_CELLS != 0):
                        fs_pack(rate, pos % 4, 0, DS_OBSERVE)
        nxt = row * GEN ** PEND_SLOTS
        fs_store(nxt, 0, 1, st)
        for j in unroll(0, 8):
            nxt[GEN ** (FS_CELLS + j)] = rate[j]
    absorbed = absorb * n_children_g ** PEND_SLOTS

    # ---- the batching sumcheck (BYTECODE_VARS variables, 2 claims per child) ----
    # One challenge lam, after a grind whose nonce follows the last full rate: child i's fresh
    # claim takes lam^(2i), its carried one lam^(2i+1). Fresh and carried share one
    # layout (point, then value), so the two differ only in which buffer they come
    # from. Each record holds the child's power of lam^2, then the running value.
    absorbed_cap = fs_load(absorbed, 0, 1)
    full = fs_perm_pending(absorbed_cap, absorbed, FS_CELLS)
    if const(BATCH_LAM_GRIND_BITS == 0):
        st = full
    else:
        nonce_rate = StackBuf(8)
        st = fs_absorb_nonce(full, nonce_rate, 0, bc_msgs[GEN ** 0])
        grind_check(st[1], tabs, BATCH_LAM_GRIND_BITS)
    lam = st[0]
    lam_sq = lam * lam
    bc_chain = HeapBuf((n_children_g * GEN) ** PAIR_SLOTS)
    bc_chain[GEN ** 0] = 1
    bc_chain[GEN ** 1] = 0
    for xc in mul_range(1, n_children_g):
        row = bc_chain * xc ** PAIR_SLOTS
        lam_pow = row[GEN ** 0]
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        nxt = row * GEN ** PAIR_SLOTS
        nxt[GEN ** 0] = lam_pow * lam_sq
        nxt[GEN ** 1] = row[GEN ** 1] + lam_pow * (fresh[GEN ** FRESH_BC_VALUE] + lam * carried[GEN ** DEFER_STMT_BC_VALUE])
    bc_end = bc_chain * n_children_g ** PAIR_SLOTS
    bc_running = bc_end[GEN ** 1]
    bc_point = HeapBuf(BYTECODE_VARS)
    fs0, fs1, fs2, fs3, fs4, bc_running = batch_sumcheck(st[8], st[9], st[10], st[11], st[12], bc_msgs * GEN ** BC_LAM_WORDS, bc_running, bc_point, tabs, BYTECODE_VARS)
    bc_point1 = HeapBuf(BYTECODE_VARS)  # 1 + bc_point, so an eq factor is one XOR
    for k in unroll(0, BYTECODE_VARS):
        bc_point1[GEN ** k] = 1 + bc_point[GEN ** k]
    bc_wsum = HeapBuf(n_children_g * GEN)
    bc_wsum[GEN ** 0] = 0
    for xc in mul_range(1, n_children_g):
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        for k in unroll(0, BYTECODE_VARS):
            rk1 = bc_point1[GEN ** k]
            if const(k == 0):
                eq_fresh = fresh[GEN ** k] + rk1
                eq_carried = carried[GEN ** k] + rk1
            else:
                eq_fresh *= fresh[GEN ** k] + rk1
                eq_carried *= carried[GEN ** k] + rk1
        row = bc_chain * xc ** PAIR_SLOTS
        bc_wsum[xc * GEN] = bc_wsum[xc] + row[GEN ** 0] * (eq_fresh + lam * eq_carried)
    assert bc_running == bytecode_star * bc_wsum[n_children_g]

    for k in unroll(0, BYTECODE_VARS):
        defer_stmt[GEN ** k] = bc_point[GEN ** k]
    defer_stmt[GEN ** DEFER_STMT_BC_VALUE] = bytecode_star
    return
```
-/
def aggregateClaims : GFn where
  name := "aggregate_claims"
  arity := 6
  rets := 0
  body ps := do
    let nChildrenG := cellOf ps 0
    let childPi := cellOf ps 1
    let childFresh := cellOf ps 2
    let childCarried := cellOf ps 3
    let deferStmt := cellOf ps 4
    let tabs := cellOf ps 5
    let bcMsgs ← B.heapBuf 47
    B.witness "bc_sumcheck_msgs" (.heap bcMsgs.v 0 (BC_LAM_WORDS + (BC_ROUND_WORDS * BYTECODE_VARS)))
    let bytecodeStar ← hinted (B.witnessCell "bc_star_hint")
    let freshRow ← B.heapBufDyn nChildrenG
    let carriedRow ← B.heapBufDyn nChildrenG
    let t0 ← B.stackBuf 5
    B.constInto (cellOf t0 0) (lit AGG_SEED_0)
    B.constInto (cellOf t0 1) (lit AGG_SEED_1)
    B.constInto (cellOf t0 2) (lit AGG_SEED_2)
    B.constInto (cellOf t0 3) (lit AGG_SEED_3)
    B.constInto (cellOf t0 4) (lit AGG_SEED_4)
    let seed := t0
    let rate ← B.stackBuf 8
    fsPack rate 0 nChildrenG DS_OBSERVE
    for j_k in [1:4] do
      fsPack_2 rate j_k 0 DS_OBSERVE
    let absorb ← B.heapBufDyn (← B.pow (← B.shifted nChildrenG 1) PEND_SLOTS)
    for j_k in [0:FS_CELLS] do
      B.store absorb j_k (cellOf seed j_k)
    for j_k in [0:8] do
      B.store absorb (FS_CELLS + j_k) (cellOf rate j_k)
    B.loopRtF 0 (pure nChildrenG) 6 (pure ([absorb.v, childFresh.v, freshRow.v, childCarried.v, carriedRow.v, childPi.v])) fun xc caps => do
      let absorb := cellOf caps 0
      let childFresh := cellOf caps 1
      let freshRow := cellOf caps 2
      let childCarried := cellOf caps 3
      let carriedRow := cellOf caps 4
      let childPi := cellOf caps 5
      let row ← B.mul absorb (← B.pow xc PEND_SLOTS)
      let rowCap ← fsLoad row 0 1
      let mut st ← fsPermPending rowCap row FS_CELLS
      let mut rate ← B.stackBuf 8
      let pi ← B.mul xc xc
      let fresh ← B.mul childFresh (← B.pow xc DEFER_SIZE)
      B.store (← B.mul freshRow xc) 0 fresh
      let carried ← B.mul childCarried (← B.pow xc DEFER_STMT_CELLS)
      B.store (← B.mul carriedRow xc) 0 carried
      for pos_k in [0:AGG_CHILD_WORDS + AGG_CHILD_PAD] do
        if (pos_k % 4) = 0 then
          if pos_k ≠ 0 then
            st ← fsPerm st rate 4
            rate ← B.stackBuf 8
          else
            pure ()
        else
          pure ()
        if (pos_k / 2) = 0 then
          fsPack rate (pos_k % 4) (← B.load (← B.mul childPi pi) pos_k) DS_OBSERVE
        else
          pure ()
        if (pos_k / 2) ≠ 0 then
          if ((pos_k - 2) / DEFER_SIZE) = 0 then
            fsPack rate (pos_k % 4) (← B.load fresh (pos_k - 2)) DS_OBSERVE
          else
            pure ()
          if ((pos_k - 2) / DEFER_SIZE) ≠ 0 then
            if (((pos_k - 2) - 24) / 24) = 0 then
              fsPack rate (pos_k % 4) (← B.load carried ((pos_k - 2) - DEFER_SIZE)) DS_OBSERVE
            else
              pure ()
            if (((pos_k - 2) - 24) / 24) ≠ 0 then
              fsPack_2 rate (pos_k % 4) 0 DS_OBSERVE
            else
              pure ()
          else
            pure ()
        else
          pure ()
      let nxt : Shifted := ⟨row, PEND_SLOTS⟩
      fsStore (⟨nxt.base, nxt.exp⟩) 0 1 st
      for j_k in [0:8] do
        B.store nxt.base (nxt.exp + (FS_CELLS + j_k)) (cellOf rate j_k)
    let absorbed ← B.mul absorb (← B.pow nChildrenG PEND_SLOTS)
    let absorbedCap ← fsLoad absorbed 0 1
    let full ← fsPermPending absorbedCap absorbed FS_CELLS
    let mut st : List V := default
    if BATCH_LAM_GRIND_BITS = 0 then
      pure () -- no use of this definition takes this branch
    else
      let nonceRate ← B.stackBuf 8
      st ← fsAbsorbNonce full nonceRate 0 (← B.load bcMsgs 0)
      let _ ← B.call (instName "grind_check" [.L BATCH_LAM_GRIND_BITS]) [(cellOf st 1).v, tabs.v] 0
      pure ()
    let lam := cellOf st 0
    let lamSq ← B.mul lam lam
    let bcChain ← B.heapBufDyn (← B.pow (← B.shifted nChildrenG 1) PAIR_SLOTS)
    B.store bcChain 0 (← B.const 1)
    B.store bcChain 1 (← B.const 0)
    B.loopRtF 0 (pure nChildrenG) 5 (pure ([bcChain.v, freshRow.v, carriedRow.v, lamSq.v, lam.v])) fun xc caps => do
      let bcChain := cellOf caps 0
      let freshRow := cellOf caps 1
      let carriedRow := cellOf caps 2
      let lamSq := cellOf caps 3
      let lam := cellOf caps 4
      let row ← B.mul bcChain (← B.pow xc PAIR_SLOTS)
      let lamPow ← B.load row 0
      let fresh ← B.load (← B.mul freshRow xc) 0
      let carried ← B.load (← B.mul carriedRow xc) 0
      let nxt : Shifted := ⟨row, PAIR_SLOTS⟩
      B.store nxt.base nxt.exp (← B.mul lamPow lamSq)
      B.store nxt.base (nxt.exp + 1) (← B.add (← B.load row 1) (← B.mul lamPow (← B.add (← B.load fresh 23) (← B.mul lam (← B.load carried 23)))))
    let bcEnd ← B.mul bcChain (← B.pow nChildrenG PAIR_SLOTS)
    let bcRunning ← B.load bcEnd 1
    let bcPoint ← B.heapBuf BYTECODE_VARS
    let t1 ← B.call (instName "batch_sumcheck" [.L BYTECODE_VARS]) [(cellOf st 8).v, (cellOf st 9).v, (cellOf st 10).v, (cellOf st 11).v, (cellOf st 12).v, (← B.shifted bcMsgs BC_LAM_WORDS).v, bcRunning.v, bcPoint.v, tabs.v] 6
    let fs0 := t1[0]!
    let fs1 := t1[1]!
    let fs2 := t1[2]!
    let fs3 := t1[3]!
    let fs4 := t1[4]!
    let bcRunning := t1[5]!
    let bcPoint1 ← B.heapBuf BYTECODE_VARS
    for k_k in [0:BYTECODE_VARS] do
      B.store bcPoint1 k_k (← B.add (← B.const 1) (← B.load bcPoint k_k))
    let bcWsum ← B.heapBufDyn (← B.shifted nChildrenG 1)
    B.store bcWsum 0 (← B.const 0)
    B.loopRtF 0 (pure nChildrenG) 6 (pure ([freshRow.v, carriedRow.v, bcPoint1.v, bcChain.v, bcWsum.v, lam.v])) fun xc caps => do
      let freshRow := cellOf caps 0
      let carriedRow := cellOf caps 1
      let bcPoint1 := cellOf caps 2
      let bcChain := cellOf caps 3
      let bcWsum := cellOf caps 4
      let lam := cellOf caps 5
      let fresh ← B.load (← B.mul freshRow xc) 0
      let carried ← B.load (← B.mul carriedRow xc) 0
      let mut eqFresh : Word := default
      let mut eqCarried : Word := default
      for k_k in [0:BYTECODE_VARS] do
        let rk1 ← B.load bcPoint1 k_k
        if k_k = 0 then
          eqFresh ← B.add (← B.load fresh k_k) rk1
          eqCarried ← B.add (← B.load carried k_k) rk1
        else
          eqFresh ← B.mul eqFresh (← B.add (← B.load fresh k_k) rk1)
          eqCarried ← B.mul eqCarried (← B.add (← B.load carried k_k) rk1)
      let row ← B.mul bcChain (← B.pow xc PAIR_SLOTS)
      let t0 ← B.add (← B.load (← B.mul bcWsum xc) 0) (← B.mul (← B.load row 0) (← B.add eqFresh (← B.mul lam eqCarried)))
      B.store (← B.mul bcWsum xc) 1 t0
    B.assertEq bcRunning (← B.mul bytecodeStar (← B.load (← B.mul bcWsum nChildrenG) 0))
    for k_k in [0:BYTECODE_VARS] do
      B.store deferStmt k_k (← B.load bcPoint k_k)
    B.store deferStmt DEFER_STMT_BC_VALUE bytecodeStar
    return []

end
end LeanVM.Dsl.Gen
