/-
  LeanVM.Dsl.Gen.StatementsAndTheClaimLists

  The guest's section `StatementsAndTheClaimLists`, translated.
-/

module

public import LeanVM.Dsl.Gen.Inline

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

set_option linter.unusedVariables false in
/-- `statement_digest` (`guests/lean_ethereum.py`, line 4286):

```
def statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer):
    # A node's statement, hashed to the two words the VM publishes, over the
    # proving environment's Fiat-Shamir seed (the proof system's version and this
    # bytecode), the leanXMSS and leanSPHINCS claim-list digests, its DA digest (zeros
    # without a root), and the DEFER_STMT_CELLS deferred-claim cells. A
    # parent rebuilds a child's statement with this same call, over list digests it
    # re-absorbed itself, which forces the child to be a proof of THIS bytecode over
    # claims read out of the parent's own tables.
    #
    # The preimage is fixed-length, so a plain hash beats the Fiat-Shamir chain.
    # Every value is one cell, hashed as its two lanes.
    cells = StackBuf(STMT_CELLS)
    cells[0] = seed_0  # the STMT_HEADER header cells
    cells[1] = seed_1
    cells[2] = xd_0
    cells[3] = xd_1
    cells[4] = sd_0
    cells[5] = sd_1
    cells[6] = da_0
    cells[7] = da_1
    for i in unroll(0, DEFER_STMT_CELLS):
        cells[STMT_DEFER_OFF + i] = defer[GEN ** i]
    st = StackBuf(2)
    keccak_cells(cells, st)
    return st[0], st[1]
```
-/
def statementDigest : GFn where
  name := "statement_digest"
  arity := 9
  rets := 2
  body ps := do
    let seed0 := cellOf ps 0
    let seed1 := cellOf ps 1
    let xd0 := cellOf ps 2
    let xd1 := cellOf ps 3
    let sd0 := cellOf ps 4
    let sd1 := cellOf ps 5
    let da0 := cellOf ps 6
    let da1 := cellOf ps 7
    let defer := cellOf ps 8
    let cells ← B.stackBuf STMT_CELLS
    B.copy (cellOf cells 0) seed0
    B.copy (cellOf cells 1) seed1
    B.copy (cellOf cells 2) xd0
    B.copy (cellOf cells 3) xd1
    B.copy (cellOf cells 4) sd0
    B.copy (cellOf cells 5) sd1
    B.copy (cellOf cells 6) da0
    B.copy (cellOf cells 7) da1
    for i_k in [0:DEFER_STMT_CELLS] do
      B.loadInto (cellOf cells (STMT_DEFER_OFF + i_k)) defer i_k
    let st ← B.stackBuf 2
    B.keccakCells (cells := (.cells (.frame cells))) (out := (.frame st))
    return [.v (cellOf st 0).v] ++ [.v (cellOf st 1).v]

set_option linter.unusedVariables false in
/-- `list_split` (`guests/lean_ethereum.py`, line 4327):

```
def list_split(n_g):
    # A list of n claims as (g^bigs, g^groups, g^rest), n = CLAIM_BIG * bigs +
    # CLAIM_GROUP * groups + rest with groups < BIG_GROUPS. The range checks and the
    # product identity leave that split the only solution.
    split = StackBuf(3)
    hint_witness(split, "signers_split")
    bigs = split[0]
    groups = split[1]
    rest = split[2]
    assert log(rest) < CLAIM_GROUP
    assert log(groups) < BIG_GROUPS
    assert_gpow(bigs)
    # Every exponent is small and nonnegative, so this is an identity over the
    # integers: CLAIM_BIG * bigs + CLAIM_GROUP * groups + rest == n.
    assert bigs ** CLAIM_BIG * groups ** CLAIM_GROUP * rest == n_g
    return bigs, groups, rest
```
-/
def listSplit : GFn where
  name := "list_split"
  arity := 1
  rets := 3
  body ps := do
    let nG := cellOf ps 0
    let split ← B.stackBuf 3
    B.witness "signers_split" (.stack split)
    let bigs := cellOf split 0
    let groups := cellOf split 1
    let rest := cellOf split 2
    let _ ← B.rangeCheck rest CLAIM_GROUP
    let _ ← B.rangeCheck groups BIG_GROUPS
    let _ ← B.assertGpow bigs
    B.assertEq (← B.mul (← B.mul (← B.pow bigs CLAIM_BIG) (← B.pow groups CLAIM_GROUP)) rest) nG
    return [.v bigs.v] ++ [.v groups.v] ++ [.v rest.v]

set_option linter.unusedVariables false in
/-- `claim_list_digest` (`guests/lean_ethereum.py`, line 4345):

```
def claim_list_digest(entries_ptr, n_g):
    # The hash of one scheme's declared claims: 64 bytes a claim, the claimed pubkey
    # then the message it signed. An empty list hashes the empty string, and the
    # padding binds the length.
    digest = StackBuf(2)
    if n_g == 1:
        keccak([0, 0], [0, 0], digest, len=0)
    else:
        bigs, groups, rest = list_split(n_g)
        chain = HeapBuf((bigs * groups * GEN) ** KECCAK_STATE)
        zero_state(chain)
        for xq in mul_range(1, bigs):
            st = chain * xq ** KECCAK_STATE
            nxt = st * GEN ** KECCAK_STATE
            blk = entries_ptr * xq ** (4 * CLAIM_BIG)
            for j in unroll(0, CLAIM_BIG):
                hint_witness(blk[4 * j:4 * j + 4], "claims")
            keccak_cells(blk[0:4 * CLAIM_BIG], nxt[0:KECCAK_STATE], state=st[0:KECCAK_STATE], final=0)
        mid = chain * bigs ** KECCAK_STATE
        mid_entries = entries_ptr * bigs ** (4 * CLAIM_BIG)
        for xq in mul_range(1, groups):
            st = mid * xq ** KECCAK_STATE
            nxt = st * GEN ** KECCAK_STATE
            blk = mid_entries * xq ** (4 * CLAIM_GROUP)
            for j in unroll(0, CLAIM_GROUP):
                hint_witness(blk[4 * j:4 * j + 4], "claims")
            keccak_cells(blk[0:4 * CLAIM_GROUP], nxt[0:KECCAK_STATE], state=st[0:KECCAK_STATE], final=0)
        last = mid * groups ** KECCAK_STATE
        d0, d1 = match(log(rest), range(0, CLAIM_GROUP), lambda k: claim_list_last(last, mid_entries * groups ** (4 * CLAIM_GROUP), k))
        digest[0] = d0
        digest[1] = d1
    return digest[0], digest[1]
```
-/
def claimListDigest : GFn where
  name := "claim_list_digest"
  arity := 2
  rets := 2
  body ps := do
    let entriesPtr := cellOf ps 0
    let nG := cellOf ps 1
    let digest ← B.stackBuf 2
    let t0 ← B.add nG (← B.const 1)
    let _ ← B.ite t0
      (do
        B.keccak (a := (.words [.zero, .zero])) (b := (.words [.zero, .zero])) (len := some 0) (out := (.frame digest)))
      (do
        let t1 ← B.call "list_split" [nG.v] 3
        let bigs := t1[0]!
        let groups := t1[1]!
        let rest := t1[2]!
        let chain ← B.heapBufDyn (← B.pow (← B.mul (← B.mul bigs groups) (← B.const (gpowE 1))) KECCAK_STATE)
        zeroState chain
        B.loopRtF 0 (pure bigs) 2 (pure ([chain.v, entriesPtr.v])) fun xq caps => do
          let chain := cellOf caps 0
          let entriesPtr := cellOf caps 1
          let st ← B.mul chain (← B.pow xq KECCAK_STATE)
          let nxt : Shifted := ⟨st, KECCAK_STATE⟩
          let blk ← B.mul entriesPtr (← B.pow xq (4 * CLAIM_BIG))
          for j_k in [0:CLAIM_BIG] do
            B.witness "claims" (.heap blk.v (4 * j_k) (((4 * j_k) + 4) - (4 * j_k)))
          B.keccakCells (cells := (.cells (.heap blk.v 0 (4 * CLAIM_BIG)))) (state := some (.heap st.v 0 KECCAK_STATE)) (final := false) (out := (.heap nxt.base.v nxt.exp KECCAK_STATE))
        let mid ← B.mul chain (← B.pow bigs KECCAK_STATE)
        let midEntries ← B.mul entriesPtr (← B.pow bigs (4 * CLAIM_BIG))
        B.loopRtF 0 (pure groups) 2 (pure ([mid.v, midEntries.v])) fun xq caps => do
          let mid := cellOf caps 0
          let midEntries := cellOf caps 1
          let st ← B.mul mid (← B.pow xq KECCAK_STATE)
          let nxt : Shifted := ⟨st, KECCAK_STATE⟩
          let blk ← B.mul midEntries (← B.pow xq (4 * CLAIM_GROUP))
          for j_k in [0:CLAIM_GROUP] do
            B.witness "claims" (.heap blk.v (4 * j_k) (((4 * j_k) + 4) - (4 * j_k)))
          B.keccakCells (cells := (.cells (.heap blk.v 0 (4 * CLAIM_GROUP)))) (state := some (.heap st.v 0 KECCAK_STATE)) (final := false) (out := (.heap nxt.base.v nxt.exp KECCAK_STATE))
        let last ← B.mul mid (← B.pow groups KECCAK_STATE)
        let t2 ← B.targets [none, none]
        let t3 ← B.mul midEntries (← B.pow groups (4 * CLAIM_GROUP))
        B.dispatchInto rest ((List.range CLAIM_GROUP).map fun arm => (instName "claim_list_last" [.L arm])) [last.v, t3.v] t2
        let d0 := cellOf t2 0
        let d1 := cellOf t2 1
        B.copy (cellOf digest 0) d0
        B.copy (cellOf digest 1) d1)
    return [.v (cellOf digest 0).v] ++ [.v (cellOf digest 1).v]

set_option linter.unusedVariables false in
/-- `child_claim_list_digest` (`guests/lean_ethereum.py`, line 4407):

```
def child_claim_list_digest(entries_ptr, region, base, limit_g, n_g):
    # The hash of one of a child's declared claim lists, over the same 64n bytes the
    # child hashed (`claim_list_digest`), so the digest it rebuilds is the one the
    # child's statement carries. The coverage marks lie in [base, base + n): the claims'
    # running count, or `base` alone along a strictly increasing gap walk.
    # A list whose slots strictly increase (no duplicate slot among them) takes the
    # cheaper walk; either walk is sound on its own, so the choice is the prover's.
    digest = StackBuf(2)
    if n_g == 1:
        keccak([0, 0], [0, 0], digest, len=0)
    else:
        bigs, groups, rest = list_split(n_g)
        mono = hint_witness("child_mono")
        if mono == GEN:
            d0, d1 = child_claim_list_mono(entries_ptr, region, base, limit_g, bigs, groups, rest)
            digest[0] = d0
            digest[1] = d1
        else:
            d0, d1 = child_claim_list_any(entries_ptr, region, base, limit_g, bigs, groups, rest)
            digest[0] = d0
            digest[1] = d1
    return digest[0], digest[1]
```
-/
def childClaimListDigest : GFn where
  name := "child_claim_list_digest"
  arity := 5
  rets := 2
  body ps := do
    let entriesPtr := cellOf ps 0
    let region := cellOf ps 1
    let base := cellOf ps 2
    let limitG := cellOf ps 3
    let nG := cellOf ps 4
    let digest ← B.stackBuf 2
    let t0 ← B.add nG (← B.const 1)
    let _ ← B.ite t0
      (do
        B.keccak (a := (.words [.zero, .zero])) (b := (.words [.zero, .zero])) (len := some 0) (out := (.frame digest)))
      (do
        let t1 ← B.call "list_split" [nG.v] 3
        let bigs := t1[0]!
        let groups := t1[1]!
        let rest := t1[2]!
        let mono ← hinted (B.witnessCell "child_mono")
        let t2 ← B.add mono (← B.const (gpowE 1))
        let _ ← B.ite t2
          (do
            let t3 ← B.call "child_claim_list_mono" [entriesPtr.v, region.v, base.v, limitG.v, bigs.v, groups.v, rest.v] 2
            let d0 := t3[0]!
            let d1 := t3[1]!
            B.copy (cellOf digest 0) d0
            B.copy (cellOf digest 1) d1)
          (do
            let t4 ← B.call "child_claim_list_any" [entriesPtr.v, region.v, base.v, limitG.v, bigs.v, groups.v, rest.v] 2
            let d0 := t4[0]!
            let d1 := t4[1]!
            B.copy (cellOf digest 0) d0
            B.copy (cellOf digest 1) d1)
        pure ())
    return [.v (cellOf digest 0).v] ++ [.v (cellOf digest 1).v]

set_option linter.unusedVariables false in
/-- `child_claim_list_any` (`guests/lean_ethereum.py`, line 4431):

```
def child_claim_list_any(entries_ptr, region, base, limit_g, bigs, groups, rest):
    last_g = limit_g / GEN
    chain = HeapBuf((bigs * groups * GEN) ** KECCAK_STATE)
    zero_state(chain)
    for xq in mul_range(1, bigs):
        st = chain * xq ** KECCAK_STATE
        nxt = st * GEN ** KECCAK_STATE
        blk = StackBuf(4 * CLAIM_BIG)
        child_claims(entries_ptr, region, base * xq ** CLAIM_BIG, last_g, blk, CLAIM_BIG)
        keccak_cells(blk, nxt[0:KECCAK_STATE], state=st[0:KECCAK_STATE], final=0)
    mid = chain * bigs ** KECCAK_STATE
    mid_base = base * bigs ** CLAIM_BIG
    for xq in mul_range(1, groups):
        st = mid * xq ** KECCAK_STATE
        nxt = st * GEN ** KECCAK_STATE
        blk = StackBuf(4 * CLAIM_GROUP)
        child_claims(entries_ptr, region, mid_base * xq ** CLAIM_GROUP, last_g, blk, CLAIM_GROUP)
        keccak_cells(blk, nxt[0:KECCAK_STATE], state=st[0:KECCAK_STATE], final=0)
    last = mid * groups ** KECCAK_STATE
    d0, d1 = match(log(rest), range(0, CLAIM_GROUP), lambda k: child_claim_list_last(last, entries_ptr, region, mid_base * groups ** CLAIM_GROUP, last_g, k))
    return d0, d1
```
-/
def childClaimListAny : GFn where
  name := "child_claim_list_any"
  arity := 7
  rets := 2
  body ps := do
    let entriesPtr := cellOf ps 0
    let region := cellOf ps 1
    let base := cellOf ps 2
    let limitG := cellOf ps 3
    let bigs := cellOf ps 4
    let groups := cellOf ps 5
    let rest := cellOf ps 6
    let lastG ← B.fdiv limitG (← B.const (gpowE 1))
    let chain ← B.heapBufDyn (← B.pow (← B.mul (← B.mul bigs groups) (← B.const (gpowE 1))) KECCAK_STATE)
    zeroState chain
    B.loopRtF 0 (pure bigs) 5 (pure ([chain.v, entriesPtr.v, region.v, base.v, lastG.v])) fun xq caps => do
      let chain := cellOf caps 0
      let entriesPtr := cellOf caps 1
      let region := cellOf caps 2
      let base := cellOf caps 3
      let lastG := cellOf caps 4
      let st ← B.mul chain (← B.pow xq KECCAK_STATE)
      let nxt : Shifted := ⟨st, KECCAK_STATE⟩
      let blk ← B.stackBuf 544
      childClaims entriesPtr region (← B.mul base (← B.pow xq CLAIM_BIG)) lastG blk CLAIM_BIG
      B.keccakCells (cells := (.cells (.frame blk))) (state := some (.heap st.v 0 KECCAK_STATE)) (final := false) (out := (.heap nxt.base.v nxt.exp KECCAK_STATE))
    let mid ← B.mul chain (← B.pow bigs KECCAK_STATE)
    let midBase ← B.mul base (← B.pow bigs CLAIM_BIG)
    B.loopRtF 0 (pure groups) 5 (pure ([mid.v, entriesPtr.v, region.v, midBase.v, lastG.v])) fun xq caps => do
      let mid := cellOf caps 0
      let entriesPtr := cellOf caps 1
      let region := cellOf caps 2
      let midBase := cellOf caps 3
      let lastG := cellOf caps 4
      let st ← B.mul mid (← B.pow xq KECCAK_STATE)
      let nxt : Shifted := ⟨st, KECCAK_STATE⟩
      let blk ← B.stackBuf 68
      childClaims entriesPtr region (← B.mul midBase (← B.pow xq CLAIM_GROUP)) lastG blk CLAIM_GROUP
      B.keccakCells (cells := (.cells (.frame blk))) (state := some (.heap st.v 0 KECCAK_STATE)) (final := false) (out := (.heap nxt.base.v nxt.exp KECCAK_STATE))
    let last ← B.mul mid (← B.pow groups KECCAK_STATE)
    let t0 ← B.targets [none, none]
    let t1 ← B.mul midBase (← B.pow groups CLAIM_GROUP)
    B.dispatchInto rest ((List.range CLAIM_GROUP).map fun arm => (instName "child_claim_list_last" [.L arm])) [last.v, entriesPtr.v, region.v, t1.v, lastG.v] t0
    let d0 := cellOf t0 0
    let d1 := cellOf t0 1
    return [.v d0.v] ++ [.v d1.v]

set_option linter.unusedVariables false in
/-- `child_claim_list_mono` (`guests/lean_ethereum.py`, line 4476):

```
def child_claim_list_mono(entries_ptr, region, base, limit_g, bigs, groups, rest):
    # The walk of a list at strictly increasing offsets o_j = e_0 + ... + e_j + j, every
    # e_j in [0, 2^h): its first offset is at least zero, and the count of claims, a
    # memory address (`assert_gpow`, below 2^30), keeps the sum below 2^60, short
    # of wrapping, so bounding its last offset below the region's size
    # (child_claim_list_mono_last) bounds them all. A record carries the sponge state,
    # then the walk's coverage slot and table entry.
    chain = HeapBuf((bigs * groups * GEN) ** MONO_REC)
    zero_state(chain)
    chain[GEN ** KECCAK_STATE] = region
    chain[GEN ** (KECCAK_STATE + 1)] = entries_ptr
    for xq in mul_range(1, bigs):
        rec = chain * xq ** MONO_REC
        nxt = rec * GEN ** MONO_REC
        blk = StackBuf(4 * CLAIM_BIG)
        walk = StackBuf(2)
        child_claims_mono(rec[GEN ** KECCAK_STATE], rec[GEN ** (KECCAK_STATE + 1)], base, blk, walk, CLAIM_BIG)
        nxt[GEN ** KECCAK_STATE] = walk[0]
        nxt[GEN ** (KECCAK_STATE + 1)] = walk[1]
        keccak_cells(blk, nxt[0:KECCAK_STATE], state=rec[0:KECCAK_STATE], final=0)
    mid = chain * bigs ** MONO_REC
    for xq in mul_range(1, groups):
        rec = mid * xq ** MONO_REC
        nxt = rec * GEN ** MONO_REC
        blk = StackBuf(4 * CLAIM_GROUP)
        walk = StackBuf(2)
        child_claims_mono(rec[GEN ** KECCAK_STATE], rec[GEN ** (KECCAK_STATE + 1)], base, blk, walk, CLAIM_GROUP)
        nxt[GEN ** KECCAK_STATE] = walk[0]
        nxt[GEN ** (KECCAK_STATE + 1)] = walk[1]
        keccak_cells(blk, nxt[0:KECCAK_STATE], state=rec[0:KECCAK_STATE], final=0)
    last = mid * groups ** MONO_REC
    d0, d1 = match(log(rest), range(0, CLAIM_GROUP), lambda k: child_claim_list_mono_last(last, region, base, limit_g, k))
    return d0, d1
```
-/
def childClaimListMono : GFn where
  name := "child_claim_list_mono"
  arity := 7
  rets := 2
  body ps := do
    let entriesPtr := cellOf ps 0
    let region := cellOf ps 1
    let base := cellOf ps 2
    let limitG := cellOf ps 3
    let bigs := cellOf ps 4
    let groups := cellOf ps 5
    let rest := cellOf ps 6
    let chain ← B.heapBufDyn (← B.pow (← B.mul (← B.mul bigs groups) (← B.const (gpowE 1))) MONO_REC)
    zeroState chain
    B.store chain KECCAK_STATE region
    B.store chain 14 entriesPtr
    B.loopRtF 0 (pure bigs) 2 (pure ([chain.v, base.v])) fun xq caps => do
      let chain := cellOf caps 0
      let base := cellOf caps 1
      let rec' ← B.mul chain (← B.pow xq MONO_REC)
      let nxt : Shifted := ⟨rec', MONO_REC⟩
      let blk ← B.stackBuf 544
      let walk ← B.stackBuf 2
      childClaimsMono (← B.load rec' KECCAK_STATE) (← B.load rec' 14) base blk walk CLAIM_BIG
      B.store nxt.base (nxt.exp + KECCAK_STATE) (cellOf walk 0)
      B.store nxt.base (nxt.exp + 14) (cellOf walk 1)
      B.keccakCells (cells := (.cells (.frame blk))) (state := some (.heap rec'.v 0 KECCAK_STATE)) (final := false) (out := (.heap nxt.base.v nxt.exp KECCAK_STATE))
    let mid ← B.mul chain (← B.pow bigs MONO_REC)
    B.loopRtF 0 (pure groups) 2 (pure ([mid.v, base.v])) fun xq caps => do
      let mid := cellOf caps 0
      let base := cellOf caps 1
      let rec' ← B.mul mid (← B.pow xq MONO_REC)
      let nxt : Shifted := ⟨rec', MONO_REC⟩
      let blk ← B.stackBuf 68
      let walk ← B.stackBuf 2
      childClaimsMono (← B.load rec' KECCAK_STATE) (← B.load rec' 14) base blk walk CLAIM_GROUP
      B.store nxt.base (nxt.exp + KECCAK_STATE) (cellOf walk 0)
      B.store nxt.base (nxt.exp + 14) (cellOf walk 1)
      B.keccakCells (cells := (.cells (.frame blk))) (state := some (.heap rec'.v 0 KECCAK_STATE)) (final := false) (out := (.heap nxt.base.v nxt.exp KECCAK_STATE))
    let last ← B.mul mid (← B.pow groups MONO_REC)
    let t0 ← B.targets [none, none]
    B.dispatchInto rest ((List.range CLAIM_GROUP).map fun arm => (instName "child_claim_list_mono_last" [.L arm])) [last.v, region.v, base.v, limitG.v] t0
    let d0 := cellOf t0 0
    let d1 := cellOf t0 1
    return [.v d0.v] ++ [.v d1.v]

set_option linter.unusedVariables false in
/-- `claim_list_last`, a `Const` family (`guests/lean_ethereum.py`, line 4379):

```
def claim_list_last(state, blk, k: Const):
    digest = StackBuf(2)
    if const(k == 0):
        keccak_cells([0], digest, state=state[0:KECCAK_STATE], len=0)
    else:
        for j in unroll(0, k):
            hint_witness(blk[4 * j:4 * j + 4], "claims")
        keccak_cells(blk[0:4 * k], digest, state=state[0:KECCAK_STATE])
    return digest[0], digest[1]
```
-/
def claimListLast (k : Nat) : GFn where
  name := instName "claim_list_last" [.L k]
  arity := 2
  rets := 2
  body ps := do
    let state := cellOf ps 0
    let blk := cellOf ps 1
    let digest ← B.stackBuf 2
    if k = 0 then
      B.keccakCells (cells := (.words [.zero])) (state := some (.heap state.v 0 KECCAK_STATE)) (len := some 0) (out := (.frame digest))
    else
      let j_k := 0
      B.witness "claims" (.heap blk.v (4 * j_k) (((4 * j_k) + 4) - (4 * j_k)))
      B.keccakCells (cells := (.cells (.heap blk.v 0 (4 * k)))) (state := some (.heap state.v 0 KECCAK_STATE)) (out := (.frame digest))
    return [.v (cellOf digest 0).v] ++ [.v (cellOf digest 1).v]

set_option linter.unusedVariables false in
/-- `claim_list_last`, a `Const` family (`guests/lean_ethereum.py`, line 4379):

```
def claim_list_last(state, blk, k: Const):
    digest = StackBuf(2)
    if const(k == 0):
        keccak_cells([0], digest, state=state[0:KECCAK_STATE], len=0)
    else:
        for j in unroll(0, k):
            hint_witness(blk[4 * j:4 * j + 4], "claims")
        keccak_cells(blk[0:4 * k], digest, state=state[0:KECCAK_STATE])
    return digest[0], digest[1]
```
-/
def claimListLast_2 (k : Nat) : GFn where
  name := instName "claim_list_last" [.L k]
  arity := 2
  rets := 2
  body ps := do
    let state := cellOf ps 0
    let blk := cellOf ps 1
    let digest ← B.stackBuf 2
    if k = 0 then
      pure () -- no use of this definition takes this branch
    else
      for j_k in [0:k] do
        B.witness "claims" (.heap blk.v (4 * j_k) (((4 * j_k) + 4) - (4 * j_k)))
      B.keccakCells (cells := (.cells (.heap blk.v 0 (4 * k)))) (state := some (.heap state.v 0 KECCAK_STATE)) (out := (.frame digest))
    return [.v (cellOf digest 0).v] ++ [.v (cellOf digest 1).v]

set_option linter.unusedVariables false in
/-- `child_claim_list_last`, a `Const` family (`guests/lean_ethereum.py`, line 4527):

```
def child_claim_list_last(state, entries_ptr, region, marks, last_g, k: Const):
    digest = StackBuf(2)
    if const(k == 0):
        keccak_cells([0], digest, state=state[0:KECCAK_STATE], len=0)
    else:
        blk = StackBuf(4 * CLAIM_GROUP)
        child_claims(entries_ptr, region, marks, last_g, blk, k)
        keccak_cells(blk[0:4 * k], digest, state=state[0:KECCAK_STATE])
    return digest[0], digest[1]
```
-/
def childClaimListLast (k : Nat) : GFn where
  name := instName "child_claim_list_last" [.L k]
  arity := 5
  rets := 2
  body ps := do
    let state := cellOf ps 0
    let entriesPtr := cellOf ps 1
    let region := cellOf ps 2
    let marks := cellOf ps 3
    let lastG := cellOf ps 4
    let digest ← B.stackBuf 2
    if k = 0 then
      B.keccakCells (cells := (.words [.zero])) (state := some (.heap state.v 0 KECCAK_STATE)) (len := some 0) (out := (.frame digest))
    else
      let blk ← B.stackBuf 68
      childClaims_2 entriesPtr region marks lastG blk k
      B.keccakCells (cells := (.cells (.frame (blk.take (4 * k))))) (state := some (.heap state.v 0 KECCAK_STATE)) (out := (.frame digest))
    return [.v (cellOf digest 0).v] ++ [.v (cellOf digest 1).v]

set_option linter.unusedVariables false in
/-- `child_claim_list_last`, a `Const` family (`guests/lean_ethereum.py`, line 4527):

```
def child_claim_list_last(state, entries_ptr, region, marks, last_g, k: Const):
    digest = StackBuf(2)
    if const(k == 0):
        keccak_cells([0], digest, state=state[0:KECCAK_STATE], len=0)
    else:
        blk = StackBuf(4 * CLAIM_GROUP)
        child_claims(entries_ptr, region, marks, last_g, blk, k)
        keccak_cells(blk[0:4 * k], digest, state=state[0:KECCAK_STATE])
    return digest[0], digest[1]
```
-/
def childClaimListLast_2 (k : Nat) : GFn where
  name := instName "child_claim_list_last" [.L k]
  arity := 5
  rets := 2
  body ps := do
    let state := cellOf ps 0
    let entriesPtr := cellOf ps 1
    let region := cellOf ps 2
    let marks := cellOf ps 3
    let lastG := cellOf ps 4
    let digest ← B.stackBuf 2
    if k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let blk ← B.stackBuf 68
      childClaims_3 entriesPtr region marks lastG blk k
      B.keccakCells (cells := (.cells (.frame (blk.take (4 * k))))) (state := some (.heap state.v 0 KECCAK_STATE)) (out := (.frame digest))
    return [.v (cellOf digest 0).v] ++ [.v (cellOf digest 1).v]

set_option linter.unusedVariables false in
/-- `child_claim_list_last`, a `Const` family (`guests/lean_ethereum.py`, line 4527):

```
def child_claim_list_last(state, entries_ptr, region, marks, last_g, k: Const):
    digest = StackBuf(2)
    if const(k == 0):
        keccak_cells([0], digest, state=state[0:KECCAK_STATE], len=0)
    else:
        blk = StackBuf(4 * CLAIM_GROUP)
        child_claims(entries_ptr, region, marks, last_g, blk, k)
        keccak_cells(blk[0:4 * k], digest, state=state[0:KECCAK_STATE])
    return digest[0], digest[1]
```
-/
def childClaimListLast_3 (k : Nat) : GFn where
  name := instName "child_claim_list_last" [.L k]
  arity := 5
  rets := 2
  body ps := do
    let state := cellOf ps 0
    let entriesPtr := cellOf ps 1
    let region := cellOf ps 2
    let marks := cellOf ps 3
    let lastG := cellOf ps 4
    let digest ← B.stackBuf 2
    if k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let blk ← B.stackBuf 68
      childClaims entriesPtr region marks lastG blk k
      B.keccakCells (cells := (.cells (.frame (blk.take (4 * k))))) (state := some (.heap state.v 0 KECCAK_STATE)) (out := (.frame digest))
    return [.v (cellOf digest 0).v] ++ [.v (cellOf digest 1).v]

set_option linter.unusedVariables false in
/-- `child_claim_list_mono_last`, a `Const` family (`guests/lean_ethereum.py`, line 4511):

```
def child_claim_list_mono_last(rec, region, mark, limit_g, k: Const):
    digest = StackBuf(2)
    if const(k == 0):
        keccak_cells([0], digest, state=rec[0:KECCAK_STATE], len=0)
        cov_end = rec[GEN ** KECCAK_STATE]
    else:
        blk = StackBuf(4 * CLAIM_GROUP)
        walk = StackBuf(2)
        child_claims_mono(rec[GEN ** KECCAK_STATE], rec[GEN ** (KECCAK_STATE + 1)], mark, blk, walk, k)
        keccak_cells(blk[0:4 * k], digest, state=rec[0:KECCAK_STATE])
        cov_end = walk[0]
    # The offset after the last claim is at most the region's size.
    assert log(cov_end / region) < log(limit_g * GEN)
    return digest[0], digest[1]
```
-/
def childClaimListMonoLast (k : Nat) : GFn where
  name := instName "child_claim_list_mono_last" [.L k]
  arity := 4
  rets := 2
  body ps := do
    let rec' := cellOf ps 0
    let region := cellOf ps 1
    let mark := cellOf ps 2
    let limitG := cellOf ps 3
    let digest ← B.stackBuf 2
    let mut covEnd : Word := default
    if k = 0 then
      B.keccakCells (cells := (.words [.zero])) (state := some (.heap rec'.v 0 KECCAK_STATE)) (len := some 0) (out := (.frame digest))
      covEnd ← B.load rec' KECCAK_STATE
    else
      let blk ← B.stackBuf 68
      let walk ← B.stackBuf 2
      childClaimsMono_2 (← B.load rec' KECCAK_STATE) (← B.load rec' 14) mark blk walk k
      B.keccakCells (cells := (.cells (.frame (blk.take (4 * k))))) (state := some (.heap rec'.v 0 KECCAK_STATE)) (out := (.frame digest))
      covEnd := cellOf walk 0
    let t0 ← B.shifted limitG (1 - 1)
    let _ ← B.rangeCheckK (← B.fdiv covEnd region) t0
    return [.v (cellOf digest 0).v] ++ [.v (cellOf digest 1).v]

set_option linter.unusedVariables false in
/-- `child_claim_list_mono_last`, a `Const` family (`guests/lean_ethereum.py`, line 4511):

```
def child_claim_list_mono_last(rec, region, mark, limit_g, k: Const):
    digest = StackBuf(2)
    if const(k == 0):
        keccak_cells([0], digest, state=rec[0:KECCAK_STATE], len=0)
        cov_end = rec[GEN ** KECCAK_STATE]
    else:
        blk = StackBuf(4 * CLAIM_GROUP)
        walk = StackBuf(2)
        child_claims_mono(rec[GEN ** KECCAK_STATE], rec[GEN ** (KECCAK_STATE + 1)], mark, blk, walk, k)
        keccak_cells(blk[0:4 * k], digest, state=rec[0:KECCAK_STATE])
        cov_end = walk[0]
    # The offset after the last claim is at most the region's size.
    assert log(cov_end / region) < log(limit_g * GEN)
    return digest[0], digest[1]
```
-/
def childClaimListMonoLast_2 (k : Nat) : GFn where
  name := instName "child_claim_list_mono_last" [.L k]
  arity := 4
  rets := 2
  body ps := do
    let rec' := cellOf ps 0
    let region := cellOf ps 1
    let mark := cellOf ps 2
    let limitG := cellOf ps 3
    let digest ← B.stackBuf 2
    let mut covEnd : Word := default
    if k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let blk ← B.stackBuf 68
      let walk ← B.stackBuf 2
      childClaimsMono (← B.load rec' KECCAK_STATE) (← B.load rec' 14) mark blk walk k
      B.keccakCells (cells := (.cells (.frame (blk.take (4 * k))))) (state := some (.heap rec'.v 0 KECCAK_STATE)) (out := (.frame digest))
      covEnd := cellOf walk 0
    let t0 ← B.shifted limitG (1 - 1)
    let _ ← B.rangeCheckK (← B.fdiv covEnd region) t0
    return [.v (cellOf digest 0).v] ++ [.v (cellOf digest 1).v]

end
end LeanVM.Dsl.Gen
