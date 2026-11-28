/-
  LeanVM.Guest.Program.StatementsAndClaimLists

  The guest's section "statements and the claim lists".
-/

module

public import LeanVM.Guest.Program.LeanSphincs

/-!
# Statements and the claim lists
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- A node's statement, hashed to the two words the VM publishes, over the proving environment's Fiat-Shamir seed (the proof system's version and this bytecode), the leanXMSS and leanSPHINCS claim-list digests, its DA digest (zeros without a root), and the DEFER_STMT_CELLS deferred-claim cells. A parent rebuilds a child's statement with this same call, over list digests it re-absorbed itself, which forces the child to be a proof of THIS bytecode over claims read out of the parent's own tables.

The preimage is fixed-length, so a plain hash beats the Fiat-Shamir chain. Every value is one cell, hashed as its two lanes.
-/
def statementDigest : GFn where
  name := "statement_digest"
  arity := 9
  rets := 2
  body ps := do
    let seed0 := ps[0]
    let seed1 := ps[1]
    let xd0 := ps[2]
    let xd1 := ps[3]
    let sd0 := ps[4]
    let sd1 := ps[5]
    let da0 := ps[6]
    let da1 := ps[7]
    let defer := ps[8]
    let cells ← B.stackBuf STMT_CELLS
    cells[0] := seed0  -- the STMT_HEADER header cells
    cells[1] := seed1
    cells[2] := xd0
    cells[3] := xd1
    cells[4] := sd0
    cells[5] := sd1
    cells[6] := da0
    cells[7] := da1
    for i in [0:DEFER_STMT_CELLS] do
      cells[STMT_DEFER_OFF + i] := defer[GEN ^ i]
    let st ← B.stackBuf 2
    B.keccakCells cells st
    return [.v st[0].v, .v st[1].v]

def zeroState (chain : Word) : B Unit := B.inline "zero_state" do
  for k in [0:KECCAK_STATE] do
    chain[GEN ^ k] := 0

/-- A list of n claims as (g^bigs, g^groups, g^rest), n = CLAIM_BIG * bigs + CLAIM_GROUP * groups + rest with groups < BIG_GROUPS. The range checks and the product identity leave that split the only solution. -/
def listSplit : GFn where
  name := "list_split"
  arity := 1
  rets := 3
  body ps := do
    let nG := ps[0]
    let split ← B.stackBuf 3
    B.witness "signers_split" (.stack split)
    let bigs := split[0]
    let groups := split[1]
    let rest := split[2]
    assert log rest < CLAIM_GROUP
    assert log groups < BIG_GROUPS
    let _ ← B.assertGpow bigs
    -- Every exponent is small and nonnegative, so this is an identity over the integers: CLAIM_BIG * bigs + CLAIM_GROUP * groups + rest == n.
    assert bigs ^ CLAIM_BIG * groups ^ CLAIM_GROUP * rest == nG
    return [.v bigs.v, .v groups.v, .v rest.v]

/-- The hash of one scheme's declared claims: 64 bytes a claim, the claimed pubkey then the message it signed. An empty list hashes the empty string, and the padding binds the length. -/
def claimListDigest : GFn where
  name := "claim_list_digest"
  arity := 2
  rets := 2
  body ps := do
    let entriesPtr := ps[0]
    let nG := ps[1]
    let digest ← B.stackBuf 2
    let t0 ← val (nG + 1)
    let _ ← B.ite t0
      (do
        B.keccak (a := .words [.zero, .zero]) (b := .words [.zero, .zero]) (len := some 0) (out := .frame digest))
      (do
        let t1 ← callN "list_split" [nG] 3
        let bigs := t1[0]!
        let groups := t1[1]!
        let rest := t1[2]!
        let chain ← B.heapBufDyn (← val ((bigs * groups * GEN) ^ KECCAK_STATE))
        zeroState chain
        B.loopRtF 0 (pure bigs) 2 (pure ([chain.v, entriesPtr.v])) fun xq caps => do
          let chain := caps[0]
          let entriesPtr := caps[1]
          let st ← val (chain * xq ^ KECCAK_STATE)
          let nxt : Shifted := ⟨st, KECCAK_STATE⟩
          let blk ← val (entriesPtr * xq ^ (4 * CLAIM_BIG))
          for j in [0:CLAIM_BIG] do
            B.witness "claims" (.heap blk.v (4 * j) (4 * j + 4 - 4 * j))
          B.keccakCells (cells := .cells (.heap blk.v 0 (4 * CLAIM_BIG))) (state := some (.heap st.v 0 KECCAK_STATE)) (final := false) (out := .heap nxt.base.v nxt.exp KECCAK_STATE)
        let mid ← val (chain * bigs ^ KECCAK_STATE)
        let midEntries ← val (entriesPtr * bigs ^ (4 * CLAIM_BIG))
        B.loopRtF 0 (pure groups) 2 (pure ([mid.v, midEntries.v])) fun xq caps => do
          let mid := caps[0]
          let midEntries := caps[1]
          let st ← val (mid * xq ^ KECCAK_STATE)
          let nxt : Shifted := ⟨st, KECCAK_STATE⟩
          let blk ← val (midEntries * xq ^ (4 * CLAIM_GROUP))
          for j in [0:CLAIM_GROUP] do
            B.witness "claims" (.heap blk.v (4 * j) (4 * j + 4 - 4 * j))
          B.keccakCells (cells := .cells (.heap blk.v 0 (4 * CLAIM_GROUP))) (state := some (.heap st.v 0 KECCAK_STATE)) (final := false) (out := .heap nxt.base.v nxt.exp KECCAK_STATE)
        let last ← val (mid * groups ^ KECCAK_STATE)
        let t2 ← B.targets [none, none]
        let t3 ← val (midEntries * groups ^ (4 * CLAIM_GROUP))
        B.dispatchInto rest ((List.range CLAIM_GROUP).map (fun arm => instName "claim_list_last" [.L arm])) [last.v, t3.v] t2
        let d0 := t2[0]
        let d1 := t2[1]
        digest[0] := d0
        digest[1] := d1)
    return [.v digest[0].v, .v digest[1].v]

def claimListLast (k : Nat) : GFn where
  name := instName "claim_list_last" [.L k]
  arity := 2
  rets := 2
  body ps := do
    let state := ps[0]
    let blk := ps[1]
    let digest ← B.stackBuf 2
    if k = 0 then
      B.keccakCells (cells := .words [.zero]) (state := some (.heap state.v 0 KECCAK_STATE)) (len := some 0) (out := .frame digest)
    else
      for j in [0:k] do
        B.witness "claims" (.heap blk.v (4 * j) (4 * j + 4 - 4 * j))
      B.keccakCells (cells := .cells (.heap blk.v 0 (4 * k))) (state := some (.heap state.v 0 KECCAK_STATE)) (out := .frame digest)
    return [.v digest[0].v, .v digest[1].v]

/-- n of a child's claims, each read at a hinted index into THIS node's table and marked in the coverage table. The index is an offset into the scheme's region (`region`, the coverage table from the scheme's origin) and bounded by that region's size, last_g * GEN, so a child's claim can only ever land on a slot of its own scheme. The bound so written is its own range-check target, last_g. -/
def childClaims (entriesPtr : Word) (region : Word) (marks : Word) (lastG : Word) (blk : List V) (n : Nat) : B Unit := B.inline "child_claims" do
  for j in [0:n] do
    let offHint ← hinted (B.witnessCell "child_claim_index")
    let t0 ← B.shifted lastG (1 - 1)  -- precondition as in the raw loops
    let _ ← B.rangeCheckK offHint t0
    let t1 ← val (marks * GEN ^ j)
    region[offHint] := t1
    let entry ← val (entriesPtr * offHint ^ 4)
    for c in [0:4] do
      blk[4 * j + c] := entry[GEN ^ c]

/-- The hash of one of a child's declared claim lists, over the same 64n bytes the child hashed (`claim_list_digest`), so the digest it rebuilds is the one the child's statement carries. The coverage marks lie in [base, base + n): the claims' running count, or `base` alone along a strictly increasing gap walk. A list whose slots strictly increase (no duplicate slot among them) takes the cheaper walk; either walk is sound on its own, so the choice is the prover's. -/
def childClaimListDigest : GFn where
  name := "child_claim_list_digest"
  arity := 5
  rets := 2
  body ps := do
    let entriesPtr := ps[0]
    let region := ps[1]
    let base := ps[2]
    let limitG := ps[3]
    let nG := ps[4]
    let digest ← B.stackBuf 2
    let t0 ← val (nG + 1)
    let _ ← B.ite t0
      (do
        B.keccak (a := .words [.zero, .zero]) (b := .words [.zero, .zero]) (len := some 0) (out := .frame digest))
      (do
        let t1 ← callN "list_split" [nG] 3
        let bigs := t1[0]!
        let groups := t1[1]!
        let rest := t1[2]!
        let mono ← hinted (B.witnessCell "child_mono")
        let t2 ← val (mono + GEN)
        let _ ← B.ite t2
          (do
            let t3 ← callN "child_claim_list_mono" [entriesPtr, region, base, limitG, bigs, groups, rest] 2
            let d0 := t3[0]!
            let d1 := t3[1]!
            digest[0] := d0
            digest[1] := d1)
          (do
            let t4 ← callN "child_claim_list_any" [entriesPtr, region, base, limitG, bigs, groups, rest] 2
            let d0 := t4[0]!
            let d1 := t4[1]!
            digest[0] := d0
            digest[1] := d1)
        pure ())
    return [.v digest[0].v, .v digest[1].v]

def childClaimListAny : GFn where
  name := "child_claim_list_any"
  arity := 7
  rets := 2
  body ps := do
    let entriesPtr := ps[0]
    let region := ps[1]
    let base := ps[2]
    let limitG := ps[3]
    let bigs := ps[4]
    let groups := ps[5]
    let rest := ps[6]
    let lastG ← val (limitG / GEN)
    let chain ← B.heapBufDyn (← val ((bigs * groups * GEN) ^ KECCAK_STATE))
    zeroState chain
    B.loopRtF 0 (pure bigs) 5 (pure ([chain.v, entriesPtr.v, region.v, base.v, lastG.v])) fun xq caps => do
      let chain := caps[0]
      let entriesPtr := caps[1]
      let region := caps[2]
      let base := caps[3]
      let lastG := caps[4]
      let st ← val (chain * xq ^ KECCAK_STATE)
      let nxt : Shifted := ⟨st, KECCAK_STATE⟩
      let blk ← B.stackBuf 544
      childClaims entriesPtr region (← val (base * xq ^ CLAIM_BIG)) lastG blk CLAIM_BIG
      B.keccakCells (cells := .cells (.frame blk)) (state := some (.heap st.v 0 KECCAK_STATE)) (final := false) (out := .heap nxt.base.v nxt.exp KECCAK_STATE)
    let mid ← val (chain * bigs ^ KECCAK_STATE)
    let midBase ← val (base * bigs ^ CLAIM_BIG)
    B.loopRtF 0 (pure groups) 5 (pure ([mid.v, entriesPtr.v, region.v, midBase.v, lastG.v])) fun xq caps => do
      let mid := caps[0]
      let entriesPtr := caps[1]
      let region := caps[2]
      let midBase := caps[3]
      let lastG := caps[4]
      let st ← val (mid * xq ^ KECCAK_STATE)
      let nxt : Shifted := ⟨st, KECCAK_STATE⟩
      let blk ← B.stackBuf 68
      childClaims entriesPtr region (← val (midBase * xq ^ CLAIM_GROUP)) lastG blk CLAIM_GROUP
      B.keccakCells (cells := .cells (.frame blk)) (state := some (.heap st.v 0 KECCAK_STATE)) (final := false) (out := .heap nxt.base.v nxt.exp KECCAK_STATE)
    let last ← val (mid * groups ^ KECCAK_STATE)
    let t0 ← B.targets [none, none]
    let t1 ← val (midBase * groups ^ CLAIM_GROUP)
    B.dispatchInto rest ((List.range CLAIM_GROUP).map (fun arm => instName "child_claim_list_last" [.L arm])) [last.v, entriesPtr.v, region.v, t1.v, lastG.v] t0
    let d0 := t0[0]
    let d1 := t0[1]
    return [.v d0.v, .v d1.v]

/-- n of a child's claims at strictly increasing offsets into THIS node's table: each hinted gap g^e, e >= 0 by the DEREF through it, moves the offset on by e + 1. cov and ent are the coverage slot and the table entry the next claim takes at gap zero; out receives them for the claim after the last. Every claim of the list writes the same mark, its first count: the walk cannot revisit a slot, and any other writer's value differs, so a slot written twice still conflicts. -/
def childClaimsMono (cov : Word) (ent : Word) (mark : Word) (blk : List V) (out : List V) (n : Nat) : B Unit := B.inline "child_claims_mono" do
  let mut cov := cov
  let mut ent := ent
  for j in [0:n] do
    let gap ← hinted (B.witnessCell "child_claim_gap")
    let _ ← B.assertGpow gap
    cov ← val (cov * gap)
    let gap2 ← val (gap * gap)
    ent ← val (ent * (gap2 * gap2))
    cov[GEN ^ j] := mark
    for c in [0:4] do
      blk[4 * j + c] := ent[GEN ^ (4 * j + c)]
  out[0] := cov * GEN ^ n
  out[1] := ent * GEN ^ (4 * n)

/-- The walk of a list at strictly increasing offsets o_j = e_0 + ... + e_j + j, every e_j in [0, 2^h): its first offset is at least zero, and the count of claims, a memory address (`assert_gpow`, below 2^30), keeps the sum below 2^60, short of wrapping, so bounding its last offset below the region's size (child_claim_list_mono_last) bounds them all. A record carries the sponge state, then the walk's coverage slot and table entry. -/
def childClaimListMono : GFn where
  name := "child_claim_list_mono"
  arity := 7
  rets := 2
  body ps := do
    let entriesPtr := ps[0]
    let region := ps[1]
    let base := ps[2]
    let limitG := ps[3]
    let bigs := ps[4]
    let groups := ps[5]
    let rest := ps[6]
    let chain ← B.heapBufDyn (← val ((bigs * groups * GEN) ^ MONO_REC))
    zeroState chain
    chain[GEN ^ KECCAK_STATE] := region
    chain[GEN ^ 14] := entriesPtr
    B.loopRtF 0 (pure bigs) 2 (pure ([chain.v, base.v])) fun xq caps => do
      let chain := caps[0]
      let base := caps[1]
      let rec' ← val (chain * xq ^ MONO_REC)
      let nxt : Shifted := ⟨rec', MONO_REC⟩
      let blk ← B.stackBuf 544
      let walk ← B.stackBuf 2
      childClaimsMono (← val rec'[GEN ^ KECCAK_STATE]) (← val rec'[GEN ^ 14]) base blk walk CLAIM_BIG
      nxt[GEN ^ KECCAK_STATE] := walk[0]
      nxt[GEN ^ 14] := walk[1]
      B.keccakCells (cells := .cells (.frame blk)) (state := some (.heap rec'.v 0 KECCAK_STATE)) (final := false) (out := .heap nxt.base.v nxt.exp KECCAK_STATE)
    let mid ← val (chain * bigs ^ MONO_REC)
    B.loopRtF 0 (pure groups) 2 (pure ([mid.v, base.v])) fun xq caps => do
      let mid := caps[0]
      let base := caps[1]
      let rec' ← val (mid * xq ^ MONO_REC)
      let nxt : Shifted := ⟨rec', MONO_REC⟩
      let blk ← B.stackBuf 68
      let walk ← B.stackBuf 2
      childClaimsMono (← val rec'[GEN ^ KECCAK_STATE]) (← val rec'[GEN ^ 14]) base blk walk CLAIM_GROUP
      nxt[GEN ^ KECCAK_STATE] := walk[0]
      nxt[GEN ^ 14] := walk[1]
      B.keccakCells (cells := .cells (.frame blk)) (state := some (.heap rec'.v 0 KECCAK_STATE)) (final := false) (out := .heap nxt.base.v nxt.exp KECCAK_STATE)
    let last ← val (mid * groups ^ MONO_REC)
    let t0 ← B.targets [none, none]
    B.dispatchInto rest ((List.range CLAIM_GROUP).map (fun arm => instName "child_claim_list_mono_last" [.L arm])) [last.v, region.v, base.v, limitG.v] t0
    let d0 := t0[0]
    let d1 := t0[1]
    return [.v d0.v, .v d1.v]

def childClaimListMonoLast (k : Nat) : GFn where
  name := instName "child_claim_list_mono_last" [.L k]
  arity := 4
  rets := 2
  body ps := do
    let rec' := ps[0]
    let region := ps[1]
    let mark := ps[2]
    let limitG := ps[3]
    let digest ← B.stackBuf 2
    let mut covEnd : Word := default
    if k = 0 then
      B.keccakCells (cells := .words [.zero]) (state := some (.heap rec'.v 0 KECCAK_STATE)) (len := some 0) (out := .frame digest)
      covEnd ← val rec'[GEN ^ KECCAK_STATE]
    else
      let blk ← B.stackBuf 68
      let walk ← B.stackBuf 2
      childClaimsMono (← val rec'[GEN ^ KECCAK_STATE]) (← val rec'[GEN ^ 14]) mark blk walk k
      B.keccakCells (cells := .cells (.frame blk[0:4 * k])) (state := some (.heap rec'.v 0 KECCAK_STATE)) (out := .frame digest)
      covEnd := walk[0]
    -- The offset after the last claim is at most the region's size.
    let t0 ← B.shifted limitG (1 - 1)
    let _ ← B.rangeCheckK (← val (covEnd / region)) t0
    return [.v digest[0].v, .v digest[1].v]

def childClaimListLast (k : Nat) : GFn where
  name := instName "child_claim_list_last" [.L k]
  arity := 5
  rets := 2
  body ps := do
    let state := ps[0]
    let entriesPtr := ps[1]
    let region := ps[2]
    let marks := ps[3]
    let lastG := ps[4]
    let digest ← B.stackBuf 2
    if k = 0 then
      B.keccakCells (cells := .words [.zero]) (state := some (.heap state.v 0 KECCAK_STATE)) (len := some 0) (out := .frame digest)
    else
      let blk ← B.stackBuf 68
      childClaims entriesPtr region marks lastG blk k
      B.keccakCells (cells := .cells (.frame blk[0:4 * k])) (state := some (.heap state.v 0 KECCAK_STATE)) (out := .frame digest)
    return [.v digest[0].v, .v digest[1].v]

end
end LeanVM.Guest.Program
