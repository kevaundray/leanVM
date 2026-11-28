/-
  LeanVM.Dsl.Gen.LeanSPHINCSSignatureVerification

  The guest's section `LeanSPHINCSSignatureVerification`, translated.
-/

module

public import LeanVM.Dsl.Gen.Inline

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `sp_wots` (`guests/lean_ethereum.py`, line 4105):

```
def sp_wots(pp, a0, a1, encoding):
    # The leaf of the one-time key whose address is (a0, a1), a1 of type WOTS_HASH and
    # so its key pair alone, and whose encoding digest is `encoding`. The codeword:
    # DIGIT_GROUP digits at a time, hinted in the exponent and range checked, every
    # group first, then the groups' dispatches back to back (each arm entering the next
    # dispatch, as in verify_lean_xmss), the arm walking every chain's remaining steps
    # and folding its digits in: their sums into a product that must be the target sum,
    # and the digits, each group where the digest holds it, into the digest. One
    # function for the three layers.
    at = [a0, a1]
    walks = StackBuf(SP_V * CHAIN_STEPS)
    powers = StackBuf(DIGIT_GROUP * CHAIN_STEPS + 1)
    for s in unroll(0, DIGIT_GROUP * CHAIN_STEPS + 1):
        powers[s] = GEN ** s
    digit_product = 1
    encoded = 0
    # A leanSPHINCS chain index rides its step's address, so the chain-index table a
    # leanXMSS walk reads is unused here and `powers` stands in for it.
    # The last group is the chain the others leave over: its table is as wide as theirs
    # (one unrolled `match`), its range check keeping it to one digit.
    groups = StackBuf(SP_V // DIGIT_GROUP + 1)
    for p in unroll(0, SP_V // DIGIT_GROUP + 1):
        hint_witness(groups[p:p + 1], "digits")
    for p in unroll(0, SP_V // DIGIT_GROUP):
        assert log(groups[p]) < DIGIT_GROUPS
    assert log(groups[SP_V // DIGIT_GROUP]) < CHAIN_LENGTH
    for p in unroll(0, SP_V // DIGIT_GROUP + 1):
        digit_product, encoded = match(log(groups[p]), range(0, DIGIT_GROUPS), lambda k: walk_group(at, pp, walks, powers, DIGIT_GROUP * p, DIGIT_GROUP - (DIGIT_GROUP - 1) * (p // (SP_V // DIGIT_GROUP)), k, 0, powers, digit_product, encoded))
    assert encoded == encoding
    assert digit_product == GEN ** SP_TARGET_SUM
    leaf = StackBuf(1)
    pk_at = a1 + const(SP_WOTS_PK)
    keccak_cells([sp_word(pp, a0, pk_at, walks, CHAIN_STEPS - 1, CHAIN_STEPS, j) for j in unroll(0, SP_V + 3)], leaf)
    return leaf[0]
```
-/
def spWots : GFn where
  name := "sp_wots"
  arity := 4
  rets := 1
  body ps := do
    let pp := cellOf ps 0
    let a0 := cellOf ps 1
    let a1 := cellOf ps 2
    let encoding := cellOf ps 3
    let t0 ← B.stackBuf 2
    B.copy (cellOf t0 0) a0
    B.copy (cellOf t0 1) a1
    let at' := t0
    let walks ← B.stackBuf 192
    let powers ← B.stackBuf 10
    for s_k in [0:(3 * 3) + 1] do
      B.constInto (cellOf powers s_k) (gpowE s_k)
    let digitProduct := 1
    let encoded := 0
    let groups ← B.stackBuf 22
    for p_k in [0:(SP_V / DIGIT_GROUP) + 1] do
      B.witness "digits" (.stack ((groups.drop p_k).take ((p_k + 1) - p_k)))
    for p_k in [0:SP_V / DIGIT_GROUP] do
      let _ ← B.rangeCheck (cellOf groups p_k) DIGIT_GROUPS
      pure ()
    let _ ← B.rangeCheck (cellOf groups (SP_V / DIGIT_GROUP)) CHAIN_LENGTH
    let mut digitProduct_word : Word := default
    let mut encoded_word : Word := default
    let p_k := 0
    let t1 ← B.targets [none, none]
    B.chain
    Keccak.inlineArms
    let t2_0 : B Unit := do
      walkGroup_36 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 0 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_1 : B Unit := do
      walkGroup_37 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 1 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_2 : B Unit := do
      walkGroup_38 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 2 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_3 : B Unit := do
      walkGroup_36 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) DIGIT_GROUP 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_4 : B Unit := do
      walkGroup_36 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 4 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_5 : B Unit := do
      walkGroup_37 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 5 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_6 : B Unit := do
      walkGroup_38 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 6 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_7 : B Unit := do
      walkGroup_36 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 7 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_8 : B Unit := do
      walkGroup_39 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 8 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_9 : B Unit := do
      walkGroup_40 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 9 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_10 : B Unit := do
      walkGroup_41 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 10 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_11 : B Unit := do
      walkGroup_39 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 11 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_12 : B Unit := do
      walkGroup_42 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 12 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_13 : B Unit := do
      walkGroup_43 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 13 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_14 : B Unit := do
      walkGroup_44 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 14 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_15 : B Unit := do
      walkGroup_42 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 15 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_16 : B Unit := do
      walkGroup_36 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 16 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_17 : B Unit := do
      walkGroup_37 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 17 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_18 : B Unit := do
      walkGroup_38 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 18 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_19 : B Unit := do
      walkGroup_36 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 19 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_20 : B Unit := do
      walkGroup_36 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 20 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_21 : B Unit := do
      walkGroup_37 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 21 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_22 : B Unit := do
      walkGroup_38 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 22 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_23 : B Unit := do
      walkGroup_36 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 23 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_24 : B Unit := do
      walkGroup_39 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 24 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_25 : B Unit := do
      walkGroup_40 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 25 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_26 : B Unit := do
      walkGroup_41 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 26 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_27 : B Unit := do
      walkGroup_39 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 27 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_28 : B Unit := do
      walkGroup_42 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 28 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_29 : B Unit := do
      walkGroup_43 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 29 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_30 : B Unit := do
      walkGroup_44 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 30 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_31 : B Unit := do
      walkGroup_42 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 31 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_32 : B Unit := do
      walkGroup_45 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 32 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_33 : B Unit := do
      walkGroup_46 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 33 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_34 : B Unit := do
      walkGroup_47 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 34 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_35 : B Unit := do
      walkGroup_45 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 35 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_36 : B Unit := do
      walkGroup_45 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 36 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_37 : B Unit := do
      walkGroup_46 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 37 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_38 : B Unit := do
      walkGroup_47 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 38 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_39 : B Unit := do
      walkGroup_45 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 39 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_40 : B Unit := do
      walkGroup_48 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 40 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_41 : B Unit := do
      walkGroup_49 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 41 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_42 : B Unit := do
      walkGroup_50 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 42 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_43 : B Unit := do
      walkGroup_48 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 43 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_44 : B Unit := do
      walkGroup_51 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 44 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_45 : B Unit := do
      walkGroup_52 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 45 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_46 : B Unit := do
      walkGroup_53 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 46 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_47 : B Unit := do
      walkGroup_51 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 47 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_48 : B Unit := do
      walkGroup_54 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 48 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_49 : B Unit := do
      walkGroup_55 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 49 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_50 : B Unit := do
      walkGroup_56 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 50 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_51 : B Unit := do
      walkGroup_54 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 51 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_52 : B Unit := do
      walkGroup_54 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 52 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_53 : B Unit := do
      walkGroup_55 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 53 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_54 : B Unit := do
      walkGroup_56 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 54 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_55 : B Unit := do
      walkGroup_54 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 55 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_56 : B Unit := do
      walkGroup_57 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 56 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_57 : B Unit := do
      walkGroup_58 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 57 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_58 : B Unit := do
      walkGroup_59 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 58 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_59 : B Unit := do
      walkGroup_57 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 59 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_60 : B Unit := do
      walkGroup_60 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 60 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_61 : B Unit := do
      walkGroup_61 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 61 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_62 : B Unit := do
      walkGroup_62 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 62 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_63 : B Unit := do
      walkGroup_60 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 63 0 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t1 0).v, (cellOf t1 1).v]
    let _ ← B.matchArms (cellOf groups p_k) [t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7, t2_8, t2_9, t2_10, t2_11, t2_12, t2_13, t2_14, t2_15, t2_16, t2_17, t2_18, t2_19, t2_20, t2_21, t2_22, t2_23, t2_24, t2_25, t2_26, t2_27, t2_28, t2_29, t2_30, t2_31, t2_32, t2_33, t2_34, t2_35, t2_36, t2_37, t2_38, t2_39, t2_40, t2_41, t2_42, t2_43, t2_44, t2_45, t2_46, t2_47, t2_48, t2_49, t2_50, t2_51, t2_52, t2_53, t2_54, t2_55, t2_56, t2_57, t2_58, t2_59, t2_60, t2_61, t2_62, t2_63]
    digitProduct_word := cellOf t1 0
    encoded_word := cellOf t1 1
    for p_k in [1:21] do
      let t1 ← B.targets [none, none]
      B.chain
      let t2_0 : B Unit := do
        walkGroup_63 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 0 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_1 : B Unit := do
        walkGroup_64 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 1 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_2 : B Unit := do
        walkGroup_65 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 2 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_3 : B Unit := do
        walkGroup_66 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) DIGIT_GROUP 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_4 : B Unit := do
        walkGroup_64 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 4 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_5 : B Unit := do
        walkGroup_64 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 5 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_6 : B Unit := do
        walkGroup_65 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 6 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_7 : B Unit := do
        walkGroup_66 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 7 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_8 : B Unit := do
        walkGroup_67 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 8 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_9 : B Unit := do
        walkGroup_67 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 9 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_10 : B Unit := do
        walkGroup_68 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 10 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_11 : B Unit := do
        walkGroup_69 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 11 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_12 : B Unit := do
        walkGroup_70 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 12 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_13 : B Unit := do
        walkGroup_70 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 13 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_14 : B Unit := do
        walkGroup_71 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 14 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_15 : B Unit := do
        walkGroup_72 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 15 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_16 : B Unit := do
        walkGroup_64 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 16 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_17 : B Unit := do
        walkGroup_64 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 17 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_18 : B Unit := do
        walkGroup_65 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 18 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_19 : B Unit := do
        walkGroup_66 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 19 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_20 : B Unit := do
        walkGroup_64 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 20 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_21 : B Unit := do
        walkGroup_64 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 21 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_22 : B Unit := do
        walkGroup_65 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 22 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_23 : B Unit := do
        walkGroup_66 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 23 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_24 : B Unit := do
        walkGroup_67 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 24 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_25 : B Unit := do
        walkGroup_67 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 25 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_26 : B Unit := do
        walkGroup_68 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 26 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_27 : B Unit := do
        walkGroup_69 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 27 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_28 : B Unit := do
        walkGroup_70 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 28 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_29 : B Unit := do
        walkGroup_70 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 29 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_30 : B Unit := do
        walkGroup_71 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 30 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_31 : B Unit := do
        walkGroup_72 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 31 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_32 : B Unit := do
        walkGroup_73 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 32 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_33 : B Unit := do
        walkGroup_73 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 33 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_34 : B Unit := do
        walkGroup_74 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 34 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_35 : B Unit := do
        walkGroup_75 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 35 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_36 : B Unit := do
        walkGroup_73 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 36 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_37 : B Unit := do
        walkGroup_73 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 37 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_38 : B Unit := do
        walkGroup_74 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 38 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_39 : B Unit := do
        walkGroup_75 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 39 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_40 : B Unit := do
        walkGroup_76 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 40 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_41 : B Unit := do
        walkGroup_76 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 41 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_42 : B Unit := do
        walkGroup_77 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 42 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_43 : B Unit := do
        walkGroup_78 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 43 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_44 : B Unit := do
        walkGroup_79 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 44 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_45 : B Unit := do
        walkGroup_79 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 45 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_46 : B Unit := do
        walkGroup_80 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 46 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_47 : B Unit := do
        walkGroup_81 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 47 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_48 : B Unit := do
        walkGroup_82 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 48 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_49 : B Unit := do
        walkGroup_82 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 49 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_50 : B Unit := do
        walkGroup_83 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 50 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_51 : B Unit := do
        walkGroup_84 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 51 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_52 : B Unit := do
        walkGroup_82 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 52 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_53 : B Unit := do
        walkGroup_82 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 53 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_54 : B Unit := do
        walkGroup_83 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 54 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_55 : B Unit := do
        walkGroup_84 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 55 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_56 : B Unit := do
        walkGroup_85 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 56 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_57 : B Unit := do
        walkGroup_85 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 57 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_58 : B Unit := do
        walkGroup_86 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 58 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_59 : B Unit := do
        walkGroup_87 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 59 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_60 : B Unit := do
        walkGroup_88 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 60 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_61 : B Unit := do
        walkGroup_88 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 61 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_62 : B Unit := do
        walkGroup_89 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 62 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let t2_63 : B Unit := do
        walkGroup_90 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 63 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
      let _ ← B.matchArms (cellOf groups p_k) [t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7, t2_8, t2_9, t2_10, t2_11, t2_12, t2_13, t2_14, t2_15, t2_16, t2_17, t2_18, t2_19, t2_20, t2_21, t2_22, t2_23, t2_24, t2_25, t2_26, t2_27, t2_28, t2_29, t2_30, t2_31, t2_32, t2_33, t2_34, t2_35, t2_36, t2_37, t2_38, t2_39, t2_40, t2_41, t2_42, t2_43, t2_44, t2_45, t2_46, t2_47, t2_48, t2_49, t2_50, t2_51, t2_52, t2_53, t2_54, t2_55, t2_56, t2_57, t2_58, t2_59, t2_60, t2_61, t2_62, t2_63]
      digitProduct_word := cellOf t1 0
      encoded_word := cellOf t1 1
    let p_k := 21
    let t1 ← B.targets [none, none]
    let t2_0 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 0 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_1 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 1 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_2 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 2 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_3 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) DIGIT_GROUP 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_4 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 4 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_5 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 5 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_6 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 6 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_7 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 7 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_8 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 8 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_9 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 9 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_10 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 10 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_11 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 11 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_12 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 12 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_13 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 13 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_14 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 14 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_15 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 15 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_16 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 16 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_17 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 17 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_18 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 18 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_19 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 19 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_20 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 20 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_21 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 21 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_22 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 22 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_23 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 23 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_24 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 24 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_25 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 25 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_26 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 26 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_27 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 27 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_28 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 28 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_29 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 29 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_30 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 30 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_31 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 31 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_32 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 32 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_33 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 33 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_34 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 34 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_35 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 35 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_36 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 36 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_37 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 37 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_38 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 38 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_39 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 39 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_40 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 40 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_41 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 41 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_42 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 42 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_43 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 43 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_44 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 44 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_45 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 45 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_46 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 46 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_47 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 47 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_48 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 48 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_49 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 49 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_50 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 50 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_51 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 51 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_52 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 52 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_53 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 53 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_54 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 54 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_55 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 55 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_56 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 56 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_57 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 57 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_58 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 58 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_59 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 59 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_60 : B Unit := do
      walkGroup_91 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 60 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_61 : B Unit := do
      walkGroup_92 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 61 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_62 : B Unit := do
      walkGroup_93 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 62 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let t2_63 : B Unit := do
      walkGroup_94 at' pp walks powers (DIGIT_GROUP * p_k) (DIGIT_GROUP - ((DIGIT_GROUP - 1) * (p_k / (64 / DIGIT_GROUP)))) 63 0 powers digitProduct_word encoded_word [(cellOf t1 0).v, (cellOf t1 1).v]
    let _ ← B.matchArms (cellOf groups p_k) [t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7, t2_8, t2_9, t2_10, t2_11, t2_12, t2_13, t2_14, t2_15, t2_16, t2_17, t2_18, t2_19, t2_20, t2_21, t2_22, t2_23, t2_24, t2_25, t2_26, t2_27, t2_28, t2_29, t2_30, t2_31, t2_32, t2_33, t2_34, t2_35, t2_36, t2_37, t2_38, t2_39, t2_40, t2_41, t2_42, t2_43, t2_44, t2_45, t2_46, t2_47, t2_48, t2_49, t2_50, t2_51, t2_52, t2_53, t2_54, t2_55, t2_56, t2_57, t2_58, t2_59, t2_60, t2_61, t2_62, t2_63]
    digitProduct_word := cellOf t1 0
    encoded_word := cellOf t1 1
    B.assertEq encoded_word encoding
    B.assertEq digitProduct_word (← B.const (gpowE SP_TARGET_SUM))
    let leaf ← B.stackBuf 1
    let pkAt ← B.add a1 (← B.const (lit SP_WOTS_PK))
    let t3 ← spWord pp a0 pkAt walks (3 - 1) 3 0
    let t4 ← spWord pp a0 pkAt walks (3 - 1) 3 1
    let t5 ← spWord pp a0 pkAt walks (3 - 1) 3 2
    let t6 ← spWord pp a0 pkAt walks (3 - 1) 3 3
    let t7 ← spWord pp a0 pkAt walks (3 - 1) 3 4
    let t8 ← spWord pp a0 pkAt walks (3 - 1) 3 5
    let t9 ← spWord pp a0 pkAt walks (3 - 1) 3 6
    let t10 ← spWord pp a0 pkAt walks (3 - 1) 3 7
    let t11 ← spWord pp a0 pkAt walks (3 - 1) 3 8
    let t12 ← spWord pp a0 pkAt walks (3 - 1) 3 9
    let t13 ← spWord pp a0 pkAt walks (3 - 1) 3 10
    let t14 ← spWord pp a0 pkAt walks (3 - 1) 3 11
    let t15 ← spWord pp a0 pkAt walks (3 - 1) 3 12
    let t16 ← spWord pp a0 pkAt walks (3 - 1) 3 13
    let t17 ← spWord pp a0 pkAt walks (3 - 1) 3 14
    let t18 ← spWord pp a0 pkAt walks (3 - 1) 3 15
    let t19 ← spWord pp a0 pkAt walks (3 - 1) 3 16
    let t20 ← spWord pp a0 pkAt walks (3 - 1) 3 17
    let t21 ← spWord pp a0 pkAt walks (3 - 1) 3 18
    let t22 ← spWord pp a0 pkAt walks (3 - 1) 3 19
    let t23 ← spWord pp a0 pkAt walks (3 - 1) 3 20
    let t24 ← spWord pp a0 pkAt walks (3 - 1) 3 21
    let t25 ← spWord pp a0 pkAt walks (3 - 1) 3 22
    let t26 ← spWord pp a0 pkAt walks (3 - 1) 3 23
    let t27 ← spWord pp a0 pkAt walks (3 - 1) 3 24
    let t28 ← spWord pp a0 pkAt walks (3 - 1) 3 25
    let t29 ← spWord pp a0 pkAt walks (3 - 1) 3 26
    let t30 ← spWord pp a0 pkAt walks (3 - 1) 3 27
    let t31 ← spWord pp a0 pkAt walks (3 - 1) 3 28
    let t32 ← spWord pp a0 pkAt walks (3 - 1) 3 29
    let t33 ← spWord pp a0 pkAt walks (3 - 1) 3 30
    let t34 ← spWord pp a0 pkAt walks (3 - 1) 3 31
    let t35 ← spWord pp a0 pkAt walks (3 - 1) 3 32
    let t36 ← spWord pp a0 pkAt walks (3 - 1) 3 33
    let t37 ← spWord pp a0 pkAt walks (3 - 1) 3 34
    let t38 ← spWord pp a0 pkAt walks (3 - 1) 3 35
    let t39 ← spWord pp a0 pkAt walks (3 - 1) 3 36
    let t40 ← spWord pp a0 pkAt walks (3 - 1) 3 37
    let t41 ← spWord pp a0 pkAt walks (3 - 1) 3 38
    let t42 ← spWord pp a0 pkAt walks (3 - 1) 3 39
    let t43 ← spWord pp a0 pkAt walks (3 - 1) 3 40
    let t44 ← spWord pp a0 pkAt walks (3 - 1) 3 41
    let t45 ← spWord pp a0 pkAt walks (3 - 1) 3 42
    let t46 ← spWord pp a0 pkAt walks (3 - 1) 3 43
    let t47 ← spWord pp a0 pkAt walks (3 - 1) 3 44
    let t48 ← spWord pp a0 pkAt walks (3 - 1) 3 45
    let t49 ← spWord pp a0 pkAt walks (3 - 1) 3 46
    let t50 ← spWord pp a0 pkAt walks (3 - 1) 3 47
    let t51 ← spWord pp a0 pkAt walks (3 - 1) 3 48
    let t52 ← spWord pp a0 pkAt walks (3 - 1) 3 49
    let t53 ← spWord pp a0 pkAt walks (3 - 1) 3 50
    let t54 ← spWord pp a0 pkAt walks (3 - 1) 3 51
    let t55 ← spWord pp a0 pkAt walks (3 - 1) 3 52
    let t56 ← spWord pp a0 pkAt walks (3 - 1) 3 53
    let t57 ← spWord pp a0 pkAt walks (3 - 1) 3 54
    let t58 ← spWord pp a0 pkAt walks (3 - 1) 3 55
    let t59 ← spWord pp a0 pkAt walks (3 - 1) 3 56
    let t60 ← spWord pp a0 pkAt walks (3 - 1) 3 57
    let t61 ← spWord pp a0 pkAt walks (3 - 1) 3 58
    let t62 ← spWord pp a0 pkAt walks (3 - 1) 3 59
    let t63 ← spWord pp a0 pkAt walks (3 - 1) 3 60
    let t64 ← spWord pp a0 pkAt walks (3 - 1) 3 61
    let t65 ← spWord pp a0 pkAt walks (3 - 1) 3 62
    let t66 ← spWord pp a0 pkAt walks (3 - 1) 3 63
    let t67 ← spWord pp a0 pkAt walks (3 - 1) 3 64
    let t68 ← spWord pp a0 pkAt walks (3 - 1) 3 65
    let t69 ← spWord pp a0 pkAt walks (3 - 1) 3 66
    B.keccakCells (cells := (.words [.cell t3.v, .cell t4.v, .cell t5.v, .cell t6.v, .cell t7.v, .cell t8.v, .cell t9.v, .cell t10.v, .cell t11.v, .cell t12.v, .cell t13.v, .cell t14.v, .cell t15.v, .cell t16.v, .cell t17.v, .cell t18.v, .cell t19.v, .cell t20.v, .cell t21.v, .cell t22.v, .cell t23.v, .cell t24.v, .cell t25.v, .cell t26.v, .cell t27.v, .cell t28.v, .cell t29.v, .cell t30.v, .cell t31.v, .cell t32.v, .cell t33.v, .cell t34.v, .cell t35.v, .cell t36.v, .cell t37.v, .cell t38.v, .cell t39.v, .cell t40.v, .cell t41.v, .cell t42.v, .cell t43.v, .cell t44.v, .cell t45.v, .cell t46.v, .cell t47.v, .cell t48.v, .cell t49.v, .cell t50.v, .cell t51.v, .cell t52.v, .cell t53.v, .cell t54.v, .cell t55.v, .cell t56.v, .cell t57.v, .cell t58.v, .cell t59.v, .cell t60.v, .cell t61.v, .cell t62.v, .cell t63.v, .cell t64.v, .cell t65.v, .cell t66.v, .cell t67.v, .cell t68.v, .cell t69.v])) (out := (.frame leaf))
    return [.v (cellOf leaf 0).v]

set_option linter.unusedVariables false in
/-- `verify_sig_lean_sphincs` (`guests/lean_ethereum.py`, line 4179):

```
def verify_sig_lean_sphincs(signer, byte_bits):
    # `signer` is one 4-cell entry of the leanSPHINCS coverage table: the pubkey's PK.seed
    # and PK.root, then the message THAT signer signed, the two bound together by the
    # scheme's claim-list digest, as for leanXMSS.
    pp = signer[1]
    pk_root = signer[GEN]

    # ---- H_msg, which picks the index and every FORS leaf ----
    # H(R | PK.seed | PK.root | M | BE_32(i)) for i = 0, 1, M the claim's two cells.
    m0 = signer[GEN ** 2]
    m1 = signer[GEN ** 3]
    rho = hint_witness("sp_rand")
    d0 = StackBuf(2)
    d1 = StackBuf(1)
    keccak([rho, pp], [pk_root, m0], d0, tail=[m1, 0, 0, 0], len=SP_HMSG_LEN)
    keccak([rho, pp], [pk_root, m0], d1, tail=[m1, SP_COUNTER_ONE, 0, 0], len=SP_HMSG_LEN)

    # The digest's bits are advice pinned Boolean, and the digest is rebuilt from them:
    # byte by byte from the FORS leaves' values, which their shifts give, then the tree
    # index and the bottom leaf from the layers' leaves, the six bits the tree index
    # leaves from their own bits, and the second call's unused bytes as hinted bytes
    # (sp_from_bytes). Its high lane is what the rest leaves, checked to be a lane.
    bits0 = StackBuf(SP_CELL_BITS)
    bits1 = StackBuf(SP_CELL_BITS)
    bits2 = StackBuf(8 * SP_TAIL_BYTES)
    hint_decompose_bits(bits0, d0[0], SP_CELL_BITS)
    hint_decompose_bits(bits1, d0[1], SP_CELL_BITS)
    hint_decompose_bits(bits2, d1[0], 8 * SP_TAIL_BYTES)
    for b in unroll(0, SP_CELL_BITS):
        bits0[b] = bits0[b] * bits0[b]
        bits1[b] = bits1[b] * bits1[b]
    for b in unroll(0, 8 * SP_TAIL_BYTES):
        bits2[b] = bits2[b] * bits2[b]
    vals = StackBuf(SP_FORS_TREES * SP_FORS_HEIGHT)
    for c in unroll(0, SP_FORS_TREES):
        sp_fors_field(bits0, bits1, vals, c)
    lvals = StackBuf(SP_H)
    sp_leaf_shifts(bits1, bits2, lvals, 0, SP_HEIGHT_0)
    sp_leaf_shifts(bits1, bits2, lvals, SP_MID, SP_HEIGHT_1)
    sp_leaf_shifts(bits1, bits2, lvals, SP_TOP, SP_HEIGHT_2)
    md0 = sp_md_byte(vals, 0)
    for i in unroll(1, 16):
        md0 = md0 + sp_md_byte(vals, i)
    md1 = sp_md_byte(vals, 16)
    for i in unroll(17, SP_MD_BYTES):
        md1 = md1 + sp_md_byte(vals, i)
    # vals carries each tree's place across the trees (sp_fors_field), which the digest's
    # bytes do not: take it out again, a constant per byte.
    corr0 = 0
    corr1 = 0
    for i in unroll(0, SP_MD_BYTES):
        fc = 8 * i // SP_FORS_HEIGHT
        pc = 0
        if const(fc != (8 * i + 7) // SP_FORS_HEIGHT):
            pc = const((fc + 1) * 2 ** (8 * i + 8 - SP_FORS_HEIGHT * (fc + 1))) * const(2 ** (8 * (i % 16)))
        elif const(8 * i == SP_FORS_HEIGHT * fc):
            pc = const(fc * 256) * const(2 ** (8 * (i % 16)))
        if const(i // 16 == 0):
            corr0 = corr0 + pc
        else:
            corr1 = corr1 + pc
    # The tree index's middle byte, the top leaf's low byte; its high byte holds the top
    # leaf's two high bits, then six unused ones.
    tree_mid = lvals[SP_TOP] + lvals[SP_TOP + 8] * GEN ** 8
    pad = bits1[SP_TREE_HI_BIT + 7]
    for b in unroll(1, SP_PAD_BITS):
        pad = bits1[SP_TREE_HI_BIT + 7 - b] + GEN * pad
    d0[0] = md0 + corr0
    d0[1] = md1 + corr1 + (lvals[SP_TOP + 8] + pad * GEN ** SP_TOP_HIGH_BITS) * const(2 ** SP_TREE_HI_BIT) + tree_mid * const(2 ** SP_TREE_MID_BIT)
    unused_bytes = StackBuf(SP_UNUSED_BYTES)
    hint_witness(unused_bytes, "sp_unused")
    unused = sp_from_bytes(byte_bits, unused_bytes, SP_UNUSED_BYTES)
    high = (d1[0] + lvals[SP_MID] + lvals[0] * GEN ** 8 + unused * GEN ** (8 * SP_TAIL_BYTES)) * Y_INV
    assert_in_k(high, unused)

    # ---- FORS: each tree's opening climbed to its root, then T_k over the roots ----
    # The FORS addresses are the bottom key's: its layer and tree, its leaf the key pair.
    a0_b = lvals[SP_MID] * const(SP_TREE_MUL_0) + tree_mid * const(SP_TREE_MUL_1) + lvals[SP_TOP + 8] * const(SP_TREE_MUL_2)
    key_b = lvals[0] * const(SP_KEY_MUL_0)
    roots = StackBuf(SP_FORS_TREES)
    fors_at = key_b + const(SP_FORS_TREE)
    for c in unroll(0, SP_FORS_TREES):
        sp_fors_tree(pp, a0_b, fors_at, bits0, bits1, vals, roots, c)
    fors_pk = StackBuf(1)
    roots_at = key_b + const(SP_FORS_ROOTS)
    keccak_cells([sp_word(pp, a0_b, roots_at, roots, 0, 1, j) for j in unroll(0, 3 + SP_FORS_TREES)], fors_pk)

    # ---- the hypertree: each layer's one-time key signs what the layer below gives ----
    # The bottom key is in the digest's tree at its leaf; the middle key in that tree's
    # top bits at its low byte; the top key in tree zero at the tree's top bits.
    root_b = StackBuf(1)
    sp_layer(pp, a0_b, key_b, fors_pk[0], byte_bits, bits1, bits2, lvals, root_b, 0, SP_HEIGHT_0)
    a0_m = const(SP_LAYER_MUL) + tree_mid * const(SP_TREE_MUL_0) + lvals[SP_TOP + 8] * const(SP_TREE_MUL_1)
    key_m = lvals[SP_MID] * const(SP_KEY_MUL_0)
    root_m = StackBuf(1)
    sp_layer(pp, a0_m, key_m, root_b[0], byte_bits, bits1, bits2, lvals, root_m, SP_HEIGHT_0, SP_HEIGHT_1)
    a0_t = const(2 * SP_LAYER_MUL)
    key_t = tree_mid * const(SP_KEY_MUL_0) + lvals[SP_TOP + 8] * const(SP_KEY_MUL_1)
    root = StackBuf(1)
    sp_layer(pp, a0_t, key_t, root_m[0], byte_bits, bits1, bits2, lvals, root, SP_HEIGHT_0 + SP_HEIGHT_1, SP_HEIGHT_2)
    assert root[0] == pk_root
    return
```
-/
def verifySigLeanSphincs : GFn where
  name := "verify_sig_lean_sphincs"
  arity := 2
  rets := 0
  body ps := do
    let signer := cellOf ps 0
    let byteBits := cellOf ps 1
    let pp ← B.load signer 0
    let pkRoot ← B.load signer 1
    let m0 ← B.load signer 2
    let m1 ← B.load signer 3
    let rho ← hinted (B.witnessCell "sp_rand")
    let d0 ← B.stackBuf 2
    let d1 ← B.stackBuf 1
    B.keccak (a := (.words [.cell rho.v, .cell pp.v])) (b := (.words [.cell pkRoot.v, .cell m0.v])) (tail := some (.words [.cell m1.v, .zero, .zero, .zero])) (len := some SP_HMSG_LEN) (out := (.frame d0))
    B.keccak (a := (.words [.cell rho.v, .cell pp.v])) (b := (.words [.cell pkRoot.v, .cell m0.v])) (tail := some (.words [.cell m1.v, .cell (← B.const (lit SP_COUNTER_ONE)).v, .zero, .zero])) (len := some SP_HMSG_LEN) (out := (.frame d1))
    let bits0 ← B.stackBuf SP_CELL_BITS
    let bits1 ← B.stackBuf SP_CELL_BITS
    let bits2 ← B.stackBuf 16
    B.hintBits (.stack (bits0.take SP_CELL_BITS)) (cellOf d0 0) 0 SP_CELL_BITS
    B.hintBits (.stack (bits1.take SP_CELL_BITS)) (cellOf d0 1) 0 SP_CELL_BITS
    B.hintBits (.stack (bits2.take (8 * SP_TAIL_BYTES))) (cellOf d1 0) 0 (8 * SP_TAIL_BYTES)
    for b_k in [0:SP_CELL_BITS] do
      B.mulInto (cellOf bits0 b_k) (cellOf bits0 b_k) (cellOf bits0 b_k)
      B.mulInto (cellOf bits1 b_k) (cellOf bits1 b_k) (cellOf bits1 b_k)
    for b_k in [0:8 * SP_TAIL_BYTES] do
      B.mulInto (cellOf bits2 b_k) (cellOf bits2 b_k) (cellOf bits2 b_k)
    let vals ← B.stackBuf 240
    let c_k := 0
    spForsField bits0 bits1 vals c_k
    for c_k in [1:SP_FORS_TREES] do
      spForsField_2 bits0 bits1 vals c_k
    let lvals ← B.stackBuf SP_H
    spLeafShifts bits1 bits2 lvals 0 SP_HEIGHT_0
    spLeafShifts bits1 bits2 lvals 8 8
    spLeafShifts bits1 bits2 lvals SP_TOP SP_HEIGHT_2
    let mut md0 ← spMdByte vals 0
    for i_k in [1:4] do
      let t0 ← spMdByte vals i_k
      md0 ← B.add md0 t0
    for i_k in [4:6] do
      let t0 ← spMdByte_2 vals i_k
      md0 ← B.add md0 t0
    for i_k in [6:9] do
      let t0 ← spMdByte vals i_k
      md0 ← B.add md0 t0
    for i_k in [9:11] do
      let t0 ← spMdByte_2 vals i_k
      md0 ← B.add md0 t0
    for i_k in [11:14] do
      let t0 ← spMdByte vals i_k
      md0 ← B.add md0 t0
    for i_k in [14:16] do
      let t0 ← spMdByte_2 vals i_k
      md0 ← B.add md0 t0
    let mut md1 ← spMdByte_2 vals 16
    for i_k in [17:19] do
      let t1 ← spMdByte vals i_k
      md1 ← B.add md1 t1
    for i_k in [19:21] do
      let t1 ← spMdByte_2 vals i_k
      md1 ← B.add md1 t1
    for i_k in [21:24] do
      let t1 ← spMdByte vals i_k
      md1 ← B.add md1 t1
    for i_k in [24:26] do
      let t1 ← spMdByte_2 vals i_k
      md1 ← B.add md1 t1
    for i_k in [26:29] do
      let t1 ← spMdByte vals i_k
      md1 ← B.add md1 t1
    let i_k := 29
    let t1 ← spMdByte_2 vals i_k
    md1 ← B.add md1 t1
    let mut corr0 := 0
    let mut corr1 := 0
    let mut corr0_fe : E := default
    for i_k in [0:15] do
      let fc := (8 * i_k) / SP_FORS_HEIGHT
      let mut pc := 0
      if fc ≠ (((8 * i_k) + 7) / SP_FORS_HEIGHT) then
        pc := ((fc + 1) * (2 ^ (((8 * i_k) + 8) - (SP_FORS_HEIGHT * (fc + 1))))) * (2 ^ (8 * (i_k % 16)))
      else
        if (8 * i_k) = (SP_FORS_HEIGHT * fc) then
          pc := (fc * 256) * (2 ^ (8 * (i_k % 16)))
        else
          pure ()
      if (i_k / 16) = 0 then
        corr0 := corr0 + pc
      else
        pure () -- no use of this definition takes this branch
    let i_k := 15
    let fc := (8 * i_k) / SP_FORS_HEIGHT
    let pc := 0
    let mut pc_fe : E := default
    if fc ≠ (((8 * i_k) + 7) / SP_FORS_HEIGHT) then
      pure () -- no use of this definition takes this branch
    else
      if (8 * i_k) = (SP_FORS_HEIGHT * fc) then
        pc_fe := (lit (fc * 256)) * (lit (2 ^ (8 * (i_k % 16))))
      else
        pure () -- no use of this definition takes this branch
    if (i_k / 16) = 0 then
      corr0_fe := (lit corr0) + pc_fe
    else
      pure () -- no use of this definition takes this branch
    for i_k in [16:SP_MD_BYTES] do
      let fc := (8 * i_k) / SP_FORS_HEIGHT
      let mut pc := 0
      if fc ≠ (((8 * i_k) + 7) / SP_FORS_HEIGHT) then
        pc := ((fc + 1) * (2 ^ (((8 * i_k) + 8) - (SP_FORS_HEIGHT * (fc + 1))))) * (2 ^ (8 * (i_k % 16)))
      else
        if (8 * i_k) = (SP_FORS_HEIGHT * fc) then
          pc := (fc * 256) * (2 ^ (8 * (i_k % 16)))
        else
          pure ()
      if (i_k / 16) = 0 then
        pure () -- no use of this definition takes this branch
      else
        corr1 := corr1 + pc
    let treeMid ← B.add (cellOf lvals SP_TOP) (← B.mul (cellOf lvals (SP_TOP + 8)) (← B.const (gpowE 8)))
    let mut pad := cellOf bits1 (SP_TREE_HI_BIT + 7)
    for b_k in [1:SP_PAD_BITS] do
      pad ← B.add (cellOf bits1 ((SP_TREE_HI_BIT + 7) - b_k)) (← B.shifted pad 1)
    B.addInto (cellOf d0 0) md0 (← B.const corr0_fe)
    B.addInto (cellOf d0 1) (← B.add (← B.add md1 (← B.const (lit corr1))) (← B.mul (← B.add (cellOf lvals (SP_TOP + 8)) (← B.shifted pad 2)) (← B.const (lit (2 ^ SP_TREE_HI_BIT))))) (← B.mul treeMid (← B.const (lit (2 ^ SP_TREE_MID_BIT))))
    let unusedBytes ← B.stackBuf SP_UNUSED_BYTES
    B.witness "sp_unused" (.stack unusedBytes)
    let unused ← spFromBytes byteBits unusedBytes SP_UNUSED_BYTES
    let high ← B.mul (← B.add (← B.add (← B.add (cellOf d1 0) (cellOf lvals 8)) (← B.mul (cellOf lvals 0) (← B.const (gpowE 8)))) (← B.shifted unused 16)) (← B.const (lit Y_INV))
    B.assertInK high unused
    let a0B ← B.add (← B.add (← B.mul (cellOf lvals 8) (← B.const (lit SP_TREE_MUL_0))) (← B.mul treeMid (← B.const (lit SP_TREE_MUL_1)))) (← B.mul (cellOf lvals (SP_TOP + 8)) (← B.const (lit SP_TREE_MUL_2)))
    let keyB ← B.mul (cellOf lvals 0) (← B.const (lit SP_KEY_MUL_0))
    let roots ← B.stackBuf SP_FORS_TREES
    let forsAt ← B.add keyB (← B.const (lit SP_FORS_TREE))
    let c_k := 0
    spForsTree pp a0B forsAt bits0 bits1 vals roots c_k
    let c_k := 1
    spForsTree_2 pp a0B forsAt bits0 bits1 vals roots c_k
    for c_k in [2:4] do
      spForsTree_3 pp a0B forsAt bits0 bits1 vals roots c_k
    for c_k in [4:8] do
      spForsTree_4 pp a0B forsAt bits0 bits1 vals roots c_k
    for c_k in [8:16] do
      spForsTree_5 pp a0B forsAt bits0 bits1 vals roots c_k
    for c_k in [16:SP_FORS_TREES] do
      spForsTree_6 pp a0B forsAt bits0 bits1 vals roots c_k
    let forsPk ← B.stackBuf 1
    let rootsAt ← B.add keyB (← B.const (lit SP_FORS_ROOTS))
    let t2 ← spWord pp a0B rootsAt roots 0 1 0
    let t3 ← spWord pp a0B rootsAt roots 0 1 1
    let t4 ← spWord pp a0B rootsAt roots 0 1 2
    let t5 ← spWord pp a0B rootsAt roots 0 1 3
    let t6 ← spWord pp a0B rootsAt roots 0 1 4
    let t7 ← spWord pp a0B rootsAt roots 0 1 5
    let t8 ← spWord pp a0B rootsAt roots 0 1 6
    let t9 ← spWord pp a0B rootsAt roots 0 1 7
    let t10 ← spWord pp a0B rootsAt roots 0 1 8
    let t11 ← spWord pp a0B rootsAt roots 0 1 9
    let t12 ← spWord pp a0B rootsAt roots 0 1 10
    let t13 ← spWord pp a0B rootsAt roots 0 1 11
    let t14 ← spWord pp a0B rootsAt roots 0 1 12
    let t15 ← spWord pp a0B rootsAt roots 0 1 13
    let t16 ← spWord pp a0B rootsAt roots 0 1 14
    let t17 ← spWord pp a0B rootsAt roots 0 1 15
    let t18 ← spWord pp a0B rootsAt roots 0 1 16
    let t19 ← spWord pp a0B rootsAt roots 0 1 17
    let t20 ← spWord pp a0B rootsAt roots 0 1 18
    let t21 ← spWord pp a0B rootsAt roots 0 1 19
    let t22 ← spWord pp a0B rootsAt roots 0 1 20
    let t23 ← spWord pp a0B rootsAt roots 0 1 21
    let t24 ← spWord pp a0B rootsAt roots 0 1 22
    let t25 ← spWord pp a0B rootsAt roots 0 1 23
    let t26 ← spWord pp a0B rootsAt roots 0 1 24
    let t27 ← spWord pp a0B rootsAt roots 0 1 25
    let t28 ← spWord pp a0B rootsAt roots 0 1 26
    B.keccakCells (cells := (.words [.cell t2.v, .cell t3.v, .cell t4.v, .cell t5.v, .cell t6.v, .cell t7.v, .cell t8.v, .cell t9.v, .cell t10.v, .cell t11.v, .cell t12.v, .cell t13.v, .cell t14.v, .cell t15.v, .cell t16.v, .cell t17.v, .cell t18.v, .cell t19.v, .cell t20.v, .cell t21.v, .cell t22.v, .cell t23.v, .cell t24.v, .cell t25.v, .cell t26.v, .cell t27.v, .cell t28.v])) (out := (.frame forsPk))
    let rootB ← B.stackBuf 1
    spLayer pp a0B keyB (cellOf forsPk 0) byteBits bits1 bits2 lvals rootB 0 SP_HEIGHT_0
    let a0M ← B.add (← B.add (← B.const (lit SP_LAYER_MUL)) (← B.mul treeMid (← B.const (lit SP_TREE_MUL_0)))) (← B.mul (cellOf lvals (SP_TOP + 8)) (← B.const (lit SP_TREE_MUL_1)))
    let keyM ← B.mul (cellOf lvals SP_MID) (← B.const (lit SP_KEY_MUL_0))
    let rootM ← B.stackBuf 1
    spLayer pp a0M keyM (cellOf rootB 0) byteBits bits1 bits2 lvals rootM 8 8
    let a0T := 2 * SP_LAYER_MUL
    let keyT ← B.add (← B.mul treeMid (← B.const (lit SP_KEY_MUL_0))) (← B.mul (cellOf lvals (SP_TOP + 8)) (← B.const (lit SP_KEY_MUL_1)))
    let root ← B.stackBuf 1
    spLayer_2 pp (lit a0T) keyT (cellOf rootM 0) byteBits bits1 bits2 lvals root (8 + 8) SP_HEIGHT_2
    B.assertEq (cellOf root 0) pkRoot
    return []

end
end LeanVM.Dsl.Gen
