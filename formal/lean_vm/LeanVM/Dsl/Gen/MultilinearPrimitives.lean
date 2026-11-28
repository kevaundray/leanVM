/-
  LeanVM.Dsl.Gen.MultilinearPrimitives

  The guest's section `MultilinearPrimitives`, translated.
-/

module

public import LeanVM.Dsl.Gen.Inline

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

set_option linter.unusedVariables false in
/-- `eq_prefix_chain` (`guests/lean_ethereum.py`, line 987):

```
def eq_prefix_chain(chain, seed, a, b1, count_g):
    # Prefix products of eq(a_k, b_k) = a_k + b1_k, b1 = 1 + b, from `seed`, so a
    # reader picks the partial product up at its own certified length. Entry t is
    # written from inputs with index < t only, so a garbage tail past a buffer's
    # written extent cannot corrupt any shorter prefix.
    assert log(count_g) < EQ_CHAIN_ARMS
    done = match(log(count_g), range(0, EQ_CHAIN_ARMS), lambda n: eq_prefix_run(chain, seed, a, b1, n))  # a match needs a target
    return
```
-/
def eqPrefixChain : GFn where
  name := "eq_prefix_chain"
  arity := 5
  rets := 0
  body ps := do
    let chain := cellOf ps 0
    let seed := cellOf ps 1
    let a := cellOf ps 2
    let b1 := cellOf ps 3
    let countG := cellOf ps 4
    let _ ← B.rangeCheck countG EQ_CHAIN_ARMS
    let t0 ← B.targets [none]
    B.dispatchInto countG ((List.range EQ_CHAIN_ARMS).map fun arm => (instName "eq_prefix_run" [.L arm])) [chain.v, seed.v, a.v, b1.v] t0
    let done := cellOf t0 0
    return []

set_option linter.unusedVariables false in
/-- `rs_eq_run` (`guests/lean_ethereum.py`, line 1034):

```
def rs_eq_run(z_vals, point1, count_g):
    # One run of the telescoped ring-switch product E = sum_k c_k * prod_j
    # (z_j^(2^k) + 1 + ris_j): coordinate x multiplies row k by (z^(2^k) + 1 +
    # point_x), z evolving by squaring per row. The runtime coordinates walk
    # OUTSIDE and the fixed Frobenius powers inside, so nothing stores a z-power
    # table. Coordinates go RS_CHUNK an iteration, so a row is read and written once
    # per chunk; count = RS_CHUNK q + r is pinned from advice bits, and the r left
    # over run after the loop. The chain holds the starting row of ones and a row per
    # chunk, q + 2 rows at most. Returns the final row.
    bits = StackBuf(RS_COUNT_BITS)
    hint_decompose_bits_exponent(bits, count_g, RS_COUNT_BITS)
    r_g = GEN ** 0
    q_g = GEN ** 0
    for k in unroll(0, RS_COUNT_BITS):
        b = bits[k]
        bits[k] = b * b
        if const(k // RS_CHUNK_BITS == 0):
            r_g *= 1 + b * (1 + GEN ** (2 ** k))
        else:
            q_g *= 1 + b * (1 + GEN ** (2 ** (k - RS_CHUNK_BITS)))
    assert q_g ** RS_CHUNK * r_g == count_g
    chain = HeapBuf((q_g * GEN ** 2) ** BASE_FIELD_BITS)
    for k in unroll(0, BASE_FIELD_BITS):
        chain[GEN ** k] = 1
    for xq in mul_range(1, q_g):
        base = xq ** RS_CHUNK
        done = rs_eq_rows(chain * xq ** BASE_FIELD_BITS, z_vals * base, point1 * base, RS_CHUNK)
    base = q_g ** RS_CHUNK
    row = chain * q_g ** BASE_FIELD_BITS
    last = match(log(r_g), range(0, RS_CHUNK), lambda n: rs_eq_rows(row, z_vals * base, point1 * base, n))
    return last
```
-/
def rsEqRun : GFn where
  name := "rs_eq_run"
  arity := 3
  rets := 1
  body ps := do
    let zVals := cellOf ps 0
    let point1 := cellOf ps 1
    let countG := cellOf ps 2
    let bits ← B.stackBuf RS_COUNT_BITS
    B.hintBitsExpTo (.stack (bits.take RS_COUNT_BITS)) countG RS_COUNT_BITS
    let rG : GPow := ⟨0⟩
    let qG : GPow := ⟨0⟩
    let mut rG_word : Word := default
    let mut qG_word : Word := default
    let k_k := 0
    let b := cellOf bits k_k
    B.mulInto (cellOf bits k_k) b b
    if (k_k / RS_CHUNK_BITS) = 0 then
      rG_word ← B.add (← B.const 1) (← B.mul b (← B.const (1 + (gpowE (2 ^ k_k)))))
    else
      pure () -- no use of this definition takes this branch
    for k_k in [1:4] do
      let b := cellOf bits k_k
      B.mulInto (cellOf bits k_k) b b
      if (k_k / RS_CHUNK_BITS) = 0 then
        rG_word ← B.mul rG_word (← B.add (← B.const 1) (← B.mul b (← B.const (1 + (gpowE (2 ^ k_k))))))
      else
        qG_word ← B.add (← B.const 1) (← B.mul b (← B.const (1 + (gpowE (2 ^ (k_k - RS_CHUNK_BITS))))))
    for k_k in [4:RS_COUNT_BITS] do
      let b := cellOf bits k_k
      B.mulInto (cellOf bits k_k) b b
      if (k_k / RS_CHUNK_BITS) = 0 then
        pure () -- no use of this definition takes this branch
      else
        qG_word ← B.mul qG_word (← B.add (← B.const 1) (← B.mul b (← B.const (1 + (gpowE (2 ^ (k_k - RS_CHUNK_BITS)))))))
    B.assertEq (← B.mul (← B.pow qG_word RS_CHUNK) rG_word) countG
    let chain ← B.heapBufDyn (← B.pow (← B.shifted qG_word 2) BASE_FIELD_BITS)
    for k_k in [0:BASE_FIELD_BITS] do
      B.store chain k_k (← B.const 1)
    B.loopRtF 0 (pure qG_word) 3 (pure ([chain.v, zVals.v, point1.v])) fun xq caps => do
      let chain := cellOf caps 0
      let zVals := cellOf caps 1
      let point1 := cellOf caps 2
      let base ← B.pow xq RS_CHUNK
      let done ← call1 (instName "rs_eq_rows" [.L RS_CHUNK]) [(← B.mul chain (← B.pow xq BASE_FIELD_BITS)).v, (← B.mul zVals base).v, (← B.mul point1 base).v]
      pure ()
    let base ← B.pow qG_word RS_CHUNK
    let row ← B.mul chain (← B.pow qG_word BASE_FIELD_BITS)
    let t0 ← B.targets [none]
    let t1 ← B.mul zVals base
    let t2 ← B.mul point1 base
    B.dispatchInto rG_word ((List.range RS_CHUNK).map fun arm => (instName "rs_eq_rows" [.L arm])) [row.v, t1.v, t2.v] t0
    let last := cellOf t0 0
    return [.v last.v]

set_option linter.unusedVariables false in
/-- `sumcheck_round4` (`guests/lean_ethereum.py`, line 1088):

```
def sumcheck_round4(rd, msg_cursor, claim, tabs):
    # One PLAIN sumcheck round, from the sponge of round record `rd` into the next
    # record's. The prover sends the round polynomial's coefficients bar the one the
    # split h(0) + h(1) == claim fixes, so the verifier derives that one and reads h
    # at the challenge by Horner. Nothing is reapplied: no eq factor, no separate
    # term for the tables still waiting, and the eq point is not read here at all.
    sp = fs_load(rd, ROUND_FS, 1)
    rate = StackBuf(8)
    c0, msg_cursor = fs_next(rate, 0, msg_cursor)
    c2, msg_cursor = fs_next(rate, 1, msg_cursor)
    c3, msg_cursor = fs_next(rate, 2, msg_cursor)
    # The split identity fixes c1 = claim + c2 + c3, so it is neither sent nor bound,
    # and h(y) = c0 + y (claim + (1 + y) (c2 + (1 + y) c3)). Then the round's grind.
    sp, y, msg_cursor = fs_grind_squeeze(sp, rate, 3, msg_cursor, tabs, ROUND3_GRIND_BITS)
    fs_store(rd * GEN ** ROUND_SLOTS, ROUND_FS, 1, sp)
    y1 = 1 + y
    return msg_cursor, c0 + y * (claim + y1 * (c2 + y1 * c3)), y
```
-/
def sumcheckRound4 : GFn where
  name := "sumcheck_round4"
  arity := 4
  rets := 3
  body ps := do
    let rd := cellOf ps 0
    let msgCursor := cellOf ps 1
    let claim := cellOf ps 2
    let tabs := cellOf ps 3
    let sp ← fsLoad rd ROUND_FS 1
    let rate ← B.stackBuf 8
    let (t0, t1) ← fsNext rate 0 msgCursor
    let c0 := t0
    let msgCursor_ptr : Shifted := t1
    let (t2, t3) ← fsNext_2 rate 1 (⟨msgCursor_ptr.base, msgCursor_ptr.exp⟩)
    let c2 := t2
    let msgCursor_ptr : Shifted := t3
    let (t4, t5) ← fsNext_2 rate 2 (⟨msgCursor_ptr.base, msgCursor_ptr.exp⟩)
    let c3 := t4
    let msgCursor_ptr : Shifted := t5
    let (t6, t7, t8) ← fsGrindSqueeze sp rate 3 (⟨msgCursor_ptr.base, msgCursor_ptr.exp⟩) tabs ROUND3_GRIND_BITS
    let sp := t6
    let y := t7
    let msgCursor_ptr : Shifted := t8
    fsStore (⟨rd, ROUND_SLOTS⟩) ROUND_FS 1 sp
    let y1 ← B.add (← B.const 1) y
    let t9 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted msgCursor_ptr.base msgCursor_ptr.exp)
    let t10 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) c0 (← B.mul y (← B.add claim (← B.mul y1 (← B.add c2 (← B.mul y1 c3)))))
    return [.into t9] ++ [.into t10] ++ [.v y.v]

set_option linter.unusedVariables false in
/-- `eq_prefix_run`, a `Const` family (`guests/lean_ethereum.py`, line 997):

```
def eq_prefix_run(chain, seed, a, b1, n: Const):
    chain[GEN ** 0] = seed
    v = seed
    for k in unroll(0, n):
        v = v * (a[GEN ** k] + b1[GEN ** k])
        chain[GEN ** (k + 1)] = v
    return 0
```
-/
def eqPrefixRun (n : Nat) : GFn where
  name := instName "eq_prefix_run" [.L n]
  arity := 4
  rets := 1
  body ps := do
    let chain := cellOf ps 0
    let seed := cellOf ps 1
    let a := cellOf ps 2
    let b1 := cellOf ps 3
    B.store chain 0 seed
    let v := seed
    return [.c 0]

set_option linter.unusedVariables false in
/-- `eq_prefix_run`, a `Const` family (`guests/lean_ethereum.py`, line 997):

```
def eq_prefix_run(chain, seed, a, b1, n: Const):
    chain[GEN ** 0] = seed
    v = seed
    for k in unroll(0, n):
        v = v * (a[GEN ** k] + b1[GEN ** k])
        chain[GEN ** (k + 1)] = v
    return 0
```
-/
def eqPrefixRun_2 (n : Nat) : GFn where
  name := instName "eq_prefix_run" [.L n]
  arity := 4
  rets := 1
  body ps := do
    let chain := cellOf ps 0
    let seed := cellOf ps 1
    let a := cellOf ps 2
    let b1 := cellOf ps 3
    B.store chain 0 seed
    let mut v := seed
    let k_k := 0
    v ← B.mul v (← B.add (← B.load a k_k) (← B.load b1 k_k))
    B.store chain (k_k + 1) v
    return [.c 0]

set_option linter.unusedVariables false in
/-- `eq_prefix_run`, a `Const` family (`guests/lean_ethereum.py`, line 997):

```
def eq_prefix_run(chain, seed, a, b1, n: Const):
    chain[GEN ** 0] = seed
    v = seed
    for k in unroll(0, n):
        v = v * (a[GEN ** k] + b1[GEN ** k])
        chain[GEN ** (k + 1)] = v
    return 0
```
-/
def eqPrefixRun_3 (n : Nat) : GFn where
  name := instName "eq_prefix_run" [.L n]
  arity := 4
  rets := 1
  body ps := do
    let chain := cellOf ps 0
    let seed := cellOf ps 1
    let a := cellOf ps 2
    let b1 := cellOf ps 3
    B.store chain 0 seed
    let mut v := seed
    for k_k in [0:n] do
      v ← B.mul v (← B.add (← B.load a k_k) (← B.load b1 k_k))
      B.store chain (k_k + 1) v
    return [.c 0]

set_option linter.unusedVariables false in
/-- `rs_eq_rows`, a `Const` family (`guests/lean_ethereum.py`, line 1012):

```
def rs_eq_rows(row, zs, ps, n: Const):
    # Coordinates 0..n of zs/ps multiply rows 0..64 of `row` into the next row, row k
    # by prod_i (zs_i^(2^k) + ps_i), the Frobenius powers walked inside.
    nxt = row * GEN ** BASE_FIELD_BITS
    if const(n == 0):
        nxt = row
    else:
        zv = StackBuf(RS_CHUNK * BASE_FIELD_BITS)  # zv[64 i + k] = zs_i^(2^k)
        a = StackBuf(RS_CHUNK)
        for i in unroll(0, n):
            zv[BASE_FIELD_BITS * i] = zs[GEN ** i]
            a[i] = ps[GEN ** i]
        for k in unroll(0, BASE_FIELD_BITS):
            acc = row[GEN ** k]
            for i in unroll(0, n):
                acc *= zv[BASE_FIELD_BITS * i + k] + a[i]
                if const(k != BASE_FIELD_BITS - 1):
                    zv[BASE_FIELD_BITS * i + k + 1] = zv[BASE_FIELD_BITS * i + k] * zv[BASE_FIELD_BITS * i + k]
            nxt[GEN ** k] = acc
    return nxt
```
-/
def rsEqRows (n : Nat) : GFn where
  name := instName "rs_eq_rows" [.L n]
  arity := 3
  rets := 1
  body ps := do
    let row := cellOf ps 0
    let zs := cellOf ps 1
    let ps' := cellOf ps 2
    let nxt : Shifted := ⟨row, BASE_FIELD_BITS⟩
    if n = 0 then
      pure () -- no use of this definition takes this branch
    else
      let zv ← B.stackBuf 512
      let a ← B.stackBuf RS_CHUNK
      for i_k in [0:n] do
        B.loadInto (cellOf zv (BASE_FIELD_BITS * i_k)) zs i_k
        B.loadInto (cellOf a i_k) ps' i_k
      for k_k in [0:BASE_FIELD_BITS] do
        let mut acc ← B.load row k_k
        for i_k in [0:n] do
          acc ← B.mul acc (← B.add (cellOf zv ((BASE_FIELD_BITS * i_k) + k_k)) (cellOf a i_k))
          if k_k ≠ (BASE_FIELD_BITS - 1) then
            B.mulInto (cellOf zv (((BASE_FIELD_BITS * i_k) + k_k) + 1)) (cellOf zv ((BASE_FIELD_BITS * i_k) + k_k)) (cellOf zv ((BASE_FIELD_BITS * i_k) + k_k))
          else
            pure ()
        B.store nxt.base (nxt.exp + k_k) acc
    let t0 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted nxt.base nxt.exp)
    return [.into t0]

set_option linter.unusedVariables false in
/-- `rs_eq_rows`, a `Const` family (`guests/lean_ethereum.py`, line 1012):

```
def rs_eq_rows(row, zs, ps, n: Const):
    # Coordinates 0..n of zs/ps multiply rows 0..64 of `row` into the next row, row k
    # by prod_i (zs_i^(2^k) + ps_i), the Frobenius powers walked inside.
    nxt = row * GEN ** BASE_FIELD_BITS
    if const(n == 0):
        nxt = row
    else:
        zv = StackBuf(RS_CHUNK * BASE_FIELD_BITS)  # zv[64 i + k] = zs_i^(2^k)
        a = StackBuf(RS_CHUNK)
        for i in unroll(0, n):
            zv[BASE_FIELD_BITS * i] = zs[GEN ** i]
            a[i] = ps[GEN ** i]
        for k in unroll(0, BASE_FIELD_BITS):
            acc = row[GEN ** k]
            for i in unroll(0, n):
                acc *= zv[BASE_FIELD_BITS * i + k] + a[i]
                if const(k != BASE_FIELD_BITS - 1):
                    zv[BASE_FIELD_BITS * i + k + 1] = zv[BASE_FIELD_BITS * i + k] * zv[BASE_FIELD_BITS * i + k]
            nxt[GEN ** k] = acc
    return nxt
```
-/
def rsEqRows_2 (n : Nat) : GFn where
  name := instName "rs_eq_rows" [.L n]
  arity := 3
  rets := 1
  body ps := do
    let row := cellOf ps 0
    let zs := cellOf ps 1
    let ps' := cellOf ps 2
    let nxt : Shifted := ⟨row, BASE_FIELD_BITS⟩
    let mut nxt_word : Word := default
    if n = 0 then
      nxt_word := row
    else
      pure () -- no use of this definition takes this branch
    return [.v nxt_word.v]

set_option linter.unusedVariables false in
/-- `rs_eq_rows`, a `Const` family (`guests/lean_ethereum.py`, line 1012):

```
def rs_eq_rows(row, zs, ps, n: Const):
    # Coordinates 0..n of zs/ps multiply rows 0..64 of `row` into the next row, row k
    # by prod_i (zs_i^(2^k) + ps_i), the Frobenius powers walked inside.
    nxt = row * GEN ** BASE_FIELD_BITS
    if const(n == 0):
        nxt = row
    else:
        zv = StackBuf(RS_CHUNK * BASE_FIELD_BITS)  # zv[64 i + k] = zs_i^(2^k)
        a = StackBuf(RS_CHUNK)
        for i in unroll(0, n):
            zv[BASE_FIELD_BITS * i] = zs[GEN ** i]
            a[i] = ps[GEN ** i]
        for k in unroll(0, BASE_FIELD_BITS):
            acc = row[GEN ** k]
            for i in unroll(0, n):
                acc *= zv[BASE_FIELD_BITS * i + k] + a[i]
                if const(k != BASE_FIELD_BITS - 1):
                    zv[BASE_FIELD_BITS * i + k + 1] = zv[BASE_FIELD_BITS * i + k] * zv[BASE_FIELD_BITS * i + k]
            nxt[GEN ** k] = acc
    return nxt
```
-/
def rsEqRows_3 (n : Nat) : GFn where
  name := instName "rs_eq_rows" [.L n]
  arity := 3
  rets := 1
  body ps := do
    let row := cellOf ps 0
    let zs := cellOf ps 1
    let ps' := cellOf ps 2
    let nxt : Shifted := ⟨row, BASE_FIELD_BITS⟩
    if n = 0 then
      pure () -- no use of this definition takes this branch
    else
      let zv ← B.stackBuf 512
      let a ← B.stackBuf RS_CHUNK
      let i_k := 0
      B.loadInto (cellOf zv (BASE_FIELD_BITS * i_k)) zs i_k
      B.loadInto (cellOf a i_k) ps' i_k
      for k_k in [0:BASE_FIELD_BITS] do
        let mut acc ← B.load row k_k
        let i_k := 0
        acc ← B.mul acc (← B.add (cellOf zv ((BASE_FIELD_BITS * i_k) + k_k)) (cellOf a i_k))
        if k_k ≠ (BASE_FIELD_BITS - 1) then
          B.mulInto (cellOf zv (((BASE_FIELD_BITS * i_k) + k_k) + 1)) (cellOf zv ((BASE_FIELD_BITS * i_k) + k_k)) (cellOf zv ((BASE_FIELD_BITS * i_k) + k_k))
        else
          pure ()
        B.store nxt.base (nxt.exp + k_k) acc
    let t0 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted nxt.base nxt.exp)
    return [.into t0]

set_option linter.unusedVariables false in
/-- `gkr_rounds`, a `Const` family (`guests/lean_ethereum.py`, line 1107):

```
def gkr_rounds(rd, pt, tabs, n: Const):
    # n GKR rounds, from the round record at `rd` (ROUND_SLOTS consecutive fields) to the
    # one n further. The prover sends every coefficient but c0, which the round's
    # pulled-out eq factor leaves fixed: c0 + r (c1 + ... + c4) == claim, r being the
    # previous point's coordinate pt[q], then the round's grind; the challenge goes to
    # pt[MU_CAP + 2 + q].
    if const(n != 0):
        sp = fs_load(rd, ROUND_FS, 1)
        cur = rd[GEN ** ROUND_CURSOR]
        claim = rd[GEN ** ROUND_CLAIM]
        for q in unroll(0, n):
            rate = StackBuf(8)
            c1, cur = fs_next(rate, 0, cur)
            c2, cur = fs_next(rate, 1, cur)
            c3, cur = fs_next(rate, 2, cur)
            c4, cur = fs_next(rate, 3, cur)
            sp, rk, cur = fs_grind_squeeze(sp, rate, 4, cur, tabs, ROUND5_GRIND_BITS)
            c0 = claim + pt[GEN ** q] * (c1 + c2 + c3 + c4)
            pt[GEN ** (MU_CAP + 2 + q)] = rk
            claim = c0 + rk * (c1 + rk * (c2 + rk * (c3 + rk * c4)))
        rd_next = rd * GEN ** (ROUND_SLOTS * n)
        fs_store(rd_next, ROUND_FS, 1, sp)
        rd_next[GEN ** ROUND_CURSOR] = cur
        rd_next[GEN ** ROUND_CLAIM] = claim
    return 0
```
-/
def gkrRounds (n : Nat) : GFn where
  name := instName "gkr_rounds" [.L n]
  arity := 3
  rets := 1
  body ps := do
    let rd := cellOf ps 0
    let pt := cellOf ps 1
    let tabs := cellOf ps 2
    if n ≠ 0 then
      let mut sp ← fsLoad rd ROUND_FS 1
      let cur ← B.load rd ROUND_CURSOR
      let mut claim ← B.load rd ROUND_CLAIM
      let mut cur_ptr : Shifted := default
      let q_k := 0
      let rate ← B.stackBuf 8
      let (t0, t1) ← fsNext rate 0 cur
      let c1 := t0
      cur_ptr := t1
      let (t2, t3) ← fsNext_2 rate 1 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c2 := t2
      cur_ptr := t3
      let (t4, t5) ← fsNext_2 rate 2 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c3 := t4
      cur_ptr := t5
      let (t6, t7) ← fsNext_2 rate 3 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c4 := t6
      cur_ptr := t7
      let (t8, t9, t10) ← fsGrindSqueeze sp rate 4 (⟨cur_ptr.base, cur_ptr.exp⟩) tabs ROUND5_GRIND_BITS
      sp := t8
      let rk := t9
      cur_ptr := t10
      let c0 ← B.add claim (← B.mul (← B.load pt q_k) (← B.add (← B.add (← B.add c1 c2) c3) c4))
      B.store pt ((MU_CAP + 2) + q_k) rk
      claim ← B.add c0 (← B.mul rk (← B.add c1 (← B.mul rk (← B.add c2 (← B.mul rk (← B.add c3 (← B.mul rk c4)))))))
      let q_k := 1
      let rate ← B.stackBuf 8
      let (t0, t1) ← fsNext_2 rate 0 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c1 := t0
      cur_ptr := t1
      let (t2, t3) ← fsNext_2 rate 1 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c2 := t2
      cur_ptr := t3
      let (t4, t5) ← fsNext_2 rate 2 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c3 := t4
      cur_ptr := t5
      let (t6, t7) ← fsNext_2 rate 3 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c4 := t6
      cur_ptr := t7
      let (t8, t9, t10) ← fsGrindSqueeze sp rate 4 (⟨cur_ptr.base, cur_ptr.exp⟩) tabs ROUND5_GRIND_BITS
      sp := t8
      let rk := t9
      cur_ptr := t10
      let c0 ← B.add claim (← B.mul (← B.load pt q_k) (← B.add (← B.add (← B.add c1 c2) c3) c4))
      B.store pt ((MU_CAP + 2) + q_k) rk
      claim ← B.add c0 (← B.mul rk (← B.add c1 (← B.mul rk (← B.add c2 (← B.mul rk (← B.add c3 (← B.mul rk c4)))))))
      let rdNext : Shifted := ⟨rd, ROUND_SLOTS * n⟩
      fsStore (⟨rdNext.base, rdNext.exp⟩) ROUND_FS 1 sp
      B.store rdNext.base (rdNext.exp + ROUND_CURSOR) (← B.shifted cur_ptr.base cur_ptr.exp)
      B.store rdNext.base (rdNext.exp + ROUND_CLAIM) claim
    else
      pure ()
    return [.c 0]

set_option linter.unusedVariables false in
/-- `gkr_rounds`, a `Const` family (`guests/lean_ethereum.py`, line 1107):

```
def gkr_rounds(rd, pt, tabs, n: Const):
    # n GKR rounds, from the round record at `rd` (ROUND_SLOTS consecutive fields) to the
    # one n further. The prover sends every coefficient but c0, which the round's
    # pulled-out eq factor leaves fixed: c0 + r (c1 + ... + c4) == claim, r being the
    # previous point's coordinate pt[q], then the round's grind; the challenge goes to
    # pt[MU_CAP + 2 + q].
    if const(n != 0):
        sp = fs_load(rd, ROUND_FS, 1)
        cur = rd[GEN ** ROUND_CURSOR]
        claim = rd[GEN ** ROUND_CLAIM]
        for q in unroll(0, n):
            rate = StackBuf(8)
            c1, cur = fs_next(rate, 0, cur)
            c2, cur = fs_next(rate, 1, cur)
            c3, cur = fs_next(rate, 2, cur)
            c4, cur = fs_next(rate, 3, cur)
            sp, rk, cur = fs_grind_squeeze(sp, rate, 4, cur, tabs, ROUND5_GRIND_BITS)
            c0 = claim + pt[GEN ** q] * (c1 + c2 + c3 + c4)
            pt[GEN ** (MU_CAP + 2 + q)] = rk
            claim = c0 + rk * (c1 + rk * (c2 + rk * (c3 + rk * c4)))
        rd_next = rd * GEN ** (ROUND_SLOTS * n)
        fs_store(rd_next, ROUND_FS, 1, sp)
        rd_next[GEN ** ROUND_CURSOR] = cur
        rd_next[GEN ** ROUND_CLAIM] = claim
    return 0
```
-/
def gkrRounds_2 (n : Nat) : GFn where
  name := instName "gkr_rounds" [.L n]
  arity := 3
  rets := 1
  body ps := do
    let rd := cellOf ps 0
    let pt := cellOf ps 1
    let tabs := cellOf ps 2
    if n ≠ 0 then
      let mut sp ← fsLoad rd ROUND_FS 1
      let cur ← B.load rd ROUND_CURSOR
      let mut claim ← B.load rd ROUND_CLAIM
      let mut cur_ptr : Shifted := default
      let q_k := 0
      let rate ← B.stackBuf 8
      let (t0, t1) ← fsNext rate 0 cur
      let c1 := t0
      cur_ptr := t1
      let (t2, t3) ← fsNext_2 rate 1 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c2 := t2
      cur_ptr := t3
      let (t4, t5) ← fsNext_2 rate 2 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c3 := t4
      cur_ptr := t5
      let (t6, t7) ← fsNext_2 rate 3 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c4 := t6
      cur_ptr := t7
      let (t8, t9, t10) ← fsGrindSqueeze sp rate 4 (⟨cur_ptr.base, cur_ptr.exp⟩) tabs ROUND5_GRIND_BITS
      sp := t8
      let rk := t9
      cur_ptr := t10
      let c0 ← B.add claim (← B.mul (← B.load pt q_k) (← B.add (← B.add (← B.add c1 c2) c3) c4))
      B.store pt ((MU_CAP + 2) + q_k) rk
      claim ← B.add c0 (← B.mul rk (← B.add c1 (← B.mul rk (← B.add c2 (← B.mul rk (← B.add c3 (← B.mul rk c4)))))))
      for q_k in [1:n] do
        let rate ← B.stackBuf 8
        let (t0, t1) ← fsNext_2 rate 0 (⟨cur_ptr.base, cur_ptr.exp⟩)
        let c1 := t0
        cur_ptr := t1
        let (t2, t3) ← fsNext_2 rate 1 (⟨cur_ptr.base, cur_ptr.exp⟩)
        let c2 := t2
        cur_ptr := t3
        let (t4, t5) ← fsNext_2 rate 2 (⟨cur_ptr.base, cur_ptr.exp⟩)
        let c3 := t4
        cur_ptr := t5
        let (t6, t7) ← fsNext_2 rate 3 (⟨cur_ptr.base, cur_ptr.exp⟩)
        let c4 := t6
        cur_ptr := t7
        let (t8, t9, t10) ← fsGrindSqueeze sp rate 4 (⟨cur_ptr.base, cur_ptr.exp⟩) tabs ROUND5_GRIND_BITS
        sp := t8
        let rk := t9
        cur_ptr := t10
        let c0 ← B.add claim (← B.mul (← B.load pt q_k) (← B.add (← B.add (← B.add c1 c2) c3) c4))
        B.store pt ((MU_CAP + 2) + q_k) rk
        claim ← B.add c0 (← B.mul rk (← B.add c1 (← B.mul rk (← B.add c2 (← B.mul rk (← B.add c3 (← B.mul rk c4)))))))
      let rdNext : Shifted := ⟨rd, ROUND_SLOTS * n⟩
      fsStore (⟨rdNext.base, rdNext.exp⟩) ROUND_FS 1 sp
      B.store rdNext.base (rdNext.exp + ROUND_CURSOR) (← B.shifted cur_ptr.base cur_ptr.exp)
      B.store rdNext.base (rdNext.exp + ROUND_CLAIM) claim
    else
      pure () -- no use of this definition takes this branch
    return [.c 0]

set_option linter.unusedVariables false in
/-- `gkr_rounds`, a `Const` family (`guests/lean_ethereum.py`, line 1107):

```
def gkr_rounds(rd, pt, tabs, n: Const):
    # n GKR rounds, from the round record at `rd` (ROUND_SLOTS consecutive fields) to the
    # one n further. The prover sends every coefficient but c0, which the round's
    # pulled-out eq factor leaves fixed: c0 + r (c1 + ... + c4) == claim, r being the
    # previous point's coordinate pt[q], then the round's grind; the challenge goes to
    # pt[MU_CAP + 2 + q].
    if const(n != 0):
        sp = fs_load(rd, ROUND_FS, 1)
        cur = rd[GEN ** ROUND_CURSOR]
        claim = rd[GEN ** ROUND_CLAIM]
        for q in unroll(0, n):
            rate = StackBuf(8)
            c1, cur = fs_next(rate, 0, cur)
            c2, cur = fs_next(rate, 1, cur)
            c3, cur = fs_next(rate, 2, cur)
            c4, cur = fs_next(rate, 3, cur)
            sp, rk, cur = fs_grind_squeeze(sp, rate, 4, cur, tabs, ROUND5_GRIND_BITS)
            c0 = claim + pt[GEN ** q] * (c1 + c2 + c3 + c4)
            pt[GEN ** (MU_CAP + 2 + q)] = rk
            claim = c0 + rk * (c1 + rk * (c2 + rk * (c3 + rk * c4)))
        rd_next = rd * GEN ** (ROUND_SLOTS * n)
        fs_store(rd_next, ROUND_FS, 1, sp)
        rd_next[GEN ** ROUND_CURSOR] = cur
        rd_next[GEN ** ROUND_CLAIM] = claim
    return 0
```
-/
def gkrRounds_3 (n : Nat) : GFn where
  name := instName "gkr_rounds" [.L n]
  arity := 3
  rets := 1
  body ps := do
    let rd := cellOf ps 0
    let pt := cellOf ps 1
    let tabs := cellOf ps 2
    if n ≠ 0 then
      let mut sp ← fsLoad rd ROUND_FS 1
      let cur ← B.load rd ROUND_CURSOR
      let mut claim ← B.load rd ROUND_CLAIM
      let mut cur_ptr : Shifted := default
      let q_k := 0
      let rate ← B.stackBuf 8
      let (t0, t1) ← fsNext rate 0 cur
      let c1 := t0
      cur_ptr := t1
      let (t2, t3) ← fsNext_2 rate 1 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c2 := t2
      cur_ptr := t3
      let (t4, t5) ← fsNext_2 rate 2 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c3 := t4
      cur_ptr := t5
      let (t6, t7) ← fsNext_2 rate 3 (⟨cur_ptr.base, cur_ptr.exp⟩)
      let c4 := t6
      cur_ptr := t7
      let (t8, t9, t10) ← fsGrindSqueeze sp rate 4 (⟨cur_ptr.base, cur_ptr.exp⟩) tabs ROUND5_GRIND_BITS
      sp := t8
      let rk := t9
      cur_ptr := t10
      let c0 ← B.add claim (← B.mul (← B.load pt q_k) (← B.add (← B.add (← B.add c1 c2) c3) c4))
      B.store pt ((MU_CAP + 2) + q_k) rk
      claim ← B.add c0 (← B.mul rk (← B.add c1 (← B.mul rk (← B.add c2 (← B.mul rk (← B.add c3 (← B.mul rk c4)))))))
      let rdNext : Shifted := ⟨rd, ROUND_SLOTS * n⟩
      fsStore (⟨rdNext.base, rdNext.exp⟩) ROUND_FS 1 sp
      B.store rdNext.base (rdNext.exp + ROUND_CURSOR) (← B.shifted cur_ptr.base cur_ptr.exp)
      B.store rdNext.base (rdNext.exp + ROUND_CLAIM) claim
    else
      pure () -- no use of this definition takes this branch
    return [.c 0]

set_option linter.unusedVariables false in
/-- `plus_one_run`, a `Const` family (`guests/lean_ethereum.py`, line 1006):

```
def plus_one_run(out, src, n: Const):
    for k in unroll(0, n):
        out[GEN ** k] = 1 + src[GEN ** k]
    return 0
```
-/
def plusOneRun (n : Nat) : GFn where
  name := instName "plus_one_run" [.L n]
  arity := 2
  rets := 1
  body ps := do
    let out := cellOf ps 0
    let src := cellOf ps 1
    return [.c 0]

set_option linter.unusedVariables false in
/-- `plus_one_run`, a `Const` family (`guests/lean_ethereum.py`, line 1006):

```
def plus_one_run(out, src, n: Const):
    for k in unroll(0, n):
        out[GEN ** k] = 1 + src[GEN ** k]
    return 0
```
-/
def plusOneRun_2 (n : Nat) : GFn where
  name := instName "plus_one_run" [.L n]
  arity := 2
  rets := 1
  body ps := do
    let out := cellOf ps 0
    let src := cellOf ps 1
    let k_k := 0
    B.store out k_k (← B.add (← B.const 1) (← B.load src k_k))
    return [.c 0]

set_option linter.unusedVariables false in
/-- `plus_one_run`, a `Const` family (`guests/lean_ethereum.py`, line 1006):

```
def plus_one_run(out, src, n: Const):
    for k in unroll(0, n):
        out[GEN ** k] = 1 + src[GEN ** k]
    return 0
```
-/
def plusOneRun_3 (n : Nat) : GFn where
  name := instName "plus_one_run" [.L n]
  arity := 2
  rets := 1
  body ps := do
    let out := cellOf ps 0
    let src := cellOf ps 1
    for k_k in [0:n] do
      B.store out k_k (← B.add (← B.const 1) (← B.load src k_k))
    return [.c 0]

set_option linter.unusedVariables false in
/-- `batch_sumcheck`, a `Const` family (`guests/lean_ethereum.py`, line 1134):

```
def batch_sumcheck(fs0, fs1, fs2, fs3, fs4, msgs, running, point, tabs, n_rounds: Const):
    # The rounds of a claim-batching sumcheck: two hinted values per round
    # (g(1) and g(inf)) and the degree-two round's nonce, if any, the split fixing the
    # third against the running claim, and the challenges collected into `point`.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    for rd in unroll(0, n_rounds):
        rate = StackBuf(8)
        msg_g1, c = fs_next(rate, 0, msgs * GEN ** (BC_ROUND_WORDS * rd))
        msg_ginf, c = fs_next(rate, 1, c)
        sp, rv, c = fs_grind_squeeze(sp, rate, 2, c, tabs, ROUND2_GRIND_BITS)
        point[GEN ** rd] = rv
        g_zero = running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        running = (msg_ginf * rv + c_one) * rv + g_zero  # fold the degree-2 round at rv
    return sp[8], sp[9], sp[10], sp[11], sp[12], running
```
-/
def batchSumcheck (nRounds : Nat) : GFn where
  name := instName "batch_sumcheck" [.L nRounds]
  arity := 9
  rets := 6
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let msgs := cellOf ps 5
    let mut running := cellOf ps 6
    let point := cellOf ps 7
    let tabs := cellOf ps 8
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let rd_k := 0
    let rate ← B.stackBuf 8
    let (t0, t1) ← fsNext rate 0 msgs
    let msgG1 := t0
    let c : Shifted := t1
    let (t2, t3) ← fsNext_2 rate 1 (⟨c.base, c.exp⟩)
    let msgGinf := t2
    let c : Shifted := t3
    let (t4, t5, t6) ← fsGrindSqueeze sp rate 2 (⟨c.base, c.exp⟩) tabs ROUND2_GRIND_BITS
    sp := t4
    let rv := t5
    let c : Shifted := t6
    B.store point rd_k rv
    let gZero ← B.add running msgG1
    let cOne ← B.add (← B.add gZero msgG1) msgGinf
    running ← B.add (← B.mul (← B.add (← B.mul msgGinf rv) cOne) rv) gZero
    for rd_k in [1:nRounds] do
      let rate ← B.stackBuf 8
      let (t0, t1) ← fsNext_2 rate 0 (⟨msgs, BC_ROUND_WORDS * rd_k⟩)
      let msgG1 := t0
      let c : Shifted := t1
      let (t2, t3) ← fsNext_2 rate 1 (⟨c.base, c.exp⟩)
      let msgGinf := t2
      let c : Shifted := t3
      let (t4, t5, t6) ← fsGrindSqueeze sp rate 2 (⟨c.base, c.exp⟩) tabs ROUND2_GRIND_BITS
      sp := t4
      let rv := t5
      let c : Shifted := t6
      B.store point rd_k rv
      let gZero ← B.add running msgG1
      let cOne ← B.add (← B.add gZero msgG1) msgGinf
      running ← B.add (← B.mul (← B.add (← B.mul msgGinf rv) cOne) rv) gZero
    return [.v (cellOf sp 8).v] ++ [.v (cellOf sp 9).v] ++ [.v (cellOf sp 10).v] ++ [.v (cellOf sp 11).v] ++ [.v (cellOf sp 12).v] ++ [.v running.v]

set_option linter.unusedVariables false in
/-- `fold_final_msg`, a `Const` family (`guests/lean_ethereum.py`, line 1067):

```
def fold_final_msg(msg, point, log_len: Const):
    weights = StackBuf(2 * YR_LOG_CAP)
    for j in unroll(0, log_len):
        weights[2 * j] = 1 + point[GEN ** j]
        weights[2 * j + 1] = point[GEN ** j]
    # Weighted fold of the final_msg multilinear over 2^log_len values (log_len is
    # the candidate's yr_log_n; the frame buffers use the global max size).
    l0 = StackBuf(2 ** YR_LOG_CAP)
    for t in unroll(0, 2 ** log_len // 2):
        l0[t] = weights[0] * msg[GEN ** (2 * t)] + weights[1] * msg[GEN ** (2 * t + 1)]
    cursor = l0
    n = 2 ** log_len // 2
    for j in unroll(1, log_len):
        nxt = StackBuf(2 ** YR_LOG_CAP)
        for t in unroll(0, n // 2):
            nxt[t] = weights[2 * j] * cursor[2 * t] + weights[2 * j + 1] * cursor[2 * t + 1]
        cursor = nxt
        n = n // 2
    return cursor[0]
```
-/
def foldFinalMsg (logLen : Nat) : GFn where
  name := instName "fold_final_msg" [.L logLen]
  arity := 2
  rets := 1
  body ps := do
    let msg := cellOf ps 0
    let point := cellOf ps 1
    let weights ← B.stackBuf 10
    for j_k in [0:logLen] do
      B.addInto (cellOf weights (2 * j_k)) (← B.const 1) (← B.load point j_k)
      B.loadInto (cellOf weights ((2 * j_k) + 1)) point j_k
    let l0 ← B.stackBuf 32
    for t_k in [0:(2 ^ logLen) / 2] do
      B.addInto (cellOf l0 t_k) (← B.mul (cellOf weights 0) (← B.load msg (2 * t_k))) (← B.mul (cellOf weights 1) (← B.load msg ((2 * t_k) + 1)))
    let mut cursor := l0
    let mut n := (2 ^ logLen) / 2
    let j_k := 1
    let nxt ← B.stackBuf 32
    let t_k := 0
    B.addInto (cellOf nxt t_k) (← B.mul (cellOf weights (2 * j_k)) (cellOf cursor (2 * t_k))) (← B.mul (cellOf weights ((2 * j_k) + 1)) (cellOf cursor ((2 * t_k) + 1)))
    cursor := nxt
    n := n / 2
    return [.v (cellOf cursor 0).v]

set_option linter.unusedVariables false in
/-- `fold_final_msg`, a `Const` family (`guests/lean_ethereum.py`, line 1067):

```
def fold_final_msg(msg, point, log_len: Const):
    weights = StackBuf(2 * YR_LOG_CAP)
    for j in unroll(0, log_len):
        weights[2 * j] = 1 + point[GEN ** j]
        weights[2 * j + 1] = point[GEN ** j]
    # Weighted fold of the final_msg multilinear over 2^log_len values (log_len is
    # the candidate's yr_log_n; the frame buffers use the global max size).
    l0 = StackBuf(2 ** YR_LOG_CAP)
    for t in unroll(0, 2 ** log_len // 2):
        l0[t] = weights[0] * msg[GEN ** (2 * t)] + weights[1] * msg[GEN ** (2 * t + 1)]
    cursor = l0
    n = 2 ** log_len // 2
    for j in unroll(1, log_len):
        nxt = StackBuf(2 ** YR_LOG_CAP)
        for t in unroll(0, n // 2):
            nxt[t] = weights[2 * j] * cursor[2 * t] + weights[2 * j + 1] * cursor[2 * t + 1]
        cursor = nxt
        n = n // 2
    return cursor[0]
```
-/
def foldFinalMsg_2 (logLen : Nat) : GFn where
  name := instName "fold_final_msg" [.L logLen]
  arity := 2
  rets := 1
  body ps := do
    let msg := cellOf ps 0
    let point := cellOf ps 1
    let weights ← B.stackBuf 10
    for j_k in [0:logLen] do
      B.addInto (cellOf weights (2 * j_k)) (← B.const 1) (← B.load point j_k)
      B.loadInto (cellOf weights ((2 * j_k) + 1)) point j_k
    let l0 ← B.stackBuf 32
    for t_k in [0:(2 ^ logLen) / 2] do
      B.addInto (cellOf l0 t_k) (← B.mul (cellOf weights 0) (← B.load msg (2 * t_k))) (← B.mul (cellOf weights 1) (← B.load msg ((2 * t_k) + 1)))
    let mut cursor := l0
    let mut n := (2 ^ logLen) / 2
    let j_k := 1
    let nxt ← B.stackBuf 32
    for t_k in [0:n / 2] do
      B.addInto (cellOf nxt t_k) (← B.mul (cellOf weights (2 * j_k)) (cellOf cursor (2 * t_k))) (← B.mul (cellOf weights ((2 * j_k) + 1)) (cellOf cursor ((2 * t_k) + 1)))
    cursor := nxt
    n := n / 2
    let j_k := 2
    let nxt ← B.stackBuf 32
    let t_k := 0
    B.addInto (cellOf nxt t_k) (← B.mul (cellOf weights (2 * j_k)) (cellOf cursor (2 * t_k))) (← B.mul (cellOf weights ((2 * j_k) + 1)) (cellOf cursor ((2 * t_k) + 1)))
    cursor := nxt
    n := n / 2
    return [.v (cellOf cursor 0).v]

set_option linter.unusedVariables false in
/-- `fold_final_msg`, a `Const` family (`guests/lean_ethereum.py`, line 1067):

```
def fold_final_msg(msg, point, log_len: Const):
    weights = StackBuf(2 * YR_LOG_CAP)
    for j in unroll(0, log_len):
        weights[2 * j] = 1 + point[GEN ** j]
        weights[2 * j + 1] = point[GEN ** j]
    # Weighted fold of the final_msg multilinear over 2^log_len values (log_len is
    # the candidate's yr_log_n; the frame buffers use the global max size).
    l0 = StackBuf(2 ** YR_LOG_CAP)
    for t in unroll(0, 2 ** log_len // 2):
        l0[t] = weights[0] * msg[GEN ** (2 * t)] + weights[1] * msg[GEN ** (2 * t + 1)]
    cursor = l0
    n = 2 ** log_len // 2
    for j in unroll(1, log_len):
        nxt = StackBuf(2 ** YR_LOG_CAP)
        for t in unroll(0, n // 2):
            nxt[t] = weights[2 * j] * cursor[2 * t] + weights[2 * j + 1] * cursor[2 * t + 1]
        cursor = nxt
        n = n // 2
    return cursor[0]
```
-/
def foldFinalMsg_3 (logLen : Nat) : GFn where
  name := instName "fold_final_msg" [.L logLen]
  arity := 2
  rets := 1
  body ps := do
    let msg := cellOf ps 0
    let point := cellOf ps 1
    let weights ← B.stackBuf 10
    for j_k in [0:logLen] do
      B.addInto (cellOf weights (2 * j_k)) (← B.const 1) (← B.load point j_k)
      B.loadInto (cellOf weights ((2 * j_k) + 1)) point j_k
    let l0 ← B.stackBuf 32
    for t_k in [0:(2 ^ logLen) / 2] do
      B.addInto (cellOf l0 t_k) (← B.mul (cellOf weights 0) (← B.load msg (2 * t_k))) (← B.mul (cellOf weights 1) (← B.load msg ((2 * t_k) + 1)))
    let mut cursor := l0
    let mut n := (2 ^ logLen) / 2
    for j_k in [1:3] do
      let nxt ← B.stackBuf 32
      for t_k in [0:n / 2] do
        B.addInto (cellOf nxt t_k) (← B.mul (cellOf weights (2 * j_k)) (cellOf cursor (2 * t_k))) (← B.mul (cellOf weights ((2 * j_k) + 1)) (cellOf cursor ((2 * t_k) + 1)))
      cursor := nxt
      n := n / 2
    let j_k := 3
    let nxt ← B.stackBuf 32
    let t_k := 0
    B.addInto (cellOf nxt t_k) (← B.mul (cellOf weights (2 * j_k)) (cellOf cursor (2 * t_k))) (← B.mul (cellOf weights ((2 * j_k) + 1)) (cellOf cursor ((2 * t_k) + 1)))
    cursor := nxt
    n := n / 2
    return [.v (cellOf cursor 0).v]

set_option linter.unusedVariables false in
/-- `fold_final_msg`, a `Const` family (`guests/lean_ethereum.py`, line 1067):

```
def fold_final_msg(msg, point, log_len: Const):
    weights = StackBuf(2 * YR_LOG_CAP)
    for j in unroll(0, log_len):
        weights[2 * j] = 1 + point[GEN ** j]
        weights[2 * j + 1] = point[GEN ** j]
    # Weighted fold of the final_msg multilinear over 2^log_len values (log_len is
    # the candidate's yr_log_n; the frame buffers use the global max size).
    l0 = StackBuf(2 ** YR_LOG_CAP)
    for t in unroll(0, 2 ** log_len // 2):
        l0[t] = weights[0] * msg[GEN ** (2 * t)] + weights[1] * msg[GEN ** (2 * t + 1)]
    cursor = l0
    n = 2 ** log_len // 2
    for j in unroll(1, log_len):
        nxt = StackBuf(2 ** YR_LOG_CAP)
        for t in unroll(0, n // 2):
            nxt[t] = weights[2 * j] * cursor[2 * t] + weights[2 * j + 1] * cursor[2 * t + 1]
        cursor = nxt
        n = n // 2
    return cursor[0]
```
-/
def foldFinalMsg_4 (logLen : Nat) : GFn where
  name := instName "fold_final_msg" [.L logLen]
  arity := 2
  rets := 1
  body ps := do
    let msg := cellOf ps 0
    let point := cellOf ps 1
    let weights ← B.stackBuf 10
    for j_k in [0:logLen] do
      B.addInto (cellOf weights (2 * j_k)) (← B.const 1) (← B.load point j_k)
      B.loadInto (cellOf weights ((2 * j_k) + 1)) point j_k
    let l0 ← B.stackBuf 32
    for t_k in [0:(2 ^ logLen) / 2] do
      B.addInto (cellOf l0 t_k) (← B.mul (cellOf weights 0) (← B.load msg (2 * t_k))) (← B.mul (cellOf weights 1) (← B.load msg ((2 * t_k) + 1)))
    let mut cursor := l0
    let mut n := (2 ^ logLen) / 2
    for j_k in [1:4] do
      let nxt ← B.stackBuf 32
      for t_k in [0:n / 2] do
        B.addInto (cellOf nxt t_k) (← B.mul (cellOf weights (2 * j_k)) (cellOf cursor (2 * t_k))) (← B.mul (cellOf weights ((2 * j_k) + 1)) (cellOf cursor ((2 * t_k) + 1)))
      cursor := nxt
      n := n / 2
    let j_k := 4
    let nxt ← B.stackBuf 32
    let t_k := 0
    B.addInto (cellOf nxt t_k) (← B.mul (cellOf weights (2 * j_k)) (cellOf cursor (2 * t_k))) (← B.mul (cellOf weights ((2 * j_k) + 1)) (cellOf cursor ((2 * t_k) + 1)))
    cursor := nxt
    n := n / 2
    return [.v (cellOf cursor 0).v]

end
end LeanVM.Dsl.Gen
