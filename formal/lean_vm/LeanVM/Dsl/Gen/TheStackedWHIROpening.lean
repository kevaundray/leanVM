/-
  LeanVM.Dsl.Gen.TheStackedWHIROpening

  The guest's section `TheStackedWHIROpening`, translated.
-/

module

public import LeanVM.Dsl.Gen.Inline

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

set_option linter.unusedVariables false in
/-- `opening_round` (`guests/lean_ethereum.py`, line 1210):

```
def opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, alphas, coefs):
    # One fold round: the four scalars [u0, w, c0, c1], grind, then alpha, beta. The
    # row folds read alpha, beta at coefs[0..2]; alpha is also the point's coordinate.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    msg = StackBuf(8)
    u0, cursor = fs_next(msg, 0, cursor)
    w, cursor = fs_next(msg, 1, cursor)
    c0, cursor = fs_next(msg, 2, cursor)
    c1, cursor = fs_next(msg, 3, cursor)
    sp, alpha, cursor = fs_grind_squeeze(sp, msg, 4, cursor, tabs, FOLD_GRIND_BITS)
    rate = StackBuf(8)
    sp, beta = squeeze(sp, rate, 0)
    alphas[GEN ** 0] = alpha
    coefs[GEN ** 0] = alpha
    coefs[GEN ** 1] = beta
    # u0 + alpha (u0 + claim) + alpha^2 w + beta c0 + alpha beta (c0 + c1)
    out = u0 + beta * c0 + alpha * (u0 + claim + alpha * w + beta * (c0 + c1))
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, out
```
-/
def openingRound : GFn where
  name := "opening_round"
  arity := 10
  rets := 7
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let cursor := cellOf ps 5
    let claim := cellOf ps 6
    let tabs := cellOf ps 7
    let alphas := cellOf ps 8
    let coefs := cellOf ps 9
    let sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let msg ← B.stackBuf 8
    let (t0, t1) ← fsNext msg 0 cursor
    let u0 := t0
    let cursor_ptr : Shifted := t1
    let (t2, t3) ← fsNext_2 msg 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let w := t2
    let cursor_ptr : Shifted := t3
    let (t4, t5) ← fsNext_2 msg 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let c0 := t4
    let cursor_ptr : Shifted := t5
    let (t6, t7) ← fsNext_2 msg 3 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let c1 := t6
    let cursor_ptr : Shifted := t7
    let (t8, t9, t10) ← fsGrindSqueeze sp msg 4 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs FOLD_GRIND_BITS
    let sp := t8
    let alpha := t9
    let cursor_ptr : Shifted := t10
    let rate ← B.stackBuf 8
    let (t11, t12) ← squeeze sp rate 0
    let sp := t11
    let beta := t12
    B.store alphas 0 alpha
    B.store coefs 0 alpha
    B.store coefs 1 beta
    let out ← B.add (← B.add u0 (← B.mul beta c0)) (← B.mul alpha (← B.add (← B.add (← B.add u0 claim) (← B.mul alpha w)) (← B.mul beta (← B.add c0 c1))))
    let t13 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted cursor_ptr.base cursor_ptr.exp)
    return [.v (cellOf sp 8).v] ++ [.v (cellOf sp 9).v] ++ [.v (cellOf sp 10).v] ++ [.v (cellOf sp 11).v] ++ [.v (cellOf sp 12).v] ++ [.into t13] ++ [.v out.v]

set_option linter.unusedVariables false in
/-- `opening_tail_round` (`guests/lean_ethereum.py`, line 1273):

```
def opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs):
    # One round of the closing sumcheck: h(0) + h(1) == claim fixes h's linear
    # coefficient, so c0 and c2 are sent and h(r) = c0 + r (claim + (1 + r) c2). Then
    # the round's grind.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    c0, cursor = fs_next(rate, 0, cursor)
    c2, cursor = fs_next(rate, 1, cursor)
    sp, r, cursor = fs_grind_squeeze(sp, rate, 2, cursor, tabs, ROUND2_GRIND_BITS)
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, c0 + r * (claim + (1 + r) * c2), r
```
-/
def openingTailRound : GFn where
  name := "opening_tail_round"
  arity := 8
  rets := 8
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let cursor := cellOf ps 5
    let claim := cellOf ps 6
    let tabs := cellOf ps 7
    let sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let rate ← B.stackBuf 8
    let (t0, t1) ← fsNext rate 0 cursor
    let c0 := t0
    let cursor_ptr : Shifted := t1
    let (t2, t3) ← fsNext_2 rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let c2 := t2
    let cursor_ptr : Shifted := t3
    let (t4, t5, t6) ← fsGrindSqueeze sp rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs ROUND2_GRIND_BITS
    let sp := t4
    let r := t5
    let cursor_ptr : Shifted := t6
    let t7 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted cursor_ptr.base cursor_ptr.exp)
    let t8 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) c0 (← B.mul r (← B.add claim (← B.mul (← B.add (← B.const 1) r) c2)))
    return [.v (cellOf sp 8).v] ++ [.v (cellOf sp 9).v] ++ [.v (cellOf sp 10).v] ++ [.v (cellOf sp 11).v] ++ [.v (cellOf sp 12).v] ++ [.into t7] ++ [.into t8] ++ [.v r.v]

set_option linter.unusedVariables false in
/-- `squeeze_point_from`, a `Const` family (`guests/lean_ethereum.py`, line 1257):

```
def squeeze_point_from(fs0, fs1, fs2, fs3, fs4, first, point, n: Const):
    # n challenges whose first, `first`, a permutation already drew, the sponge its
    # capacity: the other n - 1 are fresh squeezes.
    point[GEN ** 0] = first
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    if const(n // 2 == 0):
        out = sp
    else:
        no_rate = StackBuf(8)
        for x in unroll(1, n):
            sp, r = squeeze(sp, no_rate, 0)
            point[GEN ** x] = r
        out = [sp[8], sp[9], sp[10], sp[11], sp[12]]
    return out[0], out[1], out[2], out[3], out[4]
```
-/
def squeezePointFrom (n : Nat) : GFn where
  name := instName "squeeze_point_from" [.L n]
  arity := 7
  rets := 5
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let first := cellOf ps 5
    let point := cellOf ps 6
    B.store point 0 first
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut out : List V := default
    if (n / 2) = 0 then
      pure () -- no use of this definition takes this branch
    else
      let noRate ← B.stackBuf 8
      for x_k in [1:n] do
        let (t0, t1) ← squeeze sp noRate 0
        sp := t0
        let r := t1
        B.store point x_k r
      let t2 ← B.stackBuf 5
      B.copy (cellOf t2 0) (cellOf sp 8)
      B.copy (cellOf t2 1) (cellOf sp 9)
      B.copy (cellOf t2 2) (cellOf sp 10)
      B.copy (cellOf t2 3) (cellOf sp 11)
      B.copy (cellOf t2 4) (cellOf sp 12)
      out := t2
    return [.v (cellOf out 0).v] ++ [.v (cellOf out 1).v] ++ [.v (cellOf out 2).v] ++ [.v (cellOf out 3).v] ++ [.v (cellOf out 4).v]

set_option linter.unusedVariables false in
/-- `opening_message`, a `Const` family (`guests/lean_ethereum.py`, line 1230):

```
def opening_message(fs0, fs1, fs2, fs3, fs4, cursor, out, n: Const, nonce: Const):
    # n stream words into out, then, with `nonce`, a grinding nonce, then the
    # permutation the next challenge comes from. Returns that output's first cell (the
    # challenge), its second (where the proof of work is), its capacity and the cursor.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    for pos in unroll(0, n):
        if pos % 4 == 0:
            if pos != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        value, cursor = fs_next(rate, pos % 4, cursor)
        out[GEN ** pos] = value
    if const(nonce == 1):
        if const(n % 4 == 0):
            if const(n != 0):
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        sp = fs_absorb_nonce(sp, rate, n % 4, cursor[GEN ** 0])
        cursor = cursor * GEN
    elif const(n == 0):
        sp = fs_perm(sp, rate, 0)
    else:
        sp = fs_perm(sp, rate, (n + 3) % 4 + 1)
    return sp[0], sp[1], sp[8], sp[9], sp[10], sp[11], sp[12], cursor
```
-/
def openingMessage (n : Nat) (nonce : Nat) : GFn where
  name := instName "opening_message" [.L n, .L nonce]
  arity := 7
  rets := 8
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let cursor := cellOf ps 5
    let out := cellOf ps 6
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let rate ← B.stackBuf 8
    let mut cursor_ptr : Shifted := default
    let pos_k := 0
    if (pos_k % 4) = 0 then
      if pos_k ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    let (t0, t1) ← fsNext rate (pos_k % 4) cursor
    let value := t0
    cursor_ptr := t1
    B.store out pos_k value
    if nonce = 1 then
      if (n % 4) = 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      sp ← fsAbsorbNonce sp rate (n % 4) (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
    else
      pure () -- no use of this definition takes this branch
    let t2 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted cursor_ptr.base cursor_ptr.exp)
    return [.v (cellOf sp 0).v] ++ [.v (cellOf sp 1).v] ++ [.v (cellOf sp 8).v] ++ [.v (cellOf sp 9).v] ++ [.v (cellOf sp 10).v] ++ [.v (cellOf sp 11).v] ++ [.v (cellOf sp 12).v] ++ [.into t2]

set_option linter.unusedVariables false in
/-- `opening_message`, a `Const` family (`guests/lean_ethereum.py`, line 1230):

```
def opening_message(fs0, fs1, fs2, fs3, fs4, cursor, out, n: Const, nonce: Const):
    # n stream words into out, then, with `nonce`, a grinding nonce, then the
    # permutation the next challenge comes from. Returns that output's first cell (the
    # challenge), its second (where the proof of work is), its capacity and the cursor.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    for pos in unroll(0, n):
        if pos % 4 == 0:
            if pos != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        value, cursor = fs_next(rate, pos % 4, cursor)
        out[GEN ** pos] = value
    if const(nonce == 1):
        if const(n % 4 == 0):
            if const(n != 0):
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        sp = fs_absorb_nonce(sp, rate, n % 4, cursor[GEN ** 0])
        cursor = cursor * GEN
    elif const(n == 0):
        sp = fs_perm(sp, rate, 0)
    else:
        sp = fs_perm(sp, rate, (n + 3) % 4 + 1)
    return sp[0], sp[1], sp[8], sp[9], sp[10], sp[11], sp[12], cursor
```
-/
def openingMessage_2 (n : Nat) (nonce : Nat) : GFn where
  name := instName "opening_message" [.L n, .L nonce]
  arity := 7
  rets := 8
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let cursor := cellOf ps 5
    let out := cellOf ps 6
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut rate ← B.stackBuf 8
    let mut cursor_ptr : Shifted := default
    let pos_k := 0
    if (pos_k % 4) = 0 then
      if pos_k ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    let (t0, t1) ← fsNext rate (pos_k % 4) cursor
    let value := t0
    cursor_ptr := t1
    B.store out pos_k value
    for pos_k in [1:n] do
      if (pos_k % 4) = 0 then
        if pos_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      let (t0, t1) ← fsNext_2 rate (pos_k % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      let value := t0
      cursor_ptr := t1
      B.store out pos_k value
    if nonce = 1 then
      if (n % 4) = 0 then
        if n ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      sp ← fsAbsorbNonce sp rate (n % 4) (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
    else
      pure () -- no use of this definition takes this branch
    let t2 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted cursor_ptr.base cursor_ptr.exp)
    return [.v (cellOf sp 0).v] ++ [.v (cellOf sp 1).v] ++ [.v (cellOf sp 8).v] ++ [.v (cellOf sp 9).v] ++ [.v (cellOf sp 10).v] ++ [.v (cellOf sp 11).v] ++ [.v (cellOf sp 12).v] ++ [.into t2]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:3] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 3
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:nHs] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 2
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    for j_k in [yrLog:YR_LOG_CAP] do
      B.store tailChallenges j_k (← B.const 0)
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked_2 (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:3] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 3
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:8] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [2:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [8:10] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [10:nHs] do
        sc := 1
        for i_k in [0:3] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 3
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    for j_k in [yrLog:YR_LOG_CAP] do
      B.store tailChallenges j_k (← B.const 0)
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked_3 (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let mut sc_fe : E := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:3] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 3
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:8] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [2:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [8:10] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [10:14] do
        sc := 1
        for i_k in [0:3] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [3:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [14:16] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 2
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        for i_k in [3:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [16:18] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [18:nHs] do
        sc := 1
        for i_k in [0:4] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 4
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    let j_k := 4
    B.store tailChallenges j_k (← B.const 0)
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked_4 (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let mut sc_fe : E := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:3] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 3
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:8] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [2:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [8:10] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [10:14] do
        sc := 1
        for i_k in [0:3] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [3:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [14:16] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 2
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        for i_k in [3:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [16:18] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [18:22] do
        sc := 1
        for i_k in [0:4] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [4:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [22:24] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [2:4] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [4:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [24:26] do
        sc := 1
        for i_k in [0:4] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [4:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [26:30] do
        sc := 1
        for i_k in [0:3] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 3
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        for i_k in [4:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [30:32] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 2
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 3
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        for i_k in [4:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_fe * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [32:34] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [34:nHs] do
        sc := 1
        for i_k in [0:5] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 5
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked_5 (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:4] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 4
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:nHs] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 2
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    for j_k in [yrLog:YR_LOG_CAP] do
      B.store tailChallenges j_k (← B.const 0)
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked_6 (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:4] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 4
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:8] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [2:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [8:10] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [10:nHs] do
        sc := 1
        for i_k in [0:3] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 3
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    for j_k in [yrLog:YR_LOG_CAP] do
      B.store tailChallenges j_k (← B.const 0)
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked_7 (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let mut sc_fe : E := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:4] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 4
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:8] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [2:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [8:10] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [10:14] do
        sc := 1
        for i_k in [0:3] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [3:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [14:16] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 2
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        for i_k in [3:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [16:18] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [18:nHs] do
        sc := 1
        for i_k in [0:4] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 4
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    let j_k := 4
    B.store tailChallenges j_k (← B.const 0)
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked_8 (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let mut sc_fe : E := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:4] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 4
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:8] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [2:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [8:10] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [10:14] do
        sc := 1
        for i_k in [0:3] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [3:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [14:16] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 2
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        for i_k in [3:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [16:18] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [18:22] do
        sc := 1
        for i_k in [0:4] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [4:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [22:24] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [2:4] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [4:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [24:26] do
        sc := 1
        for i_k in [0:4] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [4:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [26:30] do
        sc := 1
        for i_k in [0:3] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 3
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        for i_k in [4:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [30:32] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 2
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 3
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        for i_k in [4:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_fe * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [32:34] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [34:nHs] do
        sc := 1
        for i_k in [0:5] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 5
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked_9 (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:5] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 5
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:nHs] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 2
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    for j_k in [yrLog:YR_LOG_CAP] do
      B.store tailChallenges j_k (← B.const 0)
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked_10 (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:5] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 5
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:8] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [2:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [8:10] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [10:nHs] do
        sc := 1
        for i_k in [0:3] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 3
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    for j_k in [yrLog:YR_LOG_CAP] do
      B.store tailChallenges j_k (← B.const 0)
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `open_stacked`, a `Const` family (`guests/lean_ethereum.py`, line 1563):

```
def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_positions`,
    # `level_queries` and `level_residual`, which read the tables a rate changes (query
    # counts, tree and cap depths, squeezes) at `ml + r * LIG_RATE_STRIDE`. Every other
    # LIG_* table is read at the size's first-rate row `ml`, which `opening_placeholders`
    # checks does not vary by rate. Only the executed arm pops the opening's hint streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction) and 1/lam at row lvl, its OOD claim's scalar lam at row lvl + 1.
    # A level's high part (its folds' coefficients, normalizers in) sits at its folds'
    # offset, and its OOD point's row, mu coordinates, follows the previous levels'.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** n_folds)
    cols_total = 0
    for cl in unroll(0, last):
        cols_total = cols_total + LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + cl]
    ood_z = HeapBuf(GEN ** cols_total)
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, the most any rate draws there, follow the previous
    # levels' (LIG_POS_OFF).
    query_positions = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])
    query_win_ptrs = HeapBuf(GEN ** LIG_POS_TOTAL[m_idx])

    claim = target
    cols_off = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        pos_off = LIG_POS_OFF[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** cols_off
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** folds_off
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        if const(lvl == last):
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu, n_hs, hs_bits, 1))
        else:
            root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], 0, 0, 0, 0))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv
        cols_off = cols_off + mu

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_total = 0
    for bl in unroll(0, last):
        basis_total = basis_total + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + bl] + yr_log
    basis_d = HeapBuf(GEN ** basis_total)
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    basis_off = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (basis_off + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (basis_off + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
        basis_off = basis_off + prefix_len + yr_log
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    res_basis = 0
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        h, h_high = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual(query_positions * GEN ** LIG_POS_OFF[ml], basis_d * GEN ** res_basis, level_hs * GEN ** LIG_FOLDS_OFF[ml], level_lam_invs[GEN ** lvl], LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml]))
        res_basis = res_basis + LIG_RESIDUAL_PREFIX_LEN[ml] + yr_log
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    ood_off = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** ood_off
        ood_off = ood_off + LIG_LOG_MSG_COLS[ml - 1]
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail
```
-/
def openStacked_11 (mIdx : Nat) : GFn where
  name := instName "open_stacked" [.L mIdx]
  arity := 11
  rets := 5
  body ps := do
    let rateSel := cellOf ps 0
    let mut fs0 := cellOf ps 1
    let mut fs1 := cellOf ps 2
    let mut fs2 := cellOf ps 3
    let mut fs3 := cellOf ps 4
    let mut fs4 := cellOf ps 5
    let target := cellOf ps 6
    let commitRoot0 := cellOf ps 7
    let commitRoot1 := cellOf ps 8
    let mut cursor := cellOf ps 9
    let tabs := cellOf ps 10
    let nLevels := arrInt LIG_N_LEVELS mIdx
    let last := arrInt LIG_YR_LEVEL mIdx
    let yrLog := arrInt LIG_YR_LOG_LEN mIdx
    let yrLen := arrInt LIG_YR_LEN mIdx
    let nFolds := arrInt LIG_TOTAL_FOLDS mIdx
    let finalMsg ← B.heapBufDyn (← B.const (gpowE (yrLen + (arrInt LIG_FOLDS ((mIdx * LIG_MAX_LEVELS) + last)))))
    let levelRoots ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store levelRoots 0 commitRoot0
    B.store levelRoots 1 commitRoot1
    let foldChallenges ← B.heapBufDyn (← B.const (gpowE nFolds))
    let roundCoefs ← B.heapBufDyn (← B.const (gpowE (2 * nFolds)))
    let levelScales ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelLamInvs ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelHs ← B.heapBufDyn (← B.const (gpowE nFolds))
    let mut colsTotal := 0
    for cl_k in [0:last] do
      colsTotal := colsTotal + (arrInt LIG_LOG_MSG_COLS ((mIdx * LIG_MAX_LEVELS) + cl_k))
    let oodZ ← B.heapBufDyn (← B.const (gpowE colsTotal))
    let oodScalars ← B.heapBufDyn (← B.const (gpowE nLevels))
    let queryPositions ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let queryWinPtrs ← B.heapBufDyn (← B.const (gpowE (arrInt LIG_POS_TOTAL mIdx)))
    let mut claim := target
    let mut colsOff := 0
    let mut ml : Nat := default
    let mut vanish : Nat := default
    let mut sent : Word := default
    let mut zFirst : Word := default
    let mut powOod : Word := default
    let mut oodRow : Word := default
    let mut sp : List V := default
    let mut rate : List V := default
    let mut cursor_ptr : Shifted := default
    let mut noRate : List V := default
    let mut lam : Word := default
    let mut nHs : Nat := default
    let mut hsBits : Nat := default
    let mut hs : Word := default
    let mut sc : Nat := default
    let mut sc_field : E := default
    let mut scale : Word := default
    let mut oodRow_ptr : Shifted := default
    let mut hs_ptr : Shifted := default
    let mut lam_nat : Nat := default
    let mut sc_fe : E := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, foldChallenges.v, roundCoefs.v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    let mut oodY : Word := default
    let mut word0 : Word := default
    let mut pow0 : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
      let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
      zFirst := t1[0]!
      powOod := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
      let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
      B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
      B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
      oodRow := oodZ
      let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, oodRow.v] 5
      fs0 := t2[0]!
      fs1 := t2[1]!
      fs2 := t2[2]!
      fs3 := t2[3]!
      fs4 := t2[4]!
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext rate 0 cursor
      oodY := t3
      cursor_ptr := t4
      sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
      cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
      word0 := cellOf sp 0
      pow0 := cellOf sp 1
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t5 ← B.targets [none, none, none, none, none]
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, queryPositions.v, queryWinPtrs.v, tabs.v] t5
    fs0 := cellOf t5 0
    fs1 := cellOf t5 1
    fs2 := cellOf t5 2
    fs3 := cellOf t5 3
    fs4 := cellOf t5 4
    let mut lamInv : Word := default
    if lvl_k ≠ last then
      sp ← fsCap fs0 fs1 fs2 fs3 fs4
      noRate ← B.stackBuf 8
      let (t6, t7) ← squeeze sp noRate 0
      sp := t6
      lam := t7
      lamInv ← B.fdiv (← B.const 1) lam
      fs0 := cellOf sp 8
      fs1 := cellOf sp 9
      fs2 := cellOf sp 10
      fs3 := cellOf sp 11
      fs4 := cellOf sp 12
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      nHs := 0
      hsBits := 0
      hs := levelHs
      for c_k in [0:2] do
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
      let c_k := 2
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 3
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      let i_k := 0
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 4
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:arrInt LIG_HIGH_BITS ml] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      let c_k := 5
      sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
      for i_k in [0:2] do
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure ()
      let i_k := 2
      if ((c_k / (2 ^ i_k)) % 2) = 1 then
        sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
        sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
      else
        pure () -- no use of this definition takes this branch
      B.store hs c_k (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
    let mut root0 : Word := default
    let mut root1 : Word := default
    let mut batched : Word := default
    let mut lamPow : Word := default
    if lvl_k = last then
      pure () -- no use of this definition takes this branch
    else
      let t8 ← B.targets [none, none, none, none]
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, roundCoefs.v, hs.v, queryPositions.v, queryWinPtrs.v] t8
      root0 := cellOf t8 0
      root1 := cellOf t8 1
      batched := cellOf t8 2
      lamPow := cellOf t8 3
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      B.store oodScalars (lvl_k + 1) lam
      claim ← B.add claim (← B.mul lam oodY)
      scale ← B.mul (← B.mul lam lam) lamPow
      claim ← B.add claim (← B.mul scale batched)
      B.store levelScales lvl_k scale
      B.store levelLamInvs lvl_k lamInv
    else
      pure () -- no use of this definition takes this branch
    colsOff := colsOff + mu
    for lvl_k in [1:5] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let posOff := arrInt LIG_POS_OFF ml
      let folds := arrInt LIG_FOLDS ml
      let mu := arrInt LIG_LOG_MSG_COLS ml
      let foldsOff := arrInt LIG_FOLDS_OFF ml
      vanish := (mu * (mu + 1)) / 2
      let j_k := 0
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
      for j_k in [1:folds] do
        let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
        fs0 := t0[0]!
        fs1 := t0[1]!
        fs2 := t0[2]!
        fs3 := t0[3]!
        fs4 := t0[4]!
        cursor := t0[5]!
        claim := t0[6]!
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        sent ← B.heapBufDyn (← B.const (gpowE (2 + folds)))
        let t1 ← B.call (instName "opening_message" [.L (2 + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, sent.v] 8
        zFirst := t1[0]!
        powOod := t1[1]!
        fs0 := t1[2]!
        fs1 := t1[3]!
        fs2 := t1[4]!
        fs3 := t1[5]!
        fs4 := t1[6]!
        cursor := t1[7]!
        let _ ← B.call (instName "grind_check" [.L OOD_GRIND_BITS]) [powOod.v, tabs.v] 0
        B.store levelRoots ((2 * lvl_k) + 2) (← B.load sent 0)
        B.store levelRoots ((2 * lvl_k) + 3) (← B.load sent 1)
        oodRow_ptr := ⟨oodZ, colsOff⟩
        let t2 ← B.call (instName "squeeze_point_from" [.L mu]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, zFirst.v, (← B.shifted oodRow_ptr.base oodRow_ptr.exp).v] 5
        fs0 := t2[0]!
        fs1 := t2[1]!
        fs2 := t2[2]!
        fs3 := t2[3]!
        fs4 := t2[4]!
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        rate ← B.stackBuf 8
        let (t3, t4) ← fsNext rate 0 cursor
        oodY := t3
        cursor_ptr := t4
        sp ← fsAbsorbNonce sp rate 1 (← B.load cursor_ptr.base cursor_ptr.exp)
        cursor_ptr := ⟨cursor_ptr.base, cursor_ptr.exp + 1⟩
        word0 := cellOf sp 0
        pow0 := cellOf sp 1
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
      let t5 ← B.targets [none, none, none, none, none]
      let t6 ← B.shifted queryPositions posOff
      let t7 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t6.v, t7.v, tabs.v] t5
      fs0 := cellOf t5 0
      fs1 := cellOf t5 1
      fs2 := cellOf t5 2
      fs3 := cellOf t5 3
      fs4 := cellOf t5 4
      if lvl_k ≠ last then
        sp ← fsCap fs0 fs1 fs2 fs3 fs4
        noRate ← B.stackBuf 8
        let (t8, t9) ← squeeze sp noRate 0
        sp := t8
        lam := t9
        lamInv ← B.fdiv (← B.const 1) lam
        fs0 := cellOf sp 8
        fs1 := cellOf sp 9
        fs2 := cellOf sp 10
        fs3 := cellOf sp 11
        fs4 := cellOf sp 12
      else
        pure () -- no use of this definition takes this branch
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        nHs := 0
        hsBits := 0
        hs_ptr := ⟨levelHs, foldsOff⟩
        for c_k in [0:2] do
          sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
          for i_k in [0:arrInt LIG_HIGH_BITS ml] do
            if ((c_k / (2 ^ i_k)) % 2) = 1 then
              sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
            else
              pure ()
          B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const (lit sc)))
        let c_k := 2
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        for i_k in [0:arrInt LIG_HIGH_BITS ml] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
        let c_k := 3
        sc := arrInt VANISH_INVS_BY_COLS (vanish + mu)
        let i_k := 0
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs_ptr.base (hs_ptr.exp + c_k) (← B.mul (← B.load sent (2 + c_k)) (← B.const sc_field))
      if lvl_k = last then
        pure () -- no use of this definition takes this branch
      else
        let t10 ← B.targets [none, none, none, none]
        let t11 ← B.shifted roundCoefs (2 * foldsOff)
        let t12 ← B.shifted hs_ptr.base hs_ptr.exp
        let t13 ← B.shifted queryPositions posOff
        let t14 ← B.shifted queryWinPtrs posOff
        B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L 0, .L 0, .L 0, .L 0])) [lam.v, lamInv.v, t11.v, t12.v, t13.v, t14.v] t10
        root0 := cellOf t10 0
        root1 := cellOf t10 1
        batched := cellOf t10 2
        lamPow := cellOf t10 3
      B.store levelRoots (2 * lvl_k) root0
      B.store levelRoots ((2 * lvl_k) + 1) root1
      if lvl_k ≠ last then
        B.store oodScalars (lvl_k + 1) lam
        claim ← B.add claim (← B.mul lam oodY)
        scale ← B.mul (← B.mul lam lam) lamPow
        claim ← B.add claim (← B.mul scale batched)
        B.store levelScales lvl_k scale
        B.store levelLamInvs lvl_k lamInv
      else
        pure () -- no use of this definition takes this branch
      colsOff := colsOff + mu
    let lvl_k := 5
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let posOff := arrInt LIG_POS_OFF ml
    let folds := arrInt LIG_FOLDS ml
    let mu := arrInt LIG_LOG_MSG_COLS ml
    let foldsOff := arrInt LIG_FOLDS_OFF ml
    vanish := (mu * (mu + 1)) / 2
    let j_k := 0
    let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
    fs0 := t0[0]!
    fs1 := t0[1]!
    fs2 := t0[2]!
    fs3 := t0[3]!
    fs4 := t0[4]!
    cursor := t0[5]!
    claim := t0[6]!
    for j_k in [1:folds] do
      let t0 ← B.call "opening_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v, (← B.shifted foldChallenges (foldsOff + j_k)).v, (← B.shifted roundCoefs (2 * (foldsOff + j_k))).v] 7
      fs0 := t0[0]!
      fs1 := t0[1]!
      fs2 := t0[2]!
      fs3 := t0[3]!
      fs4 := t0[4]!
      cursor := t0[5]!
      claim := t0[6]!
    if lvl_k = last then
      let t1 ← B.call (instName "opening_message" [.L (yrLen + folds), .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, finalMsg.v] 8
      word0 := t1[0]!
      pow0 := t1[1]!
      fs0 := t1[2]!
      fs1 := t1[3]!
      fs2 := t1[4]!
      fs3 := t1[5]!
      fs4 := t1[6]!
      cursor := t1[7]!
    else
      pure () -- no use of this definition takes this branch
    let _ ← B.call (instName "grind_check" [.L QUERY_GRIND_BITS]) [pow0.v, tabs.v] 0
    let t2 ← B.targets [none, none, none, none, none]
    let t3 ← B.shifted queryPositions posOff
    let t4 ← B.shifted queryWinPtrs posOff
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_positions" [.L (arrInt LIG_SQUEEZES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE)))])) [word0.v, fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, t3.v, t4.v, tabs.v] t2
    fs0 := cellOf t2 0
    fs1 := cellOf t2 1
    fs2 := cellOf t2 2
    fs3 := cellOf t2 3
    fs4 := cellOf t2 4
    let mut lamInv_nat : Nat := default
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      lam_nat := 0
      lamInv_nat := 0
    if lvl_k = last then
      nHs := yrLen + folds
      hsBits := yrLog + 1
      hs ← B.heapBufDyn (← B.const (gpowE nHs))
      for c_k in [0:2] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.load finalMsg c_k)
      for c_k in [2:6] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [6:8] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [2:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [8:10] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [10:14] do
        sc := 1
        for i_k in [0:3] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        for i_k in [3:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
      for c_k in [14:16] do
        sc := 1
        for i_k in [0:2] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 2
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        for i_k in [3:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc_fe := sc_field * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_fe))
      for c_k in [16:18] do
        sc := 1
        for i_k in [0:hsBits] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const (lit sc)))
      for c_k in [18:nHs] do
        sc := 1
        for i_k in [0:4] do
          if ((c_k / (2 ^ i_k)) % 2) = 1 then
            sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
          else
            pure ()
        let i_k := 4
        if ((c_k / (2 ^ i_k)) % 2) = 1 then
          sc_field := (lit sc) * (arrWord VANISH_INVS_BY_COLS (vanish + i_k))
          sc := sc * (arrInt VANISH_INVS_BY_COLS (vanish + i_k))
        else
          pure () -- no use of this definition takes this branch
        B.store hs c_k (← B.mul (← B.load finalMsg c_k) (← B.const sc_field))
    else
      pure () -- no use of this definition takes this branch
    if lvl_k = last then
      let t5 ← B.targets [none, none, none, none]
      let t6 ← B.const (lit lam_nat)
      let t7 ← B.const (lit lamInv_nat)
      let t8 ← B.shifted roundCoefs (2 * foldsOff)
      let t9 ← B.shifted queryPositions posOff
      let t10 ← B.shifted queryWinPtrs posOff
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_queries" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (1 / (lvl_k + 1)), .L folds, .L (arrInt LIG_LEAF_CELLS ml), .L (arrInt LIG_TREE_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_CAP_DEPTH (ml + (arm * LIG_RATE_STRIDE))), .L mu, .L nHs, .L hsBits, .L 1])) [t6.v, t7.v, t8.v, hs.v, t9.v, t10.v] t5
      root0 := cellOf t5 0
      root1 := cellOf t5 1
      batched := cellOf t5 2
      lamPow := cellOf t5 3
    else
      pure () -- no use of this definition takes this branch
    B.store levelRoots (2 * lvl_k) root0
    B.store levelRoots ((2 * lvl_k) + 1) root1
    if lvl_k ≠ last then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    colsOff := colsOff + mu
    let tailChallenges ← B.heapBufDyn (← B.const (gpowE YR_LOG_CAP))
    let mut tailC : Word := default
    for j_k in [0:yrLog] do
      let t15 ← B.call "opening_tail_round" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, claim.v, tabs.v] 8
      fs0 := t15[0]!
      fs1 := t15[1]!
      fs2 := t15[2]!
      fs3 := t15[3]!
      fs4 := t15[4]!
      cursor := t15[5]!
      claim := t15[6]!
      tailC := t15[7]!
      B.store tailChallenges j_k tailC
    let j_k := 4
    B.store tailChallenges j_k (← B.const 0)
    let yrAtTail ← call1 (instName "fold_final_msg" [.L yrLog]) [finalMsg.v, tailChallenges.v]
    let laneFolds := arrInt LIG_FOLDS (mIdx * LIG_MAX_LEVELS)
    let foldHead := nFolds - laneFolds
    let point ← B.heapBuf 40
    let point1 ← B.heapBuf 40
    for j_k in [0:foldHead] do
      B.store point j_k (← B.load foldChallenges (laneFolds + j_k))
      B.store point1 j_k (← B.add (← B.const 1) (← B.load foldChallenges (laneFolds + j_k)))
    for j_k in [0:yrLog] do
      B.store point (foldHead + j_k) (← B.load tailChallenges j_k)
      B.store point1 (foldHead + j_k) (← B.add (← B.const 1) (← B.load tailChallenges j_k))
    for j_k in [0:laneFolds] do
      B.store point ((foldHead + yrLog) + j_k) (← B.load foldChallenges j_k)
      B.store point1 ((foldHead + yrLog) + j_k) (← B.add (← B.const 1) (← B.load foldChallenges j_k))
    for j_k in [nFolds + yrLog:SIZE_BITS + QKECCAK_SLOT_LOG] do
      B.store point j_k (← B.const 0)
      B.store point1 j_k (← B.const 1)
    let mut basisTotal := 0
    for bl_k in [0:last] do
      basisTotal := (basisTotal + (arrInt LIG_RESIDUAL_PREFIX_LEN ((mIdx * LIG_MAX_LEVELS) + bl_k))) + yrLog
    let basisD ← B.heapBufDyn (← B.const (gpowE basisTotal))
    let levelScale ← B.heapBufDyn (← B.const (gpowE nLevels))
    let levelAfter ← B.heapBufDyn (← B.const (gpowE nLevels))
    let mut basisOff := 0
    let mut foldC : Word := default
    let mut coefB : Word := default
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
    vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
    scale ← B.load levelScales lvl_k
    let after : GPow := ⟨0⟩
    let mut after_word : Word := default
    let t_k := 0
    foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
    coefB := foldC
    B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
    scale ← B.mul scale coefB
    after_word := foldC
    for t_k in [1:prefixLen] do
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word foldC
    for j_k in [0:yrLog] do
      tailC ← B.load tailChallenges j_k
      coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
      B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
      scale ← B.mul scale coefB
      after_word ← B.mul after_word tailC
    B.store levelScale lvl_k scale
    B.store levelAfter lvl_k after_word
    basisOff := (basisOff + prefixLen) + yrLog
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let prefixLen := arrInt LIG_RESIDUAL_PREFIX_LEN ml
      vanish := ((arrInt LIG_LOG_MSG_COLS ml) * ((arrInt LIG_LOG_MSG_COLS ml) + 1)) / 2
      scale ← B.load levelScales lvl_k
      let after : GPow := ⟨0⟩
      let t_k := 0
      foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
      coefB := foldC
      B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
      scale ← B.mul scale coefB
      after_word := foldC
      for t_k in [1:prefixLen] do
        foldC ← B.load foldChallenges ((arrInt LIG_RESIDUAL_FOLD_OFF ml) + t_k)
        coefB ← B.mul foldC (← B.const (arrWord VANISH_INVS_BY_COLS (vanish + t_k)))
        B.store basisD (basisOff + t_k) (← B.fdiv (← B.add (← B.const 1) foldC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word foldC
      for j_k in [0:yrLog] do
        tailC ← B.load tailChallenges j_k
        coefB ← B.mul tailC (← B.const (arrWord VANISH_INVS_BY_COLS ((vanish + prefixLen) + j_k)))
        B.store basisD ((basisOff + prefixLen) + j_k) (← B.fdiv (← B.add (← B.const 1) tailC) coefB)
        scale ← B.mul scale coefB
        after_word ← B.mul after_word tailC
      B.store levelScale lvl_k scale
      B.store levelAfter lvl_k after_word
      basisOff := (basisOff + prefixLen) + yrLog
    let innerChain ← B.heapBufDyn (← B.const (gpowE (2 * nLevels)))
    B.store innerChain 0 (← B.const 0)
    B.store innerChain 1 claim
    let mut resBasis := 0
    let lvl_k := 0
    ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
    let t16 ← B.targets [none, none]
    let t17 ← B.load levelLamInvs lvl_k
    B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [queryPositions.v, basisD.v, levelHs.v, t17.v] t16
    let h := cellOf t16 0
    let hHigh := cellOf t16 1
    resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
    let acc := innerChain
    B.store acc 2 (← B.add (← B.load acc 0) (← B.mul (← B.load levelScale lvl_k) h))
    B.store acc 3 (← B.add (← B.load acc 1) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    for lvl_k in [1:last] do
      ml := (mIdx * LIG_MAX_LEVELS) + lvl_k
      let t16 ← B.targets [none, none]
      let t17 ← B.shifted queryPositions (arrInt LIG_POS_OFF ml)
      let t18 ← B.shifted basisD resBasis
      let t19 ← B.shifted levelHs (arrInt LIG_FOLDS_OFF ml)
      let t20 ← B.load levelLamInvs lvl_k
      B.dispatchInto rateSel ((List.range LIG_N_RATES).map fun arm => (instName "level_residual" [.L (arrInt LIG_QUERIES (ml + (arm * LIG_RATE_STRIDE))), .L (arrInt LIG_LOG_MSG_COLS ml), .L (arrInt LIG_FOLDS ml), .L (arrInt LIG_HIGH_BITS ml)])) [t17.v, t18.v, t19.v, t20.v] t16
      let h := cellOf t16 0
      let hHigh := cellOf t16 1
      resBasis := (resBasis + (arrInt LIG_RESIDUAL_PREFIX_LEN ml)) + yrLog
      let acc_ptr : Shifted := ⟨innerChain, 2 * lvl_k⟩
      B.store acc_ptr.base (acc_ptr.exp + 2) (← B.add (← B.load acc_ptr.base acc_ptr.exp) (← B.mul (← B.load levelScale lvl_k) h))
      B.store acc_ptr.base (acc_ptr.exp + 3) (← B.add (← B.load acc_ptr.base (acc_ptr.exp + 1)) (← B.mul (← B.mul (← B.load levelScales lvl_k) (← B.load levelAfter lvl_k)) hHigh))
    let oodInner := 0
    let mut oodOff := 0
    let mut oodInner_word : Word := default
    let oodLvl_k := 1
    ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
    let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
    let risStart := arrInt LIG_FOLDS_OFF ml
    let oz := oodZ
    oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
    let mut scalar ← B.load oodScalars oodLvl_k
    for t_k in [0:zFolded] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz t_k)) (← B.load foldChallenges (risStart + t_k)))
    for t_k in [0:yrLog] do
      scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz (zFolded + t_k))) (← B.load tailChallenges t_k))
    oodInner_word := scalar
    for oodLvl_k in [2:nLevels] do
      ml := (mIdx * LIG_MAX_LEVELS) + oodLvl_k
      let zFolded := (arrInt LIG_LOG_MSG_COLS (ml - 1)) - yrLog
      let risStart := arrInt LIG_FOLDS_OFF ml
      let oz_ptr : Shifted := ⟨oodZ, oodOff⟩
      oodOff := oodOff + (arrInt LIG_LOG_MSG_COLS (ml - 1))
      scalar ← B.load oodScalars oodLvl_k
      for t_k in [0:zFolded] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + t_k))) (← B.load foldChallenges (risStart + t_k)))
      for t_k in [0:yrLog] do
        scalar ← B.mul scalar (← B.add (← B.add (← B.const 1) (← B.load oz_ptr.base (oz_ptr.exp + (zFolded + t_k)))) (← B.load tailChallenges t_k))
      oodInner_word ← B.add oodInner_word scalar
    let total : Shifted := ⟨innerChain, 2 * last⟩
    let t21 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.load total.base total.exp) oodInner_word
    return [.load total.base.v (total.exp + 1)] ++ [.v point.v] ++ [.v point1.v] ++ [.into t21] ++ [.v yrAtTail.v]

set_option linter.unusedVariables false in
/-- `level_positions`, a `Const` family (`guests/lean_ethereum.py`, line 1519):

```
def level_positions(word0, fs0, fs1, fs2, fs3, fs4, positions, win_ptrs, tabs, squeezes: Const, depth: Const, cap_depth: Const):
    # A level's query positions, FIELD_BITS // depth a word: the first word, word0, drawn
    # by the query nonce's permutation, the rest one squeeze each. Row k of sqz is the
    # capacity of the permutation that drew word k - 1; returns the last one.
    sqz = HeapBuf((GEN ** (squeezes + 1)) ** FS_CELLS)
    sqz[GEN ** FS_CELLS] = fs0
    sqz[GEN ** (FS_CELLS + 1)] = fs1
    sqz[GEN ** (FS_CELLS + 2)] = fs2
    sqz[GEN ** (FS_CELLS + 3)] = fs3
    sqz[GEN ** (FS_CELLS + 4)] = fs4
    decode_query_windows(word0, positions, win_ptrs, tabs, depth, cap_depth)
    for xs in mul_range(GEN, GEN ** squeezes):
        row = sqz * xs ** FS_CELLS
        row_cap = fs_load(row, 0, 1)
        no_rate = StackBuf(8)
        row_sp, packed_word = squeeze(row_cap, no_rate, 0)
        fs_store(row * GEN ** FS_CELLS, 0, 1, row_sp)
        query_ptr = xs ** (FIELD_BITS // depth)
        decode_query_windows(packed_word, positions * query_ptr, win_ptrs * query_ptr, tabs, depth, cap_depth)
    sp = fs_load(sqz * (GEN ** squeezes) ** FS_CELLS, 0, 1)
    return sp[0], sp[1], sp[2], sp[3], sp[4]
```
-/
def levelPositions (squeezes : Nat) (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "level_positions" [.L squeezes, .L depth, .L capDepth]
  arity := 9
  rets := 5
  body ps := do
    let word0 := cellOf ps 0
    let fs0 := cellOf ps 1
    let fs1 := cellOf ps 2
    let fs2 := cellOf ps 3
    let fs3 := cellOf ps 4
    let fs4 := cellOf ps 5
    let positions := cellOf ps 6
    let winPtrs := cellOf ps 7
    let tabs := cellOf ps 8
    let sqz ← B.heapBufDyn (← B.const ((gpowE (squeezes + 1)) ^ FS_CELLS))
    B.store sqz FS_CELLS fs0
    B.store sqz 6 fs1
    B.store sqz 7 fs2
    B.store sqz 8 fs3
    B.store sqz 9 fs4
    let _ ← B.call (instName "decode_query_windows" [.L depth, .L capDepth]) [word0.v, positions.v, winPtrs.v, tabs.v] 0
    B.loopRtF 1 (B.const (gpowE squeezes)) 4 (pure ([sqz.v, positions.v, winPtrs.v, tabs.v])) fun xs caps => do
      let sqz := cellOf caps 0
      let positions := cellOf caps 1
      let winPtrs := cellOf caps 2
      let tabs := cellOf caps 3
      let row ← B.mul sqz (← B.pow xs FS_CELLS)
      let rowCap ← fsLoad row 0 1
      let noRate ← B.stackBuf 8
      let (t0, t1) ← squeeze rowCap noRate 0
      let rowSp := t0
      let packedWord := t1
      fsStore (⟨row, FS_CELLS⟩) 0 1 rowSp
      let queryPtr ← B.pow xs (FIELD_BITS / depth)
      let _ ← B.call (instName "decode_query_windows" [.L depth, .L capDepth]) [packedWord.v, (← B.mul positions queryPtr).v, (← B.mul winPtrs queryPtr).v, tabs.v] 0
      pure ()
    let sp ← fsLoad (← B.mul sqz (← B.const ((gpowE squeezes) ^ FS_CELLS))) 0 1
    return [.v (cellOf sp 0).v] ++ [.v (cellOf sp 1).v] ++ [.v (cellOf sp 2).v] ++ [.v (cellOf sp 3).v] ++ [.v (cellOf sp 4).v]

set_option linter.unusedVariables false in
/-- `level_queries`, a `Const` family (`guests/lean_ethereum.py`, line 1542):

```
def level_queries(lam, lam_inv, coefs, hs, positions, win_ptrs, n_queries: Const, base: Const, folds: Const, leaf_cells: Const, depth: Const, cap_depth: Const, mu: Const, n_hs: Const, hs_bits: Const, final: Const):
    # A level's Merkle cap, hinted and checked up to its root, and the level's query batch
    # walked into it. Returns the root, the batch's sum, and lam^n_queries. At level 0 a
    # leaf image lists its lanes from the top down: the lanes a padding-free commitment
    # leaves out are its LEADING words, whose whole blocks the committer hashes once for
    # all leaves. The flip is a compile-time index.
    cap = HeapBuf(GEN ** (4 * 2 ** cap_depth))
    hint_witness(cap[0:4 * 2 ** cap_depth], "merkle_caps")
    flags = HeapBuf(GEN ** (2 ** cap_depth))
    hint_witness(flags[0:2 ** cap_depth], "merkle_cap_active")
    root_0, root_1 = verify_merkle_cap(cap, flags, cap_depth)
    if const(base == 1):
        pairs = n_queries // 2
        odd = n_queries % 2
    else:
        pairs = n_queries
        odd = 0
    batched = opening_queries(cap, flags, lam_inv, coefs, hs, positions, win_ptrs, GEN ** pairs, odd, base, folds, leaf_cells, depth, cap_depth, mu, mu * (mu + 1) // 2, n_hs, hs_bits, final)
    return root_0, root_1, batched, lam ** n_queries
```
-/
def levelQueries (nQueries : Nat) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : GFn where
  name := instName "level_queries" [.L nQueries, .L base, .L folds, .L leafCells, .L depth, .L capDepth, .L mu, .L nHs, .L hsBits, .L final]
  arity := 6
  rets := 4
  body ps := do
    let lam := cellOf ps 0
    let lamInv := cellOf ps 1
    let coefs := cellOf ps 2
    let hs := cellOf ps 3
    let positions := cellOf ps 4
    let winPtrs := cellOf ps 5
    let cap ← B.heapBufDyn (← B.const (gpowE (4 * (2 ^ capDepth))))
    B.witness "merkle_caps" (.heap cap.v 0 (4 * (2 ^ capDepth)))
    let flags ← B.heapBufDyn (← B.const (gpowE (2 ^ capDepth)))
    B.witness "merkle_cap_active" (.heap flags.v 0 (2 ^ capDepth))
    let t0 ← B.call (instName "verify_merkle_cap" [.L capDepth]) [cap.v, flags.v] 2
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
    let batched ← call1 (instName "opening_queries" [.L odd, .L base, .L folds, .L leafCells, .L depth, .L capDepth, .L mu, .L ((mu * (mu + 1)) / 2), .L nHs, .L hsBits, .L final]) [cap.v, flags.v, lamInv.v, coefs.v, hs.v, positions.v, winPtrs.v, (← B.const (gpowE pairs)).v]
    let t1 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.pow lam nQueries)
    return [.v root0.v] ++ [.v root1.v] ++ [.v batched.v] ++ [.into t1]

set_option linter.unusedVariables false in
/-- `level_residual`, a `Const` family (`guests/lean_ethereum.py`, line 1481):

```
def level_residual(positions, row_d, hs, lam_inv, n_queries: Const, n_cols: Const, n_hs: Const, hs_bits: Const):
    # A non-final level's residual chains at the terminal point, RES_BATCH queries an
    # iteration sharing the row's reads and constants, then the rest one at a time. Query
    # q is weighted lam^q: each chain runs h <- (h + term_q) * lam_inv, ending
    # at lam^-n * sum_q lam^q term_q.
    chain = HeapBuf(GEN ** (2 * (n_queries // RES_BATCH + 1)))
    chain[GEN ** 0] = 0
    chain[GEN ** 1] = 0
    for xr in mul_range(1, GEN ** (n_queries // RES_BATCH)):
        batch = positions * xr ** RES_BATCH
        rec = chain * xr * xr
        h = rec[GEN ** 0]
        h_high = rec[GEN ** 1]
        for k in unroll(0, RES_BATCH):
            eq_q, high_q = residual_query(batch[GEN ** k], row_d, hs, n_cols, n_hs, hs_bits)
            h = (h + eq_q) * lam_inv
            h_high = (h_high + high_q) * lam_inv
        rec[GEN ** 2] = h
        rec[GEN ** 3] = h_high
    rec = chain * GEN ** (2 * (n_queries // RES_BATCH))
    h = rec[GEN ** 0]
    h_high = rec[GEN ** 1]
    if const(n_queries % RES_BATCH != 0):
        rest = HeapBuf(GEN ** (2 * (n_queries % RES_BATCH + 1)))
        rest[GEN ** 0] = h
        rest[GEN ** 1] = h_high
        tail = positions * (GEN ** (n_queries // RES_BATCH)) ** RES_BATCH
        for xq in mul_range(1, GEN ** (n_queries % RES_BATCH)):
            rq = rest * xq * xq
            eq_q, high_q = residual_query(tail[xq], row_d, hs, n_cols, n_hs, hs_bits)
            rq[GEN ** 2] = (rq[GEN ** 0] + eq_q) * lam_inv
            rq[GEN ** 3] = (rq[GEN ** 1] + high_q) * lam_inv
        end = rest * GEN ** (2 * (n_queries % RES_BATCH))
        h = end[GEN ** 0]
        h_high = end[GEN ** 1]
    return h, h_high
```
-/
def levelResidual (nQueries : Nat) (nCols : Nat) (nHs : Nat) (hsBits : Nat) : GFn where
  name := instName "level_residual" [.L nQueries, .L nCols, .L nHs, .L hsBits]
  arity := 4
  rets := 2
  body ps := do
    let positions := cellOf ps 0
    let rowD := cellOf ps 1
    let hs := cellOf ps 2
    let lamInv := cellOf ps 3
    let chain ← B.heapBufDyn (← B.const (gpowE (2 * ((nQueries / RES_BATCH) + 1))))
    B.store chain 0 (← B.const 0)
    B.store chain 1 (← B.const 0)
    B.loopRtF 0 (B.const (gpowE (nQueries / RES_BATCH))) 5 (pure ([positions.v, chain.v, rowD.v, hs.v, lamInv.v])) fun xr caps => do
      let positions := cellOf caps 0
      let chain := cellOf caps 1
      let rowD := cellOf caps 2
      let hs := cellOf caps 3
      let lamInv := cellOf caps 4
      let batch ← B.mul positions (← B.pow xr RES_BATCH)
      let rec' ← B.mul (← B.mul chain xr) xr
      let mut h ← B.load rec' 0
      let mut hHigh ← B.load rec' 1
      for k_k in [0:RES_BATCH] do
        let (t0, t1) ← residualQuery (← B.load batch k_k) rowD hs nCols nHs hsBits
        let eqQ := t0
        let highQ := t1
        h ← B.mul (← B.add h eqQ) lamInv
        hHigh ← B.mul (← B.add hHigh highQ) lamInv
      B.store rec' 2 h
      B.store rec' 3 hHigh
    let rec' : Shifted := ⟨chain, 2 * (nQueries / RES_BATCH)⟩
    let mut h ← B.load rec'.base rec'.exp
    let mut hHigh ← B.load rec'.base (rec'.exp + 1)
    if (nQueries % RES_BATCH) ≠ 0 then
      let rest ← B.heapBufDyn (← B.const (gpowE (2 * ((nQueries % RES_BATCH) + 1))))
      B.store rest 0 h
      B.store rest 1 hHigh
      let tail ← B.mul positions (← B.const ((gpowE (nQueries / RES_BATCH)) ^ RES_BATCH))
      B.loopRtF 0 (B.const (gpowE (nQueries % RES_BATCH))) 5 (pure ([rest.v, tail.v, rowD.v, hs.v, lamInv.v])) fun xq caps => do
        let rest := cellOf caps 0
        let tail := cellOf caps 1
        let rowD := cellOf caps 2
        let hs := cellOf caps 3
        let lamInv := cellOf caps 4
        let rq ← B.mul (← B.mul rest xq) xq
        let (t0, t1) ← residualQuery (← B.load (← B.mul tail xq) 0) rowD hs nCols nHs hsBits
        let eqQ := t0
        let highQ := t1
        B.store rq 2 (← B.mul (← B.add (← B.load rq 0) eqQ) lamInv)
        B.store rq 3 (← B.mul (← B.add (← B.load rq 1) highQ) lamInv)
      let end' : Shifted := ⟨rest, 2 * (nQueries % RES_BATCH)⟩
      h ← B.load end'.base end'.exp
      hHigh ← B.load end'.base (end'.exp + 1)
    else
      pure () -- no use of this definition takes this branch
    return [.v h.v] ++ [.v hHigh.v]

set_option linter.unusedVariables false in
/-- `level_residual`, a `Const` family (`guests/lean_ethereum.py`, line 1481):

```
def level_residual(positions, row_d, hs, lam_inv, n_queries: Const, n_cols: Const, n_hs: Const, hs_bits: Const):
    # A non-final level's residual chains at the terminal point, RES_BATCH queries an
    # iteration sharing the row's reads and constants, then the rest one at a time. Query
    # q is weighted lam^q: each chain runs h <- (h + term_q) * lam_inv, ending
    # at lam^-n * sum_q lam^q term_q.
    chain = HeapBuf(GEN ** (2 * (n_queries // RES_BATCH + 1)))
    chain[GEN ** 0] = 0
    chain[GEN ** 1] = 0
    for xr in mul_range(1, GEN ** (n_queries // RES_BATCH)):
        batch = positions * xr ** RES_BATCH
        rec = chain * xr * xr
        h = rec[GEN ** 0]
        h_high = rec[GEN ** 1]
        for k in unroll(0, RES_BATCH):
            eq_q, high_q = residual_query(batch[GEN ** k], row_d, hs, n_cols, n_hs, hs_bits)
            h = (h + eq_q) * lam_inv
            h_high = (h_high + high_q) * lam_inv
        rec[GEN ** 2] = h
        rec[GEN ** 3] = h_high
    rec = chain * GEN ** (2 * (n_queries // RES_BATCH))
    h = rec[GEN ** 0]
    h_high = rec[GEN ** 1]
    if const(n_queries % RES_BATCH != 0):
        rest = HeapBuf(GEN ** (2 * (n_queries % RES_BATCH + 1)))
        rest[GEN ** 0] = h
        rest[GEN ** 1] = h_high
        tail = positions * (GEN ** (n_queries // RES_BATCH)) ** RES_BATCH
        for xq in mul_range(1, GEN ** (n_queries % RES_BATCH)):
            rq = rest * xq * xq
            eq_q, high_q = residual_query(tail[xq], row_d, hs, n_cols, n_hs, hs_bits)
            rq[GEN ** 2] = (rq[GEN ** 0] + eq_q) * lam_inv
            rq[GEN ** 3] = (rq[GEN ** 1] + high_q) * lam_inv
        end = rest * GEN ** (2 * (n_queries % RES_BATCH))
        h = end[GEN ** 0]
        h_high = end[GEN ** 1]
    return h, h_high
```
-/
def levelResidual_2 (nQueries : Nat) (nCols : Nat) (nHs : Nat) (hsBits : Nat) : GFn where
  name := instName "level_residual" [.L nQueries, .L nCols, .L nHs, .L hsBits]
  arity := 4
  rets := 2
  body ps := do
    let positions := cellOf ps 0
    let rowD := cellOf ps 1
    let hs := cellOf ps 2
    let lamInv := cellOf ps 3
    let chain ← B.heapBufDyn (← B.const (gpowE (2 * ((nQueries / RES_BATCH) + 1))))
    B.store chain 0 (← B.const 0)
    B.store chain 1 (← B.const 0)
    B.loopRtF 0 (B.const (gpowE (nQueries / RES_BATCH))) 5 (pure ([positions.v, chain.v, rowD.v, hs.v, lamInv.v])) fun xr caps => do
      let positions := cellOf caps 0
      let chain := cellOf caps 1
      let rowD := cellOf caps 2
      let hs := cellOf caps 3
      let lamInv := cellOf caps 4
      let batch ← B.mul positions (← B.pow xr RES_BATCH)
      let rec' ← B.mul (← B.mul chain xr) xr
      let mut h ← B.load rec' 0
      let mut hHigh ← B.load rec' 1
      for k_k in [0:RES_BATCH] do
        let (t0, t1) ← residualQuery_2 (← B.load batch k_k) rowD hs nCols nHs hsBits
        let eqQ := t0
        let highQ := t1
        h ← B.mul (← B.add h eqQ) lamInv
        hHigh ← B.mul (← B.add hHigh highQ) lamInv
      B.store rec' 2 h
      B.store rec' 3 hHigh
    let rec' : Shifted := ⟨chain, 2 * (nQueries / RES_BATCH)⟩
    let mut h ← B.load rec'.base rec'.exp
    let mut hHigh ← B.load rec'.base (rec'.exp + 1)
    if (nQueries % RES_BATCH) ≠ 0 then
      let rest ← B.heapBufDyn (← B.const (gpowE (2 * ((nQueries % RES_BATCH) + 1))))
      B.store rest 0 h
      B.store rest 1 hHigh
      let tail ← B.mul positions (← B.const ((gpowE (nQueries / RES_BATCH)) ^ RES_BATCH))
      B.loopRtF 0 (B.const (gpowE (nQueries % RES_BATCH))) 5 (pure ([rest.v, tail.v, rowD.v, hs.v, lamInv.v])) fun xq caps => do
        let rest := cellOf caps 0
        let tail := cellOf caps 1
        let rowD := cellOf caps 2
        let hs := cellOf caps 3
        let lamInv := cellOf caps 4
        let rq ← B.mul (← B.mul rest xq) xq
        let (t0, t1) ← residualQuery_2 (← B.load (← B.mul tail xq) 0) rowD hs nCols nHs hsBits
        let eqQ := t0
        let highQ := t1
        B.store rq 2 (← B.mul (← B.add (← B.load rq 0) eqQ) lamInv)
        B.store rq 3 (← B.mul (← B.add (← B.load rq 1) highQ) lamInv)
      let end' : Shifted := ⟨rest, 2 * (nQueries % RES_BATCH)⟩
      h ← B.load end'.base end'.exp
      hHigh ← B.load end'.base (end'.exp + 1)
    else
      pure ()
    return [.v h.v] ++ [.v hHigh.v]

set_option linter.unusedVariables false in
/-- `opening_queries`, a `Const` family (`guests/lean_ethereum.py`, line 1429):

```
def opening_queries(cap, flags, lam_inv, coefs, hs, positions, query_win_ptrs, n_iters_g, odd: Const, base: Const, folds: Const, leaf_cells: Const, depth: Const, cap_depth: Const, mu: Const, vanish: Const, n_hs: Const, hs_bits: Const, final: Const):
    # Specialize by row and path shape so opening configurations share query code.
    # Base-field rows (level 0) run two queries an iteration, sharing the loop
    # overhead and the challenge reads; an odd count runs its first query alone,
    # ahead of the pairs. Extension rows run one query an iteration.
    # Query k is weighted lam^k: the chain runs h <- (h + v_k) / lam, ending at
    # sum_k lam^(k - n) v_k, which the caller scales by lam^n. The final level's
    # queries are checks, with nothing to sum.
    chain = HeapBuf(n_iters_g * GEN)
    if odd == 1:
        chain[GEN ** 0] = opening_query(cap, flags, coefs, hs, positions[GEN ** 0], query_win_ptrs[GEN ** 0], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final) * lam_inv
    else:
        chain[GEN ** 0] = 0
    for xi in mul_range(1, n_iters_g):
        if base == 1:
            pair_pos = positions * xi * xi
            pair_wins = query_win_ptrs * xi * xi
            d0 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** odd], pair_wins[GEN ** odd], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            d1 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** (odd + 1)], pair_wins[GEN ** (odd + 1)], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = ((chain[xi] + d0) * lam_inv + d1) * lam_inv
        else:
            d = opening_query(cap, flags, coefs, hs, positions[xi], query_win_ptrs[xi], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = (chain[xi] + d) * lam_inv
    if final == 0:
        total = chain[n_iters_g]
    else:
        total = 0
    return total
```
-/
def openingQueries (odd : Nat) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : GFn where
  name := instName "opening_queries" [.L odd, .L base, .L folds, .L leafCells, .L depth, .L capDepth, .L mu, .L vanish, .L nHs, .L hsBits, .L final]
  arity := 8
  rets := 1
  body ps := do
    let cap := cellOf ps 0
    let flags := cellOf ps 1
    let lamInv := cellOf ps 2
    let coefs := cellOf ps 3
    let hs := cellOf ps 4
    let positions := cellOf ps 5
    let queryWinPtrs := cellOf ps 6
    let nItersG := cellOf ps 7
    let chain ← B.heapBufDyn (← B.shifted nItersG 1)
    if odd = 1 then
      let t0 ← openingQuery cap flags coefs hs (← B.load positions 0) (← B.load queryWinPtrs 0) base folds leafCells depth capDepth mu vanish nHs hsBits final
      B.store chain 0 (← B.mul t0 lamInv)
    else
      B.store chain 0 (← B.const 0)
    B.loopRtF 0 (pure nItersG) 8 (pure ([positions.v, queryWinPtrs.v, cap.v, flags.v, coefs.v, hs.v, chain.v, lamInv.v])) fun xi caps => do
      let positions := cellOf caps 0
      let queryWinPtrs := cellOf caps 1
      let cap := cellOf caps 2
      let flags := cellOf caps 3
      let coefs := cellOf caps 4
      let hs := cellOf caps 5
      let chain := cellOf caps 6
      let lamInv := cellOf caps 7
      if base = 1 then
        let pairPos ← B.mul (← B.mul positions xi) xi
        let pairWins ← B.mul (← B.mul queryWinPtrs xi) xi
        let d0 ← openingQuery cap flags coefs hs (← B.load pairPos odd) (← B.load pairWins odd) base folds leafCells depth capDepth mu vanish nHs hsBits final
        let d1 ← openingQuery cap flags coefs hs (← B.load pairPos (odd + 1)) (← B.load pairWins (odd + 1)) base folds leafCells depth capDepth mu vanish nHs hsBits final
        if final = 0 then
          let t0 ← B.mul (← B.add (← B.mul (← B.add (← B.load (← B.mul chain xi) 0) d0) lamInv) d1) lamInv
          B.store (← B.mul chain xi) 1 t0
        else
          pure () -- no use of this definition takes this branch
      else
        let d ← openingQuery_2 cap flags coefs hs (← B.load (← B.mul positions xi) 0) (← B.load (← B.mul queryWinPtrs xi) 0) base folds leafCells depth capDepth mu vanish nHs hsBits final
        if final = 0 then
          let t0 ← B.mul (← B.add (← B.load (← B.mul chain xi) 0) d) lamInv
          B.store (← B.mul chain xi) 1 t0
        else
          pure () -- no use of this definition takes this branch
    let mut total : Word := default
    if final = 0 then
      total ← B.load (← B.mul chain nItersG) 0
    else
      pure () -- no use of this definition takes this branch
    return [.v total.v]

set_option linter.unusedVariables false in
/-- `opening_queries`, a `Const` family (`guests/lean_ethereum.py`, line 1429):

```
def opening_queries(cap, flags, lam_inv, coefs, hs, positions, query_win_ptrs, n_iters_g, odd: Const, base: Const, folds: Const, leaf_cells: Const, depth: Const, cap_depth: Const, mu: Const, vanish: Const, n_hs: Const, hs_bits: Const, final: Const):
    # Specialize by row and path shape so opening configurations share query code.
    # Base-field rows (level 0) run two queries an iteration, sharing the loop
    # overhead and the challenge reads; an odd count runs its first query alone,
    # ahead of the pairs. Extension rows run one query an iteration.
    # Query k is weighted lam^k: the chain runs h <- (h + v_k) / lam, ending at
    # sum_k lam^(k - n) v_k, which the caller scales by lam^n. The final level's
    # queries are checks, with nothing to sum.
    chain = HeapBuf(n_iters_g * GEN)
    if odd == 1:
        chain[GEN ** 0] = opening_query(cap, flags, coefs, hs, positions[GEN ** 0], query_win_ptrs[GEN ** 0], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final) * lam_inv
    else:
        chain[GEN ** 0] = 0
    for xi in mul_range(1, n_iters_g):
        if base == 1:
            pair_pos = positions * xi * xi
            pair_wins = query_win_ptrs * xi * xi
            d0 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** odd], pair_wins[GEN ** odd], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            d1 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** (odd + 1)], pair_wins[GEN ** (odd + 1)], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = ((chain[xi] + d0) * lam_inv + d1) * lam_inv
        else:
            d = opening_query(cap, flags, coefs, hs, positions[xi], query_win_ptrs[xi], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = (chain[xi] + d) * lam_inv
    if final == 0:
        total = chain[n_iters_g]
    else:
        total = 0
    return total
```
-/
def openingQueries_2 (odd : Nat) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : GFn where
  name := instName "opening_queries" [.L odd, .L base, .L folds, .L leafCells, .L depth, .L capDepth, .L mu, .L vanish, .L nHs, .L hsBits, .L final]
  arity := 8
  rets := 1
  body ps := do
    let cap := cellOf ps 0
    let flags := cellOf ps 1
    let lamInv := cellOf ps 2
    let coefs := cellOf ps 3
    let hs := cellOf ps 4
    let positions := cellOf ps 5
    let queryWinPtrs := cellOf ps 6
    let nItersG := cellOf ps 7
    let chain ← B.heapBufDyn (← B.shifted nItersG 1)
    if odd = 1 then
      pure () -- no use of this definition takes this branch
    else
      B.store chain 0 (← B.const 0)
    B.loopRtF 0 (pure nItersG) 8 (pure ([positions.v, queryWinPtrs.v, cap.v, flags.v, coefs.v, hs.v, chain.v, lamInv.v])) fun xi caps => do
      let positions := cellOf caps 0
      let queryWinPtrs := cellOf caps 1
      let cap := cellOf caps 2
      let flags := cellOf caps 3
      let coefs := cellOf caps 4
      let hs := cellOf caps 5
      let chain := cellOf caps 6
      let lamInv := cellOf caps 7
      if base = 1 then
        pure () -- no use of this definition takes this branch
      else
        let d : E ← openingQuery_3 cap flags coefs hs (← B.load (← B.mul positions xi) 0) (← B.load (← B.mul queryWinPtrs xi) 0) base folds leafCells depth capDepth mu vanish nHs hsBits final
        if final = 0 then
          pure () -- no use of this definition takes this branch
        else
          pure ()
    let mut total : Nat := default
    if final = 0 then
      pure () -- no use of this definition takes this branch
    else
      total := 0
    return [.c (lit total)]

set_option linter.unusedVariables false in
/-- `opening_queries`, a `Const` family (`guests/lean_ethereum.py`, line 1429):

```
def opening_queries(cap, flags, lam_inv, coefs, hs, positions, query_win_ptrs, n_iters_g, odd: Const, base: Const, folds: Const, leaf_cells: Const, depth: Const, cap_depth: Const, mu: Const, vanish: Const, n_hs: Const, hs_bits: Const, final: Const):
    # Specialize by row and path shape so opening configurations share query code.
    # Base-field rows (level 0) run two queries an iteration, sharing the loop
    # overhead and the challenge reads; an odd count runs its first query alone,
    # ahead of the pairs. Extension rows run one query an iteration.
    # Query k is weighted lam^k: the chain runs h <- (h + v_k) / lam, ending at
    # sum_k lam^(k - n) v_k, which the caller scales by lam^n. The final level's
    # queries are checks, with nothing to sum.
    chain = HeapBuf(n_iters_g * GEN)
    if odd == 1:
        chain[GEN ** 0] = opening_query(cap, flags, coefs, hs, positions[GEN ** 0], query_win_ptrs[GEN ** 0], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final) * lam_inv
    else:
        chain[GEN ** 0] = 0
    for xi in mul_range(1, n_iters_g):
        if base == 1:
            pair_pos = positions * xi * xi
            pair_wins = query_win_ptrs * xi * xi
            d0 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** odd], pair_wins[GEN ** odd], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            d1 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** (odd + 1)], pair_wins[GEN ** (odd + 1)], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = ((chain[xi] + d0) * lam_inv + d1) * lam_inv
        else:
            d = opening_query(cap, flags, coefs, hs, positions[xi], query_win_ptrs[xi], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = (chain[xi] + d) * lam_inv
    if final == 0:
        total = chain[n_iters_g]
    else:
        total = 0
    return total
```
-/
def openingQueries_3 (odd : Nat) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : GFn where
  name := instName "opening_queries" [.L odd, .L base, .L folds, .L leafCells, .L depth, .L capDepth, .L mu, .L vanish, .L nHs, .L hsBits, .L final]
  arity := 8
  rets := 1
  body ps := do
    let cap := cellOf ps 0
    let flags := cellOf ps 1
    let lamInv := cellOf ps 2
    let coefs := cellOf ps 3
    let hs := cellOf ps 4
    let positions := cellOf ps 5
    let queryWinPtrs := cellOf ps 6
    let nItersG := cellOf ps 7
    let chain ← B.heapBufDyn (← B.shifted nItersG 1)
    if odd = 1 then
      pure () -- no use of this definition takes this branch
    else
      B.store chain 0 (← B.const 0)
    B.loopRtF 0 (pure nItersG) 8 (pure ([positions.v, queryWinPtrs.v, cap.v, flags.v, coefs.v, hs.v, chain.v, lamInv.v])) fun xi caps => do
      let positions := cellOf caps 0
      let queryWinPtrs := cellOf caps 1
      let cap := cellOf caps 2
      let flags := cellOf caps 3
      let coefs := cellOf caps 4
      let hs := cellOf caps 5
      let chain := cellOf caps 6
      let lamInv := cellOf caps 7
      if base = 1 then
        pure () -- no use of this definition takes this branch
      else
        let d : E ← openingQuery_4 cap flags coefs hs (← B.load (← B.mul positions xi) 0) (← B.load (← B.mul queryWinPtrs xi) 0) base folds leafCells depth capDepth mu vanish nHs hsBits final
        if final = 0 then
          pure () -- no use of this definition takes this branch
        else
          pure ()
    let mut total : Nat := default
    if final = 0 then
      pure () -- no use of this definition takes this branch
    else
      total := 0
    return [.c (lit total)]

set_option linter.unusedVariables false in
/-- `opening_queries`, a `Const` family (`guests/lean_ethereum.py`, line 1429):

```
def opening_queries(cap, flags, lam_inv, coefs, hs, positions, query_win_ptrs, n_iters_g, odd: Const, base: Const, folds: Const, leaf_cells: Const, depth: Const, cap_depth: Const, mu: Const, vanish: Const, n_hs: Const, hs_bits: Const, final: Const):
    # Specialize by row and path shape so opening configurations share query code.
    # Base-field rows (level 0) run two queries an iteration, sharing the loop
    # overhead and the challenge reads; an odd count runs its first query alone,
    # ahead of the pairs. Extension rows run one query an iteration.
    # Query k is weighted lam^k: the chain runs h <- (h + v_k) / lam, ending at
    # sum_k lam^(k - n) v_k, which the caller scales by lam^n. The final level's
    # queries are checks, with nothing to sum.
    chain = HeapBuf(n_iters_g * GEN)
    if odd == 1:
        chain[GEN ** 0] = opening_query(cap, flags, coefs, hs, positions[GEN ** 0], query_win_ptrs[GEN ** 0], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final) * lam_inv
    else:
        chain[GEN ** 0] = 0
    for xi in mul_range(1, n_iters_g):
        if base == 1:
            pair_pos = positions * xi * xi
            pair_wins = query_win_ptrs * xi * xi
            d0 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** odd], pair_wins[GEN ** odd], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            d1 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** (odd + 1)], pair_wins[GEN ** (odd + 1)], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = ((chain[xi] + d0) * lam_inv + d1) * lam_inv
        else:
            d = opening_query(cap, flags, coefs, hs, positions[xi], query_win_ptrs[xi], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = (chain[xi] + d) * lam_inv
    if final == 0:
        total = chain[n_iters_g]
    else:
        total = 0
    return total
```
-/
def openingQueries_4 (odd : Nat) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : GFn where
  name := instName "opening_queries" [.L odd, .L base, .L folds, .L leafCells, .L depth, .L capDepth, .L mu, .L vanish, .L nHs, .L hsBits, .L final]
  arity := 8
  rets := 1
  body ps := do
    let cap := cellOf ps 0
    let flags := cellOf ps 1
    let lamInv := cellOf ps 2
    let coefs := cellOf ps 3
    let hs := cellOf ps 4
    let positions := cellOf ps 5
    let queryWinPtrs := cellOf ps 6
    let nItersG := cellOf ps 7
    let chain ← B.heapBufDyn (← B.shifted nItersG 1)
    if odd = 1 then
      pure () -- no use of this definition takes this branch
    else
      B.store chain 0 (← B.const 0)
    B.loopRtF 0 (pure nItersG) 8 (pure ([positions.v, queryWinPtrs.v, cap.v, flags.v, coefs.v, hs.v, chain.v, lamInv.v])) fun xi caps => do
      let positions := cellOf caps 0
      let queryWinPtrs := cellOf caps 1
      let cap := cellOf caps 2
      let flags := cellOf caps 3
      let coefs := cellOf caps 4
      let hs := cellOf caps 5
      let chain := cellOf caps 6
      let lamInv := cellOf caps 7
      if base = 1 then
        pure () -- no use of this definition takes this branch
      else
        let d : E ← openingQuery_5 cap flags coefs hs (← B.load (← B.mul positions xi) 0) (← B.load (← B.mul queryWinPtrs xi) 0) base folds leafCells depth capDepth mu vanish nHs hsBits final
        if final = 0 then
          pure () -- no use of this definition takes this branch
        else
          pure ()
    let mut total : Nat := default
    if final = 0 then
      pure () -- no use of this definition takes this branch
    else
      total := 0
    return [.c (lit total)]

set_option linter.unusedVariables false in
/-- `opening_queries`, a `Const` family (`guests/lean_ethereum.py`, line 1429):

```
def opening_queries(cap, flags, lam_inv, coefs, hs, positions, query_win_ptrs, n_iters_g, odd: Const, base: Const, folds: Const, leaf_cells: Const, depth: Const, cap_depth: Const, mu: Const, vanish: Const, n_hs: Const, hs_bits: Const, final: Const):
    # Specialize by row and path shape so opening configurations share query code.
    # Base-field rows (level 0) run two queries an iteration, sharing the loop
    # overhead and the challenge reads; an odd count runs its first query alone,
    # ahead of the pairs. Extension rows run one query an iteration.
    # Query k is weighted lam^k: the chain runs h <- (h + v_k) / lam, ending at
    # sum_k lam^(k - n) v_k, which the caller scales by lam^n. The final level's
    # queries are checks, with nothing to sum.
    chain = HeapBuf(n_iters_g * GEN)
    if odd == 1:
        chain[GEN ** 0] = opening_query(cap, flags, coefs, hs, positions[GEN ** 0], query_win_ptrs[GEN ** 0], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final) * lam_inv
    else:
        chain[GEN ** 0] = 0
    for xi in mul_range(1, n_iters_g):
        if base == 1:
            pair_pos = positions * xi * xi
            pair_wins = query_win_ptrs * xi * xi
            d0 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** odd], pair_wins[GEN ** odd], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            d1 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** (odd + 1)], pair_wins[GEN ** (odd + 1)], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = ((chain[xi] + d0) * lam_inv + d1) * lam_inv
        else:
            d = opening_query(cap, flags, coefs, hs, positions[xi], query_win_ptrs[xi], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = (chain[xi] + d) * lam_inv
    if final == 0:
        total = chain[n_iters_g]
    else:
        total = 0
    return total
```
-/
def openingQueries_5 (odd : Nat) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : GFn where
  name := instName "opening_queries" [.L odd, .L base, .L folds, .L leafCells, .L depth, .L capDepth, .L mu, .L vanish, .L nHs, .L hsBits, .L final]
  arity := 8
  rets := 1
  body ps := do
    let cap := cellOf ps 0
    let flags := cellOf ps 1
    let lamInv := cellOf ps 2
    let coefs := cellOf ps 3
    let hs := cellOf ps 4
    let positions := cellOf ps 5
    let queryWinPtrs := cellOf ps 6
    let nItersG := cellOf ps 7
    let chain ← B.heapBufDyn (← B.shifted nItersG 1)
    if odd = 1 then
      pure () -- no use of this definition takes this branch
    else
      B.store chain 0 (← B.const 0)
    B.loopRtF 0 (pure nItersG) 8 (pure ([positions.v, queryWinPtrs.v, cap.v, flags.v, coefs.v, hs.v, chain.v, lamInv.v])) fun xi caps => do
      let positions := cellOf caps 0
      let queryWinPtrs := cellOf caps 1
      let cap := cellOf caps 2
      let flags := cellOf caps 3
      let coefs := cellOf caps 4
      let hs := cellOf caps 5
      let chain := cellOf caps 6
      let lamInv := cellOf caps 7
      if base = 1 then
        pure () -- no use of this definition takes this branch
      else
        let d : E ← openingQuery_6 cap flags coefs hs (← B.load (← B.mul positions xi) 0) (← B.load (← B.mul queryWinPtrs xi) 0) base folds leafCells depth capDepth mu vanish nHs hsBits final
        if final = 0 then
          pure () -- no use of this definition takes this branch
        else
          pure ()
    let mut total : Nat := default
    if final = 0 then
      pure () -- no use of this definition takes this branch
    else
      total := 0
    return [.c (lit total)]

set_option linter.unusedVariables false in
/-- `walk_path`, a `Const` family (`guests/lean_ethereum.py`, line 1301):

```
def walk_path(n0, n1, wins, cap, flags, path_depth: Const, cap_depth: Const):
    # The path, a window of QW levels a dispatch (`decode_query_windows`): each arm knows its
    # levels' order bits, so it hashes the running node against the sibling its hinted pair holds.
    path = StackBuf(LIG_PATH_CAP)
    hint_witness(path[0:4 * path_depth], "merkle_children")
    for i in unroll(0, (path_depth + QW - 1) // QW):
        if const(QW * i + QW == QW * ((path_depth + QW - 1) // QW)):
            width = path_depth - QW * i
        else:
            width = QW
        w = wins[GEN ** i]
        if const(width == 6):
            n0, n1 = match(log(w), range(0, 64), lambda k: walk_window(n0, n1, path, QW * i, 6, k))
        elif const(width == 5):
            n0, n1 = match(log(w), range(0, 32), lambda k: walk_window(n0, n1, path, QW * i, 5, k))
        elif const(width == 4):
            n0, n1 = match(log(w), range(0, 16), lambda k: walk_window(n0, n1, path, QW * i, 4, k))
        elif const(width == 3):
            n0, n1 = match(log(w), range(0, 8), lambda k: walk_window(n0, n1, path, QW * i, 3, k))
        elif const(width == 2):
            n0, n1 = match(log(w), range(0, 4), lambda k: walk_window(n0, n1, path, QW * i, 2, k))
        else:
            n0, n1 = match(log(w), range(0, 2), lambda k: walk_window(n0, n1, path, QW * i, 1, k))
    # The reached cap leaf is node 2*parent + bit at cells 2*node, 2*node + 1, where
    # parent = 2^(cap_depth-1) + q: the child bit and q are the last two windows, g^bit
    # and g^q, the constant parts folded into the address immediates. Every cap is at
    # least two levels deep (`decode_query_windows` gives q cap_depth - 1 bits).
    wb = wins[GEN ** ((path_depth + QW - 1) // QW)]
    q = wins[GEN ** ((path_depth + QW - 1) // QW + 1)]
    flags_q = flags * q
    flags_q[GEN ** (2 ** (cap_depth - 1))] = 1  # the cap check propagates this obligation to the root
    q2 = q * q
    leaf = cap * q2 * q2 * (wb * wb)
    leaf[GEN ** (2 ** (cap_depth + 1))] = n0
    leaf[GEN ** (2 ** (cap_depth + 1) + 1)] = n1
    return
```
-/
def walkPath (pathDepth : Nat) (capDepth : Nat) : GFn where
  name := instName "walk_path" [.L pathDepth, .L capDepth]
  arity := 5
  rets := 0
  body ps := do
    let mut n0 := cellOf ps 0
    let mut n1 := cellOf ps 1
    let wins := cellOf ps 2
    let cap := cellOf ps 3
    let flags := cellOf ps 4
    let path ← B.stackBuf LIG_PATH_CAP
    B.witness "merkle_children" (.stack (path.take (4 * pathDepth)))
    let i_k := 0
    let mut width : Nat := default
    if ((QW * i_k) + QW) = (QW * (((pathDepth + QW) - 1) / QW)) then
      pure () -- no use of this definition takes this branch
    else
      width := QW
    let w ← B.load wins i_k
    if width = 6 then
      let t0 ← B.targets [none, none]
      Keccak.inlineArms
      let _ ← B.matchArms w ((List.range 64).map fun arm => do
        walkWindow n0 n1 path (6 * i_k) 6 arm [(cellOf t0 0).v, (cellOf t0 1).v])
      n0 := cellOf t0 0
      n1 := cellOf t0 1
    else
      pure () -- no use of this definition takes this branch
    let i_k := 1
    if ((QW * i_k) + QW) = (QW * (((pathDepth + QW) - 1) / QW)) then
      width := pathDepth - (QW * i_k)
    else
      pure () -- no use of this definition takes this branch
    let w ← B.load wins i_k
    if width = 6 then
      let t0 ← B.targets [none, none]
      Keccak.inlineArms
      let _ ← B.matchArms w ((List.range 64).map fun arm => do
        walkWindow n0 n1 path (6 * i_k) 6 arm [(cellOf t0 0).v, (cellOf t0 1).v])
      n0 := cellOf t0 0
      n1 := cellOf t0 1
    else
      pure () -- no use of this definition takes this branch
    let wb ← B.load wins (((pathDepth + QW) - 1) / QW)
    let q ← B.load wins ((((pathDepth + QW) - 1) / QW) + 1)
    let flagsQ ← B.mul flags q
    B.store flagsQ (2 ^ (capDepth - 1)) (← B.const 1)
    let q2 ← B.mul q q
    let leaf ← B.mul (← B.mul (← B.mul cap q2) q2) (← B.mul wb wb)
    B.store leaf (2 ^ (capDepth + 1)) n0
    B.store leaf ((2 ^ (capDepth + 1)) + 1) n1
    return []

set_option linter.unusedVariables false in
/-- `walk_path`, a `Const` family (`guests/lean_ethereum.py`, line 1301):

```
def walk_path(n0, n1, wins, cap, flags, path_depth: Const, cap_depth: Const):
    # The path, a window of QW levels a dispatch (`decode_query_windows`): each arm knows its
    # levels' order bits, so it hashes the running node against the sibling its hinted pair holds.
    path = StackBuf(LIG_PATH_CAP)
    hint_witness(path[0:4 * path_depth], "merkle_children")
    for i in unroll(0, (path_depth + QW - 1) // QW):
        if const(QW * i + QW == QW * ((path_depth + QW - 1) // QW)):
            width = path_depth - QW * i
        else:
            width = QW
        w = wins[GEN ** i]
        if const(width == 6):
            n0, n1 = match(log(w), range(0, 64), lambda k: walk_window(n0, n1, path, QW * i, 6, k))
        elif const(width == 5):
            n0, n1 = match(log(w), range(0, 32), lambda k: walk_window(n0, n1, path, QW * i, 5, k))
        elif const(width == 4):
            n0, n1 = match(log(w), range(0, 16), lambda k: walk_window(n0, n1, path, QW * i, 4, k))
        elif const(width == 3):
            n0, n1 = match(log(w), range(0, 8), lambda k: walk_window(n0, n1, path, QW * i, 3, k))
        elif const(width == 2):
            n0, n1 = match(log(w), range(0, 4), lambda k: walk_window(n0, n1, path, QW * i, 2, k))
        else:
            n0, n1 = match(log(w), range(0, 2), lambda k: walk_window(n0, n1, path, QW * i, 1, k))
    # The reached cap leaf is node 2*parent + bit at cells 2*node, 2*node + 1, where
    # parent = 2^(cap_depth-1) + q: the child bit and q are the last two windows, g^bit
    # and g^q, the constant parts folded into the address immediates. Every cap is at
    # least two levels deep (`decode_query_windows` gives q cap_depth - 1 bits).
    wb = wins[GEN ** ((path_depth + QW - 1) // QW)]
    q = wins[GEN ** ((path_depth + QW - 1) // QW + 1)]
    flags_q = flags * q
    flags_q[GEN ** (2 ** (cap_depth - 1))] = 1  # the cap check propagates this obligation to the root
    q2 = q * q
    leaf = cap * q2 * q2 * (wb * wb)
    leaf[GEN ** (2 ** (cap_depth + 1))] = n0
    leaf[GEN ** (2 ** (cap_depth + 1) + 1)] = n1
    return
```
-/
def walkPath_2 (pathDepth : Nat) (capDepth : Nat) : GFn where
  name := instName "walk_path" [.L pathDepth, .L capDepth]
  arity := 5
  rets := 0
  body ps := do
    let mut n0 := cellOf ps 0
    let mut n1 := cellOf ps 1
    let wins := cellOf ps 2
    let cap := cellOf ps 3
    let flags := cellOf ps 4
    let path ← B.stackBuf LIG_PATH_CAP
    B.witness "merkle_children" (.stack (path.take (4 * pathDepth)))
    let i_k := 0
    let mut width : Nat := default
    if ((QW * i_k) + QW) = (QW * (((pathDepth + QW) - 1) / QW)) then
      width := pathDepth - (QW * i_k)
    else
      pure () -- no use of this definition takes this branch
    let w ← B.load wins i_k
    if width = 6 then
      let t0 ← B.targets [none, none]
      Keccak.inlineArms
      let _ ← B.matchArms w ((List.range 64).map fun arm => do
        walkWindow n0 n1 path (6 * i_k) 6 arm [(cellOf t0 0).v, (cellOf t0 1).v])
      n0 := cellOf t0 0
      n1 := cellOf t0 1
    else
      pure () -- no use of this definition takes this branch
    let wb ← B.load wins (((pathDepth + QW) - 1) / QW)
    let q ← B.load wins ((((pathDepth + QW) - 1) / QW) + 1)
    let flagsQ ← B.mul flags q
    B.store flagsQ (2 ^ (capDepth - 1)) (← B.const 1)
    let q2 ← B.mul q q
    let leaf ← B.mul (← B.mul (← B.mul cap q2) q2) (← B.mul wb wb)
    B.store leaf (2 ^ (capDepth + 1)) n0
    B.store leaf ((2 ^ (capDepth + 1)) + 1) n1
    return []

set_option linter.unusedVariables false in
/-- `walk_path`, a `Const` family (`guests/lean_ethereum.py`, line 1301):

```
def walk_path(n0, n1, wins, cap, flags, path_depth: Const, cap_depth: Const):
    # The path, a window of QW levels a dispatch (`decode_query_windows`): each arm knows its
    # levels' order bits, so it hashes the running node against the sibling its hinted pair holds.
    path = StackBuf(LIG_PATH_CAP)
    hint_witness(path[0:4 * path_depth], "merkle_children")
    for i in unroll(0, (path_depth + QW - 1) // QW):
        if const(QW * i + QW == QW * ((path_depth + QW - 1) // QW)):
            width = path_depth - QW * i
        else:
            width = QW
        w = wins[GEN ** i]
        if const(width == 6):
            n0, n1 = match(log(w), range(0, 64), lambda k: walk_window(n0, n1, path, QW * i, 6, k))
        elif const(width == 5):
            n0, n1 = match(log(w), range(0, 32), lambda k: walk_window(n0, n1, path, QW * i, 5, k))
        elif const(width == 4):
            n0, n1 = match(log(w), range(0, 16), lambda k: walk_window(n0, n1, path, QW * i, 4, k))
        elif const(width == 3):
            n0, n1 = match(log(w), range(0, 8), lambda k: walk_window(n0, n1, path, QW * i, 3, k))
        elif const(width == 2):
            n0, n1 = match(log(w), range(0, 4), lambda k: walk_window(n0, n1, path, QW * i, 2, k))
        else:
            n0, n1 = match(log(w), range(0, 2), lambda k: walk_window(n0, n1, path, QW * i, 1, k))
    # The reached cap leaf is node 2*parent + bit at cells 2*node, 2*node + 1, where
    # parent = 2^(cap_depth-1) + q: the child bit and q are the last two windows, g^bit
    # and g^q, the constant parts folded into the address immediates. Every cap is at
    # least two levels deep (`decode_query_windows` gives q cap_depth - 1 bits).
    wb = wins[GEN ** ((path_depth + QW - 1) // QW)]
    q = wins[GEN ** ((path_depth + QW - 1) // QW + 1)]
    flags_q = flags * q
    flags_q[GEN ** (2 ** (cap_depth - 1))] = 1  # the cap check propagates this obligation to the root
    q2 = q * q
    leaf = cap * q2 * q2 * (wb * wb)
    leaf[GEN ** (2 ** (cap_depth + 1))] = n0
    leaf[GEN ** (2 ** (cap_depth + 1) + 1)] = n1
    return
```
-/
def walkPath_3 (pathDepth : Nat) (capDepth : Nat) : GFn where
  name := instName "walk_path" [.L pathDepth, .L capDepth]
  arity := 5
  rets := 0
  body ps := do
    let mut n0 := cellOf ps 0
    let mut n1 := cellOf ps 1
    let wins := cellOf ps 2
    let cap := cellOf ps 3
    let flags := cellOf ps 4
    let path ← B.stackBuf LIG_PATH_CAP
    B.witness "merkle_children" (.stack (path.take (4 * pathDepth)))
    let i_k := 0
    let mut width : Nat := default
    if ((QW * i_k) + QW) = (QW * (((pathDepth + QW) - 1) / QW)) then
      pure () -- no use of this definition takes this branch
    else
      width := QW
    let w ← B.load wins i_k
    if width = 6 then
      let t0 ← B.targets [none, none]
      Keccak.inlineArms
      let _ ← B.matchArms w ((List.range 64).map fun arm => do
        walkWindow n0 n1 path (6 * i_k) 6 arm [(cellOf t0 0).v, (cellOf t0 1).v])
      n0 := cellOf t0 0
      n1 := cellOf t0 1
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:((pathDepth + QW) - 1) / QW] do
      if ((QW * i_k) + QW) = (QW * (((pathDepth + QW) - 1) / QW)) then
        width := pathDepth - (QW * i_k)
      else
        width := QW
      let w ← B.load wins i_k
      if width = 6 then
        let t0 ← B.targets [none, none]
        Keccak.inlineArms
        let _ ← B.matchArms w ((List.range 64).map fun arm => do
          walkWindow n0 n1 path (6 * i_k) 6 arm [(cellOf t0 0).v, (cellOf t0 1).v])
        n0 := cellOf t0 0
        n1 := cellOf t0 1
      else
        pure () -- no use of this definition takes this branch
    let wb ← B.load wins (((pathDepth + QW) - 1) / QW)
    let q ← B.load wins ((((pathDepth + QW) - 1) / QW) + 1)
    let flagsQ ← B.mul flags q
    B.store flagsQ (2 ^ (capDepth - 1)) (← B.const 1)
    let q2 ← B.mul q q
    let leaf ← B.mul (← B.mul (← B.mul cap q2) q2) (← B.mul wb wb)
    B.store leaf (2 ^ (capDepth + 1)) n0
    B.store leaf ((2 ^ (capDepth + 1)) + 1) n1
    return []

end
end LeanVM.Dsl.Gen
