/-
  LeanVM.Dsl.Gen.Inline

  The guest's `@inline` functions, one Lean function per text of their calls that no other merges with.
-/

module

public import LeanVM.Dsl.Gen.Support
public import LeanVM.Dsl.Gen.Config

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

set_option linter.unusedVariables false in
/-- `@inline walk_window` (`guests/lean_ethereum.py`, line 1286):

```
@inline
def walk_window(n0, n1, path, lvl0: Const, width: Const, k: Const):
    # Levels lvl0..lvl0+width of a Merkle path, whose order bits are k's: each hashes the running
    # node with the sibling on the other side of its hinted pair, which binds the link.
    for r in unroll(0, width):
        lvl = lvl0 + r
        nxt = StackBuf(2)
        if const((k // 2 ** r) % 2 == 0):
            keccak([n0, n1], path[4 * lvl + 2:4 * lvl + 4], nxt)
        else:
            keccak(path[4 * lvl:4 * lvl + 2], [n0, n1], nxt)
        n0 = nxt[0]
        n1 = nxt[1]
    return n0, n1
```
-/
def walkWindow (n0 : Word) (n1 : Word) (path : List V) (lvl0 : Nat) (width : Nat) (k : Nat) (dsts : List V) : B (Unit) := B.inline "walk_window" do
  let mut n0 := n0
  let mut n1 := n1
  for r_k in [0:width] do
    let lvl := lvl0 + r_k
    let nxt ← B.stackBuf 2
    if ((k / (2 ^ r_k)) % 2) = 0 then
      B.keccak (a := (.words [.cell n0.v, .cell n1.v])) (b := (.cells (.frame ((path.drop ((4 * lvl) + 2)).take (((4 * lvl) + 4) - ((4 * lvl) + 2)))))) (out := (.frame nxt))
    else
      B.keccak (a := (.cells (.frame ((path.drop (4 * lvl)).take (((4 * lvl) + 2) - (4 * lvl)))))) (b := (.words [.cell n0.v, .cell n1.v])) (out := (.frame nxt))
    n0 := cellOf nxt 0
    n1 := cellOf nxt 1
  B.copy (cellOf dsts 0) n0
  B.copy (cellOf dsts 1) n1

set_option linter.unusedVariables false in
/-- `@inline pack64x2` (`guests/lean_ethereum.py`, line 567):

```
@inline
def pack64x2(a, b):
    assert_in_k(a, b)
    return a + Y_TOWER * b
```
-/
def pack64x2 (a : Word) (b : Word) (dsts : List V) : B (Unit) := B.inline "pack64x2" do
  B.assertInK a b
  Ex.into (cellOf dsts 0) (.add (.w a) (.mul (Ex.nat Y_TOWER) (.w b)))

set_option linter.unusedVariables false in
/-- `@inline novel_eval` (`guests/lean_ethereum.py`, line 1340):

```
@inline
def novel_eval(coefs, ws, n: Const, nbits: Const):
    # sum_(c < n) coefs[c] prod_(i: c_i = 1) ws[i], the novel basis at a point whose
    # What_i normalizers the coefficients already carry: folded the lowest bit first,
    # out[m] = in[2m] + ws[i] in[2m + 1], level i of `buf` at 2^(nbits+1) - 2^(nbits+1-i).
    if const(nbits // 4 == 0):
        buf = StackBuf(16)
    elif const(nbits == 4):
        buf = StackBuf(32)
    elif const(nbits == 5):
        buf = StackBuf(64)
    else:
        buf = StackBuf(128)
    if const(nbits == 0):
        out = coefs[GEN ** 0]
    else:
        for i in unroll(0, nbits):
            n_in = const((n + 2 ** i - 1) // 2 ** i)
            at = const(2 ** (nbits + 1) - 2 ** (nbits + 1 - i))
            for m in unroll(0, (n_in + 1) // 2):
                if const(i == 0):
                    lo = coefs[GEN ** (2 * m)]
                    if const((2 * m + 1) // n_in == 0):
                        hi = coefs[GEN ** (2 * m + 1)]
                else:
                    src = const(2 ** (nbits + 1) - 2 ** (nbits + 2 - i))
                    lo = buf[src + 2 * m]
                    if const((2 * m + 1) // n_in == 0):
                        hi = buf[src + 2 * m + 1]
                if const((2 * m + 1) // n_in == 0):
                    buf[at + m] = lo + ws[i] * hi
                else:
                    buf[at + m] = lo
        out = buf[2 ** (nbits + 1) - 4]
    return out
```
-/
def novelEval (coefs : Word) (ws : List V) (n : Nat) (nbits : Nat) : B (Word) := B.inline "novel_eval" do
  let mut buf : List V := default
  if (nbits / 4) = 0 then
    buf ← B.stackBuf 16
  else
    if nbits = 4 then
      buf ← B.stackBuf 32
    else
      if nbits = 5 then
        buf ← B.stackBuf 64
      else
        buf ← B.stackBuf 128
  let mut out : Word := default
  if nbits = 0 then
    out ← B.load coefs 0
  else
    let mut lo : Word := default
    let mut hi : Word := default
    let mut src : Nat := default
    for i_k in [0:nbits] do
      let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
      let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
      for m_k in [0:(nIn + 1) / 2] do
        if i_k = 0 then
          lo ← B.load coefs (2 * m_k)
          if (((2 * m_k) + 1) / nIn) = 0 then
            hi ← B.load coefs ((2 * m_k) + 1)
          else
            pure ()
        else
          src := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 2) - i_k))
          lo := cellOf buf (src + (2 * m_k))
          if (((2 * m_k) + 1) / nIn) = 0 then
            hi := cellOf buf ((src + (2 * m_k)) + 1)
          else
            pure ()
        if (((2 * m_k) + 1) / nIn) = 0 then
          B.addInto (cellOf buf (at' + m_k)) lo (← B.mul (cellOf ws i_k) hi)
        else
          B.copy (cellOf buf (at' + m_k)) lo
    out := cellOf buf ((2 ^ (nbits + 1)) - 4)
  return out

set_option linter.unusedVariables false in
/-- `@inline opening_query` (`guests/lean_ethereum.py`, line 1377):

```
@inline
def opening_query(cap, flags, coefs, hs, x, wins, base: Const, folds: Const, leaf_cells: Const, depth: Const, cap_depth: Const, mu: Const, vanish: Const, n_hs: Const, hs_bits: Const, final: Const):
    # One query: hash the hinted row up its Merkle path into the shared cap, then fold
    # it at its point x round by round as the prover folded the lanes. A row is one
    # hinted word a lane: a K lane at level 0, whose leaf image lists the lanes from the
    # top down, an E word deeper, which is already the leaf's cell. At a non-final level
    # the fold is returned (its high part's share is taken out in open_stacked's
    # residual pass); at the final level it must be P_final(x).
    interleave = const(2 ** folds)
    if const(folds // 5 == 0):
        row = StackBuf(16)
        acc = StackBuf(16)
    else:
        row = StackBuf(LIG_ROW_CAP)
        acc = StackBuf(LIG_ROW_CAP)
    hint_witness(row[0:interleave], "merkle_leaf_rows")
    leaf_hash_state = StackBuf(2)
    if base == 1:
        # Packing proves each hinted lane is in K before hashing or folding it.
        packed_row = StackBuf(LIG_PACKED_ROW_CAP)
        for jb in unroll(0, interleave // 2):
            packed_row[jb] = pack64x2(row[2 * jb], row[2 * jb + 1])
        keccak_cells(packed_row[0:leaf_cells], leaf_hash_state)
    else:
        keccak_cells(row[0:leaf_cells], leaf_hash_state)
    walk_path(leaf_hash_state[0], leaf_hash_state[1], wins, cap, flags, depth - cap_depth, cap_depth)
    # Round j takes the lane pairs (F, G) to G + t F, t = alpha + beta x.
    for j in unroll(0, folds):
        t = coefs[GEN ** (2 * j)] + coefs[GEN ** (2 * j + 1)] * x
        n_out = const(2 ** (folds - 1 - j))
        for m in unroll(0, n_out):
            if const(j == 0):
                if const(base == 1):
                    acc[m] = row[interleave - 2 - 2 * m] + t * row[interleave - 1 - 2 * m]
                else:
                    acc[m] = row[2 * m + 1] + t * row[2 * m]
            else:
                src = const(interleave - 4 * n_out)
                acc[interleave - 2 * n_out + m] = acc[src + 2 * m + 1] + t * acc[src + 2 * m]
    value = acc[interleave - 2]
    if const(final == 1):
        # The unnormalized W_i(x) for i <= mu, W_(i+1) = W_i (W_i + W_i(beta_i)).
        ws = StackBuf(YR_LOG_CAP + 1)
        ws[0] = x
        for i in unroll(1, mu + 1):
            ws[i] = ws[i - 1] * (ws[i - 1] + VANISH_BY_COLS[vanish + i - 1])
        assert value == novel_eval(hs, ws, n_hs, hs_bits)
        out = 0
    else:
        out = value
    return out
```
-/
def openingQuery (cap : Word) (flags : Word) (coefs : Word) (hs : Word) (x : Word) (wins : Word) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : B (FW) := B.inline "opening_query" do
  let interleave := 2 ^ folds
  let mut row : List V := default
  let mut acc : List V := default
  if (folds / 5) = 0 then
    row ← B.stackBuf 16
    acc ← B.stackBuf 16
  else
    row ← B.stackBuf LIG_ROW_CAP
    acc ← B.stackBuf LIG_ROW_CAP
  B.witness "merkle_leaf_rows" (.stack (row.take interleave))
  let leafHashState ← B.stackBuf 2
  if base = 1 then
    let packedRow ← B.stackBuf LIG_PACKED_ROW_CAP
    for jb_k in [0:interleave / 2] do
      pack64x2 (cellOf row (2 * jb_k)) (cellOf row ((2 * jb_k) + 1)) [(cellOf packedRow jb_k).v]
    B.keccakCells (cells := (.cells (.frame (packedRow.take leafCells)))) (out := (.frame leafHashState))
  else
    B.keccakCells (cells := (.cells (.frame (row.take leafCells)))) (out := (.frame leafHashState))
  let _ ← B.call (instName "walk_path" [.L (depth - capDepth), .L capDepth]) [(cellOf leafHashState 0).v, (cellOf leafHashState 1).v, wins.v, cap.v, flags.v] 0
  let mut src : Nat := default
  for j_k in [0:folds] do
    let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
    let nOut := 2 ^ ((folds - 1) - j_k)
    for m_k in [0:nOut] do
      if j_k = 0 then
        if base = 1 then
          B.addInto (cellOf acc m_k) (cellOf row ((interleave - 2) - (2 * m_k))) (← B.mul t (cellOf row ((interleave - 1) - (2 * m_k))))
        else
          B.addInto (cellOf acc m_k) (cellOf row ((2 * m_k) + 1)) (← B.mul t (cellOf row (2 * m_k)))
      else
        src := interleave - (4 * nOut)
        B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let value := cellOf acc (interleave - 2)
  let mut out : FW := default
  if final = 1 then
    let ws ← B.stackBuf 6
    B.copy (cellOf ws 0) x
    for i_k in [1:mu + 1] do
      Ex.into (cellOf ws i_k) (.mul (.v (cellOf ws (i_k - 1))) (.add (.v (cellOf ws (i_k - 1))) (.c (arrWord VANISH_BY_COLS ((vanish + i_k) - 1)))))
    let t0 ← novelEval hs ws nHs hsBits
    B.assertEq value t0
    out := FW.c (lit 0)
  else
    out := FW.w value
  return out

set_option linter.unusedVariables false in
/-- `@inline assert_window` (`guests/lean_ethereum.py`, line 795):

```
@inline
def assert_window(w, width: Const):
    # log(w) < 2^width, the bound spelled out per width (a range check takes a literal bound).
    if const(width == 1):
        assert log(w) < 2
    elif const(width == 2):
        assert log(w) < 4
    elif const(width == 3):
        assert log(w) < 8
    elif const(width == 4):
        assert log(w) < 16
    elif const(width == 5):
        assert log(w) < 32
    elif const(width == 6):
        assert log(w) < 64
    elif const(width == 7):
        assert log(w) < 128
    elif const(width == 8):
        assert log(w) < 256
    elif const(width == 9):
        assert log(w) < 512
    elif const(width == 10):
        assert log(w) < 1024
    elif const(width == 11):
        assert log(w) < 2048
    else:
        assert 0 == 1  # no window is wider than the window table covers
    return
```
-/
def assertWindow (w : Word) (width : Nat) : B (Unit) := B.inline "assert_window" do
  if width = 1 then
    let _ ← B.rangeCheck w 2
    pure ()
  else
    if width = 2 then
      let _ ← B.rangeCheck w 4
      pure ()
    else
      if width = 3 then
        let _ ← B.rangeCheck w 8
        pure ()
      else
        if width = 4 then
          let _ ← B.rangeCheck w 16
          pure ()
        else
          if width = 5 then
            let _ ← B.rangeCheck w 32
            pure ()
          else
            if width = 6 then
              let _ ← B.rangeCheck w 64
              pure ()
            else
              if width = 7 then
                let _ ← B.rangeCheck w 128
                pure ()
              else
                if width = 8 then
                  let _ ← B.rangeCheck w 256
                  pure ()
                else
                  if width = 9 then
                    let _ ← B.rangeCheck w 512
                    pure ()
                  else
                    if width = 10 then
                      let _ ← B.rangeCheck w 1024
                      pure ()
                    else
                      if width = 11 then
                        let _ ← B.rangeCheck w 2048
                        pure ()
                      else
                        B.assertEq (← B.const 0) (← B.const 1)

set_option linter.unusedVariables false in
/-- `@inline query_window_split` (`guests/lean_ethereum.py`, line 835):

```
@inline
def query_window_split(word, wins, tabs, parts, at: Const, start: Const, width: Const, cut: Const):
    # A window whose bits cross a limb boundary `cut` bits in: its two runs hinted and range checked apart,
    # each read as its bit pattern into parts[0], parts[1], and joined in the exponent into wins[at].
    hint_windows_exponent(parts, word, start, cut, 1, 2)
    hint_windows_exponent(parts, word, start + cut, width - cut, 1, 3)
    lo = parts[2]
    hi = parts[3]
    assert_window(lo, cut)
    assert_window(hi, width - cut)
    hp = hi
    for s in unroll(0, cut):
        hp = hp * hp
    wins[at] = lo * hp
    parts[0] = tabs[lo]
    parts[1] = tabs[hi]
    return
```
-/
def queryWindowSplit (word' : Word) (wins : List V) (tabs : Word) (parts : List V) (at' : Nat) (start : Nat) (width : Nat) (cut : Nat) : B (Unit) := B.inline "query_window_split" do
  B.hintWindowsExp (.stack (parts.take (2 + 1))) word' start cut 1 2
  B.hintWindowsExp (.stack (parts.take (3 + 1))) word' (start + cut) (width - cut) 1 3
  let lo := cellOf parts 2
  let hi := cellOf parts 3
  assertWindow lo cut
  assertWindow hi (width - cut)
  let mut hp := hi
  for _ in [0:cut] do
    hp ← B.mul hp hp
  B.mulInto (cellOf wins at') lo hp
  B.loadInto (cellOf parts 0) (← B.mul tabs lo) 0
  B.loadInto (cellOf parts 1) (← B.mul tabs hi) 0

set_option linter.unusedVariables false in
/-- `@inline query_window` (`guests/lean_ethereum.py`, line 825):

```
@inline
def query_window(word, wins, tabs, at: Const, start: Const, width: Const):
    # Bits start..start+width of `word` into wins[at] as g^n, n the integer they spell, range checked below
    # 2^width. Returns n's bit pattern, `tabs[g^n]` (`query_tables`).
    hint_windows_exponent(wins, word, start, width, 1, at)
    w = wins[at]
    assert_window(w, width)
    return tabs[w]
```
-/
def queryWindow (word' : Word) (wins : List V) (tabs : Word) (at' : Nat) (start : Nat) (width : Nat) : B (Word) := B.inline "query_window" do
  B.hintWindowsExp (.stack (wins.take (at' + 1))) word' start width 1 at'
  let w := cellOf wins at'
  assertWindow w width
  let t0 ← B.load (← B.mul tabs w) 0
  return t0

set_option linter.unusedVariables false in
/-- `@inline residual_query` (`guests/lean_ethereum.py`, line 1462):

```
@inline
def residual_query(basis_chain, row_d, hs, n_cols: Const, n_hs: Const, hs_bits: Const):
    # prod_t (d_t + chain_t) over one query's message-column coordinates, chain_t =
    # W_t(x), x the query position; then the high part's share of the query's fold,
    # What_mu(x) sum_j p_(2^mu + j) X_j(x), its normalizers in hs.
    ws = StackBuf(HIGH_BITS_CAP)
    ws[0] = basis_chain
    prefix_eq = row_d[GEN ** 0] + basis_chain
    for t in unroll(1, n_cols + 1):
        # subspace-vanishing recurrence for the novel-basis point, a function of n_cols alone
        if const(t // HIGH_BITS_CAP == 0):
            ws[t] = basis_chain * (basis_chain + VANISH_BY_COLS[n_cols * (n_cols + 1) // 2 + t - 1])
            basis_chain = ws[t]
        else:
            basis_chain *= basis_chain + VANISH_BY_COLS[n_cols * (n_cols + 1) // 2 + t - 1]
        if const(t != n_cols):
            prefix_eq *= row_d[GEN ** t] + basis_chain
    return prefix_eq, basis_chain * novel_eval(hs, ws, n_hs, hs_bits)
```
-/
def residualQuery (basisChain : Word) (rowD : Word) (hs : Word) (nCols : Nat) (nHs : Nat) (hsBits : Nat) : B (Word × Word) := B.inline "residual_query" do
  let ws ← B.stackBuf HIGH_BITS_CAP
  B.copy (cellOf ws 0) basisChain
  let mut prefixEq ← B.add (← B.load rowD 0) basisChain
  let mut basisChain := basisChain
  for t_k in [1:nCols + 1] do
    if (t_k / HIGH_BITS_CAP) = 0 then
      Ex.into (cellOf ws t_k) (.mul (.w basisChain) (.add (.w basisChain) (.c (arrWord VANISH_BY_COLS ((((nCols * (nCols + 1)) / 2) + t_k) - 1)))))
      basisChain := cellOf ws t_k
    else
      basisChain ← Ex.lower (.mul (.w basisChain) (.add (.w basisChain) (.c (arrWord VANISH_BY_COLS ((((nCols * (nCols + 1)) / 2) + t_k) - 1)))))
    if t_k ≠ nCols then
      prefixEq ← B.mul prefixEq (← B.add (← B.load rowD t_k) basisChain)
    else
      pure ()
  let t0 ← novelEval hs ws nHs hsBits
  let t1 ← B.mul basisChain t0
  return (prefixEq, t1)

set_option linter.unusedVariables false in
/-- `@inline carry_step` (`guests/lean_ethereum.py`, line 2739):

```
@inline
def carry_step(c0, c1, n0, n1, e_t, u_t, v_t, t: Const):
    # Extend every t-bit prefix p of r by bit t of r, to p and p + 2^t: c0[p], c1[p]
    # weigh the carry 0 and 1 into bit t, and e_t, u_t, v_t are bit t's weights for
    # (x, y) equal, (1, 0) and (0, 1). The zero prefix never carries.
    for p in unroll(0, 2 ** t):
        if p == 0:
            n0[0] = c0[0] * e_t
            n0[2 ** t] = c0[0] * u_t
            n1[2 ** t] = c0[0] * v_t
        else:
            n0[p] = c0[p] * e_t + c1[p] * u_t
            n1[p] = c1[p] * v_t
            n0[p + 2 ** t] = c0[p] * u_t
            n1[p + 2 ** t] = c0[p] * v_t + c1[p] * e_t
    return
```
-/
def carryStep (c0 : List V) (c1 : List V) (n0 : List V) (n1 : List V) (eT : Word) (uT : Word) (vT : Word) (t : Nat) : B (Unit) := B.inline "carry_step" do
  for p_k in [0:2 ^ t] do
    if p_k = 0 then
      B.mulInto (cellOf n0 0) (cellOf c0 0) eT
      B.mulInto (cellOf n0 (2 ^ t)) (cellOf c0 0) uT
      B.mulInto (cellOf n1 (2 ^ t)) (cellOf c0 0) vT
    else
      B.addInto (cellOf n0 p_k) (← B.mul (cellOf c0 p_k) eT) (← B.mul (cellOf c1 p_k) uT)
      B.mulInto (cellOf n1 p_k) (cellOf c1 p_k) vT
      B.mulInto (cellOf n0 (p_k + (2 ^ t))) (cellOf c0 p_k) uT
      B.addInto (cellOf n1 (p_k + (2 ^ t))) (← B.mul (cellOf c0 p_k) vT) (← B.mul (cellOf c1 p_k) eT)

set_option linter.unusedVariables false in
/-- `@inline carry_wrap` (`guests/lean_ethereum.py`, line 2757):

```
@inline
def carry_wrap(c0, c1, out, e_t, s_t, t: Const):
    # carry_step's last bit, the carry out dropped: u_t + v_t = s_t weighs it either way.
    for p in unroll(0, 2 ** t):
        if p == 0:
            out[0] = c0[0] * e_t
            out[2 ** t] = c0[0] * s_t
        else:
            out[p] = c0[p] * e_t + c1[p] * s_t
            out[p + 2 ** t] = c0[p] * s_t + c1[p] * e_t
    return
```
-/
def carryWrap (c0 : List V) (c1 : List V) (out : List V) (eT : Word) (sT : Word) (t : Nat) : B (Unit) := B.inline "carry_wrap" do
  for p_k in [0:2 ^ t] do
    if p_k = 0 then
      B.mulInto (cellOf out 0) (cellOf c0 0) eT
      B.mulInto (cellOf out (2 ^ t)) (cellOf c0 0) sT
    else
      B.addInto (cellOf out p_k) (← B.mul (cellOf c0 p_k) eT) (← B.mul (cellOf c1 p_k) sT)
      B.addInto (cellOf out (p_k + (2 ^ t))) (← B.mul (cellOf c0 p_k) sT) (← B.mul (cellOf c1 p_k) eT)

set_option linter.unusedVariables false in
/-- `@inline keccak_shifts_eq` (`guests/lean_ethereum.py`, line 2770):

```
@inline
def keccak_shifts_eq(a, b, shifts):
    # shifts[r] for every used r: the multilinear extension of "x = y + r mod 64" at
    # (a, b), a ripple of the carry over the six bits. Split r = rl + 8 rh: the low
    # three bits leave a carry c into the high three, which then add rh + c, so
    # shifts[r] = L0[rl] H[rh] + L1[rl] H[rh + 1] over tables of eight.
    w_eq = StackBuf(KECCAK_Z_BITS)
    w_sum = StackBuf(KECCAK_Z_BITS)
    w_up = StackBuf(KECCAK_Z_BITS)
    w_down = StackBuf(KECCAK_Z_BITS)
    # Bits 0 and 3 start the two tables: their weights are the first level itself.
    lo0 = StackBuf(2)
    lo1 = StackBuf(2)
    hi0 = StackBuf(2)
    hi1 = StackBuf(2)
    # As products, (1 + a)(1 + b) + ab, a(1 + b) and (1 + a)b, trading XORs for MULs;
    # b's 1 + b_t is the local sumcheck's, already in the frame.
    for t in unroll(0, KECCAK_Z_BITS):
        a_t = a[GEN ** t]
        b_t = b[GEN ** t]
        a_t1 = 1 + a_t
        b_t1 = 1 + b_t
        if t == 0:
            lo0[0] = a_t1 * b_t1 + a_t * b_t
            lo0[1] = a_t * b_t1
            lo1[1] = a_t1 * b_t
        elif t == 3:
            hi0[0] = a_t1 * b_t1 + a_t * b_t
            hi0[1] = a_t * b_t1
            hi1[1] = a_t1 * b_t
        elif const(t + 1 == KECCAK_Z_BITS):
            w_eq[t] = a_t1 * b_t1 + a_t * b_t
            w_sum[t] = a_t + b_t
        else:
            w_eq[t] = a_t1 * b_t1 + a_t * b_t
            w_up[t] = a_t * b_t1
            w_down[t] = a_t1 * b_t
    mid0 = StackBuf(4)
    mid1 = StackBuf(4)
    carry_step(lo0, lo1, mid0, mid1, w_eq[1], w_up[1], w_down[1], 1)
    low0 = StackBuf(8)
    low1 = StackBuf(8)
    carry_step(mid0, mid1, low0, low1, w_eq[2], w_up[2], w_down[2], 2)
    hmid0 = StackBuf(4)
    hmid1 = StackBuf(4)
    carry_step(hi0, hi1, hmid0, hmid1, w_eq[4], w_up[4], w_down[4], 1)
    high = StackBuf(8)
    carry_wrap(hmid0, hmid1, high, w_eq[5], w_sum[5], 2)
    for r in unroll(0, 64):
        if KECCAK_SHIFT_USED[r] == 1:
            if r % 8 == 0:
                shifts[r] = low0[0] * high[r // 8]
            else:
                shifts[r] = low0[r % 8] * high[r // 8] + low1[r % 8] * high[(r // 8 + 1) % 8]
    return
```
-/
def keccakShiftsEq (a : Word) (b : Word) (shifts : List V) : B (Unit) := B.inline "keccak_shifts_eq" do
  let wEq ← B.stackBuf KECCAK_Z_BITS
  let wSum ← B.stackBuf KECCAK_Z_BITS
  let wUp ← B.stackBuf KECCAK_Z_BITS
  let wDown ← B.stackBuf KECCAK_Z_BITS
  let lo0 ← B.stackBuf 2
  let lo1 ← B.stackBuf 2
  let hi0 ← B.stackBuf 2
  let hi1 ← B.stackBuf 2
  for t_k in [0:KECCAK_Z_BITS] do
    let aT ← B.load a t_k
    let bT ← B.load b t_k
    let aT1 ← Ex.lower (.add (Ex.nat 1) (.w aT))
    let bT1 ← Ex.lower (.add (Ex.nat 1) (.w bT))
    if t_k = 0 then
      B.addInto (cellOf lo0 0) (← B.mul aT1 bT1) (← B.mul aT bT)
      B.mulInto (cellOf lo0 1) aT bT1
      B.mulInto (cellOf lo1 1) aT1 bT
    else
      if t_k = 3 then
        B.addInto (cellOf hi0 0) (← B.mul aT1 bT1) (← B.mul aT bT)
        B.mulInto (cellOf hi0 1) aT bT1
        B.mulInto (cellOf hi1 1) aT1 bT
      else
        if (t_k + 1) = KECCAK_Z_BITS then
          B.addInto (cellOf wEq t_k) (← B.mul aT1 bT1) (← B.mul aT bT)
          B.addInto (cellOf wSum t_k) aT bT
        else
          B.addInto (cellOf wEq t_k) (← B.mul aT1 bT1) (← B.mul aT bT)
          B.mulInto (cellOf wUp t_k) aT bT1
          B.mulInto (cellOf wDown t_k) aT1 bT
  let mid0 ← B.stackBuf 4
  let mid1 ← B.stackBuf 4
  carryStep lo0 lo1 mid0 mid1 (cellOf wEq 1) (cellOf wUp 1) (cellOf wDown 1) 1
  let low0 ← B.stackBuf 8
  let low1 ← B.stackBuf 8
  carryStep mid0 mid1 low0 low1 (cellOf wEq 2) (cellOf wUp 2) (cellOf wDown 2) 2
  let hmid0 ← B.stackBuf 4
  let hmid1 ← B.stackBuf 4
  carryStep hi0 hi1 hmid0 hmid1 (cellOf wEq 4) (cellOf wUp 4) (cellOf wDown 4) 1
  let high ← B.stackBuf 8
  carryWrap hmid0 hmid1 high (cellOf wEq 5) (cellOf wSum 5) 2
  for r_k in [0:64] do
    if (arrInt KECCAK_SHIFT_USED r_k) = 1 then
      if (r_k % 8) = 0 then
        B.mulInto (cellOf shifts r_k) (cellOf low0 0) (cellOf high (r_k / 8))
      else
        B.addInto (cellOf shifts r_k) (← B.mul (cellOf low0 (r_k % 8)) (cellOf high (r_k / 8))) (← B.mul (cellOf low1 (r_k % 8)) (cellOf high (((r_k / 8) + 1) % 8)))
    else
      pure ()

set_option linter.unusedVariables false in
/-- `@inline slice_weight` (`guests/lean_ethereum.py`, line 2885):

```
@inline
def slice_weight(slices, top, top1, z: Const):
    # eq(local, z) from the five-coordinate tree `slices` and the top coordinate.
    if const(z // 32 == 1):
        w = slices[2 ** (KECCAK_Z_BITS - 1) - 2 + z % 32] * top
    else:
        w = slices[2 ** (KECCAK_Z_BITS - 1) - 2 + z % 32] * top1
    return w
```
-/
def sliceWeight (slices : List V) (top : Word) (top1 : Word) (z : Nat) : B (Word) := B.inline "slice_weight" do
  let mut w : Word := default
  if (z / 32) = 1 then
    w ← B.mul (cellOf slices (((2 ^ (KECCAK_Z_BITS - 1)) - 2) + (z % 32))) top
  else
    w ← B.mul (cellOf slices (((2 ^ (KECCAK_Z_BITS - 1)) - 2) + (z % 32))) top1
  return w

set_option linter.unusedVariables false in
/-- `@inline assert_digit` (`guests/lean_ethereum.py`, line 2167):

```
@inline
def assert_digit(d, width: Const):
    # d = g^u with u < 2^width: three cycles, no XOR.
    if const(width == 1):
        assert log(d) < 2
    if const(width == 2):
        assert log(d) < 4
    if const(width == 3):
        assert log(d) < 8
    if const(width == 4):
        assert log(d) < 16
    return
```
-/
def assertDigit (d : Word) (width : Nat) : B (Unit) := B.inline "assert_digit" do
  if width = 1 then
    let _ ← B.rangeCheck d 2
    pure ()
  else
    pure ()
  if width = 2 then
    let _ ← B.rangeCheck d 4
    pure ()
  else
    pure ()
  if width = 3 then
    let _ ← B.rangeCheck d 8
    pure ()
  else
    pure ()
  if width = 4 then
    let _ ← B.rangeCheck d 16
    pure ()
  else
    pure ()

set_option linter.unusedVariables false in
/-- `@inline fs_perm_pending` (`guests/lean_ethereum.py`, line 659):

```
@inline
def fs_perm_pending(cap, rec, at: Const):
    # The permutation taking a full rate held in the record cells at..at+8.
    nxt = StackBuf(KECCAK_STATE)
    keccak([rec[GEN ** at], rec[GEN ** (at + 1)]], [rec[GEN ** (at + 2)], rec[GEN ** (at + 3)]], nxt, tail=[rec[GEN ** (at + 4)], rec[GEN ** (at + 5)], rec[GEN ** (at + 6)], rec[GEN ** (at + 7)]], cap=cap)
    return nxt
```
-/
def fsPermPending (cap : List V) (rec' : Word) (at' : Nat) : B (List V) := B.inline "fs_perm_pending" do
  let nxt ← B.stackBuf KECCAK_STATE
  B.keccakDuplex (a := (.words [.cell (← B.load rec' at').v, .cell (← B.load rec' (at' + 1)).v])) (b := (.words [.cell (← B.load rec' (at' + 2)).v, .cell (← B.load rec' (at' + 3)).v])) (tail := some (.words [.cell (← B.load rec' (at' + 4)).v, .cell (← B.load rec' (at' + 5)).v, .cell (← B.load rec' (at' + 6)).v, .cell (← B.load rec' (at' + 7)).v])) (cap := (.frame cap)) (out := (.frame nxt))
  return nxt

set_option linter.unusedVariables false in
/-- `@inline walk` (`guests/lean_ethereum.py`, line 3770):

```
@inline
def walk(at, pp, walks, tags, powers, i: Const, k: Const, lx: Const):
    # Walk chain i from position k to its end, the step leaving position s landing in
    # chain i's slot s of `walks`, so the tip is chain_tip(walks, i) whatever k is. A
    # leanSPHINCS step's address is at[0] and at[1] with i and s added, the value last;
    # a leanXMSS one carries only s, at[s] computed once per key, i riding after the
    # value, read off a cell set outside the dispatch (the zero cell, `powers` or
    # `tags`), so an arm names it rather than setting it again.
    if const(lx == 1):
        if const(i == 0):
            tag = 0
        elif const(LX_TAG_SLOT[i] == 0):
            tag = powers[LX_TAG_LOG[i]]
        else:
            tag = tags[LX_TAG_SLOT[i] - 1]
    if const(k == CHAIN_STEPS):
        hint_witness(walks[(i + 1) * CHAIN_STEPS - 1:(i + 1) * CHAIN_STEPS], "chain_starts")
    else:
        value = hint_witness("chain_starts")
        for s in unroll(k, CHAIN_STEPS):
            o = CHAIN_STEPS * i + s
            if const(lx == 1):
                keccak([pp, at[s]], [value, tag], walks[o:o + 1])
            else:
                keccak([pp, at[0]], [at[1] + const(i * SP_WORD2_MUL + s * SP_WORD3_MUL_0), value], walks[o:o + 1])
            value = walks[o]
    return
```
-/
def walk (at' : List V) (pp : Word) (walks : List V) (tags : List V) (powers : List V) (i : Nat) (k : Nat) (lx : Nat) : B (Unit) := B.inline "walk" do
  let mut tag : FW := default
  if lx = 1 then
    if i = 0 then
      tag := FW.c (lit 0)
    else
      if (arrInt LX_TAG_SLOT i) = 0 then
        tag := FW.w (cellOf powers (arrInt LX_TAG_LOG i))
      else
        tag := FW.w (cellOf tags ((arrInt LX_TAG_SLOT i) - 1))
  else
    pure ()
  if k = CHAIN_STEPS then
    B.witness "chain_starts" (.stack ((walks.drop (((i + 1) * CHAIN_STEPS) - 1)).take (((i + 1) * CHAIN_STEPS) - (((i + 1) * CHAIN_STEPS) - 1))))
  else
    let mut value ← hinted (B.witnessCell "chain_starts")
    for s_k in [k:CHAIN_STEPS] do
      let o := (CHAIN_STEPS * i) + s_k
      if lx = 1 then
        B.keccak (a := (.words [.cell pp.v, .cell (cellOf at' s_k).v])) (b := (.words [.cell value.v, (← tag.msg)])) (out := (.frame ((walks.drop o).take ((o + 1) - o))))
      else
        B.keccak (a := (.words [.cell pp.v, .cell (cellOf at' 0).v])) (b := (.words [.cell (← Ex.lower (.add (.v (cellOf at' 1)) (.c (lit ((i * SP_WORD2_MUL) + (s_k * SP_WORD3_MUL_0)))))).v, .cell value.v])) (out := (.frame ((walks.drop o).take ((o + 1) - o))))
      value := cellOf walks o

set_option linter.unusedVariables false in
/-- `@inline child_claims_mono` (`guests/lean_ethereum.py`, line 4455):

```
@inline
def child_claims_mono(cov, ent, mark, blk, out, n: Const):
    # n of a child's claims at strictly increasing offsets into THIS node's table: each
    # hinted gap g^e, e >= 0 by the DEREF through it, moves the offset on by e + 1.
    # cov and ent are the coverage slot and the table entry the next claim takes at
    # gap zero; out receives them for the claim after the last. Every claim of the list
    # writes the same mark, its first count: the walk cannot revisit a slot, and any
    # other writer's value differs, so a slot written twice still conflicts.
    for j in unroll(0, n):
        gap = hint_witness("child_claim_gap")
        assert_gpow(gap)
        cov = cov * gap
        gap2 = gap * gap
        ent = ent * (gap2 * gap2)
        cov[GEN ** j] = mark
        for c in unroll(0, 4):
            blk[4 * j + c] = ent[GEN ** (4 * j + c)]
    out[0] = cov * GEN ** n
    out[1] = ent * GEN ** (4 * n)
    return
```
-/
def childClaimsMono (cov : Word) (ent : Word) (mark : Word) (blk : List V) (out : List V) (n : Nat) : B (Unit) := B.inline "child_claims_mono" do
  let mut cov := cov
  let mut ent := ent
  for j_k in [0:n] do
    let gap ← hinted (B.witnessCell "child_claim_gap")
    let _ ← B.assertGpow gap
    cov ← B.mul cov gap
    let gap2 ← B.mul gap gap
    ent ← B.mul ent (← B.mul gap2 gap2)
    B.store cov j_k mark
    for c_k in [0:4] do
      B.loadInto (cellOf blk ((4 * j_k) + c_k)) ent ((4 * j_k) + c_k)
  Ex.into (cellOf out 0) (.mul (.w cov) (.g n))
  Ex.into (cellOf out 1) (.mul (.w ent) (.g (4 * n)))

set_option linter.unusedVariables false in
/-- `@inline child_claims` (`guests/lean_ethereum.py`, line 4391):

```
@inline
def child_claims(entries_ptr, region, marks, last_g, blk, n: Const):
    # n of a child's claims, each read at a hinted index into THIS node's table and
    # marked in the coverage table. The index is an offset into the scheme's region
    # (`region`, the coverage table from the scheme's origin) and bounded by that
    # region's size, last_g * GEN, so a child's claim can only ever land on a slot of
    # its own scheme. The bound so written is its own range-check target, last_g.
    for j in unroll(0, n):
        off_hint = hint_witness("child_claim_index")
        assert log(off_hint) < log(last_g * GEN)  # precondition as in the raw loops
        region[off_hint] = marks * (GEN ** j)
        entry = entries_ptr * (off_hint ** 4)
        for c in unroll(0, 4):
            blk[4 * j + c] = entry[GEN ** c]
    return
```
-/
def childClaims (entriesPtr : Word) (region : Word) (marks : Word) (lastG : Word) (blk : List V) (n : Nat) : B (Unit) := B.inline "child_claims" do
  for j_k in [0:n] do
    let offHint ← hinted (B.witnessCell "child_claim_index")
    let t0 ← B.shifted lastG (1 - 1)
    let _ ← B.rangeCheckK offHint t0
    let t1 ← Ex.lower (.mul (.w marks) (.g j_k))
    B.store (← B.mul region offHint) 0 t1
    let entry ← Ex.lower (.mul (.w entriesPtr) (.pow (.w offHint) 4))
    for c_k in [0:4] do
      B.loadInto (cellOf blk ((4 * j_k) + c_k)) entry c_k

set_option linter.unusedVariables false in
/-- `@inline zero_state` (`guests/lean_ethereum.py`, line 4321):

```
@inline
def zero_state(chain):
    for k in unroll(0, KECCAK_STATE):
        chain[GEN ** k] = 0
    return
```
-/
def zeroState (chain : Word) : B (Unit) := B.inline "zero_state" do
  for k_k in [0:KECCAK_STATE] do
    B.store chain k_k (← B.const 0)

set_option linter.unusedVariables false in
/-- `@inline sp_from_bytes` (`guests/lean_ethereum.py`, line 3960):

```
@inline
def sp_from_bytes(byte_bits, marks, n: Const):
    # The integer whose n bytes, low first, are hinted in the exponent at marks[k]: each
    # range checked and read off `byte_bits` as the bits it spells.
    for t in unroll(0, n):
        k = n - 1 - t
        assert log(marks[k]) < SP_BYTE_VALUES
        if const(t == 0):
            value = byte_bits[marks[k]]
        else:
            value = byte_bits[marks[k]] + value * GEN ** 8
    return value
```
-/
def spFromBytes (byteBits : Word) (marks : List V) (n : Nat) : B (Word) := B.inline "sp_from_bytes" do
  let mut value : Word := default
  for t_k in [0:n] do
    let k := (n - 1) - t_k
    let _ ← B.rangeCheck (cellOf marks k) SP_BYTE_VALUES
    if t_k = 0 then
      value ← B.load (← B.mul byteBits (cellOf marks k)) 0
    else
      value ← Ex.lower (.add (.ld (B.mul byteBits (cellOf marks k)) 0) (.mul (.w value) (.g 8)))
  return value

set_option linter.unusedVariables false in
/-- `@inline sp_leaf_bit` (`guests/lean_ethereum.py`, line 4015):

```
@inline
def sp_leaf_bit(bits1, bits2, b: Const):
    # Bit b of the three layers' leaves one after the other, bottom first, which the
    # digest's last four bytes hold: the bottom leaf the last byte (the second call's
    # byte 1), the middle one the byte before (its byte 0), and the top one the tree
    # index's high bits (the first call's byte 31, then the low two bits of 30).
    x = bits2[(b + SP_MID) % (8 * SP_TAIL_BYTES)]
    if const(b // 8 == SP_TOP // 8):
        x = bits1[b - SP_TOP + SP_TREE_MID_BIT]
    if const(b // 8 == SP_TOP // 8 + 1):
        x = bits1[b - SP_TOP - 8 + SP_TREE_HI_BIT]
    return x
```
-/
def spLeafBit (bits1 : List V) (bits2 : List V) (b : Nat) : B (Word) := B.inline "sp_leaf_bit" do
  let mut x := cellOf bits2 ((b + 8) % (8 * SP_TAIL_BYTES))
  if (b / 8) = (SP_TOP / 8) then
    x := cellOf bits1 ((b - SP_TOP) + SP_TREE_MID_BIT)
  else
    pure ()
  if (b / 8) = ((SP_TOP / 8) + 1) then
    x := cellOf bits1 (((b - SP_TOP) - 8) + SP_TREE_HI_BIT)
  else
    pure ()
  return x

set_option linter.unusedVariables false in
/-- `@inline is_child` (`guests/lean_ethereum.py`, line 3751):

```
@inline
def is_child(node, kids, k: Const, bit):
    # A node is not ordered against its sibling: the two children are hinted in
    # order, at kids[k] and kids[k + 1], and `node` is checked to be the one `bit`
    # names, the left one at 0, the right one at 1. One product, stored where the
    # left child's difference already is, which is the assert.
    check = StackBuf(1)
    check[0] = node + kids[k]
    check[0] = bit * (kids[k] + kids[k + 1])
    return
```
-/
def isChild (node : Word) (kids : List V) (k : Nat) (bit : Word) : B (Unit) := B.inline "is_child" do
  let check ← B.stackBuf 1
  B.addInto (cellOf check 0) node (cellOf kids k)
  B.mulInto (cellOf check 0) bit (← B.add (cellOf kids k) (cellOf kids (k + 1)))

set_option linter.unusedVariables false in
/-- `@inline sp_be16` (`guests/lean_ethereum.py`, line 4039):

```
@inline
def sp_be16(vals, at: Const, n: Const):
    # The n-bit value vals[at] as the last two bytes of an A1 word, big endian: its low
    # byte masked and placed last, its high bits before it.
    if const((n + 7) // 8 == 2):
        v = vals[at] * const(SP_WORD3_MUL_0) + vals[at + 8] * (GEN ** 8 * const(SP_WORD3_MUL_0) + const(SP_WORD3_MUL_1))
    else:
        v = vals[at] * const(SP_WORD3_MUL_0)
    return v
```
-/
def spBe16 (vals : List V) (at' : Nat) (n : Nat) : B (Word) := B.inline "sp_be16" do
  let mut v : Word := default
  if ((n + 7) / 8) = 2 then
    v ← Ex.lower (.add (.mul (.v (cellOf vals at')) (.c (lit SP_WORD3_MUL_0))) (.mul (.v (cellOf vals (at' + 8))) (.add (.mul (.g 8) (.c (lit SP_WORD3_MUL_0))) (.c (lit SP_WORD3_MUL_1)))))
  else
    v ← Ex.lower (.mul (.v (cellOf vals at')) (.c (lit SP_WORD3_MUL_0)))
  return v

set_option linter.unusedVariables false in
/-- `@inline sp_path` (`guests/lean_ethereum.py`, line 4142):

```
@inline
def sp_path(node, pp, a0, bits1, bits2, lvals, out, off: Const, height: Const):
    # The path from `node` up the tree whose address is a0, the leaf's bits from leaf bit
    # `off` and its ancestors' indices in lvals, the two children of each node hinted in
    # order, the root into out.
    cur = node
    for z in unroll(0, height):
        # The two children, then three cells the compiler pads (as in sp_fors_tree).
        kids = StackBuf(5)
        hint_witness(kids[0:2], "siblings")
        is_child(cur, kids, 0, sp_leaf_bit(bits1, bits2, off + z))
        # The parent's height, then its index, none at the root.
        node_at = const(SP_TREE + (z + 1) * SP_WORD2_MUL)
        if const(z + 1 == height):
            parent = out
        else:
            node_at = sp_be16(lvals, off + z + 1, height - z - 1) + node_at
            parent = StackBuf(1)
        keccak([pp, a0], [node_at, kids[0]], parent, tail=kids[1:5], len=80, pad_tail=1)
        cur = parent[0]
    return
```
-/
def spPath (node : Word) (pp : Word) (a0 : FW) (bits1 : List V) (bits2 : List V) (lvals : List V) (out : List V) (off : Nat) (height : Nat) : B (Unit) := B.inline "sp_path" do
  let mut cur := node
  for z_k in [0:height] do
    let kids ← B.stackBuf 5
    B.witness "siblings" (.stack (kids.take 2))
    let t0 ← spLeafBit bits1 bits2 (off + z_k)
    isChild cur kids 0 t0
    let mut nodeAt : FW := FW.c (lit (SP_TREE + ((z_k + 1) * SP_WORD2_MUL)))
    let mut parent : List V := default
    if (z_k + 1) = height then
      parent := out
    else
      let t1 ← spBe16 lvals ((off + z_k) + 1) ((height - z_k) - 1)
      nodeAt ← Ex.bind (.add (.w t1) nodeAt.ex)
      parent ← B.stackBuf 1
    B.keccak (a := (.words [.cell pp.v, (← a0.msg)])) (b := (.words [(← nodeAt.msg), .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
    cur := cellOf parent 0

set_option linter.unusedVariables false in
/-- `@inline sp_layer` (`guests/lean_ethereum.py`, line 4165):

```
@inline
def sp_layer(pp, a0, key, signed, byte_bits, bits1, bits2, lvals, out, off: Const, height: Const):
    # One layer: the key at (a0, key), `key` its key pair as A1 holds it, signs `signed`,
    # its counter rebuilt from four bytes, then the path to its tree's root into out.
    ctr = StackBuf(SP_COUNTER_BYTES)
    hint_witness(ctr, "sp_counter")
    counter = sp_from_bytes(byte_bits, ctr, SP_COUNTER_BYTES)
    enc = StackBuf(1)
    enc_at = key + const(SP_WOTS_ENC)
    keccak([pp, a0], [enc_at, signed], enc, tail=[counter, 0, 0, 0], len=SP_ENCODING_BYTES)
    leaf = sp_wots(pp, a0, key, enc[0])
    sp_path(leaf, pp, a0, bits1, bits2, lvals, out, off, height)
    return
```
-/
def spLayer (pp : Word) (a0 : FW) (key : Word) (signed : Word) (byteBits : Word) (bits1 : List V) (bits2 : List V) (lvals : List V) (out : List V) (off : Nat) (height : Nat) : B (Unit) := B.inline "sp_layer" do
  let ctr ← B.stackBuf SP_COUNTER_BYTES
  B.witness "sp_counter" (.stack ctr)
  let counter ← spFromBytes byteBits ctr SP_COUNTER_BYTES
  let enc ← B.stackBuf 1
  let encAt ← Ex.lower (.add (.w key) (.c (lit SP_WOTS_ENC)))
  B.keccak (a := (.words [.cell pp.v, (← a0.msg)])) (b := (.words [.cell encAt.v, .cell signed.v])) (tail := some (.words [.cell counter.v, .zero, .zero, .zero])) (len := some SP_ENCODING_BYTES) (out := (.frame enc))
  let leaf ← call1 "sp_wots" [pp.v, (← FW.val a0).v, key.v, (cellOf enc 0).v]
  spPath leaf pp a0 bits1 bits2 lvals out off height

set_option linter.unusedVariables false in
/-- `@inline sp_fors_at` (`guests/lean_ethereum.py`, line 4050):

```
@inline
def sp_fors_at(a1, vals, c: Const, z: Const):
    # The A1 of tree c's node at height z on the opened leaf's path, `a1` being the
    # trees' with neither: z, then the node's tree index across the trees in the word's
    # last two bytes, big endian. vals holds the index below the root, whose high byte is
    # c's part alone from height SP_FORS_HEIGHT - 8 on, a constant added first so that trees
    # sharing it share the sum; at the root the index is c.
    at = a1 + const(z * SP_WORD2_MUL)
    if const(z == SP_FORS_HEIGHT):
        at = at + const(c * SP_WORD3_MUL_0)
    elif const(z // (SP_FORS_HEIGHT - 8) == 0):
        at = at + sp_be16(vals, SP_FORS_HEIGHT * c + z, 16)
    else:
        at = at + const(c // 2 ** (z - (SP_FORS_HEIGHT - 8))) * (GEN ** 8 * const(SP_WORD3_MUL_0) + const(SP_WORD3_MUL_1))
        at = at + sp_be16(vals, SP_FORS_HEIGHT * c + z, 8)
    return at
```
-/
def spForsAt (a1 : Word) (vals : List V) (c : Nat) (z : Nat) : B (Word) := B.inline "sp_fors_at" do
  let mut at' ← Ex.lower (.add (.w a1) (.c (lit (z * SP_WORD2_MUL))))
  if z = SP_FORS_HEIGHT then
    at' ← Ex.lower (.add (.w at') (.c (lit (c * SP_WORD3_MUL_0))))
  else
    if (z / (SP_FORS_HEIGHT - 8)) = 0 then
      let t0 ← spBe16 vals ((SP_FORS_HEIGHT * c) + z) 16
      at' ← B.add at' t0
    else
      at' ← Ex.lower (.add (.w at') (.mul (.c (lit (c / (2 ^ (z - (SP_FORS_HEIGHT - 8)))))) (.add (.mul (.g 8) (.c (lit SP_WORD3_MUL_0))) (.c (lit SP_WORD3_MUL_1)))))
      let t0 ← spBe16 vals ((SP_FORS_HEIGHT * c) + z) 8
      at' ← B.add at' t0
  return at'

set_option linter.unusedVariables false in
/-- `@inline sp_md_bit` (`guests/lean_ethereum.py`, line 3974):

```
@inline
def sp_md_bit(bits0, bits1, p: Const):
    # Bit p of the digest read most significant first, as base_2b reads it: bit
    # 7 - p % 8 of byte p // 8, from the bit runs of the first call's two cells.
    b = bits0[(8 * (p // 8) + 7 - p % 8) % SP_CELL_BITS]
    if const(p // SP_CELL_BITS == 1):
        b = bits1[8 * (p // 8) + 7 - p % 8 - SP_CELL_BITS]
    return b
```
-/
def spMdBit (bits0 : List V) (bits1 : List V) (p : Nat) : B (Word) := B.inline "sp_md_bit" do
  let mut b := cellOf bits0 ((((8 * (p / 8)) + 7) - (p % 8)) % SP_CELL_BITS)
  if (p / SP_CELL_BITS) = 1 then
    b := cellOf bits1 ((((8 * (p / 8)) + 7) - (p % 8)) - SP_CELL_BITS)
  else
    pure ()
  return b

set_option linter.unusedVariables false in
/-- `@inline sp_fors_tree` (`guests/lean_ethereum.py`, line 4068):

```
@inline
def sp_fors_tree(pp, a0, a1, bits0, bits1, vals, roots, c: Const):
    # FORS tree c: its leaf, hashed from the hinted secret, then climbed up the hinted
    # ordered pairs to its root, into roots[c].
    secret = hint_witness("sp_fors_secrets")
    held = StackBuf(1)
    keccak([pp, a0], [sp_fors_at(a1, vals, c, 0), secret], held)
    cur = held[0]
    for z in unroll(0, SP_FORS_HEIGHT):
        # The two children, then three cells the compiler sets to the padding, so the
        # node's hash reads the right child in place (`pad_tail=1`).
        kids = StackBuf(5)
        hint_witness(kids[0:2], "sp_fors_nodes")
        is_child(cur, kids, 0, sp_md_bit(bits0, bits1, SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - 1 - z))
        node_at = sp_fors_at(a1, vals, c, z + 1)
        if const(z + 1 == SP_FORS_HEIGHT):
            keccak([pp, a0], [node_at, kids[0]], roots[c:c + 1], tail=kids[1:5], len=80, pad_tail=1)
        else:
            parent = StackBuf(1)
            keccak([pp, a0], [node_at, kids[0]], parent, tail=kids[1:5], len=80, pad_tail=1)
            cur = parent[0]
    return
```
-/
def spForsTree (pp : Word) (a0 : Word) (a1 : Word) (bits0 : List V) (bits1 : List V) (vals : List V) (roots : List V) (c : Nat) : B (Unit) := B.inline "sp_fors_tree" do
  let secret ← hinted (B.witnessCell "sp_fors_secrets")
  let held ← B.stackBuf 1
  let t0 ← spForsAt a1 vals c 0
  B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell t0.v, .cell secret.v])) (out := (.frame held))
  let mut cur := cellOf held 0
  let mut parent : List V := default
  for z_k in [0:SP_FORS_HEIGHT] do
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack (kids.take 2))
    let t1 ← spMdBit bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt a1 vals c (z_k + 1)
    if (z_k + 1) = SP_FORS_HEIGHT then
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame ((roots.drop c).take ((c + 1) - c))))
    else
      parent ← B.stackBuf 1
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
      cur := cellOf parent 0

set_option linter.unusedVariables false in
/-- `@inline sp_md_byte` (`guests/lean_ethereum.py`, line 3996):

```
@inline
def sp_md_byte(vals, i: Const):
    # Digest byte i < SP_MD_BYTES where its cell holds it, from the shifts of field c,
    # the one its first bit is in, and of c + 1 if it reaches it. A byte inside c is c
    # shifted past the bits after the byte, masked to eight bits; a byte across both is
    # c's low bits raised past c + 1's high ones. It keeps the trees' places vals carries,
    # which the caller takes out.
    c = 8 * i // SP_FORS_HEIGHT
    if const(c == (8 * i + 7) // SP_FORS_HEIGHT):
        v = vals[SP_FORS_HEIGHT * (2 * c + 1) - 8 * i - 8]
        if const(8 * i != SP_FORS_HEIGHT * c):
            v = v + vals[SP_FORS_HEIGHT * (2 * c + 1) - 8 * i] * GEN ** 8
        v = v * const(2 ** (8 * (i % 16)))
    else:
        v = (vals[SP_FORS_HEIGHT * c] + vals[SP_FORS_HEIGHT * (2 * c + 1) - 8 * i] * GEN ** (SP_FORS_HEIGHT * (c + 1) - 8 * i)) * const(2 ** (8 * (i % 16) + 8 * i + 8 - SP_FORS_HEIGHT * (c + 1)))
        v = v + vals[SP_FORS_HEIGHT * (2 * c + 3) - 8 * i - 8] * const(2 ** (8 * (i % 16)))
    return v
```
-/
def spMdByte (vals : List V) (i : Nat) : B (Word) := B.inline "sp_md_byte" do
  let c := (8 * i) / SP_FORS_HEIGHT
  let mut v : Word := default
  if c = (((8 * i) + 7) / SP_FORS_HEIGHT) then
    v := cellOf vals (((SP_FORS_HEIGHT * ((2 * c) + 1)) - (8 * i)) - 8)
    if (8 * i) ≠ (SP_FORS_HEIGHT * c) then
      v ← Ex.lower (.add (.w v) (.mul (.v (cellOf vals ((SP_FORS_HEIGHT * ((2 * c) + 1)) - (8 * i)))) (.g 8)))
    else
      pure ()
    v ← Ex.lower (.mul (.w v) (.c (lit (2 ^ (8 * (i % 16))))))
  else
    v ← Ex.lower (.mul (.add (.v (cellOf vals (SP_FORS_HEIGHT * c))) (.mul (.v (cellOf vals ((SP_FORS_HEIGHT * ((2 * c) + 1)) - (8 * i)))) (.g ((SP_FORS_HEIGHT * (c + 1)) - (8 * i))))) (.c (lit (2 ^ ((((8 * (i % 16)) + (8 * i)) + 8) - (SP_FORS_HEIGHT * (c + 1)))))))
    v ← Ex.lower (.add (.w v) (.mul (.v (cellOf vals (((SP_FORS_HEIGHT * ((2 * c) + 3)) - (8 * i)) - 8))) (.c (lit (2 ^ (8 * (i % 16)))))))
  return v

set_option linter.unusedVariables false in
/-- `@inline sp_leaf_shifts` (`guests/lean_ethereum.py`, line 4029):

```
@inline
def sp_leaf_shifts(bits1, bits2, lvals, off: Const, n: Const):
    # The leaf of n bits from leaf bit `off` and its right shifts: lvals[off + z] is the
    # index of its ancestor at height z.
    lvals[off + n - 1] = sp_leaf_bit(bits1, bits2, off + n - 1)
    for r in unroll(1, n):
        lvals[off + n - 1 - r] = sp_leaf_bit(bits1, bits2, off + n - 1 - r) + GEN * lvals[off + n - r]
    return
```
-/
def spLeafShifts (bits1 : List V) (bits2 : List V) (lvals : List V) (off : Nat) (n : Nat) : B (Unit) := B.inline "sp_leaf_shifts" do
  let t0 ← spLeafBit bits1 bits2 ((off + n) - 1)
  B.copy (cellOf lvals ((off + n) - 1)) t0
  for r_k in [1:n] do
    let t1 ← spLeafBit bits1 bits2 (((off + n) - 1) - r_k)
    Ex.into (cellOf lvals (((off + n) - 1) - r_k)) (.add (.w t1) (.mul (.g 1) (.v (cellOf lvals ((off + n) - r_k)))))

set_option linter.unusedVariables false in
/-- `@inline sp_fors_field` (`guests/lean_ethereum.py`, line 3984):

```
@inline
def sp_fors_field(bits0, bits1, vals, c: Const):
    # FORS tree c's leaf, the digest's SP_FORS_HEIGHT bits from bit SP_FORS_HEIGHT c,
    # and its right shifts, each with tree c's place across the trees: vals[SP_FORS_HEIGHT
    # c + z] is the FIPS 205 tree index of the leaf's ancestor at height z, c 2^(height - z)
    # plus its index in tree c.
    vals[SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - 1] = sp_md_bit(bits0, bits1, SP_FORS_HEIGHT * c) + const(2 * c)
    for r in unroll(1, SP_FORS_HEIGHT):
        vals[SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - 1 - r] = sp_md_bit(bits0, bits1, SP_FORS_HEIGHT * c + r) + GEN * vals[SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - r]
    return
```
-/
def spForsField (bits0 : List V) (bits1 : List V) (vals : List V) (c : Nat) : B (Unit) := B.inline "sp_fors_field" do
  let t0 ← spMdBit bits0 bits1 (SP_FORS_HEIGHT * c)
  Ex.into (cellOf vals (((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1)) (.add (.w t0) (.c (lit (2 * c))))
  for r_k in [1:SP_FORS_HEIGHT] do
    let t1 ← spMdBit bits0 bits1 ((SP_FORS_HEIGHT * c) + r_k)
    Ex.into (cellOf vals ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - r_k)) (.add (.w t1) (.mul (.g 1) (.v (cellOf vals (((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - r_k)))))

set_option linter.unusedVariables false in
/-- `@inline sp_word` (`guests/lean_ethereum.py`, line 4092):

```
@inline
def sp_word(pp, a0, a1, run, first: Const, stride: Const, j: Const):
    # Word j of a T_l input: PK.seed, the address, then the values, value i at
    # run[first + stride i] (the FORS roots, or a one-time key's chain tips).
    w = pp
    if const(j == 1):
        w = a0
    if const(j == 2):
        w = a1
    if const(j // 3 != 0):
        w = run[first + stride * (j - 3)]
    return w
```
-/
def spWord (pp : Word) (a0 : Word) (a1 : Word) (run : List V) (first : Nat) (stride : Nat) (j : Nat) : B (Word) := B.inline "sp_word" do
  let mut w := pp
  if j = 1 then
    w := a0
  else
    pure ()
  if j = 2 then
    w := a1
  else
    pure ()
  if (j / 3) ≠ 0 then
    w := cellOf run (first + (stride * (j - 3)))
  else
    pure ()
  return w

set_option linter.unusedVariables false in
/-- `@inline ring_psi` (`guests/lean_ethereum.py`, line 3291):

```
@inline
def ring_psi(out, r: Const, v, g):
    # out[r] = Psi(v) = sum_b g_b v^(2^b), the inner stage: 7 squarings and 8 products.
    psi = g[0] * v
    for b in unroll(1, RING_MAP_WIDTH - 1):
        v = v * v
        psi += g[b] * v
    v = v * v
    out[r] = psi + g[RING_MAP_WIDTH - 1] * v
    return
```
-/
def ringPsi (out : List V) (r : Nat) (v : Word) (g : List V) : B (Unit) := B.inline "ring_psi" do
  let mut psi ← B.mul (cellOf g 0) v
  let mut v := v
  for b_k in [1:RING_MAP_WIDTH - 1] do
    v ← B.mul v v
    psi ← B.add psi (← B.mul (cellOf g b_k) v)
  v ← B.mul v v
  B.addInto (cellOf out r) psi (← B.mul (cellOf g (RING_MAP_WIDTH - 1)) v)

set_option linter.unusedVariables false in
/-- `@inline keccak_form` (`guests/lean_ethereum.py`, line 2855):

```
@inline
def keccak_form(lanes, shifts, f_lanes, f_off: Const):
    # <L^T(E), f> for theta, rho, pi's transpose L^T, on weights that factor as lane
    # times slice: E = lanes (x) eZ and f = f_lanes (x) fZ, the slices entering only
    # through shifts[r] = sum_z fZ[z] eZ[(z + r) % 64]. f_lanes are frame cells from
    # f_off.
    total = 0
    column = StackBuf(5)
    column_next = StackBuf(5)
    f_column = StackBuf(5)
    for x in unroll(0, 5):
        acc = 0
        acc_next = 0
        f_acc = 0
        for y in unroll(0, 5):
            lane_weight = lanes[GEN ** KECCAK_PI[x + 5 * y]]
            moved = lane_weight * shifts[KECCAK_RHO[x + 5 * y]]
            f_weight = f_lanes[f_off + x + 5 * y]
            total += f_weight * moved
            acc += moved
            acc_next += lane_weight * shifts[(KECCAK_RHO[x + 5 * y] + 1) % 64]
            f_acc += f_weight
        column[x] = acc
        column_next[x] = acc_next
        f_column[x] = f_acc
    for x in unroll(0, 5):
        total += f_column[x] * (column[(x + 1) % 5] + column_next[(x + 4) % 5])
    return total
```
-/
def keccakForm (lanes : Word) (shifts : List V) (fLanes : List V) (fOff : Nat) : B (FW) := B.inline "keccak_form" do
  let mut total : FW := FW.c (lit 0)
  let column ← B.stackBuf 5
  let columnNext ← B.stackBuf 5
  let fColumn ← B.stackBuf 5
  let mut laneWeight : Word := default
  let mut moved : Word := default
  let mut fWeight : Word := default
  for x_k in [0:5] do
    let mut acc : FW := FW.c (lit 0)
    let mut accNext : FW := FW.c (lit 0)
    let mut fAcc : FW := FW.c (lit 0)
    for y_k in [0:5] do
      laneWeight ← B.load lanes (arrInt KECCAK_PI (x_k + (5 * y_k)))
      moved ← B.mul laneWeight (cellOf shifts (arrInt KECCAK_RHO (x_k + (5 * y_k))))
      fWeight := cellOf fLanes ((fOff + x_k) + (5 * y_k))
      total ← Ex.bind (.add total.ex (.mul (.w fWeight) (.w moved)))
      acc ← Ex.bind (.add acc.ex (.w moved))
      accNext ← Ex.bind (.add accNext.ex (.mul (.w laneWeight) (.v (cellOf shifts (((arrInt KECCAK_RHO (x_k + (5 * y_k))) + 1) % 64)))))
      fAcc ← Ex.bind (.add fAcc.ex (.w fWeight))
    Ex.into (cellOf column x_k) acc.ex
    Ex.into (cellOf columnNext x_k) accNext.ex
    Ex.into (cellOf fColumn x_k) fAcc.ex
  for x_k in [0:5] do
    total ← Ex.bind (.add total.ex (.mul (.v (cellOf fColumn x_k)) (.add (.v (cellOf column ((x_k + 1) % 5))) (.v (cellOf columnNext ((x_k + 4) % 5))))))
  return total

set_option linter.unusedVariables false in
/-- `@inline fold_node` (`guests/lean_ethereum.py`, line 2827):

```
@inline
def fold_node(src, dst, a_t, a_t1, p: Const, b: Const, t: Const):
    # x0 + a (x0 + x1) as (1 + a) x0 + a x1: a MUL for an XOR, the scarcer row.
    n = 2 ** (KECCAK_Z_BITS - t)
    for k in unroll(0, n // 2):
        x0 = src[p * n + (2 * k + (n - 1) * b) % n]
        x1 = src[p * n + (2 * k + 1 + (n - 1) * b) % n]
        dst[(p + 2 ** t * b) * (n // 2) + k] = a_t1 * x0 + a_t * x1
    return
```
-/
def foldNode (src : List V) (dst : List V) (aT : Word) (aT1 : Word) (p : Nat) (b : Nat) (t : Nat) : B (Unit) := B.inline "fold_node" do
  let n := 2 ^ (KECCAK_Z_BITS - t)
  for k_k in [0:n / 2] do
    let x0 := cellOf src ((p * n) + (((2 * k_k) + ((n - 1) * b)) % n))
    let x1 := cellOf src ((p * n) + ((((2 * k_k) + 1) + ((n - 1) * b)) % n))
    B.addInto (cellOf dst (((p + ((2 ^ t) * b)) * (n / 2)) + k_k)) (← B.mul aT1 x0) (← B.mul aT x1)

set_option linter.unusedVariables false in
/-- `@inline fold_shifts` (`guests/lean_ethereum.py`, line 2838):

```
@inline
def fold_shifts(src, dst, a_t, t: Const):
    # One level of sum_w eq(a, w) V[w - r] for every used r at once, LSB first: node
    # p of depth t is the vector for the residue p of r mod 2^t, 2^(6 - t) cells at
    # p 2^(6 - t). Folding bit t splits it by bit t of r, b: V[w - r] pairs the
    # parent's cells 2k - b and 2k + 1 - b.
    a_t1 = 1 + a_t
    for p in unroll(0, 2 ** t):
        for b in unroll(0, 2):
            if const(t + 1 == KECCAK_Z_BITS):
                if KECCAK_SHIFT_USED[p + 2 ** t * b] == 1:
                    fold_node(src, dst, a_t, a_t1, p, b, t)
            else:
                fold_node(src, dst, a_t, a_t1, p, b, t)
    return
```
-/
def foldShifts (src : List V) (dst : List V) (aT : Word) (t : Nat) : B (Unit) := B.inline "fold_shifts" do
  let aT1 ← Ex.lower (.add (Ex.nat 1) (.w aT))
  for p_k in [0:2 ^ t] do
    for b_k in [0:2] do
      if (t + 1) = KECCAK_Z_BITS then
        if (arrInt KECCAK_SHIFT_USED (p_k + ((2 ^ t) * b_k))) = 1 then
          foldNode src dst aT aT1 p_k b_k t
        else
          pure ()
      else
        foldNode src dst aT aT1 p_k b_k t

set_option linter.unusedVariables false in
/-- `@inline eqtree` (`guests/lean_ethereum.py`, line 949):

```
@inline
def eqtree(point_ptr, out, n_coords: Const):
    # The eq tensor of the n_coords challenges at point_ptr[0..n_coords), built by
    # doubling into out (size 2^(n_coords+1) - 2); the final 2^n_coords values start
    # at offset 2^n_coords - 2.
    r0 = point_ptr[GEN ** 0]
    out[GEN ** 0] = 1 + r0
    out[GEN ** 1] = r0
    for t in unroll(1, n_coords):
        rt = point_ptr[GEN ** t]
        one_plus_rt = 1 + rt
        for i in unroll(0, 2 ** t):
            pw = out[GEN ** (2 ** t - 2 + i)]
            out[GEN ** (2 ** (t + 1) - 2 + i)] = pw * one_plus_rt
            out[GEN ** (2 ** (t + 1) - 2 + 2 ** t + i)] = pw * rt
    return
```
-/
def eqtree (pointPtr : Shifted) (out : Word) (nCoords : Nat) : B (Unit) := B.inline "eqtree" do
  let r0 ← B.load pointPtr.base pointPtr.exp
  B.store out 0 (← Ex.lower (.add (Ex.nat 1) (.w r0)))
  B.store out 1 r0
  let mut pw : Word := default
  for t_k in [1:nCoords] do
    let rt ← B.load pointPtr.base (pointPtr.exp + t_k)
    let onePlusRt ← Ex.lower (.add (Ex.nat 1) (.w rt))
    for i_k in [0:2 ^ t_k] do
      pw ← B.load out (((2 ^ t_k) - 2) + i_k)
      B.store out (((2 ^ (t_k + 1)) - 2) + i_k) (← B.mul pw onePlusRt)
      B.store out ((((2 ^ (t_k + 1)) - 2) + (2 ^ t_k)) + i_k) (← B.mul pw rt)

set_option linter.unusedVariables false in
/-- `@inline eqtree_frame` (`guests/lean_ethereum.py`, line 967):

```
@inline
def eqtree_frame(point_ptr, out, n_coords: Const, count: Const):
    # eqtree into frame cells, in the same layout, the last level cut at `count`
    # (which must exceed half of it).
    r0 = point_ptr[GEN ** 0]
    out[0] = 1 + r0
    out[1] = r0
    for t in unroll(1, n_coords):
        rt = point_ptr[GEN ** t]
        one_plus_rt = 1 + rt
        for i in unroll(0, 2 ** t):
            pw = out[2 ** t - 2 + i]
            out[2 ** (t + 1) - 2 + i] = pw * one_plus_rt
            if const(t + 1 == n_coords):
                if (2 ** t + i) // count == 0:
                    out[2 ** (t + 1) - 2 + 2 ** t + i] = pw * rt
            else:
                out[2 ** (t + 1) - 2 + 2 ** t + i] = pw * rt
    return
```
-/
def eqtreeFrame (pointPtr : Shifted) (out : List V) (nCoords : Nat) (count : Nat) : B (Unit) := B.inline "eqtree_frame" do
  let r0 ← B.load pointPtr.base pointPtr.exp
  Ex.into (cellOf out 0) (.add (Ex.nat 1) (.w r0))
  B.copy (cellOf out 1) r0
  let mut pw : Word := default
  for t_k in [1:nCoords] do
    let rt ← B.load pointPtr.base (pointPtr.exp + t_k)
    let onePlusRt ← Ex.lower (.add (Ex.nat 1) (.w rt))
    for i_k in [0:2 ^ t_k] do
      pw := cellOf out (((2 ^ t_k) - 2) + i_k)
      B.mulInto (cellOf out (((2 ^ (t_k + 1)) - 2) + i_k)) pw onePlusRt
      if (t_k + 1) = nCoords then
        if (((2 ^ t_k) + i_k) / count) = 0 then
          B.mulInto (cellOf out ((((2 ^ (t_k + 1)) - 2) + (2 ^ t_k)) + i_k)) pw rt
        else
          pure ()
      else
        B.mulInto (cellOf out ((((2 ^ (t_k + 1)) - 2) + (2 ^ t_k)) + i_k)) pw rt

set_option linter.unusedVariables false in
/-- `@inline keccak_slot_lanes` (`guests/lean_ethereum.py`, line 3101):

```
@inline
def keccak_slot_lanes(slot, segment_point, out, first: Const, count: Const):
    # The weight an opening's slot point puts on each lane, into the frame cells
    # out[0..25): the states it speaks of start at `first`, one per segment, for the
    # first `count` segments.
    slot_weights = StackBuf(2 ** (QKECCAK_SLOT_LOG + 1) - 2)
    eqtree_frame(slot, slot_weights, QKECCAK_SLOT_LOG, KECCAK_LANES * KECCAK_SEGMENTS)
    seg_weights = StackBuf(2 ** (KECCAK_SEG_LOG + 1) - 2)
    eqtree_frame(segment_point, seg_weights, KECCAK_SEG_LOG, 2 ** KECCAK_SEG_LOG)
    for lane in unroll(0, KECCAK_LANES):
        lane_acc = 0
        for m in unroll(0, count):
            lane_acc += seg_weights[2 ** KECCAK_SEG_LOG - 2 + m] * slot_weights[2 ** QKECCAK_SLOT_LOG - 2 + KECCAK_LANES * (first + m) + lane]
        out[lane] = lane_acc
    return
```
-/
def keccakSlotLanes (slot : Word) (segmentPoint : Word) (out : List V) (first : Nat) (count : Nat) : B (Unit) := B.inline "keccak_slot_lanes" do
  let slotWeights ← B.stackBuf 126
  eqtreeFrame (Shifted.of (slot)) slotWeights QKECCAK_SLOT_LOG (KECCAK_LANES * KECCAK_SEGMENTS)
  let segWeights ← B.stackBuf 2
  eqtreeFrame (Shifted.of (segmentPoint)) segWeights KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
  for lane_k in [0:KECCAK_LANES] do
    let mut laneAcc : FW := FW.c (lit 0)
    for m_k in [0:count] do
      laneAcc ← Ex.bind (.add laneAcc.ex (.mul (.v (cellOf segWeights (((2 ^ KECCAK_SEG_LOG) - 2) + m_k))) (.v (cellOf slotWeights ((((2 ^ QKECCAK_SLOT_LOG) - 2) + (KECCAK_LANES * (first + m_k))) + lane_k)))))
    Ex.into (cellOf out lane_k) laneAcc.ex

set_option linter.unusedVariables false in
/-- `@inline split_limbs` (`guests/lean_ethereum.py`, line 573):

```
@inline
def split_limbs(word):
    # Hint the low limb and derive the quotient by Y. Requiring both in K proves
    # `word = lo + Y*hi`, which binds them.
    lo = StackBuf(1)
    hint_f128_limbs(lo, word)
    hi = (word + lo[0]) * Y_INV
    assert_in_k(lo[0], hi)
    return lo[0], hi
```
-/
def splitLimbs (word' : Word) : B (Word × Word) := B.inline "split_limbs" do
  let lo ← B.stackBuf 1
  B.hintLimbs word' lo
  let hi ← Ex.lower (.mul (.add (.w word') (.v (cellOf lo 0))) (Ex.nat Y_INV))
  B.assertInK (cellOf lo 0) hi
  return (cellOf lo 0, hi)

set_option linter.unusedVariables false in
/-- `@inline sel_g_nibble` (`guests/lean_ethereum.py`, line 2107):

```
@inline
def sel_g_nibble(out, gs, width: Const):
    # out[u] = prod_t gs[t]^(bit t of u) for u < 2^width.
    vals = StackBuf(16)
    vals[0] = 1
    vals[1] = gs[GEN ** 0]
    for t in unroll(1, width):
        g_t = gs[GEN ** t]
        for i in unroll(0, 2 ** t):
            vals[2 ** t + i] = vals[i] * g_t
    for i in unroll(0, 2 ** width):
        out[GEN ** i] = vals[i]
    return
```
-/
def selGNibble (out : Word) (gs : Word) (width : Nat) : B (Unit) := B.inline "sel_g_nibble" do
  let vals ← B.stackBuf 16
  B.constInto (cellOf vals 0) 1
  B.loadInto (cellOf vals 1) gs 0
  for t_k in [1:width] do
    let gT ← B.load gs t_k
    for i_k in [0:2 ^ t_k] do
      B.mulInto (cellOf vals ((2 ^ t_k) + i_k)) (cellOf vals i_k) gT
  for i_k in [0:2 ^ width] do
    B.store out i_k (cellOf vals i_k)

set_option linter.unusedVariables false in
/-- `@inline sel_eq_nibble` (`guests/lean_ethereum.py`, line 2089):

```
@inline
def sel_eq_nibble(out, z, z1, width: Const):
    # The eq tables over coordinates z[0..t] for t < width, level t at 2^(t+1) - 2,
    # coordinate t being index bit t; z1 = 1 + z.
    levels = StackBuf(SEL_EQ_STRIDE)
    levels[0] = z1[GEN ** 0]
    levels[1] = z[GEN ** 0]
    for t in unroll(1, width):
        r = z[GEN ** t]
        r1 = z1[GEN ** t]
        for i in unroll(0, 2 ** t):
            levels[2 ** (t + 1) - 2 + i] = levels[2 ** t - 2 + i] * r1
            levels[2 ** (t + 1) - 2 + 2 ** t + i] = levels[2 ** t - 2 + i] * r
    for i in unroll(0, 2 ** (width + 1) - 2):
        out[GEN ** i] = levels[i]
    return
```
-/
def selEqNibble (out : Word) (z : Word) (z1 : Word) (width : Nat) : B (Unit) := B.inline "sel_eq_nibble" do
  let levels ← B.stackBuf SEL_EQ_STRIDE
  B.loadInto (cellOf levels 0) z1 0
  B.loadInto (cellOf levels 1) z 0
  for t_k in [1:width] do
    let r ← B.load z t_k
    let r1 ← B.load z1 t_k
    for i_k in [0:2 ^ t_k] do
      B.mulInto (cellOf levels (((2 ^ (t_k + 1)) - 2) + i_k)) (cellOf levels (((2 ^ t_k) - 2) + i_k)) r1
      B.mulInto (cellOf levels ((((2 ^ (t_k + 1)) - 2) + (2 ^ t_k)) + i_k)) (cellOf levels (((2 ^ t_k) - 2) + i_k)) r
  for i_k in [0:(2 ^ (width + 1)) - 2] do
    B.store out i_k (cellOf levels i_k)

set_option linter.unusedVariables false in
/-- `@inline gkr_product_check` (`guests/lean_ethereum.py`, line 1853):

```
@inline
def gkr_product_check(evals, lam, claim, n: Const):
    # The layer's sumcheck claim is the combined product of each tree's n children.
    combined = 0
    for i in unroll(0, N_GKR_TREES):
        tree = N_GKR_TREES - 1 - i  # Horner in lam, so the top tree lands last
        product = evals[n * tree]
        for j in unroll(1, n):
            product = product * evals[n * tree + j]
        combined = product + lam * combined
    assert claim == combined
    return
```
-/
def gkrProductCheck (evals : List V) (lam : Word) (claim : Word) (n : Nat) : B (Unit) := B.inline "gkr_product_check" do
  let mut combined : FW := FW.c (lit 0)
  for i_k in [0:N_GKR_TREES] do
    let tree := (N_GKR_TREES - 1) - i_k
    let mut product := cellOf evals (n * tree)
    for j_k in [1:n] do
      product ← B.mul product (cellOf evals ((n * tree) + j_k))
    combined ← Ex.bind (.add (.w product) (.mul (.w lam) combined.ex))
  B.assertEq claim (← FW.val combined)

set_option linter.unusedVariables false in
/-- `@inline fs_perm` (`guests/lean_ethereum.py`, line 608):

```
@inline
def fs_perm(sp, rate, k: Const):
    # The permutation taking the k waiting scalars: they overwrite the rate, zero past them.
    nxt = StackBuf(KECCAK_STATE)
    if k == 0:
        keccak([0, 0], [0, 0], nxt, cap=sp)
    if k == 1:
        keccak(rate[0:2], [0, 0], nxt, cap=sp)
    if k == 2:
        keccak(rate[0:2], rate[2:4], nxt, cap=sp)
    if k == 3:
        rate[6] = 0
        rate[7] = 0
        keccak(rate[0:2], rate[2:4], nxt, tail=rate[4:8], cap=sp)
    if k == 4:
        keccak(rate[0:2], rate[2:4], nxt, tail=rate[4:8], cap=sp)
    return nxt
```
-/
def fsPerm (sp : List V) (rate : List V) (k : Nat) : B (List V) := B.inline "fs_perm" do
  let nxt ← B.stackBuf KECCAK_STATE
  if k = 0 then
    B.keccakDuplex (a := (.words [.zero, .zero])) (b := (.words [.zero, .zero])) (cap := (.frame sp)) (out := (.frame nxt))
  else
    pure ()
  if k = 1 then
    B.keccakDuplex (a := (.cells (.frame (rate.take 2)))) (b := (.words [.zero, .zero])) (cap := (.frame sp)) (out := (.frame nxt))
  else
    pure ()
  if k = 2 then
    B.keccakDuplex (a := (.cells (.frame (rate.take 2)))) (b := (.cells (.frame ((rate.drop 2).take (4 - 2))))) (cap := (.frame sp)) (out := (.frame nxt))
  else
    pure ()
  if k = 3 then
    B.constInto (cellOf rate 6) 0
    B.constInto (cellOf rate 7) 0
    B.keccakDuplex (a := (.cells (.frame (rate.take 2)))) (b := (.cells (.frame ((rate.drop 2).take (4 - 2))))) (tail := some (.cells (.frame ((rate.drop 4).take (8 - 4))))) (cap := (.frame sp)) (out := (.frame nxt))
  else
    pure ()
  if k = 4 then
    B.keccakDuplex (a := (.cells (.frame (rate.take 2)))) (b := (.cells (.frame ((rate.drop 2).take (4 - 2))))) (tail := some (.cells (.frame ((rate.drop 4).take (8 - 4))))) (cap := (.frame sp)) (out := (.frame nxt))
  else
    pure ()
  return nxt

set_option linter.unusedVariables false in
/-- `@inline fs_pack` (`guests/lean_ethereum.py`, line 600):

```
@inline
def fs_pack(rate, k: Const, x, tag: Const):
    # Scalar x as lanes (c0, c1, 0, tag) over rate cells 2k and 2k + 1: x itself, then a constant.
    rate[2 * k] = x
    rate[2 * k + 1] = Y_TOWER * tag
    return
```
-/
def fsPack (rate : List V) (k : Nat) (x : FW) (tag : Nat) : B (Unit) := B.inline "fs_pack" do
  Ex.into (cellOf rate (2 * k)) x.ex
  Ex.into (cellOf rate ((2 * k) + 1)) (.mul (Ex.nat Y_TOWER) (Ex.nat tag))

set_option linter.unusedVariables false in
/-- `@inline fs_next` (`guests/lean_ethereum.py`, line 689):

```
@inline
def fs_next(rate, k: Const, cursor):
    # Fetch and absorb in one act: the word under `cursor` becomes waiting scalar k
    # (k < 4), and the cursor steps one word on. Reading and absorbing are inseparable,
    # so no proof-stream word can enter the computation unbound: the soundness
    # invariant the whole guest rests on.
    x = cursor[GEN ** 0]
    fs_pack(rate, k, x, DS_OBSERVE)
    return x, cursor * GEN
```
-/
def fsNext (rate : List V) (k : Nat) (cursor : Shifted) : B (Word × Shifted) := B.inline "fs_next" do
  let x ← B.load cursor.base cursor.exp
  fsPack rate k (FW.w x) DS_OBSERVE
  return (x, ⟨cursor.base, cursor.exp + 1⟩)

set_option linter.unusedVariables false in
/-- `@inline gkr_children` (`guests/lean_ethereum.py`, line 1838):

```
@inline
def gkr_children(sp, cursor, evals, n: Const):
    # Every tree's n children, tree by tree, nothing waiting before them. Returns the
    # sponge, the rate left waiting (its last one to four scalars) and the cursor.
    rate = StackBuf(8)
    for i in unroll(0, N_GKR_TREES * n):
        if i % 4 == 0:
            if i != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        ev, cursor = fs_next(rate, i % 4, cursor)
        evals[i] = ev
    return sp, rate, cursor
```
-/
def gkrChildren (sp : List V) (cursor : Shifted) (evals : List V) (n : Nat) : B (List V × List V × Shifted) := B.inline "gkr_children" do
  let mut rate ← B.stackBuf 8
  let mut sp := sp
  let mut cursor := cursor
  for i_k in [0:N_GKR_TREES * n] do
    if (i_k % 4) = 0 then
      if i_k ≠ 0 then
        sp ← fsPerm sp rate 4
        rate ← B.stackBuf 8
      else
        pure ()
    else
      pure ()
    let (t0, t1) ← fsNext rate (i_k % 4) cursor
    let ev := t0
    cursor := t1
    B.copy (cellOf evals i_k) ev
  return (sp, rate, cursor)

set_option linter.unusedVariables false in
/-- `@inline gkr_combine` (`guests/lean_ethereum.py`, line 1829):

```
@inline
def gkr_combine(vals, lam):
    # The trees' claims batched by powers of the combiner, tree t at lam^t.
    claim = vals[N_GKR_TREES - 1]
    for i in unroll(1, N_GKR_TREES):
        claim = vals[N_GKR_TREES - 1 - i] + lam * claim
    return claim
```
-/
def gkrCombine (vals : List V) (lam : Word) : B (Word) := B.inline "gkr_combine" do
  let mut claim := cellOf vals (N_GKR_TREES - 1)
  for i_k in [1:N_GKR_TREES] do
    claim ← B.add (cellOf vals ((N_GKR_TREES - 1) - i_k)) (← B.mul lam claim)
  return claim

set_option linter.unusedVariables false in
/-- `@inline challenge_from_state` (`guests/lean_ethereum.py`, line 584):

```
@inline
def challenge_from_state(state):
    # A challenge is the sponge's first two lanes, its first cell.
    return state[0]
```
-/
def challengeFromState (state : List V) : B (Word) := B.inline "challenge_from_state" do
  return cellOf state 0

set_option linter.unusedVariables false in
/-- `@inline squeeze` (`guests/lean_ethereum.py`, line 700):

```
@inline
def squeeze(sp, rate, k: Const):
    # A challenge: the permutation taking the k waiting scalars, read off its first two
    # lanes. Returns the new sponge and the challenge.
    nxt = fs_perm(sp, rate, k)
    challenge = challenge_from_state(nxt)
    return nxt, challenge
```
-/
def squeeze (sp : List V) (rate : List V) (k : Nat) : B (List V × Word) := B.inline "squeeze" do
  let nxt ← fsPerm sp rate k
  let challenge ← challengeFromState nxt
  return (nxt, challenge)

set_option linter.unusedVariables false in
/-- `@inline fs_absorb_nonce` (`guests/lean_ethereum.py`, line 627):

```
@inline
def fs_absorb_nonce(sp, rate, k: Const, nonce):
    # A grinding nonce as waiting scalar k (k < 4), with its own tag, then the
    # permutation that draws the next challenge, its first cell, and carries the
    # proof of work, the first lane of its second cell (`grind_check`).
    fs_pack(rate, k, nonce, DS_POW_NONCE)
    nxt = fs_perm(sp, rate, k + 1)
    return nxt
```
-/
def fsAbsorbNonce (sp : List V) (rate : List V) (k : Nat) (nonce : Word) : B (List V) := B.inline "fs_absorb_nonce" do
  fsPack rate k (FW.w nonce) DS_POW_NONCE
  let nxt ← fsPerm sp rate (k + 1)
  return nxt

set_option linter.unusedVariables false in
/-- `@inline fs_cap` (`guests/lean_ethereum.py`, line 667):

```
@inline
def fs_cap(fs0, fs1, fs2, fs3, fs4):
    # A carried capacity as the run a permutation reads.
    sp = [fs0, fs1, fs2, fs3, fs4]
    return sp
```
-/
def fsCap (fs0 : Word) (fs1 : Word) (fs2 : Word) (fs3 : Word) (fs4 : Word) : B (List V) := B.inline "fs_cap" do
  let t0 ← B.stackBuf 5
  B.copy (cellOf t0 0) fs0
  B.copy (cellOf t0 1) fs1
  B.copy (cellOf t0 2) fs2
  B.copy (cellOf t0 3) fs3
  B.copy (cellOf t0 4) fs4
  let sp := t0
  return sp

set_option linter.unusedVariables false in
/-- `@inline fs_store` (`guests/lean_ethereum.py`, line 681):

```
@inline
def fs_store(rec, field: Const, stride: Const, sp):
    # Store the capacity of permutation output `sp` as fs_load reads it.
    for j in unroll(0, FS_CELLS):
        rec[GEN ** ((field + j) * stride)] = sp[KECCAK_STATE - FS_CELLS + j]
    return
```
-/
def fsStore (rec' : Shifted) (field : Nat) (stride : Nat) (sp : List V) : B (Unit) := B.inline "fs_store" do
  for j_k in [0:FS_CELLS] do
    B.store rec'.base (rec'.exp + ((field + j_k) * stride)) (cellOf sp ((KECCAK_STATE - FS_CELLS) + j_k))

set_option linter.unusedVariables false in
/-- `@inline fs_grind_squeeze` (`guests/lean_ethereum.py`, line 637):

```
@inline
def fs_grind_squeeze(sp, rate, k: Const, cursor, tabs, bits: Const):
    # A challenge after a grind of `bits`, k scalars waiting (k <= 4): the nonce under
    # `cursor` joins them, a fifth permuting the four first, and its permutation draws
    # the challenge. A grind of zero bits is no nonce, a plain squeeze. Returns the new
    # sponge, the challenge and the cursor.
    if const(bits == 0):
        nxt = fs_perm(sp, rate, k)
        cur = cursor
    elif const(k == 4):
        full = fs_perm(sp, rate, 4)
        nonce_rate = StackBuf(8)
        nxt = fs_absorb_nonce(full, nonce_rate, 0, cursor[GEN ** 0])
        grind_check(nxt[1], tabs, bits)
        cur = cursor * GEN
    else:
        nxt = fs_absorb_nonce(sp, rate, k, cursor[GEN ** 0])
        grind_check(nxt[1], tabs, bits)
        cur = cursor * GEN
    return nxt, nxt[0], cur
```
-/
def fsGrindSqueeze (sp : List V) (rate : List V) (k : Nat) (cursor : Shifted) (tabs : Shifted) (bits : Nat) : B (List V × Word × Shifted) := B.inline "fs_grind_squeeze" do
  let mut nxt : List V := default
  let mut cur : Shifted := default
  if bits = 0 then
    nxt ← fsPerm sp rate k
    cur := cursor
  else
    if k = 4 then
      let full ← fsPerm sp rate 4
      let nonceRate ← B.stackBuf 8
      nxt ← fsAbsorbNonce full nonceRate 0 (← B.load cursor.base cursor.exp)
      let _ ← B.call (instName "grind_check" [.L bits]) [(cellOf nxt 1).v, (← B.shifted tabs.base tabs.exp).v] 0
      cur := ⟨cursor.base, cursor.exp + 1⟩
    else
      nxt ← fsAbsorbNonce sp rate k (← B.load cursor.base cursor.exp)
      let _ ← B.call (instName "grind_check" [.L bits]) [(cellOf nxt 1).v, (← B.shifted tabs.base tabs.exp).v] 0
      cur := ⟨cursor.base, cursor.exp + 1⟩
  return (nxt, cellOf nxt 0, cur)

set_option linter.unusedVariables false in
/-- `@inline fs_load` (`guests/lean_ethereum.py`, line 674):

```
@inline
def fs_load(rec, field: Const, stride: Const):
    # A record's carried capacity, its cells `stride` fields apart from `field` on.
    sp = [rec[GEN ** (field * stride)], rec[GEN ** ((field + 1) * stride)], rec[GEN ** ((field + 2) * stride)], rec[GEN ** ((field + 3) * stride)], rec[GEN ** ((field + 4) * stride)]]
    return sp
```
-/
def fsLoad (rec' : Word) (field : Nat) (stride : Nat) : B (List V) := B.inline "fs_load" do
  let t0 ← B.stackBuf 5
  B.loadInto (cellOf t0 0) rec' (field * stride)
  B.loadInto (cellOf t0 1) rec' ((field + 1) * stride)
  B.loadInto (cellOf t0 2) rec' ((field + 2) * stride)
  B.loadInto (cellOf t0 3) rec' ((field + 3) * stride)
  B.loadInto (cellOf t0 4) rec' ((field + 4) * stride)
  let sp := t0
  return sp

set_option linter.unusedVariables false in
/-- `@inline walk_group` (`guests/lean_ethereum.py`, line 3799):

```
@inline
def walk_group(at, pp, walks, tags, first: Const, n: Const, k: Const, lx: Const, powers, product, encoded):
    # The n chains from `first` on, at the digits of k (its low n), one dispatch for
    # all of them. Folds the digits' sum into `product`, in the exponent (`powers[s]` is
    # GEN ** s), and the digits into `encoded`, where the encoding digest holds them:
    # leanXMSS's low first, leanSPHINCS's most significant first in each byte (base_2b).
    for r in unroll(0, n):
        walk(at, pp, walks, tags, powers, first + r, (k // CHAIN_LENGTH ** r) % CHAIN_LENGTH, lx)
    if const(lx == 1):
        digits = const(k % CHAIN_LENGTH ** n * CHAIN_LENGTH ** first)
    else:
        digits = 0
        for r in unroll(0, n):
            digits = digits + const(((k // CHAIN_LENGTH ** r) % CHAIN_LENGTH) * 2 ** (8 * ((first + r) // SP_DIGITS_PER_BYTE) + W * (SP_DIGITS_PER_BYTE - 1 - (first + r) % SP_DIGITS_PER_BYTE)))
    return product * powers[DIGIT_SUMS[k % CHAIN_LENGTH ** n]], encoded + digits
```
-/
def walkGroup (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : FW) (encoded : FW) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  Ex.into (cellOf dsts 0) (.mul product.ex (.v (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))))
  Ex.into (cellOf dsts 1) (.add encoded.ex (Ex.nat digits))

set_option linter.unusedVariables false in
/-- `@inline chain_tip` (`guests/lean_ethereum.py`, line 3763):

```
@inline
def chain_tip(walks, i: Const):
    # Chain i's tip, in the last of its CHAIN_STEPS slots of `walks`.
    tip = walks[(i + 1) * CHAIN_STEPS - 1]
    return tip
```
-/
def chainTip (walks : List V) (i : Nat) : B (Word) := B.inline "chain_tip" do
  let tip := cellOf walks (((i + 1) * CHAIN_STEPS) - 1)
  return tip

set_option linter.unusedVariables false in
/-- `@inline leaf_word` (`guests/lean_ethereum.py`, line 3816):

```
@inline
def leaf_word(p0, p1, walks, j: Const):
    # Word j of a one-time leaf's input: the prefix (p0, p1), then the chain tips.
    w = p0
    if const(j == 1):
        w = p1
    if const(j != 0):
        if const(j != 1):
            w = chain_tip(walks, j - 2)
    return w
```
-/
def leafWord (p0 : Word) (p1 : Word) (walks : List V) (j : Nat) : B (Word) := B.inline "leaf_word" do
  let mut w := p0
  if j = 1 then
    w := p1
  else
    pure ()
  if j ≠ 0 then
    if j ≠ 1 then
      w ← chainTip walks (j - 2)
    else
      pure ()
  else
    pure ()
  return w

set_option linter.unusedVariables false in
/-- `@inline wots_leaf` (`guests/lean_ethereum.py`, line 3828):

```
@inline
def wots_leaf(p0, p1, walks, n: Const, leaf):
    # The hash of the prefix (p0, p1) and the n chain tips, each read where its walk left it.
    keccak_cells([leaf_word(p0, p1, walks, j) for j in unroll(0, n + 2)], leaf)
    return
```
-/
def wotsLeaf (p0 : Word) (p1 : Word) (walks : List V) (n : Nat) (leaf : List V) : B (Unit) := B.inline "wots_leaf" do
  let t0 ← leafWord p0 p1 walks 0
  let t1 ← leafWord p0 p1 walks 1
  let t2 ← leafWord p0 p1 walks 2
  let t3 ← leafWord p0 p1 walks 3
  let t4 ← leafWord p0 p1 walks 4
  let t5 ← leafWord p0 p1 walks 5
  let t6 ← leafWord p0 p1 walks 6
  let t7 ← leafWord p0 p1 walks 7
  let t8 ← leafWord p0 p1 walks 8
  let t9 ← leafWord p0 p1 walks 9
  let t10 ← leafWord p0 p1 walks 10
  let t11 ← leafWord p0 p1 walks 11
  let t12 ← leafWord p0 p1 walks 12
  let t13 ← leafWord p0 p1 walks 13
  let t14 ← leafWord p0 p1 walks 14
  let t15 ← leafWord p0 p1 walks 15
  let t16 ← leafWord p0 p1 walks 16
  let t17 ← leafWord p0 p1 walks 17
  let t18 ← leafWord p0 p1 walks 18
  let t19 ← leafWord p0 p1 walks 19
  let t20 ← leafWord p0 p1 walks 20
  let t21 ← leafWord p0 p1 walks 21
  let t22 ← leafWord p0 p1 walks 22
  let t23 ← leafWord p0 p1 walks 23
  let t24 ← leafWord p0 p1 walks 24
  let t25 ← leafWord p0 p1 walks 25
  let t26 ← leafWord p0 p1 walks 26
  let t27 ← leafWord p0 p1 walks 27
  let t28 ← leafWord p0 p1 walks 28
  let t29 ← leafWord p0 p1 walks 29
  let t30 ← leafWord p0 p1 walks 30
  let t31 ← leafWord p0 p1 walks 31
  let t32 ← leafWord p0 p1 walks 32
  let t33 ← leafWord p0 p1 walks 33
  let t34 ← leafWord p0 p1 walks 34
  let t35 ← leafWord p0 p1 walks 35
  let t36 ← leafWord p0 p1 walks 36
  let t37 ← leafWord p0 p1 walks 37
  let t38 ← leafWord p0 p1 walks 38
  let t39 ← leafWord p0 p1 walks 39
  let t40 ← leafWord p0 p1 walks 40
  let t41 ← leafWord p0 p1 walks 41
  let t42 ← leafWord p0 p1 walks 42
  let t43 ← leafWord p0 p1 walks 43
  let t44 ← leafWord p0 p1 walks 44
  let t45 ← leafWord p0 p1 walks 45
  let t46 ← leafWord p0 p1 walks 46
  let t47 ← leafWord p0 p1 walks 47
  let t48 ← leafWord p0 p1 walks 48
  let t49 ← leafWord p0 p1 walks 49
  let t50 ← leafWord p0 p1 walks 50
  let t51 ← leafWord p0 p1 walks 51
  let t52 ← leafWord p0 p1 walks 52
  let t53 ← leafWord p0 p1 walks 53
  let t54 ← leafWord p0 p1 walks 54
  let t55 ← leafWord p0 p1 walks 55
  let t56 ← leafWord p0 p1 walks 56
  let t57 ← leafWord p0 p1 walks 57
  let t58 ← leafWord p0 p1 walks 58
  let t59 ← leafWord p0 p1 walks 59
  B.keccakCells (cells := (.words [.cell t0.v, .cell t1.v, .cell t2.v, .cell t3.v, .cell t4.v, .cell t5.v, .cell t6.v, .cell t7.v, .cell t8.v, .cell t9.v, .cell t10.v, .cell t11.v, .cell t12.v, .cell t13.v, .cell t14.v, .cell t15.v, .cell t16.v, .cell t17.v, .cell t18.v, .cell t19.v, .cell t20.v, .cell t21.v, .cell t22.v, .cell t23.v, .cell t24.v, .cell t25.v, .cell t26.v, .cell t27.v, .cell t28.v, .cell t29.v, .cell t30.v, .cell t31.v, .cell t32.v, .cell t33.v, .cell t34.v, .cell t35.v, .cell t36.v, .cell t37.v, .cell t38.v, .cell t39.v, .cell t40.v, .cell t41.v, .cell t42.v, .cell t43.v, .cell t44.v, .cell t45.v, .cell t46.v, .cell t47.v, .cell t48.v, .cell t49.v, .cell t50.v, .cell t51.v, .cell t52.v, .cell t53.v, .cell t54.v, .cell t55.v, .cell t56.v, .cell t57.v, .cell t58.v, .cell t59.v])) (out := (.frame leaf))

set_option linter.unusedVariables false in
/-- `@inline lx_levels` (`guests/lean_ethereum.py`, line 3838):

```
@inline
def lx_levels(cur, pp, powers, his, out, w: Const, k: Const):
    # The LX_WINDOW path levels from LX_WINDOW * w, whose index bits are k's, from `cur`
    # into out. A node's order against its hinted sibling is k's bit, and a parent's
    # address holds `leaf_index >> (level + 1)`: his[w + 1] shifted up by what is left of
    # the window, k's higher bits added. Nothing is above the top window.
    for r in unroll(0, LX_WINDOW):
        tag = const(TW_NODE + ((LX_WINDOW * w + r) % LX_HEIGHT + 1) * HI_MUL + (LX_WINDOW * w + r) // LX_HEIGHT * LX_TOP + k // 2 ** (r + 1))
        if const(w + 1 == LX_WINDOWS):
            at = tag
        elif const(r + 1 == LX_WINDOW):
            at = his[w + 1] + tag
        else:
            at = his[w + 1] * powers[LX_WINDOW - 1 - r] + tag
        if const(r + 1 == LX_WINDOW):
            parent = out
        else:
            parent = StackBuf(1)
        sibling = hint_witness("lx_path")
        if const((k // 2 ** r) % 2 == 0):
            keccak([pp, at], [cur, sibling], parent)
        else:
            keccak([pp, at], [sibling, cur], parent)
        cur = parent[0]
    return
```
-/
def lxLevels (cur : Word) (pp : Word) (powers : List V) (his : List V) (out : List V) (w : Nat) (k : Nat) : B (Unit) := B.inline "lx_levels" do
  let mut cur := cur
  for r_k in [0:LX_WINDOW] do
    let tag := ((TW_NODE + (((((LX_WINDOW * w) + r_k) % LX_HEIGHT) + 1) * HI_MUL)) + ((((LX_WINDOW * w) + r_k) / LX_HEIGHT) * LX_TOP)) + (k / (2 ^ (r_k + 1)))
    let mut at' : FW := default
    if (w + 1) = LX_WINDOWS then
      at' := FW.c (lit tag)
    else
      if (r_k + 1) = LX_WINDOW then
        at' ← Ex.bind (.add (.v (cellOf his (w + 1))) (Ex.nat tag))
      else
        at' ← Ex.bind (.add (.mul (.v (cellOf his (w + 1))) (.v (cellOf powers ((LX_WINDOW - 1) - r_k)))) (Ex.nat tag))
    let mut parent : List V := default
    if (r_k + 1) = LX_WINDOW then
      parent := out
    else
      parent ← B.stackBuf 1
    let sibling ← hinted (B.witnessCell "lx_path")
    if ((k / (2 ^ r_k)) % 2) = 0 then
      B.keccak (a := (.words [.cell pp.v, (← at'.msg)])) (b := (.words [.cell cur.v, .cell sibling.v])) (out := (.frame parent))
    else
      B.keccak (a := (.words [.cell pp.v, (← at'.msg)])) (b := (.words [.cell sibling.v, .cell cur.v])) (out := (.frame parent))
    cur := cellOf parent 0

set_option linter.unusedVariables false in
/-- `@inline lx_top_window` (`guests/lean_ethereum.py`, line 3874):

```
@inline
def lx_top_window(cur, pp, powers, his, out, w: Const, k: Const):
    # The top window, nothing above it: his[w] is k alone.
    lx_levels(cur, pp, powers, his, out, w, k)
    return const(k)
```
-/
def lxTopWindow (cur : Word) (pp : Word) (powers : List V) (his : List V) (out : List V) (w : Nat) (k : Nat) (dsts : List V) : B (Unit) := B.inline "lx_top_window" do
  lxLevels cur pp powers his out w k
  B.constInto (cellOf dsts 0) (lit k)

set_option linter.unusedVariables false in
/-- `@inline lx_window` (`guests/lean_ethereum.py`, line 3865):

```
@inline
def lx_window(cur, pp, powers, his, out, w: Const, k: Const):
    # Window w of the path (`lx_levels`). Returns his[w] as his[w + 1] and k spell it,
    # which the dispatch writes where the hinted his[w] already is: so the index the
    # signature's addresses use is the one its path takes.
    lx_levels(cur, pp, powers, his, out, w, k)
    return his[w + 1] * powers[LX_WINDOW] + const(k)
```
-/
def lxWindow (cur : Word) (pp : Word) (powers : List V) (his : List V) (out : List V) (w : Nat) (k : Nat) (dsts : List V) : B (Unit) := B.inline "lx_window" do
  lxLevels cur pp powers his out w k
  Ex.into (cellOf dsts 0) (.add (.mul (.v (cellOf his (w + 1))) (.v (cellOf powers LX_WINDOW))) (.c (lit k)))

set_option linter.unusedVariables false in
/-- `@inline verify_lean_xmss` (`guests/lean_ethereum.py`, line 3881):

```
@inline
def verify_lean_xmss(signer, tags):
    # `signer` is one 4-cell entry of the leanXMSS coverage table: the pubkey's
    # merkle root and public parameter, then the message that pubkey signed. The
    # bottom layer signs the message, the top layer the bottom root.
    pp = signer[GEN]

    # The leaf index rides the signature, so every address is derived here from it. It
    # is advice: his[v] is `leaf_index >> (LX_WINDOW * v)`, a field's value, and each window
    # of LX_WINDOW bits is hinted again in the exponent, range checked and dispatched on
    # by the path (`lx_window`). Each arm pins his[w] to his[w + 1] and its own bits, and
    # the top one has nothing above it, so his[0] is the index the windows spell. Any
    # index is one some signature may carry; the digests and the root this signature
    # must reach bind it.
    his = StackBuf(LX_WINDOWS)
    hint_witness(his, "lx_index")
    windows = StackBuf(LX_WINDOWS)
    hint_witness(windows, "lx_windows")
    powers = StackBuf(LX_DIGIT_GROUP * CHAIN_STEPS + 1)
    for s in unroll(0, LX_DIGIT_GROUP * CHAIN_STEPS + 1):
        powers[s] = GEN ** s
    for layer in unroll(0, 2):
        if const(layer == 0):
            idx = his[0]
        else:
            idx = his[LX_LAYER_WINDOWS] + LX_TOP
        # D = Th(P, A, M | R), one block: 80 bytes at the bottom, and 64 at the top,
        # where M is the bottom root.
        rho = hint_witness("randomizer")
        digest = StackBuf(1)
        if const(layer == 0):
            keccak([pp, idx + TW_MSG], [signer[GEN ** 2], signer[GEN ** 3]], digest, tail=[rho, 0, 0, 0], len=80)
        else:
            keccak([pp, idx + TW_MSG], [root, rho], digest)

        # The codeword: LX_DIGIT_GROUP digits at a time, hinted in the exponent, range
        # checked and dispatched once, the arm walking every chain's remaining steps
        # and folding its digits in: their sums into a product that must be the
        # target sum, and the digits, each where the digest holds it, into D, which
        # also checks the digits past LX_V are zero.
        steps = StackBuf(CHAIN_STEPS)
        for st in unroll(0, CHAIN_STEPS):
            steps[st] = idx + const(TW_CHAIN + st * STEP_MUL)
        walks = StackBuf(LX_V * CHAIN_STEPS)
        digit_product = 1
        encoded = 0
        groups = StackBuf(LX_DIGIT_DISPATCHES)
        hint_witness(groups, "lx_digits")
        for p in unroll(0, LX_DIGIT_DISPATCHES - 1):
            assert log(groups[p]) < LX_DIGIT_GROUPS
        assert log(groups[LX_DIGIT_DISPATCHES - 1]) < LX_TAIL_GROUPS
        # Back to back, each arm entering the next dispatch. The last group's table is as
        # wide as the others, its range check what keeps it to LX_DIGIT_TAIL digits.
        for p in unroll(0, LX_DIGIT_DISPATCHES):
            digit_product, encoded = match(log(groups[p]), range(0, LX_DIGIT_GROUPS), lambda k: walk_group(steps, pp, walks, tags, LX_DIGIT_GROUP * p, LX_GROUP_SIZES[p], k, 1, powers, digit_product, encoded))
        digest[0] = encoded  # the digits, stored where D already is
        assert digit_product == GEN ** LX_TARGET_SUM

        # The one-time leaf, then the path to the layer's root, a window at a time.
        leaf = StackBuf(1)
        wots_leaf(pp, idx + TW_LEAF, walks, LX_V, leaf)
        cur = leaf[0]
        for v in unroll(0, LX_LAYER_WINDOWS):
            w = layer * LX_LAYER_WINDOWS + v
            out = StackBuf(1)
            assert log(windows[w]) < LX_WINDOW_ARMS
            if const(w + 1 == LX_WINDOWS):
                his[w] = match(log(windows[w]), range(0, LX_WINDOW_ARMS), lambda k: lx_top_window(cur, pp, powers, his, out, w, k))
            else:
                his[w] = match(log(windows[w]), range(0, LX_WINDOW_ARMS), lambda k: lx_window(cur, pp, powers, his, out, w, k))
            cur = out[0]
        root = cur
    assert root == signer[1]
    return
```
-/
def verifyLeanXmss (signer : Word) (tags : List V) : B (Unit) := B.inline "verify_lean_xmss" do
  let pp ← B.load signer 1
  let his ← B.stackBuf LX_WINDOWS
  B.witness "lx_index" (.stack his)
  let windows ← B.stackBuf LX_WINDOWS
  B.witness "lx_windows" (.stack windows)
  let powers ← B.stackBuf 13
  for s_k in [0:(LX_DIGIT_GROUP * CHAIN_STEPS) + 1] do
    B.constInto (cellOf powers s_k) (gpowE s_k)
  let mut w : Nat := default
  let mut out : List V := default
  let mut root : Word := default
  for layer_k in [0:2] do
    let mut idx : Word := default
    if layer_k = 0 then
      idx := cellOf his 0
    else
      idx ← Ex.lower (.add (.v (cellOf his LX_LAYER_WINDOWS)) (Ex.nat LX_TOP))
    let rho ← hinted (B.witnessCell "randomizer")
    let digest ← B.stackBuf 1
    if layer_k = 0 then
      B.keccak (a := (.words [.cell pp.v, .cell (← Ex.lower (.add (.w idx) (Ex.nat TW_MSG))).v])) (b := (.words [.cell (← B.load signer 2).v, .cell (← B.load signer 3).v])) (tail := some (.words [.cell rho.v, .zero, .zero, .zero])) (len := some 80) (out := (.frame digest))
    else
      B.keccak (a := (.words [.cell pp.v, .cell (← Ex.lower (.add (.w idx) (Ex.nat TW_MSG))).v])) (b := (.words [.cell root.v, .cell rho.v])) (out := (.frame digest))
    let steps ← B.stackBuf CHAIN_STEPS
    for st_k in [0:CHAIN_STEPS] do
      Ex.into (cellOf steps st_k) (.add (.w idx) (.c (lit (TW_CHAIN + (st_k * STEP_MUL)))))
    let walks ← B.stackBuf 174
    let mut digitProduct : FW := FW.c (lit 1)
    let mut encoded : FW := FW.c (lit 0)
    let groups ← B.stackBuf LX_DIGIT_DISPATCHES
    B.witness "lx_digits" (.stack groups)
    for p_k in [0:LX_DIGIT_DISPATCHES - 1] do
      let _ ← B.rangeCheck (cellOf groups p_k) LX_DIGIT_GROUPS
      pure ()
    let _ ← B.rangeCheck (cellOf groups (LX_DIGIT_DISPATCHES - 1)) LX_TAIL_GROUPS
    for p_k in [0:LX_DIGIT_DISPATCHES] do
      let t0 ← B.targets [none, none]
      if p_k + 1 < LX_DIGIT_DISPATCHES then
        B.chain
      else
        pure ()
      if p_k = 0 then
        Keccak.inlineArms
      else
        pure ()
      let _ ← B.matchArms (cellOf groups p_k) ((List.range LX_DIGIT_GROUPS).map fun arm => do
        walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) arm 1 powers digitProduct encoded [(cellOf t0 0).v, (cellOf t0 1).v])
      digitProduct := FW.w (cellOf t0 0)
      encoded := FW.w (cellOf t0 1)
    Ex.into (cellOf digest 0) encoded.ex
    B.assertEq (← FW.val digitProduct) (← B.const (gpowE LX_TARGET_SUM))
    let leaf ← B.stackBuf 1
    wotsLeaf pp (← Ex.lower (.add (.w idx) (Ex.nat TW_LEAF))) walks LX_V leaf
    let mut cur := cellOf leaf 0
    for v_k in [0:LX_LAYER_WINDOWS] do
      w := (layer_k * LX_LAYER_WINDOWS) + v_k
      out ← B.stackBuf 1
      let _ ← B.rangeCheck (cellOf windows w) LX_WINDOW_ARMS
      if (w + 1) = LX_WINDOWS then
        let t1 ← B.targets [some (cellOf his w).v]
        Keccak.inlineArms
        let _ ← B.matchArms (cellOf windows w) ((List.range LX_WINDOW_ARMS).map fun arm => do
          lxTopWindow cur pp powers his out w arm [(cellOf t1 0).v])
        pure ()
      else
        let t1 ← B.targets [some (cellOf his w).v]
        Keccak.inlineArms
        let _ ← B.matchArms (cellOf windows w) ((List.range LX_WINDOW_ARMS).map fun arm => do
          lxWindow cur pp powers his out w arm [(cellOf t1 0).v])
        pure ()
      cur := cellOf out 0
    root := cur
  B.assertEq root (← B.load signer 0)

end
end LeanVM.Dsl.Gen
