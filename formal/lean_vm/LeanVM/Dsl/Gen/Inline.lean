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
  B.addInto (cellOf dsts 0) a (← B.mul (← B.const (lit 18446744073709551616)) b)

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
def novelEval_5 (coefs : Word) (ws : List V) (n : Nat) (nbits : Nat) : B (Word) := B.inline "novel_eval" do
  let mut buf : List V := default
  if (nbits / 4) = 0 then
    pure () -- no use of this definition takes this branch
  else
    if nbits = 4 then
      pure () -- no use of this definition takes this branch
    else
      if nbits = 5 then
        pure () -- no use of this definition takes this branch
      else
        buf ← B.stackBuf 128
  let mut out : Word := default
  if nbits = 0 then
    pure () -- no use of this definition takes this branch
  else
    let mut lo : Word := default
    let mut hi : Word := default
    let mut src : Nat := default
    for i_k in [0:5] do
      let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
      let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
      for m_k in [0:(nIn + 1) / 2] do
        if i_k = 0 then
          lo ← B.load coefs (2 * m_k)
          if (((2 * m_k) + 1) / nIn) = 0 then
            hi ← B.load coefs ((2 * m_k) + 1)
          else
            pure () -- no use of this definition takes this branch
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
    let i_k := 5
    let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
    let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
    let m_k := 0
    if i_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      src := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 2) - i_k))
      lo := cellOf buf (src + (2 * m_k))
      if (((2 * m_k) + 1) / nIn) = 0 then
        hi := cellOf buf ((src + (2 * m_k)) + 1)
      else
        pure () -- no use of this definition takes this branch
    if (((2 * m_k) + 1) / nIn) = 0 then
      B.addInto (cellOf buf (at' + m_k)) lo (← B.mul (cellOf ws i_k) hi)
    else
      pure () -- no use of this definition takes this branch
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
def openingQuery_6 (cap : Word) (flags : Word) (coefs : Word) (hs : Word) (x : Word) (wins : Word) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : B (E) := B.inline "opening_query" do
  let interleave := 2 ^ folds
  let mut row : List V := default
  let mut acc : List V := default
  if (folds / 5) = 0 then
    row ← B.stackBuf 16
    acc ← B.stackBuf 16
  else
    pure () -- no use of this definition takes this branch
  B.witness "merkle_leaf_rows" (.stack (row.take interleave))
  let leafHashState ← B.stackBuf 2
  if base = 1 then
    pure () -- no use of this definition takes this branch
  else
    B.keccakCells (cells := (.cells (.frame (row.take leafCells)))) (out := (.frame leafHashState))
  let _ ← B.call (instName "walk_path" [.L (depth - capDepth), .L capDepth]) [(cellOf leafHashState 0).v, (cellOf leafHashState 1).v, wins.v, cap.v, flags.v] 0
  let mut src : Nat := default
  for j_k in [0:3] do
    let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
    let nOut := 2 ^ ((folds - 1) - j_k)
    for m_k in [0:nOut] do
      if j_k = 0 then
        if base = 1 then
          pure () -- no use of this definition takes this branch
        else
          B.addInto (cellOf acc m_k) (cellOf row ((2 * m_k) + 1)) (← B.mul t (cellOf row (2 * m_k)))
      else
        src := interleave - (4 * nOut)
        B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let j_k := 3
  let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
  let nOut := 2 ^ ((folds - 1) - j_k)
  let m_k := 0
  if j_k = 0 then
    pure () -- no use of this definition takes this branch
  else
    src := interleave - (4 * nOut)
    B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let value := cellOf acc (interleave - 2)
  let mut out : Nat := default
  if final = 1 then
    let ws ← B.stackBuf 6
    B.copy (cellOf ws 0) x
    for i_k in [1:mu + 1] do
      B.mulInto (cellOf ws i_k) (cellOf ws (i_k - 1)) (← B.add (cellOf ws (i_k - 1)) (← B.const (arrWord VANISH_BY_COLS ((vanish + i_k) - 1))))
    let t0 ← novelEval_5 hs ws nHs hsBits
    B.assertEq value t0
    out := 0
  else
    pure () -- no use of this definition takes this branch
  return lit out

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
def novelEval_4 (coefs : Word) (ws : List V) (n : Nat) (nbits : Nat) : B (Word) := B.inline "novel_eval" do
  let mut buf : List V := default
  if (nbits / 4) = 0 then
    pure () -- no use of this definition takes this branch
  else
    if nbits = 4 then
      pure () -- no use of this definition takes this branch
    else
      if nbits = 5 then
        buf ← B.stackBuf 64
      else
        pure () -- no use of this definition takes this branch
  let mut out : Word := default
  if nbits = 0 then
    pure () -- no use of this definition takes this branch
  else
    let mut lo : Word := default
    let mut hi : Word := default
    let mut src : Nat := default
    for i_k in [0:4] do
      let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
      let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
      for m_k in [0:(nIn + 1) / 2] do
        if i_k = 0 then
          lo ← B.load coefs (2 * m_k)
          if (((2 * m_k) + 1) / nIn) = 0 then
            hi ← B.load coefs ((2 * m_k) + 1)
          else
            pure () -- no use of this definition takes this branch
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
    let i_k := 4
    let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
    let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
    let m_k := 0
    if i_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      src := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 2) - i_k))
      lo := cellOf buf (src + (2 * m_k))
      if (((2 * m_k) + 1) / nIn) = 0 then
        hi := cellOf buf ((src + (2 * m_k)) + 1)
      else
        pure () -- no use of this definition takes this branch
    if (((2 * m_k) + 1) / nIn) = 0 then
      B.addInto (cellOf buf (at' + m_k)) lo (← B.mul (cellOf ws i_k) hi)
    else
      pure () -- no use of this definition takes this branch
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
def openingQuery_5 (cap : Word) (flags : Word) (coefs : Word) (hs : Word) (x : Word) (wins : Word) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : B (E) := B.inline "opening_query" do
  let interleave := 2 ^ folds
  let mut row : List V := default
  let mut acc : List V := default
  if (folds / 5) = 0 then
    row ← B.stackBuf 16
    acc ← B.stackBuf 16
  else
    pure () -- no use of this definition takes this branch
  B.witness "merkle_leaf_rows" (.stack (row.take interleave))
  let leafHashState ← B.stackBuf 2
  if base = 1 then
    pure () -- no use of this definition takes this branch
  else
    B.keccakCells (cells := (.cells (.frame (row.take leafCells)))) (out := (.frame leafHashState))
  let _ ← B.call (instName "walk_path" [.L (depth - capDepth), .L capDepth]) [(cellOf leafHashState 0).v, (cellOf leafHashState 1).v, wins.v, cap.v, flags.v] 0
  let mut src : Nat := default
  for j_k in [0:3] do
    let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
    let nOut := 2 ^ ((folds - 1) - j_k)
    for m_k in [0:nOut] do
      if j_k = 0 then
        if base = 1 then
          pure () -- no use of this definition takes this branch
        else
          B.addInto (cellOf acc m_k) (cellOf row ((2 * m_k) + 1)) (← B.mul t (cellOf row (2 * m_k)))
      else
        src := interleave - (4 * nOut)
        B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let j_k := 3
  let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
  let nOut := 2 ^ ((folds - 1) - j_k)
  let m_k := 0
  if j_k = 0 then
    pure () -- no use of this definition takes this branch
  else
    src := interleave - (4 * nOut)
    B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let value := cellOf acc (interleave - 2)
  let mut out : Nat := default
  if final = 1 then
    let ws ← B.stackBuf 6
    B.copy (cellOf ws 0) x
    for i_k in [1:mu + 1] do
      B.mulInto (cellOf ws i_k) (cellOf ws (i_k - 1)) (← B.add (cellOf ws (i_k - 1)) (← B.const (arrWord VANISH_BY_COLS ((vanish + i_k) - 1))))
    let t0 ← novelEval_4 hs ws nHs hsBits
    B.assertEq value t0
    out := 0
  else
    pure () -- no use of this definition takes this branch
  return lit out

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
def novelEval_3 (coefs : Word) (ws : List V) (n : Nat) (nbits : Nat) : B (Word) := B.inline "novel_eval" do
  let mut buf : List V := default
  if (nbits / 4) = 0 then
    pure () -- no use of this definition takes this branch
  else
    if nbits = 4 then
      buf ← B.stackBuf 32
    else
      pure () -- no use of this definition takes this branch
  let mut out : Word := default
  if nbits = 0 then
    pure () -- no use of this definition takes this branch
  else
    let mut lo : Word := default
    let mut hi : Word := default
    let mut src : Nat := default
    for i_k in [0:3] do
      let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
      let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
      for m_k in [0:(nIn + 1) / 2] do
        if i_k = 0 then
          lo ← B.load coefs (2 * m_k)
          if (((2 * m_k) + 1) / nIn) = 0 then
            hi ← B.load coefs ((2 * m_k) + 1)
          else
            pure () -- no use of this definition takes this branch
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
    let i_k := 3
    let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
    let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
    let m_k := 0
    if i_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      src := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 2) - i_k))
      lo := cellOf buf (src + (2 * m_k))
      if (((2 * m_k) + 1) / nIn) = 0 then
        hi := cellOf buf ((src + (2 * m_k)) + 1)
      else
        pure () -- no use of this definition takes this branch
    if (((2 * m_k) + 1) / nIn) = 0 then
      B.addInto (cellOf buf (at' + m_k)) lo (← B.mul (cellOf ws i_k) hi)
    else
      pure () -- no use of this definition takes this branch
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
def openingQuery_4 (cap : Word) (flags : Word) (coefs : Word) (hs : Word) (x : Word) (wins : Word) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : B (E) := B.inline "opening_query" do
  let interleave := 2 ^ folds
  let mut row : List V := default
  let mut acc : List V := default
  if (folds / 5) = 0 then
    row ← B.stackBuf 16
    acc ← B.stackBuf 16
  else
    pure () -- no use of this definition takes this branch
  B.witness "merkle_leaf_rows" (.stack (row.take interleave))
  let leafHashState ← B.stackBuf 2
  if base = 1 then
    pure () -- no use of this definition takes this branch
  else
    B.keccakCells (cells := (.cells (.frame (row.take leafCells)))) (out := (.frame leafHashState))
  let _ ← B.call (instName "walk_path" [.L (depth - capDepth), .L capDepth]) [(cellOf leafHashState 0).v, (cellOf leafHashState 1).v, wins.v, cap.v, flags.v] 0
  let mut src : Nat := default
  for j_k in [0:3] do
    let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
    let nOut := 2 ^ ((folds - 1) - j_k)
    for m_k in [0:nOut] do
      if j_k = 0 then
        if base = 1 then
          pure () -- no use of this definition takes this branch
        else
          B.addInto (cellOf acc m_k) (cellOf row ((2 * m_k) + 1)) (← B.mul t (cellOf row (2 * m_k)))
      else
        src := interleave - (4 * nOut)
        B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let j_k := 3
  let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
  let nOut := 2 ^ ((folds - 1) - j_k)
  let m_k := 0
  if j_k = 0 then
    pure () -- no use of this definition takes this branch
  else
    src := interleave - (4 * nOut)
    B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let value := cellOf acc (interleave - 2)
  let mut out : Nat := default
  if final = 1 then
    let ws ← B.stackBuf 6
    B.copy (cellOf ws 0) x
    for i_k in [1:mu + 1] do
      B.mulInto (cellOf ws i_k) (cellOf ws (i_k - 1)) (← B.add (cellOf ws (i_k - 1)) (← B.const (arrWord VANISH_BY_COLS ((vanish + i_k) - 1))))
    let t0 ← novelEval_3 hs ws nHs hsBits
    B.assertEq value t0
    out := 0
  else
    pure () -- no use of this definition takes this branch
  return lit out

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
                        pure () -- no use of this definition takes this branch

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
def queryWindowSplit_2 (word' : Word) (wins : List V) (tabs : Word) (parts : List V) (at' : Nat) (start : Nat) (width : Nat) (cut : Nat) : B (Unit) := B.inline "query_window_split" do
  B.hintWindowsExp (.stack (parts.take (2 + 1))) word' start cut 1 2
  B.hintWindowsExp (.stack (parts.take (3 + 1))) word' (start + cut) (width - cut) 1 3
  let lo := cellOf parts 2
  let hi := cellOf parts 3
  assertWindow lo cut
  assertWindow hi (width - cut)
  let mut hp := hi
  hp ← B.mul hp hp
  B.mulInto (cellOf wins at') lo hp
  B.loadInto (cellOf parts 0) (← B.mul tabs lo) 0
  B.loadInto (cellOf parts 1) (← B.mul tabs hi) 0

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
    pure () -- no use of this definition takes this branch
  let mut out : Word := default
  if nbits = 0 then
    pure () -- no use of this definition takes this branch
  else
    let mut lo : Word := default
    let mut hi : Word := default
    let mut src : Nat := default
    for i_k in [0:2] do
      let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
      let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
      for m_k in [0:(nIn + 1) / 2] do
        if i_k = 0 then
          lo ← B.load coefs (2 * m_k)
          if (((2 * m_k) + 1) / nIn) = 0 then
            hi ← B.load coefs ((2 * m_k) + 1)
          else
            pure () -- no use of this definition takes this branch
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
    let i_k := 2
    let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
    let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
    let m_k := 0
    if i_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      src := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 2) - i_k))
      lo := cellOf buf (src + (2 * m_k))
      if (((2 * m_k) + 1) / nIn) = 0 then
        hi := cellOf buf ((src + (2 * m_k)) + 1)
      else
        pure () -- no use of this definition takes this branch
    if (((2 * m_k) + 1) / nIn) = 0 then
      B.addInto (cellOf buf (at' + m_k)) lo (← B.mul (cellOf ws i_k) hi)
    else
      pure () -- no use of this definition takes this branch
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
def openingQuery_3 (cap : Word) (flags : Word) (coefs : Word) (hs : Word) (x : Word) (wins : Word) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : B (E) := B.inline "opening_query" do
  let interleave := 2 ^ folds
  let mut row : List V := default
  let mut acc : List V := default
  if (folds / 5) = 0 then
    row ← B.stackBuf 16
    acc ← B.stackBuf 16
  else
    pure () -- no use of this definition takes this branch
  B.witness "merkle_leaf_rows" (.stack (row.take interleave))
  let leafHashState ← B.stackBuf 2
  if base = 1 then
    pure () -- no use of this definition takes this branch
  else
    B.keccakCells (cells := (.cells (.frame (row.take leafCells)))) (out := (.frame leafHashState))
  let _ ← B.call (instName "walk_path" [.L (depth - capDepth), .L capDepth]) [(cellOf leafHashState 0).v, (cellOf leafHashState 1).v, wins.v, cap.v, flags.v] 0
  let mut src : Nat := default
  for j_k in [0:3] do
    let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
    let nOut := 2 ^ ((folds - 1) - j_k)
    for m_k in [0:nOut] do
      if j_k = 0 then
        if base = 1 then
          pure () -- no use of this definition takes this branch
        else
          B.addInto (cellOf acc m_k) (cellOf row ((2 * m_k) + 1)) (← B.mul t (cellOf row (2 * m_k)))
      else
        src := interleave - (4 * nOut)
        B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let j_k := 3
  let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
  let nOut := 2 ^ ((folds - 1) - j_k)
  let m_k := 0
  if j_k = 0 then
    pure () -- no use of this definition takes this branch
  else
    src := interleave - (4 * nOut)
    B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let value := cellOf acc (interleave - 2)
  let mut out : Nat := default
  if final = 1 then
    let ws ← B.stackBuf 6
    B.copy (cellOf ws 0) x
    for i_k in [1:mu + 1] do
      B.mulInto (cellOf ws i_k) (cellOf ws (i_k - 1)) (← B.add (cellOf ws (i_k - 1)) (← B.const (arrWord VANISH_BY_COLS ((vanish + i_k) - 1))))
    let t0 ← novelEval hs ws nHs hsBits
    B.assertEq value t0
    out := 0
  else
    pure () -- no use of this definition takes this branch
  return lit out

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
def openingQuery_2 (cap : Word) (flags : Word) (coefs : Word) (hs : Word) (x : Word) (wins : Word) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : B (Word) := B.inline "opening_query" do
  let interleave := 2 ^ folds
  let mut row : List V := default
  let mut acc : List V := default
  if (folds / 5) = 0 then
    row ← B.stackBuf 16
    acc ← B.stackBuf 16
  else
    pure () -- no use of this definition takes this branch
  B.witness "merkle_leaf_rows" (.stack (row.take interleave))
  let leafHashState ← B.stackBuf 2
  if base = 1 then
    pure () -- no use of this definition takes this branch
  else
    B.keccakCells (cells := (.cells (.frame (row.take leafCells)))) (out := (.frame leafHashState))
  let _ ← B.call (instName "walk_path" [.L (depth - capDepth), .L capDepth]) [(cellOf leafHashState 0).v, (cellOf leafHashState 1).v, wins.v, cap.v, flags.v] 0
  let mut src : Nat := default
  for j_k in [0:3] do
    let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
    let nOut := 2 ^ ((folds - 1) - j_k)
    for m_k in [0:nOut] do
      if j_k = 0 then
        if base = 1 then
          pure () -- no use of this definition takes this branch
        else
          B.addInto (cellOf acc m_k) (cellOf row ((2 * m_k) + 1)) (← B.mul t (cellOf row (2 * m_k)))
      else
        src := interleave - (4 * nOut)
        B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let j_k := 3
  let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
  let nOut := 2 ^ ((folds - 1) - j_k)
  let m_k := 0
  if j_k = 0 then
    pure () -- no use of this definition takes this branch
  else
    src := interleave - (4 * nOut)
    B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let value := cellOf acc (interleave - 2)
  let mut out : Word := default
  if final = 1 then
    pure () -- no use of this definition takes this branch
  else
    out := value
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
def openingQuery (cap : Word) (flags : Word) (coefs : Word) (hs : Word) (x : Word) (wins : Word) (base : Nat) (folds : Nat) (leafCells : Nat) (depth : Nat) (capDepth : Nat) (mu : Nat) (vanish : Nat) (nHs : Nat) (hsBits : Nat) (final : Nat) : B (Word) := B.inline "opening_query" do
  let interleave := 2 ^ folds
  let mut row : List V := default
  let mut acc : List V := default
  if (folds / 5) = 0 then
    pure () -- no use of this definition takes this branch
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
    pure () -- no use of this definition takes this branch
  let _ ← B.call (instName "walk_path" [.L (depth - capDepth), .L capDepth]) [(cellOf leafHashState 0).v, (cellOf leafHashState 1).v, wins.v, cap.v, flags.v] 0
  let mut src : Nat := default
  for j_k in [0:5] do
    let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
    let nOut := 2 ^ ((folds - 1) - j_k)
    for m_k in [0:nOut] do
      if j_k = 0 then
        if base = 1 then
          B.addInto (cellOf acc m_k) (cellOf row ((interleave - 2) - (2 * m_k))) (← B.mul t (cellOf row ((interleave - 1) - (2 * m_k))))
        else
          pure () -- no use of this definition takes this branch
      else
        src := interleave - (4 * nOut)
        B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let j_k := 5
  let t ← B.add (← B.load coefs (2 * j_k)) (← B.mul (← B.load coefs ((2 * j_k) + 1)) x)
  let nOut := 2 ^ ((folds - 1) - j_k)
  let m_k := 0
  if j_k = 0 then
    pure () -- no use of this definition takes this branch
  else
    src := interleave - (4 * nOut)
    B.addInto (cellOf acc ((interleave - (2 * nOut)) + m_k)) (cellOf acc ((src + (2 * m_k)) + 1)) (← B.mul t (cellOf acc (src + (2 * m_k))))
  let value := cellOf acc (interleave - 2)
  let mut out : Word := default
  if final = 1 then
    pure () -- no use of this definition takes this branch
  else
    out := value
  return out

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
def novelEval_2 (coefs : Word) (ws : List V) (n : Nat) (nbits : Nat) : B (Word) := B.inline "novel_eval" do
  let mut buf : List V := default
  if (nbits / 4) = 0 then
    buf ← B.stackBuf 16
  else
    pure () -- no use of this definition takes this branch
  let mut out : Word := default
  if nbits = 0 then
    pure () -- no use of this definition takes this branch
  else
    let mut lo : Word := default
    let mut hi : Word := default
    let mut src : Nat := default
    let i_k := 0
    let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
    let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
    for m_k in [0:(nIn + 1) / 2] do
      if i_k = 0 then
        lo ← B.load coefs (2 * m_k)
        if (((2 * m_k) + 1) / nIn) = 0 then
          hi ← B.load coefs ((2 * m_k) + 1)
        else
          pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
      if (((2 * m_k) + 1) / nIn) = 0 then
        B.addInto (cellOf buf (at' + m_k)) lo (← B.mul (cellOf ws i_k) hi)
      else
        pure () -- no use of this definition takes this branch
    let i_k := 1
    let nIn := ((n + (2 ^ i_k)) - 1) / (2 ^ i_k)
    let at' := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 1) - i_k))
    let m_k := 0
    if i_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      src := (2 ^ (nbits + 1)) - (2 ^ ((nbits + 2) - i_k))
      lo := cellOf buf (src + (2 * m_k))
      if (((2 * m_k) + 1) / nIn) = 0 then
        hi := cellOf buf ((src + (2 * m_k)) + 1)
      else
        pure () -- no use of this definition takes this branch
    if (((2 * m_k) + 1) / nIn) = 0 then
      B.addInto (cellOf buf (at' + m_k)) lo (← B.mul (cellOf ws i_k) hi)
    else
      pure () -- no use of this definition takes this branch
    out := cellOf buf ((2 ^ (nbits + 1)) - 4)
  return out

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
def residualQuery_2 (basisChain : Word) (rowD : Word) (hs : Word) (nCols : Nat) (nHs : Nat) (hsBits : Nat) : B (Word × Word) := B.inline "residual_query" do
  let ws ← B.stackBuf HIGH_BITS_CAP
  B.copy (cellOf ws 0) basisChain
  let mut prefixEq ← B.add (← B.load rowD 0) basisChain
  let mut basisChain := basisChain
  for t_k in [1:nCols + 1] do
    if (t_k / HIGH_BITS_CAP) = 0 then
      B.mulInto (cellOf ws t_k) basisChain (← B.add basisChain (← B.const (arrWord VANISH_BY_COLS ((((nCols * (nCols + 1)) / 2) + t_k) - 1))))
      basisChain := cellOf ws t_k
    else
      basisChain ← B.mul basisChain (← B.add basisChain (← B.const (arrWord VANISH_BY_COLS ((((nCols * (nCols + 1)) / 2) + t_k) - 1))))
    if t_k ≠ nCols then
      prefixEq ← B.mul prefixEq (← B.add (← B.load rowD t_k) basisChain)
    else
      pure ()
  let t0 ← novelEval_2 hs ws nHs hsBits
  let t1 ← B.mul basisChain t0
  return (prefixEq, t1)

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
      B.mulInto (cellOf ws t_k) basisChain (← B.add basisChain (← B.const (arrWord VANISH_BY_COLS ((((nCols * (nCols + 1)) / 2) + t_k) - 1))))
      basisChain := cellOf ws t_k
    else
      basisChain ← B.mul basisChain (← B.add basisChain (← B.const (arrWord VANISH_BY_COLS ((((nCols * (nCols + 1)) / 2) + t_k) - 1))))
    if t_k ≠ nCols then
      prefixEq ← B.mul prefixEq (← B.add (← B.load rowD t_k) basisChain)
    else
      pure ()
  let t0 ← novelEval hs ws nHs hsBits
  let t1 ← B.mul basisChain t0
  return (prefixEq, t1)

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
  let mut tag : Nat := default
  if lx = 1 then
    if i = 0 then
      tag := 0
    else
      pure () -- no use of this definition takes this branch
  else
    pure () -- no use of this definition takes this branch
  if k = CHAIN_STEPS then
    B.witness "chain_starts" (.stack ((walks.drop (((i + 1) * CHAIN_STEPS) - 1)).take (((i + 1) * CHAIN_STEPS) - (((i + 1) * CHAIN_STEPS) - 1))))
  else
    let mut value ← hinted (B.witnessCell "chain_starts")
    for s_k in [k:CHAIN_STEPS] do
      let o := (CHAIN_STEPS * i) + s_k
      if lx = 1 then
        B.keccak (a := (.words [.cell pp.v, .cell (cellOf at' s_k).v])) (b := (.words [.cell value.v, .zero])) (out := (.frame ((walks.drop o).take ((o + 1) - o))))
      else
        pure () -- no use of this definition takes this branch
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
def childClaimsMono_2 (cov : Word) (ent : Word) (mark : Word) (blk : List V) (out : List V) (n : Nat) : B (Unit) := B.inline "child_claims_mono" do
  let mut cov := cov
  let mut ent := ent
  let j_k := 0
  let gap ← hinted (B.witnessCell "child_claim_gap")
  let _ ← B.assertGpow gap
  cov ← B.mul cov gap
  let gap2 ← B.mul gap gap
  ent ← B.mul ent (← B.mul gap2 gap2)
  B.store cov j_k mark
  for c_k in [0:4] do
    B.loadInto (cellOf blk ((4 * j_k) + c_k)) ent ((4 * j_k) + c_k)
  B.mulInto (cellOf out 0) cov (← B.const (gpowE n))
  B.mulInto (cellOf out 1) ent (← B.const (gpowE (4 * n)))

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
def childClaims_3 (entriesPtr : Word) (region : Word) (marks : Word) (lastG : Word) (blk : List V) (n : Nat) : B (Unit) := B.inline "child_claims" do
  let j_k := 0
  let offHint ← hinted (B.witnessCell "child_claim_index")
  let t0 ← B.shifted lastG (1 - 1)
  let _ ← B.rangeCheckK offHint t0
  B.store (← B.mul region offHint) 0 marks
  let entry ← B.mul entriesPtr (← B.pow offHint 4)
  for c_k in [0:4] do
    B.loadInto (cellOf blk ((4 * j_k) + c_k)) entry c_k
  let j_k := 1
  let offHint ← hinted (B.witnessCell "child_claim_index")
  let t0 ← B.shifted lastG (1 - 1)
  let _ ← B.rangeCheckK offHint t0
  let t1 ← B.shifted marks j_k
  B.store (← B.mul region offHint) 0 t1
  let entry ← B.mul entriesPtr (← B.pow offHint 4)
  for c_k in [0:4] do
    B.loadInto (cellOf blk ((4 * j_k) + c_k)) entry c_k

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
def childClaims_2 (entriesPtr : Word) (region : Word) (marks : Word) (lastG : Word) (blk : List V) (n : Nat) : B (Unit) := B.inline "child_claims" do
  let j_k := 0
  let offHint ← hinted (B.witnessCell "child_claim_index")
  let t0 ← B.shifted lastG (1 - 1)
  let _ ← B.rangeCheckK offHint t0
  B.store (← B.mul region offHint) 0 marks
  let entry ← B.mul entriesPtr (← B.pow offHint 4)
  for c_k in [0:4] do
    B.loadInto (cellOf blk ((4 * j_k) + c_k)) entry c_k

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
def keccakForm_2 (lanes : Word) (shifts : List V) (fLanes : List V) (fOff : Nat) (dsts : List V) : B (Unit) := B.inline "keccak_form" do
  let total := 0
  let column ← B.stackBuf 5
  let columnNext ← B.stackBuf 5
  let fColumn ← B.stackBuf 5
  let mut laneWeight : Word := default
  let mut moved : Word := default
  let mut fWeight : Word := default
  let mut total_word : Word := default
  let x_k := 0
  let acc := 0
  let accNext := 0
  let fAcc := 0
  let mut acc_word : Word := default
  let mut accNext_word : Word := default
  let mut fAcc_word : Word := default
  let y_k := 0
  laneWeight ← B.load lanes (arrInt KECCAK_PI (x_k + (5 * y_k)))
  moved ← B.mul laneWeight (cellOf shifts (arrInt KECCAK_RHO (x_k + (5 * y_k))))
  fWeight := cellOf fLanes ((fOff + x_k) + (5 * y_k))
  total_word ← B.mul fWeight moved
  acc_word := moved
  accNext_word ← B.mul laneWeight (cellOf shifts (((arrInt KECCAK_RHO (x_k + (5 * y_k))) + 1) % 64))
  fAcc_word := fWeight
  for y_k in [1:5] do
    laneWeight ← B.load lanes (arrInt KECCAK_PI (x_k + (5 * y_k)))
    moved ← B.mul laneWeight (cellOf shifts (arrInt KECCAK_RHO (x_k + (5 * y_k))))
    fWeight := cellOf fLanes ((fOff + x_k) + (5 * y_k))
    total_word ← B.add total_word (← B.mul fWeight moved)
    acc_word ← B.add acc_word moved
    accNext_word ← B.add accNext_word (← B.mul laneWeight (cellOf shifts (((arrInt KECCAK_RHO (x_k + (5 * y_k))) + 1) % 64)))
    fAcc_word ← B.add fAcc_word fWeight
  B.copy (cellOf column x_k) acc_word
  B.copy (cellOf columnNext x_k) accNext_word
  B.copy (cellOf fColumn x_k) fAcc_word
  for x_k in [1:5] do
    let acc := 0
    let accNext := 0
    let fAcc := 0
    let y_k := 0
    laneWeight ← B.load lanes (arrInt KECCAK_PI (x_k + (5 * y_k)))
    moved ← B.mul laneWeight (cellOf shifts (arrInt KECCAK_RHO (x_k + (5 * y_k))))
    fWeight := cellOf fLanes ((fOff + x_k) + (5 * y_k))
    total_word ← B.add total_word (← B.mul fWeight moved)
    acc_word := moved
    accNext_word ← B.mul laneWeight (cellOf shifts (((arrInt KECCAK_RHO (x_k + (5 * y_k))) + 1) % 64))
    fAcc_word := fWeight
    for y_k in [1:5] do
      laneWeight ← B.load lanes (arrInt KECCAK_PI (x_k + (5 * y_k)))
      moved ← B.mul laneWeight (cellOf shifts (arrInt KECCAK_RHO (x_k + (5 * y_k))))
      fWeight := cellOf fLanes ((fOff + x_k) + (5 * y_k))
      total_word ← B.add total_word (← B.mul fWeight moved)
      acc_word ← B.add acc_word moved
      accNext_word ← B.add accNext_word (← B.mul laneWeight (cellOf shifts (((arrInt KECCAK_RHO (x_k + (5 * y_k))) + 1) % 64)))
      fAcc_word ← B.add fAcc_word fWeight
    B.copy (cellOf column x_k) acc_word
    B.copy (cellOf columnNext x_k) accNext_word
    B.copy (cellOf fColumn x_k) fAcc_word
  for x_k in [0:5] do
    total_word ← B.add total_word (← B.mul (cellOf fColumn x_k) (← B.add (cellOf column ((x_k + 1) % 5)) (cellOf columnNext ((x_k + 4) % 5))))
  B.copy (cellOf dsts 0) total_word

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
    let aT1 ← B.add (← B.const 1) aT
    let bT1 ← B.add (← B.const 1) bT
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
def eqtree (pointPtr : Word) (out : Word) (nCoords : Nat) : B (Unit) := B.inline "eqtree" do
  let r0 ← B.load pointPtr 0
  B.store out 0 (← B.add (← B.const 1) r0)
  B.store out 1 r0
  let mut pw : Word := default
  for t_k in [1:nCoords] do
    let rt ← B.load pointPtr t_k
    let onePlusRt ← B.add (← B.const 1) rt
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
def eqtreeFrame_3 (pointPtr : Shifted) (out : List V) (nCoords : Nat) (count : Nat) : B (Unit) := B.inline "eqtree_frame" do
  let r0 ← B.load pointPtr.base pointPtr.exp
  B.addInto (cellOf out 0) (← B.const 1) r0
  B.copy (cellOf out 1) r0
  let mut pw : Word := default
  for t_k in [1:nCoords] do
    let rt ← B.load pointPtr.base (pointPtr.exp + t_k)
    let onePlusRt ← B.add (← B.const 1) rt
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
def selGNibble_3 (out : Word) (gs : Word) (width : Nat) : B (Unit) := B.inline "sel_g_nibble" do
  let vals ← B.stackBuf 16
  B.constInto (cellOf vals 0) 1
  B.loadInto (cellOf vals 1) gs 0
  let t_k := 1
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
def selEqNibble_3 (out : Word) (z : Word) (z1 : Word) (width : Nat) : B (Unit) := B.inline "sel_eq_nibble" do
  let levels ← B.stackBuf SEL_EQ_STRIDE
  B.loadInto (cellOf levels 0) z1 0
  B.loadInto (cellOf levels 1) z 0
  let t_k := 1
  let r ← B.load z t_k
  let r1 ← B.load z1 t_k
  for i_k in [0:2 ^ t_k] do
    B.mulInto (cellOf levels (((2 ^ (t_k + 1)) - 2) + i_k)) (cellOf levels (((2 ^ t_k) - 2) + i_k)) r1
    B.mulInto (cellOf levels ((((2 ^ (t_k + 1)) - 2) + (2 ^ t_k)) + i_k)) (cellOf levels (((2 ^ t_k) - 2) + i_k)) r
  for i_k in [0:(2 ^ (width + 1)) - 2] do
    B.store out i_k (cellOf levels i_k)

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
def selGNibble_2 (out : Word) (gs : Word) (width : Nat) : B (Unit) := B.inline "sel_g_nibble" do
  let vals ← B.stackBuf 16
  B.constInto (cellOf vals 0) 1
  B.loadInto (cellOf vals 1) gs 0
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
def selEqNibble_2 (out : Word) (z : Word) (z1 : Word) (width : Nat) : B (Unit) := B.inline "sel_eq_nibble" do
  let levels ← B.stackBuf SEL_EQ_STRIDE
  B.loadInto (cellOf levels 0) z1 0
  B.loadInto (cellOf levels 1) z 0
  for i_k in [0:(2 ^ (width + 1)) - 2] do
    B.store out i_k (cellOf levels i_k)

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
def fsPack_2 (rate : List V) (k : Nat) (x : E) (tag : Nat) : B (Unit) := B.inline "fs_pack" do
  B.constInto (cellOf rate (2 * k)) x
  B.constInto (cellOf rate ((2 * k) + 1)) ((lit Y_TOWER) * (lit tag))

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
  B.mulInto (cellOf out 0) cov (← B.const (gpowE n))
  B.mulInto (cellOf out 1) ent (← B.const (gpowE (4 * n)))

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
  let j_k := 0
  let offHint ← hinted (B.witnessCell "child_claim_index")
  let t0 ← B.shifted lastG (1 - 1)
  let _ ← B.rangeCheckK offHint t0
  B.store (← B.mul region offHint) 0 marks
  let entry ← B.mul entriesPtr (← B.pow offHint 4)
  for c_k in [0:4] do
    B.loadInto (cellOf blk ((4 * j_k) + c_k)) entry c_k
  for j_k in [1:n] do
    let offHint ← hinted (B.witnessCell "child_claim_index")
    let t0 ← B.shifted lastG (1 - 1)
    let _ ← B.rangeCheckK offHint t0
    let t1 ← B.shifted marks j_k
    B.store (← B.mul region offHint) 0 t1
    let entry ← B.mul entriesPtr (← B.pow offHint 4)
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
      value ← B.add (← B.load (← B.mul byteBits (cellOf marks k)) 0) (← B.shifted value 8)
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
def spLeafBit_2 (bits1 : List V) (bits2 : List V) (b : Nat) : B (Word) := B.inline "sp_leaf_bit" do
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
    v ← B.add (← B.mul (cellOf vals at') (← B.const (lit SP_WORD3_MUL_0))) (← B.mul (cellOf vals (at' + 8)) (← B.const (((gpowE 8) * (lit SP_WORD3_MUL_0)) + (lit SP_WORD3_MUL_1))))
  else
    v ← B.mul (cellOf vals at') (← B.const (lit SP_WORD3_MUL_0))
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
def spPath_2 (node : Word) (pp : Word) (a0 : E) (bits1 : List V) (bits2 : List V) (lvals : List V) (out : List V) (off : Nat) (height : Nat) : B (Unit) := B.inline "sp_path" do
  let mut cur := node
  let z_k := 0
  let kids ← B.stackBuf 5
  B.witness "siblings" (.stack (kids.take 2))
  let t0 ← spLeafBit_2 bits1 bits2 (off + z_k)
  isChild cur kids 0 t0
  let nodeAt := SP_TREE + ((z_k + 1) * SP_WORD2_MUL)
  let mut nodeAt_word : Word := default
  let mut parent : List V := default
  if (z_k + 1) = height then
    pure () -- no use of this definition takes this branch
  else
    let t1 ← spBe16 lvals ((off + z_k) + 1) ((height - z_k) - 1)
    nodeAt_word ← B.add t1 (← B.const (lit nodeAt))
    parent ← B.stackBuf 1
  B.keccak (a := (.words [.cell pp.v, .cell (← B.const a0).v])) (b := (.words [.cell nodeAt_word.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
  cur := cellOf parent 0
  for z_k in [1:9] do
    let kids ← B.stackBuf 5
    B.witness "siblings" (.stack (kids.take 2))
    let t0 ← spLeafBit_2 bits1 bits2 (off + z_k)
    isChild cur kids 0 t0
    let nodeAt := SP_TREE + ((z_k + 1) * SP_WORD2_MUL)
    if (z_k + 1) = height then
      pure () -- no use of this definition takes this branch
    else
      let t1 ← spBe16 lvals ((off + z_k) + 1) ((height - z_k) - 1)
      nodeAt_word ← B.add t1 (← B.const (lit nodeAt))
      parent ← B.stackBuf 1
    B.keccak (a := (.words [.cell pp.v, .cell (← B.const a0).v])) (b := (.words [.cell nodeAt_word.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
    cur := cellOf parent 0
  let z_k := 9
  let kids ← B.stackBuf 5
  B.witness "siblings" (.stack (kids.take 2))
  let t0 ← spLeafBit_2 bits1 bits2 (off + z_k)
  isChild cur kids 0 t0
  let nodeAt := SP_TREE + ((z_k + 1) * SP_WORD2_MUL)
  if (z_k + 1) = height then
    parent := out
  else
    pure () -- no use of this definition takes this branch
  B.keccak (a := (.words [.cell pp.v, .cell (← B.const a0).v])) (b := (.words [.cell (← B.const (lit nodeAt)).v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
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
def spLayer_2 (pp : Word) (a0 : E) (key : Word) (signed : Word) (byteBits : Word) (bits1 : List V) (bits2 : List V) (lvals : List V) (out : List V) (off : Nat) (height : Nat) : B (Unit) := B.inline "sp_layer" do
  let ctr ← B.stackBuf SP_COUNTER_BYTES
  B.witness "sp_counter" (.stack ctr)
  let counter ← spFromBytes byteBits ctr SP_COUNTER_BYTES
  let enc ← B.stackBuf 1
  let encAt ← B.add key (← B.const (lit SP_WOTS_ENC))
  B.keccak (a := (.words [.cell pp.v, .cell (← B.const a0).v])) (b := (.words [.cell encAt.v, .cell signed.v])) (tail := some (.words [.cell counter.v, .zero, .zero, .zero])) (len := some SP_ENCODING_BYTES) (out := (.frame enc))
  let leaf ← call1 "sp_wots" [pp.v, (← B.const a0).v, key.v, (cellOf enc 0).v]
  spPath_2 leaf pp a0 bits1 bits2 lvals out off height

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
def spPath (node : Word) (pp : Word) (a0 : Word) (bits1 : List V) (bits2 : List V) (lvals : List V) (out : List V) (off : Nat) (height : Nat) : B (Unit) := B.inline "sp_path" do
  let mut cur := node
  let z_k := 0
  let kids ← B.stackBuf 5
  B.witness "siblings" (.stack (kids.take 2))
  let t0 ← spLeafBit_2 bits1 bits2 (off + z_k)
  isChild cur kids 0 t0
  let nodeAt := SP_TREE + ((z_k + 1) * SP_WORD2_MUL)
  let mut nodeAt_word : Word := default
  let mut parent : List V := default
  if (z_k + 1) = height then
    pure () -- no use of this definition takes this branch
  else
    let t1 ← spBe16 lvals ((off + z_k) + 1) ((height - z_k) - 1)
    nodeAt_word ← B.add t1 (← B.const (lit nodeAt))
    parent ← B.stackBuf 1
  B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt_word.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
  cur := cellOf parent 0
  for z_k in [1:7] do
    let kids ← B.stackBuf 5
    B.witness "siblings" (.stack (kids.take 2))
    let t0 ← spLeafBit_2 bits1 bits2 (off + z_k)
    isChild cur kids 0 t0
    let nodeAt := SP_TREE + ((z_k + 1) * SP_WORD2_MUL)
    if (z_k + 1) = height then
      pure () -- no use of this definition takes this branch
    else
      let t1 ← spBe16 lvals ((off + z_k) + 1) ((height - z_k) - 1)
      nodeAt_word ← B.add t1 (← B.const (lit nodeAt))
      parent ← B.stackBuf 1
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt_word.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
    cur := cellOf parent 0
  let z_k := 7
  let kids ← B.stackBuf 5
  B.witness "siblings" (.stack (kids.take 2))
  let t0 ← spLeafBit_2 bits1 bits2 (off + z_k)
  isChild cur kids 0 t0
  let nodeAt := SP_TREE + ((z_k + 1) * SP_WORD2_MUL)
  if (z_k + 1) = height then
    parent := out
  else
    pure () -- no use of this definition takes this branch
  B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell (← B.const (lit nodeAt)).v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
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
def spLayer (pp : Word) (a0 : Word) (key : Word) (signed : Word) (byteBits : Word) (bits1 : List V) (bits2 : List V) (lvals : List V) (out : List V) (off : Nat) (height : Nat) : B (Unit) := B.inline "sp_layer" do
  let ctr ← B.stackBuf SP_COUNTER_BYTES
  B.witness "sp_counter" (.stack ctr)
  let counter ← spFromBytes byteBits ctr SP_COUNTER_BYTES
  let enc ← B.stackBuf 1
  let encAt ← B.add key (← B.const (lit SP_WOTS_ENC))
  B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell encAt.v, .cell signed.v])) (tail := some (.words [.cell counter.v, .zero, .zero, .zero])) (len := some SP_ENCODING_BYTES) (out := (.frame enc))
  let leaf ← call1 "sp_wots" [pp.v, a0.v, key.v, (cellOf enc 0).v]
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
  let mut at' := a1
  if z = SP_FORS_HEIGHT then
    pure () -- no use of this definition takes this branch
  else
    if (z / (SP_FORS_HEIGHT - 8)) = 0 then
      let t0 ← spBe16 vals ((SP_FORS_HEIGHT * c) + z) 16
      at' ← B.add at' t0
    else
      pure () -- no use of this definition takes this branch
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
def spMdBit_2 (bits0 : List V) (bits1 : List V) (p : Nat) : B (Word) := B.inline "sp_md_bit" do
  let mut b := cellOf bits0 ((((8 * (p / 8)) + 7) - (p % 8)) % SP_CELL_BITS)
  if (p / SP_CELL_BITS) = 1 then
    b := cellOf bits1 ((((8 * (p / 8)) + 7) - (p % 8)) - SP_CELL_BITS)
  else
    pure ()
  return b

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
def spForsAt_2 (a1 : Word) (vals : List V) (c : Nat) (z : Nat) : B (Word) := B.inline "sp_fors_at" do
  let mut at' ← B.add a1 (← B.const (lit (z * SP_WORD2_MUL)))
  if z = SP_FORS_HEIGHT then
    at' := at'
  else
    if (z / (SP_FORS_HEIGHT - 8)) = 0 then
      let t0 ← spBe16 vals ((SP_FORS_HEIGHT * c) + z) 16
      at' ← B.add at' t0
    else
      at' := at'
      let t0 ← spBe16 vals ((SP_FORS_HEIGHT * c) + z) 8
      at' ← B.add at' t0
  return at'

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
def spForsAt_3 (a1 : Word) (vals : List V) (c : Nat) (z : Nat) : B (Word) := B.inline "sp_fors_at" do
  let mut at' ← B.add a1 (← B.const (lit (z * SP_WORD2_MUL)))
  if z = SP_FORS_HEIGHT then
    at' ← B.add at' (← B.const (lit (c * SP_WORD3_MUL_0)))
  else
    if (z / (SP_FORS_HEIGHT - 8)) = 0 then
      pure () -- no use of this definition takes this branch
    else
      at' ← B.add at' (← B.const ((lit (c / (2 ^ (z - (SP_FORS_HEIGHT - 8))))) * (((gpowE 8) * (lit SP_WORD3_MUL_0)) + (lit SP_WORD3_MUL_1))))
      let t0 ← spBe16 vals ((SP_FORS_HEIGHT * c) + z) 8
      at' ← B.add at' t0
  return at'

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
def spForsTree_6 (pp : Word) (a0 : Word) (a1 : Word) (bits0 : List V) (bits1 : List V) (vals : List V) (roots : List V) (c : Nat) : B (Unit) := B.inline "sp_fors_tree" do
  let secret ← hinted (B.witnessCell "sp_fors_secrets")
  let held ← B.stackBuf 1
  let t0 ← spForsAt a1 vals c 0
  B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell t0.v, .cell secret.v])) (out := (.frame held))
  let mut cur := cellOf held 0
  let mut parent : List V := default
  let z_k := 0
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    pure () -- no use of this definition takes this branch
  else
    parent ← B.stackBuf 1
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
    cur := cellOf parent 0
  for z_k in [1:6] do
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack (kids.take 2))
    let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt_3 a1 vals c (z_k + 1)
    if (z_k + 1) = SP_FORS_HEIGHT then
      pure () -- no use of this definition takes this branch
    else
      parent ← B.stackBuf 1
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
      cur := cellOf parent 0
  for z_k in [6:9] do
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack (kids.take 2))
    let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
    if (z_k + 1) = SP_FORS_HEIGHT then
      pure () -- no use of this definition takes this branch
    else
      parent ← B.stackBuf 1
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
      cur := cellOf parent 0
  let z_k := 9
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_3 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame ((roots.drop c).take ((c + 1) - c))))
  else
    pure () -- no use of this definition takes this branch

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
def spForsTree_5 (pp : Word) (a0 : Word) (a1 : Word) (bits0 : List V) (bits1 : List V) (vals : List V) (roots : List V) (c : Nat) : B (Unit) := B.inline "sp_fors_tree" do
  let secret ← hinted (B.witnessCell "sp_fors_secrets")
  let held ← B.stackBuf 1
  let t0 ← spForsAt a1 vals c 0
  B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell t0.v, .cell secret.v])) (out := (.frame held))
  let mut cur := cellOf held 0
  let mut parent : List V := default
  let z_k := 0
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    pure () -- no use of this definition takes this branch
  else
    parent ← B.stackBuf 1
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
    cur := cellOf parent 0
  for z_k in [1:5] do
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack (kids.take 2))
    let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt_3 a1 vals c (z_k + 1)
    if (z_k + 1) = SP_FORS_HEIGHT then
      pure () -- no use of this definition takes this branch
    else
      parent ← B.stackBuf 1
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
      cur := cellOf parent 0
  for z_k in [5:9] do
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack (kids.take 2))
    let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
    if (z_k + 1) = SP_FORS_HEIGHT then
      pure () -- no use of this definition takes this branch
    else
      parent ← B.stackBuf 1
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
      cur := cellOf parent 0
  let z_k := 9
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_3 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame ((roots.drop c).take ((c + 1) - c))))
  else
    pure () -- no use of this definition takes this branch

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
def spForsTree_4 (pp : Word) (a0 : Word) (a1 : Word) (bits0 : List V) (bits1 : List V) (vals : List V) (roots : List V) (c : Nat) : B (Unit) := B.inline "sp_fors_tree" do
  let secret ← hinted (B.witnessCell "sp_fors_secrets")
  let held ← B.stackBuf 1
  let t0 ← spForsAt a1 vals c 0
  B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell t0.v, .cell secret.v])) (out := (.frame held))
  let mut cur := cellOf held 0
  let mut parent : List V := default
  let z_k := 0
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    pure () -- no use of this definition takes this branch
  else
    parent ← B.stackBuf 1
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
    cur := cellOf parent 0
  for z_k in [1:4] do
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack (kids.take 2))
    let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt_3 a1 vals c (z_k + 1)
    if (z_k + 1) = SP_FORS_HEIGHT then
      pure () -- no use of this definition takes this branch
    else
      parent ← B.stackBuf 1
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
      cur := cellOf parent 0
  for z_k in [4:9] do
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack (kids.take 2))
    let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
    if (z_k + 1) = SP_FORS_HEIGHT then
      pure () -- no use of this definition takes this branch
    else
      parent ← B.stackBuf 1
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
      cur := cellOf parent 0
  let z_k := 9
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_3 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame ((roots.drop c).take ((c + 1) - c))))
  else
    pure () -- no use of this definition takes this branch

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
def spForsTree_3 (pp : Word) (a0 : Word) (a1 : Word) (bits0 : List V) (bits1 : List V) (vals : List V) (roots : List V) (c : Nat) : B (Unit) := B.inline "sp_fors_tree" do
  let secret ← hinted (B.witnessCell "sp_fors_secrets")
  let held ← B.stackBuf 1
  let t0 ← spForsAt a1 vals c 0
  B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell t0.v, .cell secret.v])) (out := (.frame held))
  let mut cur := cellOf held 0
  let mut parent : List V := default
  let z_k := 0
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    pure () -- no use of this definition takes this branch
  else
    parent ← B.stackBuf 1
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
    cur := cellOf parent 0
  for z_k in [1:3] do
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack (kids.take 2))
    let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt_3 a1 vals c (z_k + 1)
    if (z_k + 1) = SP_FORS_HEIGHT then
      pure () -- no use of this definition takes this branch
    else
      parent ← B.stackBuf 1
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
      cur := cellOf parent 0
  for z_k in [3:9] do
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack (kids.take 2))
    let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
    if (z_k + 1) = SP_FORS_HEIGHT then
      pure () -- no use of this definition takes this branch
    else
      parent ← B.stackBuf 1
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
      cur := cellOf parent 0
  let z_k := 9
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_3 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame ((roots.drop c).take ((c + 1) - c))))
  else
    pure () -- no use of this definition takes this branch

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
def spForsTree_2 (pp : Word) (a0 : Word) (a1 : Word) (bits0 : List V) (bits1 : List V) (vals : List V) (roots : List V) (c : Nat) : B (Unit) := B.inline "sp_fors_tree" do
  let secret ← hinted (B.witnessCell "sp_fors_secrets")
  let held ← B.stackBuf 1
  let t0 ← spForsAt a1 vals c 0
  B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell t0.v, .cell secret.v])) (out := (.frame held))
  let mut cur := cellOf held 0
  let mut parent : List V := default
  let z_k := 0
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    pure () -- no use of this definition takes this branch
  else
    parent ← B.stackBuf 1
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
    cur := cellOf parent 0
  let z_k := 1
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_3 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    pure () -- no use of this definition takes this branch
  else
    parent ← B.stackBuf 1
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
    cur := cellOf parent 0
  for z_k in [2:9] do
    let kids ← B.stackBuf 5
    B.witness "sp_fors_nodes" (.stack (kids.take 2))
    let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
    if (z_k + 1) = SP_FORS_HEIGHT then
      pure () -- no use of this definition takes this branch
    else
      parent ← B.stackBuf 1
      B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame parent))
      cur := cellOf parent 0
  let z_k := 9
  let kids ← B.stackBuf 5
  B.witness "sp_fors_nodes" (.stack (kids.take 2))
  let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
  isChild cur kids 0 t1
  let nodeAt ← spForsAt_3 a1 vals c (z_k + 1)
  if (z_k + 1) = SP_FORS_HEIGHT then
    B.keccak (a := (.words [.cell pp.v, .cell a0.v])) (b := (.words [.cell nodeAt.v, .cell (cellOf kids 0).v])) (tail := some (.cells (.frame ((kids.drop 1).take (5 - 1))))) (len := some 80) (padTail := true) (out := (.frame ((roots.drop c).take ((c + 1) - c))))
  else
    pure () -- no use of this definition takes this branch

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
    let t1 ← spMdBit_2 bits0 bits1 ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - z_k)
    isChild cur kids 0 t1
    let nodeAt ← spForsAt_2 a1 vals c (z_k + 1)
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
def spMdByte_2 (vals : List V) (i : Nat) : B (Word) := B.inline "sp_md_byte" do
  let c := (8 * i) / SP_FORS_HEIGHT
  let mut v : Word := default
  if c = (((8 * i) + 7) / SP_FORS_HEIGHT) then
    v := cellOf vals (((SP_FORS_HEIGHT * ((2 * c) + 1)) - (8 * i)) - 8)
    if (8 * i) ≠ (SP_FORS_HEIGHT * c) then
      v ← B.add v (← B.mul (cellOf vals ((SP_FORS_HEIGHT * ((2 * c) + 1)) - (8 * i))) (← B.const (gpowE 8)))
    else
      pure ()
    v ← B.mul v (← B.const (lit (2 ^ (8 * (i % 16)))))
  else
    v ← B.mul (← B.add (cellOf vals (SP_FORS_HEIGHT * c)) (← B.mul (cellOf vals ((SP_FORS_HEIGHT * ((2 * c) + 1)) - (8 * i))) (← B.const (gpowE ((SP_FORS_HEIGHT * (c + 1)) - (8 * i)))))) (← B.const (lit (2 ^ ((((8 * (i % 16)) + (8 * i)) + 8) - (SP_FORS_HEIGHT * (c + 1))))))
    v ← B.add v (cellOf vals (((SP_FORS_HEIGHT * ((2 * c) + 3)) - (8 * i)) - 8))
  return v

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
      pure () -- no use of this definition takes this branch
    else
      pure ()
    v := v
  else
    v ← B.mul (← B.add (cellOf vals (SP_FORS_HEIGHT * c)) (← B.mul (cellOf vals ((SP_FORS_HEIGHT * ((2 * c) + 1)) - (8 * i))) (← B.const (gpowE ((SP_FORS_HEIGHT * (c + 1)) - (8 * i)))))) (← B.const (lit (2 ^ ((((8 * (i % 16)) + (8 * i)) + 8) - (SP_FORS_HEIGHT * (c + 1))))))
    v ← B.add v (← B.mul (cellOf vals (((SP_FORS_HEIGHT * ((2 * c) + 3)) - (8 * i)) - 8)) (← B.const (lit (2 ^ (8 * (i % 16))))))
  return v

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
def spLeafBit (bits1 : List V) (bits2 : List V) (b : Nat) (dsts : List V) : B (Unit) := B.inline "sp_leaf_bit" do
  let mut x := cellOf bits2 ((b + 8) % (8 * SP_TAIL_BYTES))
  if (b / 8) = (SP_TOP / 8) then
    pure () -- no use of this definition takes this branch
  else
    pure ()
  if (b / 8) = ((SP_TOP / 8) + 1) then
    x := cellOf bits1 (((b - SP_TOP) - 8) + SP_TREE_HI_BIT)
  else
    pure ()
  B.copy (cellOf dsts 0) x

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
  spLeafBit bits1 bits2 ((off + n) - 1) [(cellOf lvals ((off + n) - 1)).v]
  for r_k in [1:n] do
    let t0 ← spLeafBit_2 bits1 bits2 (((off + n) - 1) - r_k)
    B.addInto (cellOf lvals (((off + n) - 1) - r_k)) t0 (← B.mul (← B.const (gpowE 1)) (cellOf lvals ((off + n) - r_k)))

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
def spForsField_2 (bits0 : List V) (bits1 : List V) (vals : List V) (c : Nat) : B (Unit) := B.inline "sp_fors_field" do
  let t0 ← spMdBit_2 bits0 bits1 (SP_FORS_HEIGHT * c)
  B.addInto (cellOf vals (((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1)) t0 (← B.const (lit (2 * c)))
  for r_k in [1:SP_FORS_HEIGHT] do
    let t1 ← spMdBit_2 bits0 bits1 ((SP_FORS_HEIGHT * c) + r_k)
    B.addInto (cellOf vals ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - r_k)) t1 (← B.mul (← B.const (gpowE 1)) (cellOf vals (((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - r_k)))

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
def spMdBit (bits0 : List V) (bits1 : List V) (p : Nat) (dsts : List V) : B (Unit) := B.inline "sp_md_bit" do
  let b := cellOf bits0 ((((8 * (p / 8)) + 7) - (p % 8)) % SP_CELL_BITS)
  if (p / SP_CELL_BITS) = 1 then
    pure () -- no use of this definition takes this branch
  else
    pure ()
  B.copy (cellOf dsts 0) b

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
  spMdBit bits0 bits1 (SP_FORS_HEIGHT * c) [(cellOf vals (((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1)).v]
  for r_k in [1:SP_FORS_HEIGHT] do
    let t0 ← spMdBit_2 bits0 bits1 ((SP_FORS_HEIGHT * c) + r_k)
    B.addInto (cellOf vals ((((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - 1) - r_k)) t0 (← B.mul (← B.const (gpowE 1)) (cellOf vals (((SP_FORS_HEIGHT * c) + SP_FORS_HEIGHT) - r_k)))

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
def walk_5 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (powers : List V) (i : Nat) (k : Nat) (lx : Nat) : B (Unit) := B.inline "walk" do
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    pure ()
  if k = CHAIN_STEPS then
    B.witness "chain_starts" (.stack ((walks.drop (((i + 1) * CHAIN_STEPS) - 1)).take (((i + 1) * CHAIN_STEPS) - (((i + 1) * CHAIN_STEPS) - 1))))
  else
    let mut value ← hinted (B.witnessCell "chain_starts")
    let s_k := 0
    let o := (CHAIN_STEPS * i) + s_k
    if lx = 1 then
      pure () -- no use of this definition takes this branch
    else
      B.keccak (a := (.words [.cell pp.v, .cell (cellOf at' 0).v])) (b := (.words [.cell (cellOf at' 1).v, .cell value.v])) (out := (.frame ((walks.drop o).take ((o + 1) - o))))
    value := cellOf walks o
    for s_k in [1:CHAIN_STEPS] do
      let o := (CHAIN_STEPS * i) + s_k
      if lx = 1 then
        pure () -- no use of this definition takes this branch
      else
        B.keccak (a := (.words [.cell pp.v, .cell (cellOf at' 0).v])) (b := (.words [.cell (← B.add (cellOf at' 1) (← B.const (lit ((i * SP_WORD2_MUL) + (s_k * SP_WORD3_MUL_0))))).v, .cell value.v])) (out := (.frame ((walks.drop o).take ((o + 1) - o))))
      value := cellOf walks o

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
def walkGroup_94 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    let r_k := 0
    digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walk_7 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (powers : List V) (i : Nat) (k : Nat) (lx : Nat) : B (Unit) := B.inline "walk" do
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    pure ()
  if k = CHAIN_STEPS then
    pure () -- no use of this definition takes this branch
  else
    let mut value ← hinted (B.witnessCell "chain_starts")
    let s_k := 2
    let o := (CHAIN_STEPS * i) + s_k
    if lx = 1 then
      pure () -- no use of this definition takes this branch
    else
      B.keccak (a := (.words [.cell pp.v, .cell (cellOf at' 0).v])) (b := (.words [.cell (← B.add (cellOf at' 1) (← B.const (lit ((i * SP_WORD2_MUL) + (s_k * SP_WORD3_MUL_0))))).v, .cell value.v])) (out := (.frame ((walks.drop o).take ((o + 1) - o))))
    value := cellOf walks o

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
def walkGroup_93 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    let r_k := 0
    digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walk_6 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (powers : List V) (i : Nat) (k : Nat) (lx : Nat) : B (Unit) := B.inline "walk" do
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    pure ()
  if k = CHAIN_STEPS then
    pure () -- no use of this definition takes this branch
  else
    let mut value ← hinted (B.witnessCell "chain_starts")
    for s_k in [k:CHAIN_STEPS] do
      let o := (CHAIN_STEPS * i) + s_k
      if lx = 1 then
        pure () -- no use of this definition takes this branch
      else
        B.keccak (a := (.words [.cell pp.v, .cell (cellOf at' 0).v])) (b := (.words [.cell (← B.add (cellOf at' 1) (← B.const (lit ((i * SP_WORD2_MUL) + (s_k * SP_WORD3_MUL_0))))).v, .cell value.v])) (out := (.frame ((walks.drop o).take ((o + 1) - o))))
      value := cellOf walks o

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
def walkGroup_92 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    let r_k := 0
    digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_91 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    let r_k := 0
    digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.copy (cellOf dsts 1) encoded

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
def walkGroup_90 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_89 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_88 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_87 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_86 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_85 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_84 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_83 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_82 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_81 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_80 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_79 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_78 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_77 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_76 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_75 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_74 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_73 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_72 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_71 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_70 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_69 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_68 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_67 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_66 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_65 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_64 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_63 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.copy (cellOf dsts 1) encoded

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
def walkGroup_62 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_61 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_60 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_59 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_58 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_57 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_56 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_55 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_54 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_53 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_52 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_51 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_50 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_49 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_48 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_47 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_46 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_45 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_44 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_43 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_42 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_41 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_40 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_39 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_38 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_7 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_37 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_36 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_5 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_6 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    pure () -- no use of this definition takes this branch
  else
    digits := 0
    for r_k in [0:n] do
      digits := digits + (((k / (4 ^ r_k)) % 4) * (2 ^ ((8 * ((first + r_k) / 4)) + (2 * ((4 - 1) - ((first + r_k) % 4))))))
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (4 ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def fsPack (rate : List V) (k : Nat) (x : Word) (tag : Nat) : B (Unit) := B.inline "fs_pack" do
  B.copy (cellOf rate (2 * k)) x
  B.constInto (cellOf rate ((2 * k) + 1)) ((lit Y_TOWER) * (lit tag))

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
  fsPack rate k nonce DS_POW_NONCE
  let nxt ← fsPerm sp rate (k + 1)
  return nxt

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
def fsGrindSqueeze_4 (sp : List V) (rate : List V) (k : Nat) (cursor : Word) (tabs : Shifted) (bits : Nat) : B (List V × Word × Shifted) := B.inline "fs_grind_squeeze" do
  let mut nxt : List V := default
  let mut cur : Shifted := default
  if bits = 0 then
    pure () -- no use of this definition takes this branch
  else
    if k = 4 then
      pure () -- no use of this definition takes this branch
    else
      nxt ← fsAbsorbNonce sp rate k (← B.load cursor 0)
      let _ ← B.call (instName "grind_check" [.L bits]) [(cellOf nxt 1).v, (← B.shifted tabs.base tabs.exp).v] 0
      cur := ⟨cursor, 1⟩
  return (nxt, cellOf nxt 0, ⟨cur.base, cur.exp⟩)

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
def fsGrindSqueeze_3 (sp : List V) (rate : List V) (k : Nat) (cursor : Shifted) (tabs : Shifted) (bits : Nat) : B (List V × Word × Shifted) := B.inline "fs_grind_squeeze" do
  let mut nxt : List V := default
  let mut cur : Shifted := default
  if bits = 0 then
    pure () -- no use of this definition takes this branch
  else
    if k = 4 then
      pure () -- no use of this definition takes this branch
    else
      nxt ← fsAbsorbNonce sp rate k (← B.load cursor.base cursor.exp)
      let _ ← B.call (instName "grind_check" [.L bits]) [(cellOf nxt 1).v, (← B.shifted tabs.base tabs.exp).v] 0
      cur := ⟨cursor.base, cursor.exp + 1⟩
  return (nxt, cellOf nxt 0, ⟨cur.base, cur.exp⟩)

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
def keccakForm (lanes : Word) (shifts : List V) (fLanes : List V) (fOff : Nat) : B (Word) := B.inline "keccak_form" do
  let total := 0
  let column ← B.stackBuf 5
  let columnNext ← B.stackBuf 5
  let fColumn ← B.stackBuf 5
  let mut laneWeight : Word := default
  let mut moved : Word := default
  let mut fWeight : Word := default
  let mut total_word : Word := default
  let x_k := 0
  let acc := 0
  let accNext := 0
  let fAcc := 0
  let mut acc_word : Word := default
  let mut accNext_word : Word := default
  let mut fAcc_word : Word := default
  let y_k := 0
  laneWeight ← B.load lanes (arrInt KECCAK_PI (x_k + (5 * y_k)))
  moved ← B.mul laneWeight (cellOf shifts (arrInt KECCAK_RHO (x_k + (5 * y_k))))
  fWeight := cellOf fLanes ((fOff + x_k) + (5 * y_k))
  total_word ← B.mul fWeight moved
  acc_word := moved
  accNext_word ← B.mul laneWeight (cellOf shifts (((arrInt KECCAK_RHO (x_k + (5 * y_k))) + 1) % 64))
  fAcc_word := fWeight
  for y_k in [1:5] do
    laneWeight ← B.load lanes (arrInt KECCAK_PI (x_k + (5 * y_k)))
    moved ← B.mul laneWeight (cellOf shifts (arrInt KECCAK_RHO (x_k + (5 * y_k))))
    fWeight := cellOf fLanes ((fOff + x_k) + (5 * y_k))
    total_word ← B.add total_word (← B.mul fWeight moved)
    acc_word ← B.add acc_word moved
    accNext_word ← B.add accNext_word (← B.mul laneWeight (cellOf shifts (((arrInt KECCAK_RHO (x_k + (5 * y_k))) + 1) % 64)))
    fAcc_word ← B.add fAcc_word fWeight
  B.copy (cellOf column x_k) acc_word
  B.copy (cellOf columnNext x_k) accNext_word
  B.copy (cellOf fColumn x_k) fAcc_word
  for x_k in [1:5] do
    let acc := 0
    let accNext := 0
    let fAcc := 0
    let y_k := 0
    laneWeight ← B.load lanes (arrInt KECCAK_PI (x_k + (5 * y_k)))
    moved ← B.mul laneWeight (cellOf shifts (arrInt KECCAK_RHO (x_k + (5 * y_k))))
    fWeight := cellOf fLanes ((fOff + x_k) + (5 * y_k))
    total_word ← B.add total_word (← B.mul fWeight moved)
    acc_word := moved
    accNext_word ← B.mul laneWeight (cellOf shifts (((arrInt KECCAK_RHO (x_k + (5 * y_k))) + 1) % 64))
    fAcc_word := fWeight
    for y_k in [1:5] do
      laneWeight ← B.load lanes (arrInt KECCAK_PI (x_k + (5 * y_k)))
      moved ← B.mul laneWeight (cellOf shifts (arrInt KECCAK_RHO (x_k + (5 * y_k))))
      fWeight := cellOf fLanes ((fOff + x_k) + (5 * y_k))
      total_word ← B.add total_word (← B.mul fWeight moved)
      acc_word ← B.add acc_word moved
      accNext_word ← B.add accNext_word (← B.mul laneWeight (cellOf shifts (((arrInt KECCAK_RHO (x_k + (5 * y_k))) + 1) % 64)))
      fAcc_word ← B.add fAcc_word fWeight
    B.copy (cellOf column x_k) acc_word
    B.copy (cellOf columnNext x_k) accNext_word
    B.copy (cellOf fColumn x_k) fAcc_word
  for x_k in [0:5] do
    total_word ← B.add total_word (← B.mul (cellOf fColumn x_k) (← B.add (cellOf column ((x_k + 1) % 5)) (cellOf columnNext ((x_k + 4) % 5))))
  return total_word

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
def foldNode_2 (src : List V) (dst : List V) (aT : Word) (aT1 : Word) (p : Nat) (b : Nat) (t : Nat) : B (Unit) := B.inline "fold_node" do
  let n := 2 ^ (KECCAK_Z_BITS - t)
  let k_k := 0
  let x0 := cellOf src ((p * n) + (((2 * k_k) + ((n - 1) * b)) % n))
  let x1 := cellOf src ((p * n) + ((((2 * k_k) + 1) + ((n - 1) * b)) % n))
  B.addInto (cellOf dst (((p + ((2 ^ t) * b)) * (n / 2)) + k_k)) (← B.mul aT1 x0) (← B.mul aT x1)

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
def foldShifts_2 (src : List V) (dst : List V) (aT : Word) (t : Nat) : B (Unit) := B.inline "fold_shifts" do
  let aT1 ← B.add (← B.const 1) aT
  for p_k in [0:2 ^ t] do
    for b_k in [0:2] do
      if (t + 1) = KECCAK_Z_BITS then
        if (arrInt KECCAK_SHIFT_USED (p_k + ((2 ^ t) * b_k))) = 1 then
          foldNode_2 src dst aT aT1 p_k b_k t
        else
          pure ()
      else
        foldNode src dst aT aT1 p_k b_k t

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
  let aT1 ← B.add (← B.const 1) aT
  let p_k := 0
  for b_k in [0:2] do
    if (t + 1) = KECCAK_Z_BITS then
      pure () -- no use of this definition takes this branch
    else
      foldNode src dst aT aT1 p_k b_k t

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
def eqtreeFrame_2 (pointPtr : Word) (out : List V) (nCoords : Nat) (count : Nat) : B (Unit) := B.inline "eqtree_frame" do
  let r0 ← B.load pointPtr 0
  B.addInto (cellOf out 0) (← B.const 1) r0
  B.copy (cellOf out 1) r0
  let mut pw : Word := default
  for t_k in [1:nCoords] do
    let rt ← B.load pointPtr t_k
    let onePlusRt ← B.add (← B.const 1) rt
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
def eqtreeFrame (pointPtr : Word) (out : List V) (nCoords : Nat) (count : Nat) : B (Unit) := B.inline "eqtree_frame" do
  let r0 ← B.load pointPtr 0
  B.addInto (cellOf out 0) (← B.const 1) r0
  B.copy (cellOf out 1) r0

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
def keccakSlotLanes_2 (slot : Word) (segmentPoint : Word) (out : List V) (first : Nat) (count : Nat) : B (Unit) := B.inline "keccak_slot_lanes" do
  let slotWeights ← B.stackBuf 126
  eqtreeFrame_2 slot slotWeights QKECCAK_SLOT_LOG (KECCAK_LANES * KECCAK_SEGMENTS)
  let segWeights ← B.stackBuf 2
  eqtreeFrame segmentPoint segWeights KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
  let lane_k := 0
  let laneAcc := 0
  let mut laneAcc_word : Word := default
  let m_k := 0
  laneAcc_word ← B.mul (cellOf segWeights (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) (cellOf slotWeights ((((2 ^ QKECCAK_SLOT_LOG) - 2) + (KECCAK_LANES * (first + m_k))) + lane_k))
  let m_k := 1
  laneAcc_word ← B.add laneAcc_word (← B.mul (cellOf segWeights (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) (cellOf slotWeights ((((2 ^ QKECCAK_SLOT_LOG) - 2) + (KECCAK_LANES * (first + m_k))) + lane_k)))
  B.copy (cellOf out lane_k) laneAcc_word
  for lane_k in [1:KECCAK_LANES] do
    let laneAcc := 0
    let m_k := 0
    laneAcc_word ← B.mul (cellOf segWeights (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) (cellOf slotWeights ((((2 ^ QKECCAK_SLOT_LOG) - 2) + (KECCAK_LANES * (first + m_k))) + lane_k))
    let m_k := 1
    laneAcc_word ← B.add laneAcc_word (← B.mul (cellOf segWeights (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) (cellOf slotWeights ((((2 ^ QKECCAK_SLOT_LOG) - 2) + (KECCAK_LANES * (first + m_k))) + lane_k)))
    B.copy (cellOf out lane_k) laneAcc_word

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
def eqtree_3 (pointPtr : Shifted) (out : Word) (nCoords : Nat) : B (Unit) := B.inline "eqtree" do
  let r0 ← B.load pointPtr.base pointPtr.exp
  B.store out 0 (← B.add (← B.const 1) r0)
  B.store out 1 r0
  let mut pw : Word := default
  for t_k in [1:nCoords] do
    let rt ← B.load pointPtr.base (pointPtr.exp + t_k)
    let onePlusRt ← B.add (← B.const 1) rt
    for i_k in [0:2 ^ t_k] do
      pw ← B.load out (((2 ^ t_k) - 2) + i_k)
      B.store out (((2 ^ (t_k + 1)) - 2) + i_k) (← B.mul pw onePlusRt)
      B.store out ((((2 ^ (t_k + 1)) - 2) + (2 ^ t_k)) + i_k) (← B.mul pw rt)

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
  eqtreeFrame_2 slot slotWeights QKECCAK_SLOT_LOG (KECCAK_LANES * KECCAK_SEGMENTS)
  let segWeights ← B.stackBuf 2
  eqtreeFrame segmentPoint segWeights KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
  let lane_k := 0
  let laneAcc := 0
  let mut laneAcc_word : Word := default
  let m_k := 0
  laneAcc_word ← B.mul (cellOf segWeights (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) (cellOf slotWeights ((((2 ^ QKECCAK_SLOT_LOG) - 2) + (KECCAK_LANES * (first + m_k))) + lane_k))
  B.copy (cellOf out lane_k) laneAcc_word
  for lane_k in [1:KECCAK_LANES] do
    let laneAcc := 0
    let m_k := 0
    laneAcc_word ← B.mul (cellOf segWeights (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) (cellOf slotWeights ((((2 ^ QKECCAK_SLOT_LOG) - 2) + (KECCAK_LANES * (first + m_k))) + lane_k))
    B.copy (cellOf out lane_k) laneAcc_word

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
def eqtree_2 (pointPtr : Word) (out : Word) (nCoords : Nat) : B (Unit) := B.inline "eqtree" do
  let r0 ← B.load pointPtr 0
  B.store out 0 (← B.add (← B.const 1) r0)
  B.store out 1 r0

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
  let hi ← B.mul (← B.add word' (cellOf lo 0)) (← B.const (lit Y_INV))
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
def fsNext (rate : List V) (k : Nat) (cursor : Word) : B (Word × Shifted) := B.inline "fs_next" do
  let x ← B.load cursor 0
  fsPack rate k x DS_OBSERVE
  return (x, ⟨cursor, 1⟩)

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
def fsNext_2 (rate : List V) (k : Nat) (cursor : Shifted) : B (Word × Shifted) := B.inline "fs_next" do
  let x ← B.load cursor.base cursor.exp
  fsPack rate k x DS_OBSERVE
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
def gkrChildren_2 (sp : List V) (cursor : Word) (evals : List V) (n : Nat) : B (List V × List V × Shifted) := B.inline "gkr_children" do
  let mut rate ← B.stackBuf 8
  let mut cursor_ptr : Shifted := default
  let mut sp := sp
  let i_k := 0
  if (i_k % 4) = 0 then
    if i_k ≠ 0 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
  else
    pure () -- no use of this definition takes this branch
  let (t0, t1) ← fsNext rate (i_k % 4) cursor
  let ev := t0
  cursor_ptr := t1
  B.copy (cellOf evals i_k) ev
  for i_k in [1:N_GKR_TREES * n] do
    if (i_k % 4) = 0 then
      if i_k ≠ 0 then
        sp ← fsPerm sp rate 4
        rate ← B.stackBuf 8
      else
        pure () -- no use of this definition takes this branch
    else
      pure ()
    let (t0, t1) ← fsNext_2 rate (i_k % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let ev := t0
    cursor_ptr := t1
    B.copy (cellOf evals i_k) ev
  return (sp, rate, ⟨cursor_ptr.base, cursor_ptr.exp⟩)

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
def fsGrindSqueeze_2 (sp : List V) (rate : List V) (k : Nat) (cursor : Word) (tabs : Word) (bits : Nat) : B (List V × Word × Word) := B.inline "fs_grind_squeeze" do
  let mut nxt : List V := default
  let mut cur : Word := default
  if bits = 0 then
    nxt ← fsPerm sp rate k
    cur := cursor
  else
    pure () -- no use of this definition takes this branch
  return (nxt, cellOf nxt 0, cur)

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
def gkrProductCheck_2 (evals : List V) (lam : Word) (claim : Word) (n : Nat) : B (Unit) := B.inline "gkr_product_check" do
  let combined := 0
  let mut combined_word : Word := default
  let i_k := 0
  let tree := (N_GKR_TREES - 1) - i_k
  let mut product := cellOf evals (n * tree)
  let j_k := 1
  product ← B.mul product (cellOf evals ((n * tree) + j_k))
  combined_word ← B.add product (← B.mul lam (← B.const (lit combined)))
  for i_k in [1:N_GKR_TREES] do
    let tree := (N_GKR_TREES - 1) - i_k
    product := cellOf evals (n * tree)
    let j_k := 1
    product ← B.mul product (cellOf evals ((n * tree) + j_k))
    combined_word ← B.add product (← B.mul lam combined_word)
  B.assertEq claim combined_word

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
def fsStore_2 (rec' : Word) (field : Nat) (stride : Nat) (sp : List V) : B (Unit) := B.inline "fs_store" do
  for j_k in [0:FS_CELLS] do
    B.store rec' ((field + j_k) * stride) (cellOf sp ((KECCAK_STATE - FS_CELLS) + j_k))

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
  let combined := 0
  let mut combined_word : Word := default
  let i_k := 0
  let tree := (N_GKR_TREES - 1) - i_k
  let mut product := cellOf evals (n * tree)
  for j_k in [1:n] do
    product ← B.mul product (cellOf evals ((n * tree) + j_k))
  combined_word ← B.add product (← B.mul lam (← B.const (lit combined)))
  for i_k in [1:N_GKR_TREES] do
    let tree := (N_GKR_TREES - 1) - i_k
    product := cellOf evals (n * tree)
    for j_k in [1:n] do
      product ← B.mul product (cellOf evals ((n * tree) + j_k))
    combined_word ← B.add product (← B.mul lam combined_word)
  B.assertEq claim combined_word

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
  let mut cursor := cursor
  let mut sp := sp
  for i_k in [0:N_GKR_TREES * n] do
    if (i_k % 4) = 0 then
      if i_k ≠ 0 then
        sp ← fsPerm sp rate 4
        rate ← B.stackBuf 8
      else
        pure ()
    else
      pure ()
    let (t0, t1) ← fsNext_2 rate (i_k % 4) (⟨cursor.base, cursor.exp⟩)
    let ev := t0
    cursor := t1
    B.copy (cellOf evals i_k) ev
  return (sp, rate, ⟨cursor.base, cursor.exp⟩)

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
def fsGrindSqueeze (sp : List V) (rate : List V) (k : Nat) (cursor : Shifted) (tabs : Word) (bits : Nat) : B (List V × Word × Shifted) := B.inline "fs_grind_squeeze" do
  let mut nxt : List V := default
  let mut cur : Shifted := default
  if bits = 0 then
    nxt ← fsPerm sp rate k
    cur := ⟨cursor.base, cursor.exp⟩
  else
    if k = 4 then
      let full ← fsPerm sp rate 4
      let nonceRate ← B.stackBuf 8
      nxt ← fsAbsorbNonce full nonceRate 0 (← B.load cursor.base cursor.exp)
      let _ ← B.call (instName "grind_check" [.L bits]) [(cellOf nxt 1).v, tabs.v] 0
      cur := ⟨cursor.base, cursor.exp + 1⟩
    else
      nxt ← fsAbsorbNonce sp rate k (← B.load cursor.base cursor.exp)
      let _ ← B.call (instName "grind_check" [.L bits]) [(cellOf nxt 1).v, tabs.v] 0
      cur := ⟨cursor.base, cursor.exp + 1⟩
  return (nxt, cellOf nxt 0, ⟨cur.base, cur.exp⟩)

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
def walk_2 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (powers : List V) (i : Nat) (k : Nat) (lx : Nat) : B (Unit) := B.inline "walk" do
  let mut tag : Word := default
  if lx = 1 then
    if i = 0 then
      pure () -- no use of this definition takes this branch
    else
      if (arrInt LX_TAG_SLOT i) = 0 then
        tag := cellOf powers (arrInt LX_TAG_LOG i)
      else
        tag := cellOf tags ((arrInt LX_TAG_SLOT i) - 1)
  else
    pure () -- no use of this definition takes this branch
  if k = CHAIN_STEPS then
    B.witness "chain_starts" (.stack ((walks.drop (((i + 1) * CHAIN_STEPS) - 1)).take (((i + 1) * CHAIN_STEPS) - (((i + 1) * CHAIN_STEPS) - 1))))
  else
    let mut value ← hinted (B.witnessCell "chain_starts")
    for s_k in [k:CHAIN_STEPS] do
      let o := (CHAIN_STEPS * i) + s_k
      if lx = 1 then
        B.keccak (a := (.words [.cell pp.v, .cell (cellOf at' s_k).v])) (b := (.words [.cell value.v, .cell tag.v])) (out := (.frame ((walks.drop o).take ((o + 1) - o))))
      else
        pure () -- no use of this definition takes this branch
      value := cellOf walks o

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
def walkGroup (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walk_3 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (powers : List V) (i : Nat) (k : Nat) (lx : Nat) : B (Unit) := B.inline "walk" do
  let mut tag : Nat := default
  if lx = 1 then
    if i = 0 then
      tag := 0
    else
      pure () -- no use of this definition takes this branch
  else
    pure () -- no use of this definition takes this branch
  if k = CHAIN_STEPS then
    pure () -- no use of this definition takes this branch
  else
    let mut value ← hinted (B.witnessCell "chain_starts")
    let s_k := 2
    let o := (CHAIN_STEPS * i) + s_k
    if lx = 1 then
      B.keccak (a := (.words [.cell pp.v, .cell (cellOf at' s_k).v])) (b := (.words [.cell value.v, .zero])) (out := (.frame ((walks.drop o).take ((o + 1) - o))))
    else
      pure () -- no use of this definition takes this branch
    value := cellOf walks o

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
def walkGroup_2 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_3 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walk_4 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (powers : List V) (i : Nat) (k : Nat) (lx : Nat) : B (Unit) := B.inline "walk" do
  let mut tag : Word := default
  if lx = 1 then
    if i = 0 then
      pure () -- no use of this definition takes this branch
    else
      if (arrInt LX_TAG_SLOT i) = 0 then
        tag := cellOf powers (arrInt LX_TAG_LOG i)
      else
        tag := cellOf tags ((arrInt LX_TAG_SLOT i) - 1)
  else
    pure () -- no use of this definition takes this branch
  if k = CHAIN_STEPS then
    pure () -- no use of this definition takes this branch
  else
    let mut value ← hinted (B.witnessCell "chain_starts")
    let s_k := 2
    let o := (CHAIN_STEPS * i) + s_k
    if lx = 1 then
      B.keccak (a := (.words [.cell pp.v, .cell (cellOf at' s_k).v])) (b := (.words [.cell value.v, .cell tag.v])) (out := (.frame ((walks.drop o).take ((o + 1) - o))))
    else
      pure () -- no use of this definition takes this branch
    value := cellOf walks o

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
def walkGroup_3 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [2:n] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_4 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_3 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [2:n] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_5 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_6 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_3 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_7 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:3] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_8 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_3 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:3] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_9 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:3] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_10 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_3 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:3] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_11 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_12 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_3 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_13 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [2:n] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_14 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_3 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [2:n] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_15 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_16 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : GPow) (encoded : E) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_3 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.copy (cellOf dsts 0) (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.constInto (cellOf dsts 1) (encoded + (lit digits))

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
def walkGroup_17 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.copy (cellOf dsts 1) encoded

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
def walkGroup_18 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_19 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_20 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [2:n] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_21 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [2:n] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_22 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_23 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_24 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:3] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_25 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:3] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_26 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:3] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_27 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:3] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_28 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_29 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 2
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 3
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_30 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:2] do
    walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [2:n] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_31 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [2:n] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_32 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  for r_k in [1:n] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_33 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  for r_k in [0:n] do
    walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_34 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
def walkGroup_35 (at' : List V) (pp : Word) (walks : List V) (tags : List V) (first : Nat) (n : Nat) (k : Nat) (lx : Nat) (powers : List V) (product : Word) (encoded : Word) (dsts : List V) : B (Unit) := B.inline "walk_group" do
  let r_k := 0
  walk_2 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let r_k := 1
  walk_4 at' pp walks tags powers (first + r_k) ((k / (CHAIN_LENGTH ^ r_k)) % CHAIN_LENGTH) lx
  let mut digits : Nat := default
  if lx = 1 then
    digits := (k % (CHAIN_LENGTH ^ n)) * (CHAIN_LENGTH ^ first)
  else
    pure () -- no use of this definition takes this branch
  B.mulInto (cellOf dsts 0) product (cellOf powers (arrInt DIGIT_SUMS (k % (CHAIN_LENGTH ^ n))))
  B.addInto (cellOf dsts 1) encoded (← B.const (lit digits))

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
  let r_k := 0
  let tag := ((TW_NODE + (((((LX_WINDOW * w) + r_k) % LX_HEIGHT) + 1) * HI_MUL)) + ((((LX_WINDOW * w) + r_k) / LX_HEIGHT) * LX_TOP)) + (k / (2 ^ (r_k + 1)))
  let mut at' : Word := default
  if (w + 1) = LX_WINDOWS then
    pure () -- no use of this definition takes this branch
  else
    if (r_k + 1) = LX_WINDOW then
      pure () -- no use of this definition takes this branch
    else
      at' ← B.add (← B.mul (cellOf his (w + 1)) (cellOf powers ((LX_WINDOW - 1) - r_k))) (← B.const (lit tag))
  let mut parent : List V := default
  if (r_k + 1) = LX_WINDOW then
    pure () -- no use of this definition takes this branch
  else
    parent ← B.stackBuf 1
  let sibling ← hinted (B.witnessCell "lx_path")
  if ((k / (2 ^ r_k)) % 2) = 0 then
    B.keccak (a := (.words [.cell pp.v, .cell at'.v])) (b := (.words [.cell cur.v, .cell sibling.v])) (out := (.frame parent))
  else
    B.keccak (a := (.words [.cell pp.v, .cell at'.v])) (b := (.words [.cell sibling.v, .cell cur.v])) (out := (.frame parent))
  cur := cellOf parent 0
  for r_k in [1:LX_WINDOW] do
    let tag := ((TW_NODE + (((((LX_WINDOW * w) + r_k) % LX_HEIGHT) + 1) * HI_MUL)) + ((((LX_WINDOW * w) + r_k) / LX_HEIGHT) * LX_TOP)) + (k / (2 ^ (r_k + 1)))
    if (w + 1) = LX_WINDOWS then
      pure () -- no use of this definition takes this branch
    else
      if (r_k + 1) = LX_WINDOW then
        at' ← B.add (cellOf his (w + 1)) (← B.const (lit tag))
      else
        at' ← B.add (← B.mul (cellOf his (w + 1)) (cellOf powers ((LX_WINDOW - 1) - r_k))) (← B.const (lit tag))
    if (r_k + 1) = LX_WINDOW then
      parent := out
    else
      parent ← B.stackBuf 1
    let sibling ← hinted (B.witnessCell "lx_path")
    if ((k / (2 ^ r_k)) % 2) = 0 then
      B.keccak (a := (.words [.cell pp.v, .cell at'.v])) (b := (.words [.cell cur.v, .cell sibling.v])) (out := (.frame parent))
    else
      B.keccak (a := (.words [.cell pp.v, .cell at'.v])) (b := (.words [.cell sibling.v, .cell cur.v])) (out := (.frame parent))
    cur := cellOf parent 0

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
  B.mulInto (cellOf dsts 0) (cellOf his (w + 1)) (cellOf powers 8)

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
def lxWindow_2 (cur : Word) (pp : Word) (powers : List V) (his : List V) (out : List V) (w : Nat) (k : Nat) (dsts : List V) : B (Unit) := B.inline "lx_window" do
  lxLevels cur pp powers his out w k
  B.addInto (cellOf dsts 0) (← B.mul (cellOf his (w + 1)) (cellOf powers 8)) (← B.const (lit k))

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
def lxLevels_2 (cur : Word) (pp : Word) (powers : List V) (his : List V) (out : List V) (w : Nat) (k : Nat) : B (Unit) := B.inline "lx_levels" do
  let mut cur := cur
  let r_k := 0
  let tag := ((TW_NODE + (((((LX_WINDOW * w) + r_k) % LX_HEIGHT) + 1) * HI_MUL)) + ((((LX_WINDOW * w) + r_k) / LX_HEIGHT) * LX_TOP)) + (k / (2 ^ (r_k + 1)))
  let mut at' : Nat := default
  if (w + 1) = LX_WINDOWS then
    at' := tag
  else
    pure () -- no use of this definition takes this branch
  let mut parent : List V := default
  if (r_k + 1) = LX_WINDOW then
    pure () -- no use of this definition takes this branch
  else
    parent ← B.stackBuf 1
  let sibling ← hinted (B.witnessCell "lx_path")
  if ((k / (2 ^ r_k)) % 2) = 0 then
    B.keccak (a := (.words [.cell pp.v, .cell (← B.const (lit at')).v])) (b := (.words [.cell cur.v, .cell sibling.v])) (out := (.frame parent))
  else
    B.keccak (a := (.words [.cell pp.v, .cell (← B.const (lit at')).v])) (b := (.words [.cell sibling.v, .cell cur.v])) (out := (.frame parent))
  cur := cellOf parent 0
  for r_k in [1:LX_WINDOW] do
    let tag := ((TW_NODE + (((((LX_WINDOW * w) + r_k) % LX_HEIGHT) + 1) * HI_MUL)) + ((((LX_WINDOW * w) + r_k) / LX_HEIGHT) * LX_TOP)) + (k / (2 ^ (r_k + 1)))
    if (w + 1) = LX_WINDOWS then
      at' := tag
    else
      pure () -- no use of this definition takes this branch
    if (r_k + 1) = LX_WINDOW then
      parent := out
    else
      parent ← B.stackBuf 1
    let sibling ← hinted (B.witnessCell "lx_path")
    if ((k / (2 ^ r_k)) % 2) = 0 then
      B.keccak (a := (.words [.cell pp.v, .cell (← B.const (lit at')).v])) (b := (.words [.cell cur.v, .cell sibling.v])) (out := (.frame parent))
    else
      B.keccak (a := (.words [.cell pp.v, .cell (← B.const (lit at')).v])) (b := (.words [.cell sibling.v, .cell cur.v])) (out := (.frame parent))
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
  lxLevels_2 cur pp powers his out w k
  B.constInto (cellOf dsts 0) (lit k)

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
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
  let layer_k := 0
  let mut idx : Word := default
  if layer_k = 0 then
    idx := cellOf his 0
  else
    pure () -- no use of this definition takes this branch
  let rho ← hinted (B.witnessCell "randomizer")
  let digest ← B.stackBuf 1
  if layer_k = 0 then
    B.keccak (a := (.words [.cell pp.v, .cell (← B.add idx (← B.const (lit TW_MSG))).v])) (b := (.words [.cell (← B.load signer 2).v, .cell (← B.load signer 3).v])) (tail := some (.words [.cell rho.v, .zero, .zero, .zero])) (len := some 80) (out := (.frame digest))
  else
    pure () -- no use of this definition takes this branch
  let steps ← B.stackBuf CHAIN_STEPS
  for st_k in [0:CHAIN_STEPS] do
    B.addInto (cellOf steps st_k) idx (← B.const (lit (TW_CHAIN + (st_k * STEP_MUL))))
  let walks ← B.stackBuf 174
  let digitProduct := 1
  let encoded := 0
  let groups ← B.stackBuf LX_DIGIT_DISPATCHES
  B.witness "lx_digits" (.stack groups)
  for p_k in [0:LX_DIGIT_DISPATCHES - 1] do
    let _ ← B.rangeCheck (cellOf groups p_k) LX_DIGIT_GROUPS
    pure ()
  let _ ← B.rangeCheck (cellOf groups (LX_DIGIT_DISPATCHES - 1)) LX_TAIL_GROUPS
  let mut digitProduct_word : Word := default
  let mut encoded_word : Word := default
  let p_k := 0
  let t0 ← B.targets [none, none]
  B.chain
  Keccak.inlineArms
  let t1_0 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 0 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_1 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 1 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_2 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 2 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_3 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 3 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_4 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) LX_DIGIT_GROUP 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_5 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 5 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_6 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 6 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_7 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 7 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_8 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 8 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_9 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 9 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_10 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 10 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_11 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 11 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_12 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 12 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_13 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 13 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_14 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 14 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_15 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 15 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_16 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 16 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_17 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 17 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_18 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 18 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_19 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 19 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_20 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 20 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_21 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 21 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_22 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 22 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_23 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 23 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_24 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 24 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_25 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 25 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_26 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 26 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_27 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 27 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_28 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 28 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_29 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 29 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_30 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 30 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_31 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 31 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_32 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 32 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_33 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 33 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_34 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 34 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_35 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 35 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_36 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 36 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_37 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 37 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_38 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 38 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_39 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 39 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_40 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 40 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_41 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 41 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_42 : B Unit := do
    walkGroup_8 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 42 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_43 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 43 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_44 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 44 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_45 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 45 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_46 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 46 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_47 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 47 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_48 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 48 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_49 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 49 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_50 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 50 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_51 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 51 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_52 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 52 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_53 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 53 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_54 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 54 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_55 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 55 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_56 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 56 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_57 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 57 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_58 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 58 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_59 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 59 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_60 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 60 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_61 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 61 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_62 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 62 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_63 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 63 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_64 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 64 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_65 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 65 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_66 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 66 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_67 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 67 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_68 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 68 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_69 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 69 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_70 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 70 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_71 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 71 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_72 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 72 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_73 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 73 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_74 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 74 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_75 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 75 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_76 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 76 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_77 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 77 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_78 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 78 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_79 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 79 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_80 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 80 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_81 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 81 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_82 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 82 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_83 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 83 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_84 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 84 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_85 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 85 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_86 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 86 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_87 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 87 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_88 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 88 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_89 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 89 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_90 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 90 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_91 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 91 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_92 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 92 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_93 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 93 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_94 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 94 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_95 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 95 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_96 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 96 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_97 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 97 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_98 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 98 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_99 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 99 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_100 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 100 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_101 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 101 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_102 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 102 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_103 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 103 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_104 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 104 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_105 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 105 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_106 : B Unit := do
    walkGroup_8 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 106 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_107 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 107 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_108 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 108 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_109 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 109 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_110 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 110 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_111 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 111 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_112 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 112 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_113 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 113 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_114 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 114 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_115 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 115 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_116 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 116 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_117 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 117 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_118 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 118 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_119 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 119 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_120 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 120 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_121 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 121 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_122 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 122 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_123 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 123 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_124 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 124 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_125 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 125 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_126 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 126 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_127 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 127 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_128 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 128 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_129 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 129 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_130 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 130 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_131 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 131 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_132 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 132 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_133 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 133 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_134 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 134 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_135 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 135 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_136 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 136 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_137 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 137 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_138 : B Unit := do
    walkGroup_12 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 138 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_139 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 139 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_140 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 140 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_141 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 141 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_142 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 142 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_143 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 143 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_144 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 144 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_145 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 145 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_146 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 146 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_147 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 147 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_148 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 148 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_149 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 149 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_150 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 150 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_151 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 151 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_152 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 152 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_153 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 153 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_154 : B Unit := do
    walkGroup_12 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 154 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_155 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 155 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_156 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 156 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_157 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 157 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_158 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 158 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_159 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 159 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_160 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 160 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_161 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 161 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_162 : B Unit := do
    walkGroup_14 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 162 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_163 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 163 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_164 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 164 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_165 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 165 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_166 : B Unit := do
    walkGroup_14 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 166 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_167 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 167 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_168 : B Unit := do
    walkGroup_15 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 168 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_169 : B Unit := do
    walkGroup_15 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 169 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_170 : B Unit := do
    walkGroup_16 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 170 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_171 : B Unit := do
    walkGroup_15 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 171 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_172 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 172 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_173 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 173 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_174 : B Unit := do
    walkGroup_14 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 174 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_175 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 175 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_176 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 176 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_177 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 177 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_178 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 178 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_179 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 179 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_180 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 180 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_181 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 181 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_182 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 182 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_183 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 183 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_184 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 184 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_185 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 185 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_186 : B Unit := do
    walkGroup_12 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 186 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_187 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 187 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_188 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 188 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_189 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 189 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_190 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 190 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_191 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 191 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_192 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 192 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_193 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 193 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_194 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 194 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_195 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 195 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_196 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 196 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_197 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 197 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_198 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 198 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_199 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 199 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_200 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 200 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_201 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 201 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_202 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 202 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_203 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 203 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_204 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 204 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_205 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 205 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_206 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 206 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_207 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 207 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_208 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 208 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_209 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 209 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_210 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 210 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_211 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 211 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_212 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 212 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_213 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 213 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_214 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 214 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_215 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 215 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_216 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 216 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_217 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 217 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_218 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 218 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_219 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 219 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_220 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 220 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_221 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 221 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_222 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 222 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_223 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 223 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_224 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 224 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_225 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 225 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_226 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 226 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_227 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 227 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_228 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 228 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_229 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 229 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_230 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 230 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_231 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 231 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_232 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 232 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_233 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 233 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_234 : B Unit := do
    walkGroup_8 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 234 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_235 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 235 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_236 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 236 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_237 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 237 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_238 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 238 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_239 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 239 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_240 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 240 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_241 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 241 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_242 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 242 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_243 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 243 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_244 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 244 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_245 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 245 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_246 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 246 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_247 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 247 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_248 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 248 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_249 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 249 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_250 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 250 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_251 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 251 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_252 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 252 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_253 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 253 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_254 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 254 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_255 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 255 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let _ ← B.matchArms (cellOf groups p_k) [t1_0, t1_1, t1_2, t1_3, t1_4, t1_5, t1_6, t1_7, t1_8, t1_9, t1_10, t1_11, t1_12, t1_13, t1_14, t1_15, t1_16, t1_17, t1_18, t1_19, t1_20, t1_21, t1_22, t1_23, t1_24, t1_25, t1_26, t1_27, t1_28, t1_29, t1_30, t1_31, t1_32, t1_33, t1_34, t1_35, t1_36, t1_37, t1_38, t1_39, t1_40, t1_41, t1_42, t1_43, t1_44, t1_45, t1_46, t1_47, t1_48, t1_49, t1_50, t1_51, t1_52, t1_53, t1_54, t1_55, t1_56, t1_57, t1_58, t1_59, t1_60, t1_61, t1_62, t1_63, t1_64, t1_65, t1_66, t1_67, t1_68, t1_69, t1_70, t1_71, t1_72, t1_73, t1_74, t1_75, t1_76, t1_77, t1_78, t1_79, t1_80, t1_81, t1_82, t1_83, t1_84, t1_85, t1_86, t1_87, t1_88, t1_89, t1_90, t1_91, t1_92, t1_93, t1_94, t1_95, t1_96, t1_97, t1_98, t1_99, t1_100, t1_101, t1_102, t1_103, t1_104, t1_105, t1_106, t1_107, t1_108, t1_109, t1_110, t1_111, t1_112, t1_113, t1_114, t1_115, t1_116, t1_117, t1_118, t1_119, t1_120, t1_121, t1_122, t1_123, t1_124, t1_125, t1_126, t1_127, t1_128, t1_129, t1_130, t1_131, t1_132, t1_133, t1_134, t1_135, t1_136, t1_137, t1_138, t1_139, t1_140, t1_141, t1_142, t1_143, t1_144, t1_145, t1_146, t1_147, t1_148, t1_149, t1_150, t1_151, t1_152, t1_153, t1_154, t1_155, t1_156, t1_157, t1_158, t1_159, t1_160, t1_161, t1_162, t1_163, t1_164, t1_165, t1_166, t1_167, t1_168, t1_169, t1_170, t1_171, t1_172, t1_173, t1_174, t1_175, t1_176, t1_177, t1_178, t1_179, t1_180, t1_181, t1_182, t1_183, t1_184, t1_185, t1_186, t1_187, t1_188, t1_189, t1_190, t1_191, t1_192, t1_193, t1_194, t1_195, t1_196, t1_197, t1_198, t1_199, t1_200, t1_201, t1_202, t1_203, t1_204, t1_205, t1_206, t1_207, t1_208, t1_209, t1_210, t1_211, t1_212, t1_213, t1_214, t1_215, t1_216, t1_217, t1_218, t1_219, t1_220, t1_221, t1_222, t1_223, t1_224, t1_225, t1_226, t1_227, t1_228, t1_229, t1_230, t1_231, t1_232, t1_233, t1_234, t1_235, t1_236, t1_237, t1_238, t1_239, t1_240, t1_241, t1_242, t1_243, t1_244, t1_245, t1_246, t1_247, t1_248, t1_249, t1_250, t1_251, t1_252, t1_253, t1_254, t1_255]
  digitProduct_word := cellOf t0 0
  encoded_word := cellOf t0 1
  for p_k in [1:14] do
    let t0 ← B.targets [none, none]
    B.chain
    let t1_0 : B Unit := do
      walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 0 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_1 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 1 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_2 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 2 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_3 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 3 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_4 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) LX_DIGIT_GROUP 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_5 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 5 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_6 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 6 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_7 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 7 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_8 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 8 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_9 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 9 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_10 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 10 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_11 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 11 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_12 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 12 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_13 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 13 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_14 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 14 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_15 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 15 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_16 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 16 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_17 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 17 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_18 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 18 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_19 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 19 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_20 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 20 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_21 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 21 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_22 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 22 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_23 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 23 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_24 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 24 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_25 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 25 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_26 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 26 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_27 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 27 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_28 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 28 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_29 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 29 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_30 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 30 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_31 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 31 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_32 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 32 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_33 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 33 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_34 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 34 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_35 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 35 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_36 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 36 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_37 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 37 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_38 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 38 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_39 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 39 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_40 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 40 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_41 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 41 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_42 : B Unit := do
      walkGroup_25 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 42 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_43 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 43 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_44 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 44 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_45 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 45 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_46 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 46 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_47 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 47 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_48 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 48 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_49 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 49 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_50 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 50 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_51 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 51 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_52 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 52 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_53 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 53 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_54 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 54 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_55 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 55 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_56 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 56 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_57 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 57 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_58 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 58 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_59 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 59 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_60 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 60 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_61 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 61 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_62 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 62 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_63 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 63 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_64 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 64 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_65 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 65 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_66 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 66 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_67 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 67 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_68 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 68 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_69 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 69 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_70 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 70 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_71 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 71 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_72 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 72 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_73 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 73 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_74 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 74 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_75 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 75 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_76 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 76 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_77 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 77 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_78 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 78 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_79 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 79 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_80 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 80 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_81 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 81 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_82 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 82 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_83 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 83 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_84 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 84 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_85 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 85 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_86 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 86 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_87 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 87 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_88 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 88 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_89 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 89 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_90 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 90 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_91 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 91 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_92 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 92 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_93 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 93 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_94 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 94 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_95 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 95 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_96 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 96 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_97 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 97 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_98 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 98 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_99 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 99 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_100 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 100 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_101 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 101 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_102 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 102 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_103 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 103 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_104 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 104 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_105 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 105 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_106 : B Unit := do
      walkGroup_25 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 106 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_107 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 107 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_108 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 108 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_109 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 109 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_110 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 110 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_111 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 111 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_112 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 112 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_113 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 113 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_114 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 114 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_115 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 115 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_116 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 116 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_117 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 117 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_118 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 118 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_119 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 119 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_120 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 120 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_121 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 121 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_122 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 122 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_123 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 123 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_124 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 124 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_125 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 125 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_126 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 126 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_127 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 127 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_128 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 128 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_129 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 129 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_130 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 130 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_131 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 131 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_132 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 132 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_133 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 133 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_134 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 134 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_135 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 135 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_136 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 136 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_137 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 137 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_138 : B Unit := do
      walkGroup_29 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 138 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_139 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 139 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_140 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 140 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_141 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 141 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_142 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 142 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_143 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 143 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_144 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 144 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_145 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 145 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_146 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 146 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_147 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 147 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_148 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 148 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_149 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 149 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_150 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 150 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_151 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 151 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_152 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 152 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_153 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 153 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_154 : B Unit := do
      walkGroup_29 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 154 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_155 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 155 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_156 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 156 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_157 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 157 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_158 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 158 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_159 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 159 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_160 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 160 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_161 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 161 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_162 : B Unit := do
      walkGroup_31 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 162 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_163 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 163 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_164 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 164 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_165 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 165 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_166 : B Unit := do
      walkGroup_31 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 166 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_167 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 167 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_168 : B Unit := do
      walkGroup_32 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 168 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_169 : B Unit := do
      walkGroup_32 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 169 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_170 : B Unit := do
      walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 170 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_171 : B Unit := do
      walkGroup_32 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 171 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_172 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 172 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_173 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 173 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_174 : B Unit := do
      walkGroup_31 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 174 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_175 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 175 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_176 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 176 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_177 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 177 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_178 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 178 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_179 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 179 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_180 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 180 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_181 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 181 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_182 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 182 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_183 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 183 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_184 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 184 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_185 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 185 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_186 : B Unit := do
      walkGroup_29 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 186 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_187 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 187 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_188 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 188 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_189 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 189 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_190 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 190 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_191 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 191 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_192 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 192 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_193 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 193 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_194 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 194 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_195 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 195 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_196 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 196 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_197 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 197 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_198 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 198 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_199 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 199 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_200 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 200 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_201 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 201 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_202 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 202 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_203 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 203 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_204 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 204 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_205 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 205 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_206 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 206 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_207 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 207 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_208 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 208 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_209 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 209 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_210 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 210 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_211 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 211 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_212 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 212 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_213 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 213 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_214 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 214 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_215 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 215 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_216 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 216 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_217 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 217 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_218 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 218 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_219 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 219 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_220 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 220 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_221 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 221 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_222 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 222 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_223 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 223 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_224 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 224 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_225 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 225 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_226 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 226 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_227 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 227 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_228 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 228 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_229 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 229 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_230 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 230 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_231 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 231 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_232 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 232 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_233 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 233 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_234 : B Unit := do
      walkGroup_25 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 234 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_235 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 235 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_236 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 236 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_237 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 237 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_238 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 238 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_239 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 239 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_240 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 240 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_241 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 241 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_242 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 242 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_243 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 243 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_244 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 244 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_245 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 245 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_246 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 246 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_247 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 247 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_248 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 248 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_249 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 249 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_250 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 250 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_251 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 251 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_252 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 252 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_253 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 253 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_254 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 254 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_255 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 255 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let _ ← B.matchArms (cellOf groups p_k) [t1_0, t1_1, t1_2, t1_3, t1_4, t1_5, t1_6, t1_7, t1_8, t1_9, t1_10, t1_11, t1_12, t1_13, t1_14, t1_15, t1_16, t1_17, t1_18, t1_19, t1_20, t1_21, t1_22, t1_23, t1_24, t1_25, t1_26, t1_27, t1_28, t1_29, t1_30, t1_31, t1_32, t1_33, t1_34, t1_35, t1_36, t1_37, t1_38, t1_39, t1_40, t1_41, t1_42, t1_43, t1_44, t1_45, t1_46, t1_47, t1_48, t1_49, t1_50, t1_51, t1_52, t1_53, t1_54, t1_55, t1_56, t1_57, t1_58, t1_59, t1_60, t1_61, t1_62, t1_63, t1_64, t1_65, t1_66, t1_67, t1_68, t1_69, t1_70, t1_71, t1_72, t1_73, t1_74, t1_75, t1_76, t1_77, t1_78, t1_79, t1_80, t1_81, t1_82, t1_83, t1_84, t1_85, t1_86, t1_87, t1_88, t1_89, t1_90, t1_91, t1_92, t1_93, t1_94, t1_95, t1_96, t1_97, t1_98, t1_99, t1_100, t1_101, t1_102, t1_103, t1_104, t1_105, t1_106, t1_107, t1_108, t1_109, t1_110, t1_111, t1_112, t1_113, t1_114, t1_115, t1_116, t1_117, t1_118, t1_119, t1_120, t1_121, t1_122, t1_123, t1_124, t1_125, t1_126, t1_127, t1_128, t1_129, t1_130, t1_131, t1_132, t1_133, t1_134, t1_135, t1_136, t1_137, t1_138, t1_139, t1_140, t1_141, t1_142, t1_143, t1_144, t1_145, t1_146, t1_147, t1_148, t1_149, t1_150, t1_151, t1_152, t1_153, t1_154, t1_155, t1_156, t1_157, t1_158, t1_159, t1_160, t1_161, t1_162, t1_163, t1_164, t1_165, t1_166, t1_167, t1_168, t1_169, t1_170, t1_171, t1_172, t1_173, t1_174, t1_175, t1_176, t1_177, t1_178, t1_179, t1_180, t1_181, t1_182, t1_183, t1_184, t1_185, t1_186, t1_187, t1_188, t1_189, t1_190, t1_191, t1_192, t1_193, t1_194, t1_195, t1_196, t1_197, t1_198, t1_199, t1_200, t1_201, t1_202, t1_203, t1_204, t1_205, t1_206, t1_207, t1_208, t1_209, t1_210, t1_211, t1_212, t1_213, t1_214, t1_215, t1_216, t1_217, t1_218, t1_219, t1_220, t1_221, t1_222, t1_223, t1_224, t1_225, t1_226, t1_227, t1_228, t1_229, t1_230, t1_231, t1_232, t1_233, t1_234, t1_235, t1_236, t1_237, t1_238, t1_239, t1_240, t1_241, t1_242, t1_243, t1_244, t1_245, t1_246, t1_247, t1_248, t1_249, t1_250, t1_251, t1_252, t1_253, t1_254, t1_255]
    digitProduct_word := cellOf t0 0
    encoded_word := cellOf t0 1
  let p_k := 14
  let t0 ← B.targets [none, none]
  let t1_0 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 0 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_1 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 1 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_2 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 2 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_3 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 3 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_4 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) LX_DIGIT_GROUP 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_5 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 5 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_6 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 6 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_7 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 7 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_8 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 8 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_9 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 9 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_10 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 10 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_11 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 11 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_12 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 12 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_13 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 13 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_14 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 14 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_15 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 15 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_16 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 16 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_17 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 17 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_18 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 18 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_19 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 19 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_20 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 20 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_21 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 21 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_22 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 22 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_23 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 23 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_24 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 24 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_25 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 25 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_26 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 26 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_27 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 27 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_28 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 28 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_29 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 29 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_30 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 30 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_31 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 31 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_32 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 32 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_33 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 33 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_34 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 34 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_35 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 35 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_36 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 36 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_37 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 37 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_38 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 38 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_39 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 39 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_40 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 40 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_41 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 41 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_42 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 42 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_43 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 43 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_44 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 44 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_45 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 45 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_46 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 46 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_47 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 47 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_48 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 48 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_49 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 49 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_50 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 50 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_51 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 51 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_52 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 52 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_53 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 53 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_54 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 54 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_55 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 55 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_56 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 56 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_57 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 57 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_58 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 58 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_59 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 59 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_60 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 60 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_61 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 61 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_62 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 62 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_63 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 63 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_64 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 64 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_65 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 65 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_66 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 66 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_67 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 67 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_68 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 68 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_69 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 69 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_70 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 70 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_71 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 71 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_72 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 72 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_73 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 73 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_74 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 74 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_75 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 75 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_76 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 76 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_77 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 77 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_78 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 78 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_79 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 79 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_80 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 80 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_81 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 81 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_82 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 82 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_83 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 83 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_84 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 84 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_85 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 85 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_86 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 86 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_87 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 87 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_88 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 88 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_89 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 89 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_90 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 90 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_91 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 91 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_92 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 92 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_93 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 93 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_94 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 94 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_95 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 95 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_96 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 96 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_97 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 97 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_98 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 98 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_99 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 99 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_100 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 100 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_101 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 101 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_102 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 102 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_103 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 103 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_104 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 104 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_105 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 105 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_106 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 106 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_107 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 107 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_108 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 108 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_109 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 109 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_110 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 110 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_111 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 111 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_112 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 112 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_113 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 113 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_114 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 114 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_115 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 115 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_116 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 116 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_117 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 117 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_118 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 118 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_119 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 119 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_120 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 120 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_121 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 121 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_122 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 122 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_123 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 123 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_124 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 124 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_125 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 125 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_126 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 126 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_127 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 127 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_128 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 128 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_129 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 129 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_130 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 130 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_131 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 131 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_132 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 132 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_133 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 133 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_134 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 134 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_135 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 135 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_136 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 136 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_137 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 137 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_138 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 138 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_139 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 139 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_140 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 140 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_141 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 141 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_142 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 142 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_143 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 143 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_144 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 144 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_145 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 145 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_146 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 146 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_147 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 147 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_148 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 148 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_149 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 149 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_150 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 150 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_151 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 151 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_152 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 152 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_153 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 153 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_154 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 154 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_155 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 155 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_156 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 156 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_157 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 157 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_158 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 158 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_159 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 159 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_160 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 160 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_161 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 161 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_162 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 162 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_163 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 163 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_164 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 164 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_165 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 165 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_166 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 166 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_167 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 167 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_168 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 168 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_169 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 169 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_170 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 170 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_171 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 171 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_172 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 172 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_173 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 173 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_174 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 174 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_175 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 175 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_176 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 176 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_177 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 177 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_178 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 178 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_179 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 179 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_180 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 180 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_181 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 181 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_182 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 182 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_183 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 183 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_184 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 184 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_185 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 185 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_186 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 186 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_187 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 187 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_188 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 188 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_189 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 189 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_190 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 190 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_191 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 191 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_192 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 192 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_193 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 193 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_194 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 194 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_195 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 195 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_196 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 196 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_197 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 197 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_198 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 198 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_199 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 199 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_200 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 200 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_201 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 201 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_202 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 202 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_203 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 203 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_204 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 204 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_205 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 205 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_206 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 206 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_207 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 207 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_208 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 208 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_209 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 209 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_210 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 210 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_211 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 211 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_212 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 212 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_213 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 213 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_214 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 214 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_215 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 215 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_216 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 216 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_217 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 217 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_218 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 218 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_219 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 219 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_220 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 220 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_221 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 221 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_222 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 222 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_223 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 223 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_224 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 224 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_225 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 225 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_226 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 226 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_227 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 227 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_228 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 228 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_229 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 229 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_230 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 230 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_231 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 231 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_232 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 232 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_233 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 233 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_234 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 234 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_235 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 235 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_236 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 236 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_237 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 237 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_238 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 238 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_239 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 239 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_240 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 240 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_241 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 241 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_242 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 242 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_243 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 243 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_244 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 244 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_245 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 245 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_246 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 246 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_247 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 247 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_248 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 248 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_249 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 249 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_250 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 250 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_251 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 251 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_252 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 252 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_253 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 253 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_254 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 254 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_255 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 255 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let _ ← B.matchArms (cellOf groups p_k) [t1_0, t1_1, t1_2, t1_3, t1_4, t1_5, t1_6, t1_7, t1_8, t1_9, t1_10, t1_11, t1_12, t1_13, t1_14, t1_15, t1_16, t1_17, t1_18, t1_19, t1_20, t1_21, t1_22, t1_23, t1_24, t1_25, t1_26, t1_27, t1_28, t1_29, t1_30, t1_31, t1_32, t1_33, t1_34, t1_35, t1_36, t1_37, t1_38, t1_39, t1_40, t1_41, t1_42, t1_43, t1_44, t1_45, t1_46, t1_47, t1_48, t1_49, t1_50, t1_51, t1_52, t1_53, t1_54, t1_55, t1_56, t1_57, t1_58, t1_59, t1_60, t1_61, t1_62, t1_63, t1_64, t1_65, t1_66, t1_67, t1_68, t1_69, t1_70, t1_71, t1_72, t1_73, t1_74, t1_75, t1_76, t1_77, t1_78, t1_79, t1_80, t1_81, t1_82, t1_83, t1_84, t1_85, t1_86, t1_87, t1_88, t1_89, t1_90, t1_91, t1_92, t1_93, t1_94, t1_95, t1_96, t1_97, t1_98, t1_99, t1_100, t1_101, t1_102, t1_103, t1_104, t1_105, t1_106, t1_107, t1_108, t1_109, t1_110, t1_111, t1_112, t1_113, t1_114, t1_115, t1_116, t1_117, t1_118, t1_119, t1_120, t1_121, t1_122, t1_123, t1_124, t1_125, t1_126, t1_127, t1_128, t1_129, t1_130, t1_131, t1_132, t1_133, t1_134, t1_135, t1_136, t1_137, t1_138, t1_139, t1_140, t1_141, t1_142, t1_143, t1_144, t1_145, t1_146, t1_147, t1_148, t1_149, t1_150, t1_151, t1_152, t1_153, t1_154, t1_155, t1_156, t1_157, t1_158, t1_159, t1_160, t1_161, t1_162, t1_163, t1_164, t1_165, t1_166, t1_167, t1_168, t1_169, t1_170, t1_171, t1_172, t1_173, t1_174, t1_175, t1_176, t1_177, t1_178, t1_179, t1_180, t1_181, t1_182, t1_183, t1_184, t1_185, t1_186, t1_187, t1_188, t1_189, t1_190, t1_191, t1_192, t1_193, t1_194, t1_195, t1_196, t1_197, t1_198, t1_199, t1_200, t1_201, t1_202, t1_203, t1_204, t1_205, t1_206, t1_207, t1_208, t1_209, t1_210, t1_211, t1_212, t1_213, t1_214, t1_215, t1_216, t1_217, t1_218, t1_219, t1_220, t1_221, t1_222, t1_223, t1_224, t1_225, t1_226, t1_227, t1_228, t1_229, t1_230, t1_231, t1_232, t1_233, t1_234, t1_235, t1_236, t1_237, t1_238, t1_239, t1_240, t1_241, t1_242, t1_243, t1_244, t1_245, t1_246, t1_247, t1_248, t1_249, t1_250, t1_251, t1_252, t1_253, t1_254, t1_255]
  digitProduct_word := cellOf t0 0
  encoded_word := cellOf t0 1
  B.copy (cellOf digest 0) encoded_word
  B.assertEq digitProduct_word (← B.const (gpowE LX_TARGET_SUM))
  let leaf ← B.stackBuf 1
  wotsLeaf pp (← B.add idx (← B.const (lit TW_LEAF))) walks LX_V leaf
  let mut cur := cellOf leaf 0
  for v_k in [0:LX_LAYER_WINDOWS] do
    w := (layer_k * LX_LAYER_WINDOWS) + v_k
    out ← B.stackBuf 1
    let _ ← B.rangeCheck (cellOf windows w) LX_WINDOW_ARMS
    if (w + 1) = LX_WINDOWS then
      pure () -- no use of this definition takes this branch
    else
      let t2 ← B.targets [some (cellOf his w).v]
      Keccak.inlineArms
      let t3_0 : B Unit := do
        lxWindow cur pp powers his out w 0 [(cellOf t2 0).v]
      let t3_1 : B Unit := do
        lxWindow_2 cur pp powers his out w 1 [(cellOf t2 0).v]
      let t3_2 : B Unit := do
        lxWindow_2 cur pp powers his out w 2 [(cellOf t2 0).v]
      let t3_3 : B Unit := do
        lxWindow_2 cur pp powers his out w 3 [(cellOf t2 0).v]
      let t3_4 : B Unit := do
        lxWindow_2 cur pp powers his out w 4 [(cellOf t2 0).v]
      let t3_5 : B Unit := do
        lxWindow_2 cur pp powers his out w 5 [(cellOf t2 0).v]
      let t3_6 : B Unit := do
        lxWindow_2 cur pp powers his out w 6 [(cellOf t2 0).v]
      let t3_7 : B Unit := do
        lxWindow_2 cur pp powers his out w 7 [(cellOf t2 0).v]
      let t3_8 : B Unit := do
        lxWindow_2 cur pp powers his out w 8 [(cellOf t2 0).v]
      let t3_9 : B Unit := do
        lxWindow_2 cur pp powers his out w 9 [(cellOf t2 0).v]
      let t3_10 : B Unit := do
        lxWindow_2 cur pp powers his out w 10 [(cellOf t2 0).v]
      let t3_11 : B Unit := do
        lxWindow_2 cur pp powers his out w 11 [(cellOf t2 0).v]
      let t3_12 : B Unit := do
        lxWindow_2 cur pp powers his out w 12 [(cellOf t2 0).v]
      let t3_13 : B Unit := do
        lxWindow_2 cur pp powers his out w 13 [(cellOf t2 0).v]
      let t3_14 : B Unit := do
        lxWindow_2 cur pp powers his out w 14 [(cellOf t2 0).v]
      let t3_15 : B Unit := do
        lxWindow_2 cur pp powers his out w 15 [(cellOf t2 0).v]
      let t3_16 : B Unit := do
        lxWindow_2 cur pp powers his out w 16 [(cellOf t2 0).v]
      let t3_17 : B Unit := do
        lxWindow_2 cur pp powers his out w 17 [(cellOf t2 0).v]
      let t3_18 : B Unit := do
        lxWindow_2 cur pp powers his out w 18 [(cellOf t2 0).v]
      let t3_19 : B Unit := do
        lxWindow_2 cur pp powers his out w 19 [(cellOf t2 0).v]
      let t3_20 : B Unit := do
        lxWindow_2 cur pp powers his out w 20 [(cellOf t2 0).v]
      let t3_21 : B Unit := do
        lxWindow_2 cur pp powers his out w 21 [(cellOf t2 0).v]
      let t3_22 : B Unit := do
        lxWindow_2 cur pp powers his out w 22 [(cellOf t2 0).v]
      let t3_23 : B Unit := do
        lxWindow_2 cur pp powers his out w 23 [(cellOf t2 0).v]
      let t3_24 : B Unit := do
        lxWindow_2 cur pp powers his out w 24 [(cellOf t2 0).v]
      let t3_25 : B Unit := do
        lxWindow_2 cur pp powers his out w 25 [(cellOf t2 0).v]
      let t3_26 : B Unit := do
        lxWindow_2 cur pp powers his out w 26 [(cellOf t2 0).v]
      let t3_27 : B Unit := do
        lxWindow_2 cur pp powers his out w 27 [(cellOf t2 0).v]
      let t3_28 : B Unit := do
        lxWindow_2 cur pp powers his out w 28 [(cellOf t2 0).v]
      let t3_29 : B Unit := do
        lxWindow_2 cur pp powers his out w 29 [(cellOf t2 0).v]
      let t3_30 : B Unit := do
        lxWindow_2 cur pp powers his out w 30 [(cellOf t2 0).v]
      let t3_31 : B Unit := do
        lxWindow_2 cur pp powers his out w 31 [(cellOf t2 0).v]
      let t3_32 : B Unit := do
        lxWindow_2 cur pp powers his out w 32 [(cellOf t2 0).v]
      let t3_33 : B Unit := do
        lxWindow_2 cur pp powers his out w 33 [(cellOf t2 0).v]
      let t3_34 : B Unit := do
        lxWindow_2 cur pp powers his out w 34 [(cellOf t2 0).v]
      let t3_35 : B Unit := do
        lxWindow_2 cur pp powers his out w 35 [(cellOf t2 0).v]
      let t3_36 : B Unit := do
        lxWindow_2 cur pp powers his out w 36 [(cellOf t2 0).v]
      let t3_37 : B Unit := do
        lxWindow_2 cur pp powers his out w 37 [(cellOf t2 0).v]
      let t3_38 : B Unit := do
        lxWindow_2 cur pp powers his out w 38 [(cellOf t2 0).v]
      let t3_39 : B Unit := do
        lxWindow_2 cur pp powers his out w 39 [(cellOf t2 0).v]
      let t3_40 : B Unit := do
        lxWindow_2 cur pp powers his out w 40 [(cellOf t2 0).v]
      let t3_41 : B Unit := do
        lxWindow_2 cur pp powers his out w 41 [(cellOf t2 0).v]
      let t3_42 : B Unit := do
        lxWindow_2 cur pp powers his out w 42 [(cellOf t2 0).v]
      let t3_43 : B Unit := do
        lxWindow_2 cur pp powers his out w 43 [(cellOf t2 0).v]
      let t3_44 : B Unit := do
        lxWindow_2 cur pp powers his out w 44 [(cellOf t2 0).v]
      let t3_45 : B Unit := do
        lxWindow_2 cur pp powers his out w 45 [(cellOf t2 0).v]
      let t3_46 : B Unit := do
        lxWindow_2 cur pp powers his out w 46 [(cellOf t2 0).v]
      let t3_47 : B Unit := do
        lxWindow_2 cur pp powers his out w 47 [(cellOf t2 0).v]
      let t3_48 : B Unit := do
        lxWindow_2 cur pp powers his out w 48 [(cellOf t2 0).v]
      let t3_49 : B Unit := do
        lxWindow_2 cur pp powers his out w 49 [(cellOf t2 0).v]
      let t3_50 : B Unit := do
        lxWindow_2 cur pp powers his out w 50 [(cellOf t2 0).v]
      let t3_51 : B Unit := do
        lxWindow_2 cur pp powers his out w 51 [(cellOf t2 0).v]
      let t3_52 : B Unit := do
        lxWindow_2 cur pp powers his out w 52 [(cellOf t2 0).v]
      let t3_53 : B Unit := do
        lxWindow_2 cur pp powers his out w 53 [(cellOf t2 0).v]
      let t3_54 : B Unit := do
        lxWindow_2 cur pp powers his out w 54 [(cellOf t2 0).v]
      let t3_55 : B Unit := do
        lxWindow_2 cur pp powers his out w 55 [(cellOf t2 0).v]
      let t3_56 : B Unit := do
        lxWindow_2 cur pp powers his out w 56 [(cellOf t2 0).v]
      let t3_57 : B Unit := do
        lxWindow_2 cur pp powers his out w 57 [(cellOf t2 0).v]
      let t3_58 : B Unit := do
        lxWindow_2 cur pp powers his out w 58 [(cellOf t2 0).v]
      let t3_59 : B Unit := do
        lxWindow_2 cur pp powers his out w 59 [(cellOf t2 0).v]
      let t3_60 : B Unit := do
        lxWindow_2 cur pp powers his out w 60 [(cellOf t2 0).v]
      let t3_61 : B Unit := do
        lxWindow_2 cur pp powers his out w 61 [(cellOf t2 0).v]
      let t3_62 : B Unit := do
        lxWindow_2 cur pp powers his out w 62 [(cellOf t2 0).v]
      let t3_63 : B Unit := do
        lxWindow_2 cur pp powers his out w 63 [(cellOf t2 0).v]
      let t3_64 : B Unit := do
        lxWindow_2 cur pp powers his out w 64 [(cellOf t2 0).v]
      let t3_65 : B Unit := do
        lxWindow_2 cur pp powers his out w 65 [(cellOf t2 0).v]
      let t3_66 : B Unit := do
        lxWindow_2 cur pp powers his out w 66 [(cellOf t2 0).v]
      let t3_67 : B Unit := do
        lxWindow_2 cur pp powers his out w 67 [(cellOf t2 0).v]
      let t3_68 : B Unit := do
        lxWindow_2 cur pp powers his out w 68 [(cellOf t2 0).v]
      let t3_69 : B Unit := do
        lxWindow_2 cur pp powers his out w 69 [(cellOf t2 0).v]
      let t3_70 : B Unit := do
        lxWindow_2 cur pp powers his out w 70 [(cellOf t2 0).v]
      let t3_71 : B Unit := do
        lxWindow_2 cur pp powers his out w 71 [(cellOf t2 0).v]
      let t3_72 : B Unit := do
        lxWindow_2 cur pp powers his out w 72 [(cellOf t2 0).v]
      let t3_73 : B Unit := do
        lxWindow_2 cur pp powers his out w 73 [(cellOf t2 0).v]
      let t3_74 : B Unit := do
        lxWindow_2 cur pp powers his out w 74 [(cellOf t2 0).v]
      let t3_75 : B Unit := do
        lxWindow_2 cur pp powers his out w 75 [(cellOf t2 0).v]
      let t3_76 : B Unit := do
        lxWindow_2 cur pp powers his out w 76 [(cellOf t2 0).v]
      let t3_77 : B Unit := do
        lxWindow_2 cur pp powers his out w 77 [(cellOf t2 0).v]
      let t3_78 : B Unit := do
        lxWindow_2 cur pp powers his out w 78 [(cellOf t2 0).v]
      let t3_79 : B Unit := do
        lxWindow_2 cur pp powers his out w 79 [(cellOf t2 0).v]
      let t3_80 : B Unit := do
        lxWindow_2 cur pp powers his out w 80 [(cellOf t2 0).v]
      let t3_81 : B Unit := do
        lxWindow_2 cur pp powers his out w 81 [(cellOf t2 0).v]
      let t3_82 : B Unit := do
        lxWindow_2 cur pp powers his out w 82 [(cellOf t2 0).v]
      let t3_83 : B Unit := do
        lxWindow_2 cur pp powers his out w 83 [(cellOf t2 0).v]
      let t3_84 : B Unit := do
        lxWindow_2 cur pp powers his out w 84 [(cellOf t2 0).v]
      let t3_85 : B Unit := do
        lxWindow_2 cur pp powers his out w 85 [(cellOf t2 0).v]
      let t3_86 : B Unit := do
        lxWindow_2 cur pp powers his out w 86 [(cellOf t2 0).v]
      let t3_87 : B Unit := do
        lxWindow_2 cur pp powers his out w 87 [(cellOf t2 0).v]
      let t3_88 : B Unit := do
        lxWindow_2 cur pp powers his out w 88 [(cellOf t2 0).v]
      let t3_89 : B Unit := do
        lxWindow_2 cur pp powers his out w 89 [(cellOf t2 0).v]
      let t3_90 : B Unit := do
        lxWindow_2 cur pp powers his out w 90 [(cellOf t2 0).v]
      let t3_91 : B Unit := do
        lxWindow_2 cur pp powers his out w 91 [(cellOf t2 0).v]
      let t3_92 : B Unit := do
        lxWindow_2 cur pp powers his out w 92 [(cellOf t2 0).v]
      let t3_93 : B Unit := do
        lxWindow_2 cur pp powers his out w 93 [(cellOf t2 0).v]
      let t3_94 : B Unit := do
        lxWindow_2 cur pp powers his out w 94 [(cellOf t2 0).v]
      let t3_95 : B Unit := do
        lxWindow_2 cur pp powers his out w 95 [(cellOf t2 0).v]
      let t3_96 : B Unit := do
        lxWindow_2 cur pp powers his out w 96 [(cellOf t2 0).v]
      let t3_97 : B Unit := do
        lxWindow_2 cur pp powers his out w 97 [(cellOf t2 0).v]
      let t3_98 : B Unit := do
        lxWindow_2 cur pp powers his out w 98 [(cellOf t2 0).v]
      let t3_99 : B Unit := do
        lxWindow_2 cur pp powers his out w 99 [(cellOf t2 0).v]
      let t3_100 : B Unit := do
        lxWindow_2 cur pp powers his out w 100 [(cellOf t2 0).v]
      let t3_101 : B Unit := do
        lxWindow_2 cur pp powers his out w 101 [(cellOf t2 0).v]
      let t3_102 : B Unit := do
        lxWindow_2 cur pp powers his out w 102 [(cellOf t2 0).v]
      let t3_103 : B Unit := do
        lxWindow_2 cur pp powers his out w 103 [(cellOf t2 0).v]
      let t3_104 : B Unit := do
        lxWindow_2 cur pp powers his out w 104 [(cellOf t2 0).v]
      let t3_105 : B Unit := do
        lxWindow_2 cur pp powers his out w 105 [(cellOf t2 0).v]
      let t3_106 : B Unit := do
        lxWindow_2 cur pp powers his out w 106 [(cellOf t2 0).v]
      let t3_107 : B Unit := do
        lxWindow_2 cur pp powers his out w 107 [(cellOf t2 0).v]
      let t3_108 : B Unit := do
        lxWindow_2 cur pp powers his out w 108 [(cellOf t2 0).v]
      let t3_109 : B Unit := do
        lxWindow_2 cur pp powers his out w 109 [(cellOf t2 0).v]
      let t3_110 : B Unit := do
        lxWindow_2 cur pp powers his out w 110 [(cellOf t2 0).v]
      let t3_111 : B Unit := do
        lxWindow_2 cur pp powers his out w 111 [(cellOf t2 0).v]
      let t3_112 : B Unit := do
        lxWindow_2 cur pp powers his out w 112 [(cellOf t2 0).v]
      let t3_113 : B Unit := do
        lxWindow_2 cur pp powers his out w 113 [(cellOf t2 0).v]
      let t3_114 : B Unit := do
        lxWindow_2 cur pp powers his out w 114 [(cellOf t2 0).v]
      let t3_115 : B Unit := do
        lxWindow_2 cur pp powers his out w 115 [(cellOf t2 0).v]
      let t3_116 : B Unit := do
        lxWindow_2 cur pp powers his out w 116 [(cellOf t2 0).v]
      let t3_117 : B Unit := do
        lxWindow_2 cur pp powers his out w 117 [(cellOf t2 0).v]
      let t3_118 : B Unit := do
        lxWindow_2 cur pp powers his out w 118 [(cellOf t2 0).v]
      let t3_119 : B Unit := do
        lxWindow_2 cur pp powers his out w 119 [(cellOf t2 0).v]
      let t3_120 : B Unit := do
        lxWindow_2 cur pp powers his out w 120 [(cellOf t2 0).v]
      let t3_121 : B Unit := do
        lxWindow_2 cur pp powers his out w 121 [(cellOf t2 0).v]
      let t3_122 : B Unit := do
        lxWindow_2 cur pp powers his out w 122 [(cellOf t2 0).v]
      let t3_123 : B Unit := do
        lxWindow_2 cur pp powers his out w 123 [(cellOf t2 0).v]
      let t3_124 : B Unit := do
        lxWindow_2 cur pp powers his out w 124 [(cellOf t2 0).v]
      let t3_125 : B Unit := do
        lxWindow_2 cur pp powers his out w 125 [(cellOf t2 0).v]
      let t3_126 : B Unit := do
        lxWindow_2 cur pp powers his out w 126 [(cellOf t2 0).v]
      let t3_127 : B Unit := do
        lxWindow_2 cur pp powers his out w 127 [(cellOf t2 0).v]
      let t3_128 : B Unit := do
        lxWindow_2 cur pp powers his out w 128 [(cellOf t2 0).v]
      let t3_129 : B Unit := do
        lxWindow_2 cur pp powers his out w 129 [(cellOf t2 0).v]
      let t3_130 : B Unit := do
        lxWindow_2 cur pp powers his out w 130 [(cellOf t2 0).v]
      let t3_131 : B Unit := do
        lxWindow_2 cur pp powers his out w 131 [(cellOf t2 0).v]
      let t3_132 : B Unit := do
        lxWindow_2 cur pp powers his out w 132 [(cellOf t2 0).v]
      let t3_133 : B Unit := do
        lxWindow_2 cur pp powers his out w 133 [(cellOf t2 0).v]
      let t3_134 : B Unit := do
        lxWindow_2 cur pp powers his out w 134 [(cellOf t2 0).v]
      let t3_135 : B Unit := do
        lxWindow_2 cur pp powers his out w 135 [(cellOf t2 0).v]
      let t3_136 : B Unit := do
        lxWindow_2 cur pp powers his out w 136 [(cellOf t2 0).v]
      let t3_137 : B Unit := do
        lxWindow_2 cur pp powers his out w 137 [(cellOf t2 0).v]
      let t3_138 : B Unit := do
        lxWindow_2 cur pp powers his out w 138 [(cellOf t2 0).v]
      let t3_139 : B Unit := do
        lxWindow_2 cur pp powers his out w 139 [(cellOf t2 0).v]
      let t3_140 : B Unit := do
        lxWindow_2 cur pp powers his out w 140 [(cellOf t2 0).v]
      let t3_141 : B Unit := do
        lxWindow_2 cur pp powers his out w 141 [(cellOf t2 0).v]
      let t3_142 : B Unit := do
        lxWindow_2 cur pp powers his out w 142 [(cellOf t2 0).v]
      let t3_143 : B Unit := do
        lxWindow_2 cur pp powers his out w 143 [(cellOf t2 0).v]
      let t3_144 : B Unit := do
        lxWindow_2 cur pp powers his out w 144 [(cellOf t2 0).v]
      let t3_145 : B Unit := do
        lxWindow_2 cur pp powers his out w 145 [(cellOf t2 0).v]
      let t3_146 : B Unit := do
        lxWindow_2 cur pp powers his out w 146 [(cellOf t2 0).v]
      let t3_147 : B Unit := do
        lxWindow_2 cur pp powers his out w 147 [(cellOf t2 0).v]
      let t3_148 : B Unit := do
        lxWindow_2 cur pp powers his out w 148 [(cellOf t2 0).v]
      let t3_149 : B Unit := do
        lxWindow_2 cur pp powers his out w 149 [(cellOf t2 0).v]
      let t3_150 : B Unit := do
        lxWindow_2 cur pp powers his out w 150 [(cellOf t2 0).v]
      let t3_151 : B Unit := do
        lxWindow_2 cur pp powers his out w 151 [(cellOf t2 0).v]
      let t3_152 : B Unit := do
        lxWindow_2 cur pp powers his out w 152 [(cellOf t2 0).v]
      let t3_153 : B Unit := do
        lxWindow_2 cur pp powers his out w 153 [(cellOf t2 0).v]
      let t3_154 : B Unit := do
        lxWindow_2 cur pp powers his out w 154 [(cellOf t2 0).v]
      let t3_155 : B Unit := do
        lxWindow_2 cur pp powers his out w 155 [(cellOf t2 0).v]
      let t3_156 : B Unit := do
        lxWindow_2 cur pp powers his out w 156 [(cellOf t2 0).v]
      let t3_157 : B Unit := do
        lxWindow_2 cur pp powers his out w 157 [(cellOf t2 0).v]
      let t3_158 : B Unit := do
        lxWindow_2 cur pp powers his out w 158 [(cellOf t2 0).v]
      let t3_159 : B Unit := do
        lxWindow_2 cur pp powers his out w 159 [(cellOf t2 0).v]
      let t3_160 : B Unit := do
        lxWindow_2 cur pp powers his out w 160 [(cellOf t2 0).v]
      let t3_161 : B Unit := do
        lxWindow_2 cur pp powers his out w 161 [(cellOf t2 0).v]
      let t3_162 : B Unit := do
        lxWindow_2 cur pp powers his out w 162 [(cellOf t2 0).v]
      let t3_163 : B Unit := do
        lxWindow_2 cur pp powers his out w 163 [(cellOf t2 0).v]
      let t3_164 : B Unit := do
        lxWindow_2 cur pp powers his out w 164 [(cellOf t2 0).v]
      let t3_165 : B Unit := do
        lxWindow_2 cur pp powers his out w 165 [(cellOf t2 0).v]
      let t3_166 : B Unit := do
        lxWindow_2 cur pp powers his out w 166 [(cellOf t2 0).v]
      let t3_167 : B Unit := do
        lxWindow_2 cur pp powers his out w 167 [(cellOf t2 0).v]
      let t3_168 : B Unit := do
        lxWindow_2 cur pp powers his out w 168 [(cellOf t2 0).v]
      let t3_169 : B Unit := do
        lxWindow_2 cur pp powers his out w 169 [(cellOf t2 0).v]
      let t3_170 : B Unit := do
        lxWindow_2 cur pp powers his out w 170 [(cellOf t2 0).v]
      let t3_171 : B Unit := do
        lxWindow_2 cur pp powers his out w 171 [(cellOf t2 0).v]
      let t3_172 : B Unit := do
        lxWindow_2 cur pp powers his out w 172 [(cellOf t2 0).v]
      let t3_173 : B Unit := do
        lxWindow_2 cur pp powers his out w 173 [(cellOf t2 0).v]
      let t3_174 : B Unit := do
        lxWindow_2 cur pp powers his out w 174 [(cellOf t2 0).v]
      let t3_175 : B Unit := do
        lxWindow_2 cur pp powers his out w 175 [(cellOf t2 0).v]
      let t3_176 : B Unit := do
        lxWindow_2 cur pp powers his out w 176 [(cellOf t2 0).v]
      let t3_177 : B Unit := do
        lxWindow_2 cur pp powers his out w 177 [(cellOf t2 0).v]
      let t3_178 : B Unit := do
        lxWindow_2 cur pp powers his out w 178 [(cellOf t2 0).v]
      let t3_179 : B Unit := do
        lxWindow_2 cur pp powers his out w 179 [(cellOf t2 0).v]
      let t3_180 : B Unit := do
        lxWindow_2 cur pp powers his out w 180 [(cellOf t2 0).v]
      let t3_181 : B Unit := do
        lxWindow_2 cur pp powers his out w 181 [(cellOf t2 0).v]
      let t3_182 : B Unit := do
        lxWindow_2 cur pp powers his out w 182 [(cellOf t2 0).v]
      let t3_183 : B Unit := do
        lxWindow_2 cur pp powers his out w 183 [(cellOf t2 0).v]
      let t3_184 : B Unit := do
        lxWindow_2 cur pp powers his out w 184 [(cellOf t2 0).v]
      let t3_185 : B Unit := do
        lxWindow_2 cur pp powers his out w 185 [(cellOf t2 0).v]
      let t3_186 : B Unit := do
        lxWindow_2 cur pp powers his out w 186 [(cellOf t2 0).v]
      let t3_187 : B Unit := do
        lxWindow_2 cur pp powers his out w 187 [(cellOf t2 0).v]
      let t3_188 : B Unit := do
        lxWindow_2 cur pp powers his out w 188 [(cellOf t2 0).v]
      let t3_189 : B Unit := do
        lxWindow_2 cur pp powers his out w 189 [(cellOf t2 0).v]
      let t3_190 : B Unit := do
        lxWindow_2 cur pp powers his out w 190 [(cellOf t2 0).v]
      let t3_191 : B Unit := do
        lxWindow_2 cur pp powers his out w 191 [(cellOf t2 0).v]
      let t3_192 : B Unit := do
        lxWindow_2 cur pp powers his out w 192 [(cellOf t2 0).v]
      let t3_193 : B Unit := do
        lxWindow_2 cur pp powers his out w 193 [(cellOf t2 0).v]
      let t3_194 : B Unit := do
        lxWindow_2 cur pp powers his out w 194 [(cellOf t2 0).v]
      let t3_195 : B Unit := do
        lxWindow_2 cur pp powers his out w 195 [(cellOf t2 0).v]
      let t3_196 : B Unit := do
        lxWindow_2 cur pp powers his out w 196 [(cellOf t2 0).v]
      let t3_197 : B Unit := do
        lxWindow_2 cur pp powers his out w 197 [(cellOf t2 0).v]
      let t3_198 : B Unit := do
        lxWindow_2 cur pp powers his out w 198 [(cellOf t2 0).v]
      let t3_199 : B Unit := do
        lxWindow_2 cur pp powers his out w 199 [(cellOf t2 0).v]
      let t3_200 : B Unit := do
        lxWindow_2 cur pp powers his out w 200 [(cellOf t2 0).v]
      let t3_201 : B Unit := do
        lxWindow_2 cur pp powers his out w 201 [(cellOf t2 0).v]
      let t3_202 : B Unit := do
        lxWindow_2 cur pp powers his out w 202 [(cellOf t2 0).v]
      let t3_203 : B Unit := do
        lxWindow_2 cur pp powers his out w 203 [(cellOf t2 0).v]
      let t3_204 : B Unit := do
        lxWindow_2 cur pp powers his out w 204 [(cellOf t2 0).v]
      let t3_205 : B Unit := do
        lxWindow_2 cur pp powers his out w 205 [(cellOf t2 0).v]
      let t3_206 : B Unit := do
        lxWindow_2 cur pp powers his out w 206 [(cellOf t2 0).v]
      let t3_207 : B Unit := do
        lxWindow_2 cur pp powers his out w 207 [(cellOf t2 0).v]
      let t3_208 : B Unit := do
        lxWindow_2 cur pp powers his out w 208 [(cellOf t2 0).v]
      let t3_209 : B Unit := do
        lxWindow_2 cur pp powers his out w 209 [(cellOf t2 0).v]
      let t3_210 : B Unit := do
        lxWindow_2 cur pp powers his out w 210 [(cellOf t2 0).v]
      let t3_211 : B Unit := do
        lxWindow_2 cur pp powers his out w 211 [(cellOf t2 0).v]
      let t3_212 : B Unit := do
        lxWindow_2 cur pp powers his out w 212 [(cellOf t2 0).v]
      let t3_213 : B Unit := do
        lxWindow_2 cur pp powers his out w 213 [(cellOf t2 0).v]
      let t3_214 : B Unit := do
        lxWindow_2 cur pp powers his out w 214 [(cellOf t2 0).v]
      let t3_215 : B Unit := do
        lxWindow_2 cur pp powers his out w 215 [(cellOf t2 0).v]
      let t3_216 : B Unit := do
        lxWindow_2 cur pp powers his out w 216 [(cellOf t2 0).v]
      let t3_217 : B Unit := do
        lxWindow_2 cur pp powers his out w 217 [(cellOf t2 0).v]
      let t3_218 : B Unit := do
        lxWindow_2 cur pp powers his out w 218 [(cellOf t2 0).v]
      let t3_219 : B Unit := do
        lxWindow_2 cur pp powers his out w 219 [(cellOf t2 0).v]
      let t3_220 : B Unit := do
        lxWindow_2 cur pp powers his out w 220 [(cellOf t2 0).v]
      let t3_221 : B Unit := do
        lxWindow_2 cur pp powers his out w 221 [(cellOf t2 0).v]
      let t3_222 : B Unit := do
        lxWindow_2 cur pp powers his out w 222 [(cellOf t2 0).v]
      let t3_223 : B Unit := do
        lxWindow_2 cur pp powers his out w 223 [(cellOf t2 0).v]
      let t3_224 : B Unit := do
        lxWindow_2 cur pp powers his out w 224 [(cellOf t2 0).v]
      let t3_225 : B Unit := do
        lxWindow_2 cur pp powers his out w 225 [(cellOf t2 0).v]
      let t3_226 : B Unit := do
        lxWindow_2 cur pp powers his out w 226 [(cellOf t2 0).v]
      let t3_227 : B Unit := do
        lxWindow_2 cur pp powers his out w 227 [(cellOf t2 0).v]
      let t3_228 : B Unit := do
        lxWindow_2 cur pp powers his out w 228 [(cellOf t2 0).v]
      let t3_229 : B Unit := do
        lxWindow_2 cur pp powers his out w 229 [(cellOf t2 0).v]
      let t3_230 : B Unit := do
        lxWindow_2 cur pp powers his out w 230 [(cellOf t2 0).v]
      let t3_231 : B Unit := do
        lxWindow_2 cur pp powers his out w 231 [(cellOf t2 0).v]
      let t3_232 : B Unit := do
        lxWindow_2 cur pp powers his out w 232 [(cellOf t2 0).v]
      let t3_233 : B Unit := do
        lxWindow_2 cur pp powers his out w 233 [(cellOf t2 0).v]
      let t3_234 : B Unit := do
        lxWindow_2 cur pp powers his out w 234 [(cellOf t2 0).v]
      let t3_235 : B Unit := do
        lxWindow_2 cur pp powers his out w 235 [(cellOf t2 0).v]
      let t3_236 : B Unit := do
        lxWindow_2 cur pp powers his out w 236 [(cellOf t2 0).v]
      let t3_237 : B Unit := do
        lxWindow_2 cur pp powers his out w 237 [(cellOf t2 0).v]
      let t3_238 : B Unit := do
        lxWindow_2 cur pp powers his out w 238 [(cellOf t2 0).v]
      let t3_239 : B Unit := do
        lxWindow_2 cur pp powers his out w 239 [(cellOf t2 0).v]
      let t3_240 : B Unit := do
        lxWindow_2 cur pp powers his out w 240 [(cellOf t2 0).v]
      let t3_241 : B Unit := do
        lxWindow_2 cur pp powers his out w 241 [(cellOf t2 0).v]
      let t3_242 : B Unit := do
        lxWindow_2 cur pp powers his out w 242 [(cellOf t2 0).v]
      let t3_243 : B Unit := do
        lxWindow_2 cur pp powers his out w 243 [(cellOf t2 0).v]
      let t3_244 : B Unit := do
        lxWindow_2 cur pp powers his out w 244 [(cellOf t2 0).v]
      let t3_245 : B Unit := do
        lxWindow_2 cur pp powers his out w 245 [(cellOf t2 0).v]
      let t3_246 : B Unit := do
        lxWindow_2 cur pp powers his out w 246 [(cellOf t2 0).v]
      let t3_247 : B Unit := do
        lxWindow_2 cur pp powers his out w 247 [(cellOf t2 0).v]
      let t3_248 : B Unit := do
        lxWindow_2 cur pp powers his out w 248 [(cellOf t2 0).v]
      let t3_249 : B Unit := do
        lxWindow_2 cur pp powers his out w 249 [(cellOf t2 0).v]
      let t3_250 : B Unit := do
        lxWindow_2 cur pp powers his out w 250 [(cellOf t2 0).v]
      let t3_251 : B Unit := do
        lxWindow_2 cur pp powers his out w 251 [(cellOf t2 0).v]
      let t3_252 : B Unit := do
        lxWindow_2 cur pp powers his out w 252 [(cellOf t2 0).v]
      let t3_253 : B Unit := do
        lxWindow_2 cur pp powers his out w 253 [(cellOf t2 0).v]
      let t3_254 : B Unit := do
        lxWindow_2 cur pp powers his out w 254 [(cellOf t2 0).v]
      let t3_255 : B Unit := do
        lxWindow_2 cur pp powers his out w 255 [(cellOf t2 0).v]
      let _ ← B.matchArms (cellOf windows w) [t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7, t3_8, t3_9, t3_10, t3_11, t3_12, t3_13, t3_14, t3_15, t3_16, t3_17, t3_18, t3_19, t3_20, t3_21, t3_22, t3_23, t3_24, t3_25, t3_26, t3_27, t3_28, t3_29, t3_30, t3_31, t3_32, t3_33, t3_34, t3_35, t3_36, t3_37, t3_38, t3_39, t3_40, t3_41, t3_42, t3_43, t3_44, t3_45, t3_46, t3_47, t3_48, t3_49, t3_50, t3_51, t3_52, t3_53, t3_54, t3_55, t3_56, t3_57, t3_58, t3_59, t3_60, t3_61, t3_62, t3_63, t3_64, t3_65, t3_66, t3_67, t3_68, t3_69, t3_70, t3_71, t3_72, t3_73, t3_74, t3_75, t3_76, t3_77, t3_78, t3_79, t3_80, t3_81, t3_82, t3_83, t3_84, t3_85, t3_86, t3_87, t3_88, t3_89, t3_90, t3_91, t3_92, t3_93, t3_94, t3_95, t3_96, t3_97, t3_98, t3_99, t3_100, t3_101, t3_102, t3_103, t3_104, t3_105, t3_106, t3_107, t3_108, t3_109, t3_110, t3_111, t3_112, t3_113, t3_114, t3_115, t3_116, t3_117, t3_118, t3_119, t3_120, t3_121, t3_122, t3_123, t3_124, t3_125, t3_126, t3_127, t3_128, t3_129, t3_130, t3_131, t3_132, t3_133, t3_134, t3_135, t3_136, t3_137, t3_138, t3_139, t3_140, t3_141, t3_142, t3_143, t3_144, t3_145, t3_146, t3_147, t3_148, t3_149, t3_150, t3_151, t3_152, t3_153, t3_154, t3_155, t3_156, t3_157, t3_158, t3_159, t3_160, t3_161, t3_162, t3_163, t3_164, t3_165, t3_166, t3_167, t3_168, t3_169, t3_170, t3_171, t3_172, t3_173, t3_174, t3_175, t3_176, t3_177, t3_178, t3_179, t3_180, t3_181, t3_182, t3_183, t3_184, t3_185, t3_186, t3_187, t3_188, t3_189, t3_190, t3_191, t3_192, t3_193, t3_194, t3_195, t3_196, t3_197, t3_198, t3_199, t3_200, t3_201, t3_202, t3_203, t3_204, t3_205, t3_206, t3_207, t3_208, t3_209, t3_210, t3_211, t3_212, t3_213, t3_214, t3_215, t3_216, t3_217, t3_218, t3_219, t3_220, t3_221, t3_222, t3_223, t3_224, t3_225, t3_226, t3_227, t3_228, t3_229, t3_230, t3_231, t3_232, t3_233, t3_234, t3_235, t3_236, t3_237, t3_238, t3_239, t3_240, t3_241, t3_242, t3_243, t3_244, t3_245, t3_246, t3_247, t3_248, t3_249, t3_250, t3_251, t3_252, t3_253, t3_254, t3_255]
      pure ()
    cur := cellOf out 0
  root := cur
  let layer_k := 1
  if layer_k = 0 then
    pure () -- no use of this definition takes this branch
  else
    idx ← B.add (cellOf his LX_LAYER_WINDOWS) (← B.const (lit LX_TOP))
  let rho ← hinted (B.witnessCell "randomizer")
  let digest ← B.stackBuf 1
  if layer_k = 0 then
    pure () -- no use of this definition takes this branch
  else
    B.keccak (a := (.words [.cell pp.v, .cell (← B.add idx (← B.const (lit TW_MSG))).v])) (b := (.words [.cell root.v, .cell rho.v])) (out := (.frame digest))
  let steps ← B.stackBuf CHAIN_STEPS
  for st_k in [0:CHAIN_STEPS] do
    B.addInto (cellOf steps st_k) idx (← B.const (lit (TW_CHAIN + (st_k * STEP_MUL))))
  let walks ← B.stackBuf 174
  let digitProduct := 1
  let encoded := 0
  let groups ← B.stackBuf LX_DIGIT_DISPATCHES
  B.witness "lx_digits" (.stack groups)
  for p_k in [0:LX_DIGIT_DISPATCHES - 1] do
    let _ ← B.rangeCheck (cellOf groups p_k) LX_DIGIT_GROUPS
    pure ()
  let _ ← B.rangeCheck (cellOf groups (LX_DIGIT_DISPATCHES - 1)) LX_TAIL_GROUPS
  let p_k := 0
  let t0 ← B.targets [none, none]
  B.chain
  Keccak.inlineArms
  let t1_0 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 0 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_1 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 1 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_2 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 2 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_3 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 3 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_4 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) LX_DIGIT_GROUP 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_5 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 5 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_6 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 6 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_7 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 7 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_8 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 8 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_9 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 9 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_10 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 10 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_11 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 11 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_12 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 12 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_13 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 13 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_14 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 14 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_15 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 15 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_16 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 16 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_17 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 17 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_18 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 18 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_19 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 19 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_20 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 20 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_21 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 21 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_22 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 22 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_23 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 23 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_24 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 24 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_25 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 25 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_26 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 26 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_27 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 27 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_28 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 28 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_29 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 29 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_30 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 30 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_31 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 31 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_32 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 32 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_33 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 33 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_34 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 34 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_35 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 35 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_36 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 36 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_37 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 37 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_38 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 38 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_39 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 39 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_40 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 40 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_41 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 41 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_42 : B Unit := do
    walkGroup_8 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 42 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_43 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 43 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_44 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 44 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_45 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 45 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_46 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 46 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_47 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 47 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_48 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 48 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_49 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 49 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_50 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 50 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_51 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 51 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_52 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 52 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_53 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 53 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_54 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 54 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_55 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 55 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_56 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 56 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_57 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 57 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_58 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 58 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_59 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 59 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_60 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 60 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_61 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 61 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_62 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 62 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_63 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 63 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_64 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 64 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_65 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 65 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_66 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 66 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_67 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 67 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_68 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 68 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_69 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 69 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_70 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 70 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_71 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 71 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_72 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 72 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_73 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 73 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_74 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 74 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_75 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 75 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_76 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 76 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_77 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 77 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_78 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 78 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_79 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 79 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_80 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 80 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_81 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 81 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_82 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 82 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_83 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 83 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_84 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 84 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_85 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 85 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_86 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 86 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_87 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 87 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_88 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 88 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_89 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 89 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_90 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 90 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_91 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 91 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_92 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 92 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_93 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 93 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_94 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 94 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_95 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 95 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_96 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 96 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_97 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 97 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_98 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 98 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_99 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 99 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_100 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 100 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_101 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 101 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_102 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 102 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_103 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 103 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_104 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 104 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_105 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 105 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_106 : B Unit := do
    walkGroup_8 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 106 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_107 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 107 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_108 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 108 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_109 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 109 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_110 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 110 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_111 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 111 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_112 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 112 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_113 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 113 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_114 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 114 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_115 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 115 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_116 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 116 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_117 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 117 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_118 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 118 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_119 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 119 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_120 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 120 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_121 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 121 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_122 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 122 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_123 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 123 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_124 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 124 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_125 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 125 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_126 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 126 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_127 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 127 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_128 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 128 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_129 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 129 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_130 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 130 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_131 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 131 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_132 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 132 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_133 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 133 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_134 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 134 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_135 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 135 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_136 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 136 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_137 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 137 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_138 : B Unit := do
    walkGroup_12 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 138 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_139 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 139 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_140 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 140 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_141 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 141 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_142 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 142 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_143 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 143 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_144 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 144 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_145 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 145 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_146 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 146 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_147 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 147 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_148 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 148 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_149 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 149 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_150 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 150 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_151 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 151 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_152 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 152 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_153 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 153 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_154 : B Unit := do
    walkGroup_12 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 154 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_155 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 155 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_156 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 156 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_157 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 157 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_158 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 158 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_159 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 159 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_160 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 160 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_161 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 161 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_162 : B Unit := do
    walkGroup_14 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 162 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_163 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 163 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_164 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 164 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_165 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 165 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_166 : B Unit := do
    walkGroup_14 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 166 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_167 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 167 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_168 : B Unit := do
    walkGroup_15 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 168 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_169 : B Unit := do
    walkGroup_15 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 169 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_170 : B Unit := do
    walkGroup_16 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 170 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_171 : B Unit := do
    walkGroup_15 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 171 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_172 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 172 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_173 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 173 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_174 : B Unit := do
    walkGroup_14 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 174 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_175 : B Unit := do
    walkGroup_13 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 175 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_176 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 176 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_177 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 177 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_178 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 178 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_179 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 179 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_180 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 180 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_181 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 181 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_182 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 182 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_183 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 183 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_184 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 184 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_185 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 185 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_186 : B Unit := do
    walkGroup_12 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 186 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_187 : B Unit := do
    walkGroup_11 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 187 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_188 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 188 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_189 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 189 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_190 : B Unit := do
    walkGroup_10 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 190 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_191 : B Unit := do
    walkGroup_9 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 191 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_192 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 192 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_193 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 193 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_194 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 194 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_195 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 195 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_196 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 196 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_197 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 197 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_198 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 198 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_199 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 199 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_200 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 200 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_201 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 201 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_202 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 202 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_203 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 203 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_204 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 204 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_205 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 205 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_206 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 206 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_207 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 207 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_208 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 208 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_209 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 209 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_210 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 210 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_211 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 211 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_212 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 212 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_213 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 213 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_214 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 214 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_215 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 215 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_216 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 216 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_217 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 217 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_218 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 218 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_219 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 219 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_220 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 220 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_221 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 221 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_222 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 222 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_223 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 223 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_224 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 224 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_225 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 225 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_226 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 226 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_227 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 227 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_228 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 228 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_229 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 229 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_230 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 230 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_231 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 231 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_232 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 232 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_233 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 233 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_234 : B Unit := do
    walkGroup_8 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 234 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_235 : B Unit := do
    walkGroup_7 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 235 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_236 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 236 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_237 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 237 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_238 : B Unit := do
    walkGroup_6 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 238 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_239 : B Unit := do
    walkGroup_5 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 239 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_240 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 240 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_241 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 241 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_242 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 242 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_243 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 243 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_244 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 244 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_245 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 245 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_246 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 246 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_247 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 247 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_248 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 248 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_249 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 249 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_250 : B Unit := do
    walkGroup_4 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 250 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_251 : B Unit := do
    walkGroup_3 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 251 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_252 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 252 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_253 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 253 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_254 : B Unit := do
    walkGroup_2 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 254 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_255 : B Unit := do
    walkGroup steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 255 1 powers (⟨Nat.log2 digitProduct⟩) (lit encoded) [(cellOf t0 0).v, (cellOf t0 1).v]
  let _ ← B.matchArms (cellOf groups p_k) [t1_0, t1_1, t1_2, t1_3, t1_4, t1_5, t1_6, t1_7, t1_8, t1_9, t1_10, t1_11, t1_12, t1_13, t1_14, t1_15, t1_16, t1_17, t1_18, t1_19, t1_20, t1_21, t1_22, t1_23, t1_24, t1_25, t1_26, t1_27, t1_28, t1_29, t1_30, t1_31, t1_32, t1_33, t1_34, t1_35, t1_36, t1_37, t1_38, t1_39, t1_40, t1_41, t1_42, t1_43, t1_44, t1_45, t1_46, t1_47, t1_48, t1_49, t1_50, t1_51, t1_52, t1_53, t1_54, t1_55, t1_56, t1_57, t1_58, t1_59, t1_60, t1_61, t1_62, t1_63, t1_64, t1_65, t1_66, t1_67, t1_68, t1_69, t1_70, t1_71, t1_72, t1_73, t1_74, t1_75, t1_76, t1_77, t1_78, t1_79, t1_80, t1_81, t1_82, t1_83, t1_84, t1_85, t1_86, t1_87, t1_88, t1_89, t1_90, t1_91, t1_92, t1_93, t1_94, t1_95, t1_96, t1_97, t1_98, t1_99, t1_100, t1_101, t1_102, t1_103, t1_104, t1_105, t1_106, t1_107, t1_108, t1_109, t1_110, t1_111, t1_112, t1_113, t1_114, t1_115, t1_116, t1_117, t1_118, t1_119, t1_120, t1_121, t1_122, t1_123, t1_124, t1_125, t1_126, t1_127, t1_128, t1_129, t1_130, t1_131, t1_132, t1_133, t1_134, t1_135, t1_136, t1_137, t1_138, t1_139, t1_140, t1_141, t1_142, t1_143, t1_144, t1_145, t1_146, t1_147, t1_148, t1_149, t1_150, t1_151, t1_152, t1_153, t1_154, t1_155, t1_156, t1_157, t1_158, t1_159, t1_160, t1_161, t1_162, t1_163, t1_164, t1_165, t1_166, t1_167, t1_168, t1_169, t1_170, t1_171, t1_172, t1_173, t1_174, t1_175, t1_176, t1_177, t1_178, t1_179, t1_180, t1_181, t1_182, t1_183, t1_184, t1_185, t1_186, t1_187, t1_188, t1_189, t1_190, t1_191, t1_192, t1_193, t1_194, t1_195, t1_196, t1_197, t1_198, t1_199, t1_200, t1_201, t1_202, t1_203, t1_204, t1_205, t1_206, t1_207, t1_208, t1_209, t1_210, t1_211, t1_212, t1_213, t1_214, t1_215, t1_216, t1_217, t1_218, t1_219, t1_220, t1_221, t1_222, t1_223, t1_224, t1_225, t1_226, t1_227, t1_228, t1_229, t1_230, t1_231, t1_232, t1_233, t1_234, t1_235, t1_236, t1_237, t1_238, t1_239, t1_240, t1_241, t1_242, t1_243, t1_244, t1_245, t1_246, t1_247, t1_248, t1_249, t1_250, t1_251, t1_252, t1_253, t1_254, t1_255]
  digitProduct_word := cellOf t0 0
  encoded_word := cellOf t0 1
  for p_k in [1:14] do
    let t0 ← B.targets [none, none]
    B.chain
    let t1_0 : B Unit := do
      walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 0 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_1 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 1 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_2 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 2 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_3 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 3 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_4 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) LX_DIGIT_GROUP 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_5 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 5 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_6 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 6 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_7 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 7 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_8 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 8 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_9 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 9 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_10 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 10 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_11 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 11 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_12 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 12 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_13 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 13 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_14 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 14 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_15 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 15 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_16 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 16 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_17 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 17 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_18 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 18 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_19 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 19 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_20 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 20 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_21 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 21 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_22 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 22 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_23 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 23 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_24 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 24 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_25 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 25 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_26 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 26 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_27 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 27 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_28 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 28 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_29 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 29 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_30 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 30 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_31 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 31 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_32 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 32 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_33 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 33 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_34 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 34 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_35 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 35 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_36 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 36 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_37 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 37 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_38 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 38 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_39 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 39 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_40 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 40 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_41 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 41 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_42 : B Unit := do
      walkGroup_25 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 42 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_43 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 43 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_44 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 44 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_45 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 45 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_46 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 46 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_47 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 47 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_48 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 48 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_49 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 49 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_50 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 50 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_51 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 51 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_52 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 52 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_53 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 53 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_54 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 54 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_55 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 55 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_56 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 56 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_57 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 57 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_58 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 58 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_59 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 59 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_60 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 60 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_61 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 61 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_62 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 62 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_63 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 63 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_64 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 64 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_65 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 65 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_66 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 66 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_67 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 67 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_68 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 68 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_69 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 69 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_70 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 70 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_71 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 71 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_72 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 72 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_73 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 73 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_74 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 74 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_75 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 75 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_76 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 76 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_77 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 77 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_78 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 78 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_79 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 79 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_80 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 80 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_81 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 81 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_82 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 82 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_83 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 83 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_84 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 84 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_85 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 85 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_86 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 86 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_87 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 87 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_88 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 88 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_89 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 89 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_90 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 90 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_91 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 91 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_92 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 92 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_93 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 93 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_94 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 94 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_95 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 95 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_96 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 96 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_97 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 97 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_98 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 98 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_99 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 99 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_100 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 100 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_101 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 101 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_102 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 102 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_103 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 103 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_104 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 104 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_105 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 105 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_106 : B Unit := do
      walkGroup_25 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 106 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_107 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 107 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_108 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 108 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_109 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 109 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_110 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 110 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_111 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 111 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_112 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 112 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_113 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 113 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_114 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 114 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_115 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 115 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_116 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 116 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_117 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 117 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_118 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 118 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_119 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 119 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_120 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 120 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_121 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 121 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_122 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 122 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_123 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 123 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_124 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 124 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_125 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 125 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_126 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 126 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_127 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 127 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_128 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 128 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_129 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 129 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_130 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 130 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_131 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 131 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_132 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 132 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_133 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 133 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_134 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 134 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_135 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 135 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_136 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 136 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_137 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 137 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_138 : B Unit := do
      walkGroup_29 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 138 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_139 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 139 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_140 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 140 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_141 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 141 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_142 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 142 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_143 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 143 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_144 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 144 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_145 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 145 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_146 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 146 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_147 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 147 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_148 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 148 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_149 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 149 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_150 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 150 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_151 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 151 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_152 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 152 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_153 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 153 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_154 : B Unit := do
      walkGroup_29 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 154 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_155 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 155 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_156 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 156 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_157 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 157 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_158 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 158 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_159 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 159 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_160 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 160 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_161 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 161 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_162 : B Unit := do
      walkGroup_31 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 162 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_163 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 163 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_164 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 164 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_165 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 165 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_166 : B Unit := do
      walkGroup_31 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 166 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_167 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 167 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_168 : B Unit := do
      walkGroup_32 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 168 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_169 : B Unit := do
      walkGroup_32 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 169 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_170 : B Unit := do
      walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 170 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_171 : B Unit := do
      walkGroup_32 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 171 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_172 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 172 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_173 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 173 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_174 : B Unit := do
      walkGroup_31 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 174 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_175 : B Unit := do
      walkGroup_30 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 175 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_176 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 176 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_177 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 177 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_178 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 178 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_179 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 179 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_180 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 180 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_181 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 181 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_182 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 182 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_183 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 183 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_184 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 184 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_185 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 185 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_186 : B Unit := do
      walkGroup_29 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 186 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_187 : B Unit := do
      walkGroup_28 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 187 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_188 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 188 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_189 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 189 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_190 : B Unit := do
      walkGroup_27 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 190 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_191 : B Unit := do
      walkGroup_26 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 191 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_192 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 192 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_193 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 193 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_194 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 194 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_195 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 195 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_196 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 196 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_197 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 197 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_198 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 198 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_199 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 199 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_200 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 200 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_201 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 201 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_202 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 202 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_203 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 203 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_204 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 204 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_205 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 205 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_206 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 206 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_207 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 207 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_208 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 208 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_209 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 209 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_210 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 210 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_211 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 211 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_212 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 212 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_213 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 213 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_214 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 214 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_215 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 215 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_216 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 216 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_217 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 217 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_218 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 218 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_219 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 219 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_220 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 220 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_221 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 221 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_222 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 222 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_223 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 223 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_224 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 224 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_225 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 225 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_226 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 226 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_227 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 227 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_228 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 228 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_229 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 229 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_230 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 230 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_231 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 231 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_232 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 232 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_233 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 233 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_234 : B Unit := do
      walkGroup_25 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 234 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_235 : B Unit := do
      walkGroup_24 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 235 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_236 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 236 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_237 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 237 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_238 : B Unit := do
      walkGroup_23 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 238 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_239 : B Unit := do
      walkGroup_22 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 239 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_240 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 240 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_241 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 241 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_242 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 242 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_243 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 243 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_244 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 244 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_245 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 245 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_246 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 246 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_247 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 247 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_248 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 248 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_249 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 249 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_250 : B Unit := do
      walkGroup_21 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 250 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_251 : B Unit := do
      walkGroup_20 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 251 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_252 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 252 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_253 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 253 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_254 : B Unit := do
      walkGroup_19 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 254 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let t1_255 : B Unit := do
      walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 255 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
    let _ ← B.matchArms (cellOf groups p_k) [t1_0, t1_1, t1_2, t1_3, t1_4, t1_5, t1_6, t1_7, t1_8, t1_9, t1_10, t1_11, t1_12, t1_13, t1_14, t1_15, t1_16, t1_17, t1_18, t1_19, t1_20, t1_21, t1_22, t1_23, t1_24, t1_25, t1_26, t1_27, t1_28, t1_29, t1_30, t1_31, t1_32, t1_33, t1_34, t1_35, t1_36, t1_37, t1_38, t1_39, t1_40, t1_41, t1_42, t1_43, t1_44, t1_45, t1_46, t1_47, t1_48, t1_49, t1_50, t1_51, t1_52, t1_53, t1_54, t1_55, t1_56, t1_57, t1_58, t1_59, t1_60, t1_61, t1_62, t1_63, t1_64, t1_65, t1_66, t1_67, t1_68, t1_69, t1_70, t1_71, t1_72, t1_73, t1_74, t1_75, t1_76, t1_77, t1_78, t1_79, t1_80, t1_81, t1_82, t1_83, t1_84, t1_85, t1_86, t1_87, t1_88, t1_89, t1_90, t1_91, t1_92, t1_93, t1_94, t1_95, t1_96, t1_97, t1_98, t1_99, t1_100, t1_101, t1_102, t1_103, t1_104, t1_105, t1_106, t1_107, t1_108, t1_109, t1_110, t1_111, t1_112, t1_113, t1_114, t1_115, t1_116, t1_117, t1_118, t1_119, t1_120, t1_121, t1_122, t1_123, t1_124, t1_125, t1_126, t1_127, t1_128, t1_129, t1_130, t1_131, t1_132, t1_133, t1_134, t1_135, t1_136, t1_137, t1_138, t1_139, t1_140, t1_141, t1_142, t1_143, t1_144, t1_145, t1_146, t1_147, t1_148, t1_149, t1_150, t1_151, t1_152, t1_153, t1_154, t1_155, t1_156, t1_157, t1_158, t1_159, t1_160, t1_161, t1_162, t1_163, t1_164, t1_165, t1_166, t1_167, t1_168, t1_169, t1_170, t1_171, t1_172, t1_173, t1_174, t1_175, t1_176, t1_177, t1_178, t1_179, t1_180, t1_181, t1_182, t1_183, t1_184, t1_185, t1_186, t1_187, t1_188, t1_189, t1_190, t1_191, t1_192, t1_193, t1_194, t1_195, t1_196, t1_197, t1_198, t1_199, t1_200, t1_201, t1_202, t1_203, t1_204, t1_205, t1_206, t1_207, t1_208, t1_209, t1_210, t1_211, t1_212, t1_213, t1_214, t1_215, t1_216, t1_217, t1_218, t1_219, t1_220, t1_221, t1_222, t1_223, t1_224, t1_225, t1_226, t1_227, t1_228, t1_229, t1_230, t1_231, t1_232, t1_233, t1_234, t1_235, t1_236, t1_237, t1_238, t1_239, t1_240, t1_241, t1_242, t1_243, t1_244, t1_245, t1_246, t1_247, t1_248, t1_249, t1_250, t1_251, t1_252, t1_253, t1_254, t1_255]
    digitProduct_word := cellOf t0 0
    encoded_word := cellOf t0 1
  let p_k := 14
  let t0 ← B.targets [none, none]
  let t1_0 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 0 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_1 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 1 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_2 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 2 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_3 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 3 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_4 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) LX_DIGIT_GROUP 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_5 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 5 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_6 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 6 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_7 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 7 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_8 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 8 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_9 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 9 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_10 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 10 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_11 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 11 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_12 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 12 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_13 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 13 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_14 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 14 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_15 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 15 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_16 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 16 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_17 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 17 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_18 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 18 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_19 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 19 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_20 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 20 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_21 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 21 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_22 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 22 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_23 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 23 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_24 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 24 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_25 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 25 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_26 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 26 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_27 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 27 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_28 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 28 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_29 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 29 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_30 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 30 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_31 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 31 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_32 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 32 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_33 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 33 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_34 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 34 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_35 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 35 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_36 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 36 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_37 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 37 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_38 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 38 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_39 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 39 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_40 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 40 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_41 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 41 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_42 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 42 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_43 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 43 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_44 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 44 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_45 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 45 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_46 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 46 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_47 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 47 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_48 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 48 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_49 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 49 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_50 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 50 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_51 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 51 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_52 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 52 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_53 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 53 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_54 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 54 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_55 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 55 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_56 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 56 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_57 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 57 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_58 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 58 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_59 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 59 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_60 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 60 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_61 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 61 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_62 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 62 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_63 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 63 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_64 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 64 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_65 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 65 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_66 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 66 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_67 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 67 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_68 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 68 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_69 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 69 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_70 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 70 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_71 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 71 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_72 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 72 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_73 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 73 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_74 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 74 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_75 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 75 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_76 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 76 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_77 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 77 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_78 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 78 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_79 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 79 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_80 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 80 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_81 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 81 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_82 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 82 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_83 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 83 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_84 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 84 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_85 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 85 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_86 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 86 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_87 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 87 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_88 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 88 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_89 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 89 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_90 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 90 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_91 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 91 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_92 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 92 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_93 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 93 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_94 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 94 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_95 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 95 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_96 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 96 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_97 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 97 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_98 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 98 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_99 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 99 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_100 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 100 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_101 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 101 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_102 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 102 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_103 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 103 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_104 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 104 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_105 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 105 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_106 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 106 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_107 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 107 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_108 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 108 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_109 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 109 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_110 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 110 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_111 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 111 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_112 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 112 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_113 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 113 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_114 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 114 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_115 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 115 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_116 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 116 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_117 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 117 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_118 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 118 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_119 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 119 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_120 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 120 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_121 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 121 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_122 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 122 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_123 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 123 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_124 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 124 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_125 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 125 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_126 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 126 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_127 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 127 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_128 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 128 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_129 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 129 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_130 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 130 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_131 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 131 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_132 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 132 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_133 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 133 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_134 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 134 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_135 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 135 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_136 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 136 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_137 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 137 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_138 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 138 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_139 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 139 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_140 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 140 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_141 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 141 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_142 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 142 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_143 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 143 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_144 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 144 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_145 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 145 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_146 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 146 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_147 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 147 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_148 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 148 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_149 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 149 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_150 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 150 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_151 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 151 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_152 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 152 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_153 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 153 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_154 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 154 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_155 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 155 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_156 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 156 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_157 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 157 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_158 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 158 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_159 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 159 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_160 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 160 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_161 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 161 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_162 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 162 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_163 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 163 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_164 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 164 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_165 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 165 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_166 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 166 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_167 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 167 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_168 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 168 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_169 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 169 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_170 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 170 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_171 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 171 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_172 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 172 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_173 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 173 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_174 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 174 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_175 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 175 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_176 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 176 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_177 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 177 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_178 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 178 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_179 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 179 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_180 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 180 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_181 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 181 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_182 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 182 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_183 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 183 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_184 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 184 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_185 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 185 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_186 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 186 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_187 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 187 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_188 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 188 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_189 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 189 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_190 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 190 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_191 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 191 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_192 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 192 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_193 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 193 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_194 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 194 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_195 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 195 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_196 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 196 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_197 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 197 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_198 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 198 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_199 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 199 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_200 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 200 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_201 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 201 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_202 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 202 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_203 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 203 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_204 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 204 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_205 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 205 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_206 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 206 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_207 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 207 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_208 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 208 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_209 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 209 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_210 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 210 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_211 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 211 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_212 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 212 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_213 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 213 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_214 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 214 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_215 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 215 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_216 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 216 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_217 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 217 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_218 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 218 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_219 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 219 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_220 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 220 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_221 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 221 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_222 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 222 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_223 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 223 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_224 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 224 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_225 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 225 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_226 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 226 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_227 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 227 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_228 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 228 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_229 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 229 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_230 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 230 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_231 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 231 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_232 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 232 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_233 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 233 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_234 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 234 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_235 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 235 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_236 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 236 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_237 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 237 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_238 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 238 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_239 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 239 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_240 : B Unit := do
    walkGroup_17 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 240 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_241 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 241 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_242 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 242 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_243 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 243 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_244 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 244 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_245 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 245 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_246 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 246 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_247 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 247 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_248 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 248 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_249 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 249 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_250 : B Unit := do
    walkGroup_33 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 250 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_251 : B Unit := do
    walkGroup_35 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 251 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_252 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 252 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_253 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 253 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_254 : B Unit := do
    walkGroup_34 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 254 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let t1_255 : B Unit := do
    walkGroup_18 steps pp walks tags (LX_DIGIT_GROUP * p_k) (arrInt LX_GROUP_SIZES p_k) 255 1 powers digitProduct_word encoded_word [(cellOf t0 0).v, (cellOf t0 1).v]
  let _ ← B.matchArms (cellOf groups p_k) [t1_0, t1_1, t1_2, t1_3, t1_4, t1_5, t1_6, t1_7, t1_8, t1_9, t1_10, t1_11, t1_12, t1_13, t1_14, t1_15, t1_16, t1_17, t1_18, t1_19, t1_20, t1_21, t1_22, t1_23, t1_24, t1_25, t1_26, t1_27, t1_28, t1_29, t1_30, t1_31, t1_32, t1_33, t1_34, t1_35, t1_36, t1_37, t1_38, t1_39, t1_40, t1_41, t1_42, t1_43, t1_44, t1_45, t1_46, t1_47, t1_48, t1_49, t1_50, t1_51, t1_52, t1_53, t1_54, t1_55, t1_56, t1_57, t1_58, t1_59, t1_60, t1_61, t1_62, t1_63, t1_64, t1_65, t1_66, t1_67, t1_68, t1_69, t1_70, t1_71, t1_72, t1_73, t1_74, t1_75, t1_76, t1_77, t1_78, t1_79, t1_80, t1_81, t1_82, t1_83, t1_84, t1_85, t1_86, t1_87, t1_88, t1_89, t1_90, t1_91, t1_92, t1_93, t1_94, t1_95, t1_96, t1_97, t1_98, t1_99, t1_100, t1_101, t1_102, t1_103, t1_104, t1_105, t1_106, t1_107, t1_108, t1_109, t1_110, t1_111, t1_112, t1_113, t1_114, t1_115, t1_116, t1_117, t1_118, t1_119, t1_120, t1_121, t1_122, t1_123, t1_124, t1_125, t1_126, t1_127, t1_128, t1_129, t1_130, t1_131, t1_132, t1_133, t1_134, t1_135, t1_136, t1_137, t1_138, t1_139, t1_140, t1_141, t1_142, t1_143, t1_144, t1_145, t1_146, t1_147, t1_148, t1_149, t1_150, t1_151, t1_152, t1_153, t1_154, t1_155, t1_156, t1_157, t1_158, t1_159, t1_160, t1_161, t1_162, t1_163, t1_164, t1_165, t1_166, t1_167, t1_168, t1_169, t1_170, t1_171, t1_172, t1_173, t1_174, t1_175, t1_176, t1_177, t1_178, t1_179, t1_180, t1_181, t1_182, t1_183, t1_184, t1_185, t1_186, t1_187, t1_188, t1_189, t1_190, t1_191, t1_192, t1_193, t1_194, t1_195, t1_196, t1_197, t1_198, t1_199, t1_200, t1_201, t1_202, t1_203, t1_204, t1_205, t1_206, t1_207, t1_208, t1_209, t1_210, t1_211, t1_212, t1_213, t1_214, t1_215, t1_216, t1_217, t1_218, t1_219, t1_220, t1_221, t1_222, t1_223, t1_224, t1_225, t1_226, t1_227, t1_228, t1_229, t1_230, t1_231, t1_232, t1_233, t1_234, t1_235, t1_236, t1_237, t1_238, t1_239, t1_240, t1_241, t1_242, t1_243, t1_244, t1_245, t1_246, t1_247, t1_248, t1_249, t1_250, t1_251, t1_252, t1_253, t1_254, t1_255]
  digitProduct_word := cellOf t0 0
  encoded_word := cellOf t0 1
  B.copy (cellOf digest 0) encoded_word
  B.assertEq digitProduct_word (← B.const (gpowE LX_TARGET_SUM))
  let leaf ← B.stackBuf 1
  wotsLeaf pp (← B.add idx (← B.const (lit TW_LEAF))) walks LX_V leaf
  cur := cellOf leaf 0
  for v_k in [0:LX_LAYER_WINDOWS] do
    w := (layer_k * LX_LAYER_WINDOWS) + v_k
    out ← B.stackBuf 1
    let _ ← B.rangeCheck (cellOf windows w) LX_WINDOW_ARMS
    if (w + 1) = LX_WINDOWS then
      let t2 ← B.targets [some (cellOf his w).v]
      Keccak.inlineArms
      let _ ← B.matchArms (cellOf windows w) ((List.range LX_WINDOW_ARMS).map fun arm => do
        lxTopWindow cur pp powers his out w arm [(cellOf t2 0).v])
      pure ()
    else
      let t2 ← B.targets [some (cellOf his w).v]
      Keccak.inlineArms
      let t3_0 : B Unit := do
        lxWindow cur pp powers his out w 0 [(cellOf t2 0).v]
      let t3_1 : B Unit := do
        lxWindow_2 cur pp powers his out w 1 [(cellOf t2 0).v]
      let t3_2 : B Unit := do
        lxWindow_2 cur pp powers his out w 2 [(cellOf t2 0).v]
      let t3_3 : B Unit := do
        lxWindow_2 cur pp powers his out w 3 [(cellOf t2 0).v]
      let t3_4 : B Unit := do
        lxWindow_2 cur pp powers his out w 4 [(cellOf t2 0).v]
      let t3_5 : B Unit := do
        lxWindow_2 cur pp powers his out w 5 [(cellOf t2 0).v]
      let t3_6 : B Unit := do
        lxWindow_2 cur pp powers his out w 6 [(cellOf t2 0).v]
      let t3_7 : B Unit := do
        lxWindow_2 cur pp powers his out w 7 [(cellOf t2 0).v]
      let t3_8 : B Unit := do
        lxWindow_2 cur pp powers his out w 8 [(cellOf t2 0).v]
      let t3_9 : B Unit := do
        lxWindow_2 cur pp powers his out w 9 [(cellOf t2 0).v]
      let t3_10 : B Unit := do
        lxWindow_2 cur pp powers his out w 10 [(cellOf t2 0).v]
      let t3_11 : B Unit := do
        lxWindow_2 cur pp powers his out w 11 [(cellOf t2 0).v]
      let t3_12 : B Unit := do
        lxWindow_2 cur pp powers his out w 12 [(cellOf t2 0).v]
      let t3_13 : B Unit := do
        lxWindow_2 cur pp powers his out w 13 [(cellOf t2 0).v]
      let t3_14 : B Unit := do
        lxWindow_2 cur pp powers his out w 14 [(cellOf t2 0).v]
      let t3_15 : B Unit := do
        lxWindow_2 cur pp powers his out w 15 [(cellOf t2 0).v]
      let t3_16 : B Unit := do
        lxWindow_2 cur pp powers his out w 16 [(cellOf t2 0).v]
      let t3_17 : B Unit := do
        lxWindow_2 cur pp powers his out w 17 [(cellOf t2 0).v]
      let t3_18 : B Unit := do
        lxWindow_2 cur pp powers his out w 18 [(cellOf t2 0).v]
      let t3_19 : B Unit := do
        lxWindow_2 cur pp powers his out w 19 [(cellOf t2 0).v]
      let t3_20 : B Unit := do
        lxWindow_2 cur pp powers his out w 20 [(cellOf t2 0).v]
      let t3_21 : B Unit := do
        lxWindow_2 cur pp powers his out w 21 [(cellOf t2 0).v]
      let t3_22 : B Unit := do
        lxWindow_2 cur pp powers his out w 22 [(cellOf t2 0).v]
      let t3_23 : B Unit := do
        lxWindow_2 cur pp powers his out w 23 [(cellOf t2 0).v]
      let t3_24 : B Unit := do
        lxWindow_2 cur pp powers his out w 24 [(cellOf t2 0).v]
      let t3_25 : B Unit := do
        lxWindow_2 cur pp powers his out w 25 [(cellOf t2 0).v]
      let t3_26 : B Unit := do
        lxWindow_2 cur pp powers his out w 26 [(cellOf t2 0).v]
      let t3_27 : B Unit := do
        lxWindow_2 cur pp powers his out w 27 [(cellOf t2 0).v]
      let t3_28 : B Unit := do
        lxWindow_2 cur pp powers his out w 28 [(cellOf t2 0).v]
      let t3_29 : B Unit := do
        lxWindow_2 cur pp powers his out w 29 [(cellOf t2 0).v]
      let t3_30 : B Unit := do
        lxWindow_2 cur pp powers his out w 30 [(cellOf t2 0).v]
      let t3_31 : B Unit := do
        lxWindow_2 cur pp powers his out w 31 [(cellOf t2 0).v]
      let t3_32 : B Unit := do
        lxWindow_2 cur pp powers his out w 32 [(cellOf t2 0).v]
      let t3_33 : B Unit := do
        lxWindow_2 cur pp powers his out w 33 [(cellOf t2 0).v]
      let t3_34 : B Unit := do
        lxWindow_2 cur pp powers his out w 34 [(cellOf t2 0).v]
      let t3_35 : B Unit := do
        lxWindow_2 cur pp powers his out w 35 [(cellOf t2 0).v]
      let t3_36 : B Unit := do
        lxWindow_2 cur pp powers his out w 36 [(cellOf t2 0).v]
      let t3_37 : B Unit := do
        lxWindow_2 cur pp powers his out w 37 [(cellOf t2 0).v]
      let t3_38 : B Unit := do
        lxWindow_2 cur pp powers his out w 38 [(cellOf t2 0).v]
      let t3_39 : B Unit := do
        lxWindow_2 cur pp powers his out w 39 [(cellOf t2 0).v]
      let t3_40 : B Unit := do
        lxWindow_2 cur pp powers his out w 40 [(cellOf t2 0).v]
      let t3_41 : B Unit := do
        lxWindow_2 cur pp powers his out w 41 [(cellOf t2 0).v]
      let t3_42 : B Unit := do
        lxWindow_2 cur pp powers his out w 42 [(cellOf t2 0).v]
      let t3_43 : B Unit := do
        lxWindow_2 cur pp powers his out w 43 [(cellOf t2 0).v]
      let t3_44 : B Unit := do
        lxWindow_2 cur pp powers his out w 44 [(cellOf t2 0).v]
      let t3_45 : B Unit := do
        lxWindow_2 cur pp powers his out w 45 [(cellOf t2 0).v]
      let t3_46 : B Unit := do
        lxWindow_2 cur pp powers his out w 46 [(cellOf t2 0).v]
      let t3_47 : B Unit := do
        lxWindow_2 cur pp powers his out w 47 [(cellOf t2 0).v]
      let t3_48 : B Unit := do
        lxWindow_2 cur pp powers his out w 48 [(cellOf t2 0).v]
      let t3_49 : B Unit := do
        lxWindow_2 cur pp powers his out w 49 [(cellOf t2 0).v]
      let t3_50 : B Unit := do
        lxWindow_2 cur pp powers his out w 50 [(cellOf t2 0).v]
      let t3_51 : B Unit := do
        lxWindow_2 cur pp powers his out w 51 [(cellOf t2 0).v]
      let t3_52 : B Unit := do
        lxWindow_2 cur pp powers his out w 52 [(cellOf t2 0).v]
      let t3_53 : B Unit := do
        lxWindow_2 cur pp powers his out w 53 [(cellOf t2 0).v]
      let t3_54 : B Unit := do
        lxWindow_2 cur pp powers his out w 54 [(cellOf t2 0).v]
      let t3_55 : B Unit := do
        lxWindow_2 cur pp powers his out w 55 [(cellOf t2 0).v]
      let t3_56 : B Unit := do
        lxWindow_2 cur pp powers his out w 56 [(cellOf t2 0).v]
      let t3_57 : B Unit := do
        lxWindow_2 cur pp powers his out w 57 [(cellOf t2 0).v]
      let t3_58 : B Unit := do
        lxWindow_2 cur pp powers his out w 58 [(cellOf t2 0).v]
      let t3_59 : B Unit := do
        lxWindow_2 cur pp powers his out w 59 [(cellOf t2 0).v]
      let t3_60 : B Unit := do
        lxWindow_2 cur pp powers his out w 60 [(cellOf t2 0).v]
      let t3_61 : B Unit := do
        lxWindow_2 cur pp powers his out w 61 [(cellOf t2 0).v]
      let t3_62 : B Unit := do
        lxWindow_2 cur pp powers his out w 62 [(cellOf t2 0).v]
      let t3_63 : B Unit := do
        lxWindow_2 cur pp powers his out w 63 [(cellOf t2 0).v]
      let t3_64 : B Unit := do
        lxWindow_2 cur pp powers his out w 64 [(cellOf t2 0).v]
      let t3_65 : B Unit := do
        lxWindow_2 cur pp powers his out w 65 [(cellOf t2 0).v]
      let t3_66 : B Unit := do
        lxWindow_2 cur pp powers his out w 66 [(cellOf t2 0).v]
      let t3_67 : B Unit := do
        lxWindow_2 cur pp powers his out w 67 [(cellOf t2 0).v]
      let t3_68 : B Unit := do
        lxWindow_2 cur pp powers his out w 68 [(cellOf t2 0).v]
      let t3_69 : B Unit := do
        lxWindow_2 cur pp powers his out w 69 [(cellOf t2 0).v]
      let t3_70 : B Unit := do
        lxWindow_2 cur pp powers his out w 70 [(cellOf t2 0).v]
      let t3_71 : B Unit := do
        lxWindow_2 cur pp powers his out w 71 [(cellOf t2 0).v]
      let t3_72 : B Unit := do
        lxWindow_2 cur pp powers his out w 72 [(cellOf t2 0).v]
      let t3_73 : B Unit := do
        lxWindow_2 cur pp powers his out w 73 [(cellOf t2 0).v]
      let t3_74 : B Unit := do
        lxWindow_2 cur pp powers his out w 74 [(cellOf t2 0).v]
      let t3_75 : B Unit := do
        lxWindow_2 cur pp powers his out w 75 [(cellOf t2 0).v]
      let t3_76 : B Unit := do
        lxWindow_2 cur pp powers his out w 76 [(cellOf t2 0).v]
      let t3_77 : B Unit := do
        lxWindow_2 cur pp powers his out w 77 [(cellOf t2 0).v]
      let t3_78 : B Unit := do
        lxWindow_2 cur pp powers his out w 78 [(cellOf t2 0).v]
      let t3_79 : B Unit := do
        lxWindow_2 cur pp powers his out w 79 [(cellOf t2 0).v]
      let t3_80 : B Unit := do
        lxWindow_2 cur pp powers his out w 80 [(cellOf t2 0).v]
      let t3_81 : B Unit := do
        lxWindow_2 cur pp powers his out w 81 [(cellOf t2 0).v]
      let t3_82 : B Unit := do
        lxWindow_2 cur pp powers his out w 82 [(cellOf t2 0).v]
      let t3_83 : B Unit := do
        lxWindow_2 cur pp powers his out w 83 [(cellOf t2 0).v]
      let t3_84 : B Unit := do
        lxWindow_2 cur pp powers his out w 84 [(cellOf t2 0).v]
      let t3_85 : B Unit := do
        lxWindow_2 cur pp powers his out w 85 [(cellOf t2 0).v]
      let t3_86 : B Unit := do
        lxWindow_2 cur pp powers his out w 86 [(cellOf t2 0).v]
      let t3_87 : B Unit := do
        lxWindow_2 cur pp powers his out w 87 [(cellOf t2 0).v]
      let t3_88 : B Unit := do
        lxWindow_2 cur pp powers his out w 88 [(cellOf t2 0).v]
      let t3_89 : B Unit := do
        lxWindow_2 cur pp powers his out w 89 [(cellOf t2 0).v]
      let t3_90 : B Unit := do
        lxWindow_2 cur pp powers his out w 90 [(cellOf t2 0).v]
      let t3_91 : B Unit := do
        lxWindow_2 cur pp powers his out w 91 [(cellOf t2 0).v]
      let t3_92 : B Unit := do
        lxWindow_2 cur pp powers his out w 92 [(cellOf t2 0).v]
      let t3_93 : B Unit := do
        lxWindow_2 cur pp powers his out w 93 [(cellOf t2 0).v]
      let t3_94 : B Unit := do
        lxWindow_2 cur pp powers his out w 94 [(cellOf t2 0).v]
      let t3_95 : B Unit := do
        lxWindow_2 cur pp powers his out w 95 [(cellOf t2 0).v]
      let t3_96 : B Unit := do
        lxWindow_2 cur pp powers his out w 96 [(cellOf t2 0).v]
      let t3_97 : B Unit := do
        lxWindow_2 cur pp powers his out w 97 [(cellOf t2 0).v]
      let t3_98 : B Unit := do
        lxWindow_2 cur pp powers his out w 98 [(cellOf t2 0).v]
      let t3_99 : B Unit := do
        lxWindow_2 cur pp powers his out w 99 [(cellOf t2 0).v]
      let t3_100 : B Unit := do
        lxWindow_2 cur pp powers his out w 100 [(cellOf t2 0).v]
      let t3_101 : B Unit := do
        lxWindow_2 cur pp powers his out w 101 [(cellOf t2 0).v]
      let t3_102 : B Unit := do
        lxWindow_2 cur pp powers his out w 102 [(cellOf t2 0).v]
      let t3_103 : B Unit := do
        lxWindow_2 cur pp powers his out w 103 [(cellOf t2 0).v]
      let t3_104 : B Unit := do
        lxWindow_2 cur pp powers his out w 104 [(cellOf t2 0).v]
      let t3_105 : B Unit := do
        lxWindow_2 cur pp powers his out w 105 [(cellOf t2 0).v]
      let t3_106 : B Unit := do
        lxWindow_2 cur pp powers his out w 106 [(cellOf t2 0).v]
      let t3_107 : B Unit := do
        lxWindow_2 cur pp powers his out w 107 [(cellOf t2 0).v]
      let t3_108 : B Unit := do
        lxWindow_2 cur pp powers his out w 108 [(cellOf t2 0).v]
      let t3_109 : B Unit := do
        lxWindow_2 cur pp powers his out w 109 [(cellOf t2 0).v]
      let t3_110 : B Unit := do
        lxWindow_2 cur pp powers his out w 110 [(cellOf t2 0).v]
      let t3_111 : B Unit := do
        lxWindow_2 cur pp powers his out w 111 [(cellOf t2 0).v]
      let t3_112 : B Unit := do
        lxWindow_2 cur pp powers his out w 112 [(cellOf t2 0).v]
      let t3_113 : B Unit := do
        lxWindow_2 cur pp powers his out w 113 [(cellOf t2 0).v]
      let t3_114 : B Unit := do
        lxWindow_2 cur pp powers his out w 114 [(cellOf t2 0).v]
      let t3_115 : B Unit := do
        lxWindow_2 cur pp powers his out w 115 [(cellOf t2 0).v]
      let t3_116 : B Unit := do
        lxWindow_2 cur pp powers his out w 116 [(cellOf t2 0).v]
      let t3_117 : B Unit := do
        lxWindow_2 cur pp powers his out w 117 [(cellOf t2 0).v]
      let t3_118 : B Unit := do
        lxWindow_2 cur pp powers his out w 118 [(cellOf t2 0).v]
      let t3_119 : B Unit := do
        lxWindow_2 cur pp powers his out w 119 [(cellOf t2 0).v]
      let t3_120 : B Unit := do
        lxWindow_2 cur pp powers his out w 120 [(cellOf t2 0).v]
      let t3_121 : B Unit := do
        lxWindow_2 cur pp powers his out w 121 [(cellOf t2 0).v]
      let t3_122 : B Unit := do
        lxWindow_2 cur pp powers his out w 122 [(cellOf t2 0).v]
      let t3_123 : B Unit := do
        lxWindow_2 cur pp powers his out w 123 [(cellOf t2 0).v]
      let t3_124 : B Unit := do
        lxWindow_2 cur pp powers his out w 124 [(cellOf t2 0).v]
      let t3_125 : B Unit := do
        lxWindow_2 cur pp powers his out w 125 [(cellOf t2 0).v]
      let t3_126 : B Unit := do
        lxWindow_2 cur pp powers his out w 126 [(cellOf t2 0).v]
      let t3_127 : B Unit := do
        lxWindow_2 cur pp powers his out w 127 [(cellOf t2 0).v]
      let t3_128 : B Unit := do
        lxWindow_2 cur pp powers his out w 128 [(cellOf t2 0).v]
      let t3_129 : B Unit := do
        lxWindow_2 cur pp powers his out w 129 [(cellOf t2 0).v]
      let t3_130 : B Unit := do
        lxWindow_2 cur pp powers his out w 130 [(cellOf t2 0).v]
      let t3_131 : B Unit := do
        lxWindow_2 cur pp powers his out w 131 [(cellOf t2 0).v]
      let t3_132 : B Unit := do
        lxWindow_2 cur pp powers his out w 132 [(cellOf t2 0).v]
      let t3_133 : B Unit := do
        lxWindow_2 cur pp powers his out w 133 [(cellOf t2 0).v]
      let t3_134 : B Unit := do
        lxWindow_2 cur pp powers his out w 134 [(cellOf t2 0).v]
      let t3_135 : B Unit := do
        lxWindow_2 cur pp powers his out w 135 [(cellOf t2 0).v]
      let t3_136 : B Unit := do
        lxWindow_2 cur pp powers his out w 136 [(cellOf t2 0).v]
      let t3_137 : B Unit := do
        lxWindow_2 cur pp powers his out w 137 [(cellOf t2 0).v]
      let t3_138 : B Unit := do
        lxWindow_2 cur pp powers his out w 138 [(cellOf t2 0).v]
      let t3_139 : B Unit := do
        lxWindow_2 cur pp powers his out w 139 [(cellOf t2 0).v]
      let t3_140 : B Unit := do
        lxWindow_2 cur pp powers his out w 140 [(cellOf t2 0).v]
      let t3_141 : B Unit := do
        lxWindow_2 cur pp powers his out w 141 [(cellOf t2 0).v]
      let t3_142 : B Unit := do
        lxWindow_2 cur pp powers his out w 142 [(cellOf t2 0).v]
      let t3_143 : B Unit := do
        lxWindow_2 cur pp powers his out w 143 [(cellOf t2 0).v]
      let t3_144 : B Unit := do
        lxWindow_2 cur pp powers his out w 144 [(cellOf t2 0).v]
      let t3_145 : B Unit := do
        lxWindow_2 cur pp powers his out w 145 [(cellOf t2 0).v]
      let t3_146 : B Unit := do
        lxWindow_2 cur pp powers his out w 146 [(cellOf t2 0).v]
      let t3_147 : B Unit := do
        lxWindow_2 cur pp powers his out w 147 [(cellOf t2 0).v]
      let t3_148 : B Unit := do
        lxWindow_2 cur pp powers his out w 148 [(cellOf t2 0).v]
      let t3_149 : B Unit := do
        lxWindow_2 cur pp powers his out w 149 [(cellOf t2 0).v]
      let t3_150 : B Unit := do
        lxWindow_2 cur pp powers his out w 150 [(cellOf t2 0).v]
      let t3_151 : B Unit := do
        lxWindow_2 cur pp powers his out w 151 [(cellOf t2 0).v]
      let t3_152 : B Unit := do
        lxWindow_2 cur pp powers his out w 152 [(cellOf t2 0).v]
      let t3_153 : B Unit := do
        lxWindow_2 cur pp powers his out w 153 [(cellOf t2 0).v]
      let t3_154 : B Unit := do
        lxWindow_2 cur pp powers his out w 154 [(cellOf t2 0).v]
      let t3_155 : B Unit := do
        lxWindow_2 cur pp powers his out w 155 [(cellOf t2 0).v]
      let t3_156 : B Unit := do
        lxWindow_2 cur pp powers his out w 156 [(cellOf t2 0).v]
      let t3_157 : B Unit := do
        lxWindow_2 cur pp powers his out w 157 [(cellOf t2 0).v]
      let t3_158 : B Unit := do
        lxWindow_2 cur pp powers his out w 158 [(cellOf t2 0).v]
      let t3_159 : B Unit := do
        lxWindow_2 cur pp powers his out w 159 [(cellOf t2 0).v]
      let t3_160 : B Unit := do
        lxWindow_2 cur pp powers his out w 160 [(cellOf t2 0).v]
      let t3_161 : B Unit := do
        lxWindow_2 cur pp powers his out w 161 [(cellOf t2 0).v]
      let t3_162 : B Unit := do
        lxWindow_2 cur pp powers his out w 162 [(cellOf t2 0).v]
      let t3_163 : B Unit := do
        lxWindow_2 cur pp powers his out w 163 [(cellOf t2 0).v]
      let t3_164 : B Unit := do
        lxWindow_2 cur pp powers his out w 164 [(cellOf t2 0).v]
      let t3_165 : B Unit := do
        lxWindow_2 cur pp powers his out w 165 [(cellOf t2 0).v]
      let t3_166 : B Unit := do
        lxWindow_2 cur pp powers his out w 166 [(cellOf t2 0).v]
      let t3_167 : B Unit := do
        lxWindow_2 cur pp powers his out w 167 [(cellOf t2 0).v]
      let t3_168 : B Unit := do
        lxWindow_2 cur pp powers his out w 168 [(cellOf t2 0).v]
      let t3_169 : B Unit := do
        lxWindow_2 cur pp powers his out w 169 [(cellOf t2 0).v]
      let t3_170 : B Unit := do
        lxWindow_2 cur pp powers his out w 170 [(cellOf t2 0).v]
      let t3_171 : B Unit := do
        lxWindow_2 cur pp powers his out w 171 [(cellOf t2 0).v]
      let t3_172 : B Unit := do
        lxWindow_2 cur pp powers his out w 172 [(cellOf t2 0).v]
      let t3_173 : B Unit := do
        lxWindow_2 cur pp powers his out w 173 [(cellOf t2 0).v]
      let t3_174 : B Unit := do
        lxWindow_2 cur pp powers his out w 174 [(cellOf t2 0).v]
      let t3_175 : B Unit := do
        lxWindow_2 cur pp powers his out w 175 [(cellOf t2 0).v]
      let t3_176 : B Unit := do
        lxWindow_2 cur pp powers his out w 176 [(cellOf t2 0).v]
      let t3_177 : B Unit := do
        lxWindow_2 cur pp powers his out w 177 [(cellOf t2 0).v]
      let t3_178 : B Unit := do
        lxWindow_2 cur pp powers his out w 178 [(cellOf t2 0).v]
      let t3_179 : B Unit := do
        lxWindow_2 cur pp powers his out w 179 [(cellOf t2 0).v]
      let t3_180 : B Unit := do
        lxWindow_2 cur pp powers his out w 180 [(cellOf t2 0).v]
      let t3_181 : B Unit := do
        lxWindow_2 cur pp powers his out w 181 [(cellOf t2 0).v]
      let t3_182 : B Unit := do
        lxWindow_2 cur pp powers his out w 182 [(cellOf t2 0).v]
      let t3_183 : B Unit := do
        lxWindow_2 cur pp powers his out w 183 [(cellOf t2 0).v]
      let t3_184 : B Unit := do
        lxWindow_2 cur pp powers his out w 184 [(cellOf t2 0).v]
      let t3_185 : B Unit := do
        lxWindow_2 cur pp powers his out w 185 [(cellOf t2 0).v]
      let t3_186 : B Unit := do
        lxWindow_2 cur pp powers his out w 186 [(cellOf t2 0).v]
      let t3_187 : B Unit := do
        lxWindow_2 cur pp powers his out w 187 [(cellOf t2 0).v]
      let t3_188 : B Unit := do
        lxWindow_2 cur pp powers his out w 188 [(cellOf t2 0).v]
      let t3_189 : B Unit := do
        lxWindow_2 cur pp powers his out w 189 [(cellOf t2 0).v]
      let t3_190 : B Unit := do
        lxWindow_2 cur pp powers his out w 190 [(cellOf t2 0).v]
      let t3_191 : B Unit := do
        lxWindow_2 cur pp powers his out w 191 [(cellOf t2 0).v]
      let t3_192 : B Unit := do
        lxWindow_2 cur pp powers his out w 192 [(cellOf t2 0).v]
      let t3_193 : B Unit := do
        lxWindow_2 cur pp powers his out w 193 [(cellOf t2 0).v]
      let t3_194 : B Unit := do
        lxWindow_2 cur pp powers his out w 194 [(cellOf t2 0).v]
      let t3_195 : B Unit := do
        lxWindow_2 cur pp powers his out w 195 [(cellOf t2 0).v]
      let t3_196 : B Unit := do
        lxWindow_2 cur pp powers his out w 196 [(cellOf t2 0).v]
      let t3_197 : B Unit := do
        lxWindow_2 cur pp powers his out w 197 [(cellOf t2 0).v]
      let t3_198 : B Unit := do
        lxWindow_2 cur pp powers his out w 198 [(cellOf t2 0).v]
      let t3_199 : B Unit := do
        lxWindow_2 cur pp powers his out w 199 [(cellOf t2 0).v]
      let t3_200 : B Unit := do
        lxWindow_2 cur pp powers his out w 200 [(cellOf t2 0).v]
      let t3_201 : B Unit := do
        lxWindow_2 cur pp powers his out w 201 [(cellOf t2 0).v]
      let t3_202 : B Unit := do
        lxWindow_2 cur pp powers his out w 202 [(cellOf t2 0).v]
      let t3_203 : B Unit := do
        lxWindow_2 cur pp powers his out w 203 [(cellOf t2 0).v]
      let t3_204 : B Unit := do
        lxWindow_2 cur pp powers his out w 204 [(cellOf t2 0).v]
      let t3_205 : B Unit := do
        lxWindow_2 cur pp powers his out w 205 [(cellOf t2 0).v]
      let t3_206 : B Unit := do
        lxWindow_2 cur pp powers his out w 206 [(cellOf t2 0).v]
      let t3_207 : B Unit := do
        lxWindow_2 cur pp powers his out w 207 [(cellOf t2 0).v]
      let t3_208 : B Unit := do
        lxWindow_2 cur pp powers his out w 208 [(cellOf t2 0).v]
      let t3_209 : B Unit := do
        lxWindow_2 cur pp powers his out w 209 [(cellOf t2 0).v]
      let t3_210 : B Unit := do
        lxWindow_2 cur pp powers his out w 210 [(cellOf t2 0).v]
      let t3_211 : B Unit := do
        lxWindow_2 cur pp powers his out w 211 [(cellOf t2 0).v]
      let t3_212 : B Unit := do
        lxWindow_2 cur pp powers his out w 212 [(cellOf t2 0).v]
      let t3_213 : B Unit := do
        lxWindow_2 cur pp powers his out w 213 [(cellOf t2 0).v]
      let t3_214 : B Unit := do
        lxWindow_2 cur pp powers his out w 214 [(cellOf t2 0).v]
      let t3_215 : B Unit := do
        lxWindow_2 cur pp powers his out w 215 [(cellOf t2 0).v]
      let t3_216 : B Unit := do
        lxWindow_2 cur pp powers his out w 216 [(cellOf t2 0).v]
      let t3_217 : B Unit := do
        lxWindow_2 cur pp powers his out w 217 [(cellOf t2 0).v]
      let t3_218 : B Unit := do
        lxWindow_2 cur pp powers his out w 218 [(cellOf t2 0).v]
      let t3_219 : B Unit := do
        lxWindow_2 cur pp powers his out w 219 [(cellOf t2 0).v]
      let t3_220 : B Unit := do
        lxWindow_2 cur pp powers his out w 220 [(cellOf t2 0).v]
      let t3_221 : B Unit := do
        lxWindow_2 cur pp powers his out w 221 [(cellOf t2 0).v]
      let t3_222 : B Unit := do
        lxWindow_2 cur pp powers his out w 222 [(cellOf t2 0).v]
      let t3_223 : B Unit := do
        lxWindow_2 cur pp powers his out w 223 [(cellOf t2 0).v]
      let t3_224 : B Unit := do
        lxWindow_2 cur pp powers his out w 224 [(cellOf t2 0).v]
      let t3_225 : B Unit := do
        lxWindow_2 cur pp powers his out w 225 [(cellOf t2 0).v]
      let t3_226 : B Unit := do
        lxWindow_2 cur pp powers his out w 226 [(cellOf t2 0).v]
      let t3_227 : B Unit := do
        lxWindow_2 cur pp powers his out w 227 [(cellOf t2 0).v]
      let t3_228 : B Unit := do
        lxWindow_2 cur pp powers his out w 228 [(cellOf t2 0).v]
      let t3_229 : B Unit := do
        lxWindow_2 cur pp powers his out w 229 [(cellOf t2 0).v]
      let t3_230 : B Unit := do
        lxWindow_2 cur pp powers his out w 230 [(cellOf t2 0).v]
      let t3_231 : B Unit := do
        lxWindow_2 cur pp powers his out w 231 [(cellOf t2 0).v]
      let t3_232 : B Unit := do
        lxWindow_2 cur pp powers his out w 232 [(cellOf t2 0).v]
      let t3_233 : B Unit := do
        lxWindow_2 cur pp powers his out w 233 [(cellOf t2 0).v]
      let t3_234 : B Unit := do
        lxWindow_2 cur pp powers his out w 234 [(cellOf t2 0).v]
      let t3_235 : B Unit := do
        lxWindow_2 cur pp powers his out w 235 [(cellOf t2 0).v]
      let t3_236 : B Unit := do
        lxWindow_2 cur pp powers his out w 236 [(cellOf t2 0).v]
      let t3_237 : B Unit := do
        lxWindow_2 cur pp powers his out w 237 [(cellOf t2 0).v]
      let t3_238 : B Unit := do
        lxWindow_2 cur pp powers his out w 238 [(cellOf t2 0).v]
      let t3_239 : B Unit := do
        lxWindow_2 cur pp powers his out w 239 [(cellOf t2 0).v]
      let t3_240 : B Unit := do
        lxWindow_2 cur pp powers his out w 240 [(cellOf t2 0).v]
      let t3_241 : B Unit := do
        lxWindow_2 cur pp powers his out w 241 [(cellOf t2 0).v]
      let t3_242 : B Unit := do
        lxWindow_2 cur pp powers his out w 242 [(cellOf t2 0).v]
      let t3_243 : B Unit := do
        lxWindow_2 cur pp powers his out w 243 [(cellOf t2 0).v]
      let t3_244 : B Unit := do
        lxWindow_2 cur pp powers his out w 244 [(cellOf t2 0).v]
      let t3_245 : B Unit := do
        lxWindow_2 cur pp powers his out w 245 [(cellOf t2 0).v]
      let t3_246 : B Unit := do
        lxWindow_2 cur pp powers his out w 246 [(cellOf t2 0).v]
      let t3_247 : B Unit := do
        lxWindow_2 cur pp powers his out w 247 [(cellOf t2 0).v]
      let t3_248 : B Unit := do
        lxWindow_2 cur pp powers his out w 248 [(cellOf t2 0).v]
      let t3_249 : B Unit := do
        lxWindow_2 cur pp powers his out w 249 [(cellOf t2 0).v]
      let t3_250 : B Unit := do
        lxWindow_2 cur pp powers his out w 250 [(cellOf t2 0).v]
      let t3_251 : B Unit := do
        lxWindow_2 cur pp powers his out w 251 [(cellOf t2 0).v]
      let t3_252 : B Unit := do
        lxWindow_2 cur pp powers his out w 252 [(cellOf t2 0).v]
      let t3_253 : B Unit := do
        lxWindow_2 cur pp powers his out w 253 [(cellOf t2 0).v]
      let t3_254 : B Unit := do
        lxWindow_2 cur pp powers his out w 254 [(cellOf t2 0).v]
      let t3_255 : B Unit := do
        lxWindow_2 cur pp powers his out w 255 [(cellOf t2 0).v]
      let _ ← B.matchArms (cellOf windows w) [t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7, t3_8, t3_9, t3_10, t3_11, t3_12, t3_13, t3_14, t3_15, t3_16, t3_17, t3_18, t3_19, t3_20, t3_21, t3_22, t3_23, t3_24, t3_25, t3_26, t3_27, t3_28, t3_29, t3_30, t3_31, t3_32, t3_33, t3_34, t3_35, t3_36, t3_37, t3_38, t3_39, t3_40, t3_41, t3_42, t3_43, t3_44, t3_45, t3_46, t3_47, t3_48, t3_49, t3_50, t3_51, t3_52, t3_53, t3_54, t3_55, t3_56, t3_57, t3_58, t3_59, t3_60, t3_61, t3_62, t3_63, t3_64, t3_65, t3_66, t3_67, t3_68, t3_69, t3_70, t3_71, t3_72, t3_73, t3_74, t3_75, t3_76, t3_77, t3_78, t3_79, t3_80, t3_81, t3_82, t3_83, t3_84, t3_85, t3_86, t3_87, t3_88, t3_89, t3_90, t3_91, t3_92, t3_93, t3_94, t3_95, t3_96, t3_97, t3_98, t3_99, t3_100, t3_101, t3_102, t3_103, t3_104, t3_105, t3_106, t3_107, t3_108, t3_109, t3_110, t3_111, t3_112, t3_113, t3_114, t3_115, t3_116, t3_117, t3_118, t3_119, t3_120, t3_121, t3_122, t3_123, t3_124, t3_125, t3_126, t3_127, t3_128, t3_129, t3_130, t3_131, t3_132, t3_133, t3_134, t3_135, t3_136, t3_137, t3_138, t3_139, t3_140, t3_141, t3_142, t3_143, t3_144, t3_145, t3_146, t3_147, t3_148, t3_149, t3_150, t3_151, t3_152, t3_153, t3_154, t3_155, t3_156, t3_157, t3_158, t3_159, t3_160, t3_161, t3_162, t3_163, t3_164, t3_165, t3_166, t3_167, t3_168, t3_169, t3_170, t3_171, t3_172, t3_173, t3_174, t3_175, t3_176, t3_177, t3_178, t3_179, t3_180, t3_181, t3_182, t3_183, t3_184, t3_185, t3_186, t3_187, t3_188, t3_189, t3_190, t3_191, t3_192, t3_193, t3_194, t3_195, t3_196, t3_197, t3_198, t3_199, t3_200, t3_201, t3_202, t3_203, t3_204, t3_205, t3_206, t3_207, t3_208, t3_209, t3_210, t3_211, t3_212, t3_213, t3_214, t3_215, t3_216, t3_217, t3_218, t3_219, t3_220, t3_221, t3_222, t3_223, t3_224, t3_225, t3_226, t3_227, t3_228, t3_229, t3_230, t3_231, t3_232, t3_233, t3_234, t3_235, t3_236, t3_237, t3_238, t3_239, t3_240, t3_241, t3_242, t3_243, t3_244, t3_245, t3_246, t3_247, t3_248, t3_249, t3_250, t3_251, t3_252, t3_253, t3_254, t3_255]
      pure ()
    cur := cellOf out 0
  root := cur
  B.assertEq root (← B.load signer 0)

end
end LeanVM.Dsl.Gen
