/-
  LeanVM.Dsl.Gen.BitsLogsAndTheExponent

  The guest's section `BitsLogsAndTheExponent`, translated.
-/

module

public import LeanVM.Dsl.Gen.Inline

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

set_option linter.unusedVariables false in
/-- `exponent_tables` (`guests/lean_ethereum.py`, line 711):

```
def exponent_tables():
    # A read-only lookup table over the exponent domain, indexed at runtime g-powers
    # (so it must be heap, not stack): g_squares[g^j] = g^(2^j) turns integer sums of
    # powers of two into field products. It spans SIZE_BITS because
    # `log2_ceil_in_the_exponent` bounds its result there and indexes it at g^L.
    # Past them, the opening selector's nibble shares: g^(u 2^(4j)) at SIZE_BITS + 16j + u.
    g_squares = HeapBuf(WIN_TAB_AT + WIN_TAB_LEN)
    sq_run = GEN
    for j in unroll(0, SIZE_BITS):
        g_squares[GEN ** j] = sq_run
        sq_run *= sq_run
    # Then the rank keys g^(kappa RANK_STRIDE) of the placement orders.
    for k in unroll(0, SIZE_BITS):
        g_squares[GEN ** (RANK_KEYS_AT + k)] = GEN ** (k * RANK_STRIDE)
    # Then each bus block group's side.
    for s in unroll(0, N_GKR_SIDES):
        for gi in unroll(SIDE_GROUP_START[s], SIDE_GROUP_START[s + 1]):
            g_squares[GEN ** (SIDE_TAB_AT + gi)] = s
    base = GEN
    for j in unroll(0, SEL_TAB_NIBBLES):
        share = GEN ** 0
        for u in unroll(0, 16):
            g_squares[GEN ** (SIZE_BITS + 16 * j + u)] = share
            share *= base
        base = share
    # Last, a bit window's pattern by its g-power, for `query_window`.
    for n in unroll(0, WIN_TAB_LEN):
        g_squares[GEN ** (WIN_TAB_AT + n)] = const(n)
    return g_squares
```
-/
def exponentTables : GFn where
  name := "exponent_tables"
  arity := 0
  rets := 1
  body ps := do
    let gSquares ← B.heapBuf 2284
    let mut sqRun : GPow := ⟨1⟩
    for j_k in [0:SIZE_BITS] do
      B.store gSquares j_k (← B.const (gpowE sqRun.exp))
      sqRun := ⟨sqRun.exp + sqRun.exp⟩
    for k_k in [0:SIZE_BITS] do
      B.store gSquares (RANK_KEYS_AT + k_k) (← B.const (gpowE (k_k * RANK_STRIDE)))
    for s_k in [0:N_GKR_SIDES] do
      for gi_k in [arrInt SIDE_GROUP_START s_k:arrInt SIDE_GROUP_START (s_k + 1)] do
        B.store gSquares (SIDE_TAB_AT + gi_k) (← B.const (lit s_k))
    let mut base : GPow := ⟨1⟩
    for j_k in [0:SEL_TAB_NIBBLES] do
      let mut share : GPow := ⟨0⟩
      for u_k in [0:16] do
        B.store gSquares ((SIZE_BITS + (16 * j_k)) + u_k) (← B.const (gpowE share.exp))
        share := ⟨share.exp + base.exp⟩
      base := ⟨share.exp⟩
    for n_k in [0:WIN_TAB_LEN] do
      B.store gSquares (WIN_TAB_AT + n_k) (← B.const (lit n_k))
    return [.v gSquares.v]

set_option linter.unusedVariables false in
/-- `g_power_of_word` (`guests/lean_ethereum.py`, line 742):

```
def g_power_of_word(value):
    # g^value for a concrete integer `value` < 2^LOG_WORD_BITS: advice-decompose its
    # bits, tie them back to the word, and assemble Π g^(bit_j·2^j).
    bits = StackBuf(LOG_WORD_BITS)
    hint_decompose_bits(bits, value, LOG_WORD_BITS)
    word = 0
    g_value = GEN ** 0
    for j in unroll(0, LOG_WORD_BITS):
        bit = bits[j]
        bits[j] = bit * bit
        word += bit * (2 ** j)
        g_value *= 1 + bit * (1 + GEN ** (2 ** j))
    assert word == value
    return g_value
```
-/
def gPowerOfWord : GFn where
  name := "g_power_of_word"
  arity := 1
  rets := 1
  body ps := do
    let value := cellOf ps 0
    let bits ← B.stackBuf LOG_WORD_BITS
    B.hintBits (.stack (bits.take LOG_WORD_BITS)) value 0 LOG_WORD_BITS
    let word' := 0
    let gValue : GPow := ⟨0⟩
    let mut word'_word : Word := default
    let mut gValue_word : Word := default
    let j_k := 0
    let bit := cellOf bits j_k
    B.mulInto (cellOf bits j_k) bit bit
    word'_word := bit
    gValue_word ← B.add (← B.const 1) (← B.mul bit (← B.const (1 + (gpowE (2 ^ j_k)))))
    for j_k in [1:LOG_WORD_BITS] do
      let bit := cellOf bits j_k
      B.mulInto (cellOf bits j_k) bit bit
      word'_word ← B.add word'_word (← B.mul bit (← B.const ((lit 2) ^ j_k)))
      gValue_word ← B.mul gValue_word (← B.add (← B.const 1) (← B.mul bit (← B.const (1 + (gpowE (2 ^ j_k))))))
    B.assertEq word'_word value
    return [.v gValue_word.v]

set_option linter.unusedVariables false in
/-- `assert_small_g_power` (`guests/lean_ethereum.py`, line 758):

```
def assert_small_g_power(x, g_squares):
    # x = g^e with e < 2^(4 SEL_TAB_NIBBLES): hinted g-power digits, each range-checked
    # below 16, whose weighted product is x. A g-power past that, a "negative"
    # difference of two small exponents above all, has no such digits.
    digits = StackBuf(SEL_TAB_NIBBLES)
    hint_decompose_digits_exponent(digits, x, 4 * SEL_TAB_NIBBLES, SEL_TAB_NIBBLES, 4, 0)
    shares = g_squares * GEN ** SIZE_BITS
    for j in unroll(0, SEL_TAB_NIBBLES):
        d = digits[j]
        assert log(d) < 16
        if const(j == 0):
            rebuilt = shares[d]
        else:
            rebuilt *= shares[GEN ** (16 * j) * d]
    assert rebuilt == x
    return
```
-/
def assertSmallGPower : GFn where
  name := "assert_small_g_power"
  arity := 2
  rets := 0
  body ps := do
    let x := cellOf ps 0
    let gSquares := cellOf ps 1
    let digits ← B.stackBuf SEL_TAB_NIBBLES
    B.hintDigitsExp (.stack (digits.take SEL_TAB_NIBBLES)) x (4 * SEL_TAB_NIBBLES) SEL_TAB_NIBBLES 4 0
    let shares : Shifted := ⟨gSquares, SIZE_BITS⟩
    let mut rebuilt : Word := default
    for j_k in [0:SEL_TAB_NIBBLES] do
      let d := cellOf digits j_k
      let _ ← B.rangeCheck d 16
      if j_k = 0 then
        rebuilt ← B.load (← B.mul shares.base d) shares.exp
      else
        rebuilt ← B.mul rebuilt (← B.load (← B.mul shares.base d) (shares.exp + (16 * j_k)))
    B.assertEq rebuilt x
    return []

set_option linter.unusedVariables false in
/-- `grind_check`, a `Const` family (`guests/lean_ethereum.py`, line 917):

```
def grind_check(word, tabs, nbits: Const):
    # The permutation that absorbs a grinding nonce must leave its third lane, the first
    # of `word`, its second cell, with the low nbits zero (transcript::grind_check,
    # 0 < nbits < 64). That lane is rebuilt from windows of its bits at and above nbits
    # only, which IS the claim, and the word less it must be Y times a K element, which
    # pins the rebuilt lane as its first. The windows are WIN_TAB_BITS wide but the top
    # one, each range checked and read as its bit pattern, then joined by Horner in x,
    # which is GEN: no shift leaves the limb. The honest prover searches the u64 nonces
    # while verification permits the full field: each candidate still costs one
    # permutation and passes with probability 2^-nbits.
    n_win = (BASE_FIELD_BITS - nbits + WIN_TAB_BITS - 1) // WIN_TAB_BITS
    top = BASE_FIELD_BITS - nbits - WIN_TAB_BITS * (n_win - 1)
    wins = StackBuf(BASE_FIELD_BITS // WIN_TAB_BITS + 1)
    hint_windows_exponent(wins, word, nbits, WIN_TAB_BITS, n_win - 1, 0)
    hint_windows_exponent(wins, word, nbits + WIN_TAB_BITS * (n_win - 1), top, 1, n_win - 1)
    w = wins[n_win - 1]
    assert_window(w, top)
    lane = tabs[w]
    for i in unroll(1, n_win):
        w = wins[n_win - 1 - i]
        assert_window(w, WIN_TAB_BITS)
        lane = lane * GEN ** WIN_TAB_BITS + tabs[w]
    lane = lane * GEN ** nbits
    high = (word + lane) * Y_INV
    assert_in_k(high, lane)
    return
```
-/
def grindCheck (nbits : Nat) : GFn where
  name := instName "grind_check" [.L nbits]
  arity := 2
  rets := 0
  body ps := do
    let word' := cellOf ps 0
    let tabs := cellOf ps 1
    let nWin := (((BASE_FIELD_BITS - nbits) + WIN_TAB_BITS) - 1) / WIN_TAB_BITS
    let top := (BASE_FIELD_BITS - nbits) - (WIN_TAB_BITS * (nWin - 1))
    let wins ← B.stackBuf 6
    B.hintWindowsExp (.stack (wins.take (nWin - 1))) word' nbits WIN_TAB_BITS (nWin - 1) 0
    B.hintWindowsExp (.stack (wins.take ((nWin - 1) + 1))) word' (nbits + (WIN_TAB_BITS * (nWin - 1))) top 1 (nWin - 1)
    let w := cellOf wins (nWin - 1)
    assertWindow w top
    let mut lane ← B.load (← B.mul tabs w) 0
    for i_k in [1:nWin] do
      let w := cellOf wins ((nWin - 1) - i_k)
      assertWindow w WIN_TAB_BITS
      lane ← B.add (← B.shifted lane WIN_TAB_BITS) (← B.load (← B.mul tabs w) 0)
    let lane_ptr : Shifted := ⟨lane, nbits⟩
    let high ← B.mul (← B.add word' (← B.shifted lane_ptr.base lane_ptr.exp)) (← B.const (lit Y_INV))
    B.assertInK high (← B.shifted lane_ptr.base lane_ptr.exp)
    return []

set_option linter.unusedVariables false in
/-- `log2_ceil_in_the_exponent`, a `Const` family (`guests/lean_ethereum.py`, line 776):

```
def log2_ceil_in_the_exponent(g_N, g_squares, floor: Const, nbits: Const):
    # g^L, L = max(log2_ceil(N), floor), given g_N = g^N. L is advice, pinned by
    # 2^L - N >= 0 and, above the floor, N - 2^(L-1) - 1 >= 0, each a g-power with a
    # small exponent (a negative one wraps around the order of g). The first bounds
    # N below 2^nbits, as L < SIZE_BITS = nbits. N must be known nonnegative: at the
    # floor only 2^floor - N is checked, which a small negative N passes too. Both
    # callers build g_N as a product of certified powers g^(2^kappa).
    bits = HeapBuf(GEN ** nbits)
    hint_decompose_bits_exponent(bits, g_N, nbits)
    g_log = hint_log2_ceil(bits, nbits, floor)
    assert log(g_log) < SIZE_BITS
    assert log(g_log / GEN ** floor) < SIZE_BITS
    assert_small_g_power(g_squares[g_log] / g_N, g_squares)
    if g_log != GEN ** floor:
        assert_small_g_power(g_N * INV_GEN / g_squares[g_log * INV_GEN], g_squares)
    return g_log
```
-/
def log2CeilInTheExponent (floor : Nat) (nbits : Nat) : GFn where
  name := instName "log2_ceil_in_the_exponent" [.L floor, .L nbits]
  arity := 2
  rets := 1
  body ps := do
    let gN := cellOf ps 0
    let gSquares := cellOf ps 1
    let bits ← B.heapBufDyn (← B.const (gpowE nbits))
    B.hintBitsExpTo (.heap bits.v 0 nbits) gN nbits
    let gLog ← hinted (B.hintLog2Ceil (.heap bits.v 0 nbits) nbits floor)
    let _ ← B.rangeCheck gLog SIZE_BITS
    let t0 ← B.const (gpowE (SIZE_BITS - 1))
    let _ ← B.rangeCheckK (← B.fdiv gLog (← B.const (gpowE floor))) t0
    let _ ← B.call "assert_small_g_power" [(← B.fdiv (← B.load (← B.mul gSquares gLog) 0) gN).v, gSquares.v] 0
    let t1 ← B.add gLog (← B.const (gpowE floor))
    let _ ← B.ite t1
      (do
        pure ())
      (do
        let _ ← B.call "assert_small_g_power" [(← B.fdiv (← B.mul gN (← B.const (lit INV_GEN))) (← B.load (← B.mul gSquares (← B.mul gLog (← B.const (lit INV_GEN)))) 0)).v, gSquares.v] 0
        pure ())
    return [.v gLog.v]

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    for j_k in [1:4] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 4
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    for i_k in [0:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pure () -- no use of this definition takes this branch
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word := cellOf parts 0
          pHi_word := cellOf parts 1
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [5:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_2 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    for j_k in [1:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_3 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    for j_k in [1:3] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 3
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        if (off / cut) = 0 then
          pure () -- no use of this definition takes this branch
        else
          pHi_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [4:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_4 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    for j_k in [1:3] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 3
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    for i_k in [0:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word ← B.add pLo_word (← B.mul (cellOf parts 0) (← B.const (arrWord COORD_BASIS off)))
          pHi_word := cellOf parts 1
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [4:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    let i_k := 0
    let start := (perWord * depth) + (7 * i_k)
    if ((start + 7) / (FIELD_BITS + 1)) = 0 then
      pure () -- no use of this definition takes this branch
    else
      width := FIELD_BITS - start
    reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_5 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    for j_k in [1:4] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 4
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    for i_k in [0:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word ← B.add pLo_word (← B.mul (cellOf parts 0) (← B.const (arrWord COORD_BASIS off)))
          pHi_word := cellOf parts 1
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [5:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    let i_k := 0
    let start := (perWord * depth) + (7 * i_k)
    if ((start + 7) / (FIELD_BITS + 1)) = 0 then
      pure () -- no use of this definition takes this branch
    else
      width := FIELD_BITS - start
    reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_6 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          off := QW * i_k
          width := path - (QW * i_k)
        else
          pure () -- no use of this definition takes this branch
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    for j_k in [1:4] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 4
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          off := QW * i_k
          width := path - (QW * i_k)
        else
          pure () -- no use of this definition takes this branch
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word ← B.add pLo_word (← B.mul (cellOf parts 0) (← B.const (arrWord COORD_BASIS off)))
          pHi_word := cellOf parts 1
        else
          pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [5:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_7 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          off := QW * i_k
          width := path - (QW * i_k)
        else
          pure () -- no use of this definition takes this branch
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    for j_k in [1:5] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 5
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    for i_k in [0:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pure () -- no use of this definition takes this branch
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word := cellOf parts 0
          pHi_word := cellOf parts 1
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [6:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_8 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    for j_k in [1:3] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 3
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    for i_k in [0:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit_2 squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word ← B.add pLo_word (← B.mul (cellOf parts 0) (← B.const (arrWord COORD_BASIS off)))
          pHi_word := cellOf parts 1
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [4:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              pure () -- no use of this definition takes this branch
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        pure () -- no use of this definition takes this branch
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_9 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    for j_k in [1:3] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              off := QW * i_k
              width := QW
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 3
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    for i_k in [0:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pure () -- no use of this definition takes this branch
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word := cellOf parts 0
          pHi_word := cellOf parts 1
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [4:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              off := QW * i_k
              width := QW
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_10 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    for j_k in [1:3] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              off := QW * i_k
              width := QW
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 3
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    for i_k in [0:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pure () -- no use of this definition takes this branch
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit_2 squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word := cellOf parts 0
          pHi_word := cellOf parts 1
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [4:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              off := QW * i_k
              width := QW
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    let i_k := 0
    let start := (perWord * depth) + (7 * i_k)
    if ((start + 7) / (FIELD_BITS + 1)) = 0 then
      pure () -- no use of this definition takes this branch
    else
      width := FIELD_BITS - start
    reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_11 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    let j_k := 1
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 2
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit_2 squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word ← B.add pLo_word (← B.mul (cellOf parts 0) (← B.const (arrWord COORD_BASIS off)))
          pHi_word := cellOf parts 1
        else
          pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [3:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              off := QW * i_k
              width := QW
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_12 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    let j_k := 1
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 2
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:4] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        if (off / cut) = 0 then
          pure () -- no use of this definition takes this branch
        else
          pHi_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    let i_k := 4
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        off := path + 1
        width := capDepth - 1
      else
        pure () -- no use of this definition takes this branch
    if ((off + width) / (cut + 1)) = 0 then
      pure () -- no use of this definition takes this branch
    else
      if (off / cut) = 0 then
        pure () -- no use of this definition takes this branch
      else
        pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [3:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              off := QW * i_k
              width := QW
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_13 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    let j_k := 1
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 2
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word ← B.add pLo_word (← B.mul (cellOf parts 0) (← B.const (arrWord COORD_BASIS off)))
          pHi_word := cellOf parts 1
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [3:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              off := QW * i_k
              width := QW
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_14 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    let j_k := 1
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 2
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word ← B.add pLo_word (← B.mul (cellOf parts 0) (← B.const (arrWord COORD_BASIS off)))
          pHi_word := cellOf parts 1
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    for j_k in [3:perWord] do
      let base := j_k * depth
      let at0 := j_k * nWin
      let cut := 64 - (base % 64)
      let pLo := 0
      let pHi := 0
      let i_k := 0
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:nWin] do
        if (i_k + 2) = nWin then
          off := path
          width := 1
        else
          if (i_k + 1) = nWin then
            off := path + 1
            width := capDepth - 1
          else
            if (i_k + 3) = nWin then
              off := QW * i_k
              width := path - (QW * i_k)
            else
              off := QW * i_k
              width := QW
        if ((off + width) / (cut + 1)) = 0 then
          pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
        else
          pure () -- no use of this definition takes this branch
      if (cut / depth) = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store positionsOut j_k pLo_word
        reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
      B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    let i_k := 0
    let start := (perWord * depth) + (7 * i_k)
    if ((start + 7) / (FIELD_BITS + 1)) = 0 then
      pure () -- no use of this definition takes this branch
    else
      width := FIELD_BITS - start
    reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_15 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    let j_k := 1
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 2
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:3] do
      if (i_k + 2) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 1) = nWin then
          pure () -- no use of this definition takes this branch
        else
          if (i_k + 3) = nWin then
            pure () -- no use of this definition takes this branch
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        if (off / cut) = 0 then
          pure () -- no use of this definition takes this branch
        else
          pHi_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    for i_k in [3:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            pure () -- no use of this definition takes this branch
      if ((off + width) / (cut + 1)) = 0 then
        pure () -- no use of this definition takes this branch
      else
        if (off / cut) = 0 then
          pure () -- no use of this definition takes this branch
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 3
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

set_option linter.unusedVariables false in
/-- `decode_query_windows`, a `Const` family (`guests/lean_ethereum.py`, line 853):

```
def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return
```
-/
def decodeQueryWindows_16 (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := cellOf ps 0
    let positionsOut := cellOf ps 1
    let winPtrsOut := cellOf ps 2
    let tabs := cellOf ps 3
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := ((path + QW) - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let reconstructed := 0
    let mut off : Nat := default
    let mut width : Nat := default
    let mut reconstructed_word : Word := default
    let mut parts : List V := default
    let j_k := 0
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pLo_word : Word := default
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word := pLo_word
    B.store winPtrsOut j_k winsPtr
    let j_k := 1
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 2
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let mut pHi_word : Word := default
    for i_k in [0:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
      else
        if (off / cut) = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit squeezedWord wins tabs parts (at0 + i_k) (base + off) width (cut - off)
          pLo_word ← B.add pLo_word (← B.mul (cellOf parts 0) (← B.const (arrWord COORD_BASIS off)))
          pHi_word := cellOf parts 1
        else
          pHi_word ← B.add pHi_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS (off - cut))))
    if (cut / depth) = 0 then
      B.store positionsOut j_k (← B.add pLo_word (← B.mul (← B.const (arrWord COORD_BASIS cut)) pHi_word))
      reconstructed_word ← B.add reconstructed_word (← B.add (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word) (← B.mul (← B.const (arrWord COORD_BASIS (base + cut))) pHi_word))
    else
      pure () -- no use of this definition takes this branch
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let j_k := 3
    let base := j_k * depth
    let at0 := j_k * nWin
    let cut := 64 - (base % 64)
    let pLo := 0
    let pHi := 0
    let i_k := 0
    if (i_k + 2) = nWin then
      pure () -- no use of this definition takes this branch
    else
      if (i_k + 1) = nWin then
        pure () -- no use of this definition takes this branch
      else
        if (i_k + 3) = nWin then
          pure () -- no use of this definition takes this branch
        else
          off := QW * i_k
          width := QW
    if ((off + width) / (cut + 1)) = 0 then
      pLo_word ← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:nWin] do
      if (i_k + 2) = nWin then
        off := path
        width := 1
      else
        if (i_k + 1) = nWin then
          off := path + 1
          width := capDepth - 1
        else
          if (i_k + 3) = nWin then
            off := QW * i_k
            width := path - (QW * i_k)
          else
            off := QW * i_k
            width := QW
      if ((off + width) / (cut + 1)) = 0 then
        pLo_word ← B.add pLo_word (← B.mul (← queryWindow squeezedWord wins tabs (at0 + i_k) (base + off) width) (← B.const (arrWord COORD_BASIS off)))
      else
        pure () -- no use of this definition takes this branch
    if (cut / depth) = 0 then
      pure () -- no use of this definition takes this branch
    else
      B.store positionsOut j_k pLo_word
      reconstructed_word ← B.add reconstructed_word (← B.mul (← B.const (arrWord COORD_BASIS base)) pLo_word)
    B.store winPtrsOut j_k (← B.shifted winsPtr at0)
    let rest ← B.stackBuf 4
    for i_k in [0:((FIELD_BITS - (perWord * depth)) + 6) / 7] do
      let start := (perWord * depth) + (7 * i_k)
      if ((start + 7) / (FIELD_BITS + 1)) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed_word ← B.add reconstructed_word (← B.mul (← queryWindow squeezedWord rest tabs i_k start width) (← B.const (arrWord COORD_BASIS start)))
    B.assertEq reconstructed_word squeezedWord
    return []

end
end LeanVM.Dsl.Gen
