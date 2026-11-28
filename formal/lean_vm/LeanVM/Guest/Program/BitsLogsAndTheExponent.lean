/-
  LeanVM.Guest.Program.BitsLogsAndTheExponent

  The guest's section "bits, logs, and the exponent".
-/

module

public import LeanVM.Guest.Program.FiatShamir

/-!
# Bits, logs, and the exponent
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- A read-only lookup table over the exponent domain, indexed at runtime g-powers (so it must be heap, not stack): g_squares[g^j] = g^(2^j) turns integer sums of powers of two into field products. It spans SIZE_BITS because `log2_ceil_in_the_exponent` bounds its result there and indexes it at g^L. Past them, the opening selector's nibble shares: g^(u 2^(4j)) at SIZE_BITS + 16j + u. -/
def exponentTables : GFn where
  name := "exponent_tables"
  arity := 0
  rets := 1
  body ps := do
    let gSquares ← B.heapBuf 2284
    let mut sqRun : GPow := ⟨1⟩
    for j in [0:SIZE_BITS] do
      gSquares[GEN ^ j] := GEN ^ sqRun.exp
      sqRun := ⟨sqRun.exp + sqRun.exp⟩
    -- Then the rank keys g^(kappa RANK_STRIDE) of the placement orders.
    for k in [0:SIZE_BITS] do
      gSquares[GEN ^ (RANK_KEYS_AT + k)] := GEN ^ (k * RANK_STRIDE)
    -- Then each bus block group's side.
    for s in [0:N_GKR_SIDES] do
      for gi in [arrInt SIDE_GROUP_START s:arrInt SIDE_GROUP_START (s + 1)] do
        gSquares[GEN ^ (SIDE_TAB_AT + gi)] := lit s
    let mut base : GPow := ⟨1⟩
    for j in [0:SEL_TAB_NIBBLES] do
      let mut share : GPow := ⟨0⟩
      for u in [0:16] do
        gSquares[GEN ^ (SIZE_BITS + 16 * j + u)] := GEN ^ share.exp
        share := ⟨share.exp + base.exp⟩
      base := ⟨share.exp⟩
    -- Last, a bit window's pattern by its g-power, for `query_window`.
    for n in [0:WIN_TAB_LEN] do
      gSquares[GEN ^ (WIN_TAB_AT + n)] := lit n
    return [.v gSquares.v]

/-- g^value for a concrete integer `value` < 2^LOG_WORD_BITS: advice-decompose its bits, tie them back to the word, and assemble Π g^(bit_j·2^j). -/
def gPowerOfWord : GFn where
  name := "g_power_of_word"
  arity := 1
  rets := 1
  body ps := do
    let value := ps[0]
    let bits ← B.stackBuf LOG_WORD_BITS
    B.hintBits (.stack bits[0:LOG_WORD_BITS]) value 0 LOG_WORD_BITS
    let mut word : FW := FW.c (lit 0)
    let mut gValue : FW := FW.c (gpowE 0)
    for j in [0:LOG_WORD_BITS] do
      let bit := bits[j]
      bits[j] := bit * bit
      word ← fold (word + bit * 2 ^ j)
      gValue ← fold (gValue * (1 + bit * (1 + GEN ^ (2 ^ j))))
    assert word == value
    return [Ex.ret gValue]

/-- x = g^e with e < 2^(4 SEL_TAB_NIBBLES): hinted g-power digits, each range-checked below 16, whose weighted product is x. A g-power past that, a "negative" difference of two small exponents above all, has no such digits. -/
def assertSmallGPower : GFn where
  name := "assert_small_g_power"
  arity := 2
  rets := 0
  body ps := do
    let x := ps[0]
    let gSquares := ps[1]
    let digits ← B.stackBuf SEL_TAB_NIBBLES
    B.hintDigitsExp (.stack digits[0:SEL_TAB_NIBBLES]) x (4 * SEL_TAB_NIBBLES) SEL_TAB_NIBBLES 4 0
    let shares : Shifted := ⟨gSquares, SIZE_BITS⟩
    let mut rebuilt : Word := default
    for j in [0:SEL_TAB_NIBBLES] do
      let d := digits[j]
      assert log d < 16
      if j = 0 then
        rebuilt ← val shares[d]
      else
        rebuilt ← val (rebuilt * shares[GEN ^ (16 * j) * d])
    assert rebuilt == x
    return []

/-- g^L, L = max(log2_ceil(N), floor), given g_N = g^N. L is advice, pinned by 2^L - N >= 0 and, above the floor, N - 2^(L-1) - 1 >= 0, each a g-power with a small exponent (a negative one wraps around the order of g). The first bounds N below 2^nbits, as L < SIZE_BITS = nbits. N must be known nonnegative: at the floor only 2^floor - N is checked, which a small negative N passes too. Both callers build g_N as a product of certified powers g^(2^kappa). -/
def log2CeilInTheExponent (floor : Nat) (nbits : Nat) : GFn where
  name := instName "log2_ceil_in_the_exponent" [.L floor, .L nbits]
  arity := 2
  rets := 1
  body ps := do
    let gN := ps[0]
    let gSquares := ps[1]
    let bits ← B.heapBufDyn (← val (GEN ^ nbits))
    B.hintBitsExpTo (.heap bits.v 0 nbits) gN nbits
    let gLog ← hinted (B.hintLog2Ceil (.heap bits.v 0 nbits) nbits floor)
    assert log gLog < SIZE_BITS
    assert log (gLog / GEN ^ floor) < SIZE_BITS
    call "assert_small_g_power" [gSquares[gLog] / gN, gSquares]
    let t1 ← val (gLog + GEN ^ floor)
    let _ ← B.ite t1
      (do
        pure ())
      (do
        call "assert_small_g_power" [gN * INV_GEN / gSquares[GEN ^ 0 * (gLog * INV_GEN)], gSquares]
        pure ())
    return [.v gLog.v]

/-- log(w) < 2^width, the bound spelled out per width (a range check takes a literal bound). -/
def assertWindow (w : Word) (width : Nat) : B Unit := B.inline "assert_window" do
  if width = 1 then
    assert log w < 2
    pure ()
  else if width = 2 then
    assert log w < 4
    pure ()
  else if width = 3 then
    assert log w < 8
    pure ()
  else if width = 4 then
    assert log w < 16
    pure ()
  else if width = 5 then
    assert log w < 32
    pure ()
  else if width = 6 then
    assert log w < 64
    pure ()
  else if width = 7 then
    assert log w < 128
    pure ()
  else if width = 8 then
    assert log w < 256
    pure ()
  else if width = 9 then
    assert log w < 512
    pure ()
  else if width = 10 then
    assert log w < 1024
    pure ()
  else if width = 11 then
    assert log w < 2048
    pure ()
  else
    assert 0 == 1  -- no window is wider than the window table covers

/-- Bits start..start+width of `word` into wins[at] as g^n, n the integer they spell, range checked below 2^width. Returns n's bit pattern, `tabs[g^n]` (`query_tables`). -/
def queryWindow (word : Word) (wins : List V) (tabs : Word) (at' : Nat) (start : Nat) (width : Nat) : B Word := B.inline "query_window" do
  B.hintWindowsExp (.stack wins[0:at' + 1]) word start width 1 at'
  let w := wins[at']
  assertWindow w width
  let t0 ← val tabs[w]
  return t0

/-- A window whose bits cross a limb boundary `cut` bits in: its two runs hinted and range checked apart, each read as its bit pattern into parts[0], parts[1], and joined in the exponent into wins[at]. -/
def queryWindowSplit (word : Word) (wins : List V) (tabs : Word) (parts : List V) (at' : Nat) (start : Nat) (width : Nat) (cut : Nat) : B Unit := B.inline "query_window_split" do
  B.hintWindowsExp (.stack parts[0:2 + 1]) word start cut 1 2
  B.hintWindowsExp (.stack parts[0:3 + 1]) word (start + cut) (width - cut) 1 3
  let lo := parts[2]
  let hi := parts[3]
  assertWindow lo cut
  assertWindow hi (width - cut)
  let mut hp := hi
  for _ in [0:cut] do
    hp ← val (hp * hp)
  wins[at'] := lo * hp
  parts[0] := tabs[lo]
  parts[1] := tabs[hi]

set_option maxHeartbeats 4000000 in
/-- The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns, shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there, the polynomial basis shifting a run as a whole only inside one limb. -/
def decodeQueryWindows (depth : Nat) (capDepth : Nat) : GFn where
  name := instName "decode_query_windows" [.L depth, .L capDepth]
  arity := 4
  rets := 0
  body ps := do
    let squeezedWord := ps[0]
    let positionsOut := ps[1]
    let winPtrsOut := ps[2]
    let tabs := ps[3]
    let perWord := FIELD_BITS / depth
    let path := depth - capDepth
    let nPw := (path + QW - 1) / QW
    let nWin := nPw + 2
    let wins ← B.stackBuf QUERY_WINDOWS_CAP
    let winsPtr ← B.addr wins
    let mut reconstructed : FW := FW.c (lit 0)
    let mut off : Nat := default
    let mut width : Nat := default
    let mut parts : List V := default
    for j in [0:perWord] do
      let base := j * depth
      let at0 := j * nWin
      -- bits of this position below the next limb; at least `depth` when it does not cross one
      let cut := 64 - base % 64
      let mut pLo : FW := FW.c (lit 0)
      let mut pHi : FW := FW.c (lit 0)
      for i in [0:nWin] do
        -- window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
        if i + 2 = nWin then
          off := path
          width := 1
        else if i + 1 = nWin then
          off := path + 1
          width := capDepth - 1
        else if i + 3 = nWin then
          off := QW * i
          width := path - QW * i
        else
          off := QW * i
          width := QW
        if (off + width) / (cut + 1) = 0 then
          pLo ← fold (pLo + queryWindow squeezedWord wins tabs (at0 + i) (base + off) width * arrWord COORD_BASIS off)
        else if off / cut = 0 then
          parts ← B.stackBuf 4
          queryWindowSplit squeezedWord wins tabs parts (at0 + i) (base + off) width (cut - off)
          pLo ← fold (pLo + parts[0] * arrWord COORD_BASIS off)
          pHi ← fold (pHi + parts[1])
        else
          pHi ← fold (pHi + queryWindow squeezedWord wins tabs (at0 + i) (base + off) width * arrWord COORD_BASIS (off - cut))
      if cut / depth = 0 then
        positionsOut[GEN ^ j] := pLo + arrWord COORD_BASIS cut * pHi
        reconstructed ← fold (reconstructed + (arrWord COORD_BASIS base * pLo + arrWord COORD_BASIS (base + cut) * pHi))
      else
        positionsOut[GEN ^ j] := pLo
        reconstructed ← fold (reconstructed + arrWord COORD_BASIS base * pLo)
      winPtrsOut[GEN ^ j] := winsPtr * GEN ^ at0
    let rest ← B.stackBuf 4
    for i in [0:(FIELD_BITS - perWord * depth + 6) / 7] do
      let start := perWord * depth + 7 * i
      if (start + 7) / (FIELD_BITS + 1) = 0 then
        width := 7
      else
        width := FIELD_BITS - start
      reconstructed ← fold (reconstructed + queryWindow squeezedWord rest tabs i start width * arrWord COORD_BASIS start)
    assert reconstructed == squeezedWord
    return []

/-- The permutation that absorbs a grinding nonce must leave its third lane, the first of `word`, its second cell, with the low nbits zero (transcript::grind_check, 0 < nbits < 64). That lane is rebuilt from windows of its bits at and above nbits only, which IS the claim, and the word less it must be Y times a K element, which pins the rebuilt lane as its first. The windows are WIN_TAB_BITS wide but the top one, each range checked and read as its bit pattern, then joined by Horner in x, which is GEN: no shift leaves the limb. The honest prover searches the u64 nonces while verification permits the full field: each candidate still costs one permutation and passes with probability 2^-nbits. -/
def grindCheck (nbits : Nat) : GFn where
  name := instName "grind_check" [.L nbits]
  arity := 2
  rets := 0
  body ps := do
    let word := ps[0]
    let tabs := ps[1]
    let nWin := (BASE_FIELD_BITS - nbits + WIN_TAB_BITS - 1) / WIN_TAB_BITS
    let top := BASE_FIELD_BITS - nbits - WIN_TAB_BITS * (nWin - 1)
    let wins ← B.stackBuf 6
    B.hintWindowsExp (.stack wins[0:nWin - 1]) word nbits WIN_TAB_BITS (nWin - 1) 0
    B.hintWindowsExp (.stack wins[0:nWin - 1 + 1]) word (nbits + WIN_TAB_BITS * (nWin - 1)) top 1 (nWin - 1)
    let w := wins[nWin - 1]
    assertWindow w top
    let mut lane : Shifted ← Shifted.of <$> val tabs[w]
    for i in [1:nWin] do
      let w := wins[nWin - 1 - i]
      assertWindow w WIN_TAB_BITS
      lane ← Shifted.of <$> val (lane * GEN ^ WIN_TAB_BITS + tabs[w])
    lane := ⟨lane.base, lane.exp + nbits⟩
    let high ← val ((word + lane) * Y_INV)
    B.assertInK high (← val lane)
    return []

end
end LeanVM.Guest.Program
