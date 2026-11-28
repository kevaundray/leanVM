/-
  LeanVM.Guest.Program.LeanXmss

  The guest's section "leanXMSS signature verification".
-/

module

public import LeanVM.Guest.Program.WotsC

/-!
# LeanXMSS signature verification
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- The LX_WINDOW path levels from LX_WINDOW * w, whose index bits are k's, from `cur` into out. A node's order against its hinted sibling is k's bit, and a parent's address holds `leaf_index >> (level + 1)`: his[w + 1] shifted up by what is left of the window, k's higher bits added. Nothing is above the top window. -/
def lxLevels (cur : Word) (pp : Word) (powers : List V) (his : List V) (out : List V) (w : Nat) (k : Nat) : B Unit := B.inline "lx_levels" do
  let mut cur := cur
  for r in [0:LX_WINDOW] do
    let tag := TW_NODE + ((LX_WINDOW * w + r) % LX_HEIGHT + 1) * HI_MUL + (LX_WINDOW * w + r) / LX_HEIGHT * LX_TOP + k / 2 ^ (r + 1)
    let mut at' : FW := default
    if w + 1 = LX_WINDOWS then
      at' := FW.c (lit tag)
    else if r + 1 = LX_WINDOW then
      at' ← fold (his[w + 1] + tag)
    else
      at' ← fold (his[w + 1] * powers[LX_WINDOW - 1 - r] + tag)
    let mut parent : List V := default
    if r + 1 = LX_WINDOW then
      parent := out
    else
      parent ← B.stackBuf 1
    let sibling ← hinted (B.witnessCell "lx_path")
    if k / 2 ^ r % 2 = 0 then
      B.keccak (.words [.cell pp.v, (← at'.msg)]) [cur, sibling] parent
    else
      B.keccak (.words [.cell pp.v, (← at'.msg)]) [sibling, cur] parent
    cur := parent[0]

/-- Window w of the path (`lx_levels`). Returns his[w] as his[w + 1] and k spell it, which the dispatch writes where the hinted his[w] already is: so the index the signature's addresses use is the one its path takes. -/
def lxWindow (cur : Word) (pp : Word) (powers : List V) (his : List V) (out : List V) (w : Nat) (k : Nat) (dsts : List V) : B Unit := B.inline "lx_window" do
  lxLevels cur pp powers his out w k
  dsts[0] := his[w + 1] * powers[LX_WINDOW] + lit k

/-- The top window, nothing above it: his[w] is k alone. -/
def lxTopWindow (cur : Word) (pp : Word) (powers : List V) (his : List V) (out : List V) (w : Nat) (k : Nat) (dsts : List V) : B Unit := B.inline "lx_top_window" do
  lxLevels cur pp powers his out w k
  dsts[0] := lit k

set_option maxHeartbeats 4000000 in
/-- `signer` is one 4-cell entry of the leanXMSS coverage table: the pubkey's merkle root and public parameter, then the message that pubkey signed. The bottom layer signs the message, the top layer the bottom root. -/
def verifyLeanXmss (signer : Word) (tags : List V) : B Unit := B.inline "verify_lean_xmss" do
  let pp ← val signer[GEN ^ 1]
  -- The leaf index rides the signature, so every address is derived here from it. It is advice: his[v] is `leaf_index >> (LX_WINDOW * v)`, a field's value, and each window of LX_WINDOW bits is hinted again in the exponent, range checked and dispatched on by the path (`lx_window`). Each arm pins his[w] to his[w + 1] and its own bits, and the top one has nothing above it, so his[0] is the index the windows spell. Any index is one some signature may carry; the digests and the root this signature must reach bind it.
  let his ← B.stackBuf LX_WINDOWS
  B.witness "lx_index" (.stack his)
  let windows ← B.stackBuf LX_WINDOWS
  B.witness "lx_windows" (.stack windows)
  let powers ← B.stackBuf 13
  for s in [0:LX_DIGIT_GROUP * CHAIN_STEPS + 1] do
    powers[s] := GEN ^ s
  let mut w : Nat := default
  let mut out : List V := default
  let mut root : Word := default
  for layer in [0:2] do
    let mut idx : Word := default
    if layer = 0 then
      idx := his[0]
    else
      idx ← val (his[LX_LAYER_WINDOWS] + LX_TOP)
    -- D = Th(P, A, M | R), one block: 80 bytes at the bottom, and 64 at the top, where M is the bottom root.
    let rho ← hinted (B.witnessCell "randomizer")
    let digest ← B.stackBuf 1
    if layer = 0 then
      B.keccak (a := .words [.cell pp.v, .cell (← val (idx + TW_MSG)).v]) (b := .words [.cell (← val signer[GEN ^ 2]).v, .cell (← val signer[GEN ^ 3]).v]) (tail := some (.words [.cell rho.v, .zero, .zero, .zero])) (len := some 80) (out := .frame digest)
    else
      B.keccak (.words [.cell pp.v, .cell (← val (idx + TW_MSG)).v]) [root, rho] digest
    -- The codeword: LX_DIGIT_GROUP digits at a time, hinted in the exponent, range checked and dispatched once, the arm walking every chain's remaining steps and folding its digits in: their sums into a product that must be the target sum, and the digits, each where the digest holds it, into D, which also checks the digits past LX_V are zero.
    let steps ← B.stackBuf CHAIN_STEPS
    for st in [0:CHAIN_STEPS] do
      steps[st] := idx + lit (TW_CHAIN + st * STEP_MUL)
    let walks ← B.stackBuf 174
    let mut digitProduct : FW := FW.c (lit 1)
    let mut encoded : FW := FW.c (lit 0)
    let groups ← B.stackBuf LX_DIGIT_DISPATCHES
    B.witness "lx_digits" (.stack groups)
    for p in [0:LX_DIGIT_DISPATCHES - 1] do
      assert log groups[p] < LX_DIGIT_GROUPS
      pure ()
    assert log groups[LX_DIGIT_DISPATCHES - 1] < LX_TAIL_GROUPS
    -- Back to back, each arm entering the next dispatch. The last group's table is as wide as the others, its range check what keeps it to LX_DIGIT_TAIL digits.
    for p in [0:LX_DIGIT_DISPATCHES] do
      let t0 ← B.targets [none, none]
      if p + 1 < LX_DIGIT_DISPATCHES then
        B.chain
      if p = 0 then
        Keccak.inlineArms
      let _ ← B.matchArms groups[p] ((List.range LX_DIGIT_GROUPS).map fun arm => do
        walkGroup steps pp walks tags (LX_DIGIT_GROUP * p) (arrInt LX_GROUP_SIZES p) arm 1 powers digitProduct encoded [t0[0].v, t0[1].v])
      digitProduct := FW.w t0[0]
      encoded := FW.w t0[1]
    digest[0] := encoded  -- the digits, stored where D already is
    assert digitProduct == GEN ^ LX_TARGET_SUM
    -- The one-time leaf, then the path to the layer's root, a window at a time.
    let leaf ← B.stackBuf 1
    wotsLeaf pp (← val (idx + TW_LEAF)) walks LX_V leaf
    let mut cur := leaf[0]
    for v_k in [0:LX_LAYER_WINDOWS] do
      w := layer * LX_LAYER_WINDOWS + v_k
      out ← B.stackBuf 1
      assert log windows[w] < LX_WINDOW_ARMS
      if w + 1 = LX_WINDOWS then
        let t1 ← B.targets [some his[w].v]
        Keccak.inlineArms
        let _ ← B.matchArms windows[w] ((List.range LX_WINDOW_ARMS).map fun arm => do
          lxTopWindow cur pp powers his out w arm [t1[0].v])
        pure ()
      else
        let t1 ← B.targets [some his[w].v]
        Keccak.inlineArms
        let _ ← B.matchArms windows[w] ((List.range LX_WINDOW_ARMS).map fun arm => do
          lxWindow cur pp powers his out w arm [t1[0].v])
        pure ()
      cur := out[0]
    root := cur
  assert root == signer[GEN ^ 0]

end
end LeanVM.Guest.Program
