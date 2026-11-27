/-
  LeanVM.Dsl.KeccakGuest

  Guest functions using the Keccak builtins, ported to the embedded language: the statement
  digest, the claim lists' last group, a DA cell's hash, the Fiat-Shamir permutation and a Merkle
  path window, each as the zkDSL compiles it today.
-/

module

public import LeanVM.Dsl.Keccak
public import LeanVM.Guest.Data.Source

/-!
# Ported Keccak users

Each function is written once, with the zkDSL source it replaces in its docstring. A `StackBuf`
is a Lean `List V` of frame values and a slice of one is `List.extract`; a heap slice is
`Cells.heap ptr lo len`, which the builtin reads or writes through fresh values. The `@inline`
functions (`fsPerm`, `walkWindow`, `spWord`) are Lean functions emitting into their caller's frame;
`fsPermAt`, `walkWindowAt`, `spWordLeaf`, `padTailAt` and `heapPair` call them, or the builtin
alone, from a function of their own for the comparison with `Expand`, as `isChildAt0` does in
`LeanVM.Dsl.Guest`.
-/

namespace LeanVM.Dsl.KeccakGuest

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

/-! ## Configuration -/

def KECCAK_STATE : Nat := LeanVM.Guest.Data.const_KECCAK_STATE
def STMT_CELLS : Nat := LeanVM.Guest.Data.const_STMT_CELLS
def STMT_HEADER : Nat := LeanVM.Guest.Data.const_STMT_HEADER
def STMT_DEFER_OFF : Nat := LeanVM.Guest.Data.const_STMT_DEFER_OFF
def DEFER_STMT_CELLS : Nat := LeanVM.Guest.Data.const_DEFER_STMT_CELLS
def CLAIM_GROUP : Nat := LeanVM.Guest.Data.const_CLAIM_GROUP
def DA_CELL : Nat := LeanVM.Guest.Data.const_DA_CELL
def SP_V : Nat := LeanVM.Guest.Data.const_SP_V
def CHAIN_STEPS : Nat := LeanVM.Guest.Data.const_CHAIN_STEPS

/-! ## `statement_digest`: `keccak_cells` of a frame run -/

/-- `statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer)`:

```
cells = StackBuf(STMT_CELLS)
cells[0] = seed_0  # ... cells[7] = da_1, the STMT_HEADER header cells
for i in unroll(0, DEFER_STMT_CELLS):
    cells[STMT_DEFER_OFF + i] = defer[GEN ** i]
st = StackBuf(2)
keccak_cells(cells, st)
return st[0], st[1]
```
-/
def statementDigest : GFn where
  name := "statement_digest"
  arity := STMT_HEADER + 1
  rets := 2
  body ps := do
    let cells ← B.stackBuf STMT_CELLS
    (List.range STMT_HEADER).forM fun i => B.atom (.copy cells[i]! ps[i]!)
    (List.range DEFER_STMT_CELLS).forM fun i =>
      B.atom (.load cells[STMT_DEFER_OFF + i]! ps[STMT_HEADER]! i)
    let st ← B.stackBuf 2
    B.keccakCells (.frame cells) (.frame st)
    return [.v st[0]!, .v st[1]!]

/-! ## `claim_list_last`: a `Const` family, heap message and heap state -/

/-- `claim_list_last(state, blk, k: Const)`, the instance at `k`:

```
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
  name := s!"claim_list_last__L{k}"
  arity := 2
  rets := 2
  body ps := do
    let state := ps[0]!
    let blk := ps[1]!
    let digest ← B.stackBuf 2
    if k = 0 then
      B.keccakCells (.words [.zero]) (.frame digest) (state := some (.heap state 0 KECCAK_STATE))
        (len := some 0)
    else
      (List.range k).forM fun j => B.hint (.witness "claims" (.heap blk (4 * j) 4))
      B.keccakCells (.heap blk 0 (4 * k)) (.frame digest)
        (state := some (.heap state 0 KECCAK_STATE))
    return [.v digest[0]!, .v digest[1]!]

/-! ## `da_verify_cell`: a hinted run, an inner product, `keccak_cells` over 16 blocks -/

/-- `s + lvals[GEN ** e] * sym[e]` from `e` on, `s` absent for the zkDSL's `s = 0`. -/
def innerProduct (lvals : Word) (sym : List V) : Option Word → List Nat → B (Option Word)
  | s, [] => pure s
  | s, e :: es => do
      let l ← B.load lvals e
      let p ← B.mul l (⟨sym[e]!⟩ : Word)
      let s' ← match s with
        | none => pure p
        | some s => B.add s p
      innerProduct lvals sym (some s') es

/-- `da_verify_cell(lvals)`:

```
sym = StackBuf(DA_CELL)
hint_witness(sym, "da_symbols")
s = 0
for e in unroll(0, DA_CELL):
    s = s + lvals[GEN ** e] * sym[e]
st = StackBuf(2)
keccak_cells(sym, st)
return st[0], st[1], s
```
-/
def daVerifyCell : GFn where
  name := "da_verify_cell"
  arity := 1
  rets := 3
  body ps := do
    let sym ← B.stackBuf DA_CELL
    B.hint (.witness "da_symbols" (.stack sym))
    let s ← innerProduct ⟨ps[0]!⟩ sym none (List.range DA_CELL)
    let st ← B.stackBuf 2
    B.keccakCells (.frame sym) (.frame st)
    return [.v st[0]!, .v st[1]!, match s with | some s => .v s.v | none => .c 0]

/-! ## `fs_perm`: the Fiat-Shamir duplex step (`cap=`) -/

/-- `fs_perm(sp, rate, k: Const)`, inline: the permutation taking the `k` waiting scalars, which
overwrite the rate, zero past them.

```
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
def fsPerm (sp rate : List V) (k : Nat) : B (List V) := do
  let nxt ← B.stackBuf KECCAK_STATE
  let zeros : Operand := .words [.zero, .zero]
  if k = 0 then B.keccakDuplex zeros zeros (.frame nxt) (.frame sp)
  if k = 1 then B.keccakDuplex (.frame (rate.extract 0 2)) zeros (.frame nxt) (.frame sp)
  if k = 2 then
    B.keccakDuplex (.frame (rate.extract 0 2)) (.frame (rate.extract 2 4)) (.frame nxt) (.frame sp)
  if k = 3 then
    B.atom (.const rate[6]! 0)
    B.atom (.const rate[7]! 0)
  if k = 3 ∨ k = 4 then
    B.keccakDuplex (.frame (rate.extract 0 2)) (.frame (rate.extract 2 4)) (.frame nxt) (.frame sp)
      (tail := some (.frame (rate.extract 4 8)))
  return nxt

/-- A function calling `fs_perm(sp, rate, k)` on a `StackBuf(spCells)` sponge (thirteen cells, a
previous output; five, a carried capacity) and a `StackBuf(8)` rate, for the comparison. -/
def fsPermAt (spCells k : Nat) : GFn where
  name := s!"fs_perm_at_{spCells}_{k}"
  arity := spCells + 8
  rets := 0
  body ps := do
    discard <| fsPerm (ps.take spCells) (ps.drop spCells) k
    return []

/-! ## `walk_window`: Merkle hash pairs in the frame -/

/-- `walk_window(n0, n1, path, lvl0: Const, width: Const, k: Const)`, inline: levels `lvl0` to
`lvl0 + width` of a Merkle path, whose order bits are `k`'s.

```
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
def walkWindow (n0 n1 : V) (path : List V) (lvl0 width k : Nat) : B (V × V) := do
  let mut n0 := n0
  let mut n1 := n1
  for r in List.range width do
    let lvl := lvl0 + r
    let nxt ← B.stackBuf 2
    let node : Operand := .words [.cell n0, .cell n1]
    if (k / 2 ^ r) % 2 = 0 then
      B.keccak node (.frame (path.extract (4 * lvl + 2) (4 * lvl + 4))) (.frame nxt)
    else
      B.keccak (.frame (path.extract (4 * lvl) (4 * lvl + 2))) node (.frame nxt)
    n0 := nxt[0]!
    n1 := nxt[1]!
  return (n0, n1)

/-- A function returning `walk_window(n0, n1, path, 0, width, k)` on a `StackBuf(4 * width)`
path, for the comparison. -/
def walkWindowAt (width k : Nat) : GFn where
  name := s!"walk_window_at_{width}_{k}"
  arity := 2 + 4 * width
  rets := 2
  body ps := do
    let (a, b) ← walkWindow ps[0]! ps[1]! (ps.drop 2) 0 width k
    return [.v a, .v b]

/-! ## `sp_word`: a list comprehension of `@inline` words -/

/-- `sp_word(pp, a0, a1, run, first: Const, stride: Const, j: Const)`, inline: word `j` of a
`T_l` input, which emits nothing.

```
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
def spWord (pp a0 a1 : V) (run : List V) (first stride j : Nat) : V :=
  if j / 3 ≠ 0 then run[first + stride * (j - 3)]!
  else if j = 2 then a1
  else if j = 1 then a0
  else pp

/-- The leaf hash ending `sp_wots`, in a function of its own for the comparison:

```
def sp_word_leaf(pp, a0, a1, walks: StackBuf(SP_V * CHAIN_STEPS)):
    leaf = StackBuf(1)
    keccak_cells([sp_word(pp, a0, a1, walks, CHAIN_STEPS - 1, CHAIN_STEPS, j) for j in unroll(0, SP_V + 3)], leaf)
    return leaf[0]
```
-/
def spWordLeaf : GFn where
  name := "sp_word_leaf"
  arity := 3 + SP_V * CHAIN_STEPS
  rets := 1
  body ps := do
    let leaf ← B.stackBuf 1
    let words := (List.range (SP_V + 3)).map fun j =>
      Msg.cell (spWord ps[0]! ps[1]! ps[2]! (ps.drop 3) (CHAIN_STEPS - 1) CHAIN_STEPS j)
    B.keccakCells (.words words) (.frame leaf)
    return [.v leaf[0]!]

/-! ## `pad_tail=1` and heap operands -/

/-- One level of `sp_path`, the padding set in the hinted children's run:

```
def pad_tail_at(pp, a0, node_at):
    kids = StackBuf(5)
    hint_witness(kids[0:2], "siblings")
    parent = StackBuf(1)
    keccak([pp, a0], [node_at, kids[0]], parent, tail=kids[1:5], len=80, pad_tail=1)
    return parent[0]
```
-/
def padTailAt : GFn where
  name := "pad_tail_at"
  arity := 3
  rets := 1
  body ps := do
    let kids ← B.stackBuf 5
    B.hint (.witness "siblings" (.stack (kids.take 2)))
    let parent ← B.stackBuf 1
    B.keccak (.words [.cell ps[0]!, .cell ps[1]!]) (.words [.cell ps[2]!, .cell kids[0]!])
      (.frame parent) (tail := some (.frame (kids.extract 1 5))) (len := some 80) (padTail := true)
    return [.v parent[0]!]

/-- The hash of `da_levels`' loop body, two heap nodes into a third:

```
def heap_pair(a, b):
    keccak(a[0:2], a[2:4], b[0:2])
    return
```
-/
def heapPair : GFn where
  name := "heap_pair"
  arity := 2
  rets := 0
  body ps := do
    B.keccak (.heap ps[0]! 0 2) (.heap ps[0]! 2 2) (.heap ps[1]! 0 2)
    return []

end
end LeanVM.Dsl.KeccakGuest
