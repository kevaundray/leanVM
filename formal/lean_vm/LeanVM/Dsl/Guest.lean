/-
  LeanVM.Dsl.Guest

  Guest functions ported to the embedded language: `selector_run_nibbles`, `is_child`,
  `eq_prefix_chain` and its `eq_prefix_run` family, `da_column_offsets`, each as the zkDSL compiles
  it today, and the improved forms the embedding allows.
-/

module

public import LeanVM.Dsl.Builder
public import LeanVM.Guest.Program.Config

/-!
# Ported guest functions

Each function is written once, as a Lean definition, with the zkDSL source it replaces in its docstring. Compile-time values are Lean's: `Const` parameters are arguments (`eqPrefixRun n`), `unroll` is `List.forM` over a range, `@inline` is a Lean function (`isChild`). The constants are the guest's (`LeanVM.Guest.Program`, `Guest/Program/Config.lean`).

The forms marked *improved* change the code where the zkDSL could not say what the program
means: a dispatch needs no dummy return, and a loop whose bound is a compile-time power of `g` is
entered unconditionally with a constant exit.
-/

namespace LeanVM.Dsl.Guest

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## Configuration -/

def LOG_CELL_SYMBOLS : Nat := LeanVM.Guest.Program.LOG_CELL_SYMBOLS
def DA_BLOCK_BITS : Nat := LeanVM.Guest.Program.DA_BLOCK_BITS
def DA_CELLS : Nat := LeanVM.Guest.Program.DA_CELLS
def EQ_CHAIN_ARMS : Nat := LeanVM.Guest.Program.EQ_CHAIN_ARMS

/-- `DA_VHAT_COLUMN[i]`. -/
def daVhatColumn (i : Nat) : E :=
  let c := LeanVM.Guest.Program.DA_VHAT_COLUMN.getD i (0, 0)
  word c.1 c.2

/-! ## `selector_run_nibbles` -/

/-- The factor `1 + b·(g^(2^t) + 1)` of a bit `b` of weight `2^t`: `g^(2^t)` at `b = 1`, else `1`. -/
def bitFactor (b : Var .bit) (t : Nat) : B Word := do
  let one ← B.const 1
  let c ← B.const (gen ^ 2 ^ t + 1)
  let m ← B.mul b c
  B.add one m

/-- The product of the factors of `bs` from weight `2^t` on, times `acc`. -/
def bitsProdFrom (acc : Word) : List (Var .bit) → Nat → B Word
  | [], _ => pure acc
  | b :: bs, t => do
      let f ← bitFactor b t
      let acc' ← B.mul acc f
      bitsProdFrom acc' bs (t + 1)

/-- `g` to the integer of the bits `bs`, low first (`g_power_of_word`'s product). -/
def gpowOfBits : List (Var .bit) → B Word
  | [] => B.const 1
  | b :: bs => do
      let f ← bitFactor b 0
      bitsProdFrom f bs 1

/-- `selector_run_nibbles(len_g)`:

```
nb = StackBuf(6)
hint_decompose_bits_exponent(nb, len_g, 6)
for k in unroll(0, 6):
    b = nb[k]
    nb[k] = b * b
r_g = (1 + nb[0] * (1 + GEN)) * (1 + nb[1] * (1 + GEN ** 2))
q_g = GEN ** 0
for k in unroll(2, 6):
    q_g *= 1 + nb[k] * (1 + GEN ** (2 ** (k - 2)))
q4 = q_g ** 4
assert q4 * r_g == len_g
return q_g
```
-/
def selectorRunNibbles : GFn where
  name := "selector_run_nibbles"
  arity := 1
  rets := 1
  body ps := do
    let len : Word := ⟨ps.head!⟩
    let nb ← B.hintBitsExp len 6
    nb.forM fun h => B.assertBit h >>= fun _ => pure ()
    let bs : List (Var .bit) := nb.map fun h => ⟨h.v⟩
    let r ← gpowOfBits (bs.take 2)
    let q ← gpowOfBits (bs.drop 2)
    let q2 ← B.mul q q
    let q4 ← B.mul q2 q2
    let t ← B.mul q4 r
    B.assertEq t len
    return [.v q.v]

/-! ## `is_child`, an `@inline` function -/

/-- `is_child(node, kids, k: Const, bit)`, inline: `node` is `kids[k + bit]`, one product stored
where the left child's difference already is.

```
check = StackBuf(1)
check[0] = node + kids[k]
check[0] = bit * (kids[k] + kids[k + 1])
```
-/
def isChild (node : Word) (kids : List V) (k : Nat) (bit : Var .bit) : B Unit := do
  let kk : Word := ⟨kids[k]!⟩
  let kk1 : Word := ⟨kids[k + 1]!⟩
  let check ← B.addCell node kk
  let s ← B.add kk kk1
  B.mulInto check bit s

/-- A function calling `is_child(node, kids, 0, bit)` on a two-cell `kids`, for the comparison. -/
def isChildAt0 : GFn where
  name := "is_child_at0"
  arity := 4
  rets := 0
  body ps := do
    isChild ⟨ps[0]!⟩ [ps[1]!, ps[2]!] 0 ⟨ps[3]!⟩
    return []

/-! ## `eq_prefix_chain` and the `eq_prefix_run` family: `Const`, `match` -/

/-- `eq_prefix_run(chain, seed, a, b1, n: Const)`, one function per `n`:

```
chain[GEN ** 0] = seed
v = seed
for k in unroll(0, n):
    v = v * (a[GEN ** k] + b1[GEN ** k])
    chain[GEN ** (k + 1)] = v
return 0
```
-/
def eqPrefixRunBody (n : Nat) (chain seed a b1 : Word) : B Unit := do
  B.store chain 0 seed
  discard <| (List.range n).foldlM (init := seed) fun v k => do
    let ak ← B.load a k
    let bk ← B.load b1 k
    let s ← B.add ak bk
    let v' ← B.mul v s
    B.store chain (k + 1) v'
    return v'

def eqPrefixRun (n : Nat) : GFn where
  name := s!"eq_prefix_run__L{n}"
  arity := 4
  rets := 1
  body ps := do
    eqPrefixRunBody n ⟨ps[0]!⟩ ⟨ps[1]!⟩ ⟨ps[2]!⟩ ⟨ps[3]!⟩
    return [.c 0]

/-- `eq_prefix_chain(chain, seed, a, b1, count_g)`:

```
assert log(count_g) < EQ_CHAIN_ARMS
done = match(log(count_g), range(0, EQ_CHAIN_ARMS),
             lambda n: eq_prefix_run(chain, seed, a, b1, n))
```
-/
def eqPrefixChain : GFn where
  name := "eq_prefix_chain"
  arity := 5
  rets := 0
  body ps := do
    let sel ← B.rangeCheck (⟨ps[4]!⟩ : Word) EQ_CHAIN_ARMS
    discard <| B.dispatch sel ((List.range EQ_CHAIN_ARMS).map fun n => (eqPrefixRun n).name)
      (ps.take 4) 1
    return []

/-- *Improved* `eq_prefix_run`: no dummy return, which only the zkDSL's `match` needed. -/
def eqPrefixRun' (n : Nat) : GFn where
  name := s!"eq_prefix_run__L{n}"
  arity := 4
  rets := 0
  body ps := do
    eqPrefixRunBody n ⟨ps[0]!⟩ ⟨ps[1]!⟩ ⟨ps[2]!⟩ ⟨ps[3]!⟩
    return []

/-- *Improved* `eq_prefix_chain`: the dispatch returns nothing. -/
def eqPrefixChain' : GFn where
  name := "eq_prefix_chain"
  arity := 5
  rets := 0
  body ps := do
    let sel ← B.rangeCheck (⟨ps[4]!⟩ : Word) EQ_CHAIN_ARMS
    discard <| B.dispatch sel ((List.range EQ_CHAIN_ARMS).map fun n => (eqPrefixRun' n).name)
      (ps.take 4) 0
    return []

/-! ## `da_column_offsets`: heap buffers, a runtime `mul_range` loop, a constant array -/

/-- One iteration of the doubling loop at bit `b`: `src = offsets·xh^L`, `dst = src·g^(L·2^b)`,
`dst[j] = src[j] + steps[j]`. -/
def daDouble (b : Nat) (xh : Word) (offsets steps : Word) : B Unit := do
  let x7 ← B.pow xh LOG_CELL_SYMBOLS
  let src ← B.mul offsets x7
  (List.range LOG_CELL_SYMBOLS).forM fun j => do
    let sj ← B.load src j
    let tj ← B.load steps j
    let d ← B.add sj tj
    B.store src (LOG_CELL_SYMBOLS * 2 ^ b + j) d

/-- The steps of bit `b`: `steps[j] = zs[j]·DA_VHAT_COLUMN[L·b + j]`. -/
def daSteps (b : Nat) (zs : Word) : B Word := do
  let steps ← B.heapBuf LOG_CELL_SYMBOLS
  (List.range LOG_CELL_SYMBOLS).forM fun j => do
    let zj ← B.load zs j
    let c ← B.const (daVhatColumn (LOG_CELL_SYMBOLS * b + j))
    let p ← B.mul zj c
    B.store steps j p
  return steps

/-- The zeroed first row of `offsets`. -/
def daZeroRow (offsets : Word) : B Unit :=
  (List.range LOG_CELL_SYMBOLS).forM fun j => do
    let z ← B.const 0
    B.store offsets j z

/-- `da_column_offsets(zs)`:

```
offsets = HeapBuf(LOG_CELL_SYMBOLS * DA_CELLS)
for j in unroll(0, LOG_CELL_SYMBOLS):
    offsets[GEN ** j] = 0
for b in unroll(0, DA_BLOCK_BITS):
    steps = HeapBuf(LOG_CELL_SYMBOLS)
    for j in unroll(0, LOG_CELL_SYMBOLS):
        steps[GEN ** j] = zs[GEN ** j] * DA_VHAT_COLUMN[LOG_CELL_SYMBOLS * b + j]
    for xh in mul_range(1, GEN ** (2 ** b)):
        src = offsets * xh ** LOG_CELL_SYMBOLS
        dst = src * GEN ** (LOG_CELL_SYMBOLS * 2 ** b)
        for j in unroll(0, LOG_CELL_SYMBOLS):
            dst[GEN ** j] = src[GEN ** j] + steps[GEN ** j]
return offsets
```

As the zkDSL lowers it: the bound `GEN ** (2 ** b)` is no parse-time integer, so the loop takes it
at run time (`B.loopRt`).
-/
def daColumnOffsets : GFn where
  name := "da_column_offsets"
  arity := 1
  rets := 1
  body ps := do
    let zs : Word := ⟨ps.head!⟩
    let offsets ← B.heapBuf (LOG_CELL_SYMBOLS * DA_CELLS)
    daZeroRow offsets
    (List.range DA_BLOCK_BITS).forM fun b => do
      let steps ← daSteps b zs
      B.loopRt 0 (B.gconst (2 ^ b)) [offsets.v, steps.v] fun xh caps =>
        daDouble b xh ⟨caps[0]!⟩ ⟨caps[1]!⟩
    return [.v offsets.v]

/-- *Improved* `da_column_offsets`: the bound `g^(2^b)` is a Lean constant, so each loop is entered
unconditionally, exits at a constant, and takes no bound parameter (`B.loopConst`). -/
def daColumnOffsets' : GFn where
  name := "da_column_offsets"
  arity := 1
  rets := 1
  body ps := do
    let zs : Word := ⟨ps.head!⟩
    let offsets ← B.heapBuf (LOG_CELL_SYMBOLS * DA_CELLS)
    daZeroRow offsets
    (List.range DA_BLOCK_BITS).forM fun b => do
      let steps ← daSteps b zs
      B.loopConst 0 (2 ^ b) [offsets.v, steps.v] fun xh caps =>
        daDouble b xh.word ⟨caps[0]!⟩ ⟨caps[1]!⟩
    return [.v offsets.v]

end
end LeanVM.Dsl.Guest
