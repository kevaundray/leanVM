/-
  LeanVM.Dsl.Keccak

  The Keccak builtins of the embedded guest language, `keccak`, its duplex step and
  `keccak_cells`, on the builder: what `Expand` emits for them, without a source text.
-/

module

public import LeanVM.Dsl.Builder

/-!
# Keccak

The zkDSL's builtins (`lower/builtins.rs`, `Expand.lowerKeccak`, `Expand.lowerKeccakCells`), as
builder actions emitting the same statements and trace:

* `B.keccak a b out tail len padTail`: the Keccak-256 of the first `len` bytes of `a ‖ b ‖ tail`,
  with `padTail` the padding set in the tail's own cells (`pad_tail=1`);
* `B.keccakDuplex a b out cap tail`: the duplex step in overwrite mode (`cap=`), the eight message
  cells over the five cells a previous output ends with. It takes no length and no `padTail`: the
  zkDSL rejects `cap=` with `len=` or `pad_tail=` (`fix(zkdsl_compiler): keccak cap= rejects
  pad_tail=`), here there is no way to write it;
* `B.keccakCells cells out state len final`: the Keccak-256 of the first `len` bytes of the cells,
  `136` bytes a `KECCAK`, continuing a 13-cell `state` if given; `final := false` absorbs the
  cells zero-extended to whole blocks, unpadded. A list comprehension over it is a Lean
  `List.mapM` building the cells.

One `KECCAK` atom per block of `136` bytes: block `k` is read from cell `17k/2` in the layout of
its parity, its output in the next block's layout, the last in the even one. The padding is XORed
into the message cells as constants or by one `XOR` with a constant cell (`xorByte`). The run
`[0x01, 0, 0, 0, 0]` is set at its first use in a scope (`padRun`, `Kind.padRun`, local to a block
as `B.block` restores it), its windows being the zero `tail` and `cap` runs and the tail of a
message ending at a cell boundary. A message cell is XORed into the previous output
(`spongeXor`), four message cells not already one run are copied into one (`spongeRun`,
`Kind.joined`), and the last block writes the one, two or thirteen cells its destination holds: a
heap destination through a fresh run of its size, copied out afterwards (`finish`).

An operand, a state or a destination is given as `Cells` (frame values, or a heap slice the
builtin reads or writes through fresh values) or, for a message operand, as words (`Msg`) the
caller has already computed, in the zkDSL's evaluation order: `a`, then `b`, then the tail. The
builder does not fail: the shapes the zkDSL rejects (an operand of the wrong length, a destination
of another size, a length ending before a word that is not zero) are elaborated as written, and
the checks against `Expand` (`LeanVM.Dsl.KeccakCheck`) are what pins the faithful ones.
-/

namespace LeanVM.Dsl

open LeanVM.Parameters LeanVM.Core LeanVM.Compiler

@[expose] public section

/-- One message cell (`Expand.SpongeCell`): a literal zero, a constant, or a value. -/
inductive Msg where
  | zero
  | const (c : E)
  | cell (v : V)
  deriving Inhabited

/-- A value as a message cell. -/
def Msg.of {τ : Ty} (x : Var τ) : Msg := .cell x.v

/-- Whether a message cell is a literal zero. -/
def Msg.isZero : Msg → Bool
  | .zero => true
  | _ => false

/-- A run of cells: frame values (a `StackBuf` or a slice of one), or `len` heap words from
`ptr·g^lo` (a `HeapBuf` slice). -/
inductive Cells where
  | frame (vs : List V)
  | heap (ptr : V) (lo len : Nat)
  deriving Inhabited

/-- A message operand: words already computed (a list literal, a literal `0` a known zero), or a
run of cells. -/
inductive Operand where
  | words (ws : List Msg)
  | cells (c : Cells)
  deriving Inhabited

/-- A frame run as an operand. -/
abbrev Operand.frame (vs : List V) : Operand := .cells (.frame vs)

/-- A heap slice as an operand. -/
abbrev Operand.heap (ptr : V) (lo len : Nat) : Operand := .cells (.heap ptr lo len)

namespace Keccak

/-- The last rate lane of a 64-byte message's one block, the padding's closing `0x80` byte
(`Expand.twoToOneClose`). -/
def twoToOneClose : E := word (0x80 * 2 ^ 56) 0

/-- `len` heap words from `ptr·g^lo` read into a fresh run, one `DEREF` each. -/
def loadRun (ptr : V) (lo len : Nat) : B (List V) := do
  let t ← B.freshRun len
  t.zipIdx.forM fun (d, k) => B.atom (.load d ptr (lo + k))
  return t

/-- The message cells of an operand (`Expand.keccakWords`): a heap slice is read into a fresh
run. -/
def resolve : Operand → B (List Msg)
  | .words ws => pure ws
  | .cells (.frame vs) => pure (vs.map .cell)
  | .cells (.heap ptr lo len) => do return (← loadRun ptr lo len).map .cell

/-- The padding values `[0x01, 0, 0, 0, 0]`: the message's first padding byte, then zeros. -/
def padValues : List E := [keccakPadValue, 0, 0, 0, 0]

/-- Set a fresh padding run and make it the scope's. -/
def setPadRun : B (List V) := do
  let o ← B.freshRun 5 .padRun
  o.zipIdx.forM fun (v, k) => do
    B.atom (.const v (padValues.getD k 0))
    B.poolConst (padValues.getD k 0)
  modify fun st => { st with keccakPad := some o }
  return o

/-- The run `[0x01, 0, 0, 0, 0]` every `keccak` of this scope shares, set at the first
(`Expand.keccakPadRun`). -/
def padRun : B (List V) := do
  if let some o := (← get).keccakPad then return o
  setPadRun

/-- What the zkDSL sets above a `match` whose arms are all `@inline` calls and which no earlier
`match` enters (`Expand.lowerMatch`): the padding run and a two-to-one hash's closing lane. -/
def inlineArms : B Unit := do
  discard padRun
  discard <| B.const twoToOneClose

/-- A value holding a message cell (`Expand.spongeCell`). -/
def spongeCell : Msg → B V
  | .zero => padRun >>= fun p => pure (p.getD 1 default)
  | .const c =>
      if c == keccakPadValue then padRun >>= fun p => pure (p.getD 0 default)
      else B.const c >>= fun w => pure w.v
  | .cell o => pure o

/-- `state + c`, into `dst` if given (`Expand.spongeXor`): a zero `c` is the state value itself,
or a copy of it into `dst`. -/
def spongeXor (state : V) (c : Msg) (dst : Option V) : B V := do
  match c with
  | .zero =>
      match dst with
      | some d => do
          B.atom (.copy d state)
          return d
      | none => return state
  | c => do
      let other ← spongeCell c
      let d ← match dst with
        | some d => pure d
        | none => B.fresh
      B.atom (.add d state other)
      return d

/-- Whether values are one run of consecutive cells. -/
def isRun : List V → Bool
  | a :: b :: vs => a.adjacent b && isRun (b :: vs)
  | _ => true

/-- The value a message cell is, if it is one. -/
def Msg.val? : Msg → Option V
  | .cell o => some o
  | _ => none

/-- Whether message cells are the padding's first byte, then zeros. -/
def padHead : List Msg → Bool
  | .const c :: rest => c == keccakPadValue && rest.all (·.isZero)
  | _ => false

/-- A fresh run holding the message cells: a constant set, a value copied. -/
def copyRun (cells : List Msg) : B (List V) := do
  let t ← B.freshRun cells.length .joined
  (cells.zip t).forM fun (c, d) =>
    match c with
    | .zero => B.atom (.const d 0)
    | .const v => B.atom (.const d v)
    | .cell o => B.atom (.copy d o)
  return t

/-- Four consecutive values holding the message cells (`Expand.spongeRun`): where they already
lie, a window of the padding run, or a fresh copy. -/
def spongeRun (cells : List Msg) : B (List V) :=
  let vals := cells.filterMap Msg.val?
  if vals.length == cells.length && isRun vals then pure vals
  else if cells.all (·.isZero) then padRun >>= fun p => pure (p.drop 1)
  else if padHead cells then padRun >>= fun p => pure (p.take 4)
  else copyRun cells

/-- The `m` and `tail` values of a `KECCAK` reading a block's first eight cells
(`Expand.keccakRate`): themselves from the zero state, or XORed into the values of the previous
output `st` they line up with. -/
def rate (block : List Msg) (st : Option (List V)) : B (List V × List V) := do
  let cell := fun (i : Nat) => block.getD i .zero
  match st with
  | none => do
      let m ← (List.range 4).mapM fun i => spongeCell (cell i)
      let tail ← spongeRun ((List.range 4).map fun j => cell (4 + j))
      return (m, tail)
  | some st => do
      let m ← (List.range 4).mapM fun i => spongeXor (st.getD i default) (cell i) none
      if (List.range 4).all fun j => (cell (4 + j)).isZero then
        return (m, (st.drop 4).take 4)
      let tail ← B.freshRun 4
      (List.range 4).forM fun j =>
        discard <| spongeXor (st.getD (4 + j) default) (cell (4 + j)) (some (tail.getD j default))
      return (m, tail)

/-- XOR the byte `v` into byte `pos` of the message cells (`Expand.xorByte`): into a constant, or
by one `XOR` with a constant cell. -/
def xorByte (cells : List Msg) (pos v : Nat) : B (List Msg) := do
  let i := pos / 16
  let w := byteWord pos v
  let c ← match cells.getD i .zero with
    | .zero => pure (Msg.const w)
    | .const c => pure (.const (c + w))
    | .cell o => do
        let k ← B.const w
        let dst ← B.fresh
        B.atom (.add dst o k.v)
        pure (.cell dst)
  return cells.set i c

/-- The `KECCAK` atoms of blocks `k`, `k + 1`, ... (`fuel` of them) of `blocks`, continuing
`state` (the zero state if `none`): block `k` read from cell `17k/2` in the layout of its parity,
XORed into the previous output, the last writing the cells `out`, each earlier one a fresh 13-cell
state the next one reads. -/
def absorbFrom (cells : List Msg) (blocks : Nat) (out : List V) :
    Nat → Option (List V) → Nat → B Unit
  | 0, _, _ => pure ()
  | fuel + 1, state, k => do
    let last := k + 1 == blocks
    let c ← if last then pure out else B.freshRun stateCells
    let block := (cells.drop (17 * k / 2)).take blockCells
    let r ← rate block state
    let b8 ← match state with
      | none => spongeCell (block.getD 8 .zero)
      | some st => spongeXor (st.getD 8 default) (block.getD 8 .zero) none
    let cap ← match state with
      | none => padRun >>= fun p => pure (p.drop 1)
      | some st => pure ((st.drop 9).take 4)
    B.atom (.keccak (r.1 ++ r.2 ++ [b8] ++ cap) c (k % 2 == 1) (!last && k % 2 == 0))
    absorbFrom cells blocks out fuel (some c) (k + 1)

/-- The `KECCAK` atoms absorbing `cells` into `state` (the zero state if `none`), the last writing
the cells `out` (`Expand.emitKeccakMessage`). With `finalLen` the message is the cells' first
`finalLen` bytes, padded, in `finalLen / rate + 1` blocks; without, the cells zero-extended to
whole blocks. `padded`: the cells past `finalLen` already hold the padding's first byte and
zeros. -/
def absorb (cells : List Msg) (finalLen : Option Nat) (state : Option (List V)) (out : List V)
    (padded : Bool) : B Unit := do
  let blocks := match finalLen with
    | some len => len / Protocol.KeccakHash.rate + 1
    | none => (16 * cells.length + Protocol.KeccakHash.rate - 1) / Protocol.KeccakHash.rate
  let read := 17 * (blocks - 1) / 2 + blockCells
  let cells := cells ++ List.replicate (read - cells.length) Msg.zero
  let cells ← match finalLen with
    | some len => do
        let cells ← if padded then pure cells
          else xorByte cells len Protocol.KeccakHash.padFirst.toNat
        xorByte cells (blocks * Protocol.KeccakHash.rate - 1) Protocol.KeccakHash.padLast.toNat
    | none => pure cells
  absorbFrom cells blocks out blocks state 0

/-- The cells a `keccak` writes in a frame destination: one or two cells in place, or the first
thirteen of a longer run. -/
def frameOut (cs : List V) : List V := if stateCells ≤ cs.length then cs.take stateCells else cs

/-- Where a `keccak` writes (`Expand.keccakOut`): a frame run's `frameOut` cells; a heap run's
cells through a fresh run of its size, with the heap slice to copy them out to. -/
def dest : Cells → B (List V × Option (V × Nat))
  | .frame cs => pure (frameOut cs, none)
  | .heap ptr lo len => do return (← B.freshRun len, some (ptr, lo))

/-- Copy what `dest` wrote out to a heap destination (`Expand.keccakFinish`). -/
def finish : List V × Option (V × Nat) → B Unit
  | (_, none) => pure ()
  | (state, some (ptr, lo)) => state.zipIdx.forM fun (s, k) => B.atom (.load s ptr (lo + k))

/-- `pad_tail=1` (`Expand.padTailInPlace`): the frame cells of the tail from byte `len` on set to
the padding, its first byte then zeros, so the message is read in place. -/
def padTail (tail : List Msg) (n len : Nat) : B Unit := do
  let tailCells := tail.filterMap fun | .cell o => some o | _ => none
  let past := len / 16
  let set := (tailCells.drop (past - 4)).take (n - past)
  set.zipIdx.forM fun (o, k) => B.atom (.const o (if k = 0 then keccakPadValue else 0))

/-- The capacity of a frame run: a 13-cell output's last five cells, else the run itself. -/
def capFrame (cs : List V) : List V := if cs.length == stateCells then cs.drop 8 else cs

/-- The last five cells of a previous output, the capacity a duplex step keeps (`cap=`): a
frame run's `capFrame`, or a heap slice's last five read into a fresh run. -/
def capRun : Cells → B (List V)
  | .frame cs => pure (capFrame cs)
  | .heap ptr lo len => loadRun ptr (lo + len - 5) 5

/-- The 13-cell state a `keccak_cells` continues (`state=`): a frame run's first thirteen, or a
heap slice read into a fresh run. -/
def stateRun : Cells → B (List V)
  | .frame cs => pure (cs.take stateCells)
  | .heap ptr lo _ => loadRun ptr lo stateCells

end Keccak

namespace B

open Keccak

/-- `keccak(a, b, out, tail=, len=, pad_tail=)` (`Expand.lowerKeccak` without `cap=`): the
Keccak-256 of the first `len` bytes of `a ‖ b ‖ tail` (all of them by default) into `out`; with
`padTail`, the padding set in the tail's frame cells from byte `len` on. -/
def keccak (a b : Operand) (out : Cells) (tail : Option Operand := none) (len : Option Nat := none)
    (padTail : Bool := false) : B Unit := do
  let a ← resolve a
  let b ← resolve b
  let t ← match tail with
    | some t => resolve t
    | none => pure []
  let cells := a ++ b ++ t
  let len := len.getD (16 * cells.length)
  if padTail then Keccak.padTail t cells.length len
  let o ← dest out
  absorb cells (some len) none o.1 padTail
  Keccak.finish o

/-- `keccak(a, b, out, tail=, cap=)` (`Expand.lowerKeccak` with `cap=`): the duplex step in
overwrite mode, the message cells `a ‖ b ‖ tail` (zero past them) over the capacity `cap`, one
`KECCAK` into `out`. -/
def keccakDuplex (a b : Operand) (out : Cells) (cap : Cells) (tail : Option Operand := none) :
    B Unit := do
  let a ← resolve a
  let b ← resolve b
  let t ← match tail with
    | some t => resolve t
    | none => pure []
  let cells := a ++ b ++ t
  let c ← capRun cap
  let cells := cells ++ List.replicate (8 - cells.length) Msg.zero
  let o ← dest out
  let (m, tl) ← rate cells none
  B.atom (.keccak (m ++ tl ++ c) o.1 false false)
  Keccak.finish o

/-- `keccak_cells(cells, out, state=, len=, final=)` (`Expand.lowerKeccakCells`): the Keccak-256
of the first `len` bytes of the cells (all of them by default) into `out`, continuing `state` if
given; `final := false` absorbs the cells zero-extended to whole blocks, unpadded. -/
def keccakCells (cells : Operand) (out : Cells) (state : Option Cells := none)
    (len : Option Nat := none) (final : Bool := true) : B Unit := do
  let cs ← resolve cells
  let finalLen := if final then some (len.getD (16 * cs.length)) else none
  let st ← match state with
    | some s => some <$> stateRun s
    | none => pure none
  let o ← dest out
  absorb cs finalLen st o.1 false
  Keccak.finish o

end B

end
end LeanVM.Dsl
