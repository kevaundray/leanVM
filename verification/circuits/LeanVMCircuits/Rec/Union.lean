module

public import LeanVMCircuits.Rec.Builder

@[expose] public section

/-!
The claim union's pools (`rec::tree::union::pool_rows`) as a builder program.

A pool is chunks of `chunk` items, each item one compression of a claim set's written form: its kind bits (`b0`,
`b1`, `pair`), its block of eight words, the counter word they give, and the chaining value, the parameter IV at a
run's start. Runs start at a pool's first item and at a chunk's first item whose begin bit is set; a one-hot over the
runs moves on at each begin, and a run's end item holds the digest of its run.

`Model.poolRows` is the part of `pool_rows` before its bits are packed, call for call: `CheckBind` replays the calls a
dump marks as a pool and checks they build what `poolRows` builds from the same state. The packing is ordinary traced
calls.
-/

namespace LeanVMCircuits.Rec.Model

/-- `union::CHUNK`. -/
def chunk : ℕ := 32

/-- `multiset::code`'s counter bits. -/
def codeMember : ℕ := 2
def codeEnd : ℕ := 4
def codePair : ℕ := 8

/-- Whether an item starts a run: never, always (the pool's first), or if a begin bit is set. -/
inductive Start where
  | no
  | yes
  | ifBit (bit : ℕ)
  deriving Repr, DecidableEq, Inhabited

/-- One item's wires: its block, kind bits, the forms the products read, its run start, selection bits and output. -/
structure PoolItem where
  m : List ℕ
  b0 : ℕ
  b1 : ℕ
  pair : ℕ
  e1 : ℕ
  isMembers : ℕ
  isPair : ℕ
  notHeader : ℕ
  start : Start
  select : Option (ℕ × ℕ)
  out : ℕ
  deriving Repr, Inhabited

/-- A pool's wires: its items, and its begin bits by chunk from the second (none for a pool of one run). -/
structure Pool where
  items : Array PoolItem := #[]
  begins : Array ℕ := #[]
  deriving Repr, Inhabited

/-- The carried state of the loop over items: the run one-hot, and the previous item's `e1`, halves and output. -/
structure PoolLoop where
  current : List ℕ
  previous : Option (ℕ × ℕ × ℕ × ℕ) := none
  pool : Pool := {}

/-- One item of a pool, `pool_rows`' inner loop body. -/
def poolItem (zero one kZero ivLo ivHi cMember cEnd cPair cFinal : ℕ) (expected : ℕ × ℕ) (i k : ℕ)
    (begin : Option ℕ) (selecting : Bool) (st : PoolLoop) : M PoolLoop := do
  let b0 ← wire
  let b1 ← wire
  let pair ← wire
  let e0 ← mulKAdd one b0 zero
  let e1 ← mulKAdd one b1 zero
  let isPad ← mulKAdd e0 b1 zero
  let isMembers ← add e0 isPad
  let isEnd ← add e1 isPad
  let either ← add e0 e1
  let notHeader ← add either isPad
  let ePair ← mulKAdd one pair zero
  let isPair ← mulKAdd isMembers pair zero
  union ePair isPair
  let start : Start := if i = 0 then .yes else match k, begin with
    | 0, some bit => .ifBit bit
    | _, _ => .no
  let startE ← match start, st.previous with
    | .yes, _ => do union isPad zero; pure one
    | .ifBit bit, some (ended, _, _, _) => do
      let eBit ← mulKAdd one bit zero
      let afterEnd ← mul ended eBit
      union afterEnd eBit
      let pad ← add ended eBit
      union isPad pad
      pure eBit
    | _, some (ended, _, _, _) => do union isPad ended; pure zero
    | _, none => pure zero
  let t ← mulKAdd cMember b0 startE
  let t ← mulKAdd cEnd b1 t
  let t ← mulKAdd cPair pair t
  let t ← mulAdd cFinal isEnd t
  let tk ← eToK t
  let tf ← kToD (tk.getD 0 0) (tk.getD 1 0) kZero kZero
  let h ← match start, st.previous with
    | .yes, _ => dConst paramIVLimbs
    | .ifBit bit, some (_, lo, hi, _) => do
      let dLo ← add lo ivLo
      let dHi ← add hi ivHi
      let lo ← mulKAdd dLo bit lo
      let hi ← mulKAdd dHi bit hi
      halvesToD lo hi
    | _, some (_, _, _, out) => pure out
    | _, none => pure 0
  let m ← (List.range 8).mapM fun _ => wire
  let out ← hashBlock h m tf
  let oh ← dToHalves out
  for (o, e) in [(oh.getD 0 0, expected.1), (oh.getD 1 0, expected.2)] do
    let diff ← add o e
    let held ← mul isEnd diff
    union held zero
  let select ← if selecting then do
      let s0 ← wire
      let s1 ← wire
      pure (some (s0, s1))
    else pure none
  let item : PoolItem := { m, b0, b1, pair, e1, isMembers, isPair, notHeader, start, select, out }
  pure { st with
    previous := some (e1, oh.getD 0 0, oh.getD 1 0, out)
    pool := { st.pool with items := st.pool.items.push item } }

/-- The run one-hot moved on at a begin bit: run `r` takes run `r - 1`'s place where the bit is set. -/
def moveOn (zero bit : ℕ) (current : List ℕ) : M (List ℕ) :=
  (List.range current.length).mapM fun r => do
    let moved := if r = 0 then zero else current.getD (r - 1) 0
    let diff ← add moved (current.getD r 0)
    mulKAdd diff bit (current.getD r 0)

/-- `pool_rows` before its bits are packed: a pool of `chunks` chunks reading runs whose digests are `digests`. -/
def poolRows (chunks : ℕ) (selecting : Bool) (digests : List ℕ) : M Pool := do
  let runs := digests.length
  let zero ← Model.zero
  let one ← Model.one
  let kZero ← kConst 0
  let iv := paramIVLimbs
  let ivLo ← eConst (iv.getD 0 0) (iv.getD 1 0) 0
  let ivHi ← eConst (iv.getD 2 0) (iv.getD 3 0) 0
  let cMember ← eConst codeMember 0 0
  let cEnd ← eConst codeEnd 0 0
  let cPair ← eConst codePair 0 0
  let cFinal ← eConst 0 final 0
  let halves ← digests.mapM dToHalves
  let mut st : PoolLoop := { current := (List.range runs).map fun r => if r = 0 then one else zero }
  for j in List.range chunks do
    let begin ← if 0 < j ∧ 1 < runs then do
        let bit ← wire
        let current ← moveOn zero bit st.current
        st := { st with current, pool := { st.pool with begins := st.pool.begins.push bit } }
        pure (some bit)
      else pure none
    let expected ← if runs = 1 then pure ((halves.getD 0 []).getD 0 0, (halves.getD 0 []).getD 1 0) else do
      let mut lo := zero
      for r in List.range runs do
        lo ← mulAdd (st.current.getD r 0) ((halves.getD r []).getD 0 0) lo
      let mut hi := zero
      for r in List.range runs do
        hi ← mulAdd (st.current.getD r 0) ((halves.getD r []).getD 1 0) hi
      pure (lo, hi)
    for k in List.range chunk do
      st ← poolItem zero one kZero ivLo ivHi cMember cEnd cPair cFinal expected (j * chunk + k) k begin selecting st
  -- The pool ends after an end or padding, in its last run.
  let ended := match st.previous with
    | some (e, _, _, _) => e
    | none => 0
  union ended one
  for (c, r) in st.current.zipIdx do
    eqConstE c (if r + 1 = runs then 1 else 0) 0 0
  pure st.pool

/-- `union::product`: the product over a pool's claims of `1 + s · valid · (X + 1 + fp)` at the point whose `X + 1` is
`x1` and whose sixteen tuple weights are `w`, `s` a slot's selection bit or one. -/
def product (items : Array PoolItem) (x1 : ℕ) (w : List ℕ) : M ℕ := do
  let zero ← Model.zero
  let one ← Model.one
  let mut label := zero
  let mut acc := one
  for item in items do
    label ← match item.start with
      | .yes => pure zero
      | .ifBit bit => mulKAdd label bit label
      | .no => pure label
    let mut header := w.getD 0 0
    for j in List.range 6 do
      header ← mulKAdd (w.getD (1 + j) 0) (item.m.getD j 0) header
    let diff ← add header label
    label ← mulAdd item.notHeader diff header
    for (valid, slot) in [item.isMembers, item.isPair].zipIdx do
      let mut fp := label
      for j in List.range 4 do
        fp ← mulKAdd (w.getD (7 + j) 0) (item.m.getD (4 * slot + j) 0) fp
      let term ← add x1 fp
      let factor ← match item.select with
        | some (s0, s1) => do
          let held ← mul valid term
          mulKAdd held (if slot = 0 then s0 else s1) one
        | none => mulAdd valid term one
      acc ← mul acc factor
  pure acc

end LeanVMCircuits.Rec.Model
