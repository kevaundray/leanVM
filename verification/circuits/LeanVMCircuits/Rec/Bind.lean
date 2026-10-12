module

public import LeanVMCircuits.Rec.Verdict
public import LeanVMCircuits.Rec.Dump

@[expose] public section

/-!
Transcript binding of a recursion circuit.

A challenge is a squeezed word of a transcript in rows: the output of a `leaf_block` at the duplex's output tag,
whose chaining value is the end of a run of absorb blocks from a constant seed. A wire is *bound* by a squeeze when
it is determined by the words absorbed before it: it is one of them or a constant, or a determination rule makes it
from bound wires. Each rule carries its justification (`Just`): a row's forms, a split, a constant mux bit, a
compression at a constant final word, an equality that is not a test, an inverse, collision resistance of the
compression and of the output window, or a marked union product (`Bind.unionsValid`).

A *test* is an equality made from outside the builder's methods (`eq_e`, `eq_k`, `eq_e_const`, `eq_k_const`) that
reads a wire depending on a challenge. Tests do not bind. The check: every test's wires are bound by one transcript,
so the test is a function of the words that transcript absorbs. The worklist records its firings per transcript, and
the verdict is `Cert.accepts` of that record (`checkbind_sound`), not the worklist's own. A hinted wire a test reads
that no transcript absorbs, and no rule determines from absorbed words, fails the check: the prover may choose it
after the challenge.
-/

namespace LeanVMCircuits.Rec.Bind

open Model

/-- How an equality counts. -/
inductive EqKind where
  /-- `eq_d`: two digests, binding. -/
  | digest
  /-- From outside the methods, between field elements: a test when it reads a challenge. -/
  | field
  /-- Inside a method (`inv`'s product held to one). -/
  | method
  deriving Repr, DecidableEq, Inhabited

/-- A marked block being replayed: a pool or a product, its calls from its start. -/
inductive Pending where
  | pool (pc : PoolCert)
  | product (qc : ProdCert)

/-- A replay of a dump's calls through the model, with what the analysis needs of each call. -/
structure Replay where
  state : State := {}
  calls : Array Call := #[]
  outs : Array (List ℕ) := #[]
  /-- The call that made each wire. -/
  maker : Array ℕ := #[]
  /-- Each equality's kind, in `State.unions` order. -/
  eqKind : Array EqKind := #[]
  /-- The call that made each equality. -/
  eqCall : Array ℕ := #[]
  pending : Option Pending := none
  pools : Array PoolCert := #[]
  prods : Array ProdCert := #[]
  /-- Each `inv` call's `EMUL` row and equality. -/
  invs : Array (ℕ × ℕ) := #[]

/-- A pool's chunk and item cursors and closing check, by `pool_rows`' call counts from its start: where
`PoolCert.ok` checks its calls. -/
def PoolCert.layout (pc : PoolCert) : PoolCert := Id.run do
  let runs := pc.digests.length
  let mut pos := pc.start + 9 + runs
  let mut chunkAt := #[]
  let mut itemAt := #[]
  for j in [0:pc.chunks] do
    chunkAt := chunkAt.push pos
    pos := pos + (if pc.begins j then 1 + 2 * runs else 0) + (if 1 < runs then 2 * runs else 0)
    for k in [0:chunk] do
      itemAt := itemAt.push pos
      let st : Start := if j * chunk + k = 0 then .yes else if k = 0 ∧ 1 < runs then .ifBit 0 else .no
      pos := pos + 13 + sLen st + 6 + hLen st + 16 + (if pc.selecting then 2 else 0)
  return { pc with chunkAt, itemAt, endAt := pos }

/-- A product's item cursors, by `product`'s call counts from its start. -/
def ProdCert.layout (qc : ProdCert) (pc : PoolCert) : ProdCert := Id.run do
  let len := if pc.selecting then 8 else 7
  let mut pos := qc.start + 2
  let mut itemAt := #[]
  for i in [0:pc.n] do
    itemAt := itemAt.push pos
    pos := pos + (if i ≠ 0 ∧ i % chunk = 0 ∧ 1 < pc.runs then 1 else 0) + 8 + 2 * len
  return { qc with itemAt }

/-- Open or close a marked block: a pool's or a product's certificate, its cursors laid out from its first call. -/
def Replay.mark (r : Replay) (line : Dump.Line) : Except String Replay :=
  match line, r.pending with
  | .call _, _ => .ok r
  | .pool chunks selecting digests, none =>
    .ok { r with
      pending := some (.pool { start := r.calls.size, chunks, selecting, digests, chunkAt := #[], itemAt := #[],
                               endAt := 0, packs := [] }) }
  | .product first x1 weights, none =>
    match r.pools.findIdx? fun pc => o r.outs (pc.blk r.outs 0) = first with
    | none => .error s!"a product of no pool marked before it: {first}"
    | some i =>
      .ok { r with pending := some (.product { pool := i, start := r.calls.size, x1, weights, itemAt := #[] }) }
  | .stop, some (.pool pc) =>
    -- The pool's `pack` calls follow its end mark.
    .ok { r with pending := none, pools := r.pools.push { pc.layout with packs := [r.calls.size] } }
  | .stop, some (.product qc) =>
    .ok { r with pending := none, prods := r.prods.push (qc.layout (r.pools.getD qc.pool default)) }
  | .stop, none => .error "an end mark without a start"
  | _, some _ => .error "a mark inside a marked block"

def eqKindOf : Call → EqKind
  | .eqD .. => .digest
  | .eqE .. | .eqK .. | .eqConstE .. | .eqConstK .. => .field
  | _ => .method

def Replay.step (r : Replay) (c : Call) : Replay := Id.run do
  -- Take the fields apart first, so that each array is updated in place.
  let { state, calls, outs, maker, eqKind, eqCall, pending, pools, prods, invs } := r
  let (n0, u0) := (state.next, state.unions.size)
  let (out, s') := c.exec.run state
  let i := calls.size
  let mut maker := maker
  for _ in [n0:s'.next] do
    maker := maker.push i
  let mut eqKind := eqKind
  let mut eqCall := eqCall
  for _ in [u0:s'.unions.size] do
    eqKind := eqKind.push (eqKindOf c)
    eqCall := eqCall.push i
  let invs := match c with
    | .inv _ => if s'.emul.size = state.emul.size + 1 ∧ s'.unions.size = u0 + 1 then invs.push (state.emul.size, u0)
      else invs
    | _ => invs
  return ⟨s', calls.push c, outs.push out, maker, eqKind, eqCall, pending, pools, prods, invs⟩

/-- The counter word's role, its top byte. -/
def role (t : ℕ) : ℕ := t / 2 ^ 56

/-- A transcript block: an absorb block's chaining values and words, or a squeeze, by call. -/
structure Block where
  call : ℕ
  cvIn : ℕ
  cvOut : ℕ
  words : List ℕ
  squeeze : Bool
  deriving Repr, Inhabited

def blocks (r : Replay) : Array Block := Id.run do
  let mut out := #[]
  for i in [0:r.calls.size] do
    match r.calls.getD i .freeE, r.outs.getD i [] with
    | Call.leafBlock h m t _, [o] =>
      if role t = 6 then out := out.push { call := i, cvIn := h, cvOut := o, words := [], squeeze := true }
      else if 2 ≤ role t ∧ role t ≤ 5 then out := out.push { call := i, cvIn := h, cvOut := o, words := m, squeeze := false }
    | _, _ => pure ()
  return out

/-- Every transcript: its path of blocks from a seed to a chaining value no absorb block extends. -/
def transcripts (bs : Array Block) : Array (Array Block) := Id.run do
  let mut absorbOf : Std.HashMap ℕ ℕ := {}
  let mut extended : Std.HashSet ℕ := {}
  let mut squeezesAt : Std.HashMap ℕ (Array Block) := {}
  for i in [0:bs.size] do
    let b := bs[i]!
    if b.squeeze then
      squeezesAt := squeezesAt.insert b.cvIn ((squeezesAt.getD b.cvIn #[]).push b)
    else
      absorbOf := absorbOf.insert b.cvOut i
      extended := extended.insert b.cvIn
  -- The ends: chaining values of absorb outputs or squeeze inputs that nothing extends.
  let mut ends : Array ℕ := #[]
  let mut seen : Std.HashSet ℕ := {}
  for b in bs do
    let cv := if b.squeeze then b.cvIn else b.cvOut
    if !extended.contains cv && !seen.contains cv then
      ends := ends.push cv
      seen := seen.insert cv
  let mut out := #[]
  for e in ends do
    -- Walk back to the seed, collecting chaining values.
    let mut cvs : Array ℕ := #[e]
    let mut cv := e
    let mut fuel := bs.size + 1
    while fuel > 0 do
      fuel := fuel - 1
      match absorbOf[cv]? with
      | some j => cv := bs[j]!.cvIn; cvs := cvs.push cv
      | none => fuel := 0
    let mut path : Array Block := #[]
    for c in cvs.reverse do
      match absorbOf[c]? with
      | some j => path := path.push bs[j]!
      | none => pure ()
      for sq in squeezesAt.getD c #[] do
        path := path.push sq
    if path.any (·.squeeze) then out := out.push path
  return out

/-- The rules of a replayed circuit, and the rows' form rules' count. -/
structure Analysis where
  nodes : ℕ
  rules : Rules Just
  /-- Rules up to here are the rows' forms, splits, muxes and compressions; the hint search walks back through
  them. -/
  nFunction : ℕ

/-- A wire's four limb nodes, as an array. -/
def limbsA (w : ℕ) : Array ℕ := (limbs4 w).toArray

/-- A table's form rules, the same for each row: each conclusion slot limb with the slot limbs it is read off. A
slot limb that is a column gives every other limb that is the same column, and is given by it; any other limb is its
form of the columns it reads, each read off the first slot limb that is that column. -/
def formPlan (t : Table) : Array (ℕ × ℕ × List (ℕ × ℕ)) := Id.run do
  let forms := formsOf t
  let mut first : Std.HashMap ℕ (ℕ × ℕ) := {}
  let mut plan := #[]
  for (slot, s) in forms.zipIdx do
    for (f, i) in slot.zipIdx do
      match f.colOf with
      | some j =>
        match first[j]? with
        | none => first := first.insert j (s, i)
        | some src => plan := (plan.push (s, i, [src])).push (src.1, src.2, [(s, i)])
      | none => pure ()
  for (slot, s) in forms.zipIdx do
    for (f, i) in slot.zipIdx do
      if f.colOf.isNone then
        let srcs := f.cols.filterMap (first[·]?)
        if srcs.length = f.cols.length then plan := plan.push (s, i, srcs)
  return plan

/-- The rows' rules, each with its justification, then collision resistance. `invs` are the `EMUL` rows and
equalities of `inv` calls. -/
def rowRules (s : State) (invs : Array (ℕ × ℕ)) : Analysis := Id.run do
  let mut r : Rules Just := {}
  for t in [Table.emul, .exk, .cast, .split, .hash] do
    let plan := formPlan t
    let rows := rowsOf s t
    for k in [0:rows.size] do
      let row := rows[k]!
      for (sl, i, srcs) in plan do
        r := r.push (.form t k sl i srcs) (srcs.map (colNode row)).toArray #[limb (row.getD sl 0) i]
  -- Constants by wire: their public row and value.
  let mut consts : Std.HashMap ℕ (ℕ × Limbs) := {}
  for p in [0:s.pub.size] do
    match s.pub[p]! with
    | (w, .const v) =>
      consts := consts.insert w (p, v)
      for i in [0:4] do
        r := r.push (.pubConst p i) #[] #[limb w i]
    | _ => pure ()
  -- The word column is the sum of its bit columns' monomials, each bit 0 or 1: either side gives the other.
  for k in [0:s.split.size] do
    let row := s.split[k]!
    let bits := (splitBitNodes row).toArray
    r := (r.push (.splitWord k) bits #[limb (row.getD 0 0) 0]).push (.splitBits k) #[limb (row.getD 0 0) 0] bits
  -- Output blocks by chaining value and block counter, for the windows of the output stream.
  let mut outputs : Std.HashMap (ℕ × ℕ) ℕ := {}
  for k in [0:s.hash.size] do
    let row := s.hash[k]!
    -- At a constant bit the mux is one half of the message.
    match consts[row.getD 3 0]? with
    | some (p, v) =>
      if v == [0, 0, 0, 0] || v == [1, 0, 0, 0] then
        let base := if v == [0, 0, 0, 0] then 6 else 10
        for i in [0:4] do
          r := r.push (.mux k i p) #[limb (row.getD 2 0) i] #[colNode row (hashSrc (base + i))]
    | none => pure ()
    -- At a constant final word the output is the compression of the inputs.
    match consts[row.getD 1 0]? with
    | some (p, v) =>
      if finalOk (v.getD 1 0) then r := r.push (.compress k p) (hashIn row).toArray (hashOut row).toArray
      match v, consts[row.getD 8 0]? with
      | t :: _, some (_, n :: _) => if role t = 6 then outputs := outputs.insert (row.getD 0 0, n) k
      | _, _ => pure ()
    | none => pure ()
  let nFunction := r.size
  for k in [0:s.hash.size] do
    r := r.push (.collision k) (hashOut s.hash[k]!).toArray (hashIn s.hash[k]!).toArray
  -- Four consecutive words of the output stream that straddle two blocks bind the chaining value.
  for ((h, n), ka) in outputs.toList do
    match outputs[(h, n + 1)]? with
    | some kb =>
      for j in [1:4] do
        r := r.push (.window ka kb j) (windowIn s.hash[ka]! s.hash[kb]! j).toArray (hashH s.hash[ka]!).toArray
    | none => pure ()
  -- `inv`: the inverse and its argument determine each other.
  for (k, u) in invs do
    let row := s.emul[k]!
    match consts[row.getD 2 0]?, consts[(s.unions[u]!).2]? with
    | some (pz, _), some (po, _) =>
      let (a, x) := (row.getD 0 0, row.getD 1 0)
      r := (r.push (.inv k u pz po true) (limbs3 a).toArray (limbs3 x).toArray).push (.inv k u pz po false)
        (limbs3 x).toArray (limbs3 a).toArray
    | _, _ => pure ()
  return { nodes := 4 * s.next, rules := r, nFunction }

/-- Each node's rules as a premise, among the first `n` rules. -/
def premiseIndex (r : Rules Just) (nodes n : ℕ) : Array (Array ℕ) := Id.run do
  let mut idx : Array (Array ℕ) := Array.replicate nodes #[]
  for i in [0:n] do
    for j in [r.premOff[i]!:r.premOff[i + 1]!] do
      let p := r.prems[j]!
      idx := idx.modify p (·.push i)
  return idx

/-- The worklist's state: each node's binding time, each rule's unbound premises, and the rules fired in order. -/
structure BindState where
  bound : Array (Option ℕ)
  left : Array ℕ
  firings : Array ℕ

/-- Fire every rule the nodes on the stack complete, at time `t`. -/
def propagate (r : Rules Just) (idx : Array (Array ℕ)) (t : ℕ) (st : BindState) (stack : Array ℕ) : BindState :=
  Id.run do
    let { bound, left, firings } := st
    let mut bound := bound
    let mut left := left
    let mut firings := firings
    let mut stack := stack
    while !stack.isEmpty do
      let v := stack.back!
      stack := stack.pop
      for ri in idx[v]! do
        let k := left[ri]! - 1
        left := left.set! ri k
        if k = 0 then
          firings := firings.push ri
          for j in [r.conclOff[ri]!:r.conclOff[ri + 1]!] do
            let c := r.concls[j]!
            if bound[c]!.isNone then
              bound := bound.set! c (some t)
              stack := stack.push c
    return { bound, left, firings }

/-- Each node's binding time in one transcript, by squeeze call (`0` for constants), and the firings that bind
them: the rules without premises, then the seeds in time order, each firing every rule whose premises it
completes. -/
def bind (r : Rules Just) (nodes : ℕ) (idx : Array (Array ℕ)) (seeds : Array (ℕ × ℕ)) :
    Array (Option ℕ) × Array ℕ := Id.run do
  let mut st : BindState := {
    bound := Array.replicate nodes none
    left := (Array.range r.size).map fun i => r.premOff[i + 1]! - r.premOff[i]!
    firings := #[] }
  for ri in [0:r.size] do
    if st.left[ri]! = 0 then
      let mut stack := #[]
      let mut bound := st.bound
      for j in [r.conclOff[ri]!:r.conclOff[ri + 1]!] do
        let c := r.concls[j]!
        if bound[c]!.isNone then
          bound := bound.set! c (some 0)
          stack := stack.push c
      st := propagate r idx 0 { st with bound, firings := st.firings.push ri } stack
  for (t, w) in seeds do
    if st.bound[w]!.isNone then
      st := propagate r idx t { st with bound := st.bound.set! w (some t) } #[w]
  return (st.bound, st.firings)

/-- A test that failed, and the hinted wires behind it that no transcript binds. -/
structure Failure where
  call : ℕ
  pair : ℕ × ℕ
  /-- The calls that made the unbound hinted wires. -/
  hints : List ℕ
  /-- Each transcript's binding times of the pair. -/
  perTranscript : List (Option ℕ × Option ℕ) := []
  deriving Repr

structure Report where
  /-- The verdict, `Cert.accepts` of the certificate the worklist records. -/
  accepted : Bool
  transcripts : ℕ
  squeezes : ℕ
  /-- Union products whose rows the certificate reads. -/
  products : ℕ
  tests : ℕ
  /-- Tests no transcript binds. -/
  unbound : Array Failure
  /-- Tests bound only after the latest challenge they read. -/
  late : Array Failure
  /-- Tests bound only with the statement's words: claims the next verifier checks. -/
  deferred : Array Failure := #[]
  /-- Statement words that read a challenge, and those no transcript binds. -/
  exposed : ℕ
  exposedUnbound : Array ℕ
  /-- Each probed node's binding time per transcript. -/
  probes : List (ℕ × List (Option ℕ)) := []
  /-- The tests the certificate names as sumchecks' last checks, and their rounds. -/
  sumchecks : ℕ := 0
  rounds : ℕ := 0
  /-- The proof-of-work checks the certificate names, and their tests. -/
  pows : ℕ := 0
  powTests : ℕ := 0
  /-- The calls of the `eq_e` tests that close no certified sumcheck and no union. -/
  others : Array ℕ := #[]
  deriving Repr

/-- The hinted wires behind an unbound node: back through the function rules concluding it, the unbound limbs of
wires that `isHint` marks (made by `free_*`), else the first unbound limbs visited. -/
def hintsOf (an : Analysis) (byConcl : Array (Array ℕ)) (bound : Array Bool) (isHint : ℕ → Bool)
    (start : List ℕ) (limit : ℕ) : List ℕ := Id.run do
  let r := an.rules
  let mut seen : Std.HashSet ℕ := {}
  let mut stack := start.toArray
  let mut hints := #[]
  let mut visited := #[]
  while !stack.isEmpty && hints.size < limit do
    let v := stack.back!
    stack := stack.pop
    if seen.contains v || bound[v]! then continue
    seen := seen.insert v
    if isHint v then hints := hints.push v
    if visited.size < limit then visited := visited.push v
    for ri in byConcl[v]! do
      for j in [r.premOff[ri]!:r.premOff[ri + 1]!] do
        stack := stack.push r.prems[j]!
  return (if hints.isEmpty then visited else hints).toList

/-- A wire's binding time: its last limb's, none if a limb is unbound. -/
def wireTime (bd : Array (Option ℕ)) (w : ℕ) : Option ℕ :=
  (limbs4 w).foldl (fun acc n => match acc, bd[n]! with
    | some t, some u => some (max t u)
    | _, _ => none) (some 0)

/-- The latest squeeze each wire depends on, by call, none for a wire no challenge reaches. A wire depends on what
the call that made it reads, and a squeeze's on that squeeze: dependence follows how wires are made, not every
relation a row states (a Merkle row's mux slot is an earlier wire, which the row does not make). Constants depend on
nothing, though a method makes one the first time it needs it. -/
def latestByCalls (rp : Replay) : Array (Option ℕ) := Id.run do
  let mut isConst : Array Bool := Array.replicate rp.state.next false
  for (w, src) in rp.state.pub do
    match src with
    | .const _ => isConst := isConst.set! w true
    | .statement _ => pure ()
  let mut gamma : Array (Option ℕ) := Array.replicate rp.state.next none
  let mut w := 0
  for i in [0:rp.calls.size] do
    let c := rp.calls.getD i .zero
    let squeeze : Bool := match c with
      | .leafBlock _ _ t _ => role t == 6
      | _ => false
    let g := if squeeze then some i else c.args.foldl (fun acc a => match acc, gamma[a]! with
      | some x, some y => some (max x y)
      | none, y => y
      | x, none => x) none
    while w < rp.state.next && rp.maker[w]! = i do
      if !isConst[w]! then gamma := gamma.set! w g
      w := w + 1
  return gamma

/-! The sumchecks behind the late tests, found by their calls. -/

/-- Each wire's making calls, with the output's place. -/
def outIndex (rp : Replay) : Std.HashMap ℕ (Array (ℕ × ℕ)) := Id.run do
  let mut idx : Std.HashMap ℕ (Array (ℕ × ℕ)) := {}
  for j in [0:rp.outs.size] do
    let os := rp.outs[j]!
    for p in [0:os.length] do
      idx := idx.insert (os.getD p 0) ((idx.getD (os.getD p 0) #[]).push (j, p))
  return idx

/-- A call making `w` as its first output that `f` takes. -/
def makerBy {α : Type} (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) (f : ℕ → Call → Option α) :
    Option α :=
  (idx.getD w #[]).findSome? fun (j, p) => if p = 0 then f j (rp.calls.getD j .zero) else none

/-- A `zero` call making `w`. -/
def zeroAt (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) : Option ℕ :=
  makerBy rp idx w fun j c => match c with
    | .zero => some j
    | _ => none

/-- Horner's calls ending at `w`: its point, the coefficients constant first, the `zero` call, the `mul_add` calls in
order. -/
def hornerOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) :
    Option (ℕ × List ℕ × ℕ × List ℕ) := Id.run do
  let some (x, c, acc, j) := makerBy rp idx w (fun j c => match c with
    | .mulAdd acc x c => some (x, c, acc, j)
    | _ => none)
    | return none
  let mut coeffs := [c]
  let mut calls := [j]
  let mut cur := acc
  for _ in [0:64] do
    if let some z := zeroAt rp idx cur then
      return some (x, coeffs, z, calls)
    match makerBy rp idx cur (fun j c => match c with
      | .mulAdd acc x' c => if x' = x then some (c, acc, j) else none
      | _ => none) with
    | some (c, acc, j) => coeffs := coeffs ++ [c]; calls := j :: calls; cur := acc
    | none => return none
  return none

/-- The `add` fold over `ws` ending at `w`: its `zero` call and its calls in order. -/
def foldOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) (ws : List ℕ) : Option (ℕ × List ℕ) := Id.run do
  let mut cur := w
  let mut calls := []
  for c in ws.reverse do
    match makerBy rp idx cur (fun j call => match call with
      | .add acc c' => if c' = c then some (acc, j) else none
      | _ => none) with
    | some (acc, j) => calls := j :: calls; cur := acc
    | none => return none
  return (zeroAt rp idx cur).map (·, calls)

/-- The round whose next claim is `w`, with the claim it reads. -/
def roundOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) : Option (RoundCert × ℕ) := do
  let (x, coeffs, hornerZero, hornerAt) ← hornerOf rp idx w
  guard (2 ≤ coeffs.length)
  -- With an eq weight the constant coefficient is `claim + e · tail`, else the linear one is `claim + tail`.
  let weighted := makerBy rp idx (coeffs.getD 0 0) (fun j c => match c with
    | .mulAdd e t cl => (foldOf rp idx t (coeffs.drop 1)).map fun (z, ts) => (e, t, cl, j, z, ts)
    | _ => none)
  let (weight, claim, fixedAt, tailZero, tailAt) ← match weighted with
    | some (e, _, cl, j, z, ts) => some (some e, cl, j, z, ts)
    | none => makerBy rp idx (coeffs.getD 1 0) (fun j c => match c with
      | .add cl t => (foldOf rp idx t (coeffs.drop 2)).map fun (z, ts) => (none, cl, j, z, ts)
      | _ => none)
  -- The challenge: three squeezed words.
  let (chalAt, w0, w1, w2) ← makerBy rp idx x (fun j c => match c with
    | .kToE a b d => some (j, a, b, d)
    | _ => none)
  let words ← [w0, w1, w2].mapM fun wk => (idx.getD wk #[]).findSome? fun (dk, p) =>
    match rp.calls.getD dk .zero with
    | .dToK d => makerBy rp idx d (fun lb c => match c with
      | .leafBlock _ _ t _ => if t / 2 ^ 56 = 6 then some (dk, p, lb) else none
      | _ => none)
    | _ => none
  return ({ coeffs, weight, tailZero, tailAt, fixedAt, chal := x, hornerZero, hornerAt, chalAt, words, time := 0 },
    claim)

/-- A round's time in a transcript: one more than the place of the block whose output its challenge's squeeze reads. -/
def roundTime (rp : Replay) (s : State) (t : Transcript) (rc : RoundCert) : Option ℕ := do
  let (_, _, lb) ← rc.words.head?
  let .leafBlock h _ _ _ := rp.calls.getD lb .zero | none
  let k ← t.blocks.findIdx? fun b => (s.hash.getD b []).getD 6 0 == h
  return k + 1

/-- The sumcheck a test closes, if one of its wires is a last claim: its rounds back to the first claim no round
makes, in the transcript drawing the last round's challenge. -/
def sumcheckOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (s : State) (ts : List Transcript)
    (u a b : ℕ) : Option SumcheckCert := Id.run do
  for (last, final) in [(a, b), (b, a)] do
    let mut rounds : List RoundCert := []
    let mut cur := last
    for _ in [0:256] do
      match roundOf rp idx cur with
      | some (rc, cl) =>
        if rounds.all (·.coeffs.length == rc.coeffs.length) then rounds := rc :: rounds; cur := cl else break
      | none => break
    if let some lastRound := rounds.getLast? then
      let some k := (List.range ts.length).find? fun k => (roundTime rp s (ts.getD k default) lastRound).isSome
        | continue
      let t := ts.getD k default
      let timed := rounds.filterMap fun rc => (roundTime rp s t rc).map fun time => { rc with time }
      if timed.length = rounds.length then
        return some { claim0 := cur, rounds := timed, deg := lastRound.coeffs.length - 1, test := u, final,
                      transcript := k }
  return none

/-- The proof-of-work checks among the test calls: `eq_k_const` tests of bits of a `split` of a trial compression's
first word, by split. -/
def powsOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (testCalls : Array ℕ) : Array PowCert := Id.run do
  let mut bySplit : Std.HashMap ℕ (Array (ℕ × ℕ)) := {}
  for j in testCalls do
    if let .eqConstK a 0 := rp.calls.getD j .zero then
      for (sp, k) in idx.getD a #[] do
        if let .split _ := rp.calls.getD sp .zero then
          bySplit := bySplit.insert sp ((bySplit.getD sp #[]).push (k, j))
  let mut out := #[]
  for (sp, ts) in bySplit.toList do
    let .split w := rp.calls.getD sp .zero | continue
    let some dk := (idx.getD w #[]).findSome? (fun (j, p) => match rp.calls.getD j .zero with
      | .dToK _ => if p = 0 then some j else none
      | _ => none) | continue
    let .dToK d := rp.calls.getD dk .zero | continue
    let some cp := makerBy rp idx d (fun j c => match c with
      | .compress .. => some j
      | _ => none) | continue
    let sorted := ts.qsort (·.1 < ·.1)
    out := out.push { compressAt := cp, dkAt := dk, splitAt := sp, bits := sorted.size,
                      testAt := (sorted.map (·.2)).toList }
  return out

def analyse (rp : Replay) (probe : List ℕ := []) : Report := Id.run do
  let s := rp.state
  let an0 := rowRules s rp.invs
  let bs := blocks rp
  let squeezes := bs.filter (·.squeeze)
  let gamma := latestByCalls rp
  let tainted := fun w => (gamma[w]!).isSome
  let latestOf := fun w => (gamma[w]!).getD 0
  -- Equalities that bind: digests, methods', and field equalities reading no challenge.
  let mut rules := an0.rules
  let mut tests : Array (ℕ × ℕ × ℕ) := #[]
  let mut isTest : Array Bool := Array.replicate s.unions.size false
  for u in [0:s.unions.size] do
    let (a, b) := s.unions[u]!
    if rp.eqKind[u]! = .field ∧ (tainted a ∨ tainted b) then
      tests := tests.push (u, a, b)
      isTest := isTest.set! u true
    else
      for j in [0:4] do
        rules := (rules.push (.eq u j true) #[limb a j] #[limb b j]).push (.eq u j false) #[limb b j] #[limb a j]
  -- A union product: bound once its pool's digests, begin bits, selection bits and the point are. A pool's `pack`
  -- calls are the run of them after its end mark.
  let pools := rp.pools.map fun pc => Id.run do
    let mut packs := #[]
    let mut j := pc.packs.headD 0
    while j < rp.calls.size && (match rp.calls.getD j .zero with | .pack _ => true | _ => false) do
      packs := packs.push j
      j := j + 1
    return { pc with packs := packs.toList }
  let mut claims : Array UnionClaim := #[]
  for qc in rp.prods do
    let uc := qc.claim rp.outs (pools.getD qc.pool default)
    rules := rules.push (.union claims.size) (uc.inputs.flatMap limbs4).toArray (limbs3 uc.out).toArray
    claims := claims.push uc
  -- The calls whose equality is a test, relaxed when the certificate replays the unions' rows.
  let mut relax : Array Bool := Array.replicate rp.calls.size false
  for (u, _, _) in tests do
    relax := relax.set! (rp.eqCall[u]!) true
  let an := { an0 with rules }
  let idx := premiseIndex rules an.nodes rules.size
  let ts := transcripts bs
  -- Each absorb block's `HASH` row, by its output wire.
  let mut rowOfOut : Std.HashMap ℕ ℕ := {}
  for k in [0:s.hash.size] do
    rowOfOut := rowOfOut.insert ((s.hash[k]!).getD 6 0) k
  let stmt := statementNodes s
  let mut binds : Array (Array (Option ℕ)) := #[]
  let mut certs : Array Transcript := #[]
  for path in ts do
    -- Absorbed words are bound at the next squeeze on the path; the blocks absorbed before a squeeze seed it.
    let mut words : Array (ℕ × ℕ) := #[]
    let mut blocksRev : Array ℕ := #[]
    let mut nextSq : Option ℕ := none
    for b in path.reverse do
      if b.squeeze then nextSq := some (match nextSq with | some t => min t b.call | none => b.call)
      else match nextSq with
        | some t =>
          for w in b.words do words := words.push (t, limb w 0)
          blocksRev := blocksRev.push (rowOfOut.getD b.cvOut 0)
        | none => pure ()
    -- The statement's words are claims the verifier of this circuit's proof checks: bound last, at the end.
    let (bd, firings) := bind rules an.nodes idx (words.reverse ++ (stmt.map (rp.calls.size, ·)).toArray)
    binds := binds.push bd
    certs := certs.push { blocks := blocksRev.reverse.toList, firings }
  -- Each product's point: `X + 1` is made by the call after the point's first.
  let points := rp.prods.map fun qc =>
    let start := rp.maker.getD qc.x1 0 - 1
    let pt : PointCert := { start, x := 0, a := [] }
    let x := match rp.calls.getD (start + 1) .zero with | .add x _ => x | _ => 0
    let a := (List.range 4).map fun j => match rp.calls.getD (pt.round j) .zero with | .add aj _ => aj | _ => 0
    { pt with x, a }
  -- Each union's coverage test: the test of its two products' outputs, and a transcript binding what both pools
  -- commit to.
  let outOf := fun (i : ℕ) => let qc := rp.prods.getD i default; ProdCert.out rp.outs (pools.getD qc.pool default) qc
  let committedOf := fun (i : ℕ) => (pools.getD (rp.prods.getD i default).pool default).committed rp.outs
  let prodIdx := List.range rp.prods.size
  let covers := tests.filterMap fun (u, a, b) =>
    match prodIdx.find? (outOf · == a), prodIdx.find? (outOf · == b) with
    | some i, some j =>
      let ls := (committedOf i ++ committedOf j).flatMap limbs4
      let k := (List.range binds.size).find? (fun k => ls.all fun n => ((binds.getD k #[])[n]?.join).isSome)
      some { test := u, sel := i, decl := j, transcript := k.getD 0 }
    | _, _ => none
  let cert : Cert := {
    rules, nodes := an.nodes, isTest, claims, transcripts := certs.toList, calls := rp.calls, relax, pools
    prods := rp.prods, points, covers }
  -- The tests closing a sumcheck whose rounds the verdict certifies.
  let idxO := outIndex rp
  let ms := cert.marks s
  let os := cert.outs
  let sumchecks := (tests.filterMap fun (u, a, b) => sumcheckOf rp idxO s certs.toList u a b).filter fun sc =>
    ({ cert with sumchecks := #[sc] }).sumchecksOk s os ms
  let pows := (powsOf rp idxO (tests.map fun (u, _, _) => rp.eqCall[u]!)).filter (·.ok os cert.calls cert.relax)
  let cert := { cert with sumchecks, pows }
  let accepted := cert.accepts s
  let mut anyBound : Array Bool := Array.replicate an.nodes false
  for bd in binds do
    for v in [0:an.nodes] do
      if bd[v]!.isSome then anyBound := anyBound.set! v true
  let mut byConcl : Array (Array ℕ) := Array.replicate an.nodes #[]
  for i in [0:an0.nFunction] do
    for j in [rules.conclOff[i]!:rules.conclOff[i + 1]!] do
      byConcl := byConcl.modify rules.concls[j]! (·.push i)
  let mut unbound := #[]
  let mut late := #[]
  let mut deferred := #[]
  let callOf := fun (i : ℕ) => rp.eqCall[i]!
  for (i, a, b) in tests do
    let g := max (latestOf a) (latestOf b)
    let mut best : Option ℕ := none
    for bd in binds do
      match wireTime bd a, wireTime bd b with
      | some ta, some tb => best := some (match best with | some x => min x (max ta tb) | none => max ta tb)
      | _, _ => pure ()
    match best with
    | none =>
      -- The hinted wires behind it in the transcript that binds most of its limbs.
      let ls := limbs4 a ++ limbs4 b
      let score := fun (bd : Array (Option ℕ)) => (ls.filter fun n => (bd[n]!).isSome).length
      let most := binds.foldl (fun acc bd => if score bd ≥ score acc then bd else acc) (binds[0]?.getD #[])
      let isHint := fun v => v < 4 * s.next && match rp.calls.getD (rp.maker[v / 4]!) .zero with
        | .freeE | .freeK | .freeD => true
        | _ => false
      let hs := hintsOf an byConcl ((Array.range an.nodes).map fun v => (most[v]?.join).isSome) isHint ls 8
      let hs := (if hs.isEmpty then [limb a 0, limb b 0] else hs).filter (· < 4 * s.next)
      let perT := binds.toList.map fun bd => (wireTime bd a, wireTime bd b)
      unbound := unbound.push ⟨callOf i, (a, b), hs.map (rp.maker[· / 4]!), perT⟩
    | some t =>
      if t = rp.calls.size then deferred := deferred.push { call := callOf i, pair := (a, b), hints := [] }
      else if t > g then late := late.push { call := callOf i, pair := (a, b), hints := [t, g] }
  let mut exposed := 0
  let mut exposedUnbound := #[]
  for (w, src) in s.pub do
    match src with
    | .statement j =>
      if tainted w then
        exposed := exposed + 1
        if !(limbs4 w).all (anyBound[·]!) then exposedUnbound := exposedUnbound.push j
    | .const _ => pure ()
  -- A probe's per-transcript binding, then its latest challenge as a last entry.
  let probes := probe.map fun w => (w, binds.toList.map (wireTime · w) ++ [if tainted w then some (latestOf w) else none])
  return {
    accepted, transcripts := ts.size, squeezes := squeezes.size, products := rp.prods.size, tests := tests.size, unbound,
    late, deferred,
    exposed, exposedUnbound, probes, sumchecks := sumchecks.size,
    rounds := sumchecks.foldl (fun n sc => n + sc.rounds.length) 0,
    pows := pows.size, powTests := pows.foldl (fun n pc => n + pc.bits) 0,
    others := tests.filterMap fun (u, _, _) => match rp.calls.getD (rp.eqCall[u]!) .zero with
      | .eqE .. => if sumchecks.any (·.test == u) || covers.any (·.test == u) then none else some (rp.eqCall[u]!)
      | _ => none }

end LeanVMCircuits.Rec.Bind
