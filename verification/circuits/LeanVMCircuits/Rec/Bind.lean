module

public import LeanVMCircuits.Rec.Justify
public import LeanVMCircuits.Rec.Union
public import LeanVMCircuits.Rec.Dump

@[expose] public section

/-!
Transcript binding of a recursion circuit.

A challenge is a squeezed word of a transcript in rows: the output of a `leaf_block` at the duplex's output tag,
whose chaining value is the end of a run of absorb blocks from a constant seed. A wire is *bound* by a squeeze when
it is determined by the words absorbed before it: it is one of them or a constant, or a determination rule makes it
from bound wires. Each rule carries its justification (`Just`): a row's forms, a split, a constant mux bit, a
compression at a constant final word, an equality that is not a test, an inverse, collision resistance of the
compression and of the output window, or a marked union product.

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

/-- A pool the dump marks, whose calls build what `Model.poolRows` builds. -/
structure ModeledPool where
  digests : List ℕ
  selecting : Bool
  pool : Pool
  deriving Inhabited

/-- A product the dump marks, whose calls build what `Model.product` builds: the pool, the point, the output. -/
structure ModeledProduct where
  pool : ℕ
  x1 : ℕ
  weights : List ℕ
  out : ℕ

/-- A marked block being replayed, and the state the model builds from its start. -/
inductive Pending where
  | pool (m : ModeledPool) (expected : State)
  | product (m : ModeledProduct) (expected : State)

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
  pools : Array ModeledPool := #[]
  products : Array ModeledProduct := #[]
  /-- Each `inv` call's `EMUL` row and equality. -/
  invs : Array (ℕ × ℕ) := #[]

/-- Two states hold the same circuit and counters (the caches follow from the calls). -/
def sameCircuit (a b : State) : Bool :=
  a.next == b.next && a.unions == b.unions && a.emul == b.emul && a.exk == b.exk && a.hash == b.hash &&
    a.split == b.split && a.cast == b.cast && a.pub == b.pub && a.statement == b.statement

/-- Open or close a marked block: at its start the model builds the block from the current state; at its end the
calls replayed since must have built the same. -/
def Replay.mark (r : Replay) (line : Dump.Line) : Except String Replay :=
  match line, r.pending with
  | .call _, _ => .ok r
  | .pool chunks selecting digests, none =>
    let (pool, expected) := (poolRows chunks selecting digests).run r.state
    .ok { r with pending := some (.pool { digests, selecting, pool } expected) }
  | .product first x1 weights, none =>
    match r.pools.findIdx? fun p => (p.pool.items[0]?.bind (·.m.head?)) = some first with
    | none => .error s!"a product of no pool marked before it: {first}"
    | some i =>
      let (out, expected) := (product r.pools[i]!.pool.items x1 weights).run r.state
      .ok { r with pending := some (.product { pool := i, x1, weights, out } expected) }
  | .stop, some (.pool m expected) =>
    if sameCircuit r.state expected then .ok { r with pending := none, pools := r.pools.push m }
    else .error "the calls marked as a pool build something else than Model.poolRows"
  | .stop, some (.product m expected) =>
    if sameCircuit r.state expected then .ok { r with pending := none, products := r.products.push m }
    else .error "the calls marked as a product build something else than Model.product"
  | .stop, none => .error "an end mark without a start"
  | _, some _ => .error "a mark inside a marked block"

def eqKindOf : Call → EqKind
  | .eqD .. => .digest
  | .eqE .. | .eqK .. | .eqConstE .. | .eqConstK .. => .field
  | _ => .method

def Replay.step (r : Replay) (c : Call) : Replay := Id.run do
  -- Take the fields apart first, so that each array is updated in place.
  let { state, calls, outs, maker, eqKind, eqCall, pending, pools, products, invs } := r
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
  return ⟨s', calls.push c, outs.push out, maker, eqKind, eqCall, pending, pools, products, invs⟩

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
  -- A union product: bound once its pool's digests, begin bits, selection bits and the point are.
  let mut claims : Array UnionClaim := #[]
  for p in rp.products do
    let mp := rp.pools[p.pool]!
    let mut ins : Array ℕ := mp.digests.toArray ++ mp.pool.begins
    for it in mp.pool.items do
      match it.select with
      | some (s0, s1) => ins := (ins.push s0).push s1
      | none => pure ()
    let uc : UnionClaim := { inputs := (ins.push p.x1 ++ p.weights.toArray).toList, out := p.out }
    rules := rules.push (.union claims.size) (uc.inputs.flatMap limbs4).toArray (limbsA uc.out)
    claims := claims.push uc
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
  let cert : Cert := { rules, nodes := an.nodes, isTest, claims, transcripts := certs.toList }
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
    accepted, transcripts := ts.size, squeezes := squeezes.size, tests := tests.size, unbound, late, deferred,
    exposed, exposedUnbound, probes }

end LeanVMCircuits.Rec.Bind
