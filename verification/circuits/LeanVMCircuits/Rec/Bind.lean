module

public import LeanVMCircuits.Rec.Closure
public import LeanVMCircuits.Rec.Union
public import LeanVMCircuits.Rec.Dump

@[expose] public section

/-!
Transcript binding of a recursion circuit.

A challenge is a squeezed word of a transcript in rows: the output of a `leaf_block` at the duplex's output tag,
whose chaining value is the end of a run of absorb blocks from a constant seed. A wire is *bound* by a squeeze when
it is determined by the words absorbed before it: it is one of them or a constant, or a determination rule makes it
from bound wires. The rules are exact views (a `CAST` or `SPLIT` row's slots, a `HASH` row's ports and columns),
functions (`EMUL`, `EXK`, the compression), equalities that are not tests, an inverse, and collision resistance of
the compression (a bound output binds the inputs).

A *test* is an equality made from outside the builder's methods (`eq_e`, `eq_k`, `eq_e_const`, `eq_k_const`) that
reads a wire depending on a challenge. Tests do not bind. The check: every test's wires are bound by some squeeze of
one transcript, so the test is a function of the words absorbed before that squeeze, which a prover fixes before it
sees the challenge. A hinted wire a test reads that no transcript absorbs, and no rule determines from absorbed
words, fails the check: the prover may choose it after the challenge.
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
  let { state, calls, outs, maker, eqKind, eqCall, pending, pools, products } := r
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
  return ⟨s', calls.push c, outs.push out, maker, eqKind, eqCall, pending, pools, products⟩

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

/-- The rules of a replayed circuit, the nodes past its wires, and the rows' function rules' count. -/
structure Analysis where
  nodes : ℕ
  rules : Rules
  /-- Rules up to here are the rows' own (views and functions); taint flows through them. -/
  nFunction : ℕ
  /-- Constants. -/
  seeds : Array ℕ

/-- A limb's node: wire `w`'s limb `i`. -/
def limb (w i : ℕ) : ℕ := 4 * w + i

/-- A wire's four limb nodes. -/
def limbs4 (w : ℕ) : Array ℕ := #[limb w 0, limb w 1, limb w 2, limb w 3]

/-- The columns a form reads. -/
partial def formCols : Form → List ℕ
  | .const _ => []
  | .col c => [c]
  | .prod a b => [a, b]
  | .sum ts => ts.flatMap formCols

/-- One row's rules from its table's forms (`RowSat`): a slot limb that is a column is that column, a constant limb
is bound, and any other limb is a function of the columns it reads. Returns the rules, the next free node, the
constant nodes, and each of the table's `nCols` columns' nodes, fresh where no slot reads it as itself.

The rules, constants and counter are threaded by value so that each is updated in place. -/
def rowForms (r : Rules) (next : ℕ) (seeds : Array ℕ) (forms : List (List Form)) (nCols : ℕ) (row : Array ℕ) :
    Rules × ℕ × Array ℕ × Array ℕ := Id.run do
  let mut r := r
  let mut next := next
  let mut seeds := seeds
  let mut cols : Array (Option ℕ) := Array.replicate nCols none
  for (slot, s) in forms.zipIdx do
    let w := row[s]!
    for (f, i) in slot.zipIdx do
      match f with
      | .col j =>
        match cols[j]! with
        | none => cols := cols.set! j (some (limb w i))
        | some n => r := r.view #[n] #[limb w i]
      | .const _ => seeds := seeds.push (limb w i)
      | _ => pure ()
  let mut ns : Array ℕ := #[]
  for j in [0:nCols] do
    match cols[j]! with
    | some n => ns := ns.push n
    | none => ns := ns.push next; next := next + 1
  for (slot, s) in forms.zipIdx do
    let w := row[s]!
    for (f, i) in slot.zipIdx do
      match f with
      | .col _ | .const _ => pure ()
      | _ => r := r.push .view ((formCols f).toArray.map (ns[·]!)) #[limb w i]
  return (r, next, seeds, ns)

/-- The rows' views and functions, then collision resistance. -/
def rowRules (s : State) : Analysis := Id.run do
  let mut r : Rules := {}
  let mut next := 4 * s.next
  let mut seeds : Array ℕ := #[]
  for row in s.emul do
    let (r', next', seeds', _) := rowForms r next seeds Rec.emul 9 row.toArray
    r := r'; next := next'; seeds := seeds'
  for row in s.exk do
    let (r', next', seeds', _) := rowForms r next seeds Rec.exk 7 row.toArray
    r := r'; next := next'; seeds := seeds'
  for row in s.cast do
    let (r', next', seeds', _) := rowForms r next seeds Rec.cast 4 row.toArray
    r := r'; next := next'; seeds := seeds'
  for row in s.split do
    let (r', next', seeds', ns) := rowForms r next seeds Rec.split 65 row.toArray
    -- The word column is the sum of its bit columns' monomials, each bit 0 or 1: either side gives the other.
    r := (r'.push .split (ns.extract 1 65) #[ns[0]!]).push .split #[ns[0]!] (ns.extract 1 65)
    next := next'; seeds := seeds'
  -- A constant's limbs, so a mux bit that is a constant chooses its half.
  let mut consts : Std.HashMap ℕ Limbs := {}
  for (w, src) in s.pub do
    match src with
    | .const v => consts := consts.insert w v
    | .statement _ => pure ()
  -- Each hash row's columns `t, f, h0..h3, m0..m7, o0..o3, sel` as nodes.
  let mut hashCols : Array (Array ℕ) := #[]
  -- Output blocks by chaining value and block counter, for the windows of the output stream.
  let mut outputs : Std.HashMap (ℕ × ℕ) ℕ := {}
  for row in s.hash do
    let a := row.toArray
    let (r', next', seeds', ns) := rowForms r next seeds Rec.hash 19 a
    r := r'; next := next'; seeds := seeds'
    -- At a constant bit the mux is one half of the message.
    match consts[a[3]!]? with
    | some [0, 0, 0, 0] => r := r.view (limbs4 a[2]!) #[ns[6]!, ns[7]!, ns[8]!, ns[9]!]
    | some [1, 0, 0, 0] => r := r.view (limbs4 a[2]!) #[ns[10]!, ns[11]!, ns[12]!, ns[13]!]
    | _ => pure ()
    r := r.push .compress (ns.extract 0 14) (ns.extract 14 18)
    match consts[a[1]!]?, consts[a[8]!]? with
    | some (t :: _), some (n :: _) => if role t = 6 then outputs := outputs.insert (a[0]!, n) hashCols.size
    | _, _ => pure ()
    hashCols := hashCols.push ns
  let nFunction := r.size
  for ns in hashCols do
    r := r.push .collision (ns.extract 14 18) (ns.extract 0 14)
  -- Four consecutive words of the output stream that straddle two blocks bind the chaining value.
  for ((h, n), ia) in outputs.toList do
    match outputs[(h, n + 1)]? with
    | some ib =>
      let (na, nb) := (hashCols[ia]!, hashCols[ib]!)
      for j in [1:4] do
        r := r.push .window (na.extract (14 + j) 18 ++ nb.extract 14 (14 + j)) (na.extract 2 6)
    | none => pure ()
  for (w, src) in s.pub do
    match src with
    | .const _ => seeds := seeds ++ limbs4 w
    | .statement _ => pure ()
  return { nodes := next, rules := r, nFunction, seeds }

/-- Each node's rules as a premise, among the first `n` rules. -/
def premiseIndex (r : Rules) (nodes n : ℕ) : Array (Array ℕ) := Id.run do
  let mut idx : Array (Array ℕ) := Array.replicate nodes #[]
  for i in [0:n] do
    for j in [r.premOff[i]!:r.premOff[i + 1]!] do
      let p := r.prems[j]!
      idx := idx.modify p (·.push i)
  return idx

/-- Each node's binding time in one transcript, by squeeze call (`0` for constants): the seeds, in time order, each
fires every rule whose premises it completes. -/
def bind (r : Rules) (nodes : ℕ) (idx : Array (Array ℕ)) (seeds : Array (ℕ × ℕ)) : Array (Option ℕ) := Id.run do
  let mut bound : Array (Option ℕ) := Array.replicate nodes none
  let mut left : Array ℕ := (Array.range r.size).map fun i => r.premOff[i + 1]! - r.premOff[i]!
  for (t, w) in seeds do
    if bound[w]!.isNone then
      bound := bound.set! w (some t)
      let mut stack := #[w]
      while !stack.isEmpty do
        let v := stack.back!
        stack := stack.pop
        for ri in idx[v]! do
          let k := left[ri]! - 1
          left := left.set! ri k
          if k = 0 then
            for j in [r.conclOff[ri]!:r.conclOff[ri + 1]!] do
              let c := r.concls[j]!
              if bound[c]!.isNone then
                bound := bound.set! c (some t)
                stack := stack.push c
  return bound

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
  let an0 := rowRules s
  let bs := blocks rp
  let squeezes := bs.filter (·.squeeze)
  let gamma := latestByCalls rp
  let tainted := fun w => (gamma[w]!).isSome
  let latestOf := fun w => (gamma[w]!).getD 0
  -- Equalities that bind: digests, methods', and field equalities reading no challenge.
  let mut rules := an0.rules
  let mut tests : Array (ℕ × ℕ × ℕ) := #[]
  for i in [0:s.unions.size] do
    let (a, b) := s.unions[i]!
    if rp.eqKind[i]! = .field ∧ (tainted a ∨ tainted b) then
      tests := tests.push (i, a, b)
    else
      for j in [0:4] do
        rules := rules.view #[limb a j] #[limb b j]
  -- `inv`: the inverse and its argument determine each other.
  for i in [0:rp.calls.size] do
    match rp.calls.getD i .freeE, rp.outs.getD i [] with
    | Call.inv a, [inv] =>
      let (ea, ei) := ((limbs4 a).extract 0 3, (limbs4 inv).extract 0 3)
      rules := (rules.push .inv ea ei).push .inv ei ea
    | _, _ => pure ()
  -- A union product: bound once its pool's digests, begin bits, selection bits and the point are.
  for p in rp.products do
    let mp := rp.pools[p.pool]!
    let mut ps : Array ℕ := #[]
    for d in mp.digests do
      ps := ps ++ limbs4 d
    for b in mp.pool.begins do
      ps := ps ++ limbs4 b
    for it in mp.pool.items do
      match it.select with
      | some (s0, s1) => ps := ps ++ limbs4 s0 ++ limbs4 s1
      | none => pure ()
    for w in p.x1 :: p.weights do
      ps := ps ++ limbs4 w
    rules := rules.push .union ps (limbs4 p.out)
  let an := { an0 with rules }
  let idx := premiseIndex rules an.nodes rules.size
  let ts := transcripts bs
  let mut binds : Array (Array (Option ℕ)) := #[]
  for path in ts do
    -- Absorbed words are bound at the next squeeze on the path.
    let mut words : Array (ℕ × ℕ) := #[]
    let mut nextSq : Option ℕ := none
    for b in path.reverse do
      if b.squeeze then nextSq := some (match nextSq with | some t => min t b.call | none => b.call)
      else match nextSq with
        | some t => for w in b.words do words := words.push (t, limb w 0)
        | none => pure ()
    -- The statement's words are claims the verifier of this circuit's proof checks: bound last, at the end.
    let stmt := s.pub.toList.flatMap fun (w, src) => match src with
      | .statement _ => (limbs4 w).toList.map (rp.calls.size, ·)
      | .const _ => []
    binds := binds.push (bind rules an.nodes idx (an.seeds.map (0, ·) ++ words.reverse ++ stmt.toArray))
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
      let ls := (limbs4 a).toList ++ (limbs4 b).toList
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
    transcripts := ts.size, squeezes := squeezes.size, tests := tests.size, unbound, late, deferred, exposed,
    exposedUnbound, probes }

end LeanVMCircuits.Rec.Bind
