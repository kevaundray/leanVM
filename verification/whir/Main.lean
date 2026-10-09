import Whir.Protocol
import Whir.CausalGame
import Whir.CommitmentAmbiguity

open Whir.Concrete Whir.Protocol

def seed (i : Nat) : UInt64 :=
  let x := UInt64.ofNat (i+1) * 11400714819323198485
  (x ^^^ (x >>> 29)) * 13787848793156543929

def fixture (i : Nat) : E := ⟨seed (3*i), seed (3*i+1), seed (3*i+2)⟩

def emitN (key : String) (xs : Array Nat) : IO Unit :=
  IO.println (key ++ "=" ++ String.intercalate "," (xs.toList.map toString))

def emitE (key : String) (xs : Array E) : IO Unit :=
  emitN key (xs.flatMap fun x => #[x.c0.toNat, x.c1.toNat, x.c2.toNat])

def requireIO (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def smoke : IO Unit := do
  let c : Config := ⟨7, #[2,2,1], #[1,2,2], #[5,3,3], #[0,1,1]⟩
  let ch : Challenges := ⟨#[
    ⟨#[fixture 1, fixture 2], #[tab 5 (fun i => fixture (10+i))], #[fixture 20], fixture 21⟩,
    ⟨#[fixture 3, fixture 4], #[tab 3 (fun i => fixture (30+i))], #[fixture 40], fixture 41⟩,
    ⟨#[fixture 5], #[], #[fixture 50], fixture 51⟩], #[fixture 6, fixture 7]⟩
  let witness := tab 96 seed
  let b := tab 128 fun i => if i < 96 then fixture (100+i) else E.zero
  let target := dot (witness.map E.ofK) b
  let (root, p) ← match prove c ch witness b target with
    | .ok result => pure result
    | .error e => throw (IO.userError ("honest prover: " ++ e))
  let check := fun proof => (verify c ch 3 root b target proof).isOk
  requireIO (check p) "honest multilevel opening rejected"
  requireIO (!check {p with levels := p.levels.pop}) "short opening accepted"
  requireIO (!check {p with residual := p.residual.pop}) "short final accepted"
  requireIO (!check {p with residual := p.residual.set! 0 (p.residual[0]! + E.one)}) "bad final accepted"
  requireIO (!(verify c ch 3 root b (target+E.one) p).isOk) "bad target accepted"
  let l0 := p.levels[0]!
  requireIO (!check {p with levels := p.levels.set! 0 {l0 with rows := l0.rows.pop}}) "missing query accepted"
  let row := l0.rows[0]!
  let rows := l0.rows.set! 0 (row.set! 0 (row[0]!+E.one))
  requireIO (!check {p with levels := p.levels.set! 0 {l0 with rows}}) "bad authenticated row accepted"
  let ood := l0.oods[0]!
  let oods := l0.oods.set! 0 {ood with value := ood.value+E.one}
  requireIO (!check {p with levels := p.levels.set! 0 {l0 with oods}}) "bad OOD accepted"
  requireIO (!check {p with levels := p.levels.set! 0 {l0 with oods := #[]}}) "missing OOD accepted"
  let badCh := {ch with levels := ch.levels.set! 0 {ch.levels[0]! with querySqueezes := #[]}}
  requireIO (!(verify c badCh 3 root b target p).isOk) "missing query challenge accepted"
  requireIO (!(verify c ch 0 root b target p).isOk) "empty lane layout accepted"
  let badPublic : Whir.CausalGame.Public := ⟨c, 3, #[], #[⟨b.pop, target⟩]⟩
  let tape : Whir.CausalGame.Tape c := ⟨E.zero,
    (fun _ => ⟨(fun _ => E.zero), (fun _ _ => E.zero), (fun _ => E.zero), E.zero⟩),
    fun _ => E.zero⟩
  requireIO (!Whir.CausalGame.experiment badPublic (fun _ _ _ => .initial default) tape)
    "malformed public claim accepted"
  IO.println "lean_smoke=honest,multilevel,truncated_lanes,bad_target,short_opening,short_final,bad_final,missing_query,bad_row,bad_ood,missing_ood,missing_challenge,bad_layout,malformed_public_claim"

def ambiguitySmoke : IO Unit := do
  requireIO (Whir.CommitmentAmbiguity.smallSession false).isOk
    "zero branch of immutable spliced commitment rejected"
  requireIO (Whir.CommitmentAmbiguity.smallSession true).isOk
    "one branch of immutable spliced commitment rejected"
  let c := (productionConfig 15 4).getD default
  let block := 2^(c.logN-c.folds[0]!)
  let mixed := tab (2^(c.logN-c.folds[0]!+c.rates[0]!)) fun q =>
    #[if q % 2 == 0 then E.zero else E.one]
  let weight := tab (2^c.logN) fun i => if i == 0 then E.one else E.zero
  for branch in #[false,true] do
    let ch : Challenges := ⟨tab c.folds.size (fun i =>
      let n := c.logN-(c.folds.toList.take (i+1)).sum
      let depth := n+c.rates[i]!
      let per := 192/depth
      let chunks := (c.queries[i]!+per-1)/per
      let raw := if i == 0 && branch then
        (List.range per).foldl (fun out j => out+2^(j*depth)) 0 else 0
      let squeeze : E := ⟨UInt64.ofNat raw, UInt64.ofNat (raw/2^64),
        UInt64.ofNat (raw/2^128)⟩
      ⟨tab c.folds[i]! (fun _ => fixture (i+1)),
        tab (if i+1 < c.folds.size then c.oodCounts[i+1]! else 0)
          (fun _ => tab n (fun j => fixture (20+i+j))),
        tab chunks (fun _ => squeeze), fixture (60+i)⟩),
      tab (c.logN-c.folds.toList.sum) (fun j => fixture (80+j))⟩
    let target := if branch then E.one else E.zero
    let witness := tab block fun i => if branch && i == 0 then (1 : K) else 0
    let (_, proof) ← match prove c ch witness weight target with
      | .ok result => pure result
      | .error e => throw (IO.userError ("production splice prover: " ++ e))
    requireIO (verify c ch 1 mixed weight target proof).isOk
      "production immutable splice branch rejected"
  IO.println "ambiguity_smoke=same_immutable_root,incompatible_claims,small_kernel_fixture,production_15_rate4,both_sessions_accepted"

def vectors : IO Unit := do
  emitN "kmul" (tab 40 fun i => (kmul (seed i) (seed (i+41))).toNat)
  emitN "kinv" (tab 12 fun i => (kinv (seed i)).toNat)
  emitE "emul" (tab 32 fun i => fixture i * fixture (i+33))
  emitE "eq" (eqTable (tab 4 fixture))
  emitN "roots" ((subspaceRoots 8).map UInt64.toNat)
  for lanes in #[1,3,4] do
    let w := tab (lanes*8) seed
    emitE s!"base_{lanes}" ((encodeBase w 5 2 1).flatten)
  let f := tab 32 fixture
  emitE "ext" ((encodeExt f 5 2 1).flatten)
  let r := fixture 70
  emitE "lane_fold" (foldLane f 8 r)
  emitE "low_fold" (foldLow f r)
  let rs := tab 5 fixture
  emitE "rotation" (rotatePoint 2 rs)
  emitE "rotation_mle" #[mle f (rotatePoint 2 rs)]
  let qs := #[0, 5, 5, 13]
  let ws := powers (fixture 80) qs.size
  let point := tab 3 fixture
  let b := induced 3 qs ws
  requireIO (mle b point == inducedAt 3 qs ws point) "dense/succinct induced disagreement"
  emitE "induced" b
  emitE "induced_at" #[inducedAt 3 qs ws point]
  for rate in [1:5] do
    for n in [15:29] do
      let c := (productionConfig n rate).getD default
      requireIO c.valid "invalid production configuration"
      emitN s!"config_{n}_{rate}" (c.folds ++ c.rates ++ c.queries ++ c.oodCounts)
  for (n, rate) in #[(14,1), (29,1), (15,0), (15,5)] do
    requireIO (productionConfig n rate).isNone "unsupported production configuration accepted"

def parseNat (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError ("invalid natural: " ++ s))

def main (args : List String) : IO Unit := do
  match args with
  | "query" :: d :: count :: limbs =>
    let depth ← parseNat d
    let count ← parseNat count
    let ns ← limbs.toArray.mapM parseNat
    requireIO (ns.size % 3 == 0) "query requires triples of limbs"
    let squeezes := tab (ns.size/3) fun i => E.mk (UInt64.ofNat ns[3*i]!) (UInt64.ofNat ns[3*i+1]!) (UInt64.ofNat ns[3*i+2]!)
    match deriveQueries depth count squeezes with
    | none => throw (IO.userError "malformed query challenge vector")
    | some qs => emitN "queries" qs
  | ["ambiguity"] => ambiguitySmoke
  | [] => vectors; smoke
  | _ => throw (IO.userError "usage: whirModel [ambiguity | query DEPTH COUNT LIMB ...]")
