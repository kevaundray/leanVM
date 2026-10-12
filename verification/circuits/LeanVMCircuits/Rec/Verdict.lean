module

public import LeanVMCircuits.Rec.UnionRows
public import LeanVMCircuits.Rec.Rounds

@[expose] public section

/-!
The checker's verdict on a recursion circuit.

`Cert.accepts`: every rule is justified, every transcript is a chain of compressions, the unions' rows are where the
certificate says (`Cert.unionsOk`), every field equality reading a challenge is a test, for every test some
transcript's `certifyT` gives both its wires a binding time, each union's coverage entry holds (`Cert.coversOk`), and
each named sumcheck's rounds, proof-of-work check and GKR odd layer are where the certificate says
(`Cert.sumchecksOk`, `PowCert.ok`, `Cert.oddsOk`).

- `tests_by`: each test's wires, at their binding time `k`, are in the closure of what one transcript's first `k`
  blocks absorb, and of the statement only once `k` passes its last block; `checkbind_sound` is its weaker form.
- `unionsValid`: on two assignments holding every constraint but the tests, under collision resistance of the
  compression, the union products are functions of their inputs.
- `tests_determined`: on two such assignments, under collision resistance of the compression and of the duplex's
  output window, agreeing on what that transcript's first `k` blocks absorb (and the statement past its last block),
  each test's wires agree.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model

attribute [local irreducible] LeanVMCircuits.Blake2s.program


/-! Which equalities are tests. -/

/-- An equality made outside the builder's methods between field elements: `eq_e`, `eq_k`, `eq_e_const`,
`eq_k_const`. -/
def _root_.LeanVMCircuits.Rec.Model.Call.isFieldEq : Call → Bool
  | .eqE .. | .eqK .. | .eqConstE .. | .eqConstK .. => true
  | _ => false

/-- One call of the scan for wires that read a challenge: the call reads one if it is a squeeze or reads a wire that
does, and so does each wire it makes, but a constant. -/
def taintStep (c : Call) (relax : Bool) (s : State) (tw : Array Bool) : State × Array Bool :=
  let g := c.isSqueeze || c.args.any (tw.getD · false)
  let s' := ((c.execR relax).run s).2
  let isConst := fun w => (s'.pub.extract s.pub.size s'.pub.size).any fun p => p.1 == w && match p.2 with
    | .const _ => true
    | .statement _ => false
  (s', (List.range (s'.next - s.next)).foldl (fun t k => t.push (g && !isConst (s.next + k))) tw)

/-- The scan before call `i`: the state, and whether each wire reads a challenge. -/
def taintUpTo (calls : Array Call) (relax : Array Bool) : ℕ → State × Array Bool
  | 0 => ({}, #[])
  | i + 1 => taintStep (calls.getD i .zero) (relax.getD i false) (taintUpTo calls relax i).1
    (taintUpTo calls relax i).2

/-- The scan from call `i`, checking each field equality the replay keeps reads no challenge. -/
def taintOk (calls : Array Call) (relax : Array Bool) (i : ℕ) (s : State) (tw : Array Bool) : Bool :=
  if h : i < calls.size then
    let c := calls[i]
    if c.isFieldEq && !relax.getD i false && c.args.any (tw.getD · false) then false
    else
      let r := taintStep c (relax.getD i false) s tw
      taintOk calls relax (i + 1) r.1 r.2
  else true
termination_by calls.size - i

theorem taintOk_sound (calls : Array Call) (relax : Array Bool) :
    ∀ i, i ≤ calls.size → taintOk calls relax i (taintUpTo calls relax i).1 (taintUpTo calls relax i).2 = true →
      ∀ j, i ≤ j → j < calls.size → (calls.getD j .zero).isFieldEq = true → relax.getD j false = false →
        ∀ a ∈ (calls.getD j .zero).args, (taintUpTo calls relax j).2.getD a false = false := by
  intro i hi h
  induction h' : calls.size - i generalizing i with
  | zero => intro j hj hj'; omega
  | succ d ih =>
    have hlt : i < calls.size := by omega
    rw [taintOk, dif_pos hlt] at h
    intro j hj hjs hfe hrl a ha
    have hget : calls[i] = calls.getD i .zero := by simp [Array.getD_eq_getD_getElem?, hlt]
    dsimp only at h
    split at h
    · simp at h
    · rename_i hc
      rcases Nat.eq_or_lt_of_le hj with hij | hj
      · subst hij
        rw [← hget] at hfe ha
        simp only [hfe, hrl, Bool.not_false, Bool.true_and, Bool.and_true, List.any_eq_true, not_exists, not_and,
          Bool.not_eq_true] at hc
        exact hc a ha
      · have h1 : taintOk calls relax (i + 1) (taintUpTo calls relax (i + 1)).1
            (taintUpTo calls relax (i + 1)).2 = true := by
          simp only [taintUpTo, ← hget]; exact h
        exact ih (i + 1) (by omega) h1 (by omega) j (by omega) hjs hfe hrl a ha

/-! The verdict. -/

/-- A transcript: its absorb blocks as `HASH` row indices in order, the firings that bind its tests, and its squeezes
as `HASH` row indices. -/
structure Transcript where
  blocks : List ℕ
  firings : Array ℕ
  squeezes : List ℕ := []
  /-- The firings that bind with `Cert.rulesRO`, the random-oracle view's rules. -/
  firingsRO : Array ℕ := #[]
  deriving Inhabited

/-- The words block `k` absorbs, as nodes. -/
def wordsOf (s : State) (k : ℕ) : List ℕ := (List.range 8).map fun j => limb ((s.hash.getD k []).getD (8 + j) 0) 0

/-- The words the blocks absorb, as nodes. -/
def absorbed (s : State) (blocks : List ℕ) : List ℕ := blocks.flatMap (wordsOf s)

/-- The statement's nodes. -/
def statementNodes (s : State) : List ℕ :=
  s.pub.toList.flatMap fun e => match e.2 with
    | .statement _ => limbs4 e.1
    | .const _ => []

/-- The place among `blocks` of the block whose output is a row's chaining value. -/
def readsBlock (s : State) (blocks : List ℕ) (row : List ℕ) : Option ℕ :=
  blocks.findIdx? fun b => (s.hash.getD b []).getD 6 0 == row.getD 0 0

/-- A transcript's challenges with their times: each of its squeeze rows' outputs, the random oracle's answer, one
after the number of blocks its chaining value needs. A challenge is so a seed of what is absorbed after it, and not of
the round that draws it. -/
def chalSeeds (s : State) (t : Transcript) : List (ℕ × ℕ) :=
  t.squeezes.flatMap fun k =>
    match isSqueezeRow s (s.hash.getD k []), readsBlock s t.blocks (s.hash.getD k []) with
    | true, some i => (hashOut (s.hash.getD k [])).map ((i + 2), ·)
    | _, _ => []

/-- A transcript's seeds: what its blocks absorb, its challenges, and the statement. -/
def seedsOf (s : State) (t : Transcript) : List ℕ :=
  absorbed s t.blocks ++ (chalSeeds s t).map (·.2) ++ statementNodes s

/-- A transcript's seeds with their times: block `i`'s words at `i + 1`, a challenge one after the block it reads,
the statement after the last block. -/
def seedsT (s : State) (t : Transcript) : List (ℕ × ℕ) :=
  (List.range t.blocks.length).flatMap (fun i => (wordsOf s (t.blocks.getD i 0)).map ((i + 1), ·)) ++ chalSeeds s t ++
    (statementNodes s).map ((t.blocks.length + 1), ·)

/-- What a transcript's first `k` blocks absorb, the challenges seeded by `k`, and the statement once `k` passes its
last block. -/
def seedsBefore (s : State) (t : Transcript) (k : ℕ) : List ℕ :=
  absorbed s (t.blocks.take k) ++ ((chalSeeds s t).filter (·.1 ≤ k)).map (·.2) ++
    if t.blocks.length < k then statementNodes s else []

theorem seedsBy_seedsT {s : State} {t : Transcript} {k : ℕ} :
    ∀ n ∈ seedsBy (seedsT s t) k, n ∈ seedsBefore s t k := by
  intro n hn
  simp only [seedsBy, seedsT, List.mem_map, List.mem_filter, List.mem_append, List.mem_flatMap, List.mem_range,
    decide_eq_true_eq] at hn
  obtain ⟨p, ⟨hp, hk⟩, rfl⟩ := hn
  simp only [seedsBefore, absorbed, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  rcases hp with (⟨i, hi, hp⟩ | hp) | ⟨w, hw, rfl⟩
  · obtain ⟨w, hw, rfl⟩ := hp
    left; left
    refine ⟨t.blocks.getD i 0, ?_, hw⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  · exact Or.inl (Or.inr ⟨p, ⟨hp, hk⟩, rfl⟩)
  · right
    rw [if_pos (by simp only at hk; omega)]
    exact hw

theorem seedsBefore_mono {s : State} {t : Transcript} {k k' : ℕ} (h : k ≤ k') :
    ∀ n ∈ seedsBefore s t k, n ∈ seedsBefore s t k' := by
  intro n hn
  simp only [seedsBefore, absorbed, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hn ⊢
  rcases hn with (⟨b, hb, hn⟩ | ⟨p, ⟨hp, hk⟩, rfl⟩) | hn
  · exact Or.inl (Or.inl ⟨b, (List.take_prefix_take_left h).subset hb, hn⟩)
  · exact Or.inl (Or.inr ⟨p, ⟨hp, by omega⟩, rfl⟩)
  · split at hn
    · rw [if_pos (by omega)]; exact Or.inr hn
    · simp at hn

theorem seedsBefore_seedsOf {s : State} {t : Transcript} {k : ℕ} :
    ∀ n ∈ seedsBefore s t k, n ∈ seedsOf s t := by
  intro n hn
  simp only [seedsBefore, seedsOf, absorbed, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hn ⊢
  rcases hn with (⟨b, hb, hn⟩ | ⟨p, ⟨hp, -⟩, rfl⟩) | hn
  · exact Or.inl (Or.inl ⟨b, List.mem_of_mem_take hb, hn⟩)
  · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
  · split at hn
    · exact Or.inr hn
    · simp at hn

/-- Whether a wire is a constant. -/
def isConst (s : State) (w : ℕ) : Bool :=
  s.pub.any fun e => e.1 == w && match e.2 with
    | .const _ => true
    | .statement _ => false

/-- Each block's chaining value is the previous block's output. -/
def links (s : State) (k : ℕ) : List ℕ → Bool
  | [] => true
  | k' :: ks => k' < s.hash.size && (s.hash.getD k' []).getD 0 0 == (s.hash.getD k []).getD 6 0 && links s k' ks

/-- The blocks are a chain of compressions from a constant chaining value. -/
def chainOk (s : State) : List ℕ → Bool
  | [] => true
  | k :: ks => k < s.hash.size && isConst s ((s.hash.getD k []).getD 0 0) && links s k ks

/-- A union's coverage test: its equality, its two products (the children's selected claims, the declared claims),
and the transcript that draws its point. -/
structure Cover where
  test : ℕ
  sel : ℕ
  decl : ℕ
  transcript : ℕ
  deriving Inhabited, Repr

/-- What `CheckBind` claims of a circuit: its justified rules, which equalities are tests, the union products, and
its transcripts; and to read the unions' rows, the calls that built it, the calls whose equality is a test, where
each union's pools and products are, and each union's coverage test. -/
structure Cert where
  rules : Rules Just
  nodes : ℕ
  isTest : Array Bool
  claims : Array UnionClaim
  transcripts : List Transcript
  calls : Array Call
  relax : Array Bool
  pools : Array PoolCert
  prods : Array ProdCert
  /-- Each product's point. -/
  points : Array PointCert
  covers : Array Cover
  sumchecks : Array SumcheckCert := #[]
  pows : Array PowCert := #[]
  odds : Array OddCert := #[]
  /-- The rules without the squeeze rows (`isSqueezeRow`), which the round certificates bind with. -/
  rulesRO : Rules Just := {}

def Cert.test (c : Cert) (u : ℕ) : Bool := c.isTest.getD u false

/-- The time a transcript's firings bind each node at: the number of its blocks it needs, one more than their number
if it needs the statement. -/
def Cert.times (c : Cert) (s : State) (t : Transcript) : Array (Option ℕ) :=
  certifyT c.rules c.nodes (seedsT s t) t.firings

/-- Each transcript with its times. -/
def Cert.marks (c : Cert) (s : State) : List (Transcript × Array (Option ℕ)) :=
  c.transcripts.map fun t => (t, c.times s t)

/-- The times in the random-oracle view: `rulesRO` and its firings. -/
def Cert.timesRO (c : Cert) (s : State) (t : Transcript) : Array (Option ℕ) :=
  certifyT c.rulesRO c.nodes (seedsT s t) t.firingsRO

/-- Each transcript with its random-oracle times. -/
def Cert.marksRO (c : Cert) (s : State) : List (Transcript × Array (Option ℕ)) :=
  c.transcripts.map fun t => (t, c.timesRO s t)

/-- When a transcript binds two wires: their limbs' latest time. -/
def bindTime (m : Array (Option ℕ)) (a b : ℕ) : Option ℕ := latest m (some 0) (limbs4 a ++ limbs4 b)

/-- Product `i`'s pool. -/
def Cert.poolOf (c : Cert) (i : ℕ) : PoolCert := c.pools.getD (c.prods.getD i default).pool default

/-- The unions' rows, given the replay with the tests' equalities relaxed: it builds the circuit without its tests,
each product's pool, product and point calls are where the certificate says, and the claims are the products'. -/
def Cert.unionsAt (c : Cert) (s t : State) (os : Array (List ℕ)) : Bool :=
  sameSat (keep s c.test) t &&
    c.claims == c.prods.map (fun qc => qc.claim os (c.pools.getD qc.pool default)) &&
    c.prods.all (fun qc => (c.pools.getD qc.pool default).ok os c.calls c.relax &&
      qc.ok os (c.pools.getD qc.pool default) c.calls c.relax) &&
    (List.range c.prods.size).all fun i => (c.points.getD i default).ok os c.calls c.relax (c.prods.getD i default)

/-- The unions' rows are where the certificate says. -/
def Cert.unionsOk (c : Cert) (s : State) : Bool :=
  match replayR c.calls c.relax 0 {} #[] with
  | none => false
  | some (t, os) => c.unionsAt s t os

/-- The relaxed replay's outputs, which a certificate's wires are read from. -/
def Cert.outs (c : Cert) : Array (List ℕ) :=
  match replayR c.calls c.relax 0 {} #[] with
  | some (_, os) => os
  | none => #[]

/-- Some transcript's marks cover every test's wires. -/
def Cert.testsBound (c : Cert) (s : State) (ms : List (Transcript × Array (Option ℕ))) : Bool :=
  (List.range s.unions.size).all fun u => !c.test u || match s.unions[u]? with
    | some (a, b) => ms.any fun m => (bindTime m.2 a b).isSome
    | none => true

/-- Each product is in a coverage entry, and each entry's equality is a test of its two products' outputs at one
point, whose transcript's marks cover what both pools commit to; the declared pool has one digest and does not select,
and the children's pool's run one-hot closes at its last digest. -/
def Cert.coversOk (c : Cert) (s : State) (os : Array (List ℕ)) (ms : List (Transcript × Array (Option ℕ))) :
    Bool :=
  (List.range c.prods.size).all (fun i => c.covers.any fun cv => cv.sel == i || cv.decl == i) &&
  c.covers.all fun cv => cv.sel < c.prods.size && cv.decl < c.prods.size && cv.transcript < ms.length &&
    c.test cv.test && c.points.getD cv.sel default == c.points.getD cv.decl default &&
    s.unions[cv.test]? == some (ProdCert.out os (c.poolOf cv.sel) (c.prods.getD cv.sel default),
      ProdCert.out os (c.poolOf cv.decl) (c.prods.getD cv.decl default)) &&
    (((c.poolOf cv.sel).committed os ++ (c.poolOf cv.decl).committed os).flatMap limbs4).all
      (fun n => ((ms.getD cv.transcript default).2.getD n none).isSome) &&
    !(c.poolOf cv.decl).selecting && (c.poolOf cv.decl).runs == 1 && (c.poolOf cv.sel).endOk os c.calls c.relax

/-- A challenge is drawn after its transcript's first `time` blocks: its `k_to_e` call reads three words, each a word
of a `d_to_k` of a squeeze whose chaining value is block `time`'s output. -/
def ChalCert.ok (s : State) (os : Array (List ℕ)) (cs : Array Call) (blocks : List ℕ) (cc : ChalCert) : Bool :=
  let wd := fun k => let e := cc.words.getD k default; outAt os e.1 e.2.1
  0 < cc.time && cc.time ≤ blocks.length && outAt os cc.chalAt 0 == cc.chal && cc.words.length == 3 &&
    cs[cc.chalAt]? == some (.kToE (wd 0) (wd 1) (wd 2)) &&
    cc.words.all fun e => cs[e.1]? == some (.dToK (outAt os e.2.2 0)) && match cs[e.2.2]? with
      | some (.leafBlock h _ t _) => t / 2 ^ 56 == 6 && h == (s.hash.getD (blocks.getD (cc.time - 1) 0) []).getD 6 0
      | _ => false

/-- A round's challenge is drawn after its transcript's first `time` blocks. -/
def RoundCert.chalOk (s : State) (os : Array (List ℕ)) (cs : Array Call) (blocks : List ℕ) (rc : RoundCert) : Bool :=
  ChalCert.ok s os cs blocks ⟨rc.chal, rc.chalAt, rc.words, rc.time⟩

/-- Wires a transcript binds by `time`: every limb of their `E` view. -/
def boundBy (m : Array (Option ℕ)) (ws : List ℕ) (time : ℕ) : Bool :=
  (ws.flatMap limbs3).all fun n => match m.getD n none with
    | some k => decide (k ≤ time)
    | none => false

/-- Each GKR odd layer's calls are in the replay, its test is a test of its claim and expected value, its input claims
are bound before `λ` is drawn, and its children before the next challenge is. -/
def Cert.oddsOk (c : Cert) (s : State) (os : Array (List ℕ)) (ms : List (Transcript × Array (Option ℕ))) : Bool :=
  c.odds.all fun oc =>
    let t := ms.getD oc.transcript default
    oc.transcript < ms.length && oc.ok os c.calls c.relax && c.test oc.test &&
      (s.unions[oc.test]? == some (oc.claim os, oc.expected os) ||
        s.unions[oc.test]? == some (oc.expected os, oc.claim os)) &&
      oc.lam.ok s os c.calls t.1.blocks && oc.next.ok s os c.calls t.1.blocks &&
      boundBy t.2 oc.values oc.lam.time &&
      boundBy t.2 ((List.range oc.m).flatMap fun k => [oc.left k, oc.right k]) oc.next.time

/-- What round `i`'s prover sends, its weight, and for the first round the input claim, are bound by the round's
time. -/
def SumcheckCert.boundOk (m : Array (Option ℕ)) (sc : SumcheckCert) (i : ℕ) : Bool :=
  let rc := sc.rounds.getD i default
  ((rc.sent ++ rc.weight.toList ++ (if i = 0 then [sc.claim0] else [])).flatMap limbs3).all fun n =>
    match m.getD n none with
    | some k => decide (k ≤ rc.time)
    | none => false

/-- Each named sumcheck's rounds are in the replay, its test is a test of its last claim, and each round's challenge
is drawn after the blocks binding what the prover sends in it. -/
def Cert.sumchecksOk (c : Cert) (s : State) (os : Array (List ℕ)) (ms : List (Transcript × Array (Option ℕ))) :
    Bool :=
  c.sumchecks.all fun sc => sc.transcript < ms.length && sc.ok os c.calls c.relax && c.test sc.test &&
    (s.unions[sc.test]? == some (sc.claimAt os sc.rounds.length, sc.final) ||
      s.unions[sc.test]? == some (sc.final, sc.claimAt os sc.rounds.length)) &&
    (List.range sc.rounds.length).all fun i =>
      (sc.rounds.getD i default).chalOk s os c.calls (ms.getD sc.transcript default).1.blocks &&
        sc.boundOk (ms.getD sc.transcript default).2 i

/-- The verdict: every rule is justified, every transcript is a chain, the unions' rows are certified, every field
equality reading a challenge is a test, some transcript marks every test's wires, the coverage entries hold, and the
named sumchecks' rounds and proof-of-work checks are certified. -/
def Cert.accepts (c : Cert) (s : State) : Bool :=
  match replayR c.calls c.relax 0 {} #[] with
  | none => false
  | some (t, os) =>
    rulesOk s c.test c.claims (fun _ => false) c.rules && c.transcripts.all (fun t => chainOk s t.blocks) &&
      c.unionsAt s t os && taintOk c.calls c.relax 0 {} #[] &&
      let ms := c.marks s
      let mr := c.marksRO s
      c.testsBound s ms && c.coversOk s os ms && c.sumchecksOk s os mr && c.pows.all (·.ok os c.calls c.relax) &&
        c.oddsOk s os mr && rulesOk s c.test c.claims (isSqueezeRow s) c.rulesRO

theorem Cert.accepts_parts {c : Cert} {s : State} (h : c.accepts s = true) :
    rulesOk s c.test c.claims (fun _ => false) c.rules = true ∧ c.transcripts.all (fun t => chainOk s t.blocks) = true ∧
      c.unionsOk s = true ∧ taintOk c.calls c.relax 0 {} #[] = true ∧ c.testsBound s (c.marks s) = true ∧
      c.coversOk s c.outs (c.marks s) = true := by
  unfold Cert.accepts at h
  unfold Cert.unionsOk Cert.outs
  split at h
  · simp at h
  · rename_i t os hr
    rw [hr]
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hr, hc⟩, hu⟩, ht⟩, ⟨⟨⟨⟨⟨hb, hcv⟩, -⟩, -⟩, -⟩, -⟩⟩ := h
    exact ⟨hr, hc, hu, ht, hb, hcv⟩

theorem Cert.accepts_rounds {c : Cert} {s : State} (h : c.accepts s = true) :
    c.sumchecksOk s c.outs (c.marksRO s) = true ∧ c.pows.all (·.ok c.outs c.calls c.relax) = true ∧
      c.oddsOk s c.outs (c.marksRO s) = true ∧ rulesOk s c.test c.claims (isSqueezeRow s) c.rulesRO = true := by
  unfold Cert.accepts at h
  unfold Cert.outs
  split at h
  · simp at h
  · rename_i t os hr
    rw [hr]
    simp only [Bool.and_eq_true] at h
    exact ⟨h.2.1.1.1.2, h.2.1.1.2, h.2.1.2, h.2.2⟩

/-- A node a transcript binds at time `k` is in the closure of what its first `k` blocks absorb, and of the statement
once `k` passes its last block. -/
theorem Cert.times_sound (c : Cert) (s : State) (t : Transcript) {n k : ℕ}
    (h : (c.times s t).getD n none = some k) : Closure c.rules (seedsBefore s t k) n :=
  (certifyT_sound _ _ _ _ n k h).mono seedsBy_seedsT

/-- The same for the random-oracle view's rules. -/
theorem Cert.timesRO_sound (c : Cert) (s : State) (t : Transcript) {n k : ℕ}
    (h : (c.timesRO s t).getD n none = some k) : Closure c.rulesRO (seedsBefore s t k) n :=
  (certifyT_sound _ _ _ _ n k h).mono seedsBy_seedsT

/-- A passing verdict: every rule is justified, and each test's wires are bound by one transcript at a time `k`: in
the closure of what its first `k` blocks absorb, and of the statement once `k` passes its last block. -/
theorem tests_by (c : Cert) (s : State) (h : c.accepts s = true) :
    rulesOk s c.test c.claims (fun _ => false) c.rules = true ∧
    ∀ u a b, s.unions[u]? = some (a, b) → c.test u = true →
      ∃ t ∈ c.transcripts, chainOk s t.blocks = true ∧ ∃ k, bindTime (c.times s t) a b = some k ∧
        ∀ n ∈ limbs4 a ++ limbs4 b, Closure c.rules (seedsBefore s t k) n := by
  obtain ⟨hr, hc, -, -, ht, -⟩ := Cert.accepts_parts h
  simp only [Cert.testsBound, List.all_eq_true, List.mem_range] at ht hc
  refine ⟨hr, fun u a b hab htu => ?_⟩
  have hu : u < s.unions.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hab
    simp at hab
  have := ht u hu
  rw [htu, hab] at this
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Cert.marks, List.mem_map] at this
  obtain ⟨_, ⟨t, htm, rfl⟩, hk⟩ := this
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hk
  refine ⟨t, htm, hc t htm, k, hk, fun n hn => ?_⟩
  obtain ⟨tn, htn, hle⟩ := (latest_some _ _ _ _ hk).2 n hn
  exact (Cert.times_sound c s t htn).mono (seedsBefore_mono hle)

/-- A passing verdict: every rule is justified, and each test's wires are in the closure of one transcript's absorbed
words and the statement. -/
theorem checkbind_sound (c : Cert) (s : State) (h : c.accepts s = true) :
    rulesOk s c.test c.claims (fun _ => false) c.rules = true ∧
    ∀ u a b, s.unions[u]? = some (a, b) → c.test u = true →
      ∃ t ∈ c.transcripts, chainOk s t.blocks = true ∧
        ∀ n ∈ limbs4 a ++ limbs4 b, Closure c.rules (seedsOf s t) n := by
  obtain ⟨hr, hall⟩ := tests_by c s h
  refine ⟨hr, fun u a b hab htu => ?_⟩
  obtain ⟨t, htm, hch, k, -, hcl⟩ := hall u a b hab htu
  exact ⟨t, htm, hch, fun n hn => (hcl n hn).mono seedsBefore_seedsOf⟩


theorem rows_of_hash {c : Call} {t s : State} {outs : List ℕ} (h : c.Rows t outs) (hh : t.hash = s.hash) :
    c.Rows s outs := by
  cases c
  case hashBlock => simp only [Call.Rows] at h ⊢; rw [← hh]; exact h
  all_goals trivial

/-- The unions' parse uniqueness, from their rows: on two assignments holding every constraint but the tests whose
compressions do not collide, each union product is a function of its claim's inputs. -/
theorem unionsValid {st st' : ℕ → Fin 4 → K} {val val' : Val} (c : Cert) (s : State) (h : c.unionsOk s = true)
    (hv : Holds st s c.test val) (hv' : Holds st' s c.test val') (hcr : HashCR s val val') :
    UnionsValid c.claims val val' := by
  unfold Cert.unionsOk at h
  split at h
  · simp at h
  · rename_i t os hr
    simp only [Cert.unionsAt, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
    obtain ⟨⟨⟨hsame, hcl⟩, hall⟩, -⟩ := h
    obtain ⟨-, -, -, hfacts⟩ := replayR_sound c.calls c.relax 0 {} #[] t os inv_empty rfl (Nat.zero_le _)
      (fun j hj => absurd hj (Nat.not_lt_zero j)) hr
    have hsat : Sat st t val := sat_of_sameSat hsame hv
    have hsat' : Sat st' t val' := sat_of_sameSat hsame hv'
    have hF : Facts c.calls c.relax os st val := fun j hj hrl _ => (hfacts j hj hj).1 st val hsat hrl
    have hF' : Facts c.calls c.relax os st' val' := fun j hj hrl _ => (hfacts j hj hj).1 st' val' hsat' hrl
    have hhash : t.hash = s.hash := by
      simp only [sameSat, Bool.and_eq_true, beq_iff_eq] at hsame
      exact hsame.1.1.1.2.symm
    have hR : RowsIn c.calls os s := fun j hj => rows_of_hash (hfacts j hj hj).2 hhash
    intro uc huc hin
    rw [hcl] at huc
    obtain ⟨qc, hq, rfl⟩ := Array.mem_map.mp huc
    obtain ⟨hp, hqk⟩ := hall qc hq
    exact claim_valid hF hF' hR hp hqk hcr hin

/-- On two assignments holding every constraint but the tests, under collision resistance of the compression and of
the duplex's output window, a test's wires are a function of what one transcript's first `k` blocks absorb, `k` its
binding time, and of the statement once `k` passes the transcript's last block. -/
theorem tests_determined {st st' : ℕ → Fin 4 → K} {val val' : Val} (c : Cert) (s : State) (h : c.accepts s = true)
    (hv : Holds st s c.test val) (hv' : Holds st' s c.test val') (hcr : HashCR s val val')
    (hw : WindowCR s val val') {u a b : ℕ}
    (hab : s.unions[u]? = some (a, b)) (ht : c.test u = true) :
    ∃ t ∈ c.transcripts, chainOk s t.blocks = true ∧ ∃ k, bindTime (c.times s t) a b = some k ∧
      ((∀ n ∈ seedsBefore s t k, nu val n = nu val' n) → val a = val' a ∧ val b = val' b) := by
  obtain ⟨hr, hall⟩ := tests_by c s h
  have hu : UnionsValid c.claims val val' := unionsValid c s (Cert.accepts_parts h).2.2.1 hv hv' hcr
  obtain ⟨t, htm, hch, k, hk, hcl⟩ := hall u a b hab ht
  refine ⟨t, htm, hch, k, hk, fun hs => ?_⟩
  have key : ∀ n ∈ limbs4 a ++ limbs4 b, nu val n = nu val' n :=
    fun n hn => closure_agree (rules_valid hr (hv.toP _) (hv'.toP _) (hcr.toP _) (hw.toP _) hu) hs (hcl n hn)
  exact ⟨eq_of_limbs4 fun n hn => key n (List.mem_append_left _ hn),
    eq_of_limbs4 fun n hn => key n (List.mem_append_right _ hn)⟩

/-- An accepted certificate's tests hold every field equality reading a challenge: no field equality its replay keeps
as a constraint reads a wire the scan marks (`taintStep`: a squeeze's output, or a wire a call makes from one, but a
constant). The kept equalities are the circuit's equalities that are not tests (`Cert.unionsOk`). -/
theorem tests_cover (c : Cert) (s : State) (h : c.accepts s = true) :
    ∀ j < c.calls.size, (c.calls.getD j .zero).isFieldEq = true → c.relax.getD j false = false →
      ∀ a ∈ (c.calls.getD j .zero).args, (taintUpTo c.calls c.relax j).2.getD a false = false := by
  intro j hj
  exact taintOk_sound c.calls c.relax 0 (Nat.zero_le _) (Cert.accepts_parts h).2.2.2.1 j (Nat.zero_le _) hj

end LeanVMCircuits.Rec.Bind
