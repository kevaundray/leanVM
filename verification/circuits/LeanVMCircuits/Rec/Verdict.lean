module

public import LeanVMCircuits.Rec.UnionRows

@[expose] public section

/-!
The checker's verdict on a recursion circuit.

`Cert.accepts`: every rule is justified, every transcript is a chain of compressions, the unions' rows are where the
certificate says (`Cert.unionsOk`), and for every test some transcript's `certify` marks both its wires.

- `checkbind_sound`: each test's wires are in the closure of one transcript's absorbed words and the statement.
- `unionsValid`: on two assignments holding every constraint but the tests, under collision resistance of the
  compression, the union products are functions of their inputs.
- `tests_determined`: on two such assignments, under collision resistance of the compression and of the duplex's
  output window, agreeing on that transcript's absorbed words and the statement, each test's wires agree: a test is a
  function of what the transcript absorbs.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model

attribute [local irreducible] LeanVMCircuits.Blake2s.program

/-! The verdict. -/

/-- A transcript: its absorb blocks as `HASH` row indices in order, and the firings that bind its tests. -/
structure Transcript where
  blocks : List ℕ
  firings : Array ℕ
  deriving Inhabited

/-- The words the blocks absorb, as nodes. -/
def absorbed (s : State) (blocks : List ℕ) : List ℕ :=
  blocks.flatMap fun k => (List.range 8).map fun j => limb ((s.hash.getD k []).getD (8 + j) 0) 0

/-- The statement's nodes. -/
def statementNodes (s : State) : List ℕ :=
  s.pub.toList.flatMap fun e => match e.2 with
    | .statement _ => limbs4 e.1
    | .const _ => []

/-- A transcript's seeds: what its blocks absorb, and the statement. -/
def seedsOf (s : State) (blocks : List ℕ) : List ℕ := absorbed s blocks ++ statementNodes s

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

/-- What `CheckBind` claims of a circuit: its justified rules, which equalities are tests, the union products, and
its transcripts; and to read the unions' rows, the calls that built it, the calls whose equality is a test, and where
each union's pools and products are. -/
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

def Cert.test (c : Cert) (u : ℕ) : Bool := c.isTest.getD u false

/-- Each transcript with the nodes its firings mark. -/
def Cert.marks (c : Cert) (s : State) : List (Transcript × Array Bool) :=
  c.transcripts.map fun t => (t, certify c.rules c.nodes (seedsOf s t.blocks) t.firings)

/-- The unions' rows: the calls replayed with the tests' equalities relaxed build the circuit without its tests, each
product's pool and product calls are where the certificate says, and the claims are the products'. -/
def Cert.unionsOk (c : Cert) (s : State) : Bool :=
  match replayR c.calls c.relax 0 {} #[] with
  | none => false
  | some (t, os) => sameSat (keep s c.test) t &&
      c.claims == c.prods.map (fun qc => qc.claim os (c.pools.getD qc.pool default)) &&
      c.prods.all fun qc => (c.pools.getD qc.pool default).ok os c.calls c.relax &&
        qc.ok os (c.pools.getD qc.pool default) c.calls c.relax

/-- The verdict: every rule is justified, every transcript is a chain, the unions' rows are certified, and some
transcript marks every test's wires. -/
def Cert.accepts (c : Cert) (s : State) : Bool :=
  rulesOk s c.test c.claims c.rules && c.transcripts.all (fun t => chainOk s t.blocks) && c.unionsOk s &&
    let ms := c.marks s
    (List.range s.unions.size).all fun u => !c.test u || match s.unions[u]? with
      | some (a, b) => ms.any fun m => (limbs4 a ++ limbs4 b).all (m.2.getD · false)
      | none => true

/-- A passing verdict: every rule is justified, and each test's wires are in the closure of one transcript's absorbed
words and the statement. -/
theorem checkbind_sound (c : Cert) (s : State) (h : c.accepts s = true) :
    rulesOk s c.test c.claims c.rules = true ∧
    ∀ u a b, s.unions[u]? = some (a, b) → c.test u = true →
      ∃ t ∈ c.transcripts, chainOk s t.blocks = true ∧
        ∀ n ∈ limbs4 a ++ limbs4 b, Closure c.rules (seedsOf s t.blocks) n := by
  simp only [Cert.accepts, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hr, hc⟩, -⟩, ht⟩ := h
  refine ⟨hr, fun u a b hab htu => ?_⟩
  have hu : u < s.unions.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hab
    simp at hab
  have := ht u hu
  rw [htu, hab] at this
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.all_eq_true, Cert.marks, List.mem_map] at this
  obtain ⟨_, ⟨t, htm, rfl⟩, hall⟩ := this
  exact ⟨t, htm, hc t htm, fun n hn => certify_sound _ _ _ _ n (hall n hn)⟩


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
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
    obtain ⟨⟨hsame, hcl⟩, hall⟩ := h
    obtain ⟨-, -, -, hfacts⟩ := replayR_sound c.calls c.relax 0 {} #[] t os inv_empty rfl (Nat.zero_le _)
      (fun j hj => absurd hj (Nat.not_lt_zero j)) hr
    have hsat : Sat st t val := sat_of_sameSat hsame hv
    have hsat' : Sat st' t val' := sat_of_sameSat hsame hv'
    have hF : Facts c.calls c.relax os st val := fun j hj hrl => (hfacts j hj hj).1 st val hsat hrl
    have hF' : Facts c.calls c.relax os st' val' := fun j hj hrl => (hfacts j hj hj).1 st' val' hsat' hrl
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
the duplex's output window, a test's wires are a function of one transcript's absorbed words and the statement. -/
theorem tests_determined {st st' : ℕ → Fin 4 → K} {val val' : Val} (c : Cert) (s : State) (h : c.accepts s = true)
    (hv : Holds st s c.test val) (hv' : Holds st' s c.test val') (hcr : HashCR s val val')
    (hw : WindowCR s val val') {u a b : ℕ}
    (hab : s.unions[u]? = some (a, b)) (ht : c.test u = true) :
    ∃ t ∈ c.transcripts, chainOk s t.blocks = true ∧
      ((∀ n ∈ seedsOf s t.blocks, nu val n = nu val' n) → val a = val' a ∧ val b = val' b) := by
  obtain ⟨hr, hall⟩ := checkbind_sound c s h
  have hu : UnionsValid c.claims val val' := by
    simp only [Cert.accepts, Bool.and_eq_true] at h
    exact unionsValid c s h.1.2 hv hv' hcr
  obtain ⟨t, htm, hch, hcl⟩ := hall u a b hab ht
  refine ⟨t, htm, hch, fun hs => ?_⟩
  have key : ∀ n ∈ limbs4 a ++ limbs4 b, nu val n = nu val' n :=
    fun n hn => closure_agree (rules_valid hr hv hv' hcr hw hu) hs (hcl n hn)
  exact ⟨eq_of_limbs4 fun n hn => key n (List.mem_append_left _ hn),
    eq_of_limbs4 fun n hn => key n (List.mem_append_right _ hn)⟩

end LeanVMCircuits.Rec.Bind
