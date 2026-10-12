module

public import LeanVMCircuits.Rec.LateSound

@[expose] public section

/-!
The round theorems' premises can all hold.

`sumcheck_test_sound` and `odd_test_sound` quantify over the prover's answers to every challenge vector. As first
stated, the answers had to compress at every hash row, the squeezes included, and to agree on what is absorbed before
each challenge whenever the challenges before it agree; the challenge, a compression of what is absorbed, then agreed
too, so no answers existed once `E` has two elements and both theorems were vacuous. They now ask for answers in the
random-oracle view (`RomAnswers`: squeezes relaxed, each challenge a seed one step after the block it reads), and
these lemmas exhibit answers meeting every premise but the circuit's acceptance, on a circuit whose challenges are
squeezes of its transcript's blocks. `top_test_sound` and `whir_test_sound` take answers in the same view.

The circuit (`state`): four `HASH` rows tagged at the duplex's output role, the first and third read as absorb blocks
(`transcript`), the second and fourth as the squeezes drawing `λ` (wire 16, from block 0) and the next challenge (wire
22, from block 1). The sumcheck (`sumcheck`) has one round reading the first block's words; the odd layer (`odd`) and
the top layer (`top`, whose last challenge is wire 23) have one value; the WHIR sumcheck (`whir`) has one fold round.
`sumcheck_answers_exist`, `odd_answers_exist`, `top_answers_exist` and `whir_answers_exist` give answers whose
challenges are any vector, which the first statement could not; `pow_answers_exist` gives proof-of-work answers whose
trial words are uniform.
-/

namespace LeanVMCircuits.Rec.Bind.RomExample

open LeanVMCircuits.Rec Model Sumcheck Polynomial Finset

/-- The duplex's output role, as a counter word. -/
def outTag : ℕ := 6 * 2 ^ 56

/-- A `HASH` row reading chaining value `h` and writing `o`, its counter wire 1, its message wires 8 to 15. -/
def row (h o : ℕ) : List ℕ := [h, 1, 2, 3, 4, 5, o, 7, 8, 9, 10, 11, 12, 13, 14, 15]

def state : State where
  next := 24
  hash := #[row 0 6, row 6 16, row 6 21, row 21 22]
  pub := #[(1, .const [outTag, 0, 0, 0])]

def transcript : Transcript where
  blocks := [0, 2]
  firings := #[]
  squeezes := [1, 3]

def round : RoundCert where
  coeffs := [8, 9]
  weight := none
  tailZero := 0
  tailAt := []
  fixedAt := 0
  chal := 16
  hornerZero := 0
  hornerAt := []
  chalAt := 0
  words := []
  time := 1

def sumcheck : SumcheckCert where
  claim0 := 17
  rounds := [round]
  deg := 1
  test := 0
  final := 18
  transcript := 0

def odd : OddCert where
  values := [17]
  lam := ⟨16, 0, [], 1⟩
  claimZero := 0
  claimAt := []
  lefts := []
  rights := []
  prodAt := []
  expZero := 0
  expAt := []
  test := 0
  next := ⟨22, 0, [], 2⟩
  sumAt := []
  outAt := []
  transcript := 0

def top : TopCert where
  values := [17]
  lam := ⟨16, 0, [], 1⟩
  claimZero := 0
  claimAt := []
  kids := []
  prodAt := []
  expZero := 0
  expAt := []
  test := 0
  low := ⟨22, 0, [], 2⟩
  high := ⟨23, 0, [], 2⟩
  lineAt := []
  transcript := 0

def whirRound : WhirRound := .fold (.recv 17 8 9 0 0 0) ⟨16, 0, [], 1⟩ 0 0

def whir : WhirCert where
  claim0 := 17
  rounds := [whirRound]
  test := 0
  final := 18
  transcript := 0

def powCert : PowCert where
  compressAt := 0
  dkAt := 0
  splitAt := 0
  bits := 0
  testAt := []

def cert : Cert where
  rules := {}
  nodes := 0
  isTest := #[]
  claims := #[]
  transcripts := [transcript]
  calls := #[]
  relax := #[]
  pools := #[]
  prods := #[]
  points := #[]
  covers := #[]
  sumchecks := #[sumcheck]
  pows := #[powCert]
  odds := #[odd]
  tops := #[top]
  whirs := #[whir]

/-- Limbs of an element of `E`. -/
noncomputable def limbsE (e : E) : Fin 4 → K := fun i =>
  match i with
  | 0 => (toE_surjective e).choose
  | 1 => (toE_surjective e).choose_spec.choose
  | 2 => (toE_surjective e).choose_spec.choose_spec.choose
  | 3 => 0

theorem ev_limbsE (val : Val) (w : ℕ) (e : E) (h : val w = limbsE e) : Model.ev val w = e := by
  rw [Model.ev, h]
  exact (toE_surjective e).choose_spec.choose_spec.choose_spec

/-- The answer to challenges `a` (`λ`) and `b` (the next): the counter its constant, the challenges theirs, the value
and the input claim one, every other wire zero. -/
noncomputable def answer (a b : E) : Val := fun w =>
  if w = 1 then limbsOf [outTag, 0, 0, 0] else if w = 16 then limbsE a else if w = 22 then limbsE b
  else if w = 17 then limbsE 1 else fun _ => 0

/-- The answer to challenges `a`, `b` and `d`, the third at wire 23. -/
noncomputable def answer3 (a b d : E) : Val := fun w => if w = 23 then limbsE d else answer a b w

/-- The transcript's random-oracle view drops every row: its two absorb blocks and its two squeezes. -/
theorem dropped_rows : ∀ r ∈ state.hash, dropOf state (cert.transcripts.getD 0 default) r = true := by
  intro r hr
  simp only [state, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

theorem rom {ι : Type} (st : ι → ℕ → Fin 4 → K) (val : ι → Val) (hpub : ∀ r, val r 1 = limbsOf [outTag, 0, 0, 0]) :
    RomAnswers cert state 0 st val where
  holds r := {
    unions := fun p hp => by simp [keepP, keep, state] at hp
    emul := fun _ hp => by simp [keepP, keep, state] at hp
    exk := fun _ hp => by simp [keepP, keep, state] at hp
    hash := fun x hx => by
      simp only [keepP] at hx
      obtain ⟨hm, hs⟩ := Array.mem_filter.mp hx
      rw [dropped_rows x hm] at hs
      exact absurd hs (by decide)
    split := fun _ hp => by simp [keepP, keep, state] at hp
    cast := fun _ hp => by simp [keepP, keep, state] at hp
    pub := fun w src hp => by
      simp only [keepP, keep, state, List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact hpub r }
  facts _ := fun j hj => absurd hj (by simp [cert])
  cr _ _ := fun x hx _ _ hs => absurd (dropped_rows x hx) (by rw [hs]; decide)
  win _ _ := fun x hx _ _ hs => absurd (dropped_rows x hx) (by rw [hs]; decide)
  unions _ _ := fun uc hu => by simp [cert] at hu

/-- What the simp sets need to compute a seed list. -/
theorem chalSeeds_eq : chalSeeds state transcript = [(2, 64), (2, 65), (2, 66), (2, 67), (3, 88), (3, 89), (3, 90), (3, 91)] := by
  simp [chalSeeds, transcript, state, row, isSqueezeRow, outTag, readsBlock, hashOut, colNode, hashSrc, limb,
    List.findIdx?_cons, List.range_succ]

theorem seeds_one : seedsBefore state transcript 1 = [32, 36, 40, 44, 48, 52, 56, 60] := by
  rw [seedsBefore, chalSeeds_eq]
  simp [absorbed, wordsOf, transcript, state, row, limb, List.range_succ]

theorem seeds_two : seedsBefore state transcript 2 =
    [32, 36, 40, 44, 48, 52, 56, 60, 32, 36, 40, 44, 48, 52, 56, 60, 64, 65, 66, 67] := by
  rw [seedsBefore, chalSeeds_eq]
  simp [absorbed, wordsOf, transcript, state, row, limb, List.range_succ]

/-- The honest instance of one round: the zero polynomial, ending at zero. -/
noncomputable def inst : Inst E 1 := .node none 0 fun _ => .leaf 0

/-- Answers meeting every premise of `sumcheck_test_sound` but acceptance, at every challenge vector. -/
theorem sumcheck_answers_exist :
    ∃ (c : Cert) (s : State) (sc : SumcheckCert) (I : Inst E sc.rounds.length)
      (st : (Fin sc.rounds.length → E) → ℕ → Fin 4 → K) (val : (Fin sc.rounds.length → E) → Val),
      sc ∈ c.sumchecks ∧ 0 < sc.rounds.length ∧ I.ok sc.deg ∧ SumcheckAnswers c s sc I st val := by
  have h0 : ∀ i : Fin sumcheck.rounds.length, i = ⟨0, by decide⟩ := fun i =>
    Fin.ext (by have := i.isLt; simp [sumcheck] at this; omega)
  refine ⟨cert, state, sumcheck, inst, fun _ _ _ => 0, fun r => answer (r ⟨0, by decide⟩) 0, by simp [cert],
    by decide, ⟨by simp, fun r => ⟨by simp [Inst.sum], trivial⟩⟩, ?_⟩
  refine ⟨rom _ _ fun r => by simp [answer], fun r r' i _ m hm => ?_, fun r i => ?_, fun r i => ?_,
    fun h => absurd h (by decide), fun r => ?_⟩
  · obtain rfl := h0 i
    rw [show (sumcheck.rounds.getD 0 default).time = 1 from rfl,
      show cert.transcripts.getD sumcheck.transcript default = transcript from rfl, seeds_one] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nu, answer]
  · obtain rfl := h0 i
    exact ev_limbsE _ 16 _ (by simp [answer, sumcheck, round])
  · obtain rfl := h0 i
    rfl
  · rw [show sumcheck.claim0 = 17 from rfl, ev_limbsE _ 17 1 (by simp [answer])]
    simp [inst, Inst.sum, lin]

/-- Answers meeting every premise of `odd_test_sound` but acceptance, at every challenge pair, with true children
zero. -/
theorem odd_answers_exist :
    ∃ (c : Cert) (s : State) (oc : OddCert) (L R : ℕ → E) (st : (Fin 2 → E) → ℕ → Fin 4 → K)
      (val : (Fin 2 → E) → Val), oc ∈ c.odds ∧ OddAnswers c s oc L R st val := by
  refine ⟨cert, state, odd, fun _ => 0, fun _ => 0, fun _ _ _ => 0, fun r => answer (r 0) (r 1), by simp [cert], ?_⟩
  refine ⟨rom _ _ fun r => by simp [answer], fun r r' m hm => ?_, fun r r' h0 m hm => ?_, fun r => ⟨?_, ?_⟩,
    fun r => ⟨0, by simp [OddCert.m, odd], ?_⟩⟩
  · rw [show odd.lam.time = 1 from rfl, show cert.transcripts.getD odd.transcript default = transcript from rfl,
      seeds_one] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nu, answer]
  · rw [show odd.next.time = 2 from rfl, show cert.transcripts.getD odd.transcript default = transcript from rfl,
      seeds_two] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp [nu, answer, h0]
  · exact ev_limbsE _ 16 _ (by simp [answer])
  · exact ev_limbsE _ 22 _ (by simp [answer])
  · rw [show odd.values.getD 0 0 = 17 from rfl, ev_limbsE _ 17 1 (by simp [answer])]
    simp

/-- Answers meeting every premise of `top_test_sound` but acceptance, at every challenge triple, with true children
zero. -/
theorem top_answers_exist :
    ∃ (c : Cert) (s : State) (tc : TopCert) (T : ℕ → ℕ → E) (st : (Fin 3 → E) → ℕ → Fin 4 → K)
      (val : (Fin 3 → E) → Val), tc ∈ c.tops ∧ TopAnswers c s tc T st val := by
  refine ⟨cert, state, top, fun _ _ => 0, fun _ _ _ => 0, fun r => answer3 (r 0) (r 1) (r 2), by simp [cert], ?_⟩
  refine ⟨rom _ _ fun r => by simp [answer3, answer], fun r r' m hm => ?_, fun r r' h0 m hm => ?_,
    fun r => ⟨?_, ?_, ?_⟩, fun r => ⟨0, by simp [TopCert.m, top], ?_⟩⟩
  · rw [show top.lam.time = 1 from rfl, show cert.transcripts.getD top.transcript default = transcript from rfl,
      seeds_one] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nu, answer3, answer]
  · rw [show top.low.time = 2 from rfl, show cert.transcripts.getD top.transcript default = transcript from rfl,
      seeds_two] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp [nu, answer3, answer, h0]
  · exact ev_limbsE _ 16 _ (by simp [answer3, answer])
  · exact ev_limbsE _ 22 _ (by simp [answer3, answer])
  · exact ev_limbsE _ 23 _ (by simp [answer3])
  · rw [show top.values.getD 0 0 = 17 from rfl, ev_limbsE _ 17 1 (by simp [answer3, answer])]
    simp

/-- Answers meeting every premise of `whir_test_sound` but acceptance, at every challenge vector. -/
theorem whir_answers_exist :
    ∃ (c : Cert) (s : State) (wc : WhirCert) (I : Inst E wc.rounds.length)
      (st : (Fin wc.rounds.length → E) → ℕ → Fin 4 → K) (val : (Fin wc.rounds.length → E) → Val),
      wc ∈ c.whirs ∧ 0 < wc.rounds.length ∧ I.ok wc.deg ∧ WhirAnswers c s wc I st val := by
  have h0 : ∀ i : Fin whir.rounds.length, i = ⟨0, by decide⟩ := fun i =>
    Fin.ext (by have := i.isLt; simp [whir] at this; omega)
  refine ⟨cert, state, whir, inst, fun _ _ _ => 0, fun r => answer (r ⟨0, by decide⟩) 0, by simp [cert],
    by decide, ⟨by simp, fun r => ⟨by simp [Inst.sum], trivial⟩⟩, ?_⟩
  refine ⟨rom _ _ fun r => by simp [answer], fun r r' i _ m hm => ?_, fun r i => ?_, fun r i => ?_, fun r => ?_⟩
  · obtain rfl := h0 i
    rw [show (whir.rounds.getD 0 default).chal.time = 1 from rfl,
      show cert.transcripts.getD whir.transcript default = transcript from rfl, seeds_one] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nu, answer]
  · obtain rfl := h0 i
    exact ev_limbsE _ 16 _ (by simp [answer, whir, whirRound])
  · obtain rfl := h0 i
    rfl
  · rw [show whir.claim0 = 17 from rfl, ev_limbsE _ 17 1 (by simp [answer])]
    simp [inst, Inst.sum, lin]

/-- Proof-of-work answers meeting every premise of `pow_test_sound` but acceptance: one trial, whose word is each
outcome. -/
theorem pow_answers_exist :
    ∃ (c : Cert) (pc : PowCert) (wd : ℕ → Fin (2 ^ 64) → Fin (2 ^ 64)) (qOf : Fin (2 ^ 64) → ℕ)
      (st : Fin (2 ^ 64) → ℕ → Fin 4 → K) (val : Fin (2 ^ 64) → Val), pc ∈ c.pows ∧
      (∀ q < 1, ∀ v : Fin (2 ^ 64), 2 ^ 64 * #{ω | wd q ω = v} = Fintype.card (Fin (2 ^ 64))) ∧
      (∀ ω, qOf ω < 1) ∧ (∀ ω, Facts c.calls c.relax c.outs (st ω) (val ω)) ∧
      ∀ ω, toWord (val ω (PowCert.trial c.outs pc) 0) = (wd (qOf ω) ω).val := by
  refine ⟨cert, powCert, fun _ ω => ω, fun _ => 0, fun _ _ _ => 0, fun ω _ _ => ofWord ω.val, by simp [cert],
    fun q _ v => ?_, fun _ => by norm_num, fun _ j hj => absurd hj (by simp [cert]), fun ω => toWord_ofWord _ ω.isLt⟩
  rw [show ({ω | ω = v} : Finset (Fin (2 ^ 64))) = {v} by ext; simp, card_singleton, Fintype.card_fin]
  ring

end LeanVMCircuits.Rec.Bind.RomExample
