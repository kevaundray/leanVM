module

public import LeanVMCircuits.Rec.LateSound

@[expose] public section

/-!
A prover's run in the random-oracle model gives the answers the round theorems take.

The round theorems (`sumcheck_test_sound`, `odd_test_sound`, `top_test_sound`, `whir_test_sound`) count challenge
vectors `r` and take the prover's answer at each (`SumcheckAnswers`, ...). A prover in the random-oracle model is
instead an assignment at each oracle `ρ`, the answers at its transcript's squeezes' output words (`Run`): in the
random-oracle view (`RomAnswers`), its squeezes' outputs `ρ`'s answers, and what its first `k` blocks absorb a function
of the answers drawn by `k` (it absorbs a block knowing only the challenges before it).

A certified check's challenges read three words of a squeeze each (`ChalCert.own`). The verdict checks they are drawn
in order from the oracle's words (`Cert.chalsOk`: each word a challenge seed one step after its challenge's time and
at no other time, no word shared, times not decreasing, increasing for WHIR). `oracleAt own ρ r` is `ρ` with challenge
`i`'s words replaced by `r i`'s coordinates; at a fixed `ρ`, the run's assignments at `oracleAt own ρ r` are answers to
the challenge vectors `r` (`Run.sumcheckAnswers`, `Run.oddAnswers`, `Run.topAnswers`, `Run.whirAnswers`). The
substitution is a lens (`readR_oracleAt`, `oracleAt_readR`, `oracleAt_oracleAt`), so a uniform oracle gives uniform
challenges: each round theorem's bound holds as a fraction of the oracles (`sumcheck_run_sound`, `odd_run_sound`,
`top_run_sound`, `whir_run_sound`). `RomExample.run_exists` gives a run meeting every premise but acceptance.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Sumcheck Polynomial Finset

/-! `E` as three coordinates over `K`. -/

noncomputable instance : Fintype E :=
  Fintype.ofSurjective (fun p : K × K × K => toE p.1 p.2.1 p.2.2) fun e => by
    obtain ⟨a, b, c, h⟩ := toE_surjective e
    exact ⟨(a, b, c), h⟩

/-- An element's three coordinates over `K`. -/
noncomputable def coords (e : E) : Fin 3 → K :=
  ![(toE_surjective e).choose, (toE_surjective e).choose_spec.choose,
    (toE_surjective e).choose_spec.choose_spec.choose]

theorem toE_coords (e : E) : toE (coords e 0) (coords e 1) (coords e 2) = e :=
  (toE_surjective e).choose_spec.choose_spec.choose_spec

theorem coords_toE (a0 a1 a2 : K) : coords (toE a0 a1 a2) = ![a0, a1, a2] := by
  obtain ⟨h0, h1, h2⟩ := toE_injective _ _ _ _ _ _ (toE_coords (toE a0 a1 a2))
  funext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

/-! The oracle with a challenge vector's coordinates in place of the challenges' words. -/

variable {n : ℕ}

/-- No two challenges' words, nor two words of one challenge, are the same node. -/
def OwnInj (own : Fin n → Fin 3 → ℕ) : Prop := Function.Injective fun p : Fin n × Fin 3 => own p.1 p.2

open Classical in
/-- The oracle `ρ` with challenge `i`'s words `own i` replaced by `r i`'s coordinates. -/
noncomputable def oracleAt (own : Fin n → Fin 3 → ℕ) (ρ : ℕ → K) (r : Fin n → E) : ℕ → K := fun m =>
  if h : ∃ p : Fin n × Fin 3, own p.1 p.2 = m then coords (r h.choose.1) h.choose.2 else ρ m

/-- The challenges an oracle gives: challenge `i`'s words read as an element of `E`. -/
noncomputable def readR (own : Fin n → Fin 3 → ℕ) (ρ : ℕ → K) : Fin n → E :=
  fun i => toE (ρ (own i 0)) (ρ (own i 1)) (ρ (own i 2))

theorem oracleAt_own {own : Fin n → Fin 3 → ℕ} (hinj : OwnInj own) (ρ : ℕ → K) (r : Fin n → E) (i : Fin n)
    (k : Fin 3) : oracleAt own ρ r (own i k) = coords (r i) k := by
  have hex : ∃ p : Fin n × Fin 3, own p.1 p.2 = own i k := ⟨(i, k), rfl⟩
  have hc : hex.choose = (i, k) := hinj hex.choose_spec
  unfold oracleAt
  rw [dif_pos hex, hc]

theorem oracleAt_off {own : Fin n → Fin 3 → ℕ} (ρ : ℕ → K) (r : Fin n → E) {m : ℕ}
    (h : ∀ i k, own i k ≠ m) : oracleAt own ρ r m = ρ m := by
  unfold oracleAt
  rw [dif_neg]
  rintro ⟨p, hp⟩
  exact h _ _ hp

/-- The challenges of the substituted oracle are the vector put in. -/
theorem readR_oracleAt {own : Fin n → Fin 3 → ℕ} (hinj : OwnInj own) (ρ : ℕ → K) (r : Fin n → E) :
    readR own (oracleAt own ρ r) = r := by
  funext i
  simp only [readR, oracleAt_own hinj]
  exact toE_coords (r i)

/-- Putting back an oracle's own challenges gives it back. -/
theorem oracleAt_readR {own : Fin n → Fin 3 → ℕ} (hinj : OwnInj own) (ρ : ℕ → K) :
    oracleAt own ρ (readR own ρ) = ρ := by
  funext m
  by_cases h : ∃ p : Fin n × Fin 3, own p.1 p.2 = m
  · obtain ⟨⟨i, k⟩, rfl⟩ := h
    rw [oracleAt_own hinj, readR, coords_toE]
    fin_cases k <;> rfl
  · push Not at h
    exact oracleAt_off ρ _ fun i k => h (i, k)

/-- The last vector put in wins. -/
theorem oracleAt_oracleAt {own : Fin n → Fin 3 → ℕ} (hinj : OwnInj own) (ρ : ℕ → K) (r r' : Fin n → E) :
    oracleAt own (oracleAt own ρ r) r' = oracleAt own ρ r' := by
  funext m
  by_cases h : ∃ p : Fin n × Fin 3, own p.1 p.2 = m
  · obtain ⟨⟨i, k⟩, rfl⟩ := h
    rw [oracleAt_own hinj, oracleAt_own hinj]
  · push Not at h
    rw [oracleAt_off _ _ fun i k => h (i, k), oracleAt_off _ _ fun i k => h (i, k),
      oracleAt_off _ _ fun i k => h (i, k)]

/-! Counting over oracles. -/

open Classical in
/-- A lens `put`/`get` from outcomes `Ω` to vectors `X`: the outcomes satisfying `P`, each counted once per vector,
are at most the vectors at each outcome whose put satisfies `P`, summed over the outcomes. -/
theorem card_lens {Ω X : Type} [Fintype Ω] [Fintype X] (put : Ω → X → Ω) (get : Ω → X)
    (hgp : ∀ ω x, get (put ω x) = x) (hpg : ∀ ω, put ω (get ω) = ω) (hpp : ∀ ω x y, put (put ω x) y = put ω y)
    (P : Ω → Prop) : #{ω | P ω} * Fintype.card X ≤ ∑ ω : Ω, #{x | P (put ω x)} := by
  calc #{ω | P ω} * Fintype.card X = #(({ω | P ω} : Finset Ω) ×ˢ (univ : Finset X)) := by
        rw [card_product, card_univ]
    _ ≤ #({p : Ω × X | P (put p.1 p.2)} : Finset (Ω × X)) := by
        refine card_le_card_of_injOn (fun p => (put p.1 p.2, get p.1)) (fun p hp => ?_) fun p hp q hq hpq => ?_
        · simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, mem_univ, true_and] at hp
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
          rw [hpp, hpg]
          exact hp.1
        · simp only [Prod.mk.injEq] at hpq
          have hx : p.2 = q.2 := by rw [← hgp p.1 p.2, ← hgp q.1 q.2, hpq.1]
          have hω : p.1 = q.1 := by rw [← hpg p.1, ← hpg q.1, ← hpp p.1 p.2, ← hpp q.1 q.2, hpq.1, hpq.2]
          exact Prod.ext hω hx
    _ = ∑ ω : Ω, #{x | P (put ω x)} := by
        simp only [card_filter]
        exact Fintype.sum_prod_type _

/-- A count read as a fraction: `A · |E| · |E|^n ≤ |Ω| · B · |E|^n` gives `A / |Ω| ≤ B / |E|`. -/
theorem frac_of_card {Ω : Type} [Fintype Ω] {A B : ℕ} (n : ℕ)
    (h : A * Fintype.card E * Fintype.card E ^ n ≤ Fintype.card Ω * B * Fintype.card E ^ n) :
    (A : ℚ≥0) / Fintype.card Ω ≤ B / Fintype.card E := by
  have hE : 0 < Fintype.card E := Fintype.card_pos
  have h' : A * Fintype.card E ≤ Fintype.card Ω * B := Nat.le_of_mul_le_mul_right h (by positivity)
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with hΩ | hΩ
  · rw [hΩ]; simp
  rw [div_le_div_iff₀ (by exact_mod_cast hΩ) (by exact_mod_cast hE)]
  rw [mul_comm (B : ℚ≥0)]
  exact_mod_cast h'

/-- A bound `n · B · |E|^(n-1)` on vectors of `E^n`, times `|E|`, is `n · B · |E|^n`. -/
theorem mul_card_le {x n B : ℕ} (h : x ≤ n * B * Fintype.card E ^ (n - 1)) :
    x * Fintype.card E ≤ n * B * Fintype.card E ^ n := by
  rcases n with _ | n
  · simp at h; simp [h]
  · calc x * Fintype.card E ≤ (n + 1) * B * Fintype.card E ^ n * Fintype.card E := Nat.mul_le_mul_right _ h
      _ = (n + 1) * B * Fintype.card E ^ (n + 1) := by ring

/-! A prover's run. -/

/-- A prover's run in the random-oracle view of transcript `T`: an assignment at each oracle `ρ`, in that view
(`RomAnswers`), whose squeezes' outputs are `ρ`'s answers (`ans`), and whose seeds before time `k` (what its first `k`
blocks absorb, and the statement past its last block) read only `ρ`'s answers drawn by `k` (`causal`). -/
structure Run (c : Cert) (s : State) (T : ℕ) (st : (ℕ → K) → ℕ → Fin 4 → K) (val : (ℕ → K) → Val) : Prop where
  rom : RomAnswers c s T st val
  ans : ∀ ρ, ∀ p ∈ chalSeeds s (c.transcripts.getD T default), nu (val ρ) p.2 = ρ p.2
  causal : ∀ ρ ρ' k, (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 ≤ k → ρ p.2 = ρ' p.2) →
    ∀ m ∈ seedsBefore s (c.transcripts.getD T default) k, nu (val ρ) m = nu (val ρ') m

theorem RomAnswers.comp {c : Cert} {s : State} {T : ℕ} {ι ι' : Type} {st : ι → ℕ → Fin 4 → K} {val : ι → Val}
    (ha : RomAnswers c s T st val) (f : ι' → ι) : RomAnswers c s T (fun r => st (f r)) (fun r => val (f r)) :=
  ⟨fun r => ha.holds (f r), fun r => ha.facts (f r), fun r r' => ha.cr (f r) (f r'),
    fun r r' => ha.win (f r) (f r'), fun r r' => ha.unions (f r) (f r')⟩

/-- Challenge `i`'s words are challenge seeds of transcript `t` at `time i + 1`, and at no other time. -/
def OwnAt (s : State) (t : Transcript) (own : Fin n → Fin 3 → ℕ) (time : Fin n → ℕ) : Prop :=
  ∀ i k, (time i + 1, own i k) ∈ chalSeeds s t ∧ ∀ p ∈ chalSeeds s t, p.2 = own i k → p.1 = time i + 1

variable {c : Cert} {s : State} {T : ℕ} {st : (ℕ → K) → ℕ → Fin 4 → K} {val : (ℕ → K) → Val}
  {own : Fin n → Fin 3 → ℕ} {time : Fin n → ℕ}

/-- Two vectors differing only at challenges drawn after `k` give assignments agreeing on the seeds before `k`. -/
theorem Run.seed_at (hR : Run c s T st val) (hown : OwnAt s (c.transcripts.getD T default) own time)
    (hinj : OwnInj own) (ρ : ℕ → K) (k : ℕ) (r r' : Fin n → E) (hr : ∀ j, r j ≠ r' j → k ≤ time j) :
    ∀ m ∈ seedsBefore s (c.transcripts.getD T default) k,
      nu (val (oracleAt own ρ r)) m = nu (val (oracleAt own ρ r')) m := by
  refine hR.causal _ _ k fun p hp hk => ?_
  by_cases h : ∃ q : Fin n × Fin 3, own q.1 q.2 = p.2
  · obtain ⟨⟨j, l⟩, hj⟩ := h
    have ht := (hown j l).2 p hp hj.symm
    have hrj : r j = r' j := by
      by_contra hne
      have := hr j hne
      omega
    rw [← hj, oracleAt_own hinj, oracleAt_own hinj, hrj]
  · push Not at h
    rw [oracleAt_off _ _ fun i k => h (i, k), oracleAt_off _ _ fun i k => h (i, k)]

/-- At increasing times, the words squeezed with challenge `i` but its own are no challenge's own words: two vectors
agreeing before `i` give assignments agreeing on them. -/
theorem Run.sib_at (hR : Run c s T st val) (hown : OwnAt s (c.transcripts.getD T default) own time)
    (hlt : ∀ i j, i < j → time i < time j) (ρ : ℕ → K) (i : Fin n) (ownL : List ℕ)
    (hL : ∀ k, own i k ∈ ownL) (r r' : Fin n → E) :
    ∀ m ∈ sibSeeds s (c.transcripts.getD T default) (time i) ownL,
      nu (val (oracleAt own ρ r)) m = nu (val (oracleAt own ρ r')) m := by
  intro m hm
  simp only [sibSeeds, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hm
  obtain ⟨p, ⟨hp, ht, hnot⟩, rfl⟩ := hm
  have hoff : ∀ j l, own j l ≠ p.2 := by
    intro j l hjl
    have htj := (hown j l).2 p hp hjl.symm
    have hji : j = i := by
      rcases lt_trichotomy j i with hji | hji | hji
      · have := hlt j i hji; omega
      · exact hji
      · have := hlt i j hji; omega
    subst hji
    have hm : ownL.contains p.2 = true := List.contains_iff_mem.mpr (hjl ▸ hL l)
    rw [hm] at hnot
    exact Bool.noConfusion hnot
  rw [hR.ans _ p hp, hR.ans _ p hp, oracleAt_off _ _ hoff, oracleAt_off _ _ hoff]

/-- Where challenge `i` reads its words as an element of `E`, the substituted oracle's challenge is `r i`. -/
theorem Run.chal_at (hR : Run c s T st val) (hown : OwnAt s (c.transcripts.getD T default) own time)
    (hinj : OwnInj own) (chal : Fin n → ℕ)
    (hread : ∀ ρ i, Model.ev (val ρ) (chal i) =
      toE (nu (val ρ) (own i 0)) (nu (val ρ) (own i 1)) (nu (val ρ) (own i 2)))
    (ρ : ℕ → K) (r : Fin n → E) (i : Fin n) : Model.ev (val (oracleAt own ρ r)) (chal i) = r i := by
  have a0 := hR.ans (oracleAt own ρ r) _ (hown i 0).1
  have a1 := hR.ans (oracleAt own ρ r) _ (hown i 1).1
  have a2 := hR.ans (oracleAt own ρ r) _ (hown i 2).1
  rw [hread, a0, a1, a2, oracleAt_own hinj, oracleAt_own hinj, oracleAt_own hinj]
  exact toE_coords (r i)

/-! What acceptance gives of the challenges. -/

theorem facts_at {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    (hF : Facts cs rl os st val) {j : ℕ} {call : Call} (h : cs[j]? = some call) (he : call.isEq = false)
    (hs : call.isSqueeze = false) : call.Holds st val (os.getD j []) := by
  obtain ⟨hj, hc⟩ := Array.getElem?_eq_some_iff.mp h
  subst hc
  exact hF j hj (by rw [he, Bool.and_false]) hs

/-- A challenge reads its three words: where the replayed calls hold, its `k_to_e` of its `d_to_k`s' words is its own
words, at places of their digests, read as an element of `E`. -/
theorem ChalCert.read {s : State} {os : Array (List ℕ)} {cs : Array Call} {rl : Array Bool} {blocks : List ℕ}
    {st : ℕ → Fin 4 → K} {val : Val} {cc : ChalCert} (hok : cc.ok s os cs blocks = true)
    (hp : cc.words.all (fun e => decide (e.2.1 < 4)) = true) (hF : Facts cs rl os st val) :
    Model.ev val cc.chal = toE (nu val ((cc.own os).getD 0 0)) (nu val ((cc.own os).getD 1 0))
      (nu val ((cc.own os).getD 2 0)) := by
  simp only [ChalCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨-, -⟩, hchal⟩, h3⟩, hk⟩, hw⟩ := hok
  simp only [List.all_eq_true, decide_eq_true_eq] at hp
  have hkE := facts_at hF hk rfl rfl
  simp only [Call.Holds] at hkE
  have hout : (os.getD cc.chalAt []).getD 0 0 = cc.chal := hchal
  rw [hout] at hkE
  rw [hkE]
  have hword : ∀ k < 3, val (outAt os (cc.words.getD k default).1 (cc.words.getD k default).2.1) 0 =
      nu val ((cc.own os).getD k 0) := by
    intro k hk3
    have hkl : k < cc.words.length := by omega
    have hmem : cc.words.getD k default ∈ cc.words := by
      rw [List.getD_eq_getElem _ _ hkl]
      exact List.getElem_mem _
    obtain ⟨hdk, -⟩ := hw _ hmem
    have hd := facts_at hF hdk rfl rfl
    simp only [Call.Holds] at hd
    have hown : (cc.own os).getD k 0 = limb (outAt os (cc.words.getD k default).2.2 0) (cc.words.getD k default).2.1 := by
      rw [ChalCert.own, List.getD_eq_getElem _ _ (by simpa using hkl), List.getElem_map,
        List.getD_eq_getElem _ _ hkl]
    rw [hown, nu_limb _ _ _ (hp _ hmem)]
    exact hd ⟨_, hp _ hmem⟩
  rw [hword 0 (by norm_num), hword 1 (by norm_num), hword 2 (by norm_num)]

/-- Challenges `cc`'s words: challenge `i`'s three. -/
def chalWords (os : Array (List ℕ)) (cc : Fin n → ChalCert) : Fin n → Fin 3 → ℕ :=
  fun i k => ((cc i).own os).getD k 0

theorem ChalCert.ok_words {s : State} {os : Array (List ℕ)} {cs : Array Call} {blocks : List ℕ} {cc : ChalCert}
    (hok : cc.ok s os cs blocks = true) : cc.words.length = 3 := by
  simp only [ChalCert.ok, Bool.and_eq_true, beq_iff_eq] at hok
  exact hok.1.1.2

/-- What the verdict's `chalsOk` gives of challenges `cc` drawn from transcript `t`: their words are the oracle's at
one step after their times, no two the same, their times do not decrease (`strict`: increase), and each word's place
is one of its digest's four. -/
theorem chalsOk_sem {s : State} {os : Array (List ℕ)} {t : Transcript} {strict : Bool} {cc : Fin n → ChalCert}
    (h : chalsOk s os t strict (List.ofFn cc) = true) (h3 : ∀ i, (cc i).words.length = 3) :
    OwnAt s t (chalWords os cc) (fun i => (cc i).time) ∧
      OwnInj (chalWords os cc) ∧ (∀ i j, i < j → (cc i).time ≤ (cc j).time) ∧
      (strict = true → ∀ i j, i < j → (cc i).time < (cc j).time) ∧
      ∀ i, (cc i).words.all (fun e => decide (e.2.1 < 4)) = true := by
  simp only [chalsOk, Bool.and_eq_true, List.all_eq_true, List.mem_ofFn, decide_eq_true_eq] at h
  obtain ⟨⟨hown, hnd⟩, hord⟩ := h
  have hlen : ∀ i, ((cc i).own os).length = 3 := fun i => by simp [ChalCert.own, h3 i]
  have hmem : ∀ i (k : Fin 3), ((cc i).own os).getD k 0 ∈ (cc i).own os := fun i k => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.isLt)]
    exact List.getElem_mem _
  have hok : ∀ i, (cc i).ownOk s os t = true := fun i => hown _ ⟨i, rfl⟩
  have hmono : ∀ i j, i < j → (cc i).time ≤ (cc j).time := by
    intro i j hij
    cases strict
    · simp only [Bool.false_eq_true, if_false, decide_eq_true_eq, List.pairwise_ofFn] at hord
      exact hord hij
    · simp only [if_true, decide_eq_true_eq, List.pairwise_ofFn] at hord
      exact (hord hij).le
  refine ⟨fun i k => ?_, fun ⟨i, k⟩ ⟨j, l⟩ hij => ?_, hmono, fun hs i j hij => ?_, fun i => ?_⟩
  · have := hok i
    simp only [ChalCert.ownOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Bool.or_eq_true,
      bne_iff_ne, ne_eq, beq_iff_eq] at this
    obtain ⟨-, hw⟩ := this
    obtain ⟨hin, hall⟩ := hw _ (hmem i k)
    refine ⟨hin, fun p hp hpe => ?_⟩
    rcases hall p hp with hne | heq
    · exact absurd hpe hne
    · exact heq
  · simp only [chalWords] at hij
    rw [List.nodup_flatMap] at hnd
    obtain ⟨hnd1, hdisj⟩ := hnd
    rw [List.pairwise_ofFn] at hdisj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact (List.disjoint_left.mp (hdisj hlt) (hmem i k) (by rw [hij]; exact hmem j l)).elim
    · have hn := hnd1 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.isLt),
        List.getD_eq_getElem _ _ (by rw [hlen]; exact l.isLt)] at hij
      have := (List.Nodup.getElem_inj_iff hn).mp hij
      exact Prod.ext rfl (Fin.ext this)
    · exact (List.disjoint_left.mp (hdisj hgt) (hmem j l) (by rw [← hij]; exact hmem i k)).elim
  · subst hs
    simp only [if_true, decide_eq_true_eq, List.pairwise_ofFn] at hord
    exact hord hij
  · have := hok i
    simp only [ChalCert.ownOk, Bool.and_eq_true] at this
    exact this.1

/-- A run's challenges: from a passing `chalsOk` and each challenge's `ChalCert.ok`, at every oracle `ρ` the
substituted oracle's challenges are the vector put in. -/
theorem Run.chals (hR : Run c s T st val) {strict : Bool} {cc : Fin n → ChalCert}
    (hch : chalsOk s c.outs (c.transcripts.getD T default) strict (List.ofFn cc) = true)
    (hok : ∀ i, (cc i).ok s c.outs c.calls (c.transcripts.getD T default).blocks = true) :
    OwnAt s (c.transcripts.getD T default) (chalWords c.outs cc) (fun i => (cc i).time) ∧
      OwnInj (chalWords c.outs cc) ∧ (∀ i j, i < j → (cc i).time ≤ (cc j).time) ∧
      (strict = true → ∀ i j, i < j → (cc i).time < (cc j).time) ∧
      ∀ ρ r i, Model.ev (val (oracleAt (chalWords c.outs cc) ρ r)) (cc i).chal = r i := by
  obtain ⟨hown, hinj, hmono, hlt, hp⟩ := chalsOk_sem hch fun i => ChalCert.ok_words (hok i)
  refine ⟨hown, hinj, hmono, hlt, fun ρ r i => hR.chal_at hown hinj (fun i => (cc i).chal) (fun ρ i => ?_) ρ r i⟩
  exact ChalCert.read (hok i) (hp i) (hR.rom.facts ρ)

/-! Each check's challenges, from acceptance. -/

theorem ofFn_getD_map {α β : Type} [Inhabited α] (l : List α) (f : α → β) :
    List.ofFn (fun i : Fin l.length => f (l.getD i default)) = l.map f := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

/-- A sumcheck's challenges, its rounds'. -/
def SumcheckCert.chals (sc : SumcheckCert) : Fin sc.rounds.length → ChalCert := fun i => (sc.rounds.getD i default).cc

/-- An odd layer's challenges, `λ` then the next. -/
def OddCert.chals (oc : OddCert) : Fin 2 → ChalCert := ![oc.lam, oc.next]

/-- A top layer's challenges, `λ`, `low` and `high`. -/
def TopCert.chals (tc : TopCert) : Fin 3 → ChalCert := ![tc.lam, tc.low, tc.high]

/-- A WHIR sumcheck's challenges, its rounds'. -/
def WhirCert.chals (wc : WhirCert) : Fin wc.rounds.length → ChalCert := fun i => (wc.rounds.getD i default).chal

theorem Cert.sumcheck_chals (h : c.accepts s = true) {sc : SumcheckCert} (hsc : sc ∈ c.sumchecks) :
    Bind.chalsOk s c.outs (c.transcripts.getD sc.transcript default) false (List.ofFn sc.chals) = true ∧
      ∀ i, (sc.chals i).ok s c.outs c.calls (c.transcripts.getD sc.transcript default).blocks = true := by
  have hall := (Cert.accepts_rounds h).1
  simp only [Cert.sumchecksOk, Array.all_eq_true', Bool.and_eq_true, List.all_eq_true, List.mem_range] at hall
  obtain ⟨⟨⟨⟨⟨htr, -⟩, -⟩, -⟩, hrounds⟩, -⟩ := hall sc hsc
  have hch := Cert.accepts_chals h
  simp only [Cert.chalsOk, Bool.and_eq_true, Array.all_eq_true'] at hch
  refine ⟨by unfold SumcheckCert.chals; rw [ofFn_getD_map]; exact hch.1.1.1 sc hsc, fun i => ?_⟩
  have := (hrounds i i.isLt).1
  rwa [Cert.marksRO_getD c s (of_decide_eq_true htr)] at this

theorem Cert.odd_chals (h : c.accepts s = true) {oc : OddCert} (hoc : oc ∈ c.odds) :
    Bind.chalsOk s c.outs (c.transcripts.getD oc.transcript default) false (List.ofFn oc.chals) = true ∧
      ∀ i, (oc.chals i).ok s c.outs c.calls (c.transcripts.getD oc.transcript default).blocks = true := by
  have hall := (Cert.accepts_rounds h).2.2.1
  simp only [Cert.oddsOk, Array.all_eq_true', Bool.and_eq_true] at hall
  obtain ⟨⟨⟨⟨⟨⟨⟨htr, -⟩, -⟩, -⟩, hlam⟩, hnext⟩, -⟩, -⟩ := hall oc hoc
  have hch := Cert.accepts_chals h
  simp only [Cert.chalsOk, Bool.and_eq_true, Array.all_eq_true'] at hch
  rw [Cert.marksRO_getD c s (by simpa using htr)] at hlam hnext
  refine ⟨by simpa [OddCert.chals, List.ofFn_succ] using hch.1.1.2 oc hoc, fun i => ?_⟩
  fin_cases i
  · exact hlam
  · exact hnext

theorem Cert.top_chals (h : c.accepts s = true) {tc : TopCert} (htc : tc ∈ c.tops) :
    Bind.chalsOk s c.outs (c.transcripts.getD tc.transcript default) false (List.ofFn tc.chals) = true ∧
      ∀ i, (tc.chals i).ok s c.outs c.calls (c.transcripts.getD tc.transcript default).blocks = true := by
  have hall := (Cert.accepts_rounds h).2.2.2.2
  simp only [Cert.lateOk, Cert.topsOk, Array.all_eq_true', Bool.and_eq_true] at hall
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨htr, -⟩, -⟩, -⟩, hlam⟩, hlow⟩, hhigh⟩, -⟩, -⟩ := hall.1.1 tc htc
  have hch := Cert.accepts_chals h
  simp only [Cert.chalsOk, Bool.and_eq_true, Array.all_eq_true'] at hch
  rw [Cert.marksRO_getD c s (by simpa using htr)] at hlam hlow hhigh
  refine ⟨by simpa [TopCert.chals, List.ofFn_succ] using hch.1.2 tc htc, fun i => ?_⟩
  fin_cases i
  · exact hlam
  · exact hlow
  · exact hhigh

theorem Cert.whir_chals (h : c.accepts s = true) {wc : WhirCert} (hwc : wc ∈ c.whirs) :
    Bind.chalsOk s c.outs (c.transcripts.getD wc.transcript default) true (List.ofFn wc.chals) = true ∧
      ∀ i, (wc.chals i).ok s c.outs c.calls (c.transcripts.getD wc.transcript default).blocks = true ∧
        c.whirBound s c.outs (c.transcripts.getD wc.transcript default, c.timesRO s (c.transcripts.getD wc.transcript default))
          (wc.rounds.getD i default) = true := by
  have hall := (Cert.accepts_rounds h).2.2.2.2
  simp only [Cert.lateOk, Cert.whirsOk, Array.all_eq_true', Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at hall
  obtain ⟨⟨⟨⟨⟨htr, -⟩, -⟩, -⟩, -⟩, hrounds⟩ := hall.2 wc hwc
  have hch := Cert.accepts_chals h
  simp only [Cert.chalsOk, Bool.and_eq_true, Array.all_eq_true'] at hch
  have hmr := Cert.marksRO_getD c s (of_decide_eq_true htr)
  refine ⟨by unfold WhirCert.chals; rw [ofFn_getD_map]; exact hch.2 wc hwc, fun i => ?_⟩
  have := hrounds i i.isLt
  rwa [hmr] at this

/-- The words a transcript's squeezes output: where the oracle answers. -/
def oracleWords (s : State) (t : Transcript) : Finset ℕ := ((chalSeeds s t).map (·.2)).toFinset

/-- An oracle on words `U`, zero elsewhere. -/
noncomputable def extU (U : Finset ℕ) (ρ : U → K) : ℕ → K := fun m => if h : m ∈ U then ρ ⟨m, h⟩ else 0

/-- A check's words are where the oracle answers. -/
theorem own_mem_oracleWords {s : State} {t : Transcript} {own : Fin n → Fin 3 → ℕ} {time : Fin n → ℕ}
    (hown : OwnAt s t own time) (i : Fin n) (k : Fin 3) : own i k ∈ oracleWords s t :=
  List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, (hown i k).1, rfl⟩)

/-! Each check's answers from a run. -/

/-- A run's assignments at the oracle with a sumcheck's challenges put in are `SumcheckAnswers`, where the circuit's
eq weights are the honest instance's at the oracle's challenges and the input claim is false where the hints are
true. -/
theorem Run.sumcheckAnswers (h : c.accepts s = true) {sc : SumcheckCert} (hsc : sc ∈ c.sumchecks)
    (hR : Run c s sc.transcript st val) (I : Inst E sc.rounds.length) (T' : ℕ → E)
    (hw : ∀ ρ (i : Fin sc.rounds.length), (sc.rounds.getD i default).weight.map (Model.ev (val ρ)) =
      I.weight (readR (chalWords c.outs sc.chals) ρ) i)
    (ρ : ℕ → K) (hf : ∀ r, (∀ w ∈ sc.hints, Model.ev (val (oracleAt (chalWords c.outs sc.chals) ρ r)) w = T' w) →
      Model.ev (val (oracleAt (chalWords c.outs sc.chals) ρ r)) sc.claim0 ≠ I.sum) :
    SumcheckAnswers c s sc I T' (fun r => st (oracleAt (chalWords c.outs sc.chals) ρ r))
      (fun r => val (oracleAt (chalWords c.outs sc.chals) ρ r)) := by
  obtain ⟨hc, hok⟩ := Cert.sumcheck_chals h hsc
  obtain ⟨hown, hinj, hmono, -, hchal⟩ := hR.chals hc hok
  refine ⟨hR.rom.comp _, fun r r' i hj => hR.seed_at hown hinj ρ _ r r' fun j hne => ?_, fun r i => hchal ρ r i,
    fun r i => by rw [hw]; exact congrArg (fun x => I.weight x i) (readR_oracleAt hinj ρ r), hf⟩
  rcases lt_or_ge j i with hji | hij
  · exact absurd (hj j hji) hne
  · rcases hij.lt_or_eq with hij | rfl
    · exact hmono i j hij
    · exact le_rfl

/-- A run's assignments at the oracle with an odd layer's challenges put in are `OddAnswers`, where some input value
is not its true children's product. -/
theorem Run.oddAnswers (h : c.accepts s = true) {oc : OddCert} (hoc : oc ∈ c.odds) (hR : Run c s oc.transcript st val)
    (L R : ℕ → E) (ρ : ℕ → K)
    (hf : ∀ r, ∃ k < oc.m, Model.ev (val (oracleAt (chalWords c.outs oc.chals) ρ r)) (oc.values.getD k 0) ≠ L k * R k) :
    OddAnswers c s oc L R (fun r => st (oracleAt (chalWords c.outs oc.chals) ρ r))
      (fun r => val (oracleAt (chalWords c.outs oc.chals) ρ r)) := by
  obtain ⟨hc, hok⟩ := Cert.odd_chals h hoc
  obtain ⟨hown, hinj, hmono, -, hchal⟩ := hR.chals hc hok
  have h01 : (oc.chals 0).time ≤ (oc.chals 1).time := hmono 0 1 (by decide)
  refine ⟨hR.rom.comp _, fun r r' => hR.seed_at hown hinj ρ _ r r' fun j _ => ?_,
    fun r r' h0 => hR.seed_at hown hinj ρ _ r r' fun j hne => ?_, fun r => ⟨hchal ρ r 0, hchal ρ r 1⟩, hf⟩
  · fin_cases j
    · exact le_rfl
    · exact h01
  · fin_cases j
    · exact absurd h0 hne
    · exact le_rfl

/-- A run's assignments at the oracle with a top layer's challenges put in are `TopAnswers`, where some input value is
not its true children's product. -/
theorem Run.topAnswers (h : c.accepts s = true) {tc : TopCert} (htc : tc ∈ c.tops) (hR : Run c s tc.transcript st val)
    (T' : ℕ → ℕ → E) (ρ : ℕ → K)
    (hf : ∀ r, ∃ k < tc.m, Model.ev (val (oracleAt (chalWords c.outs tc.chals) ρ r)) (tc.values.getD k 0) ≠
      T' k 0 * T' k 1 * T' k 2 * T' k 3) :
    TopAnswers c s tc T' (fun r => st (oracleAt (chalWords c.outs tc.chals) ρ r))
      (fun r => val (oracleAt (chalWords c.outs tc.chals) ρ r)) := by
  obtain ⟨hc, hok⟩ := Cert.top_chals h htc
  obtain ⟨hown, hinj, hmono, -, hchal⟩ := hR.chals hc hok
  have h01 : (tc.chals 0).time ≤ (tc.chals 1).time := hmono 0 1 (by decide)
  have h12 : (tc.chals 1).time ≤ (tc.chals 2).time := hmono 1 2 (by decide)
  refine ⟨hR.rom.comp _, fun r r' => hR.seed_at hown hinj ρ _ r r' fun j _ => ?_,
    fun r r' h0 => hR.seed_at hown hinj ρ _ r r' fun j hne => ?_,
    fun r => ⟨hchal ρ r 0, hchal ρ r 1, hchal ρ r 2⟩, hf⟩
  · fin_cases j
    · exact le_rfl
    · exact h01
    · exact h01.trans h12
  · fin_cases j
    · exact absurd h0 hne
    · exact le_rfl
    · exact h12

/-- A run's assignments at the oracle with a WHIR sumcheck's challenges put in are `WhirAnswers`, where the rounds'
eq weights are the honest instance's and the input claim is not its sum. -/
theorem Run.whirAnswers (h : c.accepts s = true) {wc : WhirCert} (hwc : wc ∈ c.whirs)
    (hR : Run c s wc.transcript st val) (I : Inst E wc.rounds.length)
    (hw : ∀ r (i : Fin wc.rounds.length), (wc.rounds.getD i default).weight = I.weight r i)
    (ρ : ℕ → K) (hf : ∀ r, Model.ev (val (oracleAt (chalWords c.outs wc.chals) ρ r)) wc.claim0 ≠ I.sum) :
    WhirAnswers c s wc I (fun r => st (oracleAt (chalWords c.outs wc.chals) ρ r))
      (fun r => val (oracleAt (chalWords c.outs wc.chals) ρ r)) := by
  obtain ⟨hc, hok⟩ := Cert.whir_chals h hwc
  obtain ⟨hown, hinj, hmono, hlt, hchal⟩ := hR.chals hc fun i => (hok i).1
  have hlt := hlt rfl
  refine ⟨hR.rom.comp _, fun r r' i hj m hm => ?_, fun r i => hchal ρ r i, fun r i => hw r i, hf⟩
  have hseed : ∀ m ∈ seedsBefore s (c.transcripts.getD wc.transcript default) (wc.chals i).time,
      nu (val (oracleAt (chalWords c.outs wc.chals) ρ r)) m =
        nu (val (oracleAt (chalWords c.outs wc.chals) ρ r')) m :=
    hR.seed_at hown hinj ρ _ r r' fun j hne => by
      rcases lt_or_ge j i with hji | hij
      · exact absurd (hj j hji) hne
      · rcases hij.lt_or_eq with hij | rfl
        · exact hmono i j hij
        · exact le_rfl
  have hb := (hok i).2
  have h3 := ChalCert.ok_words (hok i).1
  have hsib := hR.sib_at hown hlt ρ i
  simp only [WhirCert.chals] at hseed h3 hsib
  revert hb hm h3 hseed hsib
  cases hwr : wc.rounds.getD i default with
  | fold q cc uAt tAt =>
    intro hm hseed _ _ _
    exact hseed m hm
  | batch cc e ownL fs =>
    intro hm hseed hb h3 hsib
    simp only [WhirRound.seeds, List.mem_append] at hm
    rcases hm with hm | hm
    · exact hseed m hm
    · simp only [Cert.whirBound, Bool.and_eq_true, beq_iff_eq] at hb
      refine hsib ownL (fun k => ?_) r r' m hm
      have hci : wc.chals i = cc := by simp only [WhirCert.chals, hwr, WhirRound.chal]
      show ((wc.chals i).own c.outs).getD k 0 ∈ ownL
      simp only [WhirRound.chal] at h3
      rw [hci, hb.1.1, List.getD_eq_getElem _ _ (by simp [ChalCert.own, h3])]
      exact List.getElem_mem _

/-! A uniform oracle: each round theorem as a fraction of the oracles. -/

open Classical in
/-- Challenges whose words are among `U` are uniform when the oracle on `U` is: if at every oracle the challenge
vectors put in satisfying `Q`, times `|E|`, are at most `B · |E|^n`, the oracles on `U` satisfying `Q` are at most a
`B / |E|` fraction. -/
theorem run_frac {own : Fin n → Fin 3 → ℕ} {U : Finset ℕ} (hinj : OwnInj own) (hU : ∀ i k, own i k ∈ U)
    (Q : (ℕ → K) → Prop) (B : ℕ)
    (hB : ∀ ρ : ℕ → K, #{r : Fin n → E | Q (oracleAt own ρ r)} * Fintype.card E ≤ B * Fintype.card E ^ n) :
    (#{ρ : U → K | Q (extU U ρ)} : ℚ≥0) / Fintype.card (U → K) ≤ B / Fintype.card E := by
  let put : (U → K) → (Fin n → E) → (U → K) := fun ρ r x => oracleAt own (extU U ρ) r x.1
  let get : (U → K) → (Fin n → E) := fun ρ => readR own (extU U ρ)
  have hext : ∀ ρ r, extU U (put ρ r) = oracleAt own (extU U ρ) r := fun ρ r => by
    funext m
    by_cases hm : m ∈ U
    · simp [extU, hm, put]
    · have hoff : ∀ i k, own i k ≠ m := fun i k he => hm (he ▸ hU i k)
      simp [extU, hm, oracleAt_off _ _ hoff]
  have hgp : ∀ ρ r, get (put ρ r) = r := fun ρ r => by simp only [get, hext, readR_oracleAt hinj]
  have hpg : ∀ ρ, put ρ (get ρ) = ρ := fun ρ => by
    funext x
    simp only [put, get, oracleAt_readR hinj, extU, x.2, dif_pos]
  have hpp : ∀ ρ r r', put (put ρ r) r' = put ρ r' := fun ρ r r' => by
    funext x
    simp only [put, hext, oracleAt_oracleAt hinj]
  have hl := card_lens put get hgp hpg hpp fun ρ => Q (extU U ρ)
  rw [Fintype.card_fun, Fintype.card_fin] at hl
  refine frac_of_card n ?_
  calc #{ρ : U → K | Q (extU U ρ)} * Fintype.card E * Fintype.card E ^ n
      = #{ρ : U → K | Q (extU U ρ)} * Fintype.card E ^ n * Fintype.card E := by ring
    _ ≤ (∑ ρ : U → K, #{r | Q (extU U (put ρ r))}) * Fintype.card E := Nat.mul_le_mul_right _ hl
    _ = ∑ ρ : U → K, #{r | Q (oracleAt own (extU U ρ) r)} * Fintype.card E := by
        rw [sum_mul]
        simp only [hext]
    _ ≤ ∑ _ρ : U → K, B * Fintype.card E ^ n := sum_le_sum fun ρ _ => hB _
    _ = Fintype.card (U → K) * B * Fintype.card E ^ n := by simp [mul_assoc]

theorem card_piFinset_univ_filter {m : ℕ} (P : (Fin m → E) → Prop) [DecidablePred P] :
    #((Fintype.piFinset fun _ : Fin m => (univ : Finset E)).filter P) = #(univ.filter P) := by
  rw [Fintype.piFinset_univ]

/-- The event a sumcheck's test bounds, at oracle `ρ`: the hints are their true values, the test holds, and its other
side is the instance's final value at the oracle's challenges. -/
def sumcheckEvent (c : Cert) (s : State) (sc : SumcheckCert) (I : Inst E sc.rounds.length) (T' : ℕ → E)
    (val : (ℕ → K) → Val) (ρ : ℕ → K) : Prop :=
  (∀ w ∈ sc.hints, Model.ev (val ρ) w = T' w) ∧ (∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b) ∧
    Model.ev (val ρ) sc.final + (sc.resid.map fun t => Model.ev (val ρ) t.1 * Model.ev (val ρ) t.2.1).sum =
      I.final (readR (chalWords c.outs sc.chals) ρ)

/-- The event an odd layer's test bounds: the test holds and every next claim is its value's true line at the
oracle's next challenge. -/
def oddEvent (c : Cert) (s : State) (oc : OddCert) (L R : ℕ → E) (val : (ℕ → K) → Val) (ρ : ℕ → K) : Prop :=
  (∀ a b, s.unions[oc.test]? = some (a, b) → val ρ a = val ρ b) ∧
    ∀ k < oc.m, Model.ev (val ρ) (oc.out c.outs k) = L k + readR (chalWords c.outs oc.chals) ρ 1 * (L k + R k)

/-- The event a top layer's test bounds: the test holds and every next claim is its value's true children's
interpolation at the oracle's `low` and `high`. -/
def topEvent (c : Cert) (s : State) (tc : TopCert) (T' : ℕ → ℕ → E) (val : (ℕ → K) → Val) (ρ : ℕ → K) : Prop :=
  (∀ a b, s.unions[tc.test]? = some (a, b) → val ρ a = val ρ b) ∧
    ∀ k < tc.m, Model.ev (val ρ) (tc.out c.outs k) =
      lineE (lineE (T' k 0) (T' k 1) (readR (chalWords c.outs tc.chals) ρ 1))
        (lineE (T' k 2) (T' k 3) (readR (chalWords c.outs tc.chals) ρ 1)) (readR (chalWords c.outs tc.chals) ρ 2)

/-- The event a WHIR sumcheck's test bounds: the test holds and its terminal value is the instance's final value at
the oracle's challenges. -/
def whirEvent (c : Cert) (s : State) (wc : WhirCert) (I : Inst E wc.rounds.length) (val : (ℕ → K) → Val)
    (ρ : ℕ → K) : Prop :=
  (∀ a b, s.unions[wc.test]? = some (a, b) → val ρ a = val ρ b) ∧
    Model.ev (val ρ) wc.final = I.final (readR (chalWords c.outs wc.chals) ρ)

open Classical in
/-- Sumcheck's soundness over a uniform oracle. Take a run of an accepted circuit's certified sumcheck (`n` rounds of
degree `d`) and the honest instance `I`, with the circuit's eq weights the instance's at the oracle's challenges and
the input claim false where the hints are their true values `T'`. The oracles on words `U` holding the transcript's
squeezed words, at which the hints are their true values, the test holds and its other side is the instance's final value at the
oracle's challenges (`sumcheckEvent`) are at most an `n · d / |E|` fraction. -/
theorem sumcheck_run_sound (h : c.accepts s = true) {sc : SumcheckCert} (hsc : sc ∈ c.sumchecks)
    (I : Inst E sc.rounds.length) (hI : I.ok sc.deg) (T' : ℕ → E) (hR : Run c s sc.transcript st val)
    (hw : ∀ ρ (i : Fin sc.rounds.length), (sc.rounds.getD i default).weight.map (Model.ev (val ρ)) =
      I.weight (readR (chalWords c.outs sc.chals) ρ) i)
    (hf : ∀ ρ, (∀ w ∈ sc.hints, Model.ev (val ρ) w = T' w) → Model.ev (val ρ) sc.claim0 ≠ I.sum)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD sc.transcript default) ⊆ U) :
    (#{ρ : U → K | sumcheckEvent c s sc I T' val (extU _ ρ)} : ℚ≥0) / Fintype.card (U → K) ≤
      ((sc.rounds.length * sc.deg : ℕ) : ℚ≥0) / Fintype.card E := by
  obtain ⟨hc, hok⟩ := Cert.sumcheck_chals h hsc
  obtain ⟨hown, hinj, -⟩ := chalsOk_sem hc fun i => ChalCert.ok_words (hok i)
  refine run_frac hinj (fun i k => hU (own_mem_oracleWords hown i k)) (sumcheckEvent c s sc I T' val) _ fun ρ => mul_card_le ?_
  have hb := sumcheck_test_sound c s h hsc univ I hI T' _ _ (hR.sumcheckAnswers h hsc I T' hw ρ fun r => hf _)
  rw [card_univ] at hb
  refine hb.trans' (card_le_card fun r hr => ?_)
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, implies_true] at hr ⊢
  simp only [sumcheckEvent, readR_oracleAt hinj] at hr
  exact hr

open Classical in
/-- GKR's odd layer over a uniform oracle: for a run in which some input value is not its true children's product, the
oracles at which the test holds and every next claim is its value's true line at the oracle's next challenge
(`oddEvent`) are at most an `m / |E|` fraction. -/
theorem odd_run_sound (h : c.accepts s = true) {oc : OddCert} (hoc : oc ∈ c.odds) (L R : ℕ → E)
    (hR : Run c s oc.transcript st val) (hf : ∀ ρ, ∃ k < oc.m, Model.ev (val ρ) (oc.values.getD k 0) ≠ L k * R k)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD oc.transcript default) ⊆ U) :
    (#{ρ : U → K | oddEvent c s oc L R val (extU _ ρ)} : ℚ≥0) /
        Fintype.card (U → K) ≤ oc.m / Fintype.card E := by
  obtain ⟨hc, hok⟩ := Cert.odd_chals h hoc
  obtain ⟨hown, hinj, -⟩ := chalsOk_sem hc fun i => ChalCert.ok_words (hok i)
  refine run_frac hinj (fun i k => hU (own_mem_oracleWords hown i k)) (oddEvent c s oc L R val) _ fun ρ => ?_
  have hb := odd_test_sound c s h hoc univ L R _ _ (hR.oddAnswers h hoc L R ρ fun r => hf _)
  rw [card_univ] at hb
  refine le_trans (Nat.mul_le_mul_right _ (hb.trans' (card_le_card fun r hr => ?_))) (le_of_eq (by ring))
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, implies_true] at hr ⊢
  simp only [oddEvent, readR_oracleAt hinj] at hr
  exact hr

open Classical in
/-- GKR's radix-four top layer over a uniform oracle: for a run in which some input value is not its true children's
product, the oracles at which the test holds and every next claim is its value's true children's interpolation at the
oracle's `low` and `high` (`topEvent`) are at most an `(m + 1) / |E|` fraction. -/
theorem top_run_sound (h : c.accepts s = true) {tc : TopCert} (htc : tc ∈ c.tops) (T' : ℕ → ℕ → E)
    (hR : Run c s tc.transcript st val)
    (hf : ∀ ρ, ∃ k < tc.m, Model.ev (val ρ) (tc.values.getD k 0) ≠ T' k 0 * T' k 1 * T' k 2 * T' k 3)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD tc.transcript default) ⊆ U) :
    (#{ρ : U → K | topEvent c s tc T' val (extU _ ρ)} : ℚ≥0) /
        Fintype.card (U → K) ≤ (tc.m + 1 : ℕ) / Fintype.card E := by
  obtain ⟨hc, hok⟩ := Cert.top_chals h htc
  obtain ⟨hown, hinj, -⟩ := chalsOk_sem hc fun i => ChalCert.ok_words (hok i)
  refine run_frac hinj (fun i k => hU (own_mem_oracleWords hown i k)) (topEvent c s tc T' val) _ fun ρ => ?_
  have hb := top_test_sound c s h htc univ T' _ _ (hR.topAnswers h htc T' ρ fun r => hf _)
  rw [card_univ] at hb
  refine le_trans (Nat.mul_le_mul_right _ (hb.trans' (card_le_card fun r hr => ?_))) (le_of_eq (by ring))
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, implies_true] at hr ⊢
  simp only [topEvent, readR_oracleAt hinj] at hr
  exact hr

open Classical in
/-- WHIR's sumcheck over a uniform oracle: for a run whose input claim is not the honest instance's sum, the oracles at
which the test holds and its terminal value is the instance's final value at the oracle's challenges (`whirEvent`) are
at most an `n · d / |E|` fraction. -/
theorem whir_run_sound (h : c.accepts s = true) {wc : WhirCert} (hwc : wc ∈ c.whirs) (I : Inst E wc.rounds.length)
    (hI : I.ok wc.deg) (hR : Run c s wc.transcript st val)
    (hw : ∀ r (i : Fin wc.rounds.length), (wc.rounds.getD i default).weight = I.weight r i)
    (hf : ∀ ρ, Model.ev (val ρ) wc.claim0 ≠ I.sum)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD wc.transcript default) ⊆ U) :
    (#{ρ : U → K | whirEvent c s wc I val (extU _ ρ)} : ℚ≥0) /
        Fintype.card (U → K) ≤ ((wc.rounds.length * wc.deg : ℕ) : ℚ≥0) / Fintype.card E := by
  obtain ⟨hc, hok⟩ := Cert.whir_chals h hwc
  obtain ⟨hown, hinj, -⟩ := chalsOk_sem hc fun i => ChalCert.ok_words (hok i).1
  refine run_frac hinj (fun i k => hU (own_mem_oracleWords hown i k)) (whirEvent c s wc I val) _ fun ρ => mul_card_le ?_
  have hb := whir_test_sound c s h hwc univ I hI _ _ (hR.whirAnswers h hwc I hw ρ fun r => hf _)
  rw [card_univ] at hb
  refine hb.trans' (card_le_card fun r hr => ?_)
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, implies_true] at hr ⊢
  simp only [whirEvent, readR_oracleAt hinj] at hr
  exact hr

/-! The round theorems at each oracle: the input claim false only where it is. -/

open Classical in
/-- A count for a premise that takes one value where `G` holds: the vectors where `G`, `ev` and `bad` hold are within
any bound on those where `G` and `ev` hold, given `bad` wherever `G` holds. -/
theorem card_at {α : Type} [Fintype α] (G ev bad : α → Prop) (B : ℕ)
    (hconst : ∀ r r', G r → G r' → bad r → bad r') (hB : (∀ r, G r → bad r) → #{r | G r ∧ ev r} ≤ B) :
    #{r | G r ∧ ev r ∧ bad r} ≤ B := by
  by_cases hall : ∀ r, G r → bad r
  · refine (card_le_card fun r hr => ?_).trans (hB hall)
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    exact ⟨hr.1, hr.2.1⟩
  · push Not at hall
    obtain ⟨r₀, hg, hb⟩ := hall
    have he : ({r | G r ∧ ev r ∧ bad r} : Finset α) = ∅ := by
      ext r
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨hgr, -, hbr⟩
      exact hb (hconst r r₀ hgr hg hbr)
    rw [he, card_empty]
    exact Nat.zero_le _

/-- `sumcheckEvent` with the input claim not the instance's sum. -/
def sumcheckFalse (c : Cert) (s : State) (sc : SumcheckCert) (I : Inst E sc.rounds.length) (T' : ℕ → E)
    (val : (ℕ → K) → Val) (ρ : ℕ → K) : Prop :=
  sumcheckEvent c s sc I T' val ρ ∧ Model.ev (val ρ) sc.claim0 ≠ I.sum

open Classical in
/-- Sumcheck's soundness over a uniform oracle, at each oracle: with no premise on the input claim, the oracles at
which `sumcheckEvent` holds and the input claim is not the instance's sum (`sumcheckFalse`) are at most an `n · d / |E|` fraction. The
claim is bound before the first challenge with the hints as seeds (`sumcheck_claim_agree`), so it is one value over
the vectors put in at an oracle wherever the hints are true. -/
theorem sumcheck_run_sound_at (h : c.accepts s = true) {sc : SumcheckCert} (hsc : sc ∈ c.sumchecks)
    (I : Inst E sc.rounds.length) (hI : I.ok sc.deg) (T' : ℕ → E) (hR : Run c s sc.transcript st val)
    (hw : ∀ ρ (i : Fin sc.rounds.length), (sc.rounds.getD i default).weight.map (Model.ev (val ρ)) =
      I.weight (readR (chalWords c.outs sc.chals) ρ) i)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD sc.transcript default) ⊆ U) :
    (#{ρ : U → K | sumcheckFalse c s sc I T' val (extU _ ρ)} : ℚ≥0) /
        Fintype.card (U → K) ≤ ((sc.rounds.length * sc.deg : ℕ) : ℚ≥0) / Fintype.card E := by
  obtain ⟨hc, hok⟩ := Cert.sumcheck_chals h hsc
  obtain ⟨hown, hinj, hmono, -⟩ := chalsOk_sem hc fun i => ChalCert.ok_words (hok i)
  have hpos : 0 < sc.rounds.length := by
    have hall := (Cert.accepts_rounds h).1
    simp only [Cert.sumchecksOk, Array.all_eq_true', Bool.and_eq_true] at hall
    have := (hall sc hsc).1.1.1.1.2
    simp only [SumcheckCert.ok, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  refine run_frac hinj (fun i k => hU (own_mem_oracleWords hown i k))
    (sumcheckFalse c s sc I T' val) _ fun ρ => mul_card_le ?_
  let v := fun r => val (oracleAt (chalWords c.outs sc.chals) ρ r)
  refine (card_le_card fun r hr => ?_).trans (card_at (fun r => ∀ w ∈ sc.hints, Model.ev (v r) w = T' w)
    (fun r => (∀ a b, s.unions[sc.test]? = some (a, b) → v r a = v r b) ∧
      Model.ev (v r) sc.final + (sc.resid.map fun t => Model.ev (v r) t.1 * Model.ev (v r) t.2.1).sum = I.final r)
    (fun r => Model.ev (v r) sc.claim0 ≠ I.sum) _ (fun r r' hr hr' hb => ?_) fun hall => ?_)
  · simp only [mem_filter, mem_univ, true_and, sumcheckFalse, sumcheckEvent, readR_oracleAt hinj] at hr ⊢
    exact ⟨hr.1.1, hr.1.2, hr.2⟩
  · have hagree := sumcheck_claim_agree c s h hsc (hR.rom.comp _) T' r r'
      (hR.seed_at hown hinj ρ _ r r' fun j _ => by
        rcases Nat.eq_zero_or_pos j.val with hj | hj
        · obtain rfl : j = ⟨0, hpos⟩ := Fin.ext hj
          exact le_rfl
        · exact hmono ⟨0, hpos⟩ j hj) hr hr'
    rwa [← hagree]
  · have hb := sumcheck_test_sound c s h hsc univ I hI T' _ _ (hR.sumcheckAnswers h hsc I T' hw ρ hall)
    rw [card_univ] at hb
    refine hb.trans' (card_le_card fun r hr => ?_)
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, implies_true] at hr ⊢
    exact hr

/-- `whirEvent` with the input claim not the instance's sum. -/
def whirFalse (c : Cert) (s : State) (wc : WhirCert) (I : Inst E wc.rounds.length) (val : (ℕ → K) → Val)
    (ρ : ℕ → K) : Prop :=
  whirEvent c s wc I val ρ ∧ Model.ev (val ρ) wc.claim0 ≠ I.sum

/-- `oddEvent` with some input value not its true children's product. -/
def oddFalse (c : Cert) (s : State) (oc : OddCert) (L R : ℕ → E) (val : (ℕ → K) → Val) (ρ : ℕ → K) : Prop :=
  oddEvent c s oc L R val ρ ∧ ∃ k < oc.m, Model.ev (val ρ) (oc.values.getD k 0) ≠ L k * R k

/-- `topEvent` with some input value not its true children's product. -/
def topFalse (c : Cert) (s : State) (tc : TopCert) (T' : ℕ → ℕ → E) (val : (ℕ → K) → Val) (ρ : ℕ → K) : Prop :=
  topEvent c s tc T' val ρ ∧ ∃ k < tc.m, Model.ev (val ρ) (tc.values.getD k 0) ≠ T' k 0 * T' k 1 * T' k 2 * T' k 3

open Classical in
/-- WHIR's sumcheck over a uniform oracle, at each oracle: the oracles at which `whirEvent` holds and the input claim
is not the instance's sum (`whirFalse`) are at most an `n · d / |E|` fraction. The claim is bound before the first
challenge, so it is one value over the vectors put in at an oracle. -/
theorem whir_run_sound_at (h : c.accepts s = true) {wc : WhirCert} (hwc : wc ∈ c.whirs) (I : Inst E wc.rounds.length)
    (hI : I.ok wc.deg) (hR : Run c s wc.transcript st val)
    (hw : ∀ r (i : Fin wc.rounds.length), (wc.rounds.getD i default).weight = I.weight r i)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD wc.transcript default) ⊆ U) :
    (#{ρ : U → K | whirFalse c s wc I val (extU _ ρ)} : ℚ≥0) / Fintype.card (U → K) ≤
      ((wc.rounds.length * wc.deg : ℕ) : ℚ≥0) / Fintype.card E := by
  obtain ⟨hc, hok⟩ := Cert.whir_chals h hwc
  obtain ⟨hown, hinj, hmono, -⟩ := chalsOk_sem hc fun i => ChalCert.ok_words (hok i).1
  have hall := (Cert.accepts_rounds h).2.2.2.2
  simp only [Cert.lateOk, Cert.whirsOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hall
  obtain ⟨⟨⟨⟨⟨htr, -⟩, -⟩, -⟩, hb0⟩, -⟩ := hall.2 wc hwc
  refine run_frac hinj (fun i k => hU (own_mem_oracleWords hown i k)) (whirFalse c s wc I val) _
    fun ρ => mul_card_le ?_
  let v := fun r => val (oracleAt (chalWords c.outs wc.chals) ρ r)
  refine (card_le_card fun r hr => ?_).trans (card_at (fun _ => True)
    (fun r => (∀ a b, s.unions[wc.test]? = some (a, b) → v r a = v r b) ∧ Model.ev (v r) wc.final = I.final r)
    (fun r => Model.ev (v r) wc.claim0 ≠ I.sum) _ (fun r r' _ _ hb => ?_) fun hall => ?_)
  · simp only [mem_filter, mem_univ, true_and, whirFalse, whirEvent, readR_oracleAt hinj] at hr ⊢
    exact ⟨hr.1, hr.2⟩
  · rcases Nat.eq_zero_or_pos wc.rounds.length with h0 | hpos
    · have : r = r' := funext fun i => absurd i.isLt (by omega)
      rwa [← this]
    · have hagree := bound_agree h htr (hR.rom.comp fun r => oracleAt (chalWords c.outs wc.chals) ρ r) r r'
        (boundBy_wires hb0 _ (List.mem_singleton_self _))
        (hR.seed_at hown hinj ρ _ r r' fun j _ => by
          rcases Nat.eq_zero_or_pos j.val with hj | hj
          · obtain rfl : j = ⟨0, hpos⟩ := Fin.ext hj
            exact le_rfl
          · exact hmono ⟨0, hpos⟩ j hj)
      rwa [← hagree]
  · have hb := whir_test_sound c s h hwc univ I hI _ _ (hR.whirAnswers h hwc I hw ρ fun r => hall r trivial)
    rw [card_univ] at hb
    refine hb.trans' (card_le_card fun r hr => ?_)
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, implies_true] at hr ⊢
    exact hr

open Classical in
/-- GKR's odd layer over a uniform oracle, at each oracle: the oracles at which `oddEvent` holds and some input value
is not its true children's product (`oddFalse`) are at most an `m / |E|` fraction. The values are bound before `λ`,
so they are one list over the vectors put in at an oracle. -/
theorem odd_run_sound_at (h : c.accepts s = true) {oc : OddCert} (hoc : oc ∈ c.odds) (L R : ℕ → E)
    (hR : Run c s oc.transcript st val)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD oc.transcript default) ⊆ U) :
    (#{ρ : U → K | oddFalse c s oc L R val (extU _ ρ)} : ℚ≥0) / Fintype.card (U → K) ≤ oc.m / Fintype.card E := by
  obtain ⟨hc, hok⟩ := Cert.odd_chals h hoc
  obtain ⟨hown, hinj, hmono, -⟩ := chalsOk_sem hc fun i => ChalCert.ok_words (hok i)
  have hall := (Cert.accepts_rounds h).2.2.1
  simp only [Cert.oddsOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hall
  obtain ⟨⟨⟨⟨⟨⟨⟨htr, -⟩, -⟩, -⟩, -⟩, -⟩, hb0⟩, -⟩ := hall oc hoc
  refine run_frac hinj (fun i k => hU (own_mem_oracleWords hown i k)) (oddFalse c s oc L R val) _ fun ρ => ?_
  let v := fun r => val (oracleAt (chalWords c.outs oc.chals) ρ r)
  have hcount : #{r : Fin 2 → E | oddFalse c s oc L R val (oracleAt (chalWords c.outs oc.chals) ρ r)} ≤
      oc.m * Fintype.card E := by
    refine (card_le_card fun r hr => ?_).trans (card_at (fun _ => True)
      (fun r => (∀ a b, s.unions[oc.test]? = some (a, b) → v r a = v r b) ∧
        ∀ k < oc.m, Model.ev (v r) (oc.out c.outs k) = L k + r 1 * (L k + R k))
      (fun r => ∃ k < oc.m, Model.ev (v r) (oc.values.getD k 0) ≠ L k * R k) _ (fun r r' _ _ hb => ?_)
      fun hall => ?_)
    · simp only [mem_filter, mem_univ, true_and, oddFalse, oddEvent, readR_oracleAt hinj] at hr ⊢
      exact ⟨hr.1, hr.2⟩
    · obtain ⟨k, hk, hne⟩ := hb
      refine ⟨k, hk, ?_⟩
      have hagree := bound_agree h htr (hR.rom.comp fun r => oracleAt (chalWords c.outs oc.chals) ρ r) r r'
        (boundBy_wires hb0 (oc.values.getD k 0) (by
          have hk' : k < oc.values.length := hk
          rw [List.getD_eq_getElem _ _ hk']
          exact List.getElem_mem _))
        (hR.seed_at hown hinj ρ _ r r' fun j _ => by
          fin_cases j
          · exact le_rfl
          · exact hmono 0 1 (by decide))
      rwa [← hagree]
    · have hb := odd_test_sound c s h hoc univ L R _ _ (hR.oddAnswers h hoc L R ρ fun r => hall r trivial)
      rw [card_univ] at hb
      refine hb.trans' (card_le_card fun r hr => ?_)
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, implies_true] at hr ⊢
      exact hr
  calc _ ≤ oc.m * Fintype.card E * Fintype.card E := Nat.mul_le_mul_right _ hcount
    _ = oc.m * Fintype.card E ^ 2 := by ring

open Classical in
/-- GKR's radix-four top layer over a uniform oracle, at each oracle: the oracles at which `topEvent` holds and some
input value is not its true children's product (`topFalse`) are at most an `(m + 1) / |E|` fraction. -/
theorem top_run_sound_at (h : c.accepts s = true) {tc : TopCert} (htc : tc ∈ c.tops) (T' : ℕ → ℕ → E)
    (hR : Run c s tc.transcript st val)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD tc.transcript default) ⊆ U) :
    (#{ρ : U → K | topFalse c s tc T' val (extU _ ρ)} : ℚ≥0) / Fintype.card (U → K) ≤
      (tc.m + 1 : ℕ) / Fintype.card E := by
  obtain ⟨hc, hok⟩ := Cert.top_chals h htc
  obtain ⟨hown, hinj, hmono, -⟩ := chalsOk_sem hc fun i => ChalCert.ok_words (hok i)
  have hall := (Cert.accepts_rounds h).2.2.2.2
  simp only [Cert.lateOk, Cert.topsOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hall
  obtain ⟨⟨htops, -⟩, -⟩ := hall
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨htr, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hb0⟩, -⟩ := htops tc htc
  refine run_frac hinj (fun i k => hU (own_mem_oracleWords hown i k)) (topFalse c s tc T' val) _ fun ρ => ?_
  let v := fun r => val (oracleAt (chalWords c.outs tc.chals) ρ r)
  have hcount : #{r : Fin 3 → E | topFalse c s tc T' val (oracleAt (chalWords c.outs tc.chals) ρ r)} ≤
      (tc.m + 1) * Fintype.card E ^ 2 := by
    refine (card_le_card fun r hr => ?_).trans (card_at (fun _ => True)
      (fun r => (∀ a b, s.unions[tc.test]? = some (a, b) → v r a = v r b) ∧
        ∀ k < tc.m, Model.ev (v r) (tc.out c.outs k) =
          lineE (lineE (T' k 0) (T' k 1) (r 1)) (lineE (T' k 2) (T' k 3) (r 1)) (r 2))
      (fun r => ∃ k < tc.m, Model.ev (v r) (tc.values.getD k 0) ≠ T' k 0 * T' k 1 * T' k 2 * T' k 3) _
      (fun r r' _ _ hb => ?_) fun hall => ?_)
    · simp only [mem_filter, mem_univ, true_and, topFalse, topEvent, readR_oracleAt hinj] at hr ⊢
      exact ⟨hr.1, hr.2⟩
    · obtain ⟨k, hk, hne⟩ := hb
      refine ⟨k, hk, ?_⟩
      have hagree := bound_agree h htr (hR.rom.comp fun r => oracleAt (chalWords c.outs tc.chals) ρ r) r r'
        (boundBy_wires hb0 (tc.values.getD k 0) (by
          have hk' : k < tc.values.length := hk
          rw [List.getD_eq_getElem _ _ hk']
          exact List.getElem_mem _))
        (hR.seed_at hown hinj ρ _ r r' fun j _ => by
          fin_cases j
          · exact le_rfl
          · exact hmono 0 1 (by decide)
          · exact hmono 0 2 (by decide))
      rwa [← hagree]
    · have hb := top_test_sound c s h htc univ T' _ _ (hR.topAnswers h htc T' ρ fun r => hall r trivial)
      rw [card_univ] at hb
      refine hb.trans' (card_le_card fun r hr => ?_)
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, implies_true] at hr ⊢
      exact hr
  calc _ ≤ (tc.m + 1) * Fintype.card E ^ 2 * Fintype.card E := Nat.mul_le_mul_right _ hcount
    _ = (tc.m + 1) * Fintype.card E ^ 3 := by ring

/-! Proof of work in the ideal compression model. -/

/-- A uniform oracle's word at `q` is uniform: each value is taken at a `1 / |K|` fraction of the oracles. -/
theorem card_coord {ι : Type} [Fintype ι] [DecidableEq ι] (q : ι) (x : K) :
    Fintype.card K * #{ω : ι → K | ω q = x} = Fintype.card (ι → K) := by
  have hall : ∀ y, #{ω : ι → K | ω q = y} = #{ω : ι → K | ω q = x} := fun y => by
    refine card_bij (fun ω _ => Function.update ω q x) (fun ω _ => by simp) (fun a ha b hb hab => ?_)
      fun b hb => ⟨Function.update b q y, by simp, ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at ha hb
      funext i
      by_cases hi : i = q
      · subst hi; rw [ha, hb]
      · simpa [hi] using congrFun hab i
    · simp only [mem_filter, mem_univ, true_and] at hb
      funext i
      by_cases hi : i = q
      · subst hi; simp [hb]
      · simp [hi]
  calc Fintype.card K * #{ω : ι → K | ω q = x} = ∑ y : K, #{ω : ι → K | ω q = y} := by
        simp only [hall, sum_const, card_univ, smul_eq_mul]
    _ = Fintype.card (ι → K) := by
        rw [← card_univ (α := ι → K),
          card_eq_sum_card_fiberwise (f := fun ω : ι → K => ω q) (t := univ) (by simp)]

open Classical in
/-- Proof of work over a uniform oracle, in the ideal compression model. A prover makes `Q` trials, trial `q`'s
compression answered by the oracle's word `ω q`, and picks one, `qOf ω`; at each oracle its assignment holds every
replayed call but the trial's compression (`FactsBut`), whose digest's first word is the picked trial's answer. The
oracles at which the proof-of-work tests hold are at most a `Q / 2^b` fraction. -/
theorem pow_run_sound (h : c.accepts s = true) {pc : PowCert} (hpc : pc ∈ c.pows) (Q : ℕ)
    (st' : (Fin Q → K) → ℕ → Fin 4 → K) (val' : (Fin Q → K) → Val) (qOf : (Fin Q → K) → Fin Q)
    (hF : ∀ ω, FactsBut c.calls c.relax c.outs pc.compressAt (st' ω) (val' ω))
    (htrial : ∀ ω, val' ω (PowCert.trial c.outs pc) 0 = ω (qOf ω)) :
    (#{ω | ∀ k < pc.bits, val' ω (pc.bit c.outs (64 - pc.bits + k)) 0 = 0} : ℚ≥0) /
        Fintype.card (Fin Q → K) ≤ Q / 2 ^ pc.bits := by
  let wd : ℕ → (Fin Q → K) → Fin (2 ^ 64) := fun (q : ℕ) (ω : Fin Q → K) =>
    if hq : q < Q then ⟨toWord (ω ⟨q, hq⟩), num_lt _ _⟩ else 0
  refine pow_test_sound c s h hpc Q wd (fun q hq v => ?_) (fun ω => (qOf ω).val) (fun ω => (qOf ω).isLt) st' val'
    hF fun ω => ?_
  · have hset : ({ω : Fin Q → K | wd q ω = v} : Finset (Fin Q → K)) =
        ({ω : Fin Q → K | ω ⟨q, hq⟩ = ofWord v.val} : Finset (Fin Q → K)) := by
      ext ω
      simp only [mem_filter, mem_univ, true_and, wd, dif_pos hq]
      constructor
      · intro hv
        apply toWord_injective
        rw [toWord_ofWord _ v.isLt, ← hv]
      · intro hv
        exact Fin.ext ((congrArg toWord hv).trans (toWord_ofWord _ v.isLt))
    rw [hset]
    have := card_coord (⟨q, hq⟩ : Fin Q) (ofWord v.val)
    rw [card_K] at this
    exact this
  · simp only [wd, dif_pos (qOf ω).isLt, htrial ω]

end LeanVMCircuits.Rec.Bind
