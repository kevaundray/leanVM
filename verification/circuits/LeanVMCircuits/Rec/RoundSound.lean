module

public import LeanVMCircuits.Rec.UnionCover
public import LeanVMCircuits.Rec.Rounds

@[expose] public section

/-!
Sumcheck's soundness on the circuit's tests.

An accepted certificate names sumchecks (`Cert.sumchecksOk`): each round's calls (`RoundCert.ok`), the test of its last
claim, each round's challenge drawn by a squeeze of its transcript after its first `time` blocks (`RoundCert.chalOk`),
and what the round's prover sends, its eq weight and the input claim bound by those blocks (`SumcheckCert.boundOk`).

`sumcheck_test_sound` applies `Sumcheck.sumcheck_sound` to such a test. The honest instance is an explicit interface
(`Sumcheck.Inst`, the committed witness's truths: its round polynomials, each round's eq weight, the final value at
each challenge vector). The prover answers each challenge vector `r` of `S^n` with an assignment holding every
constraint but the tests, whose challenges are `r`, and whose transcript's blocks before round `i`'s challenge read
only the challenges before it (the random oracle's view of a prover that may adapt to every challenge so far). If the
input claim is not the instance's sum, the challenge vectors at which the test holds with the test's other side the
instance's final value are at most `n · d · |S|^(n-1)`. Where the other side is not the final value, the claims the
reduction outputs (the next layer's values, or an opening) are false, which the next reduction's test is for.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Sumcheck Polynomial

/-- A wire whose limbs a transcript binds by `time` is a function of what its first `time` blocks absorb. -/
theorem bound_agree {c : Cert} {s : State} (h : c.accepts s = true) {T : ℕ} (hT : T < (c.marks s).length)
    {st st' : ℕ → Fin 4 → K} {val val' : Val} (hv : Holds st s c.test val) (hv' : Holds st' s c.test val')
    (hcr : HashCR s val val') (hwin : WindowCR s val val') {time w : ℕ}
    (hb : ∀ n ∈ limbs3 w, ∃ k, ((c.marks s).getD T default).2.getD n none = some k ∧ k ≤ time)
    (hs : ∀ m ∈ seedsBefore s (c.transcripts.getD T default).blocks time, nu val m = nu val' m) :
    Model.ev val w = Model.ev val' w := by
  obtain ⟨hr, -, hun, -, -, -⟩ := Cert.accepts_parts h
  refine ev_eq_of_limbs3 fun n hn => ?_
  obtain ⟨k, hk, hle⟩ := hb n hn
  rw [Cert.marks_getD c s hT] at hk
  exact closure_agree (rules_valid hr hv hv' hcr hwin (unionsValid c s hun hv hv' hcr)) hs
    ((Cert.times_sound c s _ hk).mono (seedsBefore_mono hle))

theorem boundOk_wires {m : Array (Option ℕ)} {sc : SumcheckCert} {i : ℕ} (h : sc.boundOk m i = true) :
    ∀ w ∈ (sc.rounds.getD i default).sent ++ (sc.rounds.getD i default).weight.toList ++
        (if i = 0 then [sc.claim0] else []),
      ∀ n ∈ limbs3 w, ∃ k, m.getD n none = some k ∧ k ≤ (sc.rounds.getD i default).time := by
  intro w hw n hn
  simp only [SumcheckCert.boundOk, List.all_eq_true, List.mem_flatMap] at h
  have := h n ⟨w, hw, hn⟩
  split at this
  · rename_i k hk
    exact ⟨k, hk, of_decide_eq_true this⟩
  · simp at this

/-- A coefficient is one the prover sends or the fixed one. -/
theorem mem_coeffs {rc : RoundCert} {w : ℕ} (hw : w ∈ rc.coeffs) (hlen : rc.fixed < rc.coeffs.length) :
    w ∈ rc.sent ∨ w = rc.coeffs.getD rc.fixed 0 := by
  rw [← List.take_append_drop rc.fixed rc.coeffs, List.drop_eq_getElem_cons hlen] at hw
  simp only [List.mem_append, List.mem_cons] at hw
  rw [RoundCert.sent, List.eraseIdx_eq_take_drop_succ]
  rcases hw with hw | hw | hw
  · exact Or.inl (List.mem_append_left _ hw)
  · right
    rw [hw, List.getD_eq_getElem _ _ hlen]
  · exact Or.inl (List.mem_append_right _ hw)

theorem mem_tail {rc : RoundCert} {w : ℕ} (hw : w ∈ rc.coeffs.drop (rc.fixed + 1)) : w ∈ rc.sent := by
  rw [RoundCert.sent, List.eraseIdx_eq_take_drop_succ]
  exact List.mem_append_right _ hw

/-- Two assignments where every replayed call holds, agreeing on a round's claim, weight and what its prover sends,
agree on its coefficients. -/
theorem coeffs_agree {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st st' : ℕ → Fin 4 → K}
    {val val' : Val} (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') {rc : RoundCert} {d claim : ℕ}
    (hok : rc.ok os cs rl d claim = true) (hcl : Model.ev val claim = Model.ev val' claim)
    (hw : ∀ e ∈ rc.weight.toList, Model.ev val e = Model.ev val' e)
    (hs : ∀ w ∈ rc.sent, Model.ev val w = Model.ev val' w) :
    rc.coeffs.map (Model.ev val) = rc.coeffs.map (Model.ev val') := by
  simp only [RoundCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hlen, hge⟩, htl⟩, hhl⟩, hfx⟩, hcalls⟩ := hok
  simp only [RoundCert.calls, callsOk_append, Bool.and_eq_true] at hcalls
  obtain ⟨⟨hhead, hfold⟩, -⟩ := hcalls
  obtain ⟨hz, hrest⟩ := callsOk_cons hhead
  obtain ⟨-, hfc⟩ := callsOk_cons hrest
  have hfix : rc.fixed < rc.coeffs.length := by
    unfold RoundCert.fixed; split <;> omega
  -- The tail is a sum of sent coefficients, from a zero.
  have htail : Model.ev val (rc.tail os) = Model.ev val' (rc.tail os) := by
    have hz' : ∀ {st : ℕ → Fin 4 → K} {val : Val}, Facts cs rl os st val → Model.ev val (o os rc.tailZero) = 0 :=
      fun hF => holds_of_mem hF hz (List.mem_singleton_self _)
    rw [RoundCert.tail, fold_sem hF _ _ _ (by simp; omega) hfold, fold_sem hF' _ _ _ (by simp; omega) hfold,
      hz' hF, hz' hF', List.map_congr_left fun w hw => hs w (mem_tail hw)]
  have hfixed : Model.ev val (rc.coeffs.getD rc.fixed 0) = Model.ev val' (rc.coeffs.getD rc.fixed 0) := by
    have h1 : (rc.fixedCall os claim).Holds st val (os.getD rc.fixedAt []) :=
      holds_of_mem hF hfc (List.mem_singleton_self _)
    have h2 : (rc.fixedCall os claim).Holds st' val' (os.getD rc.fixedAt []) :=
      holds_of_mem hF' hfc (List.mem_singleton_self _)
    rw [← hfx]
    unfold RoundCert.fixedCall at h1 h2
    split at h1 <;> rename_i e he <;> simp only [he, Call.Holds, getD_o] at h1 h2
    · rw [h1, h2, htail, hcl, hw e (by simp [he])]
    · rw [h1, h2, htail, hcl]
  exact List.map_congr_left fun w hw => (mem_coeffs hw hfix).elim (hs w) fun he => he ▸ hfixed

open Classical Finset in
/-- Sumcheck's soundness on a certified test. Take an accepted circuit and a sumcheck it names (`sc`, `n` rounds of
degree `d`), and the honest instance `I` of degree `d`, whose eq weights are the circuit's. For each challenge vector
`r` the prover answers with an assignment holding every constraint but the tests, whose round challenges are `r`,
whose compressions and output windows do not collide with another answer's, and which agrees with every answer whose
challenges before round `i` are the same on what the transcript's blocks before round `i`'s challenge absorb. If the
input claim is not the instance's sum, the challenge vectors of `S^n` at which the test holds and its other side is
the instance's final value are at most `n · d · |S|^(n-1)`. -/
theorem sumcheck_test_sound (c : Cert) (s : State) (h : c.accepts s = true) {sc : SumcheckCert}
    (hsc : sc ∈ c.sumchecks) (S : Finset E) (I : Inst E sc.rounds.length) (hI : I.ok sc.deg)
    (st : (Fin sc.rounds.length → E) → ℕ → Fin 4 → K) (val : (Fin sc.rounds.length → E) → Val)
    (hv : ∀ r, Holds (st r) s c.test (val r)) (hcr : ∀ r r', HashCR s (val r) (val r'))
    (hwin : ∀ r r', WindowCR s (val r) (val r'))
    (hseed : ∀ r r' (i : Fin sc.rounds.length), (∀ j < i, r j = r' j) →
      ∀ m ∈ seedsBefore s (c.transcripts.getD sc.transcript default).blocks (sc.rounds.getD i default).time,
        nu (val r) m = nu (val r') m)
    (hchal : ∀ r (i : Fin sc.rounds.length), Model.ev (val r) (sc.rounds.getD i default).chal = r i)
    (hw : ∀ r (i : Fin sc.rounds.length), (sc.rounds.getD i default).weight.map (Model.ev (val r)) = I.weight r i)
    (hne : ∀ r, Model.ev (val r) sc.claim0 ≠ I.sum) :
    #{r ∈ Fintype.piFinset (fun _ : Fin sc.rounds.length => S) |
        (∀ a b, s.unions[sc.test]? = some (a, b) → val r a = val r b) ∧ Model.ev (val r) sc.final = I.final r} ≤
      sc.rounds.length * sc.deg * #S ^ (sc.rounds.length - 1) := by
  have hall := (Cert.accepts_rounds h).1
  simp only [Cert.sumchecksOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hall
  obtain ⟨⟨⟨⟨htr, hok⟩, -⟩, hpair⟩, hrounds⟩ := hall sc hsc
  simp only [SumcheckCert.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hpos, hok⟩ := hok
  have hF : ∀ r, Facts c.calls c.relax c.outs (st r) (val r) :=
    fun r => (facts_of_holds (Cert.accepts_parts h).2.2.1 (hv r)).1
  have hbound : ∀ i < sc.rounds.length, sc.boundOk ((c.marks s).getD sc.transcript default).2 i = true :=
    fun i hi => (hrounds i hi).2
  -- Round `i`'s polynomial and claims along `r`.
  set g : (Fin sc.rounds.length → E) → Fin sc.rounds.length → E[X] := fun r i => polyOf ((sc.rounds.getD i default).coeffs.map (Model.ev (val r)))
  set cl : (Fin sc.rounds.length → E) → Fin (sc.rounds.length + 1) → E := fun r k => Model.ev (val r) (sc.claimAt c.outs k)
  have hsem : ∀ r (i : Fin sc.rounds.length), (g r i).natDegree ≤ sc.deg ∧
      lin (I.weight r i) (g r i) = cl r i.castSucc ∧ cl r i.succ = (g r i).eval (r i) := by
    intro r i
    obtain ⟨h1, h2, h3⟩ := sumRound_sem (hF r) (hok i i.isLt)
    refine ⟨h1, by rw [← hw r i]; exact h2, ?_⟩
    simp only [cl, Fin.val_succ, SumcheckCert.claimAt, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [h3, hchal r i]
  -- What a round's prover sends, its weight and its claim agree between answers agreeing on the challenges before it.
  have hagree : ∀ i, (hi : i < sc.rounds.length) → ∀ r r', (∀ j : Fin sc.rounds.length, j.val < i → r j = r' j) →
      cl r ⟨i, by omega⟩ = cl r' ⟨i, by omega⟩ ∧ g r ⟨i, hi⟩ = g r' ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi r r' hrr
      have hs := hseed r r' ⟨0, hi⟩ fun j hj => absurd hj (by simp [Fin.lt_def])
      have hb := boundOk_wires (hbound 0 hi)
      have h0 : cl r ⟨0, by omega⟩ = cl r' ⟨0, by omega⟩ := by
        simp only [cl, SumcheckCert.claimAt, if_true]
        exact bound_agree h htr (hv r) (hv r') (hcr r r') (hwin r r') (hb _ (by simp)) hs
      refine ⟨h0, congrArg polyOf (coeffs_agree (hF r) (hF r') (hok 0 hi) h0 (fun e he => ?_) fun w hw => ?_)⟩
      · exact bound_agree h htr (hv r) (hv r') (hcr r r') (hwin r r') (hb _ (List.mem_append_left _ (List.mem_append_right _ he))) hs
      · exact bound_agree h htr (hv r) (hv r') (hcr r r') (hwin r r') (hb _ (List.mem_append_left _ (List.mem_append_left _ hw))) hs
    | succ i ih =>
      intro hi r r' hrr
      have hs := hseed r r' ⟨i + 1, hi⟩ fun j hj => hrr j hj
      have hb := boundOk_wires (hbound (i + 1) hi)
      obtain ⟨-, hg⟩ := ih (by omega) r r' fun j hj => hrr j (by omega)
      have hcl : cl r ⟨i + 1, by omega⟩ = cl r' ⟨i + 1, by omega⟩ := by
        have e1 := (hsem r ⟨i, by omega⟩).2.2
        have e2 := (hsem r' ⟨i, by omega⟩).2.2
        simp only [Fin.succ_mk] at e1 e2
        rw [e1, e2, hg, hrr ⟨i, by omega⟩ (by simp)]
      refine ⟨hcl, congrArg polyOf (coeffs_agree (hF r) (hF r') (hok (i + 1) hi) hcl (fun e he => ?_)
        fun w hw => ?_)⟩
      · exact bound_agree h htr (hv r) (hv r') (hcr r r') (hwin r r') (hb _ (List.mem_append_left _ (List.mem_append_right _ he))) hs
      · exact bound_agree h htr (hv r) (hv r') (hcr r r') (hwin r r') (hb _ (List.mem_append_left _ (List.mem_append_left _ hw))) hs
  have hpre : PrefixDep g := fun r r' i hrr => (hagree i i.isLt r r' fun j hj => hrr j hj).2
  -- The input claim is one value.
  set r₀ : Fin sc.rounds.length → E := fun _ => 0
  have hc0 : ∀ r, cl r 0 = cl r₀ 0 := fun r => (hagree 0 hpos r r₀ fun j hj => absurd hj (Nat.not_lt_zero _)).1
  refine le_trans (card_le_card fun r hr => ?_)
    (sumcheck_sound_fun S sc.deg I hI g hpre (fun r i => (hsem r i).1) cl (cl r₀ 0) (hne r₀))
  simp only [mem_filter] at hr ⊢
  obtain ⟨hS, htest, hfin⟩ := hr
  refine ⟨hS, hc0 r, fun i => (hsem r i).2.1, fun i => (hsem r i).2.2, ?_⟩
  have hlast : cl r (Fin.last sc.rounds.length) = Model.ev (val r) sc.final := by
    simp only [cl, Fin.val_last]
    rcases hpair with hp | hp
    · simp only [Model.ev, htest _ _ hp]
    · simp only [Model.ev, ← htest _ _ hp]
  rw [hlast, hfin]

/-! Proof of work. -/

open Classical Finset in
/-- The words below `2^m`, `m ≤ 64`, are `2^m`. -/
theorem card_low_words {m : ℕ} (hm : m ≤ 64) : #{v : Fin (2 ^ 64) | v.val < 2 ^ m} = 2 ^ m := by
  have hlt : ∀ x < 2 ^ m, x < 2 ^ 64 := fun x hx => lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hm)
  have he : ({v : Fin (2 ^ 64) | v.val < 2 ^ m} : Finset (Fin (2 ^ 64))).map Fin.valEmbedding = range (2 ^ m) := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, hlt x hx⟩, hx, rfl⟩
  rw [← card_map, he, card_range]

open Classical Finset in
/-- Proof of work's grinding bound. A prover makes `Q` trials, trial `q`'s first output word `wd q` uniform on 64-bit
words over the outcomes `Ω`, and picks one, `qOf ω`. The outcomes at which the picked trial's word has its top `b` bits
zero are at most a `Q / 2^b` fraction: each passing proof costs about `2^b` compressions. -/
theorem grinding_bound (b : ℕ) (hb : b ≤ 64) (Q : ℕ) {Ω : Type} [Fintype Ω] (wd : ℕ → Ω → Fin (2 ^ 64))
    (hwd : ∀ q < Q, ∀ v : Fin (2 ^ 64), 2 ^ 64 * #{ω | wd q ω = v} = Fintype.card Ω) (qOf : Ω → ℕ)
    (hq : ∀ ω, qOf ω < Q) :
    (#{ω | (wd (qOf ω) ω).val < 2 ^ (64 - b)} : ℚ≥0) / Fintype.card Ω ≤ Q / 2 ^ b := by
  set B : ℕ → Finset Ω := fun q => {ω | (wd q ω).val < 2 ^ (64 - b)}
  -- One trial passes at a `1 / 2^b` fraction of the outcomes.
  have hone : ∀ q < Q, 2 ^ b * #(B q) = Fintype.card Ω := by
    intro q hqQ
    have hsplit : B q = ({v : Fin (2 ^ 64) | v.val < 2 ^ (64 - b)} : Finset (Fin (2 ^ 64))).biUnion
        fun v => {ω | wd q ω = v} := by
      ext ω
      simp [B]
    have hdisj : (({v : Fin (2 ^ 64) | v.val < 2 ^ (64 - b)} : Finset (Fin (2 ^ 64))) : Set (Fin (2 ^ 64))).PairwiseDisjoint
        fun v => ({ω | wd q ω = v} : Finset Ω) := by
      intro v _ v' _ hvv'
      simp only [Function.onFun]
      rw [disjoint_left]
      intro ω h1 h2
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      exact hvv' (h1.symm.trans h2)
    have hsum : 2 ^ 64 * #(B q) = 2 ^ (64 - b) * Fintype.card Ω := by
      rw [hsplit, card_biUnion hdisj, mul_sum, sum_congr rfl fun v _ => hwd q hqQ v, sum_const, smul_eq_mul,
        card_low_words (by omega)]
    have h64 : (2 : ℕ) ^ 64 = 2 ^ (64 - b) * 2 ^ b := by rw [← pow_add]; congr 1; omega
    rw [h64, mul_assoc] at hsum
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hsum
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
  · rw [h0]; simp
  have hsub : ({ω | (wd (qOf ω) ω).val < 2 ^ (64 - b)} : Finset Ω) ⊆ (range Q).biUnion B := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    exact mem_biUnion.mpr ⟨qOf ω, mem_range.mpr (hq ω), by simp [B, hω]⟩
  have hc : (Fintype.card Ω : ℚ≥0) ≠ 0 := by exact_mod_cast h0.ne'
  calc (#{ω | (wd (qOf ω) ω).val < 2 ^ (64 - b)} : ℚ≥0) / Fintype.card Ω
      ≤ (∑ q ∈ range Q, (#(B q) : ℚ≥0)) / Fintype.card Ω := by
        gcongr
        exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    _ = ∑ _q ∈ range Q, (1 / 2 ^ b : ℚ≥0) := by
        rw [sum_div]
        refine sum_congr rfl fun q hqQ => ?_
        have := hone q (mem_range.mp hqQ)
        rw [div_eq_div_iff hc (by positivity), one_mul]
        exact_mod_cast (by rw [mul_comm]; exact this.symm : (Fintype.card Ω : ℕ) = #(B q) * 2 ^ b).symm
    _ = Q / 2 ^ b := by rw [sum_const, card_range, nsmul_eq_mul, mul_one_div]

open Classical Finset in
/-- Proof of work on the circuit. Take an accepted circuit and a proof-of-work check it names (`pc`, difficulty
`b`). For each outcome the prover answers with an assignment holding every constraint but the tests whose trial
compression's first output word is the word of the trial it picked among `Q`, each uniform. Then the outcomes at which
the check's tests hold (the word's top `b` bits zero) are at most a `Q / 2^b` fraction. -/
theorem pow_test_sound (c : Cert) (s : State) (h : c.accepts s = true) {pc : PowCert} (hpc : pc ∈ c.pows) (Q : ℕ)
    {Ω : Type} [Fintype Ω] (wd : ℕ → Ω → Fin (2 ^ 64))
    (hwd : ∀ q < Q, ∀ v : Fin (2 ^ 64), 2 ^ 64 * #{ω | wd q ω = v} = Fintype.card Ω) (qOf : Ω → ℕ)
    (hq : ∀ ω, qOf ω < Q) (st : Ω → ℕ → Fin 4 → K) (val : Ω → Val) (hv : ∀ ω, Holds (st ω) s c.test (val ω))
    (htrial : ∀ ω acc x ds, c.calls[pc.compressAt]? = some (.compress acc x ds) →
      (Rec.node (words4 (val ω acc)) (words4 (xds (val ω) x ds)) 0).toNat = (wd (qOf ω) ω).val) :
    (#{ω | ∀ k < pc.bits, val ω (pc.bit c.outs (64 - pc.bits + k)) 0 = 0} : ℚ≥0) / Fintype.card Ω ≤
      Q / 2 ^ pc.bits := by
  have hok : pc.ok c.outs c.calls c.relax = true := by
    have := (Cert.accepts_rounds h).2.1
    simp only [Array.all_eq_true'] at this
    exact this pc hpc
  have hb : pc.bits ≤ 64 := by
    simp only [PowCert.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1
  refine le_trans (div_le_div_of_nonneg_right ?_ (by positivity)) (grinding_bound pc.bits hb Q wd hwd qOf hq)
  refine Nat.cast_le.mpr (card_le_card fun ω hω => ?_)
  simp only [mem_filter, mem_univ, true_and] at hω ⊢
  obtain ⟨acc, x, ds, hc, hlt⟩ := pow_sem (facts_of_holds (Cert.accepts_parts h).2.2.1 (hv ω)).1 hok hω
  rwa [← htrial ω acc x ds hc]

/-! GKR's odd layer. -/

theorem boundBy_wires {m : Array (Option ℕ)} {ws : List ℕ} {time : ℕ} (h : boundBy m ws time = true) :
    ∀ w ∈ ws, ∀ n ∈ limbs3 w, ∃ k, m.getD n none = some k ∧ k ≤ time := by
  intro w hw n hn
  simp only [boundBy, List.all_eq_true, List.mem_flatMap] at h
  have := h n ⟨w, hw, hn⟩
  split at this
  · rename_i k hk
    exact ⟨k, hk, of_decide_eq_true this⟩
  · simp at this

theorem map_eq_range {α β : Type} (f : α → β) (d : α) (l : List α) :
    l.map f = (List.range l.length).map fun k => f (l.getD k d) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem?_eq_getElem (show i < l.length by simpa using h1)]

open Classical Finset in
/-- GKR's odd layer on the circuit. Take an accepted circuit and an odd layer it names (`oc`, `m` values), and the
layer's true children `L k`, `R k`. For each pair `r` of challenges (`λ`, then the next) the prover answers with an
assignment holding every constraint but the tests, whose challenges are `r`, whose compressions and output windows do
not collide with another answer's, which agrees with every answer on the blocks before `λ` and with every answer of
the same `λ` on the blocks before the next challenge. If some input value is not its children's product, the pairs of
`S^2` at which the test holds and every next claim is its value's true line at the next challenge are at most
`m · |S|`: an `m / |S|` fraction. -/
theorem odd_test_sound (c : Cert) (s : State) (h : c.accepts s = true) {oc : OddCert} (hoc : oc ∈ c.odds)
    (S : Finset E) (L R : ℕ → E) (st : (Fin 2 → E) → ℕ → Fin 4 → K) (val : (Fin 2 → E) → Val)
    (hv : ∀ r, Holds (st r) s c.test (val r)) (hcr : ∀ r r', HashCR s (val r) (val r'))
    (hwin : ∀ r r', WindowCR s (val r) (val r'))
    (hseed0 : ∀ r r', ∀ n ∈ seedsBefore s (c.transcripts.getD oc.transcript default).blocks oc.lam.time,
      nu (val r) n = nu (val r') n)
    (hseed1 : ∀ r r', r 0 = r' 0 →
      ∀ n ∈ seedsBefore s (c.transcripts.getD oc.transcript default).blocks oc.next.time, nu (val r) n = nu (val r') n)
    (hchal : ∀ r, Model.ev (val r) oc.lam.chal = r 0 ∧ Model.ev (val r) oc.next.chal = r 1)
    (hne : ∀ r, ∃ k < oc.m, Model.ev (val r) (oc.values.getD k 0) ≠ L k * R k) :
    #{r ∈ Fintype.piFinset (fun _ : Fin 2 => S) | (∀ a b, s.unions[oc.test]? = some (a, b) → val r a = val r b) ∧
        ∀ k < oc.m, Model.ev (val r) (oc.out c.outs k) = L k + r 1 * (L k + R k)} ≤ oc.m * #S := by
  have hall := (Cert.accepts_rounds h).2.2
  simp only [Cert.oddsOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hall
  obtain ⟨⟨⟨⟨⟨⟨⟨htr, hok⟩, -⟩, hpair⟩, -⟩, -⟩, hb0⟩, hb1⟩ := hall oc hoc
  have hm : 0 < oc.m := by
    simp only [OddCert.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1
  have hF : ∀ r, Facts c.calls c.relax c.outs (st r) (val r) :=
    fun r => (facts_of_holds (Cert.accepts_parts h).2.2.1 (hv r)).1
  have agree := fun r r' {time w : ℕ} hb hs => bound_agree h htr (hv r) (hv r') (hcr r r') (hwin r r') (time := time)
    (w := w) hb hs
  -- The values are bound before `λ`, the children before the next challenge.
  have hval : ∀ r r', ∀ k < oc.m, Model.ev (val r) (oc.values.getD k 0) = Model.ev (val r') (oc.values.getD k 0) :=
    fun r r' k hk => agree r r' (boundBy_wires hb0 _ (getD_mem_of_lt (by simpa [OddCert.m] using hk))) (hseed0 r r')
  have hch : ∀ r r', r 0 = r' 0 → ∀ k < oc.m, Model.ev (val r) (oc.left k) = Model.ev (val r') (oc.left k) ∧
      Model.ev (val r) (oc.right k) = Model.ev (val r') (oc.right k) := by
    intro r r' h0 k hk
    have hmem : oc.left k ∈ (List.range oc.m).flatMap (fun k => [oc.left k, oc.right k]) ∧
        oc.right k ∈ (List.range oc.m).flatMap (fun k => [oc.left k, oc.right k]) :=
      ⟨List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, by simp⟩,
        List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, by simp⟩⟩
    exact ⟨agree r r' (boundBy_wires hb1 _ hmem.1) (hseed1 r r' h0),
      agree r r' (boundBy_wires hb1 _ hmem.2) (hseed1 r r' h0)⟩
  -- The values' differences from the children's products, a nonzero polynomial in `λ`.
  set r₀ : Fin 2 → E := fun _ => 0
  set vs : ℕ → E := fun k => Model.ev (val r₀) (oc.values.getD k 0)
  set D : E[X] := polyOf ((List.range oc.m).map fun k => vs k - L k * R k)
  have hD0 : D ≠ 0 := by
    obtain ⟨k, hk, hk'⟩ := hne r₀
    intro hD
    have := congrArg (fun p => Polynomial.coeff p k) hD
    simp only [D, coeff_polyOf, coeff_zero, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some] at this
    exact hk' (sub_eq_zero.mp this)
  have hDdeg : D.natDegree ≤ oc.m - 1 := (natDegree_polyOf _).trans (by simp)
  set Q : (Fin 2 → E) → Prop := fun r => (∀ a b, s.unions[oc.test]? = some (a, b) → val r a = val r b) ∧
    ∀ k < oc.m, Model.ev (val r) (oc.out c.outs k) = L k + r 1 * (L k + R k)
  set A := ({r ∈ Fintype.piFinset (fun _ : Fin 2 => S) | Q r} : Finset (Fin 2 → E))
  have hext : ∀ r r' : Fin 2 → E, r 0 = r' 0 → r 1 = r' 1 → r = r' := by
    intro r r' h0 h1
    funext i
    fin_cases i
    exacts [h0, h1]
  -- At a `λ` that is no root, two answers passing the test agree on the next challenge.
  have hgood : ∀ a, D.eval a ≠ 0 → #{r ∈ A | r 0 = a} ≤ 1 := by
    intro a ha
    refine card_le_one.mpr fun r1 h1 r2 h2 => ?_
    simp only [A, mem_filter] at h1 h2
    obtain ⟨⟨-, htest, hout1⟩, h10⟩ := h1
    obtain ⟨⟨-, -, hout2⟩, h20⟩ := h2
    obtain ⟨hc1, he1, ho1⟩ := odd_sem (hF r1) hok
    obtain ⟨-, -, ho2⟩ := odd_sem (hF r2) hok
    -- The test: the values' and the products' polynomials agree at `a`.
    have htv : Model.ev (val r1) (oc.claim c.outs) = Model.ev (val r1) (oc.expected c.outs) := by
      rcases hpair with hp | hp
      · simp only [Model.ev, htest _ _ hp]
      · simp only [Model.ev, ← htest _ _ hp]
    rw [hc1, he1, (hchal r1).1, h10, map_eq_range _ 0 oc.values] at htv
    have hvs : (List.range oc.values.length).map (fun k => Model.ev (val r1) (oc.values.getD k 0)) =
        (List.range oc.m).map vs := List.map_congr_left fun k hk => hval r1 r₀ k (List.mem_range.mp hk)
    rw [hvs] at htv
    obtain ⟨k, hk, hkne⟩ : ∃ k < oc.m, Model.ev (val r1) (oc.left k) * Model.ev (val r1) (oc.right k) ≠ L k * R k := by
      by_contra hn
      simp only [not_exists, not_and, not_not] at hn
      apply ha
      have hl : (List.range oc.m).map (fun k => Model.ev (val r1) (oc.left k) * Model.ev (val r1) (oc.right k)) =
          (List.range oc.m).map (fun k => L k * R k) :=
        List.map_congr_left fun k hk => hn k (List.mem_range.mp hk)
      rw [hl] at htv
      have hD : D.eval a = (polyOf ((List.range oc.m).map vs)).eval a -
          (polyOf ((List.range oc.m).map fun k => L k * R k)).eval a := by
        rw [← Polynomial.eval_sub, ← polyOf_map_sub]
      rw [hD, htv, sub_self]
    obtain ⟨hl2, hr2⟩ := hch r2 r1 (h20.trans h10.symm) k hk
    have e1 := (ho1 k hk).symm.trans (hout1 k hk)
    have e2 := (ho2 k hk).symm.trans (hout2 k hk)
    rw [(hchal r1).2] at e1
    rw [(hchal r2).2, hl2, hr2] at e2
    refine hext r1 r2 (h10.trans h20.symm) ?_
    by_contra hx
    have hsub : (r1 1 - r2 1) * ((Model.ev (val r1) (oc.left k) + Model.ev (val r1) (oc.right k)) - (L k + R k)) = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp hsub with h0 | h0
    · exact hx (sub_eq_zero.mp h0)
    · have hs : Model.ev (val r1) (oc.left k) + Model.ev (val r1) (oc.right k) = L k + R k := sub_eq_zero.mp h0
      have hl : Model.ev (val r1) (oc.left k) = L k := by linear_combination e1 - r1 1 * h0
      have hr : Model.ev (val r1) (oc.right k) = R k := by linear_combination hs - hl
      exact hkne (by rw [hl, hr])
  -- At a root, the answers are at most one per next challenge.
  have hbad : ∀ a, #{r ∈ A | r 0 = a} ≤ #S := by
    intro a
    refine card_le_card_of_injOn (fun r => r 1) (fun r hr => ?_) (fun r hr r' hr' he => ?_)
    · simp only [Finset.mem_coe, A, mem_filter, Fintype.mem_piFinset] at hr ⊢
      exact hr.1.1 1
    · simp only [Finset.mem_coe, A, mem_filter] at hr hr'
      exact hext r r' (hr.2.trans hr'.2.symm) he
  have hfib := card_eq_sum_card_fiberwise (s := A) (t := S) (f := fun r => r 0) fun r hr => by
    exact Fintype.mem_piFinset.mp (mem_filter.mp hr).1 0
  calc #A = ∑ a ∈ S, #{r ∈ A | r 0 = a} := hfib
    _ ≤ ∑ a ∈ S, if D.eval a = 0 then #S else 1 := sum_le_sum fun a _ => by
        split
        · exact hbad a
        · exact hgood a (by assumption)
    _ = #{a ∈ S | D.eval a = 0} * #S + #{a ∈ S | ¬ D.eval a = 0} := by
        rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul, mul_one]
    _ ≤ (oc.m - 1) * #S + #S :=
        add_le_add (Nat.mul_le_mul_right _ (card_roots_le S hD0 hDdeg)) (card_le_card (filter_subset _ _))
    _ = oc.m * #S := by
        obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
        rw [hm', Nat.succ_sub_one, Nat.succ_mul]

end LeanVMCircuits.Rec.Bind
