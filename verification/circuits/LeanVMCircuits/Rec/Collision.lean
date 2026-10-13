module

public import LeanVMCircuits.Rec.RecParts
public import LeanVMCircuits.Rec.RoundSound

@[expose] public section

/-!
Collision resistance as a bounded event of the ideal compression model.

`Bind.RomAnswers` asks its answers' compressions (`HashCRP`) and output windows (`WindowCRP`) not to collide, and `Edges.RecParts` names the event `crBad` off which they do not. Here the compression is a uniformly drawn function `h : X → Y` and the prover an adaptive strategy `σ : List Y → X`: its query `i` is `σ` at the answers to its queries before `i` (`query`).

- `Collision.event_card`: for a symmetric relation `R` on answers, the oracles at which two distinct queries among the first `Q` have related answers are at most `e · Q · (Q - 1) / (2 d)` of all, where every answer is related to at most `e / d` of `Y`. The proof charges the event to the first query whose answer is related to an earlier one (`Collision.fresh_card`, by resampling that answer).
- `Collision.birthday_frac`: the adaptive birthday bound, two distinct queries with equal answers on at most `Q · (Q - 1) / (2 |Y|)` of the oracles.
- `Collision.near_frac`: for answers of four words in `V`, two distinct queries whose answers agree on two consecutive words on at most `3 · Q · (Q - 1) / (2 |V|^2)` of the oracles. A window collision (`WindowCRP`) is such an event: of its four words, `4 - j` are one pair's answers and `j` the other's, and one of them is at least two.

`Bind.hashCRP_of_oracle` and `Bind.windowCRP_of_oracle` give `HashCRP` and `WindowCRP` from the ideal model's consistency (`Bind.OracleRows`: every hash row not dropped has its outputs the oracle at its inputs, and its inputs among the queries) and the oracle off those events on the queries. `Bind.RomAnswers.of_oracle` builds `RomAnswers` from them in place of `cr` and `win`.

`Edges.crEvent` is the event over outcomes that pair other coins with the oracle, bounded by `Edges.epsCR` of the number of compression queries (`Edges.crEvent_frac`). `Edges.PcsBound` is the PCS interface (#551), and `Edges.tree_sound_eps` is `tree_sound_parts` with the `pcsBad` and `crBad` fractions replaced by their bounds.
-/

namespace LeanVMCircuits.Rec.Collision

open Finset

variable {X Y : Type}

/-! An adaptive prover against an oracle. -/

/-- The oracle's answers to the prover's first `n` queries: query `i` is the strategy at the answers before it. -/
def answers (σ : List Y → X) (h : X → Y) : ℕ → List Y
  | 0 => []
  | n + 1 => answers σ h n ++ [h (σ (answers σ h n))]

/-- The prover's query `n`. -/
def query (σ : List Y → X) (h : X → Y) (n : ℕ) : X := σ (answers σ h n)

/-- Query `m` is new: no earlier query is it. -/
def Fresh (σ : List Y → X) (h : X → Y) (m : ℕ) : Prop := ∀ i < m, query σ h i ≠ query σ h m

/-- The event of relation `R`: two distinct queries among the first `Q` have related answers. -/
def Event (R : Y → Y → Prop) (σ : List Y → X) (h : X → Y) (Q : ℕ) : Prop :=
  ∃ i < Q, ∃ i' < Q, query σ h i ≠ query σ h i' ∧ R (h (query σ h i)) (h (query σ h i'))

theorem answers_length (σ : List Y → X) (h : X → Y) (n : ℕ) : (answers σ h n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [answers, ih]

theorem mem_answers {σ : List Y → X} {h : X → Y} {i n : ℕ} (hi : i < n) : h (query σ h i) ∈ answers σ h n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [answers, List.mem_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inl (ih hi)
    · exact Or.inr (by simp [query])

/-- Two oracles agreeing on the prover's first `n` queries give it the same answers. -/
theorem answers_congr {σ : List Y → X} {h g : X → Y} {n : ℕ} (hg : ∀ i < n, g (query σ h i) = h (query σ h i)) :
    answers σ g n = answers σ h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e := ih fun i hi => hg i (by omega)
    change answers σ g n ++ [g (σ (answers σ g n))] = answers σ h n ++ [h (σ (answers σ h n))]
    rw [e]
    exact congrArg (fun y => answers σ h n ++ [y]) (hg n (Nat.lt_succ_self n))

theorem query_congr {σ : List Y → X} {h g : X → Y} {n : ℕ} (hg : ∀ i < n, g (query σ h i) = h (query σ h i)) :
    query σ g n = query σ h n := by
  simp only [query, answers_congr hg]

/-- Every query's first occurrence is fresh. -/
theorem first_fresh (σ : List Y → X) (h : X → Y) (i : ℕ) : ∃ a ≤ i, query σ h a = query σ h i ∧ Fresh σ h a := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hf : Fresh σ h i
    · exact ⟨i, le_rfl, rfl, hf⟩
    · simp only [Fresh, not_forall, not_not] at hf
      obtain ⟨i', hi', he⟩ := hf
      obtain ⟨a, ha, hq, hfa⟩ := ih i' hi'
      exact ⟨a, by omega, hq.trans he, hfa⟩

/-- The event lands on a fresh query whose answer is related to an earlier answer. -/
theorem event_fresh {R : Y → Y → Prop} (hR : ∀ y z, R y z → R z y) {σ : List Y → X} {h : X → Y} {Q : ℕ}
    (he : Event R σ h Q) : ∃ m < Q, Fresh σ h m ∧ ∃ z ∈ answers σ h m, R (h (query σ h m)) z := by
  obtain ⟨i, hi, i', hi', hne, hr⟩ := he
  obtain ⟨a, ha, hqa, hfa⟩ := first_fresh σ h i
  obtain ⟨b, hb, hqb, hfb⟩ := first_fresh σ h i'
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact ⟨b, by omega, hfb, _, mem_answers hab, by rw [hqa, hqb]; exact hR _ _ hr⟩
  · exact absurd (hqa.symm.trans hqb) hne
  · exact ⟨a, by omega, hfa, _, mem_answers hab, by rw [hqa, hqb]; exact hr⟩

open Classical in
/-- Resampling a fresh query's answer: the oracles at which fresh query `m`'s answer is in a set `S` of the answers before it, times `|Y|`, are at most the sum over all oracles of `|S|`. -/
theorem fresh_card [Fintype X] [Fintype Y] (σ : List Y → X) (m : ℕ) (S : List Y → Finset Y) :
    (univ.filter fun h : X → Y => Fresh σ h m ∧ h (query σ h m) ∈ S (answers σ h m)).card * Fintype.card Y ≤
      ∑ g : X → Y, (S (answers σ g m)).card := by
  set A := univ.filter fun h : X → Y => Fresh σ h m ∧ h (query σ h m) ∈ S (answers σ h m)
  have hl : A.card * Fintype.card Y = (A ×ˢ (univ : Finset Y)).card := by rw [card_product, card_univ]
  rw [hl, ← card_sigma]
  -- the updated oracle agrees with `h` on the queries before `m`
  have hagree : ∀ h : X → Y, Fresh σ h m → ∀ y, ∀ i < m,
      Function.update h (query σ h m) y (query σ h i) = h (query σ h i) :=
    fun h hf y i hi => Function.update_of_ne (hf i hi) _ _
  refine card_le_card_of_injOn (fun p => (⟨Function.update p.1 (query σ p.1 m) p.2, p.1 (query σ p.1 m)⟩ :
    Σ _ : X → Y, Y)) ?_ ?_
  · intro p hp
    simp only [coe_product, Set.mem_prod, mem_coe, A, mem_filter, mem_univ, true_and] at hp
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_univ, true_and]
    rw [answers_congr (hagree p.1 hp.1.1 p.2)]
    exact hp.1.2
  · rintro ⟨h1, y1⟩ hp1 ⟨h2, y2⟩ hp2 he
    simp only [coe_product, Set.mem_prod, mem_coe, A, mem_filter, mem_univ, true_and] at hp1 hp2
    simp only [Sigma.mk.injEq] at he
    obtain ⟨hg, hz⟩ := he
    have hz := eq_of_heq hz
    have q1 := query_congr (hagree h1 hp1.1.1 y1)
    have q2 := query_congr (hagree h2 hp2.1.1 y2)
    rw [hg] at q1
    have hx : query σ h1 m = query σ h2 m := q1.symm.trans q2
    have hy : y1 = y2 := by
      have := congrFun hg (query σ h1 m)
      rwa [Function.update_self, hx, Function.update_self] at this
    refine Prod.ext ?_ hy
    funext a
    by_cases ha : a = query σ h1 m
    · subst ha
      show h1 (query σ h1 m) = h2 (query σ h1 m)
      rw [hz, hx]
    · have := congrFun hg a
      rw [Function.update_of_ne ha, Function.update_of_ne (by rwa [← hx])] at this
      exact this

open Classical in
/-- The generic adaptive bound: if every answer is related by `R` to at most `e / d` of `Y`, the oracles at which two distinct queries among the first `Q` have related answers are, times `2 d`, at most `e · Q · (Q - 1)` times all. -/
theorem event_card [Fintype X] [Fintype Y] [Nonempty Y] (R : Y → Y → Prop) (hR : ∀ y z, R y z → R z y) {d e : ℕ}
    (hde : ∀ z, (univ.filter fun y => R y z).card * d ≤ e * Fintype.card Y) (σ : List Y → X) (Q : ℕ) :
    (univ.filter fun h : X → Y => Event R σ h Q).card * d * 2 ≤ e * (Q * (Q - 1)) * Fintype.card (X → Y) := by
  set N := Fintype.card (X → Y)
  set S : List Y → Finset Y := fun as => as.toFinset.biUnion fun z => univ.filter fun y => R y z
  set G : ℕ → Finset (X → Y) := fun m =>
    univ.filter fun h : X → Y => Fresh σ h m ∧ h (query σ h m) ∈ S (answers σ h m)
  have hS : ∀ as : List Y, (S as).card * d ≤ as.length * e * Fintype.card Y := by
    intro as
    calc (S as).card * d ≤ (∑ z ∈ as.toFinset, (univ.filter fun y => R y z).card) * d :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ z ∈ as.toFinset, (univ.filter fun y => R y z).card * d := sum_mul _ _ _
      _ ≤ ∑ z ∈ as.toFinset, e * Fintype.card Y := sum_le_sum fun z _ => hde z
      _ = as.toFinset.card * (e * Fintype.card Y) := by rw [sum_const, smul_eq_mul]
      _ ≤ as.length * (e * Fintype.card Y) := Nat.mul_le_mul_right _ (List.toFinset_card_le as)
      _ = _ := by ring
  have hG : ∀ m, (G m).card * d ≤ m * e * N := by
    intro m
    have hY : 0 < Fintype.card Y := Fintype.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hY
    calc (G m).card * d * Fintype.card Y = (G m).card * Fintype.card Y * d := by ring
      _ ≤ (∑ g : X → Y, (S (answers σ g m)).card) * d := Nat.mul_le_mul_right _ (fresh_card σ m S)
      _ = ∑ g : X → Y, (S (answers σ g m)).card * d := sum_mul _ _ _
      _ ≤ ∑ _g : X → Y, m * e * Fintype.card Y := sum_le_sum fun g _ => by
          simpa [answers_length] using hS (answers σ g m)
      _ = m * e * N * Fintype.card Y := by rw [sum_const, card_univ, smul_eq_mul]; ring
  have hcov : (univ.filter fun h : X → Y => Event R σ h Q) ⊆ (range Q).biUnion G := by
    intro h hh
    simp only [mem_filter, mem_univ, true_and] at hh
    obtain ⟨m, hm, hf, z, hz, hr⟩ := event_fresh hR hh
    simp only [mem_biUnion, mem_range, G, S, mem_filter, mem_univ, true_and, List.mem_toFinset]
    exact ⟨m, hm, hf, z, hz, hr⟩
  calc (univ.filter fun h : X → Y => Event R σ h Q).card * d * 2
      ≤ (∑ m ∈ range Q, (G m).card) * d * 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ((card_le_card hcov).trans card_biUnion_le))
    _ = (∑ m ∈ range Q, (G m).card * d) * 2 := by rw [sum_mul]
    _ ≤ (∑ m ∈ range Q, m * e * N) * 2 := Nat.mul_le_mul_right _ (sum_le_sum fun m _ => hG m)
    _ = (∑ m ∈ range Q, m) * 2 * (e * N) := by rw [← sum_mul, ← sum_mul]; ring
    _ = e * (Q * (Q - 1)) * N := by rw [sum_range_id_mul_two]; ring

/-- A fraction bound from a count bound. -/
theorem frac_le {a b d M : ℕ} (hd : 0 < d) (h : a * d ≤ b * M) : (a : ℚ≥0) / M ≤ (b : ℚ≥0) / d := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · simp [hM]
  · rw [div_le_div_iff₀ (by exact_mod_cast hM) (by exact_mod_cast hd)]
    exact_mod_cast h

/-! The adaptive birthday bound. -/

/-- A collision: two distinct queries among the first `Q` with equal answers. -/
def Coll (σ : List Y → X) (h : X → Y) (Q : ℕ) : Prop := Event (· = ·) σ h Q

open Classical in
theorem birthday_card [Fintype X] [Fintype Y] [Nonempty Y] (σ : List Y → X) (Q : ℕ) :
    (univ.filter fun h : X → Y => Coll σ h Q).card * Fintype.card Y * 2 ≤
      Q * (Q - 1) * Fintype.card (X → Y) := by
  have := event_card (· = ·) (fun _ _ h => h.symm) (d := Fintype.card Y) (e := 1) (fun z => by
    rw [filter_eq' univ z]; simp) σ Q
  rw [one_mul] at this
  exact this

open Classical in
/-- The adaptive birthday bound: a uniform oracle `h : X → Y` gives a prover of `Q` adaptive queries two distinct queries with equal answers with probability at most `Q · (Q - 1) / (2 |Y|)`. -/
theorem birthday_frac [Fintype X] [Fintype Y] [Nonempty Y] (σ : List Y → X) (Q : ℕ) :
    ((univ.filter fun h : X → Y => Coll σ h Q).card : ℚ≥0) / Fintype.card (X → Y) ≤
      ((Q * (Q - 1) : ℕ) : ℚ≥0) / ((2 * Fintype.card Y : ℕ) : ℚ≥0) :=
  frac_le (by have := Fintype.card_pos (α := Y); omega) (by
    have := birthday_card σ Q; rw [mul_comm 2]; linarith)

/-- Non-vacuity: two queries to an oracle from `Bool` to `Unit` always collide, and the bound is `2 · 1 / 2 = 1`. -/
example : ∀ h : Bool → Unit, Coll (fun as : List Unit => decide (as.length = 1)) h 2 :=
  fun h => ⟨0, by omega, 1, by omega, by simp [query, answers], rfl⟩

/-- Mutation test: the identity oracle on `Bool` gives the two distinct queries distinct answers, so no collision. -/
example : ¬ Coll (fun as : List Bool => decide (as.length = 1)) id 2 := by
  rintro ⟨i, hi, i', hi', hne, he⟩
  exact hne he

/-- Non-vacuity of the bound: one query never collides. -/
example (σ : List Bool → Bool) (h : Bool → Bool) : ¬ Coll σ h 1 := by
  rintro ⟨i, hi, i', hi', hne, _⟩
  exact hne (by rw [show i = 0 by omega, show i' = 0 by omega])

/-! Two answers agreeing on two consecutive words. -/

variable {V : Type}

/-- Two answers of four words agree on two consecutive words. -/
def Near (y z : Fin 4 → V) : Prop := ∃ k : Fin 3, y k.castSucc = z k.castSucc ∧ y k.succ = z k.succ

theorem near_symm {y z : Fin 4 → V} (h : Near y z) : Near z y := by
  obtain ⟨k, h1, h2⟩ := h
  exact ⟨k, h1.symm, h2.symm⟩

/-- A near hit: two distinct queries among the first `Q` whose answers agree on two consecutive words. -/
def NearHit (σ : List (Fin 4 → V) → X) (h : X → Fin 4 → V) (Q : ℕ) : Prop := Event Near σ h Q

open Classical in
/-- Fixing a word: the answers with word `k` equal to `c` and property `P`, stable under changing word `k`, times `|V|`, are at most those with `P`. -/
theorem card_fix_le [Fintype V] (k : Fin 4) (c : V) (P : (Fin 4 → V) → Prop)
    (hP : ∀ y v, P y → P (Function.update y k v)) :
    (univ.filter fun y : Fin 4 → V => y k = c ∧ P y).card * Fintype.card V ≤ (univ.filter P).card := by
  rw [← card_univ (α := V), ← card_product]
  refine card_le_card_of_injOn (fun p => Function.update p.1 k p.2) ?_ ?_
  · intro p hp
    simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, mem_univ, true_and] at hp
    simp only [coe_filter, mem_univ, true_and]
    exact hP _ _ hp.1.2
  · rintro ⟨y1, v1⟩ hp1 ⟨y2, v2⟩ hp2 he
    simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, mem_univ, true_and] at hp1 hp2 he
    have hv : v1 = v2 := by simpa using congrFun he k
    refine Prod.ext ?_ hv
    funext a
    by_cases ha : a = k
    · subst ha
      exact hp1.1.1.trans hp2.1.1.symm
    · simpa [Function.update_of_ne ha] using congrFun he a

open Classical in
/-- Every answer is near at most `3 / |V|^2` of the answers: three pairs of consecutive words, each fixing two. -/
theorem near_card [Fintype V] (z : Fin 4 → V) :
    (univ.filter fun y => Near y z).card * (Fintype.card V * Fintype.card V) ≤ 3 * Fintype.card (Fin 4 → V) := by
  have hpair : ∀ k : Fin 3, (univ.filter fun y : Fin 4 → V => y k.castSucc = z k.castSucc ∧
      y k.succ = z k.succ).card * (Fintype.card V * Fintype.card V) ≤ Fintype.card (Fin 4 → V) := by
    intro k
    have hne : k.castSucc ≠ k.succ := ne_of_lt Fin.castSucc_lt_succ
    have h1 := card_fix_le k.castSucc (z k.castSucc) (fun y => y k.succ = z k.succ)
      (fun y v hy => by rw [Function.update_of_ne (Ne.symm hne)]; exact hy)
    have h2 := card_fix_le (V := V) k.succ (z k.succ) (fun _ => True) (fun _ _ _ => trivial)
    simp only [and_true] at h2
    calc _ = (univ.filter fun y : Fin 4 → V => y k.castSucc = z k.castSucc ∧
          y k.succ = z k.succ).card * Fintype.card V * Fintype.card V := by ring
      _ ≤ (univ.filter fun y : Fin 4 → V => y k.succ = z k.succ).card * Fintype.card V :=
          Nat.mul_le_mul_right _ h1
      _ ≤ _ := h2.trans (card_le_univ _)
  have hsub : (univ.filter fun y => Near y z) ⊆ univ.biUnion fun k : Fin 3 =>
      univ.filter fun y : Fin 4 → V => y k.castSucc = z k.castSucc ∧ y k.succ = z k.succ := by
    intro y hy
    rw [mem_filter] at hy
    obtain ⟨-, k, hk⟩ := hy
    exact mem_biUnion.mpr ⟨k, mem_univ _, mem_filter.mpr ⟨mem_univ _, hk⟩⟩
  calc (univ.filter fun y => Near y z).card * (Fintype.card V * Fintype.card V)
      ≤ (∑ k : Fin 3, (univ.filter fun y : Fin 4 → V => y k.castSucc = z k.castSucc ∧
          y k.succ = z k.succ).card) * (Fintype.card V * Fintype.card V) :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ k : Fin 3, (univ.filter fun y : Fin 4 → V => y k.castSucc = z k.castSucc ∧
          y k.succ = z k.succ).card * (Fintype.card V * Fintype.card V) := sum_mul _ _ _
    _ ≤ ∑ _k : Fin 3, Fintype.card (Fin 4 → V) := sum_le_sum fun k _ => hpair k
    _ = _ := by simp

open Classical in
theorem near_count [Fintype X] [Fintype V] [Nonempty V] (σ : List (Fin 4 → V) → X) (Q : ℕ) :
    (univ.filter fun h : X → Fin 4 → V => NearHit σ h Q).card * (Fintype.card V * Fintype.card V) * 2 ≤
      3 * (Q * (Q - 1)) * Fintype.card (X → Fin 4 → V) :=
  event_card Near (fun _ _ h => near_symm h) near_card σ Q

open Classical in
/-- The near-hit bound: a uniform oracle `h : X → (Fin 4 → V)` gives a prover of `Q` adaptive queries two distinct queries whose answers agree on two consecutive words with probability at most `3 · Q · (Q - 1) / (2 |V|^2)`. -/
theorem near_frac [Fintype X] [Fintype V] [Nonempty V] (σ : List (Fin 4 → V) → X) (Q : ℕ) :
    ((univ.filter fun h : X → Fin 4 → V => NearHit σ h Q).card : ℚ≥0) / Fintype.card (X → Fin 4 → V) ≤
      ((3 * (Q * (Q - 1)) : ℕ) : ℚ≥0) / ((2 * (Fintype.card V * Fintype.card V) : ℕ) : ℚ≥0) :=
  frac_le (by have := Fintype.card_pos (α := V); positivity) (by
    have := near_count σ Q; rw [mul_comm 2]; linarith)

/-- Mutation test: answers agreeing on words 0 and 2 only are not near; agreeing on words 0 and 1 they are. -/
example : ¬ Near (![0, 1, 0, 1] : Fin 4 → Fin 2) ![0, 0, 0, 0] ∧ Near (![0, 0, 1, 1] : Fin 4 → Fin 2) ![0, 0, 0, 0] :=
  ⟨fun ⟨k, h1, h2⟩ => by fin_cases k <;> revert h1 h2 <;> decide, ⟨0, by decide, by decide⟩⟩

/-! Off the events, on the queries. -/

/-- The prover's first `Q` queries. -/
def queries (σ : List Y → X) (h : X → Y) (Q : ℕ) : Set X := {x | ∃ i < Q, query σ h i = x}

/-- No two distinct inputs of `Qs` have near answers. -/
def NearFree (H : X → Fin 4 → V) (Qs : Set X) : Prop := ∀ x ∈ Qs, ∀ x' ∈ Qs, x ≠ x' → ¬ Near (H x) (H x')

theorem injOn_of_not_coll {σ : List Y → X} {h : X → Y} {Q : ℕ} (hc : ¬ Coll σ h Q) :
    Set.InjOn h (queries σ h Q) := by
  rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩ he
  by_contra hne
  exact hc ⟨i, hi, i', hi', hne, he⟩

theorem nearFree_of_not_hit {σ : List (Fin 4 → V) → X} {h : X → Fin 4 → V} {Q : ℕ} (hc : ¬ NearHit σ h Q) :
    NearFree h (queries σ h Q) := by
  rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩ hne hn
  exact hc ⟨i, hi, i', hi', hne, hn⟩

/-- Non-vacuity: a prover of one query never collides nor hits, so the oracle is injective and near-free on it. -/
example (σ : List (Fin 4 → V) → X) (h : X → Fin 4 → V) :
    Set.InjOn h (queries σ h 1) ∧ NearFree h (queries σ h 1) := by
  refine ⟨injOn_of_not_coll ?_, nearFree_of_not_hit ?_⟩ <;>
  · rintro ⟨i, hi, i', hi', hne, _⟩
    exact hne (by rw [show i = 0 by omega, show i' = 0 by omega])

end LeanVMCircuits.Rec.Collision

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Collision

/-- A hash row's input words at an assignment: counter, finalization, chaining value, message (`hashIn`'s nodes). -/
def rowIn (val : Val) (row : List ℕ) : Fin 14 → K := fun c => nu val (colNode row (hashSrc c))

/-- A hash row's output words at an assignment (`hashOut`'s nodes). -/
def rowOut (val : Val) (row : List ℕ) : Fin 4 → K := fun k => nu val (colNode row (hashSrc (14 + k)))

/-- An input's chaining value words. -/
def chainOf (x : Fin 14 → K) : Fin 4 → K := fun k => x ⟨2 + k, by omega⟩

theorem hashIn_map (val : Val) (row : List ℕ) : (hashIn row).map (nu val) = List.ofFn (rowIn val row) := by
  apply List.ext_getElem (by simp [hashIn])
  intro n h1 h2
  simp only [hashIn, rowIn, List.getElem_map, List.getElem_range, List.getElem_ofFn]

theorem hashOut_map (val : Val) (row : List ℕ) : (hashOut row).map (nu val) = List.ofFn (rowOut val row) := by
  apply List.ext_getElem (by simp [hashOut])
  intro n h1 h2
  simp only [hashOut, rowOut, List.getElem_map, List.getElem_range, List.getElem_ofFn]

theorem hashSrc_chain {k : ℕ} (hk : k < 4) : hashSrc (2 + k) = (0, k) := by
  simp only [hashSrc, if_neg (show ¬ 2 + k < 2 by omega), if_pos (show 2 + k < 6 by omega), Nat.add_sub_cancel_left]

/-- Two hash rows of one chaining value wire have the same chaining value words. -/
theorem chainOf_rowIn {val : Val} {ra rb : List ℕ} (h0 : ra.getD 0 0 = rb.getD 0 0) :
    chainOf (rowIn val ra) = chainOf (rowIn val rb) := by
  funext k
  show nu val (colNode ra (hashSrc (2 + k.val))) = nu val (colNode rb (hashSrc (2 + k.val)))
  rw [hashSrc_chain k.isLt]
  simp only [colNode, h0]

/-- The ideal compression model's consistency at an assignment: every hash row `drop` does not name has its inputs among the queries `Qs` and its outputs the oracle `H` at its inputs. -/
def OracleRows (H : (Fin 14 → K) → Fin 4 → K) (Qs : Set (Fin 14 → K)) (s : State) (drop : List ℕ → Bool) (val : Val) :
    Prop :=
  ∀ row ∈ s.hash, drop row = false → rowIn val row ∈ Qs ∧ rowOut val row = H (rowIn val row)

/-- `HashCRP` from the ideal model: two assignments consistent with an oracle injective on the queries. -/
theorem hashCRP_of_oracle {H : (Fin 14 → K) → Fin 4 → K} {Qs : Set (Fin 14 → K)} {s : State} {drop : List ℕ → Bool}
    {val val' : Val} (hinj : Set.InjOn H Qs) (hv : OracleRows H Qs s drop val) (hv' : OracleRows H Qs s drop val') :
    HashCRP s drop val val' := by
  intro row hr row' hr' hd hd' ho
  rw [hashOut_map, hashOut_map, List.ofFn_inj] at ho
  obtain ⟨q, e⟩ := hv row hr hd
  obtain ⟨q', e'⟩ := hv' row' hr' hd'
  rw [hashIn_map, hashIn_map, List.ofFn_inj]
  exact hinj q q' (e.symm.trans (ho.trans e'))

/-- `WindowCRP` from the ideal model: two assignments consistent with an oracle near-free on the queries. Of a window's four words, `4 - j` are one row's outputs and `j` the other's; at least two consecutive ones are one row's, so two windows of distinct chaining values agreeing make two distinct queries near. -/
theorem windowCRP_of_oracle {H : (Fin 14 → K) → Fin 4 → K} {Qs : Set (Fin 14 → K)} {s : State}
    {drop : List ℕ → Bool} {val val' : Val} (hnear : NearFree H Qs) (hv : OracleRows H Qs s drop val)
    (hv' : OracleRows H Qs s drop val') : WindowCRP s drop val val' := by
  intro ra ha rb hb hda hdb h0 j hj1 hj4 hw
  obtain ⟨qa, ea⟩ := hv ra ha hda
  obtain ⟨qa', ea'⟩ := hv' ra ha hda
  obtain ⟨qb, eb⟩ := hv rb hb hdb
  obtain ⟨qb', eb'⟩ := hv' rb hb hdb
  -- the window's words: `ra`'s from word `j` on, `rb`'s before it
  have wa : ∀ k : Fin 4, j ≤ k.val → H (rowIn val ra) k = H (rowIn val' ra) k := by
    intro k hk
    rw [← ea, ← ea']
    refine hw _ (List.mem_append_left _ (List.mem_map.mpr ⟨k.val - j, List.mem_range.mpr (by omega), ?_⟩))
    show colNode ra (hashSrc (14 + j + (k.val - j))) = colNode ra (hashSrc (14 + k.val))
    rw [show 14 + j + (k.val - j) = 14 + k.val by omega]
  have wb : ∀ k : Fin 4, k.val < j → H (rowIn val rb) k = H (rowIn val' rb) k := by
    intro k hk
    rw [← eb, ← eb']
    exact hw _ (List.mem_append_right _ (List.mem_map.mpr ⟨k.val, List.mem_range.mpr hk, rfl⟩))
  have hc : chainOf (rowIn val ra) = chainOf (rowIn val' ra) := by
    by_contra hc
    have hne : rowIn val ra ≠ rowIn val' ra := fun e => hc (by rw [e])
    have hne' : rowIn val rb ≠ rowIn val' rb := fun e => hc (by rw [chainOf_rowIn h0, e, ← chainOf_rowIn h0])
    by_cases hj : j ≤ 2
    · exact hnear _ qa _ qa' hne ⟨⟨j, by omega⟩, wa _ (by simp), wa _ (by simp)⟩
    · exact hnear _ qb _ qb' hne' ⟨0, wb _ (by simp; omega), wb _ (by simp; omega)⟩
  intro n hn
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
  exact congrFun hc ⟨k, List.mem_range.mp hk⟩

/-- Non-vacuity of `OracleRows`: an assignment whose hash rows not dropped give equal inputs equal outputs (as the compression's rows do) is consistent with some oracle, all inputs being queries. -/
theorem oracleRows_exists (s : State) (drop : List ℕ → Bool) (val : Val)
    (hf : ∀ row ∈ s.hash, ∀ row' ∈ s.hash, drop row = false → drop row' = false → rowIn val row = rowIn val row' →
      rowOut val row = rowOut val row') :
    ∃ H, OracleRows H Set.univ s drop val := by
  classical
  refine ⟨fun x => if h : ∃ row ∈ s.hash, drop row = false ∧ rowIn val row = x then rowOut val h.choose else 0, ?_⟩
  intro row hr hd
  have hx : ∃ row' ∈ s.hash, drop row' = false ∧ rowIn val row' = rowIn val row := ⟨row, hr, hd, rfl⟩
  refine ⟨Set.mem_univ _, ?_⟩
  simp only [dif_pos hx]
  obtain ⟨hm, hdm, he⟩ := hx.choose_spec
  exact (hf _ hm _ hr hdm hd he).symm

/-- `RomAnswers` from the ideal compression model, in place of its premises `cr` and `win`: every answer consistent with one oracle `H` on queries `Qs`, at which `H` is injective and near-free. -/
theorem RomAnswers.of_oracle {c : Cert} {s : State} {T : ℕ} {ι : Type} {st : ι → ℕ → Fin 4 → K} {val : ι → Val}
    (holds : ∀ r, HoldsP (st r) s c.test (dropOf s (c.transcripts.getD T default)) (val r))
    (facts : ∀ r, Facts c.calls c.relax c.outs (st r) (val r))
    (unions : ∀ r r', UnionsValid c.claims (val r) (val r'))
    (H : (Fin 14 → K) → Fin 4 → K) (Qs : Set (Fin 14 → K))
    (hrows : ∀ r, OracleRows H Qs s (dropOf s (c.transcripts.getD T default)) (val r))
    (hinj : Set.InjOn H Qs) (hnear : NearFree H Qs) : RomAnswers c s T st val :=
  ⟨holds, facts, fun r r' => hashCRP_of_oracle hinj (hrows r) (hrows r'),
    fun r r' => windowCRP_of_oracle hnear (hrows r) (hrows r'), unions⟩

/-- `RomAnswers` from a run of the ideal model: every answer consistent with the oracle `h` on the first `Q` queries of a prover `σ`, off the collision and near-hit events. -/
theorem RomAnswers.of_run {c : Cert} {s : State} {T : ℕ} {ι : Type} {st : ι → ℕ → Fin 4 → K} {val : ι → Val}
    (holds : ∀ r, HoldsP (st r) s c.test (dropOf s (c.transcripts.getD T default)) (val r))
    (facts : ∀ r, Facts c.calls c.relax c.outs (st r) (val r))
    (unions : ∀ r r', UnionsValid c.claims (val r) (val r'))
    (σ : List (Fin 4 → K) → Fin 14 → K) (h : (Fin 14 → K) → Fin 4 → K) (Q : ℕ)
    (hrows : ∀ r, OracleRows h (queries σ h Q) s (dropOf s (c.transcripts.getD T default)) (val r))
    (hc : ¬ Coll σ h Q) (hn : ¬ NearHit σ h Q) : RomAnswers c s T st val :=
  RomAnswers.of_oracle holds facts unions h _ hrows (injOn_of_not_coll hc) (nearFree_of_not_hit hn)

end LeanVMCircuits.Rec.Bind

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model Finset Collision

section Oracle

variable {ι Ω₀ X V : Type}

open Classical in
/-- The collision event over outcomes pairing other coins `ω.1` with the compression oracle `ω.2`: among the first `Q` compression queries of the prover `σ ω.1`, a collision or a near hit. -/
noncomputable def crEvent [Fintype Ω₀] [Fintype X] [Fintype V] (σ : Ω₀ → List (Fin 4 → V) → X) (Q : ℕ) :
    Finset (Ω₀ × (X → Fin 4 → V)) :=
  univ.filter fun ω => Coll (σ ω.1) ω.2 Q ∨ NearHit (σ ω.1) ω.2 Q

/-- The ideal compression model's `ε_CR` for `Q` compression queries with words in `V`: the birthday bound `Q · (Q - 1) / (2 |V|^4)` and the near-hit bound `3 · Q · (Q - 1) / (2 |V|^2)`. -/
noncomputable def epsCR (V : Type) [Fintype V] (Q : ℕ) : ℚ≥0 :=
  ((Q * (Q - 1) : ℕ) : ℚ≥0) / ((2 * Fintype.card V ^ 4 : ℕ) : ℚ≥0) +
    ((3 * (Q * (Q - 1)) : ℕ) : ℚ≥0) / ((2 * (Fintype.card V * Fintype.card V) : ℕ) : ℚ≥0)

open Classical in
theorem card_filter_prod {A B : Type} [Fintype A] [Fintype B] (P : A → B → Prop) :
    (univ.filter fun ω : A × B => P ω.1 ω.2).card = ∑ a, (univ.filter (P a)).card := by
  rw [card_filter, ← univ_product_univ, sum_product]
  simp only [card_filter]

open Classical in
/-- `crEvent`'s fraction of the outcomes is at most `epsCR`. -/
theorem crEvent_frac [Fintype Ω₀] [Fintype X] [Fintype V] [Nonempty V] (σ : Ω₀ → List (Fin 4 → V) → X) (Q : ℕ) :
    ((crEvent σ Q).card : ℚ≥0) / Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤ epsCR V Q := by
  set M := Fintype.card (Ω₀ × (X → Fin 4 → V))
  have hM : M = Fintype.card Ω₀ * Fintype.card (X → Fin 4 → V) := Fintype.card_prod _ _
  have hY : Fintype.card (Fin 4 → V) = Fintype.card V ^ 4 := by simp
  have hV := Fintype.card_pos (α := V)
  set cA := (univ.filter fun ω : Ω₀ × (X → Fin 4 → V) => Coll (σ ω.1) ω.2 Q).card
  set cB := (univ.filter fun ω : Ω₀ × (X → Fin 4 → V) => NearHit (σ ω.1) ω.2 Q).card
  have hA : (cA : ℚ≥0) / M ≤ ((Q * (Q - 1) : ℕ) : ℚ≥0) / ((2 * Fintype.card V ^ 4 : ℕ) : ℚ≥0) := by
    refine frac_le (by positivity) ?_
    have hcA : cA = ∑ a, (univ.filter fun h => Coll (σ a) h Q).card := card_filter_prod fun a h => Coll (σ a) h Q
    calc cA * (2 * Fintype.card V ^ 4) = ∑ a, (univ.filter fun h => Coll (σ a) h Q).card *
          Fintype.card (Fin 4 → V) * 2 := by rw [hcA, sum_mul, hY]; exact sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ _a : Ω₀, Q * (Q - 1) * Fintype.card (X → Fin 4 → V) := sum_le_sum fun a _ => birthday_card (σ a) Q
      _ = Q * (Q - 1) * M := by rw [sum_const, card_univ, smul_eq_mul, hM]; ring
  have hB : (cB : ℚ≥0) / M ≤ ((3 * (Q * (Q - 1)) : ℕ) : ℚ≥0) /
      ((2 * (Fintype.card V * Fintype.card V) : ℕ) : ℚ≥0) := by
    refine frac_le (by positivity) ?_
    have hcB : cB = ∑ a, (univ.filter fun h => NearHit (σ a) h Q).card :=
      card_filter_prod fun a h => NearHit (σ a) h Q
    calc cB * (2 * (Fintype.card V * Fintype.card V)) = ∑ a, (univ.filter fun h => NearHit (σ a) h Q).card *
          (Fintype.card V * Fintype.card V) * 2 := by rw [hcB, sum_mul]; exact sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ _a : Ω₀, 3 * (Q * (Q - 1)) * Fintype.card (X → Fin 4 → V) := sum_le_sum fun a _ => near_count (σ a) Q
      _ = 3 * (Q * (Q - 1)) * M := by rw [sum_const, card_univ, smul_eq_mul, hM]; ring
  have hcard : ((crEvent σ Q).card : ℚ≥0) ≤ cA + cB := by
    have : crEvent σ Q = (univ.filter fun ω : Ω₀ × (X → Fin 4 → V) => Coll (σ ω.1) ω.2 Q) ∪
        (univ.filter fun ω : Ω₀ × (X → Fin 4 → V) => NearHit (σ ω.1) ω.2 Q) := by
      rw [crEvent, filter_or]
    rw [this]
    exact_mod_cast card_union_le _ _
  calc ((crEvent σ Q).card : ℚ≥0) / M ≤ ((cA : ℚ≥0) + cB) / M := by gcongr
    _ = (cA : ℚ≥0) / M + (cB : ℚ≥0) / M := add_div _ _ _
    _ ≤ epsCR V Q := add_le_add hA hB

/-- Off `crEvent`, the oracle is injective and near-free on the prover's queries: what `Bind.RomAnswers.of_oracle` and `Bind.hashCRP_of_oracle` ask. -/
theorem not_mem_crEvent [Fintype Ω₀] [Fintype X] [Fintype V] {σ : Ω₀ → List (Fin 4 → V) → X} {Q : ℕ}
    {ω : Ω₀ × (X → Fin 4 → V)} (h : ω ∉ crEvent σ Q) :
    Set.InjOn ω.2 (queries (σ ω.1) ω.2 Q) ∧ NearFree ω.2 (queries (σ ω.1) ω.2 Q) := by
  classical
  simp only [crEvent, mem_filter, mem_univ, true_and, not_or] at h
  exact ⟨injOn_of_not_coll h.1, nearFree_of_not_hit h.2⟩

open Classical in
/-- `crBad` as the collision event of each child's compression queries: its fraction in `tree_sound_parts`' sum is at most `epsCR` of the child's number of compression queries. -/
theorem crBad_frac [Fintype Ω₀] [Fintype X] [Fintype V] [Nonempty V] (P : RecParts ι (Ω₀ × (X → Fin 4 → V)))
    (σ : ι → Ω₀ → List (Fin 4 → V) → X) (Q : ι → ℕ) (hcr : ∀ v, P.crBad v = crEvent (σ v) (Q v)) (v : ι) :
    ((P.crBad v).card : ℚ≥0) / Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤ epsCR V (Q v) := by
  rw [hcr v]
  exact crEvent_frac (σ v) (Q v)

open Classical in
/-- Non-vacuity: the least parts with the collision events as `crBad` satisfy `RecParts.Ok` and `crBad_frac`'s premise. -/
example [Fintype Ω₀] [Fintype X] [Fintype V] (J : ι → ℕ) (inOk outOk : ι → ℕ → Ω₀ × (X → Fin 4 → V) → Prop)
    (held : ι → Ω₀ × (X → Fin 4 → V) → Prop) (σ : ι → Ω₀ → List (Fin 4 → V) → X) (Q : ι → ℕ) :
    (RecParts.least J inOk outOk held fun v => crEvent (σ v) (Q v)).Ok held ∧
      ∀ v, (RecParts.least J inOk outOk held fun v => crEvent (σ v) (Q v)).crBad v = crEvent (σ v) (Q v) :=
  ⟨RecParts.least_ok _ _ _ _ _, fun _ => rfl⟩

end Oracle

section Pcs

variable {ι Ω : Type}

/-- The PCS interface: child `v`'s `pcsBad` is at most `epsPCS v` of the outcomes. #551 proves such a bound for WHIR in its separate Lean project (`verification/whir`, commit `8198d0b2`): theorem `Whir.SpongefishCurrentKnowledgeFinal.current_knowledge` in `verification/whir/Whir/SpongefishCurrentKnowledgeFinal.lean` bounds, in the ideal compression model, the probability that some received record is natively accepted while the public straight-line extractor fails by `∑ k : Fin 4, finalBound Q_k`, with `finalBound Q = Q · ((17/32)^56 + 2^-78) + min(1, (2 Q^2 - Q) / 2^256) + (Q^3 + 3 Q^2 - 2 Q) / 2^256` and `Q_k` the aggregate budget of binding message shape `k`; `current_knowledge_level` gives `B / 2^49` for budgets at most `B ≤ 2^64`. Its event and outcome space are its own; matching them to `pcsBad` is this interface's premise. -/
structure PcsBound [Fintype Ω] (P : RecParts ι Ω) (epsPCS : ι → ℚ≥0) : Prop where
  le : ∀ v, ((P.pcsBad v).card : ℚ≥0) / Fintype.card Ω ≤ epsPCS v

/-- Non-vacuity: every part's PCS events are at most all the outcomes. -/
theorem PcsBound.one [Fintype Ω] (P : RecParts ι Ω) : PcsBound P fun _ => 1 :=
  ⟨fun v => div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (by positivity)⟩

/-- Non-vacuity at the least parts. -/
example [Fintype Ω] (J : ι → ℕ) (inOk outOk : ι → ℕ → Ω → Prop) (held : ι → Ω → Prop) (crBad : ι → Finset Ω) :
    PcsBound (RecParts.least J inOk outOk held crBad) fun _ => 1 :=
  PcsBound.one _

open Classical in
/-- `tree_sound_parts` with each child's `pcsBad` fraction replaced by its PCS bound `epsPCS v` (`PcsBound`, #551) and its `crBad` fraction by a bound `epsCR v` (for the collision events, `crBad_frac`). -/
theorem tree_sound_eps [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι Ω)
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (hair : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
      Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
      (∀ j < P.J v, P.inOk v j ω) → ω ∉ P.crBad v →
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω))
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (epsPCS epsCR : ι → ℚ≥0) (hpcs : PcsBound P epsPCS)
    (hcr : ∀ v ∈ T.nodes, ((P.crBad v).card : ℚ≥0) / Fintype.card Ω ≤ epsCR v) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card Ω ≤
      ∑ v ∈ T.nodes, (((bad v).card + ∑ j ∈ range (P.J v), (P.testBad v j).card : ℚ≥0) / Fintype.card Ω +
        epsPCS v + epsCR v) := by
  refine (tree_sound_parts T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP hair tD tM bad hstep
    hroot).trans (sum_le_sum fun v hv => ?_)
  rw [add_div, add_div]
  exact add_le_add (add_le_add le_rfl (hpcs.le v)) (hcr v hv)

end Pcs

end LeanVMCircuits.Rec.Edges
