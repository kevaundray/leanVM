module

public import LeanVMCircuits.Rec.TreeBound

@[expose] public section

/-!
The collision term per execution, and the tree's bound at deployed sizes.

The round theorems (`Bind.sumcheck_run_sound_at` and the like) ask collision resistance only between two answers of a run's family sharing the prefix of the transcript before a check's challenge, and only on the rows that prefix binds (`Bind.PairCR`, `Bind.Run.cr`); they bound a check's event off the run's collision event `C`, and `Bind.run_frac_off` charges `C` once. Here `C` is one execution's.

The prover model (`Bind.Run.cr_of_prefix`): at oracle `ρ`, the compression queries the prover makes before the squeeze after time `k`, `pre ρ k ownL`, are the same for every oracle agreeing with `ρ` on the answers drawn by `k` and on those drawn at `k + 1` but the words `ownL` (a deterministic prover sees nothing else by then), and every row those seeds bind is consistent with the compression oracle `H` with its input among them (the prover commits by computing). Off `C ρ`, `H` is injective and window-free on them, and the run's `cr` follows: the two answers' rows are the same prefix's queries. `Bind.Run.cr_of_queries` takes `C ρ` the event that the first `Q` compression queries of the execution at `ρ` collide or hit a window (`Collision.Coll`, `Collision.WinHit`), `Q` one execution's count.

`AirLink.tree_sound_exec` is the tree's bound over outcomes pairing the oracle on the transcripts' words with the compression oracle, child `v`'s `crBad` its execution's `Edges.crEvent` of `Q v` queries, bounded by `Edges.epsCR K (Q v)` once per child, and each check's `testBad` by a bound holding at every compression oracle (the round theorems', `n · d / |E|` and the like). `Edges.exec_bound_deployed` evaluates the terms this bound proves at deployed sizes: with `card_E` (`|E| = 2^192`), per child at most `2^40 / |E| + epsCR K Q`, below `2^-1` for `Q ≤ 2^84`, `2^-7` for `Q ≤ 2^82`, `2^-32` for `Q ≤ 2^74` and `2^-64` for `Q ≤ 2^63`; `Edges.epsCR_cap`: at `Q = 2^86` the window term alone is past one.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Finset Collision

theorem WinOn.mono {X V C R : Type} {ch : X → C} {re : X → R} {H : X → Fin 4 → V} {A B : Set X} (hAB : A ⊆ B)
    (h : WinOn ch re H A) : WinOn ch re H B := by
  obtain ⟨a, ha, b, hb, a', ha', b', hb', rest⟩ := h
  exact ⟨a, hAB ha, b, hAB hb, a', hAB ha', b', hAB hb', rest⟩

variable {c : Cert} {s : State} {T : ℕ} {val : (ℕ → K) → Val}

/-- The prover model's collision premise: a run's `cr` from a prover whose compression queries before the squeeze after
time `k`, but the words `ownL` drawn at `k + 1`, are shared by every execution agreeing with it by then (`hshare`),
include the inputs of every row those seeds bind, consistent with the compression oracle `H` (`hrows`), and on which
`H` is injective and window-free off `C` (`hfree`). -/
theorem Run.cr_of_prefix (H : (Fin 14 → K) → Fin 4 → K) (pre : (ℕ → K) → ℕ → List ℕ → Set (Fin 14 → K))
    (C : (ℕ → K) → Prop)
    (hshare : ∀ ρ ρ' k ownL, (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 ≤ k → ρ p.2 = ρ' p.2) →
      (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 = k + 1 → p.2 ∉ ownL → ρ p.2 = ρ' p.2) →
      pre ρ k ownL = pre ρ' k ownL)
    (hrows : ∀ ρ k ownL, OracleRows H (pre ρ k ownL) s (dropOf s (c.transcripts.getD T default))
      (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++ sibSeeds s (c.transcripts.getD T default) k ownL))
      (val ρ))
    (hfree : ∀ ρ k ownL, ¬ C ρ → Set.InjOn H (pre ρ k ownL) ∧ ¬ WinOn chainOf restOf H (pre ρ k ownL)) :
    ∀ ρ ρ' k (ownL : List ℕ), (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 ≤ k → ρ p.2 = ρ' p.2) →
      (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 = k + 1 → p.2 ∉ ownL → ρ p.2 = ρ' p.2) → ¬ C ρ →
      PairCR c s T (seedsBefore s (c.transcripts.getD T default) k ++ sibSeeds s (c.transcripts.getD T default) k ownL)
        (val ρ) (val ρ') := by
  intro ρ ρ' k ownL h1 h2 hC
  obtain ⟨hinj, hwin⟩ := hfree ρ k ownL hC
  have hv' := hrows ρ' k ownL
  rw [← hshare ρ ρ' k ownL h1 h2] at hv'
  exact pairCR_of_oracle H _ hinj hwin (hrows ρ k ownL) hv'

/-- `Run.cr_of_prefix` with the collision event of one execution: the prefix queries among the first `Q` compression
queries of the prover `σ ρ` against `H`, and `C ρ` their collision or window hit. -/
theorem Run.cr_of_queries (H : (Fin 14 → K) → Fin 4 → K) (pre : (ℕ → K) → ℕ → List ℕ → Set (Fin 14 → K))
    (σ : (ℕ → K) → List (Fin 4 → K) → Fin 14 → K) (Q : ℕ)
    (hshare : ∀ ρ ρ' k ownL, (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 ≤ k → ρ p.2 = ρ' p.2) →
      (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 = k + 1 → p.2 ∉ ownL → ρ p.2 = ρ' p.2) →
      pre ρ k ownL = pre ρ' k ownL)
    (hrows : ∀ ρ k ownL, OracleRows H (pre ρ k ownL) s (dropOf s (c.transcripts.getD T default))
      (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++ sibSeeds s (c.transcripts.getD T default) k ownL))
      (val ρ))
    (hsub : ∀ ρ k ownL, pre ρ k ownL ⊆ queries (σ ρ) H Q) :
    ∀ ρ ρ' k (ownL : List ℕ), (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 ≤ k → ρ p.2 = ρ' p.2) →
      (∀ p ∈ chalSeeds s (c.transcripts.getD T default), p.1 = k + 1 → p.2 ∉ ownL → ρ p.2 = ρ' p.2) →
      ¬ (Coll (σ ρ) H Q ∨ WinHit chainOf restOf (σ ρ) H Q) →
      PairCR c s T (seedsBefore s (c.transcripts.getD T default) k ++ sibSeeds s (c.transcripts.getD T default) k ownL)
        (val ρ) (val ρ') :=
  Run.cr_of_prefix H pre _ hshare hrows fun ρ k ownL hC => by
    rw [not_or] at hC
    exact ⟨(injOn_of_not_coll hC.1).mono (hsub ρ k ownL), fun hw => hC.2 (WinOn.mono (hsub ρ k ownL) hw)⟩

/-- Non-vacuity of the prover model's premises: no prefix queries and no live rows meet every premise, with no
collision event. -/
example (H : (Fin 14 → K) → Fin 4 → K)
    (hnone : ∀ k ownL row, ¬ RowLive (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++
      sibSeeds s (c.transcripts.getD T default) k ownL)) row) :
    ∀ ρ k ownL, OracleRows H ((fun _ _ _ => ∅) ρ k ownL) s (dropOf s (c.transcripts.getD T default))
      (c.liveOn T (seedsBefore s (c.transcripts.getD T default) k ++ sibSeeds s (c.transcripts.getD T default) k ownL))
      (val ρ) :=
  fun _ k ownL row _ _ hl => absurd hl (hnone k ownL row)

end LeanVMCircuits.Rec.Bind

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model Finset Edges Bind Collision

/-- A fraction over pairs at most `b` when it is at every second coordinate. -/
theorem frac_prod_le {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (S : Finset (A × B))
    (b : ℚ≥0) (h : ∀ y : B, (#{x : A | (x, y) ∈ S} : ℚ≥0) / Fintype.card A ≤ b) :
    (#S : ℚ≥0) / Fintype.card (A × B) ≤ b := by
  rcases isEmpty_or_nonempty A with hA | hA
  · simp [Fintype.card_prod, Fintype.card_eq_zero]
  have hcA : (0 : ℚ≥0) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hS : (#S : ℚ≥0) = ∑ y : B, (#{x : A | (x, y) ∈ S} : ℚ≥0) := by
    have : #S = ∑ y : B, #{x : A | (x, y) ∈ S} := by
      rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := univ) (fun _ _ => mem_univ _)]
      refine sum_congr rfl fun y _ => ?_
      refine card_bij (fun p _ => p.1) (fun p hp => ?_) (fun p hp q hq he => ?_) (fun x hx => ⟨(x, y), ?_, rfl⟩)
      · simp only [mem_filter, mem_univ, true_and] at hp ⊢
        rw [← hp.2]
        exact hp.1
      · simp only [mem_filter] at hp hq
        exact Prod.ext he (hp.2.trans hq.2.symm)
      · simp only [mem_filter, mem_univ, true_and] at hx ⊢
        simpa using hx
    exact_mod_cast this
  rw [hS, Fintype.card_prod, Nat.cast_mul, sum_div]
  calc ∑ y : B, (#{x : A | (x, y) ∈ S} : ℚ≥0) / (Fintype.card A * Fintype.card B)
      = ∑ y : B, (#{x : A | (x, y) ∈ S} : ℚ≥0) / Fintype.card A / Fintype.card B := by
        refine sum_congr rfl fun y _ => ?_
        rw [div_div]
    _ ≤ ∑ _y : B, b / Fintype.card B := sum_le_sum fun y _ => div_le_div_of_nonneg_right (h y) (by positivity)
    _ ≤ b := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos (Fintype.card B) with h0 | h0
        · simp [h0]
        · rw [mul_div_cancel₀ _ (by exact_mod_cast h0.ne')]

section Exec

variable {ι : Type}

open Classical in
/-- The tree's bound per execution: over outcomes pairing the oracle `ρ` on the transcripts' words `U` with the
compression oracle `H`, child `v`'s `crBad` its execution's collision or window event among its first `Q v`
compression queries (`Edges.crEvent`, `σ v ρ` its prover at `ρ`), charged once per child at `Edges.epsCR K (Q v)`;
check `j`'s `testBad` at most `epsTest v j` of the `ρ` at every `H` (the round theorems' bounds off the execution's
collision event, `Bind.sumcheck_run_sound_at` and the like); the bus's and constraint batch's draw events at most
`epsBus v` and `epsBatch v` of the `ρ` at every `H` (`busRun_frac`, `batchRun_frac`). The bound is the sum over the
nodes of their reduction's `bad` fraction and those bounds, with the PCS bound `epsPCS v` (#551). -/
theorem tree_sound_exec (U : Finset ℕ) (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : (U → K) × ((Fin 14 → K) → Fin 4 → K) → ℕ → Fin 4 → K)
    (val : ι → (U → K) × ((Fin 14 → K) → Fin 4 → K) → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι ((U → K) × ((Fin 14 → K) → Fin 4 → K)))
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (batchBad : ι → Finset ((U → K) × ((Fin 14 → K) → Fin 4 → K)))
    (draw : ι → (U → K) × ((Fin 14 → K) → Fin 4 → K) → Fin 5 → E)
    (wit : ι → (U → K) × ((Fin 14 → K) → Fin 4 → K) → Witness)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (t v) (wit v ω))
    (hlink : ChecksGiveRows T cert t os L slot stRoot val P batchBad draw wit)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset ((U → K) × ((Fin 14 → K) → Fin 4 → K)))
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (σ : ι → (U → K) → List (Fin 4 → K) → Fin 14 → K) (Q : ι → ℕ)
    (hcrEq : ∀ v, P.crBad v = crEvent chainOf restOf (σ v) (Q v))
    (epsTest : ι → ℕ → ℚ≥0)
    (htest : ∀ v ∈ T.nodes, ∀ j < P.J v, ∀ H, (#{ρ : U → K | (ρ, H) ∈ P.testBad v j} : ℚ≥0) /
      Fintype.card (U → K) ≤ epsTest v j)
    (epsPCS epsBus epsBatch : ι → ℚ≥0) (hpcs : PcsBound P epsPCS)
    (hbus : ∀ v ∈ T.nodes, ∀ H, (#{ρ : U → K | (ρ, H) ∈ busBad (t v) (wit v) (draw v)} : ℚ≥0) /
      Fintype.card (U → K) ≤ epsBus v)
    (hbatch : ∀ v ∈ T.nodes, ∀ H, (#{ρ : U → K | (ρ, H) ∈ batchBad v} : ℚ≥0) / Fintype.card (U → K) ≤
      epsBatch v) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤
      ∑ v ∈ T.nodes, ((bad v).card / Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) +
        ∑ j ∈ range (P.J v), epsTest v j + epsPCS v + Edges.epsCR K (Q v) + epsBus v + epsBatch v) := by
  have hcr : ∀ v ∈ T.nodes, ((P.crBad v).card : ℚ≥0) / Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤
      Edges.epsCR K (Q v) := fun v _ => by
    rw [hcrEq v]
    convert crEvent_frac (Ω₀ := U → K) chainOf restOf (fun _ _ hr hc => input_ext hc hr) (σ v) (Q v)
  have hbus' : ∀ v ∈ T.nodes, ((busBad (t v) (wit v) (draw v)).card : ℚ≥0) /
      Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤ epsBus v := fun v hv => by
    convert frac_prod_le _ _ (hbus v hv)
  have hbatch' : ∀ v ∈ T.nodes, ((batchBad v).card : ℚ≥0) /
      Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤ epsBatch v := fun v hv => by
    convert frac_prod_le _ _ (hbatch v hv)
  refine (tree_sound_bound T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP batchBad draw wit hval
    hlink tD tM bad hstep hroot epsPCS (fun v => Edges.epsCR K (Q v)) epsBus epsBatch hpcs hcr hbus' hbatch').trans
    (sum_le_sum fun v hv => ?_)
  have hj : ∑ j ∈ range (P.J v), ((P.testBad v j).card : ℚ≥0) /
      Fintype.card ((U → K) × ((Fin 14 → K) → Fin 4 → K)) ≤ ∑ j ∈ range (P.J v), epsTest v j :=
    sum_le_sum fun j hjr => frac_prod_le _ _ (htest v hv j (mem_range.mp hjr))
  simp only [add_div, Nat.cast_sum, sum_div]
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl hj) le_rfl) le_rfl) le_rfl) le_rfl

end Exec

end LeanVMCircuits.Rec.AirLink

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model Bind

/-- `|E| = 2^192`: three coordinates over `K`. -/
theorem card_E : Fintype.card E = 2 ^ 192 := by
  rw [← Fintype.card_of_bijective (f := fun p : K × K × K => toE p.1 p.2.1 p.2.2)
    ⟨fun p q h => by
      obtain ⟨h0, h1, h2⟩ := toE_injective _ _ _ _ _ _ h
      exact Prod.ext h0 (Prod.ext h1 h2), fun e => by
      obtain ⟨a, b, c, h⟩ := toE_surjective e
      exact ⟨(a, b, c), h⟩⟩]
  simp [Fintype.card_prod, card_K]

/-- `epsCR` grows with the number of queries. -/
theorem epsCR_mono (V : Type) [Fintype V] {Q Q' : ℕ} (h : Q ≤ Q') : epsCR V Q ≤ epsCR V Q' := by
  unfold epsCR
  gcongr <;> omega

/-- The terms the tree's bound proves per child at deployed sizes: its checks', bus's and batch's bounds, at most
`2^40 / |E|` together, and one execution's `epsCR K Q`. -/
theorem exec_bound_deployed {Q D : ℕ} (hD : D ≤ 2 ^ 40) :
    (Q ≤ 2 ^ 84 → (D : ℚ≥0) / Fintype.card E + epsCR K Q ≤ 1 / 2) ∧
    (Q ≤ 2 ^ 82 → (D : ℚ≥0) / Fintype.card E + epsCR K Q ≤ 1 / 2 ^ 7) ∧
    (Q ≤ 2 ^ 74 → (D : ℚ≥0) / Fintype.card E + epsCR K Q ≤ 1 / 2 ^ 32) ∧
    (Q ≤ 2 ^ 63 → (D : ℚ≥0) / Fintype.card E + epsCR K Q ≤ 1 / 2 ^ 64) := by
  have hDE : (D : ℚ≥0) / Fintype.card E ≤ 2 ^ 40 / 2 ^ 192 := by
    rw [card_E]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hD) (by positivity)
  have key : ∀ (e : ℕ) (b : ℚ≥0), (2 ^ 40 / 2 ^ 192 : ℚ≥0) + epsCR K (2 ^ e) ≤ b → Q ≤ 2 ^ e →
      (D : ℚ≥0) / Fintype.card E + epsCR K Q ≤ b :=
    fun e b hb hQ => le_trans (add_le_add hDE (epsCR_mono K hQ)) hb
  refine ⟨key 84 _ ?_, key 82 _ ?_, key 74 _ ?_, key 63 _ ?_⟩ <;>
  · simp only [epsCR, card_K]
    rw [← NNRat.coe_le_coe]
    push_cast
    norm_num

/-- The cap: at `2^86` queries the window term alone is past one, so the bound is vacuous there. -/
theorem epsCR_cap : 1 ≤ epsCR K (2 ^ 86) := by
  simp only [epsCR, card_K]
  rw [← NNRat.coe_le_coe]
  push_cast
  norm_num

end LeanVMCircuits.Rec.Edges
