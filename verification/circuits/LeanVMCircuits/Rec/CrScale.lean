module

public import LeanVMCircuits.Rec.Collision
public import LeanVMCircuits.Rec.Run

@[expose] public section

/-!
The collision term at deployed sizes, and charging collisions to one execution.

`Bind.RomAnswers` asks every two answers of a run's family (`Bind.Run.rom`, one answer per oracle) not to collide, and `Bind.RomAnswers.of_run` gets that from one prover's first `Q` compression queries only if those cover every answer's compressions: one per challenge vector, so `Q` is at least `|E|^n` times one execution's count, and `Edges.epsCR` of it is past one. The tree's bound with that `Q` is vacuous. The fix is to charge collisions per execution: `Bind.run_frac_off` bounds the oracles at which an event holds by the fraction at which it holds off a collision event `C` of the oracle (counted over the challenge vectors put in, as `Bind.run_frac`) plus the fraction of oracles in `C` itself, once; the round theorems then need agreement only between collision-free answers sharing the prefix before the challenge, which is not yet stated here.

`epsCR_deployed`: at the field's `2^64` words, one execution's `epsCR` is below `2^-7` for `2^60` queries and at least one for `2^64`, where the two-word output window term `3 Q (Q - 1) / (2 |K|^2)` reaches one: the 128-bit window collision, not the compression's 256-bit output, sets the scale.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Finset

/-- `Q` off the collision event `C`. -/
def offC (Q C : (ℕ → K) → Prop) (ρ : ℕ → K) : Prop := Q ρ ∧ ¬ C ρ

open Classical in
/-- Charging a collision event once: the oracles on `U` at which `Q` holds are at most the challenge vectors' fraction at which `Q` holds off `C`, at every oracle, plus the oracles in `C`. -/
theorem run_frac_off {n : ℕ} {own : Fin n → Fin 3 → ℕ} {U : Finset ℕ} (hinj : OwnInj own) (hU : ∀ i k, own i k ∈ U)
    (Q C : (ℕ → K) → Prop) (B : ℕ)
    (hB : ∀ ρ : ℕ → K, #{r : Fin n → E | offC Q C (oracleAt own ρ r)} * Fintype.card E ≤ B * Fintype.card E ^ n) :
    (#{ρ : U → K | Q (extU U ρ)} : ℚ≥0) / Fintype.card (U → K) ≤
      B / Fintype.card E + (#{ρ : U → K | C (extU U ρ)} : ℚ≥0) / Fintype.card (U → K) := by
  have h1 := run_frac hinj hU (offC Q C) B hB
  have hsub : #{ρ : U → K | Q (extU U ρ)} ≤ #{ρ : U → K | offC Q C (extU U ρ)} + #{ρ : U → K | C (extU U ρ)} := by
    refine (card_le_card fun ρ hρ => ?_).trans (card_union_le _ _)
    simp only [mem_filter, mem_univ, true_and, mem_union] at hρ ⊢
    by_cases hc : C (extU U ρ)
    · exact Or.inr hc
    · exact Or.inl ⟨hρ, hc⟩
  have h2 : (#{ρ : U → K | Q (extU U ρ)} : ℚ≥0) ≤
      (#{ρ : U → K | offC Q C (extU U ρ)} : ℚ≥0) + #{ρ : U → K | C (extU U ρ)} :=
    (Nat.cast_le.mpr hsub).trans_eq (Nat.cast_add _ _)
  have h3 := div_le_div_of_nonneg_right (c := (Fintype.card (U → K) : ℚ≥0)) h2 (by positivity)
  rw [add_div] at h3
  exact le_trans h3 (add_le_add_left h1 _)

end LeanVMCircuits.Rec.Bind

namespace LeanVMCircuits.Rec.Edges

/-- One execution's `epsCR` at the field's words: below `2^-7` for `2^60` compression queries, and at least one for `2^64`. -/
theorem epsCR_deployed : epsCR K (2 ^ 60) ≤ 1 / 2 ^ 7 ∧ 1 ≤ epsCR K (2 ^ 64) := by
  simp only [epsCR, card_K]
  constructor
  · rw [← NNRat.coe_le_coe]
    push_cast
    norm_num
  · rw [← NNRat.coe_le_coe]
    push_cast
    norm_num

end LeanVMCircuits.Rec.Edges
