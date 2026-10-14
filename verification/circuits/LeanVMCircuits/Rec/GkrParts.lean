module

public import LeanVMCircuits.Rec.GkrInst
public import LeanVMCircuits.Rec.RecParts
public import LeanVMCircuits.Rec.LateSound

@[expose] public section

/-!
A radix-four GKR layer past the top as a check of `RecParts`.

`Bind.layer_part`: where the parent's circuit holds a linked layer's calls and its sumcheck's test (`LayerCert.layer_sem`), the layer's next claims true (each tree's level below at `[low, high] ++ r`, `AirLink.next_claim`) make its values, the previous layer's next claims, true (each tree's level at the previous point), off three events: its sumcheck's against the honest instance `AirLink.layerInst` (`sumcheckFalse`, which `sumcheck_run_sound_at` bounds), the line event `LineBad` (children not the true ones, yet every next claim the true children's, at most `2|S|` of the pairs `(low, high)` of `S × S`, `lineBad_card`) and the `λ` event `LamBad` (values not the true ones, yet one claim at `λ`, at most one `λ`, `lamBad_card`). So a chain of layers meets `RecParts.Ok.test` with those events, each layer's inputs its values and its outputs its next claims; bounding `LineBad` and `LamBad` over a run needs the layer's children bound before `low` and its values before `λ`, which `GkrCert` does not certify.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Sumcheck Finset

/-- A radix-four layer's `λ` event: its values (the previous layer's next claims) are not the true ones, yet both
combine at `λ` to one claim. -/
def LamBad (o T : Fin 2 → E) (lam : E) : Prop := o ≠ T ∧ o 0 + lam * o 1 = T 0 + lam * T 1

/-- A radix-four layer's line event: its children are not the true ones, yet every next claim, the line at `high`
through their lines at `low`, is the true children's. -/
def LineBad (kid T : Fin 2 → Fin 4 → E) (low high : E) : Prop :=
  kid ≠ T ∧ ∀ t, lineE (lineE (kid t 0) (kid t 1) low) (lineE (kid t 2) (kid t 3) low) high =
    lineE (lineE (T t 0) (T t 1) low) (lineE (T t 2) (T t 3) low) high

open Classical in
/-- The `λ` event is at most one draw: the two combinations differ by a nonzero line in `λ`. -/
theorem lamBad_card (S : Finset E) {o T : Fin 2 → E} (h : o ≠ T) : #{lam ∈ S | LamBad o T lam} ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  have ha' := ((Finset.mem_filter.mp ha).2).2
  have hb' := ((Finset.mem_filter.mp hb).2).2
  by_cases h1 : o 1 = T 1
  · exfalso
    have h0 : o 0 = T 0 := by rw [h1] at ha'; exact add_right_cancel ha'
    exact h (funext fun i => by fin_cases i <;> simp [h0, h1])
  · have hd : o 1 - T 1 ≠ 0 := sub_ne_zero.mpr h1
    have e : (a - b) * (o 1 - T 1) = 0 := by linear_combination ha' - hb'
    rcases mul_eq_zero.mp e with e | e
    · exact sub_eq_zero.mp e
    · exact absurd e hd

theorem lineE_sub (x y x' y' t : E) : lineE x y t - lineE x' y' t = lineE (x - x') (y - y') t := by
  simp only [lineE]
  ring

open Classical in
/-- The line event is at most `2|S|` of the pairs `(low, high)`: some value's children differ, and the difference of
its two lines through them is `card_plane_zero`'s plane. -/
theorem lineBad_card (S : Finset E) {kid T : Fin 2 → Fin 4 → E} (h : kid ≠ T) :
    #{p ∈ S ×ˢ S | LineBad kid T p.1 p.2} ≤ 2 * #S := by
  obtain ⟨t, ht⟩ : ∃ t, kid t ≠ T t := by
    by_contra hall
    push Not at hall
    exact h (funext hall)
  have hd : kid t 0 - T t 0 ≠ 0 ∨ kid t 1 - T t 1 ≠ 0 ∨ kid t 2 - T t 2 ≠ 0 ∨ kid t 3 - T t 3 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ht (funext fun c => by fin_cases c <;> simp [sub_eq_zero.mp hall.1, sub_eq_zero.mp hall.2.1,
      sub_eq_zero.mp hall.2.2.1, sub_eq_zero.mp hall.2.2.2])
  refine (card_le_card fun p hp => ?_).trans (card_plane_zero S hd)
  obtain ⟨hpS, -, hpl⟩ := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr ⟨hpS, ?_⟩
  rw [← lineE_sub, ← lineE_sub, ← lineE_sub, hpl t, sub_self]

/-- A radix-four GKR layer past the top is a check of `RecParts`: where the parent's circuit holds its sumcheck's test
and its calls (`LayerCert.layer_sem`), its next claims true (each tree's level below, `W t`, at `[low, high] ++ r`)
make its values true (each tree's level, the products of `W t`'s fours, at the previous point `p`), off its sumcheck's
event against the honest instance `AirLink.layerInst` (`sumcheckFalse`), the line event (`LineBad`, at most `2|E|` of
the pairs `(low, high)`, `lineBad_card`) and the `λ` event (`LamBad`, at most one `λ`, `lamBad_card`). -/
theorem layer_part {c : Cert} {s : State} {lc : LayerCert} {sc : SumcheckCert} {cs : Array Call} {rl : Array Bool}
    {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : (ℕ → K) → Val} {outs pt : List ℕ} {T' : ℕ → E} (ρ : ℕ → K)
    (hF : Facts cs rl os st (val ρ)) (hlink : lc.linkOk sc os outs pt = true) (hok : lc.layer.ok os cs rl = true)
    (hm : lc.layer.m = 2) (p : Fin sc.rounds.length → E) (W : Fin 2 → ℕ → E)
    (htest : ∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b)
    (hhint : ∀ w ∈ sc.hints, Model.ev (val ρ) w = T' w)
    (hout : ∀ t : Fin 2, Model.ev (val ρ) (lc.layer.out os t) =
      AirLink.mleAt (sc.rounds.length + 2) (Fin.cons (Model.ev (val ρ) lc.layer.low.chal)
        (Fin.cons (Model.ev (val ρ) lc.layer.high.chal) (readR (chalWords c.outs sc.chals) ρ))) (W t))
    (hnot : ¬ sumcheckFalse c s sc (AirLink.layerInst _ p (Model.ev (val ρ) lc.layer.lam.chal) W) T' val ρ)
    (hlam : ¬ LamBad (fun t => Model.ev (val ρ) (outs.getD t 0))
      (fun t => AirLink.mleAt _ p fun z => ∏ c ∈ range 4, W t (4 * z + c)) (Model.ev (val ρ) lc.layer.lam.chal))
    (hline : ¬ LineBad (fun t i => Model.ev (val ρ) (lc.layer.kid t i))
      (fun t i => MvPolynomial.eval (readR (chalWords c.outs sc.chals) ρ) (AirLink.childMle _ (W t) i))
      (Model.ev (val ρ) lc.layer.low.chal) (Model.ev (val ρ) lc.layer.high.chal)) :
    ∀ t : Fin 2, Model.ev (val ρ) (outs.getD t 0) = AirLink.mleAt _ p fun z => ∏ c ∈ range 4, W t (4 * z + c) := by
  obtain ⟨hres, -, hclaim, hfinal, hlines⟩ := LayerCert.layer_sem hF hlink hok
  have hvals : lc.layer.values = outs := (LayerCert.link_sem hlink).2.1
  have hlen : outs.length = 2 := by rw [← hvals]; exact hm
  have hkid : (fun (t : Fin 2) (i : Fin 4) => Model.ev (val ρ) (lc.layer.kid t i)) =
      fun (t : Fin 2) (i : Fin 4) => MvPolynomial.eval (readR (chalWords c.outs sc.chals) ρ)
        (AirLink.childMle _ (W t) i) := by
    by_contra hne
    exact hline ⟨hne, fun t => (hlines t (by rw [hm]; exact t.isLt)).symm.trans
      ((hout t).trans (AirLink.next_claim _ _ _ _ _))⟩
  have hk : ∀ (t : Fin 2) (i : Fin 4), Model.ev (val ρ) (lc.layer.kid t i) =
      MvPolynomial.eval (readR (chalWords c.outs sc.chals) ρ) (AirLink.childMle _ (W t) i) :=
    fun t i => congrFun (congrFun hkid t) i
  have hfin : Model.ev (val ρ) sc.final =
      (AirLink.layerInst _ p (Model.ev (val ρ) lc.layer.lam.chal) W).final (readR (chalWords c.outs sc.chals) ρ) := by
    rw [hfinal, AirLink.layerInst_final, hm]
    have ek : ∀ (t : Fin 2) (i : ℕ), i < 4 → Model.ev (val ρ) (lc.layer.kid t i) =
        MvPolynomial.eval (readR (chalWords c.outs sc.chals) ρ) (AirLink.childMle _ (W t) i) :=
      fun t i hi => hk t ⟨i, hi⟩
    simp only [eval_polyOf, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil, List.foldr_cons, List.foldr_nil, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      one_mul, Finset.prod_range_succ, Finset.prod_range_zero, zero_mul, zero_add]
    have e0 := ek 0 0 (by norm_num); have e1 := ek 0 1 (by norm_num)
    have e2 := ek 0 2 (by norm_num); have e3 := ek 0 3 (by norm_num)
    have f0 := ek 1 0 (by norm_num); have f1 := ek 1 1 (by norm_num)
    have f2 := ek 1 2 (by norm_num); have f3 := ek 1 3 (by norm_num)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one] at e0 e1 e2 e3 f0 f1 f2 f3
    rw [e0, e1, e2, e3, f0, f1, f2, f3]
    ring
  have hsum : Model.ev (val ρ) sc.claim0 = (AirLink.layerInst _ p (Model.ev (val ρ) lc.layer.lam.chal) W).sum := by
    by_contra hne
    exact hnot ⟨⟨hhint, htest, by rw [hres, hfin]; simp⟩, hne⟩
  rw [hclaim, AirLink.layerInst_sum] at hsum
  obtain ⟨o0, o1, rfl⟩ : ∃ a b, outs = [a, b] := by
    match outs, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have hall : (fun t : Fin 2 => Model.ev (val ρ) ([o0, o1].getD t 0)) =
      fun t => AirLink.mleAt _ p fun z => ∏ c ∈ range 4, W t (4 * z + c) := by
    by_contra hne
    refine hlam ⟨hne, ?_⟩
    simp only [eval_polyOf, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Fin.sum_univ_two,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, zero_mul, zero_add] at hsum
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, List.getD_cons_zero, List.getD_cons_succ]
    linear_combination hsum
  exact fun t => congrFun hall t

/-- Non-vacuity of the events: values `(0, 1)` against true `(1, 0)` combine to one claim at `λ = 1`, and children
off by one in a single slot give every next claim the true one at `low = 0` (the line through the first two) and
`high = 0`. -/
example : LamBad ![0, 1] ![1, 0] 1 ∧ LineBad (fun _ => ![0, 0, 1, 0]) (fun _ => ![0, 0, 0, 0]) 0 0 := by
  refine ⟨⟨fun h => by simpa using congrFun h 0, by simp⟩, fun h => by simpa using congrFun (congrFun h 0) 2,
    fun t => by simp [lineE]⟩

end LeanVMCircuits.Rec.Bind
