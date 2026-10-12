module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

@[expose] public section

/-!
Round-by-round soundness of sumcheck, the protocol behind most of the recursion verifier's tests bound only after
their latest challenge.

An instance's truths (`Inst`): with rounds left, the honest round polynomial and the instance after each challenge;
with none, the final value the verifier computes itself. `Inst.ok d`: the honest polynomials have degree at most `d`
and each challenge's instance sums to the honest polynomial at it. A prover (`Prover`) answers each round with a
polynomial of degree at most `d` that may depend on the challenges so far. The verifier (`accepts`) checks that each
round's polynomial sums over `{0, 1}` to the running claim, takes the polynomial at the challenge as the next claim,
and checks the last claim against the final value.

`sumcheck_sound`: if the claim is not the instance's sum, the challenge vectors of `S^n` at which the verifier
accepts are at most `n · d · |S|^(n-1)`, so at most an `n · d / |S|` fraction (`sumcheck_sound_frac`). Each round's
polynomial is fixed before its challenge is drawn, which is what `Bind.tests_by` gives the circuit's tests.

Not proven here: that the recursion circuit's late tests are the checks of `accepts` for its reductions' instances.
-/

namespace LeanVMCircuits.Rec.Sumcheck

open Polynomial Finset Classical

variable {F : Type} [Field F] [DecidableEq F]

/-- An instance's truths for `n` rounds. -/
inductive Inst (F : Type) [Field F] : ℕ → Type
  | leaf (v : F) : Inst F 0
  | node {n : ℕ} (H : F[X]) (next : F → Inst F n) : Inst F (n + 1)

/-- The instance's sum: the final value, or the honest polynomial's sum over `{0, 1}`. -/
noncomputable def Inst.sum : {n : ℕ} → Inst F n → F
  | _, .leaf v => v
  | _, .node H _ => H.eval 0 + H.eval 1

/-- The honest polynomials have degree at most `d`, and each challenge's instance sums to the polynomial at it. -/
def Inst.ok (d : ℕ) : {n : ℕ} → Inst F n → Prop
  | _, .leaf _ => True
  | _, .node H next => H.natDegree ≤ d ∧ ∀ r, (next r).sum = H.eval r ∧ (next r).ok d

/-- A prover for `n` rounds: a polynomial, then a prover after each challenge. -/
inductive Prover (F : Type) [Field F] : ℕ → Type
  | leaf : Prover F 0
  | node {n : ℕ} (g : F[X]) (next : F → Prover F n) : Prover F (n + 1)

/-- The prover's polynomials have degree at most `d`. -/
def Prover.ok (d : ℕ) : {n : ℕ} → Prover F n → Prop
  | _, .leaf => True
  | _, .node g next => g.natDegree ≤ d ∧ ∀ r, (next r).ok d

/-- The verifier accepts the claim `c` at the challenges `r`, the first challenge first. -/
def accepts : {n : ℕ} → Inst F n → Prover F n → F → (Fin n → F) → Prop
  | _, .leaf v, .leaf, c, _ => c = v
  | _, .node _ nI, .node g nP, c, r => g.eval 0 + g.eval 1 = c ∧ accepts (nI (r 0)) (nP (r 0)) (g.eval (r 0)) (Fin.tail r)

/-- A nonzero polynomial of degree at most `d` vanishes at at most `d` points of `S`. -/
theorem card_roots_le (S : Finset F) {p : F[X]} (hp : p ≠ 0) {d : ℕ} (hd : p.natDegree ≤ d) :
    #{a ∈ S | p.eval a = 0} ≤ d := by
  classical
  calc #{a ∈ S | p.eval a = 0} ≤ #p.roots.toFinset := by
        refine card_le_card fun a ha => ?_
        rw [mem_filter] at ha
        rw [Multiset.mem_toFinset, mem_roots hp]
        exact ha.2
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
    _ ≤ d := hd

omit [Field F] [DecidableEq F] in
/-- Counting over `S^(n+1)` by the first coordinate. -/
theorem card_cons (S : Finset F) (n : ℕ) (P : F → (Fin n → F) → Prop) [DecidablePred fun r : Fin (n + 1) → F =>
    P (r 0) (Fin.tail r)] [∀ a, DecidablePred (P a)] :
    #{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | P (r 0) (Fin.tail r)} =
      ∑ a ∈ S, #{t ∈ Fintype.piFinset (fun _ : Fin n => S) | P a t} := by
  classical
  rw [← card_sigma]
  refine card_bij' (fun r _ => ⟨r 0, Fin.tail r⟩) (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, Fintype.mem_piFinset] at hr
    simp only [mem_sigma, mem_filter, Fintype.mem_piFinset]
    exact ⟨hr.1 0, fun i => hr.1 i.succ, hr.2⟩
  · intro p hp
    simp only [mem_sigma, mem_filter, Fintype.mem_piFinset] at hp
    simp only [mem_filter, Fintype.mem_piFinset, Fin.cons_zero, Fin.tail_cons]
    refine ⟨fun i => ?_, hp.2.2⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hp.1
    · simpa using hp.2.1 j
  · intro r _
    simp
  · intro p _
    simp

/-- Sumcheck's round-by-round soundness: if the claim is not the instance's sum, the verifier accepts at at most
`n · d · |S|^(n-1)` challenge vectors of `S^n`. -/
theorem sumcheck_sound (S : Finset F) (d : ℕ) :
    ∀ {n : ℕ} (I : Inst F n) (P : Prover F n), I.ok d → P.ok d → ∀ c, c ≠ I.sum →
      #{r ∈ Fintype.piFinset (fun _ : Fin n => S) | accepts I P c r} ≤ n * d * #S ^ (n - 1)
  | _, .leaf v, .leaf, _, _, c, hc => by
    simp only [accepts, Inst.sum] at hc ⊢
    simp [hc]
  | n + 1, .node H nI, .node g nP, hI, hP, c, hc => by
    classical
    obtain ⟨hH, hnext⟩ := hI
    obtain ⟨hg, hPn⟩ := hP
    simp only [Inst.sum] at hc
    -- Accepting: the first polynomial is not the honest one, and it agrees with it at the challenge or the next
    -- claim is false and the rest accepts it.
    have hsub : {r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | accepts (.node H nI) (.node g nP) c r} ⊆
        {r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | (g - H).eval (r 0) = 0 ∧ True} ∪
        {r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) |
          g.eval (r 0) ≠ (nI (r 0)).sum ∧ accepts (nI (r 0)) (nP (r 0)) (g.eval (r 0)) (Fin.tail r)} := by
      intro r hr
      simp only [mem_filter, accepts] at hr
      simp only [mem_union, mem_filter, and_true, eval_sub, sub_eq_zero]
      by_cases he : g.eval (r 0) = H.eval (r 0)
      · exact Or.inl ⟨hr.1, he⟩
      · exact Or.inr ⟨hr.1, by rw [(hnext (r 0)).1]; exact he, hr.2.2⟩
    by_cases hgH : g = H
    · subst hgH
      have hemp : {r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | accepts (.node g nI) (.node g nP) c r} = ∅ := by
        ext r
        simp only [mem_filter, accepts, Finset.notMem_empty, iff_false, not_and]
        intro _ h
        exact fun _ => hc h.symm
      rw [hemp, card_empty]
      exact Nat.zero_le _
    have hne : g - H ≠ 0 := sub_ne_zero.mpr hgH
    have hd' : (g - H).natDegree ≤ d := (natDegree_sub_le g H).trans (max_le hg hH)
    have hT : #(Fintype.piFinset fun _ : Fin n => S) = #S ^ n := by simp [Fintype.card_piFinset]
    -- The first polynomial agrees with the honest one at the challenge: at most `d` first challenges.
    have h1 : #{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | (g - H).eval (r 0) = 0 ∧ True} ≤ d * #S ^ n := by
      have e := card_cons S n (fun a (_ : Fin n → F) => (g - H).eval a = 0 ∧ True)
      rw [e]
      have hs : ∀ a ∈ S, #{t ∈ Fintype.piFinset (fun _ : Fin n => S) | (g - H).eval a = 0 ∧ True} =
          if (g - H).eval a = 0 then #S ^ n else 0 := by
        intro a _
        by_cases ha : (g - H).eval a = 0
        · rw [if_pos ha, Finset.filter_true_of_mem fun _ _ => ⟨ha, trivial⟩, hT]
        · rw [if_neg ha, Finset.filter_false_of_mem fun _ _ h => ha h.1, card_empty]
      rw [sum_congr rfl hs, ← sum_filter, sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (card_roots_le S hne hd')
    -- Otherwise the next claim is false, and the rest accepts it.
    have h2 : #{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) |
        g.eval (r 0) ≠ (nI (r 0)).sum ∧ accepts (nI (r 0)) (nP (r 0)) (g.eval (r 0)) (Fin.tail r)} ≤
        #S * (n * d * #S ^ (n - 1)) := by
      have e := card_cons S n (fun a t => g.eval a ≠ (nI a).sum ∧ accepts (nI a) (nP a) (g.eval a) t)
      rw [e]
      calc ∑ a ∈ S, #{t ∈ Fintype.piFinset (fun _ : Fin n => S) | g.eval a ≠ (nI a).sum ∧
              accepts (nI a) (nP a) (g.eval a) t}
          ≤ ∑ _a ∈ S, n * d * #S ^ (n - 1) := by
            refine sum_le_sum fun a _ => ?_
            by_cases ha : g.eval a = (nI a).sum
            · simp [ha]
            · refine (card_le_card fun t ht => ?_).trans
                (sumcheck_sound S d (nI a) (nP a) (hnext a).2 (hPn a) (g.eval a) ha)
              simp only [mem_filter] at ht ⊢
              exact ⟨ht.1, ht.2.2⟩
        _ = #S * (n * d * #S ^ (n - 1)) := by rw [sum_const, smul_eq_mul]
    have h3 : #S * (n * d * #S ^ (n - 1)) ≤ n * d * #S ^ n := by
      rcases n with _ | n
      · simp
      · rw [show n + 1 - 1 = n by omega, pow_succ]
        nlinarith [Nat.zero_le (#S), Nat.zero_le ((n + 1) * d * #S ^ n)]
    calc #{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | accepts (.node H nI) (.node g nP) c r}
        ≤ #({r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | (g - H).eval (r 0) = 0 ∧ True} ∪
          {r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) |
            g.eval (r 0) ≠ (nI (r 0)).sum ∧ accepts (nI (r 0)) (nP (r 0)) (g.eval (r 0)) (Fin.tail r)}) :=
          card_le_card hsub
      _ ≤ d * #S ^ n + #S * (n * d * #S ^ (n - 1)) := (card_union_le _ _).trans (add_le_add h1 h2)
      _ ≤ (n + 1) * d * #S ^ (n + 1 - 1) := by
        rw [show n + 1 - 1 = n by omega]
        nlinarith [h3]

/-- Sumcheck's soundness as a fraction: if the claim is not the instance's sum, the verifier accepts at at most an
`n · d / |S|` fraction of the challenge vectors of `S^n`. -/
theorem sumcheck_sound_frac (S : Finset F) (hS : S.Nonempty) (d : ℕ) {n : ℕ} (I : Inst F n) (P : Prover F n)
    (hI : I.ok d) (hP : P.ok d) (c : F) (hc : c ≠ I.sum) :
    (#{r ∈ Fintype.piFinset (fun _ : Fin n => S) | accepts I P c r} : ℚ≥0) / #S ^ n ≤ n * d / #S := by
  have h := sumcheck_sound S d I P hI hP c hc
  have hS0 : (0 : ℚ≥0) < #S := by exact_mod_cast hS.card_pos
  rw [div_le_div_iff₀ (pow_pos hS0 n) hS0]
  rcases n with _ | n
  · have : (#{r ∈ Fintype.piFinset (fun _ : Fin 0 => S) | accepts I P c r} : ℚ≥0) = 0 := by
      exact_mod_cast Nat.le_zero.mp (by simpa using h)
    rw [this]
    simp
  · have h' : (#{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | accepts I P c r} : ℚ≥0) ≤
        (n + 1) * d * #S ^ n := by
      have := h
      rw [show n + 1 - 1 = n by omega] at this
      exact_mod_cast this
    calc (#{r ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S) | accepts I P c r} : ℚ≥0) * #S
        ≤ (n + 1) * d * #S ^ n * #S := by gcongr
      _ = ((n + 1 : ℕ) : ℚ≥0) * d * #S ^ (n + 1) := by push_cast; ring

end LeanVMCircuits.Rec.Sumcheck
