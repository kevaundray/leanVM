module

public import LeanVMCircuits.Rec.TableSum
public import LeanVMCircuits.Rec.Design

@[expose] public section

/-!
The layout's heights from `Tree::converge`, and the table sumcheck's rounds.

`Tree::new` builds every circuit at its tier's heights `σ t` (`Tree::converge`, `Design.converge`): it rebuilds the circuits at the tiers' heights until no circuit's heights (`Circuit::heights`) pass its tier's, each round requiring `RecLayout::from_taus` to accept each tier's (every `τ` at most `MAX_TAU = 32`), and then raises each circuit's floor to its tier's heights (`Circuit::with_floor`). A node's verifier reads a child of tier `t` at `σ t` (`RecShape::new`). `layoutFits_converge`: where each circuit's heights hold its rows (`HeightsHold`: `Table::height_log` is at least the rows' `clog 2`), every circuit `converge` returns fits its tier's layout (`LayoutFits`), the hypothesis `AirLink.checksGiveInst_of_table` takes.

`constraints::verify` runs `n` rounds, `n` the tallest owned table's `τ` (`airs.iter().map(|a| a.tau).max()`): `taus_le_rounds` is the other hypothesis, every owned table's `τ` at most `n`.
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model Finset Edges

/-- The tables, `Table.all`. -/
instance : Fintype Table where
  elems := {.emul, .exk, .hash, .split, .cast, .pub}
  complete T := by cases T <;> simp

/-- A circuit's heights hold its rows: each table's rows at most `2^h_T` (`Circuit::heights`). -/
def HeightsHold (s : State) (h : Table → ℕ) : Prop := ∀ T, (rowsOf s T).size ≤ 2 ^ h T

/-- `RecLayout::from_taus` accepts the heights: every `τ` at most `MAX_TAU = 32`. -/
def fitsTaus (σ : Table → ℕ) : Bool := decide (∀ T, σ T ≤ 32)

/-- The least heights holding a circuit's rows: `clog 2` of each table's rows, which `Table::height_log` is at least
(`log2_ceil_usize`, and flock's batch for the hash table). -/
theorem heightsHold_clog (s : State) : HeightsHold s fun T => Nat.clog 2 (rowsOf s T).size :=
  fun _ => Nat.le_pow_clog (by norm_num) _

/-- Heights holding a circuit's rows, below heights `RecLayout::from_taus` accepts, make a layout that fits. -/
theorem layoutFits_of_le {s : State} {h σ : Table → ℕ} (hh : HeightsHold s h) (hle : ∀ T, h T ≤ σ T)
    (hσ : fitsTaus σ = true) : LayoutFits s σ := by
  have h32 : ∀ T, σ T ≤ 32 := by simpa [fitsTaus] using hσ
  exact fun T => ⟨(hh T).trans (Nat.pow_le_pow_right (by norm_num) (hle T)), h32 T⟩

/-- Every circuit `Tree::converge` returns fits its tier's layout: circuit `p` of tier `t`, built at the tiers'
heights `σ` (`circ σ p`), with heights `H σ p` holding its rows, fits `σ t`. -/
theorem layoutFits_converge (n : ℕ) (members : ℕ → List ℕ) (circ : (ℕ → Table → ℕ) → ℕ → State)
    (H : (ℕ → Table → ℕ) → ℕ → Table → ℕ) (hH : ∀ σ p, HeightsHold (circ σ p) (H σ p)) (k : ℕ)
    (σ₀ σ : ℕ → Table → ℕ) (h : Design.converge n members H fitsTaus k σ₀ = some σ) :
    ∀ t < n, ∀ p ∈ members t, LayoutFits (circ σ p) (σ t) := by
  obtain ⟨hfit, hle, -⟩ := Design.converge_fits n members H fitsTaus k σ₀ σ h
  exact fun t ht p hp => layoutFits_of_le (hH σ p) (hle t ht p hp) (hfit t ht)

/-- Non-vacuity: a tier of one empty circuit at heights three converges in two rounds, and fits them. -/
example : Design.converge 1 (fun _ => [0]) (fun _ _ _ => 3) fitsTaus 2 (fun _ _ => 3) = some (fun _ _ => 3) ∧
    LayoutFits ({} : State) fun _ => 3 :=
  have h : Design.converge 1 (fun _ => [0]) (fun _ _ _ => 3) fitsTaus 2 (fun _ _ => 3) = some (fun _ _ => 3) :=
    rfl
  ⟨h, layoutFits_converge 1 (fun _ => [0]) (fun _ _ => {}) (fun _ _ _ => 3)
    (fun _ _ T => by cases T <;> simp [rowsOf]) 2 _ _ h 0 one_pos 0 (by simp)⟩

/-- The table sumcheck's rounds, `constraints::verify`'s `n`: the tallest owned table's `τ`. -/
def rounds (taus : Table → ℕ) : ℕ := owned.sup taus

/-- Every owned table's `τ` is at most the rounds. -/
theorem taus_le_rounds (taus : Table → ℕ) : ∀ T ∈ owned, taus T ≤ rounds taus := fun _ hT => le_sup hT

/-- `ChecksGiveRows` from `ChecksGiveTable` for a tree `Tree::converge` built: each child `v` is circuit `pos v` of
tier `tier v` built at the converged heights `σ`, its parent's verifier reads it at its tier's heights, and the table
sumcheck runs `rounds` of them. `checksGiveRows_of_table`'s layout and rounds hypotheses hold (`layoutFits_converge`,
`taus_le_rounds`). -/
theorem checksGiveRows_of_converge {ι Ω : Type} [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → Edges.EdgeCert)
    (t : ι → State) (os : ι → Array (List ℕ)) (L : Edges.Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K)
    (val : ι → Ω → Val) (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (qforms : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → Table → Quad)
    (tot : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (roots : ι → Ω → Fin 2 → E) (draw : ι → Ω → Fin 5 → E)
    (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K) (m : ℕ) (members : ℕ → List ℕ)
    (circ : (ℕ → Table → ℕ) → ℕ → State) (H : (ℕ → Table → ℕ) → ℕ → Table → ℕ)
    (hH : ∀ σ p, HeightsHold (circ σ p) (H σ p)) (k : ℕ) (σ₀ σ : ℕ → Table → ℕ)
    (hconv : Design.converge m members H fitsTaus k σ₀ = some σ) (tier pos : ι → ℕ)
    (hpos : ∀ v ∈ T.nodes, tier v < m ∧ pos v ∈ members (tier v) ∧ t v = circ σ (pos v) ∧ taus v = σ (tier v) ∧
      n v = rounds (taus v))
    (h : ChecksGiveTable T cert t os L slot stRoot val P n bdraw qforms tot roots draw taus cols) :
    ChecksGiveRows T cert t os L slot stRoot val P
      (fun v => batchBad (witAt T cert t slot stRoot val taus cols v)
        (fun ω ζ i => formSums (witAt T cert t slot stRoot val taus cols v ω) ζ (qforms v ω ζ) i - tot v ω ζ i)
        (bdraw v))
      draw (witAt T cert t slot stRoot val taus cols) := by
  refine checksGiveRows_of_table T cert t os L slot stRoot val P n bdraw qforms tot roots draw taus cols
    (fun v hv => ?_) (fun v hv T' hT' => ?_) h
  · obtain ⟨ht, hp, htv, hτ, -⟩ := hpos v hv
    rw [htv, hτ]
    exact layoutFits_converge m members circ H hH k σ₀ σ hconv (tier v) ht (pos v) hp
  · obtain ⟨-, -, -, -, hn⟩ := hpos v hv
    rw [hn]
    exact taus_le_rounds (taus v) T' hT'

end LeanVMCircuits.Rec.AirLink
