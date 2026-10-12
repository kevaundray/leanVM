module

public import Mathlib.Tactic

@[expose] public section

/-!
Determination rules and their closure.

A rule says: once every premise node is determined, every conclusion node is. `Closure r seeds` is what the rules
determine from the seeds. `closure_agree` is what that means: two assignments of values to nodes that agree on the
seeds, and for which every rule is valid (agreeing on a rule's premises, they agree on its conclusions), agree on
every node of the closure.

`certify` replays a list of rule firings, the certificate `CheckBind`'s worklist records, marking a node only when a
seed or a firing whose premises are marked gives it; `certify_sound`: every node it marks is in the closure. So the
checker's verdict rests on this small replay, not on the worklist.

Each rule carries a justification of type `J`, why it holds; `LeanVMCircuits.Rec.Bind.Just` checks it against the
circuit.
-/

namespace LeanVMCircuits.Rec.Bind

/-- Determination rules over nodes, each its premises, conclusions and justification, flattened. -/
structure Rules (J : Type) where
  premOff : Array ℕ := #[0]
  prems : Array ℕ := #[]
  conclOff : Array ℕ := #[0]
  concls : Array ℕ := #[]
  why : Array J := #[]
  deriving Inhabited

variable {J : Type}

def Rules.size (r : Rules J) : ℕ := r.why.size

def Rules.push (r : Rules J) (w : J) (ps cs : Array ℕ) : Rules J :=
  { premOff := r.premOff.push (r.prems.size + ps.size), prems := r.prems ++ ps,
    conclOff := r.conclOff.push (r.concls.size + cs.size), concls := r.concls ++ cs, why := r.why.push w }

/-- Rule `i`'s premises. -/
def Rules.prem (r : Rules J) (i : ℕ) : List ℕ :=
  (r.prems.extract (r.premOff.getD i 0) (r.premOff.getD (i + 1) 0)).toList

/-- Rule `i`'s conclusions. -/
def Rules.concl (r : Rules J) (i : ℕ) : List ℕ :=
  (r.concls.extract (r.conclOff.getD i 0) (r.conclOff.getD (i + 1) 0)).toList

/-- What the rules determine from the seeds. -/
inductive Closure (r : Rules J) (seeds : List ℕ) : ℕ → Prop
  | seed {n : ℕ} : n ∈ seeds → Closure r seeds n
  | fire {i n : ℕ} : i < r.size → (∀ p ∈ r.prem i, Closure r seeds p) → n ∈ r.concl i → Closure r seeds n

/-- Rule `i` is valid for two assignments: agreeing on its premises, they agree on its conclusions. -/
def Valid {α : Type} (r : Rules J) (ν ν' : ℕ → α) (i : ℕ) : Prop :=
  (∀ p ∈ r.prem i, ν p = ν' p) → ∀ c ∈ r.concl i, ν c = ν' c

/-- Two assignments agreeing on the seeds, for which every rule is valid, agree on the closure. -/
theorem closure_agree {α : Type} {r : Rules J} {seeds : List ℕ} {ν ν' : ℕ → α}
    (hv : ∀ i < r.size, Valid r ν ν' i) (hs : ∀ n ∈ seeds, ν n = ν' n) {n : ℕ} (h : Closure r seeds n) :
    ν n = ν' n := by
  induction h with
  | seed hn => exact hs _ hn
  | fire hi _ hn ih => exact hv _ hi (fun p hp => ih p hp) _ hn

/-- Mark the nodes `ns`. -/
def mark (m : Array Bool) (ns : List ℕ) : Array Bool := ns.foldl (fun m n => m.setIfInBounds n true) m

/-- Fire rule `i` if it is a rule and its premises are marked. -/
def fire (r : Rules J) (m : Array Bool) (i : ℕ) : Array Bool :=
  if i < r.size ∧ (r.prem i).all (m.getD · false) then mark m (r.concl i) else m

/-- The nodes a certificate marks: the seeds, then each firing in order. -/
def certify (r : Rules J) (nodes : ℕ) (seeds : List ℕ) (firings : Array ℕ) : Array Bool :=
  firings.foldl (fire r) (mark (Array.replicate nodes false) seeds)

theorem getD_setIfInBounds (m : Array Bool) (k n : ℕ) (h : (m.setIfInBounds k true).getD n false = true) :
    m.getD n false = true ∨ n = k := by
  by_cases hk : n = k
  · exact Or.inr hk
  · left
    simp only [Array.getD_eq_getD_getElem?] at h ⊢
    rwa [Array.getElem?_setIfInBounds_ne (Ne.symm hk)] at h

theorem mark_marked (ns : List ℕ) : ∀ (m : Array Bool) (n : ℕ), (mark m ns).getD n false = true →
    m.getD n false = true ∨ n ∈ ns := by
  induction ns with
  | nil => intro m n h; exact Or.inl h
  | cons k ks ih =>
    intro m n h
    rcases ih _ n h with h | h
    · rcases getD_setIfInBounds m k n h with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem replicate_unmarked (nodes n : ℕ) : (Array.replicate nodes false).getD n false = false := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- Every node a certificate marks is in the closure. -/
theorem certify_sound (r : Rules J) (nodes : ℕ) (seeds : List ℕ) (firings : Array ℕ) (n : ℕ)
    (h : (certify r nodes seeds firings).getD n false = true) : Closure r seeds n := by
  -- The invariant: every marked node is in the closure.
  let Inv := fun (m : Array Bool) => ∀ k, m.getD k false = true → Closure r seeds k
  have h0 : Inv (mark (Array.replicate nodes false) seeds) := by
    intro k hk
    rcases mark_marked seeds _ k hk with hk | hk
    · rw [replicate_unmarked] at hk; exact absurd hk Bool.false_ne_true
    · exact .seed hk
  have step : ∀ m i, Inv m → Inv (fire r m i) := by
    intro m i hm k hk
    unfold fire at hk
    split at hk
    · rename_i hc
      rcases mark_marked _ m k hk with hk | hk
      · exact hm k hk
      · refine .fire hc.1 (fun p hp => hm p ?_) hk
        exact List.all_eq_true.mp hc.2 p hp
    · exact hm k hk
  have hall : ∀ (fs : List ℕ) (m : Array Bool), Inv m → Inv (fs.foldl (fire r) m) := by
    intro fs
    induction fs with
    | nil => intro m hm; exact hm
    | cons f fs ih => intro m hm; exact ih _ (step m f hm)
  unfold certify at h
  rw [← Array.foldl_toList] at h
  exact hall firings.toList _ h0 n h

end LeanVMCircuits.Rec.Bind
