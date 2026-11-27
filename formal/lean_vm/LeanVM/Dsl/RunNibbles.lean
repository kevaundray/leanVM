/-
  LeanVM.Dsl.RunNibbles

  `selector_run_nibbles`' meaning theorem, stated and proved against its definition in the
  embedded language: B1's `selector_run_nibbles_SpecP`, with no template and no numbered value.
-/

module

public import LeanVM.Dsl.Logic
public import LeanVM.Dsl.Guest
public import LeanVM.Core.Value.Bits
public import LeanVM.Guest.B1.Selectors.InterfaceP

/-!
# `selector_run_nibbles`, against its definition

B1 (`Guest/B1/Selectors/RunNibbles.lean`) restates the function's core body as a template of
forty numbered atoms, checks `fn.body = template` by `decide +kernel` over the core data, and
destructures thirty-nine numbered hypotheses. Here the function is its Lean definition
(`Dsl.Guest.selectorRunNibbles`), and the proof composes the specifications of what it is made of:

* `spec_bitFactor`, `spec_gpowOfBits`: the product of the factors `1 + b·(g^(2^t) + 1)` of
  checked bits is `g` to their integer (`bitsNat`), for every list of bits, proved once;
* `spec_selectorRunNibbles`: the body, from the hint's six outputs checked Boolean to the
  assertion `q^4·r = len`;
* `selector_run_nibbles_sound`: B1's statement, `selector_run_nibbles_SpecP`, for any program that
  holds the elaborated function at its name.
-/

namespace LeanVM.Dsl.Guest

open LeanVM.Parameters LeanVM.Core LeanVM.Core.Value LeanVM.Dsl
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Bits and their g-power -/

/-- The integer of the bits `bs`, low first, a value counting as a set bit when it is `1`. -/
def bitsNat (σ : Val) : List (Var .bit) → Nat
  | [] => 0
  | b :: bs => (if σ b.v = 1 then 1 else 0) + 2 * bitsNat σ bs

theorem bitsNat_lt (σ : Val) : ∀ bs : List (Var .bit), bitsNat σ bs < 2 ^ bs.length
  | [] => by simp [bitsNat]
  | b :: bs => by
    have := bitsNat_lt σ bs
    simp only [bitsNat, List.length_cons, pow_succ]
    split <;> omega

theorem bitsNat_append (σ : Val) : ∀ xs ys : List (Var .bit),
    bitsNat σ (xs ++ ys) = bitsNat σ xs + 2 ^ xs.length * bitsNat σ ys
  | [], ys => by simp [bitsNat]
  | x :: xs, ys => by
    simp only [List.cons_append, bitsNat, bitsNat_append σ xs ys, List.length_cons, pow_succ]
    ring

/-- The factor of a checked bit `b` at weight `2^t`. -/
theorem factor_eq {b : E} (hb : b * b = b) (t : Nat) :
    1 + b * (gen ^ 2 ^ t + 1) = gen ^ (2 ^ t * (if b = 1 then 1 else 0)) := by
  by_cases h1 : b = 1
  · subst h1
    simp only [↓reduceIte, mul_one, one_mul]
    rw [add_comm (gen ^ 2 ^ t) 1, ← add_assoc, e_add_self, zero_add]
  · have h0 : b = 0 := by
      have hb' := bitE_of_mul_self hb
      rw [hb']
      simp [bitE, h1]
    simp only [h1, ↓reduceIte, mul_zero, pow_zero]
    rw [h0, zero_mul, add_zero]

theorem spec_bitFactor (b : Var .bit) (t : Nat) :
    Spec C rd (bitFactor b t) (fun r σ => σ r.v = 1 + σ b.v * (gen ^ 2 ^ t + 1)) :=
  Spec.mono (Spec.bind (spec_const _) fun _ => Spec.bind (spec_const _) fun _ =>
      Spec.bind (spec_mul _ _) fun _ => spec_add _ _)
    (by rintro r σ ⟨one, h1, c, hc, m, hm, hr⟩; rw [hr, hm, h1, hc])

theorem spec_bitsProdFrom : ∀ (acc : Word) (bs : List (Var .bit)) (t : Nat),
    Spec C rd (bitsProdFrom acc bs t) (fun r σ => (∀ b ∈ bs, σ b.v * σ b.v = σ b.v) →
      σ r.v = σ acc.v * gen ^ (2 ^ t * bitsNat σ bs))
  | acc, [], t => Spec.mono (Spec.pure _) (by rintro _ σ rfl -; simp [bitsNat])
  | acc, b :: bs, t => Spec.mono
      (Spec.bind (spec_bitFactor b t) fun _ => Spec.bind (spec_mul _ _) fun acc' =>
        spec_bitsProdFrom acc' bs (t + 1))
      (by
        rintro r σ ⟨f, hf, acc', ha, hr⟩ hb
        rw [hr (fun x hx => hb x (List.mem_cons_of_mem _ hx)), ha, hf,
          factor_eq (hb b List.mem_cons_self), bitsNat, mul_assoc, ← pow_add]
        congr 2
        rw [pow_succ]
        ring)

/-- **The g-power of checked bits**: `g` to their integer. -/
theorem spec_gpowOfBits : ∀ bs : List (Var .bit),
    Spec C rd (gpowOfBits bs) (fun r σ => (∀ b ∈ bs, σ b.v * σ b.v = σ b.v) →
      σ r.v = gen ^ bitsNat σ bs)
  | [] => Spec.mono (spec_const _) (by intro r σ h _; simp [bitsNat, h])
  | b :: bs => Spec.mono (Spec.bind (spec_bitFactor b 0) fun f => spec_bitsProdFrom f bs 1)
      (by
        rintro r σ ⟨f, hf, hr⟩ hb
        rw [hr (fun x hx => hb x (List.mem_cons_of_mem _ hx)), hf,
          factor_eq (hb b List.mem_cons_self), ← pow_add, bitsNat]
        congr 1
        ring)

/-! ## The function -/

/-- **`selector_run_nibbles`' body**: `len_g = g^n` for some `n < 64`, and it returns
`g^(n / 4)`. -/
theorem spec_selectorRunNibbles :
    Spec C rd (selectorRunNibbles.body (params 1)) (fun rs σ =>
      ∃ n < 64, σ (V.param 0) = gen ^ n ∧ rs.map (Ret.eval σ) = [gen ^ (n / 4)]) := by
  refine Spec.mono (Spec.bind (spec_hintBitsExp _ 6) fun nb =>
    Spec.bind (Spec.forM nb (P := fun h σ => σ h.v * σ h.v = σ h.v) fun h _ =>
      Spec.mono (Spec.bind (spec_assertBit h) fun _ => Spec.pure ())
        (by rintro _ σ ⟨_, ⟨-, hb⟩, -⟩; exact hb)) fun _ =>
    Spec.bind (spec_gpowOfBits _) fun _ => Spec.bind (spec_gpowOfBits _) fun _ =>
    Spec.bind (spec_mul _ _) fun _ => Spec.bind (spec_mul _ _) fun _ =>
    Spec.bind (spec_mul _ _) fun _ => Spec.bind (spec_assertEq _ _) fun _ => Spec.pure _) ?_
  rintro rs σ ⟨nb, hl, -, hbits, r, hr, q, hq, q2, hq2, q4, hq4, t, ht, -, he, rfl⟩
  -- The six hinted values, checked Boolean.
  set bs : List (Var .bit) := nb.map fun h => ⟨h.v⟩ with hbs
  have hb : ∀ b ∈ bs, σ b.v * σ b.v = σ b.v := by
    intro b hmem
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hmem
    exact hbits h hh
  have hlen : bs.length = 6 := by simp [hbs, hl]
  have hr' := hr fun b hmem => hb b (List.mem_of_mem_take hmem)
  have hq' := hq fun b hmem => hb b (List.mem_of_mem_drop hmem)
  -- `n = r + 4q`, `r < 4`.
  have hsplit := bitsNat_append σ (bs.take 2) (bs.drop 2)
  rw [List.take_append_drop, List.length_take, hlen] at hsplit
  have hrlt := bitsNat_lt σ (bs.take 2)
  have hnlt := bitsNat_lt σ bs
  rw [List.length_take, hlen] at hrlt
  rw [hlen] at hnlt
  have h26 : min 2 6 = 2 := rfl
  simp only [h26, Nat.reducePow] at hsplit hrlt
  refine ⟨bitsNat σ bs, by simpa using hnlt, ?_, ?_⟩
  · have he' : σ t.v = σ (V.param 0) := he
    rw [← he', ht, hq4, hq2, hq', hr', ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  · simp only [List.map_cons, List.map_nil, Ret.eval, hq', List.cons.injEq, and_true]
    congr 1
    omega

/-- The function's relation: `RunNibblesOut`. -/
theorem selectorRunNibbles_sem {args rets : List E}
    (h : selectorRunNibbles.core.Sem C rd args rets) :
    LeanVM.Guest.B1.Tables.RunNibblesOut args rets := by
  obtain ⟨σ, hp, rs, ⟨n, hn, hlen, hrs⟩, rfl⟩ := GFn.sem_of_spec spec_selectorRunNibbles h
  subst hp
  rw [hrs]
  exact ⟨n, hn, hlen, rfl⟩

/-- **`selector_run_nibbles` is sound** (B1's `selector_run_nibbles_SpecP`), in any program
holding the elaborated function at its name. -/
theorem selector_run_nibbles_sound {P : Program}
    (hf : P.find? "selector_run_nibbles" = some selectorRunNibbles.core) :
    LeanVM.Guest.B1.Tables.selector_run_nibbles_SpecP P :=
  fun _ _ _ h => GFn.rel_of_sem hf (fun _ _ _ hs => selectorRunNibbles_sem hs) h

end
end LeanVM.Dsl.Guest
