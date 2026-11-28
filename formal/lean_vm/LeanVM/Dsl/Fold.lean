/-
  LeanVM.Dsl.Fold

  Constant folding in the builder: a scalar the builder knows while elaborating (a field constant) or a value, and field expressions whose constants fold and whose identities (`x + 0`, `x * 1`) vanish before anything is emitted.
-/

module

public import LeanVM.Dsl.Logic
public import LeanVM.Dsl.Keccak

/-!
# Constant folding

A guest computes with values (`Word`) and with field constants it knows while elaborating (`E`): indices, loop counters and `Const` arguments make many operands constants, and which ones depends on the arguments. The builder folds them, so an author writes the arithmetic once for every argument:

* `FW`: a scalar that is a constant (`.c`) or a value (`.w`). `FW.val` materializes it (a constant is one `SET`), `FW.msg` gives it as a Keccak message cell (a zero is the padding run's).
* `Ex`: a field expression over constants (`.c`; `.g k` is `g^k`), values (`.w`; a frame cell `.v`), pointers (`.sh p k` is `p · g^k`) and actions (`.act`, a heap read `.ld`), built with `.add`, `.mul`, `.pow`. `Ex.lower` gives its value, `Ex.into d` writes it into the cell `d`, `Ex.bind` gives it as an `FW`. All three fold: a constant subexpression is computed by Lean, a sum with a constant `0` or a product with a constant `1` is its other operand, and nothing else is rewritten, except that a product of one `.w` value and `g`-powers is that pointer (`B.shifted`); the operands' instructions are emitted left to right, each constant set where its operand is lowered (the order the zkDSL's lowering and the zkDSL's lowering use).

So `acc := ← (acc.ex.add t.ex).bind` in a loop from `acc := .c 0` emits nothing at the first iteration (the sum is `t`) and one `XOR` at each later one. The lemmas (`spec_val`, `spec_lower`, `spec_into`, `spec_bind`) state the value each one gives for expressions without actions (`Ex.Pure`), by cases on the fold: what is emitted differs, the value does not.
-/

namespace LeanVM.Dsl

open LeanVM.Parameters LeanVM.Core

@[expose] public section

/-- A scalar while elaborating: a field constant the builder knows, or a value. -/
inductive FW where
  | c (e : E)
  | w (x : Word)
  deriving Inhabited

/-- A field expression, lowered with its constants folded (`Ex.lower`, `Ex.into`, `Ex.bind`). -/
inductive Ex where
  /-- A constant. -/
  | c (e : E)
  /-- A value, which a product with `g`-powers shifts as a pointer. -/
  | w (x : Word)
  /-- A value no product shifts as a pointer: a frame cell, which the zkDSL reads as no address (`g · cell` is a product, its operands in order). -/
  | v (x : Word)
  /-- The constant `g^k`, which also shifts a pointer: `p · g^k` is the pointer `B.shifted p k`. -/
  | g (k : Nat)
  /-- The pointer `p · g^k` (`B.shifted`). -/
  | sh (p : Word) (k : Nat)
  /-- A value an action computes when the expression is lowered there. -/
  | act (m : B Word)
  /-- The word at `p·g^off`, `p` computed when the expression is lowered there. -/
  | ld (p : B Word) (off : Nat)
  | add (a b : Ex)
  | mul (a b : Ex)
  /-- `a ^ k` by square-and-multiply. -/
  | pow (a : Ex) (k : Nat)

namespace FW

/-- Its value in a valuation. -/
def eval (σ : Val) : FW → E
  | .c e => e
  | .w x => σ x.v

/-- As a value: a constant is set (`B.const`). -/
def val : FW → B Word
  | .c e => B.const e
  | .w x => pure x

/-- As an expression. -/
def ex : FW → Ex
  | .c e => .c e
  | .w x => .w x

/-- As a Keccak message cell: a constant `0` is the padding run's zero, another constant is set. -/
def msg : FW → B Msg
  | .c e => if e == 0 then pure .zero else do return .cell (← B.const e).v
  | .w x => pure (.cell x.v)

theorem spec_val {C : CallRel} {rd : Reader} (x : FW) :
    Spec C rd x.val (fun r σ => σ r.v = x.eval σ) := by
  cases x with
  | c e => exact spec_const e
  | w x => exact Spec.mono (Spec.pure x) (by rintro _ σ rfl; rfl)

end FW

namespace Ex

/-- Its value as a constant, when every leaf is one. -/
def const? : Ex → Option E
  | .c e => some e
  | .g k => some (gpowE k)
  | .add a b => match a.const?, b.const? with
    | some x, some y => some (x + y)
    | _, _ => none
  | .mul a b => match a.const?, b.const? with
    | some x, some y => some (x * y)
    | _, _ => none
  | .pow a k => a.const?.map (fieldPow · k)
  | _ => none

/-- A compile-time integer as the guest reads it in field arithmetic: its word, and when it is a power of two below `2^64` (the word `2^k` is `g^k`) also the `g`-power that shifts a pointer. -/
def nat (n : Nat) : Ex :=
  if n != 0 && n < 2 ^ 64 && n &&& (n - 1) == 0 then .g (Nat.log2 n) else .c (litField n)

/-- The exponent of a product of `.g`s. -/
def gexp? : Ex → Option Nat
  | .g k => some k
  | .mul a b => match a.gexp?, b.gexp? with
    | some i, some j => some (i + j)
    | _, _ => none
  | _ => none

/-- The pointer a product of one value (or pointer) and `.g`s is. -/
def base? : Ex → Option (Word × Nat)
  | .w x => some (x, 0)
  | .sh p k => some (p, k)
  | .mul a b => match a.base?, b.gexp? with
    | some (p, k), some j => some (p, k + j)
    | _, _ => match a.gexp?, b.base? with
      | some j, some (p, k) => some (p, j + k)
      | _, _ => none
  | _ => none

/-- A factor's value beside a constant factor: a value `.w x` is read as the zkDSL's lowering reads a name, its `use` event recorded (`B.use`); any other factor is lowered. -/
def factor (e other : Ex) (lowered : B Word) : B Word :=
  match e with
  | .w x => if other.const?.isSome then B.use x else lowered
  | _ => lowered

/-- Its value: a constant is set; `0 + b` is `b`, `1 · b` is `b`; otherwise the operands left to right, then the operation; a product of a value and `.g`s is that pointer. -/
def lower (e : Ex) : B Word :=
  match e.const? with
  | some k => B.const k
  | none =>
    match e with
    | .c k => B.const k
    | .w x => pure x
    | .v x => pure x
    | .g k => B.const (gpowE k)
    | .sh p k => B.shifted p k
    | .act m => m
    | .ld p off => do B.load (← p) off
    | .add a b =>
        if a.const? == some 0 then b.lower
        else if b.const? == some 0 then a.lower
        else do B.add (← a.lower) (← b.lower)
    | .mul a b =>
        if a.const? == some 1 then b.lower
        else if b.const? == some 1 then a.lower
        else match (Ex.mul a b).base? with
          | some (p, k) => B.shifted p k
          | none => do B.mul (← factor a b a.lower) (← factor b a b.lower)
    | .pow a k =>
        if k = 0 then do
          let _ ← a.lower
          B.const 1
        else do B.pow (← a.lower) k

/-- Written into the cell `d`: a constant `SET`, a heap read a `DEREF` into `d`, a sum or product of two operands the operation into `d`, anything else a copy. -/
def into {ρ : Ty} (d : Var ρ) (e : Ex) : B Unit :=
  match e.const? with
  | some k => B.constInto d k
  | none =>
    match e with
    | .ld p off => do B.loadInto d (← p) off
    | .add a b =>
        if a.const? == some 0 then b.into d
        else if b.const? == some 0 then a.into d
        else do B.addInto d (← a.lower) (← b.lower)
    | .mul a b =>
        if a.const? == some 1 then b.into d
        else if b.const? == some 1 then a.into d
        else do B.mulInto d (← factor a b a.lower) (← factor b a b.lower)
    | e => do B.copy d (← e.lower)

/-- As an `FW`: a constant stays one, emitting nothing; anything else is lowered. -/
def bind (e : Ex) : B FW :=
  match e.const? with
  | some k => pure (.c k)
  | none => do return .w (← e.lower)

/-- As a returned value: written into its return cell (`into`), in order with the others. -/
def ret (e : Ex) : Ret := .into fun r => e.into (⟨r⟩ : Word)

/-- No action inside: the expressions the lemmas describe. -/
def Pure : Ex → Bool
  | .c _ | .w _ | .v _ => true
  | .add a b | .mul a b => a.Pure && b.Pure
  | _ => false

/-- Its value in a valuation. -/
def eval (σ : Val) : Ex → E
  | .c e => e
  | .w x => σ x.v
  | .v x => σ x.v
  | .add a b => a.eval σ + b.eval σ
  | .mul a b => a.eval σ * b.eval σ
  | .pow a k => fieldPow (a.eval σ) k
  | .g k => gpowE k
  | _ => 0

theorem const?_eval {e : Ex} {k : E} (h : e.const? = some k) (σ : Val) : e.eval σ = k := by
  induction e generalizing k with
  | c _ => simpa [const?, eval] using h
  | add a b iha ihb =>
      simp only [const?] at h
      split at h
      · rename_i x y ha hb
        cases h
        simp [eval, iha ha, ihb hb]
      · cases h
  | mul a b iha ihb =>
      simp only [const?] at h
      split at h
      · rename_i x y ha hb
        cases h
        simp [eval, iha ha, ihb hb]
      · cases h
  | pow a n iha =>
      simp only [const?, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp [eval, iha hx]
  | g _ => simpa [const?, eval] using h
  | w _ => simp [const?] at h
  | v _ => simp [const?] at h
  | sh _ _ => simp [const?] at h
  | act _ => simp [const?] at h
  | ld _ _ => simp [const?] at h

theorem spec_use {C : CallRel} {rd : Reader} {τ : Ty} (x : Var τ) :
    Spec C rd (B.use x) (fun r _ => r = x) := by
  unfold B.use
  refine Spec.mono (Spec.bind (Spec.silent fun st => ?_) fun _ => Spec.pure x)
    fun r σ ⟨_, _, h⟩ => h
  by_cases hf : st.faithful = true <;>
    simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, hf] <;> rfl

/-- A factor's value is its lowering's, its `use` event aside. -/
theorem spec_factor {C : CallRel} {rd : Reader} {e : Ex} (o : Ex) {m : B Word}
    {Q : Word → Val → Prop} (h : Spec C rd m Q) (hw : ∀ x, e = .w x → ∀ σ, Q x σ) :
    Spec C rd (factor e o m) Q := by
  cases e with
  | w x =>
      simp only [factor]
      split
      · exact Spec.mono (spec_use x) fun r σ hr => hr ▸ hw x rfl σ
      · exact h
  | _ => exact h

theorem gexp?_pure {e : Ex} (hp : e.Pure = true) : e.gexp? = none := by
  induction e with
  | mul a b iha _ =>
      simp only [Pure, Bool.and_eq_true] at hp
      simp [gexp?, iha hp.1]
  | _ => simp_all [Pure, gexp?]

theorem base?_mul_pure {a b : Ex} (ha : a.Pure = true) (hb : b.Pure = true) :
    (Ex.mul a b).base? = none := by
  rcases h : a.base? with _ | ⟨p, k⟩ <;>
    rcases h' : b.base? with _ | ⟨q, j⟩ <;> simp [base?, h, h', gexp?_pure ha, gexp?_pure hb]

theorem spec_lower {C : CallRel} {rd : Reader} (e : Ex) (hp : e.Pure = true) :
    Spec C rd e.lower (fun r σ => σ r.v = e.eval σ) := by
  induction e with
  | c k => exact Spec.mono (spec_const k) fun _ _ h => h
  | w x => exact Spec.mono (Spec.pure x) (by rintro _ σ rfl; rfl)
  | v x => exact Spec.mono (Spec.pure x) (by rintro _ σ rfl; rfl)
  | g _ => simp [Pure] at hp
  | sh _ _ => simp [Pure] at hp
  | act _ => simp [Pure] at hp
  | ld _ _ => simp [Pure] at hp
  | pow _ _ _ => simp [Pure] at hp
  | add a b iha ihb =>
      simp only [Pure, Bool.and_eq_true] at hp
      unfold lower
      split
      · rename_i k hk
        exact Spec.mono (spec_const k) fun r σ h => h.trans (const?_eval hk σ).symm
      · dsimp only
        split
        · rename_i h0
          refine Spec.mono (ihb hp.2) fun r σ h => ?_
          rw [h]; simp only [eval]; rw [const?_eval (eq_of_beq h0) σ, zero_add]
        · split
          · rename_i _ h0
            refine Spec.mono (iha hp.1) fun r σ h => ?_
            rw [h]; simp only [eval]; rw [const?_eval (eq_of_beq h0) σ, add_zero]
          · refine Spec.mono (Spec.bind (iha hp.1) fun x =>
              Spec.bind (ihb hp.2) fun y => spec_add x y) ?_
            rintro r σ ⟨x, hx, y, hy, h⟩
            rw [h, hx, hy]; simp only [eval]
  | mul a b iha ihb =>
      simp only [Pure, Bool.and_eq_true] at hp
      unfold lower
      split
      · rename_i k hk
        exact Spec.mono (spec_const k) fun r σ h => h.trans (const?_eval hk σ).symm
      · dsimp only
        split
        · rename_i h1
          refine Spec.mono (ihb hp.2) fun r σ h => ?_
          rw [h]; simp only [eval]; rw [const?_eval (eq_of_beq h1) σ, one_mul]
        · split
          · rename_i _ h1
            refine Spec.mono (iha hp.1) fun r σ h => ?_
            rw [h]; simp only [eval]; rw [const?_eval (eq_of_beq h1) σ, mul_one]
          · rw [base?_mul_pure hp.1 hp.2]
            refine Spec.mono (Spec.bind (spec_factor b (iha hp.1) fun x hx σ => by subst hx; rfl)
              fun x => Spec.bind (spec_factor a (ihb hp.2) fun y hy σ => by subst hy; rfl)
                fun y => spec_mul x y) ?_
            rintro r σ ⟨x, hx, y, hy, h⟩
            rw [h, hx, hy]; simp only [eval]

theorem spec_into {C : CallRel} {rd : Reader} {ρ : Ty} (d : Var ρ) (e : Ex) (hp : e.Pure = true) :
    Spec C rd (e.into d) (fun _ σ => σ d.v = e.eval σ) := by
  induction e with
  | c k => exact Spec.mono (spec_constInto d k) fun _ _ h => h
  | w x =>
      refine Spec.mono (Spec.bind (spec_lower (.w x) rfl) fun y => spec_copy d y) ?_
      rintro _ σ ⟨y, hy, h⟩
      rw [h, hy]
  | v x =>
      refine Spec.mono (Spec.bind (spec_lower (.v x) rfl) fun y => spec_copy d y) ?_
      rintro _ σ ⟨y, hy, h⟩
      rw [h, hy]
  | g _ => simp [Pure] at hp
  | sh _ _ => simp [Pure] at hp
  | act _ => simp [Pure] at hp
  | ld _ _ => simp [Pure] at hp
  | pow _ _ _ => simp [Pure] at hp
  | add a b iha ihb =>
      simp only [Pure, Bool.and_eq_true] at hp
      unfold into
      split
      · rename_i k hk
        exact Spec.mono (spec_constInto d k) fun _ σ h => h.trans (const?_eval hk σ).symm
      · dsimp only
        split
        · rename_i h0
          refine Spec.mono (ihb hp.2) fun _ σ h => ?_
          rw [h]; simp only [eval]; rw [const?_eval (eq_of_beq h0) σ, zero_add]
        · split
          · rename_i _ h0
            refine Spec.mono (iha hp.1) fun _ σ h => ?_
            rw [h]; simp only [eval]; rw [const?_eval (eq_of_beq h0) σ, add_zero]
          · refine Spec.mono (Spec.bind (spec_lower a hp.1) fun x =>
              Spec.bind (spec_lower b hp.2) fun y => spec_addInto d x y) ?_
            rintro _ σ ⟨x, hx, y, hy, h⟩
            rw [h, hx, hy]; simp only [eval]
  | mul a b iha ihb =>
      simp only [Pure, Bool.and_eq_true] at hp
      unfold into
      split
      · rename_i k hk
        exact Spec.mono (spec_constInto d k) fun _ σ h => h.trans (const?_eval hk σ).symm
      · dsimp only
        split
        · rename_i h1
          refine Spec.mono (ihb hp.2) fun _ σ h => ?_
          rw [h]; simp only [eval]; rw [const?_eval (eq_of_beq h1) σ, one_mul]
        · split
          · rename_i _ h1
            refine Spec.mono (iha hp.1) fun _ σ h => ?_
            rw [h]; simp only [eval]; rw [const?_eval (eq_of_beq h1) σ, mul_one]
          · refine Spec.mono (Spec.bind (spec_factor b (spec_lower a hp.1) fun x hx σ => by subst hx; rfl)
              fun x => Spec.bind (spec_factor a (spec_lower b hp.2) fun y hy σ => by subst hy; rfl)
                fun y => spec_mulInto d x y) ?_
            rintro _ σ ⟨x, hx, y, hy, h⟩
            rw [h, hx, hy]; simp only [eval]

theorem spec_bind {C : CallRel} {rd : Reader} (e : Ex) (hp : e.Pure = true) :
    Spec C rd e.bind (fun r σ => r.eval σ = e.eval σ) := by
  unfold bind
  split
  · rename_i k hk
    exact Spec.mono (Spec.pure _) (by rintro _ σ rfl; exact (const?_eval hk σ).symm)
  · refine Spec.mono (Spec.bind (spec_lower e hp) fun x => Spec.pure (FW.w x)) ?_
    rintro _ σ ⟨x, hx, rfl⟩
    exact hx

end Ex

end
end LeanVM.Dsl
