/-
  LeanVM.Dsl.Logic

  The program logic of the embedded guest language: what the statements a builder action emits
  say of any valuation that satisfies them, rule by rule, so that a guest function's theorem is
  proved against its Lean definition.
-/

module

public import LeanVM.Dsl.Builder
public import LeanVM.Core.Lemmas
public import LeanVM.Core.Value.FieldBits

/-!
# The program logic

`Spec C rd m Q`: from any state, the action `m` appends statements, and in any valuation where they
hold before a continuation `next`, `Q` holds of `m`'s result and so does `next`. The facts are about
the valuation of the statements emitted, never about what an honest prover would write: a value a
hint wrote has a fact only through a check the action emitted.

The rules: one per primitive (`spec_atom`, `spec_hint`, the state-only actions), and the structural
ones (`Spec.pure`, `Spec.bind`, `Spec.mono`, `Spec.forM`). A guest function's relation follows from
a `Spec` of its body (`GFn.sem_of_spec`), and a program's relation at its name from that
(`GFn.rel_of_sem`). Nothing is evaluated: a body is reasoned about for all states at once, so no
value is named by a number.
-/

namespace LeanVM.Dsl

open LeanVM.Parameters LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- `m` emits statements which, holding of `σ` before `next`, give `Q` of its result, and `next`. -/
def Spec {α : Type} (C : CallRel) (rd : Reader) (m : B α) (Q : α → Val → Prop) : Prop :=
  ∀ st : St, ∃ new : List Stmt, (m.run st).2.out.toList = st.out.toList ++ new ∧
    ∀ (σ : Val) (next : Prop) (kret : List E → Prop),
      Stmt.HoldsList C rd σ new next kret → Q (m.run st).1 σ ∧ next

theorem Spec.mono {α : Type} {m : B α} {Q Q' : α → Val → Prop} (h : Spec C rd m Q)
    (hq : ∀ a σ, Q a σ → Q' a σ) : Spec C rd m Q' := by
  intro st
  obtain ⟨new, hn, hk⟩ := h st
  exact ⟨new, hn, fun σ next kret hh => ⟨hq _ _ (hk σ next kret hh).1, (hk σ next kret hh).2⟩⟩

theorem Spec.pure {α : Type} (a : α) : Spec C rd (Pure.pure a : B α) (fun b _ => b = a) :=
  fun st => ⟨[], by simp [StateT.run, Pure.pure, StateT.pure], fun _ _ _ h => ⟨rfl, h⟩⟩

theorem Spec.bind {α β : Type} {m : B α} {f : α → B β} {Q : α → Val → Prop}
    {R : α → β → Val → Prop} (hm : Spec C rd m Q) (hf : ∀ a, Spec C rd (f a) (R a)) :
    Spec C rd (m >>= f) (fun b σ => ∃ a, Q a σ ∧ R a b σ) := by
  intro st
  obtain ⟨n1, h1, k1⟩ := hm st
  obtain ⟨n2, h2, k2⟩ := hf (m.run st).1 (m.run st).2
  refine ⟨n1 ++ n2, ?_, fun σ next kret h => ?_⟩
  · change ((f (m.run st).1).run (m.run st).2).2.out.toList = _
    rw [h2, h1, List.append_assoc]
  · rw [holdsList_append] at h
    obtain ⟨hq, h⟩ := k1 σ _ kret h
    obtain ⟨hr, hn⟩ := k2 σ next kret h
    exact ⟨⟨_, hq, hr⟩, hn⟩

/-- An action that emits nothing. -/
theorem Spec.silent {α : Type} {m : B α} (h : ∀ st, (m.run st).2.out = st.out) :
    Spec C rd m (fun _ _ => True) :=
  fun st => ⟨[], by rw [h, List.append_nil], fun _ _ _ hh => ⟨trivial, hh⟩⟩

theorem spec_fresh (k : Compiler.Kind) : Spec C rd (B.fresh k) (fun _ _ => True) :=
  Spec.silent fun _ => rfl

theorem spec_freshRun (n : Nat) (k : Compiler.Kind) :
    Spec C rd (B.freshRun n k) (fun r _ => r.length = n) := fun st =>
  ⟨[], by rw [List.append_nil]; rfl, fun _ _ _ h => ⟨by
    change ((List.range n).map fun i => (⟨[], st.tag, i⟩ : V)).length = n
    simp, h⟩⟩

theorem spec_atom (a : Atom) : Spec C rd (B.atom a) (fun _ σ => a.Holds rd σ) := fun st =>
  ⟨[.atom a], by change (st.out.push (.atom a)).toList = _; simp,
    fun σ next kret h => by simpa [Stmt.HoldsList, Stmt.Holds] using h⟩

theorem spec_hint (h : Hint) : Spec C rd (B.hint h) (fun _ _ => True) := fun st =>
  ⟨[.atom (.hint h)], by change (st.out.push (.atom (.hint h))).toList = _; simp,
    fun σ next kret hh => by simpa [Stmt.HoldsList, Stmt.Holds, Atom.Holds] using hh⟩

theorem Spec.forM {γ : Type} (xs : List γ) {f : γ → B PUnit} {P : γ → Val → Prop}
    (h : ∀ x ∈ xs, Spec C rd (f x) (fun _ σ => P x σ)) :
    Spec C rd (xs.forM f) (fun _ σ => ∀ x ∈ xs, P x σ) := by
  induction xs with
  | nil => exact Spec.mono (Spec.pure _) (by simp)
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have hxs := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine Spec.mono (Spec.bind hx fun _ => hxs) ?_
    rintro _ σ ⟨_, h1, h2⟩
    simpa using ⟨h1, h2⟩

/-! ## The primitives -/

theorem spec_const (c : E) : Spec C rd (B.const c) (fun r σ => σ r.v = c) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨o, -, _, h, rfl⟩; exact h)

theorem spec_gconst (e : Nat) : Spec C rd (B.gconst e) (fun r σ => σ r.v = gen ^ e) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨o, -, _, h, rfl⟩; exact h)

theorem spec_add {σ' τ : Ty} (a : Var σ') (b : Var τ) :
    Spec C rd (B.add a b) (fun r σ => σ r.v = σ a.v + σ b.v) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨o, -, _, h, rfl⟩; exact h)

theorem spec_mul {σ' τ : Ty} (a : Var σ') (b : Var τ) :
    Spec C rd (B.mul a b) (fun r σ => σ r.v = σ a.v * σ b.v) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨o, -, _, h, rfl⟩; exact h)

theorem spec_addCell {σ' τ : Ty} (a : Var σ') (b : Var τ) :
    Spec C rd (B.addCell a b) (fun r σ => σ r.v = σ a.v + σ b.v) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨o, -, _, h, rfl⟩; exact h)

theorem spec_mulInto {ρ σ' τ : Ty} (d : Var ρ) (a : Var σ') (b : Var τ) :
    Spec C rd (B.mulInto d a b) (fun _ σ => σ d.v = σ a.v * σ b.v) := spec_atom _

theorem spec_assertEq {σ' τ : Ty} (a : Var σ') (b : Var τ) :
    Spec C rd (B.assertEq a b) (fun _ σ => σ a.v = σ b.v) :=
  Spec.mono (spec_atom _) fun _ _ h => e_add_eq_zero_iff.mp h

/-- A checked bit: the hinted value is `0` or `1` in every valuation of the check. -/
theorem spec_assertBit (h : Hinted) :
    Spec C rd (B.assertBit h) (fun r σ => r.v = h.v ∧ σ h.v * σ h.v = σ h.v) :=
  Spec.mono (Spec.bind (spec_atom _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨_, hm, rfl⟩; exact ⟨rfl, hm.symm⟩)

theorem spec_hintBitsExp {τ : Ty} (x : Var τ) (n : Nat) :
    Spec C rd (B.hintBitsExp x n) (fun hs _ => hs.length = n) :=
  Spec.mono (Spec.bind (spec_freshRun _ _) fun _ => Spec.bind (spec_hint _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨r, hr, _, -, rfl⟩; simpa using hr)

theorem spec_retInto : ∀ (rs : List V) (vs : List Ret),
    Spec C rd (B.retInto rs vs) (fun _ σ => rs.length = vs.length → rs.map σ = vs.map (Ret.eval σ))
  | [], [] => Spec.mono (Spec.pure _) (by simp)
  | r :: rs, .v x :: xs => Spec.mono (Spec.bind (spec_atom _) fun _ => spec_retInto rs xs)
      (by
        rintro _ σ ⟨_, h1, h2⟩ hl
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [List.map_cons, Ret.eval, h2 hl, List.cons.injEq, and_true]
        exact h1)
  | r :: rs, .c e :: xs => Spec.mono (Spec.bind (spec_atom _) fun _ => spec_retInto rs xs)
      (by
        rintro _ σ ⟨_, h1, h2⟩ hl
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [List.map_cons, Ret.eval, h2 hl, List.cons.injEq, and_true]
        exact h1)
  | [], _ :: _ => Spec.mono (Spec.pure _) (by simp)
  | _ :: _, [] => Spec.mono (Spec.pure _) (by simp)

theorem spec_retArea (vs : List Ret) :
    Spec C rd (B.retArea vs) (fun rs σ => rs.map σ = vs.map (Ret.eval σ)) :=
  Spec.mono (Spec.bind (spec_freshRun _ _) fun rs => Spec.bind (spec_retInto rs vs) fun _ =>
      Spec.pure rs)
    (by rintro _ σ ⟨rs, hl, _, h, rfl⟩; exact h hl)

/-! ## Functions and programs -/

/-- **A function's relation from its body's specification**: the valuation that satisfies the
function's statements takes the parameters to the arguments, satisfies `Q` of the returned
values, and returns their words. -/
theorem GFn.sem_of_spec {f : GFn} {Q : List Ret → Val → Prop}
    (h : Spec C rd (f.body (params f.arity)) Q) {args rets : List E}
    (hs : f.core.Sem C rd args rets) :
    ∃ σ : Val, (params f.arity).map σ = args ∧ ∃ rs, Q rs σ ∧ rets = rs.map (Ret.eval σ) := by
  obtain ⟨σ, hp, hb⟩ := hs
  have hm := Spec.bind h fun rs => Spec.bind (spec_retArea (C := C) (rd := rd) rs)
    fun area => Spec.pure (rs, area)
  obtain ⟨new, hn, hk⟩ := hm { name := f.name }
  simp only [List.nil_append] at hn
  change Stmt.HoldsList C rd σ (f.run.2.out.toList ++ [.ret f.run.1.2]) False _ at hb
  rw [holdsList_append] at hb
  change Stmt.HoldsList C rd σ (f.run.2.out.toList) _ _ at hb
  rw [show f.run.2.out.toList = new from hn] at hb
  obtain ⟨⟨rs, hq, area, ha, hr⟩, hret⟩ := hk σ _ _ hb
  refine ⟨σ, hp, rs, hq, ?_⟩
  simp only [Stmt.HoldsList, Stmt.Holds] at hret
  change f.run.1.2.map σ = rets at hret
  have : f.run.1 = (rs, area) := hr
  rw [this] at hret
  rw [← hret, ha]

/-- **A program's relation at a guest function's name** is the function's. -/
theorem GFn.rel_of_sem {P : Program} {f : GFn} (hf : P.find? f.name = some f.core)
    {R : List E → List E → Prop} (h : ∀ C args rets, f.core.Sem C rd args rets → R args rets)
    {args rets : List E} (hr : P.Rel rd f.name args rets) : R args rets := by
  obtain ⟨n, hn⟩ := hr
  cases n with
  | zero => exact hn.elim
  | succ n =>
    obtain ⟨fn, hfind, hsem⟩ := hn
    rw [hf] at hfind
    cases hfind
    exact h _ _ _ hsem

end
end LeanVM.Dsl
