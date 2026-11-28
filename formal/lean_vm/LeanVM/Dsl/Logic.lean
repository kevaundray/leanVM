/-
  LeanVM.Dsl.Logic

  The program logic of the embedded guest language: what the statements a builder action emits
  say of any valuation that satisfies them, rule by rule, so that a guest function's theorem is
  proved against its Lean definition.
-/

module

public import LeanVM.Dsl.Mem
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

theorem spec_poolConst (c : E) : Spec C rd (B.poolConst c) (fun _ _ => True) :=
  Spec.silent fun st => by
    show (if st.consts.contains c then st else { st with consts := c :: st.consts }).out = st.out
    split <;> rfl

theorem spec_const (c : E) : Spec C rd (B.const c) (fun r σ => σ r.v = c) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ =>
      Spec.bind (spec_poolConst _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨o, -, _, h, _, -, rfl⟩; exact h)

theorem spec_gconst (e : Nat) : Spec C rd (B.gconst e) (fun r σ => σ r.v = gen ^ e) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ =>
      Spec.bind (spec_poolConst _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨o, -, _, h, _, -, rfl⟩; exact h)

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

theorem spec_retInto : ∀ (rs : List V) (vs : List Ret), vs.all Ret.isPure = true →
    Spec C rd (B.retInto rs vs)
      (fun _ σ => rs.length = vs.length → rs.map σ = vs.map (Ret.eval rd σ))
  | [], [], _ => Spec.mono (Spec.pure _) (by simp)
  | r :: rs, .v x :: xs, hp => Spec.mono
      (Spec.bind (spec_atom _) fun _ => spec_retInto rs xs (by simpa [Ret.isPure] using hp))
      (by
        rintro _ σ ⟨_, h1, h2⟩ hl
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [List.map_cons, Ret.eval, h2 hl, List.cons.injEq, and_true]
        exact h1)
  | r :: rs, .c e :: xs, hp => Spec.mono
      (Spec.bind (spec_atom _) fun _ => spec_retInto rs xs (by simpa [Ret.isPure] using hp))
      (by
        rintro _ σ ⟨_, h1, h2⟩ hl
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [List.map_cons, Ret.eval, h2 hl, List.cons.injEq, and_true]
        exact h1)
  | r :: rs, .add a b :: xs, hp => Spec.mono
      (Spec.bind (spec_atom _) fun _ => spec_retInto rs xs (by simpa [Ret.isPure] using hp))
      (by
        rintro _ σ ⟨_, h1, h2⟩ hl
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [List.map_cons, Ret.eval, h2 hl, List.cons.injEq, and_true]
        exact h1)
  | r :: rs, .mul a b :: xs, hp => Spec.mono
      (Spec.bind (spec_atom _) fun _ => spec_retInto rs xs (by simpa [Ret.isPure] using hp))
      (by
        rintro _ σ ⟨_, h1, h2⟩ hl
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [List.map_cons, Ret.eval, h2 hl, List.cons.injEq, and_true]
        exact h1)
  | r :: rs, .load p off :: xs, hp => Spec.mono
      (Spec.bind (spec_atom _) fun _ => spec_retInto rs xs (by simpa [Ret.isPure] using hp))
      (by
        rintro _ σ ⟨_, h1, h2⟩ hl
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [List.map_cons, Ret.eval, h2 hl, List.cons.injEq, and_true]
        obtain ⟨-, h3⟩ : LoadHolds rd (σ p) off (σ r) := h1
        rw [h3]
        rfl)
  | _ :: _, .into _ :: _, hp => by simp [Ret.isPure] at hp
  | [], _ :: _, _ => Spec.mono (Spec.pure _) (by simp)
  | _ :: _, [], _ => Spec.mono (Spec.pure _) (by simp)

theorem spec_retArea (vs : List Ret) (hp : vs.all Ret.isPure = true) :
    Spec C rd (B.retArea vs) (fun rs σ => rs.map σ = vs.map (Ret.eval rd σ)) :=
  Spec.mono (Spec.bind (spec_freshRun _ _) fun rs => Spec.bind (spec_retInto rs vs hp) fun _ =>
      Spec.pure rs)
    (by rintro _ σ ⟨rs, hl, _, h, rfl⟩; exact h hl)

/-! ## Functions and programs -/

/-- **A function's relation from its body's specification**: the valuation that satisfies the
function's statements takes the parameters to the arguments, satisfies `Q` of the returned
values, and returns their words; its returns are ones the logic reads (no `Ret.into`). -/
theorem GFn.sem_of_spec {f : GFn} {Q : List Ret → Val → Prop}
    (h : Spec C rd (f.body (params f.arity)) Q) {args rets : List E}
    (hs : f.core.Sem C rd args rets) (hw : f.run.1.1.all Ret.isPure = true := by decide +kernel) :
    ∃ σ : Val, (params f.arity).map σ = args ∧ ∃ rs, Q rs σ ∧ rets = rs.map (Ret.eval rd σ) := by
  obtain ⟨σ, hp, hb⟩ := hs
  let st0 : St := { name := f.name, faithful := f.faithful }
  obtain ⟨n1, h1, k1⟩ := h st0
  obtain ⟨n2, h2, k2⟩ := spec_retArea (C := C) (rd := rd) _ hw ((f.body (params f.arity)).run st0).2
  change Stmt.HoldsList C rd σ (f.run.2.out.toList ++ [.ret f.run.1.2]) False _ at hb
  have hout : f.run.2.out.toList = n1 ++ n2 := by
    refine h2.trans ?_
    rw [h1]
    rfl
  rw [hout, holdsList_append, holdsList_append] at hb
  obtain ⟨hq, hb⟩ := k1 σ _ _ hb
  obtain ⟨ha, hret⟩ := k2 σ _ _ hb
  refine ⟨σ, hp, _, hq, ?_⟩
  simp only [Stmt.HoldsList, Stmt.Holds] at hret
  exact hret.symm.trans ha

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

/-! ## Writes into cells, division, memory, calls -/

theorem spec_constInto {ρ : Ty} (d : Var ρ) (c : E) :
    Spec C rd (B.constInto d c) (fun _ σ => σ d.v = c) := spec_atom _

theorem spec_addInto {ρ σ' τ : Ty} (d : Var ρ) (a : Var σ') (b : Var τ) :
    Spec C rd (B.addInto d a b) (fun _ σ => σ d.v = σ a.v + σ b.v) := spec_atom _

theorem spec_copy {ρ σ' : Ty} (d : Var ρ) (s : Var σ') :
    Spec C rd (B.copy d s) (fun _ σ => σ d.v = σ s.v) := spec_atom _

theorem spec_fdiv {σ' τ : Ty} (a : Var σ') (b : Var τ) :
    Spec C rd (B.fdiv a b) (fun q σ => σ a.v = σ q.v * σ b.v) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨o, -, _, h, rfl⟩; exact h)

theorem spec_load {τ : Ty} (p : Var τ) (off : Nat) :
    Spec C rd (B.load p off) (fun r σ => LoadHolds rd (σ p.v) off (σ r.v)) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨o, -, _, h, rfl⟩; exact h)

theorem spec_store {σ' τ : Ty} (p : Var σ') (off : Nat) (v : Var τ) :
    Spec C rd (B.store p off v) (fun _ σ => LoadHolds rd (σ p.v) off (σ v.v)) := spec_atom _

theorem spec_loadInto {ρ σ' : Ty} (d : Var ρ) (p : Var σ') (off : Nat) :
    Spec C rd (B.loadInto d p off) (fun _ σ => LoadHolds rd (σ p.v) off (σ d.v)) := spec_atom _

theorem spec_emitCall (f : String) (args rets : List V) :
    Spec C rd (B.emit (.call f args rets)) (fun _ σ => C f (args.map σ) (rets.map σ)) := fun st =>
  ⟨[.call f args rets], by change (st.out.push _).toList = _; simp,
    fun σ next kret h => by simpa [Stmt.HoldsList, Stmt.Holds] using h⟩

theorem spec_callInto (f : String) (args dsts : List V) :
    Spec C rd (B.callInto f args dsts) (fun _ σ => C f (args.map σ) (dsts.map σ)) :=
  spec_emitCall _ _ _

theorem out_mapM_fresh (k : Compiler.Kind) : ∀ (l : List Nat) (st : St),
    ((l.mapM fun _ => B.fresh k).run st).2.out = st.out
  | [], _ => rfl
  | _ :: l, st => by
    rw [List.mapM_cons]
    exact (out_mapM_fresh k l ((B.fresh k).run st).2).trans rfl

theorem spec_call (f : String) (args : List V) (nrets : Nat) :
    Spec C rd (B.call f args nrets) (fun rs σ => C f (args.map σ) (rs.map fun r => σ r.v)) :=
  Spec.mono (Spec.bind (Spec.silent (out_mapM_fresh .cell _)) fun rets =>
      Spec.bind (spec_emitCall f args rets) fun _ => Spec.pure _)
    (by rintro _ σ ⟨rets, -, _, h, rfl⟩; simpa [List.map_map, Function.comp_def] using h)

theorem spec_emitDispatch (x : V) (fs : List String) (args rets : List V) :
    Spec C rd (B.emit (.dispatch x fs args rets)) (fun _ σ => ∃ (j : Nat) (h : j < fs.length),
      σ x = ofK (addressOfIndex j) ∧ C fs[j] (args.map σ) (rets.map σ)) := fun st =>
  ⟨[.dispatch x fs args rets], by change (st.out.push _).toList = _; simp,
    fun σ next kret h => by simpa [Stmt.HoldsList, Stmt.Holds] using h⟩

/-- A fused `match` of calls: some arm `j` below the arm count, at `x = g^j`, holds. -/
theorem spec_dispatch {τ : Ty} (x : Var τ) (fs : List String) (args : List V) (nrets : Nat) :
    Spec C rd (B.dispatch x fs args nrets) (fun rs σ => ∃ (j : Nat) (h : j < fs.length),
      σ x.v = ofK (addressOfIndex j) ∧ C fs[j] (args.map σ) (rs.map fun r => σ r.v)) :=
  Spec.mono (Spec.bind (spec_freshRun _ _) fun rets =>
      Spec.bind (spec_emitDispatch x.v fs args rets) fun _ => Spec.pure _)
    (by rintro _ σ ⟨rets, -, _, h, rfl⟩; simpa [List.map_map, Function.comp_def] using h)

/-! ## Blocks and branches -/

/-- What a block's statements say: in any valuation where they hold before `next`, `Q` holds of
the block's result, and `next`. -/
def BlockOK (C : CallRel) (rd : Reader) {α : Type} (Q : α → Val → Prop) (r : α × List Stmt) :
    Prop :=
  ∀ σ next kret, Stmt.HoldsList C rd σ r.2 next kret → Q r.1 σ ∧ next

/-- `Spec.bind` after an action that emits nothing and whose result has a property of every run. -/
theorem Spec.bindOn {α β : Type} {m : B α} {f : α → B β} {P : α → Prop}
    {R : α → β → Val → Prop} (hm : ∀ st, (m.run st).2.out = st.out ∧ P (m.run st).1)
    (hf : ∀ a, P a → Spec C rd (f a) (R a)) :
    Spec C rd (m >>= f) (fun b σ => ∃ a, P a ∧ R a b σ) := by
  intro st
  obtain ⟨h1, h2⟩ := hm st
  obtain ⟨n, hn, hk⟩ := hf _ h2 (m.run st).2
  refine ⟨n, ?_, fun σ next kret h => ?_⟩
  · change ((f (m.run st).1).run (m.run st).2).2.out.toList = _
    rw [hn, h1]
  · obtain ⟨hr, hx⟩ := hk σ next kret h
    exact ⟨⟨_, h2, hr⟩, hx⟩

theorem spec_get : Spec C rd (get : B St) (fun _ _ => True) := Spec.silent fun _ => rfl

theorem spec_anchor : Spec C rd B.anchor (fun _ _ => True) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => spec_atom _) (fun _ _ _ => trivial)

theorem spec_closed {α : Type} {m : B α} {Q : α → Val → Prop} (h : Spec C rd m Q) :
    Spec C rd (B.closed m) Q := by
  have hif : ∀ st : St, Spec C rd (if st.pending then B.anchor else pure ())
      (fun _ _ => True) := fun st => by
    split
    · exact spec_anchor
    · exact Spec.mono (Spec.pure _) fun _ _ _ => trivial
  exact Spec.mono (Spec.bind h fun a => Spec.bind (spec_get (C := C) (rd := rd)) fun st =>
      Spec.bind (hif st) fun _ => Spec.pure a)
    (by rintro b σ ⟨a, hq, _, -, _, -, rfl⟩; exact hq)

/-- **A block**: it emits nothing where it runs, and its statements say what its body's do. -/
theorem spec_block {α : Type} {m : B α} {Q : α → Val → Prop} (h : Spec C rd m Q) (st : St) :
    ((B.block m).run st).2.out = st.out ∧ BlockOK C rd Q ((B.block m).run st).1 := by
  refine ⟨rfl, fun σ next kret hh => ?_⟩
  let st1 : St := { st with out := #[], pending := false, trace := st.trace.push .enter }
  obtain ⟨new, hn, hk⟩ := spec_closed h st1
  have hn' : ((B.closed m).run st1).2.out.toList = new := by rw [hn]; rfl
  exact hk σ next kret (by rw [← hn']; exact hh)

theorem spec_emitIte {α β : Type} {Qz : α → Val → Prop} {Qn : β → Val → Prop} (c : V)
    (zr : α × List Stmt) (nr : β × List Stmt) (hz : BlockOK C rd Qz zr)
    (hn : BlockOK C rd Qn nr) :
    Spec C rd (B.emit (.ite c zr.2 nr.2)) (fun _ σ =>
      IsInK (σ c) ∧ (σ c = 0 → Qz zr.1 σ) ∧ (σ c ≠ 0 → Qn nr.1 σ)) := fun st =>
  ⟨[.ite c zr.2 nr.2], by change (st.out.push _).toList = _; simp, fun σ next kret h => by
    simp only [Stmt.HoldsList, Stmt.Holds] at h
    obtain ⟨hk, h0, h1⟩ := h
    by_cases hc : σ c = 0
    · obtain ⟨q, hx⟩ := hz σ _ kret (h0 hc)
      exact ⟨⟨hk, fun _ => q, fun h => absurd hc h⟩, hx⟩
    · obtain ⟨q, hx⟩ := hn σ _ kret (h1 hc)
      exact ⟨⟨hk, fun h => absurd h hc, fun _ => q⟩, hx⟩⟩

/-- **A runtime branch**: `c` is in `K`, the zero block's fact holds at `c = 0`, the other's
else. -/
theorem spec_ite {τ : Ty} {α β : Type} (c : Var τ) {z : B α} {n : B β} {Qz : α → Val → Prop}
    {Qn : β → Val → Prop} (hz : Spec C rd z Qz) (hn : Spec C rd n Qn) :
    Spec C rd (B.ite c z n) (fun r σ =>
      IsInK (σ c.v) ∧ (σ c.v = 0 → Qz r.1 σ) ∧ (σ c.v ≠ 0 → Qn r.2 σ)) :=
  Spec.mono (Spec.bindOn (spec_block hz) fun zr hzr => Spec.bindOn (spec_block hn) fun nr hnr =>
      Spec.bind (spec_emitIte c.v zr nr hzr hnr) fun _ => Spec.pure (zr.1, nr.1))
    (by rintro _ σ ⟨zr, -, nr, -, _, h, rfl⟩; exact h)

/-- **A runtime branch with no `nonzero` block**. -/
theorem spec_ite0 {τ : Ty} {α : Type} (c : Var τ) {z : B α} {Qz : α → Val → Prop}
    (hz : Spec C rd z Qz) :
    Spec C rd (B.ite0 c z) (fun r σ => IsInK (σ c.v) ∧ (σ c.v = 0 → Qz r σ)) :=
  Spec.mono (Spec.bindOn (spec_block hz) fun zr hzr =>
      Spec.bind (spec_emitIte (Qn := fun (_ : Unit) _ => True) c.v zr ((), [])  hzr
        (fun _ _ _ h => ⟨trivial, h⟩)) fun _ => Spec.pure zr.1)
    (by rintro _ σ ⟨zr, -, _, ⟨hk, h0, -⟩, rfl⟩; exact ⟨hk, h0⟩)

/-! ## Hints and checks -/

theorem spec_event (e : Compiler.Event) : Spec C rd (B.event e) (fun _ _ => True) :=
  Spec.silent fun _ => rfl

theorem spec_witness (s : String) (d : Dest) : Spec C rd (B.witness s d) (fun _ _ => True) :=
  spec_hint _

theorem spec_witnessCell (s : String) : Spec C rd (B.witnessCell s) (fun _ _ => True) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_hint _) fun _ => Spec.pure _)
    (fun _ _ _ => trivial)

theorem spec_hintLog2Ceil (bits : Dest) (nbits floor : Nat) :
    Spec C rd (B.hintLog2Ceil bits nbits floor) (fun _ _ => True) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_hint _) fun _ => Spec.pure _)
    (fun _ _ _ => trivial)

theorem spec_hintWindowsExp {τ : Ty} (d : Dest) (x : Var τ) (start width count skip : Nat) :
    Spec C rd (B.hintWindowsExp d x start width count skip) (fun _ _ => True) :=
  Spec.mono (Spec.bind (spec_event _) fun _ => spec_hint _) (fun _ _ _ => trivial)

/-- `assert a != b`: the two words differ. -/
theorem spec_assertNe {σ' τ : Ty} (a : Var σ') (b : Var τ) :
    Spec C rd (B.assertNe a b) (fun _ σ => σ a.v ≠ σ b.v) :=
  Spec.mono (Spec.bind (spec_add a b) fun _ => Spec.bind (spec_fresh _) fun _ =>
      Spec.bind (spec_hint _) fun _ => Spec.bind (spec_fresh _) fun _ => spec_atom _)
    (by
      rintro _ σ ⟨x, hx, inv, -, _, -, p, -, h⟩ heq
      obtain ⟨h1, h2⟩ : σ p = σ x.v * σ inv ∧ σ p = 1 := h
      have h0 : σ x.v = 0 := by rw [hx, heq]; exact e_add_eq_zero_iff.mpr rfl
      rw [h1, h0, zero_mul] at h2
      exact zero_ne_one h2)

/-- The range check's atom: `DEREF`s through `x` and through `y`, `k = x·y`. -/
theorem spec_rangeCheckK {τ ρ : Ty} (x : Var τ) (k : Var ρ) :
    Spec C rd (B.rangeCheckK x k) (fun r σ => r.v = x.v ∧ ∃ y t1 t2 : E,
      LoadHolds rd (σ x.v) 0 t1 ∧ σ k.v = σ x.v * y ∧ LoadHolds rd y 0 t2) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_fresh _) fun _ =>
      Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨y, -, t1, -, t2, -, _, h, rfl⟩; exact ⟨rfl, σ y, σ t1, σ t2, h⟩)

/-- `assert log x < n`: the range check against the constant `g^(n-1)`. -/
theorem spec_rangeCheck {τ : Ty} (x : Var τ) (n : Nat) :
    Spec C rd (B.rangeCheck x n) (fun r σ => r.v = x.v ∧ ∃ y t1 t2 : E,
      LoadHolds rd (σ x.v) 0 t1 ∧ gpowE (n - 1) = σ x.v * y ∧ LoadHolds rd y 0 t2) :=
  Spec.mono (Spec.bind (spec_const _) fun k => Spec.bind (spec_rangeCheckK x k) fun _ =>
      Spec.pure _)
    (by
      rintro _ σ ⟨k, hk, r, ⟨hr, y, t1, t2, h1, h2, h3⟩, rfl⟩
      exact ⟨hr, y, t1, t2, h1, hk ▸ h2, h3⟩)

/-- `assert log x < log b` at a runtime bound: the range check against `b·g⁻¹`. -/
theorem spec_rangeCheckRt {τ ρ : Ty} (x : Var τ) (b : Var ρ) :
    Spec C rd (B.rangeCheckRt x b) (fun r σ => r.v = x.v ∧ ∃ y t1 t2 : E,
      LoadHolds rd (σ x.v) 0 t1 ∧ σ b.v * ofK gInv = σ x.v * y ∧ LoadHolds rd y 0 t2) :=
  Spec.mono (Spec.bind (spec_const _) fun _ => Spec.bind (spec_mul _ _) fun k =>
      spec_rangeCheckK x k)
    (by
      rintro r σ ⟨i, hi, k, hk, hr, y, t1, t2, h1, h2, h3⟩
      refine ⟨hr, y, t1, t2, h1, ?_, h3⟩
      rw [← hi, ← hk, h2])

theorem spec_assertInK {σ' τ : Ty} (a : Var σ') (b : Var τ) :
    Spec C rd (B.assertInK a b) (fun _ σ => IsInK (σ a.v) ∧ IsInK (σ b.v)) := spec_atom _

/-- `assert_gpow(x)`: a `DEREF` through `x`, so `x` is in `K`. -/
theorem spec_assertGpow {τ : Ty} (x : Var τ) :
    Spec C rd (B.assertGpow x) (fun r σ => r.v = x.v ∧ ∃ t : E, LoadHolds rd (σ x.v) 0 t) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_atom _) fun _ => Spec.pure _)
    (by rintro _ σ ⟨t, -, _, h, rfl⟩; exact ⟨rfl, σ t, h⟩)

/-! ## Advice-only actions and memory -/

theorem spec_use {τ : Ty} (x : Var τ) : Spec C rd (B.use x) (fun r _ => r = x) :=
  Spec.mono (Spec.bind (Spec.silent fun st => by
      show (if st.faithful then _ else st).out = st.out
      split <;> rfl) fun _ => Spec.pure x)
    (by rintro _ _ ⟨_, -, rfl⟩; rfl)

theorem spec_chain : Spec C rd B.chain (fun _ _ => True) := Spec.silent fun _ => rfl

theorem spec_frameAddr (p : V) (run : List V) :
    Spec C rd (B.frameAddr p run) (fun _ σ => Atom.Holds rd σ (.frameAddr p run)) := fun st =>
  ⟨[.atom (.frameAddr p run)], by change (st.out.push _).toList = _; simp,
    fun σ next kret h => by simpa [Stmt.HoldsList, Stmt.Holds] using h⟩

/-- `addr(run)`: the pointer is in `K` and the frame run is at it. -/
theorem spec_addr (run : List V) :
    Spec C rd (B.addr run) (fun r σ => Atom.Holds rd σ (.frameAddr r.v run)) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_frameAddr _ _) fun _ =>
      Spec.bind (Spec.silent fun _ => rfl) fun _ => Spec.pure _)
    (by rintro _ σ ⟨p, -, _, h, _, -, rfl⟩; exact h)

theorem spec_heapBufDyn {τ : Ty} (size : Var τ) :
    Spec C rd (B.heapBufDyn size) (fun _ _ => True) :=
  Spec.mono (Spec.bind (spec_fresh _) fun _ => Spec.bind (spec_hint _) fun _ => Spec.pure _)
    (fun _ _ _ => trivial)

/-- A runtime-start heap slice starts at `p·i`. -/
theorem spec_sliceRt {σ' τ : Ty} (p : Var σ') (i : Var τ) (off len : Nat) :
    Spec C rd (B.sliceRt p i off len) (fun d σ => ∃ q, d = .heap q off len ∧ σ q = σ p.v * σ i.v) :=
  Spec.mono (Spec.bind (spec_mul p i) fun _ => Spec.pure _)
    (by rintro _ σ ⟨q, hq, rfl⟩; exact ⟨q.v, rfl, hq⟩)

/-- `heap_base`: the offset folded, or the pointer shifted at offset `0`. -/
theorem spec_ptrAt {τ : Ty} (p : Var τ) (off : Nat) :
    Spec C rd (B.ptrAt p off) (fun r σ => (r.2 = off ∧ σ r.1.v = σ p.v) ∨
      (r.2 = 0 ∧ σ r.1.v = σ p.v * gpowE off)) := by
  unfold B.ptrAt
  split
  · exact Spec.mono (Spec.pure _) (by rintro _ _ rfl; exact Or.inl ⟨rfl, rfl⟩)
  · exact Spec.mono (Spec.bind (spec_const _) fun _ => Spec.bind (spec_mul _ _) fun _ =>
        Spec.pure _) (by rintro _ σ ⟨c, hc, q, hq, rfl⟩; exact Or.inr ⟨rfl, by rw [hq, hc]⟩)

end
end LeanVM.Dsl
