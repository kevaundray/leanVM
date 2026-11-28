/-
  LeanVM.Dsl.KeccakLogic

  The program logic's rules for the Keccak builtins: what the statements `LeanVM.Dsl.Keccak`
  emits say of a valuation that satisfies them.
-/

module

public import LeanVM.Dsl.Keccak
public import LeanVM.Dsl.Logic

/-!
# Rules for the Keccak builtins

* `spec_loadRun`: a heap slice read into a fresh run, one `DEREF` each;
* `spec_copyRun`: message cells copied into a fresh run hold their words (`Msg.eval`);
* `spec_setPadRun`, `padRun_run_none`, `padRun_run_some`: the padding run, set at its first use in
  a scope, holds `[0x01, 0, 0, 0, 0]`; a later use reads the same run and emits nothing;
* `spec_keccakDuplex`, `spec_keccakDuplex_13`: the duplex step over eight message values and a
  frame capacity is one `KECCAK` of those cells (`keccak_holds_13`: Keccak-f's output state
  into a 13-cell frame destination).

A `keccak` or `keccak_cells` reading a literal zero, and every padded message, reads the padding
run, which a statement before the action may have set: its rule needs the scope's invariant (the
run, once set, holds its values: `spec_setPadRun`, `padRun_run_some`) carried through the state,
which `Spec` does not carry.
-/

namespace LeanVM.Dsl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core
open Keccak

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The word a message cell holds. -/
def Msg.eval (σ : Val) : Msg → E
  | .zero => 0
  | .const c => c
  | .cell o => σ o

/-- A `KECCAK`'s relation reads its cells' words only. -/
theorem keccak_holds_congr {ins ins' outs : List V} {i o : Bool} {σ : Val}
    (h : ins.map σ = ins'.map σ) :
    (Atom.keccak ins outs i o).Holds rd σ ↔ (Atom.keccak ins' outs i o).Holds rd σ := by
  have hl : ins.length = ins'.length := by simpa using congrArg List.length h
  simp only [Atom.Holds, h, hl]

/-- A value of a run's `zipIdx` at its index. -/
theorem mem_zipIdx_getElem {α : Type} (l : List α) (k : Nat) (hk : k < l.length) :
    (l[k], k) ∈ l.zipIdx :=
  List.mem_zipIdx_iff_getElem?.mpr (by simp [hk])

/-- A heap slice read into a fresh run: each value the word at its offset. -/
theorem spec_loadRun (ptr : V) (lo len : Nat) :
    Spec C rd (Keccak.loadRun ptr lo len) (fun t σ => t.length = len ∧
      ∀ k (hk : k < t.length), LoadHolds rd (σ ptr) (lo + k) (σ t[k])) := by
  refine Spec.mono (Spec.bind (spec_freshRun len .cell) fun t =>
    Spec.bind (Spec.forM t.zipIdx (P := fun x σ => (Atom.load x.1 ptr (lo + x.2)).Holds rd σ)
      fun x _ => ?_) fun _ => Spec.pure t) ?_
  · obtain ⟨d, k⟩ := x
    exact spec_atom _
  · rintro t σ ⟨_, hl, _, hall, rfl⟩
    refine ⟨hl, fun k hk => ?_⟩
    have e := hall _ (mem_zipIdx_getElem t k hk)
    simp only at e
    exact e

/-- Message cells copied into a fresh run: each value the word of its cell. -/
theorem spec_copyRun (cells : List Msg) :
    Spec C rd (Keccak.copyRun cells) (fun t σ => t.map σ = cells.map (Msg.eval σ)) := by
  refine Spec.mono (Spec.bind (spec_freshRun cells.length .joined) fun t =>
    Spec.bind (Spec.forM (cells.zip t) (P := fun x σ => σ x.2 = Msg.eval σ x.1)
      fun x _ => ?_) fun _ => Spec.pure t) ?_
  · obtain ⟨c, d⟩ := x
    cases c <;> exact spec_atom _
  · rintro t σ ⟨_, hl, _, hall, rfl⟩
    refine List.ext_getElem (by simp [hl]) fun k h1 h2 => ?_
    have hk : k < cells.length := by simpa using h2
    have hk' : k < t.length := by simpa using h1
    simp only [List.getElem_map]
    exact hall (cells[k], t[k]) (List.mem_iff_getElem.mpr
      ⟨k, by simp [hl, hk], by simp⟩)

/-- The padding run set: its values hold `[0x01, 0, 0, 0, 0]`. -/
theorem spec_setPadRun : Spec C rd Keccak.setPadRun (fun o σ => o.map σ = padValues) := by
  refine Spec.mono (Spec.bind (spec_freshRun 5 .padRun) fun o =>
    Spec.bind (Spec.forM o.zipIdx (P := fun x σ => σ x.1 = padValues.getD x.2 0)
      fun x _ => ?_) fun _ =>
        Spec.bind (Spec.silent (m := modify fun st => { st with keccakPad := some o })
          fun _ => rfl) fun _ => Spec.pure o) ?_
  · obtain ⟨v, k⟩ := x
    exact Spec.mono (Spec.bind (spec_atom _) fun _ => spec_poolConst _)
      (by rintro _ σ ⟨_, h, -⟩; exact h)
  · rintro o σ ⟨_, hl, _, hall, _, -, rfl⟩
    refine List.ext_getElem (by simp [hl, padValues]) fun k h1 h2 => ?_
    have hk : k < o.length := by simpa using h1
    have e := hall _ (mem_zipIdx_getElem o k hk)
    simp only at e
    rw [List.getElem_map, e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

/-- The padding run's first use in a scope sets it. -/
theorem padRun_run_none {st : St} (h : st.keccakPad = none) :
    Keccak.padRun.run st = Keccak.setPadRun.run st := by
  simp [Keccak.padRun, h]

/-- A later use reads the run the scope set, emitting nothing. -/
theorem padRun_run_some {st : St} {o : List V} (h : st.keccakPad = some o) :
    Keccak.padRun.run st = (o, st) := by
  simp [Keccak.padRun, h]
  rfl

/-- Four message values from the zero state, as `rate` reads them: in place when they are one run,
else copied into one. -/
theorem spec_spongeRun_cells (x0 x1 x2 x3 : V) :
    Spec C rd (Keccak.spongeRun [.cell x0, .cell x1, .cell x2, .cell x3])
      (fun t σ => t.map σ = [σ x0, σ x1, σ x2, σ x3]) := by
  by_cases h : Keccak.isRun [x0, x1, x2, x3] = true
  · have e : Keccak.spongeRun [.cell x0, .cell x1, .cell x2, .cell x3] = pure [x0, x1, x2, x3] := by
      simp [Keccak.spongeRun, Keccak.Msg.val?, h]
    rw [e]
    exact Spec.mono (Spec.pure _) (by rintro _ σ rfl; rfl)
  · have e : Keccak.spongeRun [.cell x0, .cell x1, .cell x2, .cell x3] =
        Keccak.copyRun [.cell x0, .cell x1, .cell x2, .cell x3] := by
      simp [Keccak.spongeRun, Keccak.Msg.val?, h, Keccak.padHead, Msg.isZero]
    rw [e]
    exact Spec.mono (spec_copyRun _) (by rintro _ σ h; simpa [Msg.eval] using h)

/-- The rate of eight message values from the zero state: the first four values, and a run holding
the last four. -/
theorem spec_rate_cells (x0 x1 x2 x3 x4 x5 x6 x7 : V) :
    Spec C rd (Keccak.rate [.cell x0, .cell x1, .cell x2, .cell x3, .cell x4, .cell x5, .cell x6,
      .cell x7] none)
      (fun r σ => r.1 = [x0, x1, x2, x3] ∧ r.2.map σ = [σ x4, σ x5, σ x6, σ x7]) := by
  have e : Keccak.rate [.cell x0, .cell x1, .cell x2, .cell x3, .cell x4, .cell x5, .cell x6,
      .cell x7] none =
      (Keccak.spongeRun [.cell x4, .cell x5, .cell x6, .cell x7] >>= fun t =>
        pure ([x0, x1, x2, x3], t)) := rfl
  rw [e]
  exact Spec.mono (Spec.bind (spec_spongeRun_cells x4 x5 x6 x7) fun t => Spec.pure _)
    (by rintro _ σ ⟨t, ht, rfl⟩; exact ⟨rfl, ht⟩)

/-- **The duplex step** (`keccak(a, b, out, tail=, cap=)`) over eight message values and a frame
capacity, into a frame destination: one `KECCAK` of the message values then the capacity
(`capFrame`) into the destination's written cells (`frameOut`). -/
theorem spec_keccakDuplex (a0 a1 b0 b1 t0 t1 t2 t3 : V) (cs o : List V) :
    Spec C rd (B.keccakDuplex (.frame [a0, a1]) (.frame [b0, b1]) (.frame o) (.frame cs)
      (some (.frame [t0, t1, t2, t3])))
      (fun _ σ => (Atom.keccak ([a0, a1, b0, b1, t0, t1, t2, t3] ++ capFrame cs) (frameOut o)
        false false).Holds rd σ) := by
  have e : B.keccakDuplex (.frame [a0, a1]) (.frame [b0, b1]) (.frame o) (.frame cs)
      (some (.frame [t0, t1, t2, t3])) =
      (Keccak.rate [.cell a0, .cell a1, .cell b0, .cell b1, .cell t0, .cell t1, .cell t2,
        .cell t3] none >>= fun r =>
        B.atom (.keccak (r.1 ++ r.2 ++ capFrame cs) (frameOut o) false false)) := rfl
  rw [e]
  refine Spec.mono (Spec.bind (spec_rate_cells a0 a1 b0 b1 t0 t1 t2 t3) fun r => spec_atom _) ?_
  rintro _ σ ⟨⟨m, tl⟩, ⟨hm, ht⟩, h⟩
  simp only at hm ht h
  subst hm
  refine (keccak_holds_congr ?_).mp h
  simp [ht]

/-- The duplex step into a 13-cell frame destination: the destination holds Keccak-f's output
state of the message values and the capacity (`KeccakCellsRelation … .all`). -/
theorem spec_keccakDuplex_13 (a0 a1 b0 b1 t0 t1 t2 t3 : V) (cs o : List V)
    (ho : 13 ≤ o.length) :
    Spec C rd (B.keccakDuplex (.frame [a0, a1]) (.frame [b0, b1]) (.frame o) (.frame cs)
      (some (.frame [t0, t1, t2, t3])))
      (fun _ σ => KeccakCellsRelation (cells13 (([a0, a1, b0, b1, t0, t1, t2, t3] ++ capFrame cs).map σ))
        false (cells13 ((o.take 13).map σ)) false .all) := by
  have hf : frameOut o = o.take 13 := by simp [frameOut, stateCells, ho]
  refine Spec.mono (spec_keccakDuplex a0 a1 b0 b1 t0 t1 t2 t3 cs o) ?_
  rintro _ σ h
  rw [hf, keccak_holds_13 (by simp; omega)] at h
  exact h.2.2

end
end LeanVM.Dsl
