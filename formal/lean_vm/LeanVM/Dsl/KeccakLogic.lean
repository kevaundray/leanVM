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
  into a 13-cell frame destination);
* `SpecP`, `PadOk`: a builtin reading a literal zero or padding its message reads the padding run,
  which a statement before it may have set, so its rule carries the scope's invariant (the run,
  once set, holds its values) through the state: `SpecP.bind`, `SpecP.ofSpec`, `specP_padRun`,
  and `GFn.sem_of_specP` (a function starts with no run);
* `specP_keccakPair`, `specP_keccakPair_two`: the two-to-one hash (the Merkle hash pair) is one
  `KECCAK` of the four message values and the padding (`pairBlock`), its 2-cell destination
  Keccak-f's first two output cells (`pairHash`).

Not given: `keccak_cells` over several blocks, a tail, `len=` or `pad_tail=1`, whose rules are the
same composition over `absorbFrom`'s blocks and `xorByte`'s padding, longer than one lemma each.
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

/-! ## The padding run's invariant

`SpecP` is `Spec` carrying the scope's invariant `PadOk`: the padding run, once set, holds
`[0x01, 0, 0, 0, 0]`. An action reading the run (`specP_padRun`) gets its values from the
invariant when an earlier statement set it, and from its own statements otherwise; an action that
leaves the run alone keeps it (`SpecP.ofSpec`). -/

/-- The scope's padding run, if set, holds its values. -/
def PadOk (st : St) (σ : Val) : Prop := ∀ o, st.keccakPad = some o → o.map σ = padValues

/-- `Spec` from a state where `PadOk` holds, to one where it still does. -/
def SpecP {α : Type} (C : CallRel) (rd : Reader) (m : B α) (Q : α → Val → Prop) : Prop :=
  ∀ st : St, ∃ new : List Stmt, (m.run st).2.out.toList = st.out.toList ++ new ∧
    ∀ (σ : Val) (next : Prop) (kret : List E → Prop), PadOk st σ →
      Stmt.HoldsList C rd σ new next kret → (Q (m.run st).1 σ ∧ PadOk (m.run st).2 σ) ∧ next

theorem SpecP.mono {α : Type} {m : B α} {Q Q' : α → Val → Prop} (h : SpecP C rd m Q)
    (hq : ∀ a σ, Q a σ → Q' a σ) : SpecP C rd m Q' := by
  intro st
  obtain ⟨new, hn, hk⟩ := h st
  refine ⟨new, hn, fun σ next kret hp hh => ?_⟩
  obtain ⟨⟨hqa, hpa⟩, hna⟩ := hk σ next kret hp hh
  exact ⟨⟨hq _ _ hqa, hpa⟩, hna⟩

theorem SpecP.bind {α β : Type} {m : B α} {f : α → B β} {Q : α → Val → Prop}
    {R : α → β → Val → Prop} (hm : SpecP C rd m Q) (hf : ∀ a, SpecP C rd (f a) (R a)) :
    SpecP C rd (m >>= f) (fun b σ => ∃ a, Q a σ ∧ R a b σ) := by
  intro st
  obtain ⟨n1, h1, k1⟩ := hm st
  obtain ⟨n2, h2, k2⟩ := hf (m.run st).1 (m.run st).2
  refine ⟨n1 ++ n2, ?_, fun σ next kret hp h => ?_⟩
  · change ((f (m.run st).1).run (m.run st).2).2.out.toList = _
    rw [h2, h1, List.append_assoc]
  · rw [holdsList_append] at h
    obtain ⟨⟨hq, hp1⟩, h⟩ := k1 σ _ kret hp h
    obtain ⟨⟨hr, hp2⟩, hn⟩ := k2 σ next kret hp1 h
    exact ⟨⟨⟨_, hq, hr⟩, hp2⟩, hn⟩

/-- An action that leaves the padding run alone keeps the invariant. -/
theorem SpecP.ofSpec {α : Type} {m : B α} {Q : α → Val → Prop} (h : Spec C rd m Q)
    (hp : ∀ st, (m.run st).2.keccakPad = st.keccakPad) : SpecP C rd m Q := by
  intro st
  obtain ⟨new, hn, hk⟩ := h st
  refine ⟨new, hn, fun σ next kret hpad hh => ?_⟩
  obtain ⟨hq, hn'⟩ := hk σ next kret hh
  exact ⟨⟨hq, fun o ho => hpad o (by rw [← hp st]; exact ho)⟩, hn'⟩

/-- Setting the padding run makes it the scope's. -/
theorem setPadRun_sets (st : St) :
    (Keccak.setPadRun.run st).2.keccakPad = some (Keccak.setPadRun.run st).1 := by
  simp [Keccak.setPadRun]
  rfl

/-- **The padding run** holds `[0x01, 0, 0, 0, 0]`: set here, by its own statements; set before,
by the invariant. -/
theorem specP_padRun : SpecP C rd Keccak.padRun (fun o σ => o.map σ = padValues) := by
  intro st
  cases hs : st.keccakPad with
  | some o =>
    refine ⟨[], by rw [padRun_run_some hs]; simp, fun σ next kret hp hh => ?_⟩
    rw [padRun_run_some hs]
    exact ⟨⟨hp o hs, hp⟩, hh⟩
  | none =>
    obtain ⟨new, hn, hk⟩ := spec_setPadRun (C := C) (rd := rd) st
    refine ⟨new, by rw [padRun_run_none hs]; exact hn, fun σ next kret _ hh => ?_⟩
    obtain ⟨hv, hn'⟩ := hk σ next kret hh
    rw [padRun_run_none hs]
    refine ⟨⟨hv, fun o ho => ?_⟩, hn'⟩
    rw [setPadRun_sets] at ho
    cases ho
    exact hv

/-- Recording a constant leaves the padding run alone. -/
theorem poolConst_keccakPad (c : E) (st : St) :
    ((B.poolConst c).run st).2.keccakPad = st.keccakPad := by
  show (if st.consts.contains c then st else { st with consts := c :: st.consts }).keccakPad = _
  split <;> rfl

theorem specP_const (c : E) : SpecP C rd (B.const c) (fun r σ => σ r.v = c) :=
  SpecP.ofSpec (spec_const c) fun _ => poolConst_keccakPad c _

theorem specP_atom (a : Atom) : SpecP C rd (B.atom a) (fun _ σ => a.Holds rd σ) :=
  SpecP.ofSpec (spec_atom a) fun _ => rfl

theorem SpecP.pure {α : Type} (a : α) : SpecP C rd (Pure.pure a : B α) (fun b _ => b = a) :=
  SpecP.ofSpec (Spec.pure a) fun _ => rfl

/-! ## The two-to-one hash -/

/-- The block a two-to-one hash reads: the four message cells, the padding's first byte, zeros, its
closing byte, the zero capacity. -/
def pairBlock (a0 a1 b0 b1 : E) : List E :=
  [a0, a1, b0, b1, keccakPadValue, 0, 0, 0, twoToOneClose, 0, 0, 0, 0]

/-- The padding's first byte, at the start of the cell after a 64-byte message. -/
theorem byteWord_64 : byteWord 64 Protocol.KeccakHash.padFirst.toNat = keccakPadValue := rfl

/-- The padding's closing byte, at the end of a one-block message's last rate lane. -/
theorem byteWord_135 : byteWord 135 Protocol.KeccakHash.padLast.toNat = twoToOneClose := rfl

/-- The closing lane is not the padding's first byte. -/
theorem twoToOneClose_ne : (twoToOneClose == keccakPadValue) = false := by decide +kernel

/-- The cells of a two-to-one hash's block: the message values, the padding's bytes. -/
def pairCells (a0 a1 b0 b1 : V) : List Msg :=
  [.cell a0, .cell a1, .cell b0, .cell b1, .const (byteWord 64 Protocol.KeccakHash.padFirst.toNat),
    .zero, .zero, .zero, .const (byteWord 135 Protocol.KeccakHash.padLast.toNat)]

/-- The rate of a two-to-one hash's block: the message values, and the padding's run. -/
theorem rate_pair (a0 a1 b0 b1 : V) : Keccak.rate (pairCells a0 a1 b0 b1) none =
    (Keccak.spongeRun [.const (byteWord 64 Protocol.KeccakHash.padFirst.toNat), .zero, .zero,
        .zero] >>= fun t => Pure.pure ([a0, a1, b0, b1], t)) := rfl

set_option maxRecDepth 100000 in
attribute [local irreducible] Keccak.spongeRun Keccak.spongeCell Keccak.padRun in
/-- `keccak(a, b, out)` over four message values, as the builtin unfolds: the padding cells read
from the scope's run, the closing lane a constant. -/
theorem keccak_pair_eq (a0 a1 b0 b1 : V) (o : List V) :
    B.keccak (.words [.cell a0, .cell a1]) (.words [.cell b0, .cell b1]) (.frame o) =
      ((Keccak.spongeRun [.const (byteWord 64 Protocol.KeccakHash.padFirst.toNat), .zero, .zero,
          .zero] >>= fun t => Pure.pure ([a0, a1, b0, b1], t)) >>= fun r =>
        Keccak.spongeCell (.const (byteWord 135 Protocol.KeccakHash.padLast.toNat)) >>= fun b8 =>
        (Keccak.padRun >>= fun p => Pure.pure (p.drop 1)) >>= fun cap =>
        B.atom (.keccak (r.1 ++ r.2 ++ [b8] ++ cap) (frameOut o) false false) >>= fun _ =>
        Pure.pure ()) >>= fun _ => Pure.pure () := by
  have h1 : B.keccak (.words [.cell a0, .cell a1]) (.words [.cell b0, .cell b1]) (.frame o) =
      (Keccak.absorb [.cell a0, .cell a1, .cell b0, .cell b1] (some 64) none (frameOut o) false >>=
        fun _ => Pure.pure ()) := rfl
  have h2 : Keccak.absorb [.cell a0, .cell a1, .cell b0, .cell b1] (some 64) none (frameOut o)
      false = Keccak.absorbFrom (pairCells a0 a1 b0 b1) 1 (frameOut o) 1 none 0 := by
    simp only [Keccak.absorb, Keccak.xorByte]
    rfl
  have h3 : Keccak.absorbFrom (pairCells a0 a1 b0 b1) 1 (frameOut o) 1 none 0 =
      (Keccak.rate (pairCells a0 a1 b0 b1) none >>= fun r =>
        Keccak.spongeCell (.const (byteWord 135 Protocol.KeccakHash.padLast.toNat)) >>= fun b8 =>
        (Keccak.padRun >>= fun p => Pure.pure (p.drop 1)) >>= fun cap =>
        B.atom (.keccak (r.1 ++ r.2 ++ [b8] ++ cap) (frameOut o) false false) >>= fun _ =>
        Pure.pure ()) := rfl
  rw [h1, h2, h3, rate_pair]

/-- **The two-to-one hash** (`keccak(a, b, out)`, the Merkle hash pair): one `KECCAK` of the four
message values, padded, into the destination's written cells. -/
theorem specP_keccakPair (a0 a1 b0 b1 : V) (o : List V) :
    SpecP C rd (B.keccak (.words [.cell a0, .cell a1]) (.words [.cell b0, .cell b1]) (.frame o))
      (fun _ σ => ∃ oc : KeccakOutputCells, (frameOut o).length = oc.cellCount ∧
        KeccakCellsRelation (cells13 (pairBlock (σ a0) (σ a1) (σ b0) (σ b1))) false
          (cells13 ((frameOut o).map σ)) false oc) := by
  have hrun : Keccak.spongeRun [.const (byteWord 64 Protocol.KeccakHash.padFirst.toNat), .zero,
      .zero, .zero] = (Keccak.padRun >>= fun p => Pure.pure (p.take 4)) := by
    simp [Keccak.spongeRun, Keccak.Msg.val?, List.filterMap_cons, List.filterMap_nil,
      Keccak.padHead, Msg.isZero, byteWord_64]
  have hcell : Keccak.spongeCell (.const (byteWord 135 Protocol.KeccakHash.padLast.toNat)) =
      (B.const twoToOneClose >>= fun w => Pure.pure w.v) := by
    simp only [Keccak.spongeCell, byteWord_135, twoToOneClose_ne]
    rfl
  rw [keccak_pair_eq, hrun, hcell]
  refine SpecP.mono (SpecP.bind (SpecP.bind (SpecP.bind (SpecP.bind specP_padRun fun p =>
      SpecP.pure (p.take 4)) fun t => SpecP.pure ([a0, a1, b0, b1], t)) fun r =>
    SpecP.bind (SpecP.bind (specP_const _) fun w => SpecP.pure w.v) fun b8 =>
    SpecP.bind (SpecP.bind specP_padRun fun p => SpecP.pure (p.drop 1)) fun cap =>
    SpecP.bind (specP_atom _) fun _ => SpecP.pure ()) fun _ => SpecP.pure ()) ?_
  rintro _ σ ⟨_, ⟨r, ⟨t, ⟨p, hp, rfl⟩, rfl⟩, b8, ⟨w, hw, rfl⟩, cap, ⟨q, hq, rfl⟩, _,
    ⟨-, oc, ho, hk⟩, -⟩, -⟩
  refine ⟨oc, ho, ?_⟩
  have hvals : ([a0, a1, b0, b1] ++ p.take 4 ++ [w.v] ++ q.drop 1).map σ =
      pairBlock (σ a0) (σ a1) (σ b0) (σ b1) := by
    simp only [List.map_append, List.map_take, List.map_drop, hp, hq, List.map_cons,
      List.map_nil, hw]
    rfl
  rw [hvals] at hk
  exact hk

/-- Keccak-f's output cells of a two-to-one hash's block. -/
def pairHash (a0 a1 b0 b1 : E) : Fin 13 → E :=
  cellsOfState (keccakF1600 (stateOfCells (cells13 (pairBlock a0 a1 b0 b1)) false)) false

/-- **The Merkle hash pair** into a 2-cell frame run: the digest's two cells. -/
theorem specP_keccakPair_two (a0 a1 b0 b1 o0 o1 : V) :
    SpecP C rd (B.keccak (.words [.cell a0, .cell a1]) (.words [.cell b0, .cell b1])
      (.frame [o0, o1]))
      (fun _ σ => σ o0 = pairHash (σ a0) (σ a1) (σ b0) (σ b1) 0 ∧
        σ o1 = pairHash (σ a0) (σ a1) (σ b0) (σ b1) 1) := by
  refine SpecP.mono (specP_keccakPair a0 a1 b0 b1 [o0, o1]) ?_
  rintro _ σ ⟨oc, ho, hk⟩
  have hf : frameOut [o0, o1] = [o0, o1] := rfl
  rw [hf] at ho hk
  have h2 : oc.cellCount = 2 := by simpa using ho.symm
  exact ⟨hk 0 (by simp [h2]), hk 1 (by simp [h2])⟩

/-- **A function's relation from its body's `SpecP`**: a function starts with no padding run, so
the invariant holds at its start (`GFn.sem_of_spec` with the invariant). -/
theorem GFn.sem_of_specP {f : GFn} {Q : List Ret → Val → Prop}
    (h : SpecP C rd (f.body (params f.arity)) Q) {args rets : List E}
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
  obtain ⟨⟨hq, -⟩, hb⟩ := k1 σ _ _ (fun _ h => by cases h) hb
  obtain ⟨ha, hret⟩ := k2 σ _ _ hb
  refine ⟨σ, hp, _, hq, ?_⟩
  simp only [Stmt.HoldsList, Stmt.Holds] at hret
  exact hret.symm.trans ha

end
end LeanVM.Dsl
