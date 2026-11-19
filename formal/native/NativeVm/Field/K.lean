module

public import NativeVm.Field.KWin

/-!
# `K` on the machine

`kmul`: `rax := rax · rbx` in `K = GF(2^64)`, four bits of `rax` at a time (`NativeVm.Field.KWin`):
the sixteen products of `rbx` by the polynomials of degree below four in the scratch bank (`ktab`,
`Tab`), then, from the top nibble of `rax` down, a 128-bit accumulator in `(rbx, rcx)` shifted by
`x^4` and added the entry of the next nibble (`kinit`, `kstep`, `Acc`), and one reduction of the
accumulator by `x^64 = x^4 + x^3 + x + 1` (`kred`); `ksq`: `rax := rax²`. Both write `rax`, `rbx`,
`rcx`, `r8`, the scratch bank and no memory.
-/

@[expose] public section

namespace NativeVm.Field

open Native LeanVM.Parameters

/-- The table: scratch word `n` is `n · rbx` in `K`, `rcx` holding `x^k · rbx` for the entries `2^k`
to `2^(k+1) - 1`, `r8` a temporary; `rax` is kept. -/
def ktab : Stmt := blk [
  I (.movi .r8 0), I (.sstore 0 .r8), I (.sstore 1 .rbx),
  I (.mov .rcx .rbx),
  I (.mov .r8 .rcx), I (.sari .r8 63), I (.andi .r8 0x1B), I (.shli .rcx 1), I (.xor .rcx .r8),
  I (.sstore 2 .rcx), I (.mov .r8 .rcx), I (.xor .r8 .rbx), I (.sstore 3 .r8),
  I (.mov .r8 .rcx), I (.sari .r8 63), I (.andi .r8 0x1B), I (.shli .rcx 1), I (.xor .rcx .r8),
  I (.sstore 4 .rcx), I (.mov .r8 .rcx), I (.xor .r8 .rbx), I (.sstore 5 .r8),
  I (.movi .r8 2), I (.sload .r8 .r8), I (.xor .r8 .rcx), I (.sstore 6 .r8),
  I (.movi .r8 3), I (.sload .r8 .r8), I (.xor .r8 .rcx), I (.sstore 7 .r8),
  I (.mov .r8 .rcx), I (.sari .r8 63), I (.andi .r8 0x1B), I (.shli .rcx 1), I (.xor .rcx .r8),
  I (.sstore 8 .rcx), I (.mov .r8 .rcx), I (.xor .r8 .rbx), I (.sstore 9 .r8),
  I (.movi .r8 2), I (.sload .r8 .r8), I (.xor .r8 .rcx), I (.sstore 10 .r8),
  I (.movi .r8 3), I (.sload .r8 .r8), I (.xor .r8 .rcx), I (.sstore 11 .r8),
  I (.movi .r8 4), I (.sload .r8 .r8), I (.xor .r8 .rcx), I (.sstore 12 .r8),
  I (.movi .r8 5), I (.sload .r8 .r8), I (.xor .r8 .rcx), I (.sstore 13 .r8),
  I (.movi .r8 6), I (.sload .r8 .r8), I (.xor .r8 .rcx), I (.sstore 14 .r8),
  I (.movi .r8 7), I (.sload .r8 .r8), I (.xor .r8 .rcx), I (.sstore 15 .r8)]

/-- The accumulator `(rbx, rcx)` from the top nibble of `rax`: `(0, T[rax >> 60])`. -/
def kinit : Stmt :=
  blk [I (.mov .rcx .rax), I (.shri .rcx 60), I (.sload .rcx .rcx), I (.movi .rbx 0)]

/-- Step `m`: `(rbx, rcx) := (rbx, rcx) · x^4 + T[nibble]`, the nibble of `rax` at bit `56 - 4m`. -/
def kstep (m : Nat) : Stmt := blk [
  I (.mov .r8 .rcx), I (.shri .r8 60), I (.shli .rbx 4), I (.xor .rbx .r8), I (.shli .rcx 4),
  I (.mov .r8 .rax), I (.shri .r8 (56 - 4 * m)), I (.andi .r8 15), I (.sload .r8 .r8),
  I (.xor .rcx .r8)]

/-- `rax := rcx + rbx · (x^4 + x^3 + x + 1)`, the accumulator reduced, `rbx` below `2^60`. -/
def kred : Stmt := blk [
  I (.xor .rcx .rbx), I (.mov .r8 .rbx), I (.shli .r8 1), I (.xor .rcx .r8),
  I (.mov .r8 .rbx), I (.shli .r8 3), I (.xor .rcx .r8),
  I (.mov .r8 .rbx), I (.shli .r8 4), I (.xor .rcx .r8), I (.mov .rax .rcx)]

/-- `rax := rax · rbx` in `K`. -/
def kmul : Stmt := blk [ktab, kinit,
  kstep 0, kstep 1, kstep 2, kstep 3, kstep 4, kstep 5, kstep 6, kstep 7, kstep 8, kstep 9,
  kstep 10, kstep 11, kstep 12, kstep 13, kstep 14, kred]

/-- The registers `kmul` and `ksq` write. -/
abbrev kRegs : List Reg64 := [.rax, .rbx, .rcx, .r8]

theorem mulXW_unfold (t : UInt64) :
    (t <<< 1) ^^^ (UInt64.ofBitVec (t.toBitVec.sshiftRight 63) &&& 0x1B) = mulXW t := (rfl)

theorem ofLane_two : K.ofLane 2 = g := (rfl)

theorem ofLane_four : K.ofLane 4 = g * g := by
  rw [show (4 : UInt64) = mulXW 2 by decide, ofLane_mulXW, ofLane_two]

theorem ofLane_eight : K.ofLane 8 = g * (g * g) := by
  rw [show (8 : UInt64) = mulXW 4 by decide, ofLane_mulXW, ofLane_four]

/-- **`ktab` builds the table** of `rbx`. -/
theorem ktab_spec (s : QState) {E : QState → Prop} :
    WP ktab s (fun t ↦ Tab (s.reg .rbx) t.scr ∧ t.reg .rax = s.reg .rax ∧ t.mem = s.mem ∧
      RegsFrame kRegs s t) E := by
  unfold ktab
  fstep
  refine WP.sstore_cons (by decide) ?_
  refine WP.sstore_cons (by decide) ?_
  fstep; fstep; fstep; fstep; fstep; fstep
  refine WP.sstore_cons (by decide) ?_
  fstep; fstep
  refine WP.sstore_cons (by decide) ?_
  fstep; fstep; fstep; fstep; fstep
  refine WP.sstore_cons (by decide) ?_
  fstep; fstep
  refine WP.sstore_cons (by decide) ?_
  iterate 2
    fstep
    refine WP.sload_cons (by simp) ?_
    fstep
    refine WP.sstore_cons (by decide) ?_
  fstep; fstep; fstep; fstep; fstep
  refine WP.sstore_cons (by decide) ?_
  fstep; fstep
  refine WP.sstore_cons (by decide) ?_
  iterate 6
    fstep
    refine WP.sload_cons (by simp) ?_
    fstep
    refine WP.sstore_cons (by decide) ?_
  fdone
  refine ⟨?_, trivial, trivial, by rf_tac⟩
  intro n hn
  interval_cases n <;>
    simp only [QState.setScr_scr, QState.setReg_scr, Nat.reduceEqDiff, ↓reduceIte,
      natLit_toUInt64, natOne_toUInt64, show (0 : Nat).toUInt64 = 0 from rfl, UInt64.reduceToNat,
      mulXW_unfold] <;>
    simp only [ofLane_xor, ofLane_mulXW, ofLane_zero, ofLane_one, ofLane_two, ofLane_four,
      ofLane_eight, show (3 : UInt64) = 2 ^^^ 1 by decide, show (5 : UInt64) = 4 ^^^ 1 by decide,
      show (6 : UInt64) = 4 ^^^ 2 by decide, show (7 : UInt64) = 4 ^^^ 2 ^^^ 1 by decide,
      show (9 : UInt64) = 8 ^^^ 1 by decide, show (10 : UInt64) = 8 ^^^ 2 by decide,
      show (11 : UInt64) = 8 ^^^ 2 ^^^ 1 by decide, show (12 : UInt64) = 8 ^^^ 4 by decide,
      show (13 : UInt64) = 8 ^^^ 4 ^^^ 1 by decide, show (14 : UInt64) = 8 ^^^ 4 ^^^ 2 by decide,
      show (15 : UInt64) = 8 ^^^ 4 ^^^ 2 ^^^ 1 by decide] <;>
    ring

/-- The scratch bank read at a nibble is the table's entry. -/
theorem kinit_spec {s : QState} {a b : UInt64} (ht : Tab b s.scr) (ha : s.reg .rax = a)
    {E : QState → Prop} :
    WP kinit s (fun t ↦ Acc a b 0 (t.reg .rbx) (t.reg .rcx) ∧ t.reg .rax = a ∧ t.scr = s.scr ∧
      t.mem = s.mem ∧ RegsFrame kRegs s t) E := by
  unfold kinit
  fstep; fstep
  refine WP.sload_cons (by
    simp only [QState.setReg_reg, ↓reduceIte, ha]
    exact UInt64.lt_iff_toNat_lt.mpr (shr_lt a (n := 60) (by omega))) ?_
  fstep
  fdone
  refine ⟨?_, ha, trivial, trivial, by rf_tac⟩
  rw [ha]
  exact Acc.init ht

/-- After `m + 1` nibbles of `kmul` from `s`, its table in `t`. -/
def KInv (s t : QState) (m : Nat) (u : QState) : Prop :=
  Acc (s.reg .rax) (s.reg .rbx) m (u.reg .rbx) (u.reg .rcx) ∧ u.reg .rax = s.reg .rax ∧
    u.scr = t.scr ∧ u.mem = s.mem ∧ RegsFrame kRegs s u

/-- **A step keeps the accumulator.** -/
theorem kstep_spec {m : Nat} (hm : m ≤ 14) {s t u : QState} (ht : Tab (s.reg .rbx) t.scr)
    (h : KInv s t m u) {E : QState → Prop} : WP (kstep m) u (KInv s t (m + 1)) E := by
  obtain ⟨hA, ha, hs, hmu, hfu⟩ := h
  unfold kstep
  fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep
  refine WP.sload_cons (by simp only [QState.setReg_reg, ↓reduceIte]; exact and15_lt _) ?_
  fstep
  fdone
  refine ⟨?_, by simp [ha], by simp [hs], by simp [hmu], RegsFrame.trans hfu (by rf_tac)⟩
  simp only [QState.setReg_reg, ↓reduceIte, reduceCtorEq, ha, hs]
  exact Acc.step ht hm hA

/-- **`kred` reduces the accumulator.** -/
theorem kred_spec {s : QState} {a b : UInt64} (hA : Acc a b 15 (s.reg .rbx) (s.reg .rcx))
    {E : QState → Prop} :
    WP kred s (fun t ↦ K.ofLane (t.reg .rax) = K.ofLane a * K.ofLane b ∧ t.mem = s.mem ∧
      RegsFrame kRegs s t) E := by
  unfold kred
  fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep
  fdone
  refine ⟨?_, trivial, by rf_tac⟩
  exact Acc.fold hA

/-- **`kmul` multiplies in `K`.** -/
theorem kmul_spec (s : QState) {E : QState → Prop} :
    WP kmul s (fun s' ↦ K.ofLane (s'.reg .rax) = K.ofLane (s.reg .rax) * K.ofLane (s.reg .rbx) ∧
      s'.mem = s.mem ∧ RegsFrame kRegs s s') E := by
  unfold kmul
  refine WP.then (ktab_spec s) fun t ⟨ht, ha, hm, hf⟩ ↦ ?_
  refine WP.then (kinit_spec ht ha) fun u ⟨hA, ha', hs, hmu, hfu⟩ ↦ ?_
  have h : KInv s t 0 u := ⟨hA, ha', hs, hmu.trans hm, RegsFrame.trans hf hfu⟩
  refine WP.then (kstep_spec (m := 0) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 1) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 2) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 3) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 4) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 5) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 6) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 7) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 8) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 9) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 10) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 11) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 12) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 13) (by decide) ht h) fun u h ↦ ?_
  refine WP.then (kstep_spec (m := 14) (by decide) ht h) fun u h ↦ ?_
  obtain ⟨hA, -, -, hmu, hfu⟩ := h
  exact WP.mono (kred_spec hA) (fun v ⟨h1, h2, h3⟩ ↦ ⟨h1, h2.trans hmu, RegsFrame.trans hfu h3⟩)
    (fun _ h ↦ h)

/-- `rax := rax²` in `K`. -/
def ksq : Stmt := blk [I (.mov .rbx .rax), kmul]

/-- **`ksq` squares in `K`.** -/
theorem ksq_spec (s : QState) {E : QState → Prop} :
    WP ksq s (fun s' ↦ K.ofLane (s'.reg .rax) = K.ofLane (s.reg .rax) ^ 2 ∧
      s'.mem = s.mem ∧ RegsFrame kRegs s s') E := by
  unfold ksq
  fstep
  refine WP.then (kmul_spec _) fun t ⟨h1, h2, h3⟩ ↦ ?_
  fdone
  refine ⟨?_, h2, ?_⟩
  · rw [h1, sq]
    simp
  · exact RegsFrame.trans (by rf_tac) h3

end NativeVm.Field
