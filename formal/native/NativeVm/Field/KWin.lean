module

public import NativeVm.Field.Basic

/-!
# The windowed product's algebra

`kmul` (`NativeVm.Field.K`) multiplies `a · b` four bits of `a` at a time: a table of the sixteen
products `n · b`, `n` a polynomial of degree below four (`Tab`), then, from the top nibble of `a`
down, a 128-bit accumulator in two words `(hi, lo)` shifted by `x^4` and added the entry of the next
nibble, and one reduction of the accumulator at the end. This module proves its algebra in
CompPoly's quotient `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` (`BF64.toQuot`, a ring homomorphism from
`K`): a pair of words stands for the polynomial `hi·x^64 + lo` (`wv`); a step multiplies it by
`x^4` and adds the entry (`wv_step`), while the top `4 (m + 1)` bits of `a` grow by a nibble the same
way (`pw_nib`); the reduction, its high word below `2^60`, is `BF64.reduceWords` and gives the
element of `K` the pair stands for (`toQuot_fold`).
-/

@[expose] public section

namespace NativeVm.Field

open Native LeanVM.Parameters Polynomial BinaryField BF64

/-- The quotient's element of a polynomial over `GF(2)`. -/
local notation "qk" => AdjoinRoot.mk basePoly

/-- The polynomial of a word. -/
noncomputable abbrev pw (w : UInt64) : (ZMod 2)[X] := toPoly w.toBitVec

/-- The polynomial `hi·x^64 + lo` of a pair of words. -/
noncomputable def wv (hi lo : UInt64) : (ZMod 2)[X] := pw hi * X ^ 64 + pw lo

theorem toQuot_ofLane (w : UInt64) : toQuot (K.ofLane w) = qk (pw w) := rfl

theorem pw_xor (a b : UInt64) : pw (a ^^^ b) = pw a + pw b := by
  rw [pw, UInt64.toBitVec_xor, toPoly_xor]

theorem toBitVec_shl (x : UInt64) (n : Nat) (hn : n < 64) :
    (x <<< n.toUInt64).toBitVec = x.toBitVec <<< n := by
  simp [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_umod, Nat.mod_eq_of_lt hn]

theorem toBitVec_shr (x : UInt64) (n : Nat) (hn : n < 64) :
    (x >>> n.toUInt64).toBitVec = x.toBitVec >>> n := by
  simp [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod,
    Nat.mod_eq_of_lt hn]

theorem toNat_shr (x : UInt64) (n : Nat) (hn : n < 64) :
    (x >>> n.toUInt64).toNat = x.toNat / 2 ^ n := by
  rw [← UInt64.toNat_toBitVec, toBitVec_shr x n hn, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, UInt64.toNat_toBitVec]

/-- A word shifted left within its width. -/
theorem pw_shl {x : UInt64} {n d : Nat} (hx : x.toNat < 2 ^ d) (hn : d + n ≤ 64) (h64 : n < 64) :
    pw (x <<< n.toUInt64) = pw x * X ^ n := by
  rw [pw, toBitVec_shl x n h64]
  exact toPoly_shiftLeft_no_overflow _ hx hn

/-- The polynomial of a pair of words. -/
theorem toPoly_wordsToBitVec (hi lo : UInt64) : toPoly (wordsToBitVec (hi, lo)) = wv hi lo := by
  have hh : highHalf (wordsToBitVec (hi, lo)) = hi.toBitVec := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [highHalf, wordsToBitVec, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hk,
      decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hl : lowHalf (wordsToBitVec (hi, lo)) = lo.toBitVec := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [lowHalf, wordsToBitVec, BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append, ite_eq_left hk]
  rw [toPoly_halves, hh, hl, wv]

/-- A word shifted left by four, its four high bits carried into a second word. -/
theorem wv_shl4 (lo : UInt64) : wv (lo >>> 60) (lo <<< 4) = pw lo * X ^ 4 := by
  have h := congrArg toPoly
    (zeroExtendTo_shiftLeft' lo 60 4 (j := 4) (by decide) (by decide) (by omega) (by omega))
  have hlt : (zeroExtendTo (w := 128) lo.toBitVec).toNat < 2 ^ 64 := by
    rw [toNat_zeroExtendTo _ (by omega)]; exact lo.toBitVec.isLt
  rw [toPoly_shiftLeft_no_overflow _ hlt (by omega), toPoly_zeroExtendTo _ (by omega),
    toPoly_wordsToBitVec] at h
  exact h.symm

/-- **A step of the accumulator**: shifted by `x^4`, plus an entry. -/
theorem wv_step {hi : UInt64} (lo t : UInt64) (hhi : hi.toNat < 2 ^ 60) :
    wv ((hi <<< 4) ^^^ (lo >>> 60)) ((lo <<< 4) ^^^ t) = X ^ 4 * wv hi lo + pw t := by
  have h4 : pw (hi <<< 4) = pw hi * X ^ 4 := pw_shl (n := 4) hhi (by omega) (by omega)
  have hlo := wv_shl4 lo
  rw [wv] at hlo
  rw [wv, wv, pw_xor, pw_xor, h4]
  linear_combination hlo

/-- The reduction of a pair whose high word is below `2^60`. -/
theorem fold_eq_reduceWords {hi : UInt64} (lo : UInt64) (hhi : hi.toNat < 2 ^ 60) :
    lo ^^^ hi ^^^ (hi <<< 1) ^^^ (hi <<< 3) ^^^ (hi <<< 4) = reduceWords hi lo := by
  have h0 : ∀ n : Nat, 60 ≤ n → n < 64 → hi >>> n.toUInt64 = 0 := fun n h1 h2 ↦ by
    apply UInt64.toNat_inj.mp
    rw [toNat_shr hi n h2, UInt64.toNat_zero, Nat.div_eq_of_lt]
    exact lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by norm_num) h1)
  have hth : tailHigh hi = 0 := by
    rw [tailHigh, show (63 : UInt64) = (63 : Nat).toUInt64 from rfl,
      show (61 : UInt64) = (61 : Nat).toUInt64 from rfl,
      show (60 : UInt64) = (60 : Nat).toUInt64 from rfl, h0 63 (by omega) (by omega),
      h0 61 (by omega) (by omega), h0 60 (by omega) (by omega)]
    rfl
  rw [reduceWords, hth, show tailLow 0 = 0 from rfl, UInt64.xor_zero, tailLow]
  simp only [UInt64.xor_assoc]

/-- **The reduction gives the element the pair stands for.** -/
theorem toQuot_fold {hi : UInt64} (lo : UInt64) (hhi : hi.toNat < 2 ^ 60) :
    toQuot (K.ofLane (lo ^^^ hi ^^^ (hi <<< 1) ^^^ (hi <<< 3) ^^^ (hi <<< 4))) = qk (wv hi lo) := by
  rw [fold_eq_reduceWords lo hhi, toQuot_ofLane, pw, reduceWords_eq, toPoly_reduce,
    toPoly_wordsToBitVec, AdjoinRoot.mk_eq_mk]
  exact ⟨-(wv hi lo / basePoly), by rw [EuclideanDomain.mod_eq_sub_mul_div]; ring⟩

/-! ## The nibbles of the first factor -/

theorem shr_lt (a : UInt64) {n : Nat} (hn : n < 64) :
    (a >>> n.toUInt64).toNat < 2 ^ (64 - n) := by
  rw [toNat_shr a n hn, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
    show 64 - n + n = 64 by omega]
  exact a.toNat_lt

/-- **The top bits of `a` grow by a nibble**: its top `4 (m + 2)` bits are its top `4 (m + 1)`
times `x^4` plus the next nibble. -/
theorem pw_nib (a : UInt64) {m : Nat} (hm : m ≤ 14) :
    pw (a >>> (56 - 4 * m).toUInt64) =
      X ^ 4 * pw (a >>> (60 - 4 * m).toUInt64) + pw ((a >>> (56 - 4 * m).toUInt64) &&& 15) := by
  have hw : a >>> (56 - 4 * m).toUInt64 =
      ((a >>> (60 - 4 * m).toUInt64) <<< (4 : Nat).toUInt64) ^^^
        ((a >>> (56 - 4 * m).toUInt64) &&& 15) := by
    apply UInt64.toBitVec_inj.mp
    rw [UInt64.toBitVec_xor, UInt64.toBitVec_and, toBitVec_shl _ 4 (by omega),
      toBitVec_shr _ _ (by omega), toBitVec_shr _ _ (by omega)]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have h15 : (15 : UInt64).toBitVec.getLsbD k = decide (k < 4) := by
      rw [show (15 : UInt64).toBitVec = BitVec.ofNat 64 (2 ^ 4 - 1) from rfl,
        BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
      simp [hk]
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, h15, hk, decide_true, Bool.true_and]
    by_cases h : k < 4
    · simp [h]
    · have e : 60 - 4 * m + (k - 4) = 56 - 4 * m + k := by omega
      simp [h, e]
  conv_lhs => rw [hw]
  rw [pw_xor, pw_shl (n := 4) (d := 60) (lt_of_lt_of_le (shr_lt a (by omega))
    (Nat.pow_le_pow_right (by norm_num) (by omega))) (by omega) (by omega)]
  ring

theorem and15_lt (x : UInt64) : x &&& 15 < 16 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_and]
  exact lt_of_le_of_lt (Nat.and_le_right) (by decide)

/-! ## The table and the steps -/

/-- Word `n < 16` of `f` is `n · b` in `K`. -/
def Tab (b : UInt64) (f : Nat → UInt64) : Prop :=
  ∀ n < 16, K.ofLane (f n) = K.ofLane n.toUInt64 * K.ofLane b

theorem Tab.entry {b : UInt64} {f : Nat → UInt64} (h : Tab b f) {w : UInt64} (hw : w < 16) :
    toQuot (K.ofLane (f w.toNat)) = qk (pw w) * toQuot (K.ofLane b) := by
  rw [h w.toNat (UInt64.lt_iff_toNat_lt.mp hw), toQuot_mul, Nat.toUInt64_eq, UInt64.ofNat_toNat]
  rfl

/-- The accumulator after `m + 1` nibbles: `b` times the top `4 (m + 1)` bits of `a`. -/
def Acc (a b : UInt64) (m : Nat) (hi lo : UInt64) : Prop :=
  hi.toNat < 2 ^ (4 * m) ∧
    qk (wv hi lo) = qk (pw (a >>> (60 - 4 * m).toUInt64)) * toQuot (K.ofLane b)

/-- The accumulator after the top nibble: its entry. -/
theorem Acc.init {a b : UInt64} {f : Nat → UInt64} (h : Tab b f) :
    Acc a b 0 0 (f (a >>> (60 : Nat).toUInt64).toNat) := by
  have hlt : a >>> (60 : Nat).toUInt64 < 16 :=
    UInt64.lt_iff_toNat_lt.mpr (shr_lt a (n := 60) (by omega))
  have he := h.entry hlt
  rw [toQuot_ofLane] at he
  have hz : pw 0 = 0 := toPoly_zero_eq_zero
  refine ⟨by decide, ?_⟩
  rw [wv, hz, zero_mul, zero_add]
  exact he

/-- **A step keeps the accumulator**. -/
theorem Acc.step {a b : UInt64} {f : Nat → UInt64} (h : Tab b f) {m : Nat} (hm : m ≤ 14)
    {hi lo : UInt64} (hA : Acc a b m hi lo) :
    Acc a b (m + 1) ((hi <<< 4) ^^^ (lo >>> 60))
      ((lo <<< 4) ^^^ f ((a >>> (56 - 4 * m).toUInt64) &&& 15).toNat) := by
  obtain ⟨hhi, hq⟩ := hA
  have hhi60 : hi.toNat < 2 ^ 60 :=
    lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨?_, ?_⟩
  · rw [UInt64.toNat_xor]
    have h1 : (hi <<< 4).toNat < 2 ^ (4 * (m + 1)) := by
      rw [show (4 : UInt64) = (4 : Nat).toUInt64 from rfl, ← UInt64.toNat_toBitVec,
        toBitVec_shl _ 4 (by omega), BitVec.toNat_shiftLeft, UInt64.toNat_toBitVec,
        Nat.shiftLeft_eq]
      refine lt_of_le_of_lt (Nat.mod_le _ _) ?_
      rw [show 4 * (m + 1) = 4 * m + 4 by ring, pow_add]
      exact Nat.mul_lt_mul_of_pos_right hhi (by norm_num)
    have h2 : (lo >>> 60).toNat < 2 ^ (4 * (m + 1)) := by
      have := shr_lt lo (n := 60) (by omega)
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact Nat.xor_lt_two_pow h1 h2
  · have he := h.entry (and15_lt (a >>> (56 - 4 * m).toUInt64))
    rw [toQuot_ofLane] at he
    rw [wv_step _ _ hhi60, map_add, map_mul, hq, he,
      show 60 - 4 * (m + 1) = 56 - 4 * m by omega, pw_nib a hm, map_add, map_mul]
    ring

/-- **The product**: the accumulator after all sixteen nibbles, reduced. -/
theorem Acc.fold {a b hi lo : UInt64} (hA : Acc a b 15 hi lo) :
    K.ofLane (lo ^^^ hi ^^^ (hi <<< 1) ^^^ (hi <<< 3) ^^^ (hi <<< 4)) = K.ofLane a * K.ofLane b := by
  obtain ⟨hhi, hq⟩ := hA
  apply toQuot_injective
  rw [toQuot_fold lo hhi, hq, toQuot_mul, show (60 - 4 * 15 : Nat).toUInt64 = 0 from rfl,
    UInt64.shiftRight_zero]
  rfl

end NativeVm.Field
