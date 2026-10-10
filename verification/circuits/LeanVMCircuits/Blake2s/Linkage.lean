module

public import LeanVMCircuits.Blake2s.Compress
public import LeanVMCircuits.Gates

@[expose] public section

/-!
What the BLAKE2s Clean circuit lowers to, in closed form.
-/

namespace LeanVMCircuits.Blake2s

open LeanVMCircuits Gates Flock

/-- The carry into bit `i` of a ripple adder whose products start at `n`: the sum of the products below. -/
def carryAffine (n : ℕ) (carry : Affine) : ℕ → Affine
  | 0 => carry
  | i + 1 => .xor (.var (n + i)) (carryAffine n carry i)

def adderSteps (n k : ℕ) (x y : ℕ → Affine) (carry : Affine) : List Step :=
  (List.range k).map fun i =>
    .product (n + i) (.xor (x i) (carryAffine n carry i)) (.xor (y i) (carryAffine n carry i))

def sumAffine (n : ℕ) (x y : ℕ → Affine) (carry : Affine) (i : ℕ) : Affine :=
  .xor (.xor (x i) (carryAffine n carry i)) (y i)

theorem fullAdder_flat (n : ℕ) (input : Var FullAdder.Input Bit) :
    Operations.toFlat (FullAdder.main input n).2 =
      [.witness 1 (.ofFExpr (.expr ((input.x + input.carry) * (input.y + input.carry)))),
        .assert (var ⟨n⟩ - (input.x + input.carry) * (input.y + input.carry))] := by
  simp only [FullAdder.main, circuit_norm]

theorem lower_product (m : ℕ) (w : WitgenIR Bit 1) (a b : Expression Bit) (la lb : Affine)
    (ha : lowerAffine a = .ok la) (hb : lowerAffine b = .ok lb) (ba : la.bounded m) (bb : lb.bounded m) :
    Gates.lower m [.witness 1 w, .assert (var ⟨m⟩ - a * b)] = .ok [.product m la lb] := by
  show Gates.lower m [_, .assert (.add (var ⟨m⟩) (.mul (.const (-1)) (.mul a b)))] = _
  simp [Gates.lower, ha, hb, ba, bb]

theorem lower_define (m : ℕ) (w : WitgenIR Bit 1) (e : Expression Bit) (la : Affine)
    (he : lowerAffine e = .ok la) (ba : la.bounded m) :
    Gates.lower m [.witness 1 w, .assert (var ⟨m⟩ - e)] = .ok [.define m la] := by
  show Gates.lower m [_, .assert (.add (var ⟨m⟩) (.mul (.const (-1)) e))] = _
  cases e with
  | mul a b => simp [lowerAffine] at he
  | _ => simp_all [Gates.lower]

theorem Affine.bounded_mono (a : Affine) {m m' : ℕ} (h : a.bounded m) (hm : m ≤ m') : a.bounded m' := by
  induction a with
  | zero | one => rfl
  | var i => simp [Affine.bounded] at h ⊢; omega
  | xor l r il ir => simp only [Affine.bounded, Bool.and_eq_true] at h ⊢; exact ⟨il h.1, ir h.2⟩

theorem carryAffine_bounded (n : ℕ) (c : Affine) (hc : c.bounded n) (i : ℕ) :
    (carryAffine n c i).bounded (n + i) := by
  induction i with
  | zero => simpa [carryAffine] using hc
  | succ i ih =>
    simp only [carryAffine, Affine.bounded, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, Affine.bounded_mono _ ih (by omega)⟩

theorem toSubcircuit_toFlat {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit Bit Input Output) (n : ℕ) (input : Var Input Bit) :
    (circuit.toSubcircuit n input).ops.toFlat = Operations.toFlat ((circuit.main input) n).2 := by
  simp [FormalCircuit.toSubcircuit, Operations.toNested_toFlat]

theorem adder_lower (k n : ℕ) (x y : Vector (Expression Bit) k) (c : Expression Bit) (ax ay : ℕ → Affine)
    (ac : Affine) (hx : ∀ i (h : i < k), lowerAffine x[i] = .ok (ax i))
    (hy : ∀ i (h : i < k), lowerAffine y[i] = .ok (ay i)) (hc : lowerAffine c = .ok ac)
    (bx : ∀ i, i < k → (ax i).bounded n) (bY : ∀ i, i < k → (ay i).bounded n) (bc : ac.bounded n) :
    Gates.lower n (Operations.toFlat ((Adder.certified k).circuit.main { x, y, carry := c } n).2) =
        .ok (adderSteps n k ax ay ac) ∧
      (∀ i (h : i < k), lowerAffine ((Adder.certified k).circuit.output { x, y, carry := c } n).sum[i] =
        .ok (sumAffine n ax ay ac i)) ∧
      lowerAffine ((Adder.certified k).circuit.output { x, y, carry := c } n).carry = .ok (carryAffine n ac k) := by
  induction k with
  | zero =>
    refine ⟨rfl, fun i h => absurd h (by omega), ?_⟩
    simpa [Adder.certified, Adder.zero, circuit_norm, carryAffine] using hc
  | succ k ih =>
    obtain ⟨hl, hs, hcar⟩ := ih x.pop y.pop (fun i h => by simpa using hx i (by omega))
      (fun i h => by simpa using hy i (by omega)) (fun i h => bx i (by omega)) (fun i h => bY i (by omega))
    have hlen : (Adder.certified k).circuit.localLength { x := x.pop, y := y.pop, carry := c } = k :=
      (FormalCircuitBase.localLength_eq _ _ 0).symm.trans (adder_localLength _ _ 0)
    have hlen' : (Adder.certified k).circuit.elaborated.localLength
        { x := x.pop, y := y.pop, carry := c } = k := hlen
    have hout : (Adder.certified k).circuit.elaborated.output { x := x.pop, y := y.pop, carry := c } n =
        (Adder.certified k).circuit.output { x := x.pop, y := y.pop, carry := c } n := rfl
    simp only [Adder.certified, Adder.step, circuit_norm, FullAdder.circuit]
    rw [hout, hlen']
    have hxk : lowerAffine (x[k] + ((Adder.certified k).circuit.output { x := x.pop, y := y.pop, carry := c } n).carry)
        = .ok (.xor (ax k) (carryAffine n ac k)) := by
      show lowerAffine (.add _ _) = _
      simp [lowerAffine, hx k (by omega), hcar]
    have hyk : lowerAffine (y[k] + ((Adder.certified k).circuit.output { x := x.pop, y := y.pop, carry := c } n).carry)
        = .ok (.xor (ay k) (carryAffine n ac k)) := by
      show lowerAffine (.add _ _) = _
      simp [lowerAffine, hy k (by omega), hcar]
    have hbk := carryAffine_bounded n ac bc k
    refine ⟨?_, ?_, ?_⟩
    · rw [toSubcircuit_toFlat, toSubcircuit_toFlat, Gates.lower_append _ _ _ _ hl, hlen, fullAdder_flat]
      simp only [adderSteps, List.length_map, List.length_range, Nat.add_zero]
      rw [lower_product _ _ _ _ _ _ hxk hyk (by simp [Affine.bounded, Affine.bounded_mono _ (bx k (by omega))
        (Nat.le_add_right n k), hbk]) (by simp [Affine.bounded, Affine.bounded_mono _ (bY k (by omega))
        (Nat.le_add_right n k), hbk])]
      simp [Except.map, List.range_succ]
    · intro i hi
      split
      · rename_i h
        simpa using hs i h
      · have : i = k := by omega
        subst this
        show lowerAffine (.add (.add _ _) _) = _
        simp only [lowerAffine, hx i (by omega), hy i (by omega), hcar, sumAffine]
    · show lowerAffine (.add _ _) = _
      simp [lowerAffine, hcar, carryAffine]

end LeanVMCircuits.Blake2s
