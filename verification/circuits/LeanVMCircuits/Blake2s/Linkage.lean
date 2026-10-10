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

theorem certified_localLength (k : ℕ) (input : Var (Adder.Input k) Bit) :
    (Adder.certified k).circuit.localLength input = k :=
  (FormalCircuitBase.localLength_eq _ _ 0).symm.trans (adder_localLength _ _ 0)

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

theorem wrapping_lower (m n : ℕ) (x y : Vector (Expression Bit) (m + 1)) (ax ay : ℕ → Affine)
    (hx : ∀ i (h : i < m + 1), lowerAffine x[i] = .ok (ax i))
    (hy : ∀ i (h : i < m + 1), lowerAffine y[i] = .ok (ay i))
    (bx : ∀ i, i < m + 1 → (ax i).bounded n) (bY : ∀ i, i < m + 1 → (ay i).bounded n) :
    Gates.lower n (Operations.toFlat ((WrappingAdder.circuit m).main { x, y } n).2) =
        .ok (adderSteps n m ax ay .zero) ∧
      ∀ i (h : i < m + 1), lowerAffine ((WrappingAdder.circuit m).output { x, y } n)[i] =
        .ok (sumAffine n ax ay .zero i) := by
  obtain ⟨hl, hs, hcar⟩ := adder_lower m n x.pop y.pop 0 ax ay .zero
    (fun i h => by simpa using hx i (by omega)) (fun i h => by simpa using hy i (by omega)) rfl
    (fun i h => bx i (by omega)) (fun i h => bY i (by omega)) rfl
  refine ⟨?_, ?_⟩
  · simp only [WrappingAdder.circuit, WrappingAdder.main, circuit_norm]
    rw [toSubcircuit_toFlat]
    exact hl
  · intro i hi
    simp only [WrappingAdder.circuit, WrappingAdder.main, circuit_norm, Adder.circuit]
    split
    · rename_i h
      exact hs i h
    · have : i = m := by omega
      subst this
      show lowerAffine (.add (.add _ _) _) = _
      simp only [lowerAffine, hx i (by omega), hy i (by omega)]
      erw [hcar]
      rfl

def defines (n k : ℕ) (a : ℕ → Affine) : List Step := (List.range k).map fun i => .define (n + i) (a i)

theorem toFlat_append (a b : Operations Bit) : Operations.toFlat (a ++ b) = a.toFlat ++ b.toFlat := by
  induction a with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [Operations.toFlat, ih]

theorem defines_succ (n k : ℕ) (a : ℕ → Affine) :
    defines n (k + 1) a = defines n k a ++ [.define (n + k) (a k)] := by
  simp [defines, List.range_succ]

theorem defineAll_lower (n k : ℕ) (g : Fin k → Expression Bit) (a : ℕ → Affine)
    (hg : ∀ i : Fin k, lowerAffine (g i) = .ok (a i.val)) (ba : ∀ i, i < k → (a i).bounded n) :
    Gates.lower n (Operations.toFlat (List.ofFn fun i : Fin k =>
      [Operation.witness 1 (Witgen.WitgenIR.ofFExpr (Witgen.FExpr.expr (g i))),
        Operation.assert (var ⟨n + i.val * 1⟩ - g i)]).flatten) = .ok (defines n k a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ_last, List.flatten_append, toFlat_append]
    simp only [Fin.val_castSucc]
    rw [Gates.lower_append _ _ _ _ (ih (fun i => g i.castSucc) (fun i => hg i.castSucc) (fun i h => ba i (by omega)))]
    have hlen : (defines n k a).length = k := by simp [defines]
    rw [hlen, defines_succ]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, Operations.toFlat, Fin.val_last, Nat.mul_one]
    rw [lower_define _ _ _ _ (hg (Fin.last k)) (Affine.bounded_mono _ (ba k (by omega)) (by omega))]
    rfl

theorem define_output (e : Vector (Expression Bit) 32) (m i : ℕ) (hi : i < 32) :
    ((Define.main e) m).1[i] = var ⟨m + i⟩ := by
  simp [Define.main, defineBit, circuit_norm]

theorem define_lower (n : ℕ) (e : Vector (Expression Bit) 32) (a : ℕ → Affine)
    (he : ∀ i (h : i < 32), lowerAffine e[i] = .ok (a i)) (ba : ∀ i, i < 32 → (a i).bounded n) :
    Gates.lower n (Operations.toFlat ((Define.main e) n).2) = .ok (defines n 32 a) ∧
      ∀ i (h : i < 32), (Define.circuit.output e n)[i] = var ⟨n + i⟩ := by
  refine ⟨?_, ?_⟩
  · simp only [Define.main, Circuit.map.operations_eq, defineBit, circuit_norm]
    exact defineAll_lower n 32 (fun i => e[i.val]) a (fun i => he i.val i.isLt) ba
  · intro i h
    simp [Define.circuit, Define.main, defineBit, circuit_norm]

abbrev Affs := List (Vector Affine 32)

/-- Bit `i` of register `r`, a structural zero past the registers, as the lowering names it. -/
def affGet (affs : Affs) (r i : ℕ) : Affine :=
  if h : i < 32 then (affs.getD r (Vector.replicate 32 .zero))[i] else .zero

def literalAffine {w : ℕ} (k : BitVec w) (i : ℕ) : Affine := if k.getLsbD i then .one else .zero

/-- An operation's steps, at its first variable `n`, on the registers' affine bits. -/
def Op.steps (affs : Affs) (n : ℕ) : Op → List Step
  | .add x y =>
    adderSteps n 31 (affGet affs x) (affGet affs y) .zero ++
      defines (n + 31) 32 (sumAffine n (affGet affs x) (affGet affs y) .zero)
  | .addOdd k y =>
    adderSteps n 31 (literalAffine k) (affGet affs y) .zero ++
      defines (n + 31) 32 (sumAffine n (literalAffine k) (affGet affs y) .zero)
  | .addEven k y =>
    adderSteps n 30 (literalAffine (BitVec.ofNat 31 (k.toNat / 2))) (fun i => affGet affs y (i + 1)) .zero ++
      defines (n + 30) 32 fun i => if i = 0 then affGet affs y 0 else
        sumAffine n (literalAffine (BitVec.ofNat 31 (k.toNat / 2))) (fun i => affGet affs y (i + 1)) .zero (i - 1)
  | .xorRotr r x y =>
    defines n 32 fun i => .xor (affGet affs x ((i + r.val) % 32)) (affGet affs y ((i + r.val) % 32))

/-- The registers' bits lower to `affs`, every one naming only variables below `n`. -/
def Rel (registers : List Reg) (affs : Affs) (n : ℕ) : Prop :=
  registers.length = affs.length ∧
    ∀ r i (h : i < 32), lowerAffine (get registers r)[i] = .ok (affGet affs r i) ∧ (affGet affs r i).bounded n

theorem sumAffine_bounded (n m : ℕ) (x y : ℕ → Affine) (i : ℕ) (hi : i ≤ m) (hx : (x i).bounded n)
    (hy : (y i).bounded n) : (sumAffine n x y .zero i).bounded (n + m) := by
  simp only [sumAffine, Affine.bounded, Bool.and_eq_true]
  exact ⟨⟨Affine.bounded_mono _ hx (by omega),
    Affine.bounded_mono _ (carryAffine_bounded n .zero rfl i) (by omega)⟩, Affine.bounded_mono _ hy (by omega)⟩

theorem add_lower (registers : List Reg) (affs : Affs) (n x y : ℕ) (h : Rel registers affs n) :
    Gates.lower n (Operations.toFlat (((Op.add x y).circuit registers) n).2) = .ok ((Op.add x y).steps affs n) ∧
      ∀ i (hi : i < 32), (((Op.add x y).circuit registers).output n)[i] = var ⟨n + 31 + i⟩ := by
  have hlen : ∀ (input : Var (WrappingAdder.Input 32) Bit),
      (WrappingAdder.circuit 31).elaborated.localLength input = 31 := by
    intro input
    rw [show (WrappingAdder.circuit 31).elaborated.localLength input =
      ((WrappingAdder.circuit 31).main input).localLength 0 from (FormalCircuitBase.localLength_eq _ _ 0).symm]
    simp only [WrappingAdder.circuit, WrappingAdder.main, circuit_norm, Adder.circuit]
    exact certified_localLength _ _
  have hflat : Operations.toFlat (((Op.add x y).circuit registers) n).2 =
      Operations.toFlat ((WrappingAdder.circuit 31).main { x := get registers x, y := get registers y } n).2 ++
      Operations.toFlat ((Define.main ((WrappingAdder.circuit 31).output
        { x := get registers x, y := get registers y } n)) (n + 31)).2 := by
    simp only [Op.circuit, Add32.circuit, circuit_norm]
    rw [toSubcircuit_toFlat]
    simp only [Add32.main, circuit_norm]
    rw [toSubcircuit_toFlat, toSubcircuit_toFlat, show (WrappingAdder.circuit 31).localLength
      { x := get registers x, y := get registers y } = 31 from hlen _]
    rfl
  obtain ⟨_, hrel⟩ := h
  have hW := wrapping_lower 31 n (get registers x) (get registers y) (affGet affs x) (affGet affs y)
    (fun i hi => (hrel x i hi).1) (fun i hi => (hrel y i hi).1) (fun i hi => (hrel x i hi).2)
    (fun i hi => (hrel y i hi).2)
  have hD := define_lower (n + 31) ((WrappingAdder.circuit 31).output
      { x := get registers x, y := get registers y } n) (sumAffine n (affGet affs x) (affGet affs y) .zero)
    (fun i hi => hW.2 i hi)
    (fun i hi => sumAffine_bounded n 31 _ _ i (by omega) (hrel x i hi).2 (hrel y i hi).2)
  refine ⟨?_, ?_⟩
  · rw [hflat, Gates.lower_append _ _ _ _ hW.1]
    have : (adderSteps n 31 (affGet affs x) (affGet affs y) .zero).length = 31 := by simp [adderSteps]
    rw [this, hD.1]
    rfl
  · intro i hi
    simp only [Op.circuit, Add32.circuit, circuit_norm]
    rw [define_output]
    congr 2

theorem lower_literal {w : ℕ} (k : BitVec w) (i : ℕ) (hi : i < w) :
    lowerAffine (literal k : Vector (Expression Bit) w)[i] = .ok (literalAffine k i) := by
  simp only [literal, Vector.getElem_ofFn, literalAffine]
  split <;> rfl

theorem literalAffine_bounded {w : ℕ} (k : BitVec w) (i n : ℕ) : (literalAffine k i).bounded n := by
  unfold literalAffine; split <;> rfl

theorem wrapping31_localLength (input : Var (WrappingAdder.Input 32) Bit) :
    (WrappingAdder.circuit 31).localLength input = 31 := by
  rw [show (WrappingAdder.circuit 31).localLength input =
    ((WrappingAdder.circuit 31).main input).localLength 0 from (FormalCircuitBase.localLength_eq _ _ 0).symm]
  simp only [WrappingAdder.circuit, WrappingAdder.main, circuit_norm, Adder.circuit]
  exact certified_localLength _ _

theorem wrapping30_localLength (input : Var (WrappingAdder.Input 31) Bit) :
    (WrappingAdder.circuit 30).localLength input = 30 := by
  rw [show (WrappingAdder.circuit 30).localLength input =
    ((WrappingAdder.circuit 30).main input).localLength 0 from (FormalCircuitBase.localLength_eq _ _ 0).symm]
  simp only [WrappingAdder.circuit, WrappingAdder.main, circuit_norm, Adder.circuit]
  exact certified_localLength _ _

theorem addOdd_lower (registers : List Reg) (affs : Affs) (n : ℕ) (k : Word) (y : ℕ) (h : Rel registers affs n) :
    Gates.lower n (Operations.toFlat (((Op.addOdd k y).circuit registers) n).2) =
        .ok ((Op.addOdd k y).steps affs n) ∧
      ∀ i (hi : i < 32), (((Op.addOdd k y).circuit registers).output n)[i] = var ⟨n + 31 + i⟩ := by
  have hflat : Operations.toFlat (((Op.addOdd k y).circuit registers) n).2 =
      Operations.toFlat ((WrappingAdder.circuit 31).main { x := literal k, y := get registers y } n).2 ++
      Operations.toFlat ((Define.main ((WrappingAdder.circuit 31).output
        { x := literal k, y := get registers y } n)) (n + 31)).2 := by
    simp only [Op.circuit, AddOdd.circuit, circuit_norm]
    rw [toSubcircuit_toFlat]
    simp only [AddOdd.main, circuit_norm]
    rw [toSubcircuit_toFlat, toSubcircuit_toFlat, wrapping31_localLength]
    rfl
  obtain ⟨_, hrel⟩ := h
  have hW := wrapping_lower 31 n (literal k) (get registers y) (literalAffine k) (affGet affs y)
    (fun i hi => lower_literal k i hi) (fun i hi => (hrel y i hi).1) (fun i _ => literalAffine_bounded k i n)
    (fun i hi => (hrel y i hi).2)
  have hD := define_lower (n + 31) ((WrappingAdder.circuit 31).output
      { x := literal k, y := get registers y } n) (sumAffine n (literalAffine k) (affGet affs y) .zero)
    (fun i hi => hW.2 i hi)
    (fun i hi => sumAffine_bounded n 31 _ _ i (by omega) (literalAffine_bounded k i n) (hrel y i hi).2)
  refine ⟨?_, ?_⟩
  · rw [hflat, Gates.lower_append _ _ _ _ hW.1]
    have : (adderSteps n 31 (literalAffine k) (affGet affs y) .zero).length = 31 := by simp [adderSteps]
    rw [this, hD.1]
    rfl
  · intro i hi
    simp only [Op.circuit, AddOdd.circuit, circuit_norm]
    rw [define_output]
    congr 2

theorem addEven_lower (registers : List Reg) (affs : Affs) (n : ℕ) (k : Word) (y : ℕ) (h : Rel registers affs n) :
    Gates.lower n (Operations.toFlat (((Op.addEven k y).circuit registers) n).2) =
        .ok ((Op.addEven k y).steps affs n) ∧
      ∀ i (hi : i < 32), (((Op.addEven k y).circuit registers).output n)[i] = var ⟨n + 30 + i⟩ := by
  set q : BitVec 31 := BitVec.ofNat 31 (k.toNat / 2)
  have hflat : Operations.toFlat (((Op.addEven k y).circuit registers) n).2 =
      Operations.toFlat ((WrappingAdder.circuit 30).main { x := literal q, y := upper (get registers y) } n).2 ++
      Operations.toFlat ((Define.main (consLow (get registers y)[0] ((WrappingAdder.circuit 30).output
        { x := literal q, y := upper (get registers y) } n))) (n + 30)).2 := by
    simp only [Op.circuit, AddEven.circuit, circuit_norm]
    rw [toSubcircuit_toFlat]
    simp only [AddEven.main, circuit_norm]
    rw [toSubcircuit_toFlat, toSubcircuit_toFlat, wrapping30_localLength]
    rfl
  obtain ⟨_, hrel⟩ := h
  have hW := wrapping_lower 30 n (literal q) (upper (get registers y)) (literalAffine q)
    (fun i => affGet affs y (i + 1))
    (fun i hi => lower_literal q i hi) (fun i hi => by simpa [upper] using (hrel y (i + 1) (by omega)).1)
    (fun i _ => literalAffine_bounded q i n) (fun i hi => (hrel y (i + 1) (by omega)).2)
  have hD := define_lower (n + 30) (consLow (get registers y)[0] ((WrappingAdder.circuit 30).output
      { x := literal q, y := upper (get registers y) } n)) (fun i => if i = 0 then affGet affs y 0 else
        sumAffine n (literalAffine q) (fun i => affGet affs y (i + 1)) .zero (i - 1))
    (fun i hi => by
      rcases i with _ | i
      · simpa [consLow] using (hrel y 0 (by omega)).1
      · simpa [consLow] using hW.2 i (by omega))
    (fun i hi => by
      rcases i with _ | i
      · simpa using Affine.bounded_mono _ (hrel y 0 (by omega)).2 (by omega)
      · simpa using sumAffine_bounded n 30 _ _ i (by omega) (literalAffine_bounded q i n)
          (hrel y (i + 1) (by omega)).2)
  refine ⟨?_, ?_⟩
  · rw [hflat, Gates.lower_append _ _ _ _ hW.1]
    have : (adderSteps n 30 (literalAffine q) (fun i => affGet affs y (i + 1)) .zero).length = 30 := by
      simp [adderSteps]
    rw [this, hD.1]
    rfl
  · intro i hi
    simp only [Op.circuit, AddEven.circuit, circuit_norm]
    rw [define_output]
    congr 2

theorem xorRotr_lower (registers : List Reg) (affs : Affs) (n : ℕ) (r : Fin 32) (x y : ℕ)
    (h : Rel registers affs n) :
    Gates.lower n (Operations.toFlat (((Op.xorRotr r x y).circuit registers) n).2) =
        .ok ((Op.xorRotr r x y).steps affs n) ∧
      ∀ i (hi : i < 32), (((Op.xorRotr r x y).circuit registers).output n)[i] = var ⟨n + i⟩ := by
  obtain ⟨_, hrel⟩ := h
  have hD := define_lower n (rotr (xorBits (get registers x) (get registers y)) r.val)
    (fun i => .xor (affGet affs x ((i + r.val) % 32)) (affGet affs y ((i + r.val) % 32)))
    (fun i hi => by
      simp only [rotr, xorBits, Vector.getElem_ofFn, Vector.getElem_zipWith]
      show lowerAffine (.add _ _) = _
      simp [lowerAffine, (hrel x _ (Nat.mod_lt _ (by omega))).1, (hrel y _ (Nat.mod_lt _ (by omega))).1])
    (fun i hi => by
      simp [Affine.bounded, (hrel x _ (Nat.mod_lt _ (by omega))).2, (hrel y _ (Nat.mod_lt _ (by omega))).2])
  refine ⟨?_, ?_⟩
  · simp only [Op.circuit, XorRotr.circuit, circuit_norm]
    rw [toSubcircuit_toFlat]
    simp only [XorRotr.main, circuit_norm]
    rw [toSubcircuit_toFlat]
    exact hD.1
  · intro i hi
    simp only [Op.circuit, XorRotr.circuit, circuit_norm]
    rw [define_output]

end LeanVMCircuits.Blake2s
