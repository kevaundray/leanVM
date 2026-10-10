module

public import LeanVMCircuits.Flatten

@[expose] public section

namespace LeanVMCircuits.Flock

structure Artifact where
  rows : List Row
  outputs : List Affine
  deriving Repr, DecidableEq

def lowerOutputs : List (Expression Bit) → Except String (List Affine)
  | [] => .ok []
  | expression :: rest =>
    match lowerAffine expression, lowerOutputs rest with
    | .ok affine, .ok affines => .ok (affine :: affines)
    | .error message, _ => .error message
    | _, .error message => .error message

theorem lowerOutputs_correct (expressions : List (Expression Bit)) (affines : List Affine)
    (h : lowerOutputs expressions = .ok affines) (env : Environment Bit) :
    affines.map (Affine.eval env.get) = expressions.map (Expression.eval env) := by
  induction expressions generalizing affines with
  | nil => simp [lowerOutputs] at h; subst affines; rfl
  | cons expression rest ih =>
    cases ha : lowerAffine expression with
    | error message => simp [lowerOutputs, ha] at h
    | ok affine =>
      cases hr : lowerOutputs rest with
      | error message => simp [lowerOutputs, ha, hr] at h
      | ok tail =>
        simp [lowerOutputs, ha, hr] at h
        subst affines
        simp only [List.map_cons, lowerAffine_correct _ _ ha env, ih _ hr]

def inputs (n : ℕ) : Var (WrappingAdder.Input (n + 1)) Bit :=
  { x := Vector.mapRange (n + 1) fun i => var ⟨i⟩,
    y := Vector.mapRange (n + 1) fun i => var ⟨n + 1 + i⟩ }

def source (n : ℕ) := (WrappingAdder.circuit n).toSubcircuit (2 * (n + 1)) (inputs n)

def lowerCircuit (n : ℕ) : Except String Artifact :=
  match flatten 128 (source n).ops with
  | .error message => .error message
  | .ok operations =>
    match lower operations,
        lowerOutputs ((WrappingAdder.circuit n).output (inputs n) (2 * (n + 1))).toList with
    | .ok rows, .ok outputs => .ok { rows, outputs }
    | .error message, _ => .error message
    | _, .error message => .error message

def checked {α : Type} (result : Except String α) (h : result.isOk = true) : α :=
  match result with
  | .ok value => value
  | .error _ => False.elim (by simp only [Except.isOk, Except.toBool, Bool.false_eq_true] at h)

theorem checked_eq {α : Type} (result : Except String α) (h : result.isOk = true) :
    result = .ok (checked result h) := by
  cases result with
  | ok value => rfl
  | error message => simp only [Except.isOk, Except.toBool, Bool.false_eq_true] at h

/-- Checked by reduction in Lean's kernel, not by a native-decision axiom. -/
theorem export64_supported : (lowerCircuit 63).isOk = true := by decide +kernel

def adder64 : Artifact := checked (lowerCircuit 63) export64_supported

theorem adder64_source : lowerCircuit 63 = .ok adder64 := checked_eq _ _

def Artifact.value (artifact : Artifact) (assignment : ℕ → Bit) : ℕ :=
  artifact.outputs.foldr (fun wire acc => (wire.eval assignment).val + 2 * acc) 0

/-- Successful export preserves arbitrary-witness soundness of the exact Clean source. -/
theorem exported_soundness (n : ℕ) (artifact : Artifact)
    (hcode : lowerCircuit n = .ok artifact) (env : Environment Bit)
    (hrows : artifact.rows.Forall (Row.Holds env.get)) :
    artifact.value env.get =
      (Adder.value ((inputs n).x.map (Expression.eval env)) +
        Adder.value ((inputs n).y.map (Expression.eval env))) % 2 ^ (n + 1) := by
  cases hf : flatten 128 (source n).ops with
  | error message => simp [lowerCircuit, hf] at hcode
  | ok operations =>
    cases hr : lower operations with
    | error message => simp [lowerCircuit, hf, hr] at hcode
    | ok rows =>
      cases ho : lowerOutputs ((WrappingAdder.circuit n).output (inputs n) (2 * (n + 1))).toList with
      | error message => simp [lowerCircuit, hf, hr, ho] at hcode
      | ok outputs =>
        simp [lowerCircuit, hf, hr, ho] at hcode
        subst artifact
        have hflat := (lower_correct operations rows hr env).mp hrows
        have hguarantees : FlatOperation.Guarantees env operations := by
          rw [FlatOperation.guarantees_iff_forall_mem, lower_no_interactions _ _ hr]
          simp
        rw [flatten_correct _ _ _ hf] at hflat hguarantees
        have hspec := ((source n).soundness env (by change True; trivial) hflat hguarantees).1
        change WrappingAdder.Spec n (eval env (inputs n))
          (eval env ((WrappingAdder.circuit n).output (inputs n) (2 * (n + 1)))) at hspec
        have hout := lowerOutputs_correct _ _ ho env
        dsimp [Artifact.value, WrappingAdder.Spec, Adder.value] at hspec ⊢
        rw [← List.foldr_map (f := Affine.eval env.get) (g := fun b acc => b.val + 2 * acc), hout]
        simpa only [inputs, circuit_norm, Vector.toList_map] using hspec

theorem adder64_soundness (env : Environment Bit)
    (hrows : adder64.rows.Forall (Row.Holds env.get)) :
    adder64.value env.get =
      (Adder.value ((inputs 63).x.map (Expression.eval env)) +
        Adder.value ((inputs 63).y.map (Expression.eval env))) % 2 ^ 64 :=
  exported_soundness 63 adder64 adder64_source env hrows

theorem adder64_layout :
    adder64.rows.map Row.output = (List.range 63).map (128 + ·) ∧
      adder64.outputs.length = 64 := by decide +kernel

end LeanVMCircuits.Flock
