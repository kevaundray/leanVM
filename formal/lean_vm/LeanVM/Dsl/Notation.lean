/-
  LeanVM.Dsl.Notation

  The guest's surface syntax: field arithmetic on `Ex` written as in the source (`a + b * c`, `x ^ k`, `GEN ^ k`, `a / b`), frame runs and heap buffers indexed as `r[i]` and `p[GEN ^ k]`, stores written `r[i] := e`, and the source's `assert`s.
-/

module

public import LeanVM.Dsl.Fold
public import LeanVM.Dsl.Mem
public import LeanVM.Dsl.Hints
public import LeanVM.Dsl.Keccak

/-!
# The guest's notation

Everything here unfolds to the builder (`Dsl/Builder`, `Dsl/Fold`), so a function written with it emits what the builder calls it abbreviates would, in the same order:

* Arithmetic is `Ex` (`LeanVM.Dsl.Fold`): `a + b`, `a * b`, `a ^ k` (`k` a `Nat`) and `a / b` build an expression that `val` lowers (`Ex.lower`), `fold` binds as an `FW` (`Ex.bind`), and a store writes into its cell (`Ex.into`). Its leaves are coerced: a word is `.w` (a value a product with `g`-powers shifts as a pointer), a numeral or a `Nat` is `Ex.nat` (the source's integer, a `g`-power when it is a power of two), a field constant `E` is `.c`, an `FW` its expression, a `Shifted` pointer `.sh`, a `GPow` its `g`-power, an action `B Word` `.act` (run where the expression is lowered). `GEN ^ k` is the constant `g^k` (`.g k`) and `GEN` is `g`.
* `r[i]` is cell `i` of a frame run `r : List V` (a word); `p[i]` is the heap word at `p` indexed by the expression `i`, read where the expression is lowered: the `g`-power factor of `i` folds into the offset and the rest multiplies the pointer, so `p[GEN ^ k]` is `B.load p k` and `p[GEN ^ k * d]` is `B.load (p · d) k`. A `Shifted` pointer `s` adds its exponent: `s[GEN ^ k]` is `B.load s.base (s.exp + k)`.
* `r[lo:hi]` is the slice of a frame run (cells `lo ..< hi`); a frame run is a Keccak operand or destination as it is (`.cells (.frame r)`, `.frame r`), and a list of words an operand of those words.
* `r[i] := e` writes `e` into the frame cell (`Ex.into`); `p[i] := e` stores it in the heap (`B.store`, the address first).
* Calls of guest functions by name: `call f [a, b]`, `call1 f [a, b]` (one value), `callN f [a, b] n`, the arguments expressions: as the zkDSL lowered a call, the return cells are allocated first, then the arguments are lowered left to right, then the call is emitted. `callWith` and `callShapedWith` take the arguments as an action (`argsOf` for runs among them).
* `assert a == b` (`B.assertEq`), `assert a != b` (`B.assertNe`), `assert log x < n` (a range check at the constant bound `n`: the bound set first, then `x` lowered, `B.rangeCheckK`).
-/

namespace LeanVM.Dsl

open LeanVM.Parameters LeanVM.Core

@[expose] public section

/-- A constant `g^exp` bound to a name: no value until it is used. -/
structure GPow where
  exp : Nat
  deriving Inhabited

/-- Its value. -/
def GPow.fe (g : GPow) : E := gpowE g.exp

/-- A shifted pointer `base·g^exp` bound to a name: materialized where it is used (`B.shifted`). -/
structure Shifted where
  base : Word
  exp : Nat
  deriving Inhabited

/-- A word as a pointer shifted by `0`: where a name is a word in some instances and a shifted pointer in others, it is written as the pointer (`B.shifted p 0` is `p`). -/
def Shifted.of (w : Word) : Shifted := ⟨w, 0⟩

instance : Add Ex := ⟨Ex.add⟩
instance : Mul Ex := ⟨Ex.mul⟩
instance : HPow Ex Nat Ex := ⟨Ex.pow⟩
instance {n : Nat} : OfNat Ex n := ⟨Ex.nat n⟩
instance : NatCast Ex := ⟨Ex.nat⟩
instance {τ : Ty} : CoeOut (Var τ) Ex := ⟨fun x => .w ⟨x.v⟩⟩
instance : Coe FW Ex := ⟨FW.ex⟩
instance : Coe E Ex := ⟨Ex.c⟩
instance : Coe Shifted Ex := ⟨fun p => .sh p.base p.exp⟩
instance : Coe GPow Ex := ⟨fun g => .g g.exp⟩
instance : Coe (B Word) Ex := ⟨Ex.act⟩

/-- Field division (`B.fdiv`), the operands lowered left to right where the quotient is. -/
instance : Div Ex := ⟨fun a b => .act do B.fdiv (← a.lower) (← b.lower)⟩

/-- The generator `g`. `GEN ^ k` is the constant `g^k` (`Ex.g k`), which shifts a pointer it multiplies, not a power of `GEN`. -/
def GEN : Ex := .g 1

macro_rules
  | `($x ^ $k) => do
      unless x.raw.isIdent && x.raw.getId == `GEN do Lean.Macro.throwUnsupported
      `(Ex.g $k)

/-- An expression's value (`Ex.lower`). -/
abbrev val (e : Ex) : B Word := e.lower

/-- An expression as an `FW` (`Ex.bind`): a constant stays one, emitting nothing. -/
abbrev fold (e : Ex) : B FW := e.bind

/-- Cell `i` of a frame run, as a word. -/
scoped instance (priority := high) : GetElem (List V) Nat Word (fun _ _ => True) :=
  ⟨fun r i _ => ⟨r.getD i default⟩⟩

/-- Cells `lo ..< hi` of a frame run. -/
def runSlice (r : List V) (lo hi : Nat) : List V := (r.drop lo).take (hi - lo)

scoped macro_rules
  | `($r[$lo : $hi]) => `(runSlice $r $lo $hi)

instance : Coe (List V) Operand := ⟨fun vs => .cells (.frame vs)⟩
instance : Coe (List V) Cells := ⟨.frame⟩
instance : Coe (List Word) Operand := ⟨fun ws => .words (ws.map fun w => .cell w.v)⟩

/-- A heap index split as the zkDSL's lowering folds it: the exponent of its `g`-power factor, and the rest. -/
def Ex.split : Ex → Nat × Option Ex
  | .g k => (k, none)
  | .sh p k => (k, some (.w p))
  | .mul (.g k) r => (k, some r)
  | .mul r (.g k) => (k, some r)
  | i => (0, some i)

/-- The address `base·g^exp` indexed by `i`: the pointer (an action when `i` has a runtime part, which multiplies `base`) and the offset. -/
def heapAt (base : Word) (exp : Nat) (i : Ex) : B Word × Nat :=
  match i.split with
  | (k, none) => (pure base, exp + k)
  | (k, some r) => (do B.mul base (← r.lower), exp + k)

/-- What a heap index applies to: a word, or a shifted pointer. -/
class HeapPtr (α : Type) where
  addr : α → Ex → B Word × Nat

instance {τ : Ty} : HeapPtr (Var τ) := ⟨fun p i => heapAt ⟨p.v⟩ 0 i⟩
instance : HeapPtr Shifted := ⟨fun p i => heapAt p.base p.exp i⟩

/-- What indexes the heap: an expression, a word, or a shifted pointer. -/
class HeapIdx (ι : Type) where
  ex : ι → Ex

instance : HeapIdx Ex := ⟨id⟩
instance {τ : Ty} : HeapIdx (Var τ) := ⟨fun x => .w ⟨x.v⟩⟩
instance : HeapIdx Shifted := ⟨fun p => .sh p.base p.exp⟩

/-- The heap word at `p` indexed by `i`, read where the expression is lowered. -/
instance {α ι : Type} [HeapPtr α] [HeapIdx ι] : GetElem α ι Ex (fun _ _ => True) :=
  ⟨fun p i _ => let a := HeapPtr.addr p (HeapIdx.ex i); .ld a.1 a.2⟩

/-- A destination `x[i] := e` writes. -/
class Store (α ι : Type) where
  store : α → ι → Ex → B Unit

instance : Store (List V) Nat := ⟨fun r i e => e.into (⟨r.getD i default⟩ : Word)⟩
instance {α ι : Type} [HeapPtr α] [HeapIdx ι] : Store α ι := ⟨fun p i e => do
  let a := HeapPtr.addr p (HeapIdx.ex i)
  let q ← a.1
  B.store q a.2 (← e.lower)⟩

/-- `x[i] := e`: a frame cell or a heap word written (`Store`). -/
syntax (name := storeElem) (priority := high) ident noWs "[" term "]" " := " term : doElem

macro_rules (kind := storeElem)
  | `(doElem| $x:ident[$i] := $e) => `(doElem| Store.store $x $i $e)

/-- The values of call arguments, lowered left to right. -/
def args (es : List Ex) : B (List V) := es.mapM fun e => do return (← e.lower).v

/-- A call argument: a scalar, or a frame run passed as its cells. -/
inductive Arg where
  | ex (e : Ex)
  | run (r : List V)

/-- The values of call arguments, lowered left to right, a run's cells as they are. -/
def argsOf (as : List Arg) : B (List V) := do
  let vs ← as.mapM fun
    | .ex e => do return [(← e.lower).v]
    | .run r => pure r
  return vs.flatten

/-- A call of `f` returning values of the shapes `shapes`: their cells allocated first, a fresh cell per scalar and a fresh run per `StackBuf`, then the arguments `as` computes, then the call; the cells per value. -/
def callShapedWith (f : String) (as : B (List V)) (shapes : List Shape) : B (List (List V)) := do
  let rets ← shapes.mapM fun
    | .scalar => do return [← B.fresh]
    | .buf n => B.freshRun n
  let vs ← as
  B.emit (.call f vs rets.flatten)
  return rets

/-- A call of `f` returning `n` values: their cells allocated first, then the arguments `as` computes, then the call. -/
def callWith (f : String) (as : B (List V)) (n : Nat) : B (List Word) := do
  let rets ← (List.range n).mapM fun _ => B.fresh
  let vs ← as
  B.emit (.call f vs rets)
  return rets.map Var.mk

/-- A call of `f` returning nothing, on the expressions `as`. -/
def call (f : String) (as : List Ex) : B Unit := do
  let _ ← callWith f (args as) 0

/-- A call of `f` returning one value, on the expressions `as`. -/
def call1 (f : String) (as : List Ex) : B Word := do
  return (← callWith f (args as) 1).headD default

/-- A call of `f` returning `n` values, on the expressions `as`. -/
def callN (f : String) (as : List Ex) (n : Nat) : B (List Word) := callWith f (args as) n

/-- `assert log x < n`: `x = g^k` with `k < n`, at a constant bound (`B.rangeCheckK`, its bound set first). -/
def assertLog (x : Ex) (n : Nat) : B Unit := do
  let k ← B.const (gpowE (n - 1))
  let _ ← B.rangeCheckK (← x.lower) k

/-- The source's `assert`: `a == b`, `a != b`, `log x < n`. -/
syntax (name := assertElem) (priority := high) "assert " term : doElem

macro_rules (kind := assertElem)
  | `(doElem| assert $a == $b) => `(doElem| B.assertEq (← val $a) (← val $b))
  | `(doElem| assert $a != $b) => `(doElem| B.assertNe (← val $a) (← val $b))
  | `(doElem| assert log $x < $n) => `(doElem| assertLog $x $n)

end
end LeanVM.Dsl
