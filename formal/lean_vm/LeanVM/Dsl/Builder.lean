/-
  LeanVM.Dsl.Builder

  The guest language embedded in Lean: a guest function is a term of the builder monad `B`, and
  elaborating it gives the back end's input, a core function with its allocation trace
  (`Compiler.TracedFn`), without a source text, a parser or `Expand`.
-/

module

public import LeanVM.Core
public import LeanVM.Core.Word
public import LeanVM.Compiler.Unnamed
public import LeanVM.Compiler.Pooled
public import LeanVM.Compiler.Joined

/-!
# The builder

A guest function is a Lean function from its parameters' values to an action of `B`, which
appends core statements (`Core.Stmt`) and records the allocation trace as it runs. What the zkDSL
decides at compile time is Lean evaluation here:

* a compile-time parameter (`Const`) is a Lean argument, and a function called with one is a Lean
  family of guest functions (`GFn`), one per argument, named as the zkDSL names a specialization;
* `unroll` is a Lean loop (`List.forM` over a range), and `@inline` is an ordinary Lean function
  returning a `B` action, which emits into its caller's frame;
* a compile-time integer or field constant is a Lean `Nat` or `E`, folded by Lean, so nothing is
  bound virtually and no `+` means an integer sum in one place and `XOR` in another.

A runtime value is a core value `V`, carried as `Var τ`, whose type `τ` names the fact the
program logic (`LeanVM.Dsl.Logic`) proves of it from the statements emitted: a word, a bit, a
power of `g` with a bounded log, an element of `K`. A hint's outputs are `Hinted`: no primitive
takes them as a typed value until a check turns them into one (`assertBit`), so an unchecked hint
cannot reach a use that needs a fact. Runtime control is the core IR's: `match` and fused
`dispatch` on a selector, calls, and `mul_range` loops lifted to helper functions (`loopConst`,
`loopRt`) that take their captured values explicitly.

Each fresh value is `⟨[], t, k⟩` for the `t`-th allocation (`t ≥ 1`), so it never meets a
parameter (`V.param k = ⟨[], 0, k⟩`). The trace records each allocation with the `Kind` the
expansion gives the same construct, and the elaborated function goes through the same three
marking passes as an expanded one (`Compiler.markUnnamedLines`, `markPooledLines`,
`markJoinedLines`).
-/

namespace LeanVM.Dsl

open LeanVM.Parameters LeanVM.Core LeanVM.Compiler
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- A function elaborated, and its source lines (`(n, line)`: the statement at `line` begun when
the trace held `n` events). -/
abbrev Elab := TracedFn × Array (Nat × Nat)

/-- The elaboration state of one function. -/
structure St where
  /-- The tag of the next allocation. -/
  tag : Nat := 1
  out : Array Stmt := #[]
  trace : Array Event := #[]
  lines : Array (Nat × Nat) := #[]
  /-- A hint emitted since the last instruction. -/
  pending : Bool := false
  /-- The function's name, which its loop helpers' names extend. -/
  name : String := ""
  /-- The loop helpers made so far, in order. -/
  helpers : Array Elab := #[]
  deriving Inhabited

/-- The builder. -/
abbrev B := StateM St

/-- What the program logic proves of a value. -/
inductive Ty where
  | word
  | bit
  /-- `g^k` for some `k < n`. -/
  | gpow (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A runtime value of type `τ`. -/
structure Var (τ : Ty) where
  v : V
  deriving DecidableEq, Repr, Inhabited

/-- A word. -/
abbrev Word := Var .word

/-- A value a hint wrote: no fact holds of it until a check gives one. -/
structure Hinted where
  v : V
  deriving DecidableEq, Repr, Inhabited

/-- Any value, seen as a word. -/
def Var.word {τ : Ty} (x : Var τ) : Word := ⟨x.v⟩

/-- A returned value: a value, or a constant set into the return area. -/
inductive Ret where
  | v (x : V)
  | c (e : E)
  deriving Inhabited

/-- The word a returned value holds. -/
def Ret.eval (σ : Val) : Ret → E
  | .v x => σ x
  | .c e => e

namespace B

/-! ## Values, statements, the trace -/

/-- A fresh value (`Expand.fresh`). -/
def fresh (k : Kind := .cell) : B V := modifyGet fun st =>
  (⟨[], st.tag, 0⟩, { st with tag := st.tag + 1, trace := st.trace.push (.alloc [⟨[], st.tag, 0⟩] k) })

/-- `n` fresh consecutive values (`Expand.freshRun`). -/
def freshRun (n : Nat) (k : Kind := .cell) : B (List V) := modifyGet fun st =>
  let run := (List.range n).map fun i => (⟨[], st.tag, i⟩ : V)
  (run, { st with tag := st.tag + 1, trace := st.trace.push (.alloc run k) })

/-- Emit a statement: it carries instructions, so a pending hint fires on it. -/
def emit (s : Stmt) : B Unit := modify fun st =>
  { st with out := st.out.push s, pending := false, trace := st.trace.push .emit }

/-- Emit an atom. -/
def atom (a : Atom) : B Unit := emit (.atom a)

/-- Emit a hint, pending until the next instruction. -/
def hint (h : Hint) : B Unit := modify fun st =>
  { st with out := st.out.push (.atom (.hint h)), pending := true, trace := st.trace.push .emit }

/-- Record a trace event. -/
def event (e : Event) : B Unit := modify fun st => { st with trace := st.trace.push e }

/-- The statements from here on come from source line `l`. -/
def line (l : Nat) : B Unit := modify fun st => { st with lines := st.lines.push (st.trace.size, l) }

/-- The anchor a hint pending at the end of a block gets (`Expand.anchor`). -/
def anchor : B Unit := do
  let o ← fresh
  atom (.const o 0)

/-- Run `m` as a block of its own: its statements are returned, not appended, between an `enter`
and a `leave` event, with an anchor for a hint left pending (`Expand.branch`). -/
def block {α : Type} (m : B α) : B (α × List Stmt) := do
  let st ← get
  set { st with out := #[], pending := false }
  event .enter
  let a ← m
  if (← get).pending then anchor
  event .leave
  let st' ← get
  set { st' with out := st.out, pending := st.pending }
  return (a, st'.out.toList)

/-! ## Arithmetic -/

/-- A constant (`Expand.constCell`). -/
def const (c : E) : B Word := do
  let o ← fresh .pooled
  atom (.const o c)
  return ⟨o⟩

/-- `g^e`. -/
def gconst (e : Nat) : B (Var (.gpow (e + 1))) := do
  let o ← fresh .pooled
  atom (.const o (gen ^ e))
  return ⟨o⟩

/-- `a + b` (`XOR`) into a fresh value (`Expand.pureAdd`). -/
def add {σ τ : Ty} (a : Var σ) (b : Var τ) : B Word := do
  let o ← fresh .pooled
  atom (.add o a.v b.v)
  return ⟨o⟩

/-- `a · b` into a fresh value (`Expand.pureMul`). -/
def mul {σ τ : Ty} (a : Var σ) (b : Var τ) : B Word := do
  let o ← fresh .pooled
  atom (.mul o a.v b.v)
  return ⟨o⟩

/-- The product of two powers of `g`: its log is below the sum of theirs, which the logic proves
from the factors' facts, so no check is emitted. -/
def mulG {m n : Nat} (a : Var (.gpow m)) (b : Var (.gpow n)) : B (Var (.gpow (m + n))) := do
  let o ← fresh .pooled
  atom (.mul o a.v b.v)
  return ⟨o⟩

/-- `a + b` written into a cell of its own (`Expand.exprInto`), which a later write into the same
cell asserts against. -/
def addCell {σ τ : Ty} (a : Var σ) (b : Var τ) : B Word := do
  let o ← fresh
  atom (.add o a.v b.v)
  return ⟨o⟩

/-- `d = a · b` for a value `d` already written: the write-once memory makes it an assertion. -/
def mulInto {ρ σ τ : Ty} (d : Var ρ) (a : Var σ) (b : Var τ) : B Unit := atom (.mul d.v a.v b.v)

/-- `assert a == b`. -/
def assertEq {σ τ : Ty} (a : Var σ) (b : Var τ) : B Unit := atom (.assertEq a.v b.v)

/-- `b · b = b`, written into the hinted cell itself (`nb[k] = b * b`): the hint's value is a bit. -/
def assertBit (h : Hinted) : B (Var .bit) := do
  atom (.mul h.v h.v h.v)
  return ⟨h.v⟩

/-- `x ** k` by square-and-multiply, `k ≥ 1` (`Expand.powExpr`). -/
def pow {τ : Ty} (x : Var τ) (k : Nat) : B Word := do
  let mut acc : Word := x.word
  for i in (List.range (Nat.log2 k)).reverse do
    acc ← mul acc acc
    if (k / 2 ^ i) % 2 = 1 then
      acc ← mul acc x
  return acc

/-! ## Memory -/

/-- The word at `p·g^off` (`DEREF`, a heap read). -/
def load {τ : Ty} (p : Var τ) (off : Nat) : B Word := do
  let o ← fresh .pooled
  atom (.load o p.v off)
  return ⟨o⟩

/-- Store `v` at `p·g^off`: the same `DEREF`, the write-once memory making it a write or a check. -/
def store {σ τ : Ty} (p : Var σ) (off : Nat) (v : Var τ) : B Unit := atom (.load v.v p.v off)

/-- A fresh heap buffer of `size` words (`HeapBuf(size)`). -/
def heapBuf (size : Nat) : B Word := do
  let p ← fresh
  hint (.alloc p size)
  return ⟨p⟩

/-- A run of `n` frame cells (`StackBuf(n)`). -/
def stackBuf (n : Nat) : B (List V) := freshRun n

/-! ## Hints and checks -/

/-- The `n` low bits of `log x`, hinted into a fresh run (`hint_decompose_bits_exponent`). -/
def hintBitsExp {τ : Ty} (x : Var τ) (n : Nat) : B (List Hinted) := do
  let run ← freshRun n
  hint (.bitsExp x.v n (.stack run))
  return run.map Hinted.mk

/-- `assert log x < n` (`Expand.lowerAssertLt` at a constant bound): `x` is `g^k`, `k < n`,
in a memory of at least `n` words. -/
def rangeCheck {τ : Ty} (x : Var τ) (n : Nat) : B (Var (.gpow n)) := do
  let k ← const (gpowE (n - 1))
  let y ← fresh
  let t1 ← fresh
  let t2 ← fresh
  atom (.rangeCheck x.v y t1 t2 k.v)
  return ⟨x.v⟩

/-! ## Control -/

/-- A fused `match` of calls: `fs[j]` runs on `args` at `x = g^j` (`Expand.lowerDispatchedCall`),
`nrets` fresh return values. -/
def dispatch {τ : Ty} (x : Var τ) (fs : List String) (args : List V) (nrets : Nat) :
    B (List Word) := do
  let rets ← freshRun nrets
  emit (.dispatch x.v fs args rets)
  return rets.map Var.mk

/-- A call of `f` on `args`, `nrets` fresh return values. -/
def call (f : String) (args : List V) (nrets : Nat) : B (List Word) := do
  let rets ← (List.range nrets).mapM fun _ => fresh
  emit (.call f args rets)
  return rets.map Var.mk

/-- Write the returned values into the return area: a value copied, a constant set
(`Expand.returnInto`). -/
def retInto : List V → List Ret → B Unit
  | r :: rs, .v x :: xs => do atom (.copy r x); retInto rs xs
  | r :: rs, .c e :: xs => do atom (.const r e); retInto rs xs
  | _, _ => pure ()

/-- `return vs` up to its `ret`: the return area, written (`Expand.lowerReturn`). -/
def retArea (vs : List Ret) : B (List V) := do
  let rs ← freshRun vs.length .ret
  retInto rs vs
  return rs

/-- `return vs`. -/
def ret (vs : List Ret) : B Unit := do
  let rs ← retArea vs
  emit (.ret rs)

end B

/-! ## Functions -/

/-- The three marking passes an expanded function goes through (`Expand.expandQueue`). -/
def finish (core : Core.Fn) (trace : Array Event) (lines : Array (Nat × Nat)) (rets : Nat)
    (loop : Bool × Option Nat) : Elab :=
  let (named, l1) := markUnnamedLines core trace lines
  let (pooled, l2) := markPooledLines core named l1
  let (joined, l3) := markJoinedLines core pooled l2
  (⟨core, joined, rets, loop, []⟩, l3)

/-- A guest function: its name, its number of argument and return cells, and its body, from the
parameters' values to the returned ones. -/
structure GFn where
  name : String
  arity : Nat
  rets : Nat
  body : List V → B (List Ret)

/-- The parameters' values. -/
def params (n : Nat) : List V := (List.range n).map V.param

/-- A function's body and its `return`, run from the empty state. -/
def GFn.run (f : GFn) : (List Ret × List V) × St :=
  (do let rs ← f.body (params f.arity); let area ← B.retArea rs; return (rs, area)).run
    { name := f.name }

/-- A function's core function: what its body and its return area emit, then its `ret`. -/
def GFn.core (f : GFn) : Core.Fn :=
  ⟨f.name, params f.arity, f.run.2.out.toList ++ [.ret f.run.1.2]⟩

/-- A function elaborated, then the loop helpers it made. -/
def GFn.elab (f : GFn) : List Elab :=
  let st := f.run.2
  finish f.core (st.trace.push .emit) st.lines f.rets (false, none) :: st.helpers.toList

/-! ## Loops -/

namespace B

/-- Elaborate a loop helper named `name` over `arity` parameters and record it, with the helpers
its own body made. -/
def helper (name : String) (arity : Nat) (body : List V → B Unit) (hi : Option Nat) : B Unit := do
  let ps := params arity
  let ((), st) := (do body ps; ret []).run { name }
  let core : Core.Fn := ⟨name, ps, st.out.toList⟩
  modify fun s => { s with helpers := (s.helpers.push (finish core st.trace st.lines 0 (true, hi))) ++ st.helpers }

/-- The next loop helper's name: `__loop`, which the back end recognizes, and the function's. -/
def loopName : B String := do
  let st ← get
  return s!"__loop_{st.name}_{st.helpers.size}"

/-- `for x in mul_range(g^lo, g^hi)` at compile-time bounds `lo < hi`: the helper takes the counter
and the captured values `caps`, steps the counter by `g`, and calls itself until it reaches the
constant exit `g^hi`; the caller calls it once, unconditionally. -/
def loopConst (lo hi : Nat) (caps : List V) (body : Var (.gpow hi) → List V → B Unit) :
    B Unit := do
  let name ← loopName
  helper name (caps.length + 1) (fun ps => do
    let x : Var (.gpow hi) := ⟨ps.head!⟩
    body x ps.tail
    let gc ← gconst 1
    let nx ← mul x gc
    let ex ← gconst hi
    let c ← add nx ex
    emit (.callIf c.v name (nx.v :: ps.tail))) (some hi)
  let x0 ← gconst lo
  emit (.call name (x0.v :: caps) [])

/-- `for x in mul_range(g^lo, hi)` at a runtime bound, as the zkDSL lowers it (`Expand.lowerFor`):
the exit is a parameter, the first call is conditional on `g^lo ≠ hi`, and `hi` (an expression,
so an action) and the stepped counter `x·g` are evaluated once per use. -/
def loopRt {τ : Ty} (lo : Nat) (hi : B (Var τ)) (caps : List V) (body : Word → List V → B Unit) :
    B Unit := do
  let name ← loopName
  helper name (caps.length + 2) (fun ps => do
    let x : Word := ⟨ps.head!⟩
    let bnd : Word := ⟨ps[1]!⟩
    body x (ps.drop 2)
    let g1 ← gconst 1
    let nx ← mul x g1
    let c ← add nx bnd
    let g2 ← gconst 1
    let nx2 ← mul x g2
    emit (.callIf c.v name (nx2.v :: bnd.v :: ps.drop 2))) none
  let x0 ← gconst lo
  let h0 ← hi
  let c ← add x0 h0
  let x1 ← gconst lo
  let h1 ← hi
  emit (.callIf c.v name (x1.v :: h1.v :: caps))

end B

end
end LeanVM.Dsl
