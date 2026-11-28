/-
  LeanVM.Dsl.Builder

  The guest language embedded in Lean: a guest function is a term of the builder monad `B`, and
  elaborating it gives the back end's input, a core function with its allocation trace
  (`Compiler.TracedFn`), without a source text or a parser.
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
abbrev Elab := TracedFn × Array (Nat × SrcLine)

/-- A materialized shifted pointer: the value `out` holds `base·g^exp`, made as
`src · g^dist` (`src` the base itself or an earlier materialization of it). -/
structure Mat where
  exp : Nat
  out : V
  src : V
  dist : Nat
  deriving Inhabited

/-- The elaboration state of one function. -/
structure St where
  /-- The tag of the next allocation. -/
  tag : Nat := 1
  out : Array Stmt := #[]
  trace : Array Event := #[]
  lines : Array (Nat × SrcLine) := #[]
  /-- A hint emitted since the last instruction. -/
  pending : Bool := false
  /-- The function's name, which its loop helpers' names extend. -/
  name : String := ""
  /-- The loop helpers made so far, in order. -/
  helpers : Array Elab := #[]
  /-- The Keccak padding run set in this scope (the zkDSL lowering's `keccakPad`). -/
  keccakPad : Option (List V) := none
  /-- The constants set in this scope by `const` and `gconst` (the zkDSL lowering's `consts`). -/
  consts : List E := []
  /-- The shifted pointers materialized in this scope, by base (the zkDSL lowering's `mats`). -/
  mats : List (V × List Mat) := []
  /-- The run each `addr` pointer names. -/
  addrRuns : List (V × List V) := []
  /-- Whether the trace also carries what is advice only to placement and the zkDSL's lowering records: the
  `use` events of aliases and the site values of inlined calls. -/
  faithful : Bool := true
  deriving Inhabited

/-- The builder. -/
abbrev B := StateM St

/-- What the program logic proves of a value. -/
inductive Ty where
  | word
  | bit
  /-- `g^k` for some `k < n`. -/
  | gpow (n : Nat)
  /-- An element of `K`. -/
  | inK
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

/-- A returned value, written into its return cell as the zkDSL's lowering writes it: a copy of a
value, a constant, a sum, a product, a heap word; or any action writing the cell, run in order
with the others (`into`: a faithful port's `return f(x)` or `return a * b`, the operands lowered
after the cells before it are written). -/
inductive Ret where
  | v (x : V)
  | c (e : E)
  | add (a b : V)
  | mul (a b : V)
  | load (p : V) (off : Nat)
  | into (w : V → B Unit)
  deriving Inhabited

/-- The word a returned value holds (`into` holds no word the logic reads). -/
def Ret.eval (rd : Reader) (σ : Val) : Ret → E
  | .v x => σ x
  | .c e => e
  | .add a b => σ a + σ b
  | .mul a b => σ a * σ b
  | .load p off => (rd ((σ p).limb 0 * addressOfIndex off)).getD 0
  | .into _ => 0

/-- A returned value the logic reads: not `into`. -/
def Ret.isPure : Ret → Bool
  | .into _ => false
  | _ => true

namespace B

/-! ## Values, statements, the trace -/

/-- A fresh value. -/
def fresh (k : Kind := .cell) : B V := modifyGet fun st =>
  (⟨[], st.tag, 0⟩, { st with tag := st.tag + 1, trace := st.trace.push (.alloc [⟨[], st.tag, 0⟩] k) })

/-- `n` fresh consecutive values. -/
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

/-- The statements from here on come from source line `l` of `file` (none: a program that names
no files). The guest's `do` blocks write these markers themselves (`Dsl/Lines`). -/
def line (l : Nat) (file : String := "") : B Unit :=
  modify fun st => { st with lines := st.lines.push (st.trace.size, { file, line := l }) }

/-- The anchor a hint pending at the end of a block gets. -/
def anchor : B Unit := do
  let o ← fresh
  atom (.const o 0)

/-- `m`, then an anchor if it leaves a hint pending. -/
def closed {α : Type} (m : B α) : B α :=
  m >>= fun a => get >>= fun st => (if st.pending then anchor else pure ()) >>= fun _ => pure a

/-- Run `m` as a block of its own: its statements are returned, not appended, between an `enter`
and a `leave` event, with an anchor for a hint left pending; the scope's padding run, constants
and materialized pointers are the enclosing ones again after it. -/
def block {α : Type} (m : B α) : B (α × List Stmt) := do
  let st ← get
  set { st with out := #[], pending := false }
  event .enter
  let a ← closed m
  event .leave
  let st' ← get
  set { st' with out := st.out, pending := st.pending, keccakPad := st.keccakPad,
                 consts := st.consts, mats := st.mats }
  return (a, st'.out.toList)

/-! ## Arithmetic -/

/-- Record `c` as a constant set in this scope. -/
def poolConst (c : E) : B Unit :=
  modify fun st => if st.consts.contains c then st else { st with consts := c :: st.consts }

/-- A constant. -/
def const (c : E) : B Word := do
  let o ← fresh .pooled
  atom (.const o c)
  poolConst c
  return ⟨o⟩

/-- `g^e`. -/
def gconst (e : Nat) : B (Var (.gpow (e + 1))) := do
  let o ← fresh .pooled
  atom (.const o (gen ^ e))
  poolConst (gen ^ e)
  return ⟨o⟩

/-- `d = c` for a cell `d` (the zkDSL's lowering of a constant). -/
def constInto {ρ : Ty} (d : Var ρ) (c : E) : B Unit := atom (.const d.v c)

/-- `d = a + b` for a cell `d`. -/
def addInto {ρ σ τ : Ty} (d : Var ρ) (a : Var σ) (b : Var τ) : B Unit := atom (.add d.v a.v b.v)

/-- `d = s`, a copy. -/
def copy {ρ σ : Ty} (d : Var ρ) (s : Var σ) : B Unit := atom (.copy d.v s.v)

/-- `a / b` into a fresh cell `q`, as `a = q · b`. -/
def fdiv {σ τ : Ty} (a : Var σ) (b : Var τ) : B Word := do
  let q ← fresh
  atom (.mul a.v q b.v)
  return ⟨q⟩

/-- `a + b` (`XOR`) into a fresh value. -/
def add {σ τ : Ty} (a : Var σ) (b : Var τ) : B Word := do
  let o ← fresh .pooled
  atom (.add o a.v b.v)
  return ⟨o⟩

/-- `a · b` into a fresh value. -/
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

/-- `a + b` written into a cell of its own, which a later write into the same
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

/-- `x ** k` by square-and-multiply, `k ≥ 1`. -/
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

/-- `d = [p·g^off]` for a cell `d` (the zkDSL's lowering of a heap read): the `DEREF` of `store`. -/
def loadInto {ρ σ : Ty} (d : Var ρ) (p : Var σ) (off : Nat) : B Unit := atom (.load d.v p.v off)

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

/-- `assert log x < log (g·k)`, `k` holding the bound less one in the exponent: a `DEREF` through
`x`, `k = x·y`, a `DEREF` through `y` (the zkDSL's lowering after its bound). -/
def rangeCheckK {τ ρ : Ty} (x : Var τ) (k : Var ρ) : B Word := do
  let y ← fresh
  let t1 ← fresh
  let t2 ← fresh
  atom (.rangeCheck x.v y t1 t2 k.v)
  return ⟨x.v⟩

/-- `assert log x < n` (the zkDSL's lowering at a constant bound): `x` is `g^k`, `k < n`,
in a memory of at least `n` words. -/
def rangeCheck {τ : Ty} (x : Var τ) (n : Nat) : B (Var (.gpow n)) := do
  let k ← const (gpowE (n - 1))
  let r ← rangeCheckK x k
  return ⟨r.v⟩

/-! ## Control -/

/-- A fused `match` of calls: `fs[j]` runs on `args` at `x = g^j`,
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

/-- Write the returned values into the return area as the zkDSL's lowering writes each into its
cell. -/
def retInto : List V → List Ret → B Unit
  | r :: rs, .v x :: xs => do atom (.copy r x); retInto rs xs
  | r :: rs, .c e :: xs => do atom (.const r e); retInto rs xs
  | r :: rs, .add a b :: xs => do atom (.add r a b); retInto rs xs
  | r :: rs, .mul a b :: xs => do atom (.mul r a b); retInto rs xs
  | r :: rs, .load p off :: xs => do atom (.load r p off); retInto rs xs
  | r :: rs, .into w :: xs => do w r; retInto rs xs
  | _, _ => pure ()

/-- `return vs` up to its `ret`: the return area, written. -/
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

/-- The three marking passes an expanded function goes through. -/
def finish (core : Core.Fn) (trace : Array Event) (lines : Array (Nat × SrcLine)) (rets : Nat)
    (loop : Bool × Option Nat) : Elab :=
  let (named, l1) := markUnnamedLines core trace lines
  let (pooled, l2) := markPooledLines core named l1
  let (joined, l3) := markJoinedLines core pooled l2
  (⟨core, joined, rets, loop, []⟩, l3)

/-- The shape of a parameter or a returned value: one cell, or a `StackBuf(n)` run of `n`. -/
inductive Shape where
  | scalar
  | buf (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The cells of a shape. -/
def Shape.cells : Shape → Nat
  | .scalar => 1
  | .buf n => n

/-- Cells cut into consecutive runs, one per shape (a function's parameters, flattened). -/
def splitRuns : List Shape → List V → List (List V)
  | [], _ => []
  | s :: ss, vs => vs.take s.cells :: splitRuns ss (vs.drop s.cells)

/-- A guest function: its name, its number of argument and return cells, and its body, from the
parameters' values to the returned ones; `faithful` as `St.faithful`. -/
structure GFn where
  name : String
  arity : Nat
  rets : Nat
  body : List V → B (List Ret)
  faithful : Bool := true

/-- The parameters' values. -/
def params (n : Nat) : List V := (List.range n).map V.param

/-- A function's body and its `return`, run from the empty state. -/
def GFn.run (f : GFn) : (List Ret × List V) × St :=
  (do let rs ← f.body (params f.arity); let area ← B.retArea rs; return (rs, area)).run
    { name := f.name, faithful := f.faithful }

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
  let ((), st) := (do body ps; ret []).run { name, faithful := (← get).faithful }
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

/-- `for x in mul_range(g^lo, hi)` at a runtime bound, as the zkDSL lowers it:
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

/-- The value `x · g` the step of a faithful loop passes on: as the zkDSL's lowering makes the
shifted counter, a product with `g`, the second one in a scope reusing the first's base. -/
def stepOf (x : Word) : B Word := do
  let st ← get
  let mats := ((st.mats.find? (·.1 == x.v)).map (·.2)).getD []
  match mats.find? (·.exp == 1) with
  | some m =>
      let c ← const (gpowE m.dist)
      mul (⟨m.src⟩ : Word) c
  | none =>
      let c ← const (gpowE 1)
      let o ← mul x c
      modify fun st => { st with
        mats := (x.v, mats ++ [⟨1, o.v, x.v, 1⟩]) :: st.mats.filter (·.1 != x.v) }
      return o

/-- `for x in mul_range(g^lo, g^hi)` at compile-time bounds as the zkDSL lowers it
(`.const`): the helper takes the counter and the captures, its exit test and its
self-call each make `x · g` (`stepOf`); the caller calls it once, unless `lo = hi`. The captures
are an action, lowered at the call (a capture bound to a constant or a shifted pointer is made
there); `ncaps` counts their cells. -/
def loopConstF (lo hi : Nat) (ncaps : Nat) (caps : B (List V))
    (body : Word → List V → B Unit) : B Unit := do
  let name ← loopName
  helper name (ncaps + 1) (fun ps => do
    let x : Word := ⟨ps.head!⟩
    body x ps.tail
    let nx ← stepOf x
    let ex ← const (gpowE hi)
    let c ← add nx ex
    let nx2 ← stepOf x
    emit (.callIf c.v name (nx2.v :: ps.tail))) (some hi)
  if lo ≠ hi then
    let x0 ← const (gpowE lo)
    let cs ← caps
    emit (.call name (x0.v :: cs) [])

/-- `for x in mul_range(g^lo, hi)` at a runtime bound as the zkDSL lowers it (`.runtime`): `loopRt` with the stepped counter made by `stepOf` and the captures an action lowered
after the entry test, at the call. -/
def loopRtF {τ : Ty} (lo : Nat) (hi : B (Var τ)) (ncaps : Nat) (caps : B (List V))
    (body : Word → List V → B Unit) : B Unit := do
  let name ← loopName
  helper name (ncaps + 2) (fun ps => do
    let x : Word := ⟨ps.head!⟩
    let bnd : Word := ⟨ps[1]!⟩
    body x (ps.drop 2)
    let nx ← stepOf x
    let c ← add nx bnd
    let nx2 ← stepOf x
    emit (.callIf c.v name (nx2.v :: bnd.v :: ps.drop 2))) none
  let x0 ← const (gpowE lo)
  let h0 ← hi
  let c ← add x0 h0
  let x1 ← const (gpowE lo)
  let h1 ← hi
  let cs ← caps
  emit (.callIf c.v name (x1.v :: h1.v :: cs))

end B

end
end LeanVM.Dsl
