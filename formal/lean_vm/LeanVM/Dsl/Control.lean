/-
  LeanVM.Dsl.Control

  Runtime control of the embedded guest language: branches and `match` with blocks of their own,
  chained matches, fused dispatch over a `Const` family, calls with `StackBuf` returns, and what
  the faithful mode records of inlined calls and aliases.
-/

module

public import LeanVM.Dsl.Builder

/-!
# Runtime control

A branch or an arm is a `B.block`: its statements go into the core statement that holds them
(`Stmt.ite`, `Stmt.match_`), between `enter` and `leave` events, an anchor closing a hint left
pending, the scope's constants and materialized pointers restored after it, as the zkDSL's lowering
did. A compile-time branch is a Lean `if`, an `unroll` a Lean loop, so only the
runtime forms are here.

* `B.ite c zero nonzero`: `zero` runs at `c = 0`. The zkDSL's `if a == b` takes `then` as the zero
  block and `if a != b` its `else`, elaborated first; `B.ite0` is an `if ==` with no `else`, whose
  absent block records nothing.
* `B.match_ x targets arms`: the targets (fresh cells for names, `StackBuf` cells for elements) are
  allocated before the arms, as in the zkDSL's lowering; arm `j` runs at `x = g^j` and writes them. A
  chained match, whose arms enter the next one, records `chain` between its targets and its arms
  (`B.targets`, `B.chain`, `B.matchArms`).
* `B.dispatchFam x f ks args nrets`: the fused match of the calls `f k`, `k ∈ ks`, of a `Const`
  family, named as the zkDSL names a specialization (`instName`).
* `B.inline f m` and `B.use x`: advice only. Placement reads the site value the zkDSL's lowering allocates for
  an `@inline` call and the `use` event it records where an alias is read; with `St.faithful`
  they are recorded the same way, so the trace equals the zkDSL lowering's.
-/

namespace LeanVM.Dsl

open LeanVM.Parameters LeanVM.Core LeanVM.Compiler

@[expose] public section

namespace B

/-! ## Branches -/

/-- A runtime branch on `c`, which must be in `K`: `zero` at `c = 0`, `nonzero` else, each a block
of its own, `zero` elaborated first. -/
def ite {τ : Ty} {α β : Type} (c : Var τ) (zero : B α) (nonzero : B β) : B (α × β) := do
  let z ← block zero
  let n ← block nonzero
  emit (.ite c.v z.2 n.2)
  return (z.1, n.1)

/-- A runtime branch with no `nonzero` block: `zero` runs at `c = 0`, nothing else does, and the
absent block records nothing (the zkDSL lowering's `if ==` with no `else`). -/
def ite0 {τ : Ty} {α : Type} (c : Var τ) (zero : B α) : B α := do
  let z ← block zero
  emit (.ite c.v z.2 [])
  return z.1

/-! ## `match` -/

/-- The cells a `match` writes: one fresh run for the targets that are names
(`none`), a `StackBuf` cell for each that is an element (`some c`), in order. -/
def targets (ts : List (Option V)) : B (List V) := do
  let run ← freshRun (ts.filter Option.isNone).length
  return (ts.foldl (fun (acc : List V × Nat) t => match t with
    | some c => (acc.1 ++ [c], acc.2)
    | none => (acc.1 ++ [run.getD acc.2 default], acc.2 + 1)) ([], 0)).1

/-- The `match` lowered next ends each arm in the dispatch of the one after it (the zkDSL lowering's
`chainNext`): recorded between its targets and its arms. -/
def chain : B Unit := event .chain

/-- Each action run as a block of its own, in order. -/
def blocks {α : Type} : List (B α) → B (List (α × List Stmt))
  | [] => pure []
  | m :: ms => do
      let r ← block m
      let rs ← blocks ms
      return r :: rs

/-- The arms of a `match` on `x`: arm `j` runs, a block of its own, at `x = g^j`. -/
def matchArms {τ : Ty} {α : Type} (x : Var τ) (arms : List (B α)) : B (List α) := do
  let rs ← blocks arms
  emit (.match_ x.v (rs.map (·.2)))
  return rs.map (·.1)

/-- `targets = match(log(x), ...)` with arms written as actions on the target cells
(not chained). -/
def match_ {τ : Ty} (x : Var τ) (ts : List (Option V)) (arms : List (List V → B Unit)) :
    B (List V) := do
  let cells ← targets ts
  discard <| matchArms x (arms.map (· cells))
  return cells

end B

/-! ## Calls -/

/-- A `Const` argument of a specialization: an integer, or the g-power `g^k`. -/
inductive CArg where
  | L (n : Nat)
  | G (k : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The name the zkDSL gives a function specialized at its `Const` arguments:
`f_`, then `_L{n}` or `_G{k}` per argument (`eq_prefix_run__L3`). -/
def instName (f : String) (cs : List CArg) : String :=
  cs.foldl (fun s c => match c with
    | .L n => s ++ s!"_L{n}"
    | .G k => s ++ s!"_G{k}") (f ++ "_")

namespace B

/-- A fused `match` of the calls `f k` for `k ∈ ks` (arm `j` calls `f ks[j]`), on `args`, with
`nrets` fresh return values. -/
def dispatchFam {τ : Ty} (x : Var τ) (f : Nat → GFn) (ks : List Nat) (args : List V)
    (nrets : Nat) : B (List Word) :=
  dispatch x (ks.map fun k => (f k).name) args nrets

/-- A fused `match` of calls returning into the cells `rets`, allocated before the arguments are
lowered (the zkDSL's lowering: its targets, then its arguments, then the scrutinee). -/
def dispatchInto {τ : Ty} (x : Var τ) (fs : List String) (args rets : List V) : B Unit :=
  emit (.dispatch x.v fs args rets)

/-- A call returning into the cells `dsts`. -/
def callInto (f : String) (args dsts : List V) : B Unit := emit (.call f args dsts)

/-- A call whose returned values have the shapes `shapes`: a fresh cell for each scalar, a fresh
run for each `StackBuf`; the cells per value. -/
def callShaped (f : String) (args : List V) (shapes : List Shape) : B (List (List V)) := do
  let rets ← shapes.mapM fun
    | .scalar => do return [← fresh]
    | .buf n => freshRun n
  emit (.call f args rets.flatten)
  return rets

/-! ## The faithful mode -/

/-- The body of an `@inline` call to `f`: with `St.faithful`, the site value the zkDSL's lowering
allocates first (`Kind.unnamed`, at the position `Seg.i f`), and the caller's line recorded again
after the body. -/
def inline {α : Type} (f : String) (m : B α) : B α := do
  modify fun st => if st.faithful then
    { st with
      tag := st.tag + 1
      trace := st.trace.push (.alloc [⟨[.i f st.tag], st.tag, 0⟩] .unnamed) }
    else st
  let line := ((← get).lines.back?.map (·.2)).getD {}
  let a ← m
  modify fun st => if st.faithful then { st with lines := st.lines.push (st.trace.size, line) }
    else st
  return a

/-- A read of an alias of `x` (a name bound to another value, an `@inline` argument): with
`St.faithful`, the `use` event the zkDSL's lowering records. -/
def use {τ : Ty} (x : Var τ) : B (Var τ) := do
  modify fun st => if st.faithful then { st with trace := st.trace.push (.use x.v) } else st
  return x

end B

end
end LeanVM.Dsl
