/-
  LeanVM.Dsl.Check

  The migration check: each ported function, elaborated, against what `Expand` makes of the
  zkDSL source it replaces, run on the exported guest.
-/

import LeanVM.Dsl.ControlGuest
import LeanVM.Core.Expand
import LeanVM.Core.Renumber

/-!
# Elaboration against expansion

A ported function is checked against `Expand` on the guest's exported source
(`LeanVM.Guest.Data.guest`): the core functions, the ported one and those it makes (loop helpers,
`Const` specializations), are equal once their values are numbered by first occurrence (the
renumbering the guest's core data is written in, `Fn.numbering`) and the loop helpers carry the
expansion's names. Where they are equal the function's B1 proofs, stated on the renumbered core
data, hold of the ported function unchanged.

The checks are `#guard`s: the elaborator evaluates both sides, `Expand` included, which the kernel
would have to unfold through the field arithmetic of every constant. An improved form is checked
for what it changes against the faithful one (`eqPrefixChain'`, `daColumnOffsets'`).
-/

namespace LeanVM.Dsl.Check

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl LeanVM.Dsl.Guest

/-- The values of `f`, parameters first, then in order of first occurrence. -/
def canonTable (f : Core.Fn) : List V :=
  (f.params ++ Stmt.valsList f.body).foldl (fun t v => if t.contains v then t else t ++ [v]) []

/-- `f` with its values numbered by first occurrence. -/
def canon (f : Core.Fn) : Core.Fn :=
  let t := canonTable f
  f.rename fun v => V.n (t.idxOf v)

/-- The callee names of `f`'s statements at its top level, through `g`. -/
def renameCallees (g : String → String) (f : Core.Fn) : Core.Fn :=
  { f with
    name := g f.name
    body := f.body.map fun
      | .call c a r => .call (g c) a r
      | .callIf x c a => .callIf x (g c) a
      | s => s }

/-- The expansion's name of an elaborated loop helper: `__loop_<f>_<k>` is `__loop<k>`, the
expansion of one function counting its loops from zero. -/
def expansionName (f : String) (s : String) : String :=
  match s.dropPrefix? s!"__loop_{f}_" with
  | some k => s!"__loop{k}"
  | none => s

/-- The core functions `Expand` makes of `f` in the program `p`, with what it queues. -/
def expanded (p : Source.Program) (f : Source.Func) : List Core.Fn :=
  match Expand.expandQueue p 1000 0 #[f] 0 #[] with
  | .ok a => a.toList.map (·.1.core)
  | .error _ => []

/-- The core functions elaborated from `fs`, helpers named as the expansion names them. -/
def elaborated (fs : List GFn) : List Core.Fn :=
  fs.flatMap fun f => (f.elab.map (·.1.core)).map (renameCallees (expansionName f.name))

/-- Equal up to the numbering of values. -/
def sameCore (a b : List Core.Fn) : Bool := a.map canon == b.map canon

/-- The exported source of a function. -/
def src (name : String) : Source.Func :=
  (LeanVM.Guest.Data.guest.funcs.find? (·.name == name)).getD default

/-- The specialization of the exported `name` at the `Const` arguments `cs`, as `Expand` queues
it. -/
def spec (name : String) (cs : List Source.Expr) : Source.Func :=
  (Expand.specializeFn (src name) cs).toOption.getD default

/-! ## Traces -/

/-- The values of a trace: the parameters, then those its events name, in order of first
occurrence. -/
def traceTable (t : Compiler.TracedFn) : List V :=
  (t.trace.toList.flatMap fun
    | .alloc vs _ => vs
    | .use v | .shift v _ => [v]
    | _ => []).foldl (fun tb v => if tb.contains v then tb else tb ++ [v]) t.core.params

/-- A trace with its values numbered by `traceTable`, and what the back end reads beside it: the
return cells, and a loop helper's `loopSource` (`Expand` computes one for every function from its
source; the back end reads it of loop helpers only). -/
def traceStr (t : Compiler.TracedFn) : String :=
  let tb := traceTable t
  let r := fun v => tb.idxOf v
  let evs := t.trace.toList.map fun
    | .alloc vs k => s!"alloc {vs.map r} {reprStr k}"
    | .emit => "emit"
    | .enter => "enter"
    | .leave => "leave"
    | .use v => s!"use {r v}"
    | .shift v e => s!"shift {r v} {e}"
    | .chain => "chain"
    | .note n => s!"note {n}"
  let loop := if t.core.name.startsWith "__loop" then reprStr t.loop else ""
  s!"{evs} rets {t.rets} loop {loop}"

/-- Equal traces up to the numbering of values. -/
def sameTrace (a b : List Compiler.TracedFn) : Bool := a.map traceStr == b.map traceStr

/-- The traced functions `Expand` makes of `f` in the program `p`, with what it queues. -/
def expandedTraced (p : Source.Program) (f : Source.Func) : List Compiler.TracedFn :=
  match Expand.expandQueue p 1000 0 #[f] 0 #[] with
  | .ok a => a.toList.map (·.1)
  | .error _ => []

/-- The traced functions elaborated from `fs`, with their loop helpers. -/
def elaboratedTraced (fs : List GFn) : List Compiler.TracedFn :=
  fs.flatMap fun f => f.elab.map (·.1)

/-! ## The faithful ports -/

#guard sameCore (elaborated [selectorRunNibbles]) (expanded LeanVM.Guest.Data.guest (src "selector_run_nibbles"))

/-- A function calling the inline `is_child` at `k = 0` on a two-cell `StackBuf`. -/
def isChildCaller : Source.Func :=
  { name := "is_child_at0",
    params := [⟨"node", .runtime .scalar⟩, ⟨"kids", .runtime (.stackBuf 2)⟩,
      ⟨"bit", .runtime .scalar⟩],
    returnShapes := [], inline := false,
    body := [.mk 1 (.call "is_child" [.var "node", .var "kids", .lit 0, .var "bit"]),
      .mk 2 (.ret [])] }

#guard sameCore (elaborated [isChildAt0])
  (expanded { LeanVM.Guest.Data.guest with funcs := LeanVM.Guest.Data.guest.funcs ++ [isChildCaller] }
    isChildCaller)

#guard sameCore (elaborated (eqPrefixChain :: (List.range EQ_CHAIN_ARMS).map eqPrefixRun))
  (expanded LeanVM.Guest.Data.guest (src "eq_prefix_chain"))

#guard sameCore (elaborated [daColumnOffsets]) (expanded LeanVM.Guest.Data.guest (src "da_column_offsets"))

/-! ## Runtime control, hints, checks, memory: the ports of `ControlGuest`

Core functions and traces both equal `Expand`'s. -/

#guard sameCore (elaborated [assertSmallGPower])
  (expanded LeanVM.Guest.Data.guest (src "assert_small_g_power"))
#guard sameTrace (elaboratedTraced [assertSmallGPower])
  (expandedTraced LeanVM.Guest.Data.guest (src "assert_small_g_power"))

-- Both instances the guest calls.
#guard [(0, SIZE_BITS), (PCS_MIN_MU, SIZE_BITS)].all fun (fl, nb) =>
  let s := spec "log2_ceil_in_the_exponent" [.lit fl, .lit nb]
  sameCore (elaborated [log2CeilInTheExponent fl nb]) (expanded LeanVM.Guest.Data.guest s) &&
    sameTrace (elaboratedTraced [log2CeilInTheExponent fl nb])
      (expandedTraced LeanVM.Guest.Data.guest s)

-- `rs_eq_run`, its loop helper, and the instances it queues: the dispatch's, then the loop's.
#guard sameCore (elaborated (rsEqRun :: (List.range (RS_CHUNK + 1)).map rsEqRows))
  (expanded LeanVM.Guest.Data.guest (src "rs_eq_run"))
#guard sameTrace (elaboratedTraced (rsEqRun :: (List.range (RS_CHUNK + 1)).map rsEqRows))
  (expandedTraced LeanVM.Guest.Data.guest (src "rs_eq_run"))

#guard sameCore (elaborated [certifyPlacement])
  (expanded LeanVM.Guest.Data.guest (src "certify_placement"))
#guard sameTrace (elaboratedTraced [certifyPlacement])
  (expandedTraced LeanVM.Guest.Data.guest (src "certify_placement"))

#guard sameCore (elaborated [listSplit]) (expanded LeanVM.Guest.Data.guest (src "list_split"))
#guard sameTrace (elaboratedTraced [listSplit])
  (expandedTraced LeanVM.Guest.Data.guest (src "list_split"))

/-! ## `match` with `@inline` arms, chained, and runtime branches

Every `match` of the guest whose arms are `@inline` hashes, so this one is a probe written for the
check: two chained matches of an `@inline` arm, then the three shapes of a runtime `if` (both
blocks, the zero block absent from the source, the nonzero block absent). -/

/-- `sq_arm(a, k: Const)`, inline: `return a * a + k`. -/
def sqArmSrc : Source.Func :=
  { name := "sq_arm", params := [⟨"a", .runtime .scalar⟩, ⟨"k", .const⟩],
    returnShapes := [.scalar], inline := true,
    body := [.mk 1 (.ret [.add (.mul (.var "a") (.var "a")) (.var "k")])] }

/-- `match_probe(x, y, a)`:

```
for i in unroll(0, 1):
    r = match(log(x), range(0, 2), lambda k: sq_arm(a, k))
    s = match(log(y), range(0, 2), lambda k: sq_arm(r, k))
if s == a:
    assert s == a
else:
    assert s != a
if s != 0:
    assert s == s
if s == x:
    assert a == a
return s
```
-/
def matchProbeSrc : Source.Func :=
  { name := "match_probe",
    params := [⟨"x", .runtime .scalar⟩, ⟨"y", .runtime .scalar⟩, ⟨"a", .runtime .scalar⟩],
    returnShapes := [.scalar], inline := false,
    body := [
      .mk 2 (.unroll "i" (.lit 0) (.lit 1) [
        .mk 3 (.match_ [.var "r"] (.var "x")
          [.call "sq_arm" [.var "a", .lit 0], .call "sq_arm" [.var "a", .lit 1]]),
        .mk 4 (.match_ [.var "s"] (.var "y")
          [.call "sq_arm" [.var "r", .lit 0], .call "sq_arm" [.var "r", .lit 1]])]),
      .mk 5 (.ite true (.var "s") (.var "a") [.mk 6 (.assertEq (.var "s") (.var "a"))]
        [.mk 7 (.assertNe (.var "s") (.var "a"))] false),
      .mk 8 (.ite false (.var "s") (.lit 0) [.mk 9 (.assertEq (.var "s") (.var "s"))] [] false),
      .mk 10 (.ite true (.var "s") (.var "x") [.mk 11 (.assertEq (.var "a") (.var "a"))] [] false),
      .mk 12 (.ret [.var "s"])] }

/-- The guest with the probe. -/
def probeProgram : Source.Program :=
  { LeanVM.Guest.Data.guest with funcs := LeanVM.Guest.Data.guest.funcs ++ [sqArmSrc, matchProbeSrc] }

/-- `sq_arm(a, k)` inlined into the cell `rc`: `a` an alias read twice; `+ 0` dropped. -/
def sqArm (a : Word) (k : Nat) (rc : V) : B Unit := B.inline "sq_arm" do
  let a1 ← B.use a
  let a2 ← B.use a
  if k = 0 then B.mulInto (⟨rc⟩ : Word) a1 a2
  else
    let m ← B.mul a1 a2
    let c ← B.const (litField k)
    B.addInto (⟨rc⟩ : Word) m c

/-- The Keccak padding run `Expand` sets above the arms of a match of `@inline` calls (the Keccak
module's `padRun`, here for the probe alone). -/
def padRunProbe : B Unit := do
  if (← get).keccakPad.isSome then return
  let o ← B.freshRun 5 .padRun
  for (v, k) in o.zipIdx do
    B.atom (.const v (if k = 0 then keccakPadValue else 0))
    B.poolConst (if k = 0 then keccakPadValue else 0)
  modify fun st => { st with keccakPad := some o }

/-- The probe in the builder: the first match chained into the second, whose scrutinee is the
cell the chain named and which sets nothing above its arms. -/
def matchProbe : GFn where
  name := "match_probe"
  arity := 3
  rets := 1
  body ps := do
    let x : Word := ⟨ps[0]!⟩
    let y : Word := ⟨ps[1]!⟩
    let a : Word := ⟨ps[2]!⟩
    let r ← B.targets [none]
    B.chain
    padRunProbe
    discard <| B.const Expand.twoToOneClose
    discard <| B.matchArms x ((List.range 2).map fun k => sqArm a k r[0]!)
    let s ← B.targets [none]
    discard <| B.matchArms y ((List.range 2).map fun k => sqArm ⟨r[0]!⟩ k s[0]!)
    let sv : Word := ⟨s[0]!⟩
    let c ← B.add sv a
    discard <| B.ite c (B.assertEq sv a) (B.assertNe sv a)
    discard <| B.ite sv (pure ()) (B.assertEq sv sv)
    let c2 ← B.add sv x
    B.ite0 c2 (B.assertEq a a)
    return [.v sv.v]

#guard sameCore (elaborated [matchProbe]) (expanded probeProgram matchProbeSrc)
#guard sameTrace (elaboratedTraced [matchProbe]) (expandedTraced probeProgram matchProbeSrc)

/-! ## The improved forms -/

/-- The statements of the elaborated functions. -/
def atoms (fs : List Core.Fn) : Nat := (fs.map fun f => (Stmt.valsList f.body).length).sum

-- `eq_prefix_chain` improved: every arm loses its `SET 0` and its return cell, the dispatch its
-- target.
#guard (elaborated [eqPrefixChain']).map (fun f => f.body.length) ==
  (elaborated [eqPrefixChain]).map (fun f => f.body.length)
#guard ((List.range EQ_CHAIN_ARMS).map fun n => ((eqPrefixRun' n).core.body.length + 1 ==
  (eqPrefixRun n).core.body.length)).all id

-- `da_column_offsets` improved: each loop loses its entry test and its bound parameter, and each
-- iteration one stepped counter.
#guard (elaborated [daColumnOffsets']).length == (elaborated [daColumnOffsets]).length
#guard atoms (elaborated [daColumnOffsets']) < atoms (elaborated [daColumnOffsets])

end LeanVM.Dsl.Check
