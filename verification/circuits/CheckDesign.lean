import LeanVMCircuits.Rec.DesignKind
import LeanVMCircuits.Rec.Dump

/-!
`lake exe checkdesign <summaries> [<dump>...]`: compare the Lean model of `Design` with the Rust design.

The summaries (`fixtures/design-summaries.txt`, written by `rec::tree::design_tests`) hold, for a grid of tree shapes, whether `Tree::new` refuses the shape's arities or small tier, and else its design: `Place::all`, each tier's range, each position's kind, `Design::position` of the kinds below 40, each position's union shape, the dense variables and fixed stacks' variables, and the statement's length and polynomials. Each must be the model's (`Shape.check`, `Shape.places`, `Shape.start`, `Shape.stop`, `Shape.code`, `Shape.position`, `Shape.union`, `Shape.vars`, `Shape.layout`), given the program's two dense variables and each tier's fixed stack's variables, which the summary states.

Each dump is a tracked circuit (`cargo leanvm circuits`), named by its tree and position. Its calls are replayed through the builder model; each child's statement is a run of as many `free_e` calls as the circuit exposes words, and the calls after it must add to the circuit exactly what `Model.kindRows` adds from the same state, for the child's tier: the same unions, rows, public rows, wires and units. A node must read as many children as `Shape.children` says, a first-level circuit none, and the statement's length must leave the dense point a nonnegative number of words.
-/

open LeanVMCircuits.Rec
open LeanVMCircuits.Rec.Model
open LeanVMCircuits.Rec.Design

namespace CheckDesign

def placeStr : Place → String
  | ⟨t, .first⟩ => s!"{t}:F"
  | ⟨t, .node a⟩ => s!"{t}:N:{a}"
  | ⟨t, .wrap⟩ => s!"{t}:W"

def unionStr : Option UnionShape → String
  | none => "-"
  | some u => s!"{u.arity}:{u.children}:{u.declared}:{if u.optional then 1 else 0}"

def words (xs : List String) : String := " ".intercalate xs

/-- The model's summary of an accepted shape's design. -/
def summary (sh : Shape) (v0 v1 : ℕ) (kappas : List ℕ) : List String :=
  let kappa := fun t => kappas.getD t 0
  let ps := List.range sh.size
  [ "places " ++ words (sh.places.map placeStr),
    "tiers " ++ words ((List.range sh.nTiers).map fun t => s!"{sh.start t}-{sh.stop t}"),
    "codes " ++ words (ps.map fun p => toString (sh.code p)),
    "positions " ++ words ((List.range 40).map fun c => (sh.position c).elim "-" toString),
    "unions " ++ words (ps.map fun p => unionStr (sh.union p)),
    "vars " ++ words ((sh.vars v0 v1 kappa).map toString),
    "kappas " ++ words ((List.range sh.nTiers).map fun t => toString (kappa t)),
    s!"statement {(sh.layout v0 v1 kappa).len} {sh.nPolys}" ]

def nat! (s : String) : Except String ℕ := match s.toNat? with
  | some n => pure n
  | none => .error s!"not a number: {s}"

def parseShape (ws : List String) : Except String Shape := do
  match ws with
  | [a0, a, "none"] => pure ⟨← nat! a0, ← nat! a, none⟩
  | [a0, a, c, g, "-"] => pure ⟨← nat! a0, ← nat! a, some ⟨⟨← nat! c, ← nat! g⟩, none⟩⟩
  | [a0, a, c, g, sa, sc, sg] =>
    pure ⟨← nat! a0, ← nat! a, some ⟨⟨← nat! c, ← nat! g⟩, some ⟨← nat! sa, ⟨← nat! sc, ← nat! sg⟩⟩⟩⟩
  | _ => .error s!"not a shape: {words ws}"

def verdict : Option Refusal → String
  | none => "accept"
  | some .arity => "reject arity"
  | some .smallTier => "reject small"

/-- Compare every summary with the model; the number of shapes checked. -/
def checkSummaries (text : String) : Except String ℕ := do
  let lines := text.splitOn "\n" |>.filter (· ≠ "")
  let some first := lines.head? | .error "empty summaries"
  unless first = s!"consts {maxKLog} {nFlocks}" do .error s!"constants differ: {first}"
  let mut rest := lines.tail
  let mut n := 0
  while !rest.isEmpty do
    let shapeLine := rest.headD ""
    let sh ← match shapeLine.splitOn " " with
      | "shape" :: ws => parseShape ws
      | _ => .error s!"expected a shape: {shapeLine}"
    let v := rest.getD 1 ""
    unless v = verdict sh.check do .error s!"{shapeLine}: Rust says {v}, the model {verdict sh.check}"
    if sh.check = none then
      let block := (rest.drop 2).take 8
      let vars ← match (block.getD 5 "").splitOn " " with
        | ["vars", v0, v1, _, _] => pure (← nat! v0, ← nat! v1)
        | _ => .error s!"{shapeLine}: no variables"
      let kappas ← match (block.getD 6 "").splitOn " " with
        | "kappas" :: ks => ks.mapM nat!
        | _ => .error s!"{shapeLine}: no fixed stacks"
      let model := summary sh vars.1 vars.2 kappas
      for (r, m) in block.zip model do
        unless r = m do .error s!"{shapeLine}: Rust `{r}`, the model `{m}`"
      unless sh.places = (List.range sh.size).map sh.placeAt do .error s!"{shapeLine}: places not closed form"
      rest := rest.drop 10
    else
      rest := rest.drop 2
    unless rest.headD "" = "end" do .error s!"{shapeLine}: no end"
    rest := rest.tail
    n := n + 1
  return n

/-- The tracked dumps' shapes, by their name: output trees `2to1` and `4to1`, and the two claim-set examples. -/
def dumpShape (name : String) : Option (Shape × ℕ) :=
  let pos (s : String) : Option ℕ := (s.splitOn "-circuit-").getLast?.bind String.toNat?
  if name.startsWith "aggregate-" then
    let a := if (name.splitOn "-2to1-").length = 2 then 2 else 4
    some (⟨a, a, none⟩, if name.endsWith "-first" then 0 else 1)
  else if name.startsWith "claimset-single-tier-circuit-" then
    (pos name).map fun p => (⟨1, 3, some ⟨⟨12, 4⟩, none⟩⟩, p)
  else if name.startsWith "claimset-two-tier-circuit-" then
    (pos name).map fun p => (⟨1, 3, some ⟨⟨12, 4⟩, some ⟨2, ⟨5, 2⟩⟩⟩⟩, p)
  else none

def isFreeE : Model.Call → Bool
  | .freeE => true
  | _ => false

def isExpose : Model.Call → Bool
  | .exposeE _ => true
  | _ => false

/-- What a state adds to the circuit, besides its caches. -/
def sameCircuit (a b : State) : Bool :=
  a.next == b.next && a.unions == b.unions && a.emul == b.emul && a.exk == b.exk && a.hash == b.hash &&
    a.split == b.split && a.cast == b.cast && a.pub == b.pub && a.statement == b.statement &&
    a.units.eZero == b.units.eZero && a.units.eOne == b.units.eOne && a.units.kZero == b.units.kZero &&
    a.units.kOne == b.units.kOne

/-- How many calls `kindRows sh t` makes. -/
def kindCalls (sh : Shape) (t : ℕ) : ℕ :=
  if sh.size = 2 then 2
  else 2 + 3 * (sh.stop t - sh.start t) + 3 + 64 + (if t = 0 then 2 * sh.kindBits t + 1 else 0)

def checkDump (path : System.FilePath) : IO Bool := do
  let some (sh, position) := dumpShape (path.fileStem.getD "")
    | IO.eprintln s!"{path}: not a tracked circuit's name"; return false
  let text ← IO.FS.readFile path
  let (lines, _, _) ← match Dump.sections text with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"{path}: {e}"; return false
  let mut calls : Array Model.Call := #[]
  for line in lines do
    match Dump.parseLine line with
    | .ok (.call c) => calls := calls.push c
    | .ok _ => pure ()
    | .error e => do IO.eprintln s!"{path}: {e}"; return false
  let len := (calls.filter isExpose).size
  let fixed := 3 + sh.nPolys + 2 * maxKLog + 2 * nFlocks
  unless fixed ≤ len do
    IO.eprintln s!"{path}: a statement of {len} words leaves no dense point"; return false
  let (expected, tier) := match sh.children position with
    | some (a, ct) => (a, ct)
    | none => (0, 0)
  let mut s : State := {}
  let mut i := 0
  let mut children := 0
  while i < calls.size do
    -- A child's statement: a run of exactly `len` `free_e` calls.
    let run := (calls.extract i (i + len + 1)).toList
    let starts := i = 0 || !isFreeE (calls.getD (i - 1) .freeE)
    if starts && run.length = len + 1 && (run.take len).all isFreeE && !isFreeE (run.getD len .freeE) then
      let kind := s.next
      for c in run.take len do
        s := (c.exec.run s).2
      i := i + len
      let model := ((kindRows sh tier kind).run s).2
      for c in (calls.extract i (i + kindCalls sh tier)).toList do
        unless c.args.all (· < s.next) && c.ok do
          IO.eprintln s!"{path}: call {i} names a wire not yet made"; return false
        s := (c.exec.run s).2
      unless sameCircuit model s do
        IO.eprintln s!"{path}: child {children}'s kind rows differ from the model's at call {i}"; return false
      i := i + kindCalls sh tier
      children := children + 1
    else
      let c := calls.getD i .freeE
      unless c.args.all (· < s.next) && c.ok do
        IO.eprintln s!"{path}: call {i} names a wire not yet made"; return false
      s := (c.exec.run s).2
      i := i + 1
  unless children = expected do
    IO.eprintln s!"{path}: {children} children's kind rows, the model {expected}"; return false
  IO.println s!"{path}: position {position}, {children} children's kind rows are the model's, statement {len} words"
  return true

end CheckDesign

def main (args : List String) : IO UInt32 := do
  let some summaries := args.head? | IO.eprintln "usage: checkdesign <summaries> [<dump>...]"; return 2
  let mut ok := true
  match CheckDesign.checkSummaries (← IO.FS.readFile summaries) with
  | .ok n => IO.println s!"{summaries}: {n} shapes, the model's design is Rust's"
  | .error e => IO.eprintln s!"{summaries}: {e}"; ok := false
  for path in args.tail do
    ok := (← CheckDesign.checkDump path) && ok
  return if ok then 0 else 1
