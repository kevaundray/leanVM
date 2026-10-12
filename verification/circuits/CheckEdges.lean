import LeanVMCircuits.Rec.Dump
import LeanVMCircuits.Rec.Edges

/-!
`lake exe checkedges <dump>...`: read each dump's edge marks (its statement's layout, each child's statement words, the claims its reduction takes), find the calls computing each child's scale from its kind word and the call reading its digest, and check the certificate (`Edges.EdgeCert.check`, which `Edges.EdgeCert.edge` proves sound). Dumps of one tree (the name up to `-first`, `-node` or `-circuit-`) must share a layout.
-/

open LeanVMCircuits.Rec Model Edges

/-- A list given as its length, then its numbers, at the head of `ws`, and what follows it. -/
def takeList (ws : List String) : Except String (List ℕ × List String) := do
  let n ← Dump.nat (ws.headD "")
  let xs := ws.tail.take n
  unless xs.length = n do .error "a list shorter than its length"
  return (← Dump.nats xs, ws.tail.drop n)

def lastList (ws : List String) : Except String (List ℕ) := do
  let (xs, rest) ← takeList ws
  unless rest.isEmpty do .error "words after a list"
  return xs

/-- A dump's edge marks. -/
structure Marks where
  layout : Option Layout := none
  children : Array (ℕ × List ℕ) := #[]
  dense : Array (Dense ℕ) := #[]
  matrices : Array (Matrix ℕ) := #[]

def coef (s : String) : Except String (Coef ℕ) :=
  match s with
  | "zero" => pure .zero
  | "one" => pure .one
  | _ => return .of (← Dump.nat s)

def Marks.add (m : Marks) (ws : List String) : Except String Marks := do
  match ws with
  | "layout" :: nD :: nP :: nM :: nF :: rest =>
    let (nDense, nPolys, nMatrix, nFlocks) := (← Dump.nat nD, ← Dump.nat nP, ← Dump.nat nM, ← Dump.nat nF)
    let dims ← Dump.nats rest
    unless dims.length = nPolys + nFlocks do .error "a layout's prefixes"
    if m.layout.isSome then .error "two layouts"
    return { m with layout := some { nDense, nPolys, nMatrix, nFlocks, vars := dims.take nPolys,
                                     klog := dims.drop nPolys } }
  | "child" :: i :: rest => return { m with children := m.children.push (← Dump.nat i, ← lastList rest) }
  | "dense" :: poly :: rest => return { m with dense := m.dense.push ⟨← Dump.nat poly, ← lastList rest, []⟩ }
  | "term" :: nLow :: bits :: bitsLen :: scale :: value :: rest =>
    let scale ← if scale = "none" then pure none else some <$> Dump.nat scale
    let t : Term ℕ := ⟨← Dump.nat nLow, ← Dump.nat bits, ← Dump.nat bitsLen, ← lastList rest, scale, ← Dump.nat value⟩
    let some d := m.dense.back? | .error "a term before its claim"
    return { m with dense := m.dense.pop.push { d with terms := d.terms ++ [t] } }
  | ["matrix", circuit, a, b, value] =>
    return { m with matrices := m.matrices.push ⟨← Dump.nat circuit, .point [], .point [], (← coef a, ← coef b),
                                                 ← Dump.nat value⟩ }
  | "row" :: kind :: rest =>
    let row ← match kind, rest with
      | "skip", z :: rest => do pure (RowW.skip (← Dump.nat z) (← lastList rest))
      | "point", rest => do pure (RowW.point (← lastList rest))
      | _, _ => .error "a row weight"
    let some x := m.matrices.back? | .error "a row before its claim"
    return { m with matrices := m.matrices.pop.push { x with row } }
  | "col" :: kind :: rest =>
    let col ← match kind with
      | "slices" => do
        let (s, rest) ← takeList rest
        pure (ColW.slices s (← lastList rest))
      | "point" => do pure (ColW.point (← lastList rest))
      | _ => .error "a column weight"
    let some x := m.matrices.back? | .error "a column before its claim"
    return { m with matrices := m.matrices.pop.push { x with col } }
  | _ => .error s!"an edge mark: {" ".intercalate ws |>.take 80}"

/-- The calls whose outputs include each wire, with the output's position. -/
def outIndex (os : Array (List ℕ)) : Std.HashMap ℕ (Array (ℕ × ℕ)) := Id.run do
  let mut idx : Std.HashMap ℕ (Array (ℕ × ℕ)) := {}
  for j in [0:os.size] do
    let mut k := 0
    for w in os[j]! do
      idx := idx.insert w ((idx.getD w #[]).push (j, k))
      k := k + 1
  return idx

/-- The calls computing a child's scale wire `s` from its kind word `kw`, as `Design::kind_rows` makes them. -/
def scaleOf (cs : Array Call) (os : Array (List ℕ)) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (kw s : ℕ) :
    Option ScaleCert := do
  if s = kw then return .kind
  let makers := fun (w : ℕ) => (idx.getD w #[]).toList.filterMap fun (j, k) => if k = 0 then some j else none
  if let some c := (makers s).find? (cs[·]? == some Call.one) then return .one c
  let (last, f, one) ← (makers s).findSome? fun j => match (cs[j]? : Option Call) with
    | some (Call.add f one) => some (j, f, one)
    | _ => none
  let o ← (makers one).find? (cs[·]? == some Call.one)
  let e ← (List.range cs.size).find? (cs[·]? == some (Call.eToK kw))
  let sp ← (List.range cs.size).find? (cs[·]? == some (.split (out os e 0)))
  let mut acc := f
  let mut steps : List (ℕ × ℕ × ℕ) := []
  for _ in [0:65] do
    if acc = one then break
    let step := (makers acc).findSome? fun m => do
      let some (Call.mul a n) := (cs[m]? : Option Call) | none
      let (p, t) ← (makers n).findSome? fun p => match (cs[p]? : Option Call) with
        | some (Call.add t o') => if o' == one then some (p, t) else none
        | _ => none
      let k ← (makers t).find? fun k => match (cs[k]? : Option Call) with
        | some (Call.kToE1 _) => true
        | _ => false
      pure (a, k, p, m)
    let (a, k, p, m) ← step
    steps := (k, p, m) :: steps
    acc := a
  return .bits o e sp last steps

/-- The certificate of a dump's calls, outputs and marks. -/
def certOf (cs : Array Call) (os : Array (List ℕ)) (m : Marks) (L : Layout) : Except String EdgeCert := do
  let idx := outIndex os
  let claims : Claims ℕ := ⟨m.dense.toList, m.matrices.toList⟩
  let mut children := #[]
  for (i, (j, ws)) in m.children.toList.zipIdx.map (fun (x, i) => (i, x)) do
    unless i = j do .error s!"child {j} marked {i}th"
    let w := fun (n : ℕ) => ws.getD n 0
    -- The scale is the one on the fixed polynomial's claim at the child's words.
    let fixed := stmtDense L w 0 2
    let some s := claims.dense.findSome? fun d =>
        if d.poly = 2 ∧ d.low = fixed.low ∧ d.terms.map (·.value) = [w (L.dv + 2)] then
          d.terms.head?.bind (·.scale)
        else none
      | .error s!"child {j}: no claim on the fixed polynomial at its words"
    let some sc := scaleOf cs os idx (w 0) s | .error s!"child {j}: no calls computing its scale"
    let some dg := (List.range cs.size).find? (cs[·]? == some (.halvesToD (w 1) (w 2)))
      | .error s!"child {j}: its digest is not read"
    children := children.push { words := ws, scale := sc, digest := dg }
  return { calls := cs, layout := L, claims, children := children.toList }

def modeName : Mode → String
  | .kind => "kind word"
  | .one => "one"
  | .bits b => s!"{b} kind bits"

/-- Check one dump; its layout when the certificate accepts. -/
def check (path : System.FilePath) : IO (Option Layout) := do
  let text ← IO.FS.readFile path
  let (lines, _, _) ← match Dump.sections text with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"{path}: {e}"; return none
  let mut calls : Array Call := #[]
  for line in lines do
    match Dump.parseLine line with
    | .ok (.call c) => calls := calls.push c
    | .ok _ => pure ()
    | .error e => do IO.eprintln s!"{path}: {e}"; return none
  let marks ← match (Dump.edgeLines text).foldlM Marks.add {} with
    | .ok m => pure m
    | .error e => do IO.eprintln s!"{path}: {e}"; return none
  let some L := marks.layout | do IO.eprintln s!"{path}: no layout mark"; return none
  let some (_, os) := replayR calls #[] 0 {} #[] | do IO.eprintln s!"{path}: the calls do not replay"; return none
  let cert ← match certOf calls os marks L with
    | .ok c => pure c
    | .error e => do IO.eprintln s!"{path}: {e}"; return none
  let ok := cert.check
  let per := (stmtClaims L (fun _ => 0) 0 : Claims ℕ)
  let edges := if cert.children.isEmpty then "no child" else
    s!"children with scales from {", ".intercalate (cert.children.map fun ch => modeName ch.scale.mode)}, \
      each making {per.dense.length} dense and {per.matrices.length} matrix claims among them"
  IO.println s!"{path}: {if ok then "accepted" else "rejected"}: a statement of {L.len} words, the reduction takes \
    {cert.claims.dense.length} dense and {cert.claims.matrices.length} matrix claims, {edges}"
  return if ok then some L else none

/-- The tree a dump is of: its name up to its position. -/
def treeOf (path : System.FilePath) : String :=
  let name := path.fileName.getD ""
  let cut := fun (s sep : String) => (s.splitOn sep).headD s
  cut (cut (cut name "-first") "-node") "-circuit-"

def main (args : List String) : IO UInt32 := do
  let mut ok := true
  let mut layouts : Std.HashMap String Layout := {}
  for a in args do
    match ← check a with
    | none => ok := false
    | some L =>
      let t := treeOf a
      match layouts[t]? with
      | some L' =>
        if L ≠ L' then
          IO.eprintln s!"{a}: a layout other than its tree's"
          ok := false
      | none => layouts := layouts.insert t L
  return if ok then 0 else 1
