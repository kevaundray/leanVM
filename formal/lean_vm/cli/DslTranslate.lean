import LeanVM.Guest.Data.Source
import LeanVM.Core.Expand

/-!
# `dsl-translate`: the guest's source as embedded-DSL text

`lake exe dsl-translate` (or `lake env lean --run cli/DslTranslate.lean`, from `lean_vm`) reads
the exported source AST (`LeanVM.Guest.Data.guest`), the guest's text (`guests/lean_ethereum.py`,
for each function's source and the global constants' names) and the configuration's constants
(`LeanVM/Guest/Data/Source.lean`), and writes `LeanVM/Dsl/Gen/`: one module per section of the
guest, the `@inline` functions (`Inline.lean`), the constants (`Config.lean`) and the check of
every translated function against `Expand` (`Check.lean`).

The translator is `Expand` run on the source with every compile-time decision taken as `Expand`
takes it (its own readings, `Expand.eval` and the rest, on the substituted source), writing builder
calls (`LeanVM.Dsl.Builder`, `Control`, `Hints`, `Mem`, `Keccak`) instead of core statements. Its
texts keep the compile-time values symbolic: an `unroll` counter is a Lean `for` counter, a `Const`
parameter a Lean argument, a name the zkDSL binds a Lean `let`. The iterations of an `unroll`
whose texts agree become one `for` loop (a name the body rebinds and reads across iterations a
`let mut`), the others are written out; an `@inline` function is a Lean function per distinct text
of its calls; a `Const` family one `GFn` family per distinct text of its instances. A construct
the builder lacks is a marked gap (`pure () -- GAP(...)`), and the function is left out of the
check.
-/

open LeanVM.Parameters LeanVM.Core
open LeanVM.Core.Expand (Bound Binding GAddr Known)

namespace DslTranslate

abbrev SE := Source.Expr
abbrev SS := Source.Stmt
abbrev SK := Source.StmtKind
abbrev Func := Source.Func

/-! ## Lean text -/

/-- A Lean term, and whether it needs no parentheses as an argument. -/
structure Tm where
  s : String
  atom : Bool := true
  deriving Inhabited, BEq

def Tm.arg (t : Tm) : String := if t.atom then t.s else "(" ++ t.s ++ ")"

def identChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '\''

def mk (s : String) : Tm := ⟨s, !s.isEmpty && s.all identChar⟩

def cmp (s : String) : Tm := ⟨s, false⟩

def app (f : String) (args : List Tm) : Tm := cmp (" ".intercalate (f :: args.map Tm.arg))

def bin (op : String) (a b : Tm) : Tm :=
  if op == "+" && a.s == "0" then b else if op == "+" && b.s == "0" then a
  else if op == "*" && a.s == "1" then b else if op == "*" && b.s == "1" then a
  else if op == "-" && b.s == "0" then a
  else cmp s!"{a.arg} {op} {b.arg}"

def bin2 (op : String) : Option Tm → Option Tm → Option Tm
  | some a, some b => some (bin op a b)
  | _, _ => none

def num (n : Nat) : Tm := mk (toString n)

/-- Names a translated text uses, which a source name must not shadow. -/
def reserved : List String :=
  ["at", "by", "do", "then", "else", "if", "fun", "let", "in", "for", "match", "with", "from", "end",
   "open", "def", "where", "have", "show", "return", "mut", "break", "continue", "import",
   "namespace", "section", "variable", "universe", "local", "private", "protected", "partial",
   "unsafe", "theorem", "example", "abbrev", "instance", "structure", "class", "inductive",
   "deriving", "calc", "unless", "repeat", "while", "try", "catch", "finally", "nomatch", "nofun",
   "macro", "syntax", "export", "mutual", "noncomputable", "opaque", "axiom", "prefix", "infix",
   "notation", "this", "pure", "default", "discard", "get", "set", "modify", "some", "none", "true",
   "false", "id", "cellOf", "wordOf", "lit", "hinted", "call1", "gpowE", "instName", "arrWord",
   "arrInt", "ps", "caps", "dsts", "rc", "arm", "B", "E", "V", "K", "Word", "GPow", "Shifted", "Nat",
   "List", "gen", "ofK", "gInv", "max", "min", "not", "and", "or", "xor", "word", "toString",
   "Keccak", "Msg", "Cells", "Operand", "Ret", "Dest", "Shape", "CArg"]

/-- The Lean name of a source name: camel case, clear of keywords and of the text's own names. -/
def camel (n : String) : String :=
  let parts := (n.splitOn "_").filter (· != "")
  let cap (p : String) : String := match p.toList with
    | c :: cs => String.ofList (c.toUpper :: cs)
    | [] => p
  let s := match parts with
    | [] => "x"
    | p :: rest => p ++ String.join (rest.map cap)
  let s := match s.toList with
    | c :: _ => if c.isDigit then "x" ++ s else s
    | [] => "x"
  if reserved.contains s then s ++ "'" else s

/-- Lines of a `do` block. -/
inductive Code where
  /-- A line; a binding's `let` carries its site (made `let mut` if a scope assigns it) and its
  Lean type. -/
  | line (s : String) (site : Option Nat := none) (ty : String := "")
  | blk (head : String) (body : Array Code) (close : String := "")
  | sub (ind : Nat) (c : Code)
  /-- A compile-time `if` (`if const(...)`, or literals): the branch a context took, the other
  one known once a context that takes it is merged in. -/
  | fold (cond : String) (thn els : Option (Array Code))
  deriving Inhabited

def pad (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- Whether a block ends with a binding, so it needs a closing `pure ()`. -/
def lastIsLet (b : Array Code) : Bool :=
  match b.back? with
  | some (.line s _ _) => s.startsWith "let "
  | some (.blk h _ _) => h.startsWith "let "
  | some (.sub _ _) => true
  | some (.fold ..) => false
  | none => true

/-- The name a `let` line binds (not `let _`, not a tuple). -/
def letName (s : String) : Option String :=
  if s.startsWith "let " && !s.startsWith "let _" && !s.startsWith "let (" && !s.startsWith "let mut " then
    some (String.ofList ((s.toList.drop 4).takeWhile (· != ' ')))
  else none

/-- `let x [: T] := e` (or `←`) as the assignment `x := e`. -/
def asAssign (s : String) : String :=
  let cs := s.toList.drop 4
  let name := cs.takeWhile (· != ' ')
  let rest := cs.drop name.length
  let rec find : List Char → List Char
    | [] => []
    | l@(' ' :: ':' :: '=' :: ' ' :: _) => l
    | l@(' ' :: '←' :: ' ' :: _) => l
    | _ :: t => find t
  String.ofList (name ++ find rest)

/-- `s` with the identifiers `ren` renames renamed (not a field after `.`, not in a string). -/
def renameToks (ren : List (String × String)) (s : String) : String := Id.run do
  if ren.isEmpty then return s
  let mut out : String := ""
  let mut tok : String := ""
  let mut prev : Char := ' '
  let mut inStr := false
  for c in s.toList ++ [' '] do
    if !inStr && (c.isAlphanum || c == '_' || c == '\'') then tok := tok.push c
    else
      if !tok.isEmpty then
        out := out ++ (if prev != '.' then ((ren.lookup tok).getD tok) else tok)
        tok := ""
      if c == '"' then inStr := !inStr
      out := out.push c
      prev := c
  return String.ofList (out.toList.dropLast)

/-- Lines of a `do` block. Lean lets no `let` shadow a `let mut` of the same `do`: such a `let` of
the same type is an assignment, of another type a new name (`x'`), which the lines after it read
(`ren`). `scope` holds the `let mut`s in scope and their types. -/
partial def renderB (muts : List Nat) (ind : Nat) (scope : List (String × String))
    (ren : List (String × String)) (cs : Array Code) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut sc := scope
  let mut rn := ren
  for c in cs do
    match c with
    | .line s site ty =>
        let isMut := (site.any muts.contains) && s.startsWith "let "
        match letName s with
        | some x =>
            let rhs := renameToks rn (String.ofList ((s.toList.drop 4).drop x.length))
            match sc.lookup x with
            | some tm =>
                if ty.isEmpty || ty == tm then
                  out := out.push (pad ind ++ asAssign ("let " ++ x ++ rhs))
                  rn := rn.filter (·.1 != x)
                else
                  let mut x' := x ++ "'"
                  while sc.any (·.1 == x') || rn.any (·.2 == x') do x' := x' ++ "'"
                  out := out.push (pad ind ++ (if isMut then "let mut " else "let ") ++ x' ++ rhs)
                  if isMut then sc := (x', ty) :: sc
                  rn := (x, x') :: rn.filter (·.1 != x)
            | none =>
                out := out.push (pad ind ++ (if isMut then "let mut " else "let ") ++ x ++ rhs)
                if isMut then sc := (x, ty) :: sc
                rn := rn.filter (·.1 != x)
        | none =>
            -- an assignment of a `let mut` reads the renamed names, and makes it current
            let target := String.ofList (s.toList.takeWhile fun c => c.isAlphanum || c == '_' || c == '\'')
            let isAssign := sc.any (·.1 == target) &&
              (s.startsWith (target ++ " := ") || s.startsWith (target ++ " ← "))
            if isAssign then
              out := out.push (pad ind ++ target ++ renameToks rn (String.ofList (s.toList.drop target.length)))
              rn := rn.filter (·.1 != target)
            else out := out.push (pad ind ++ renameToks rn s)
    | .blk head body close =>
        let body := if lastIsLet body then body.push (.line "pure ()") else body
        let b := renderB muts (ind + 2) (if head.startsWith "for " then sc else []) rn body
        let b := b.modify (b.size - 1) (· ++ close)
        out := out ++ #[pad ind ++ renameToks rn head] ++ b
    | .sub n c => out := out ++ renderB muts (ind + n) sc rn #[c]
    | .fold cnd t e =>
        let side := fun (b : Array Code) =>
          renderB muts (ind + 2) sc rn (if lastIsLet b then b.push (.line "pure ()") else b)
        let none' := #[Code.line "pure () -- no use of this definition takes this branch"]
        out := out.push (pad ind ++ s!"if {renameToks rn cnd} then") ++ side (t.getD none')
        out := out.push (pad ind ++ "else") ++ side (e.getD none')
  return out

def renderAll (muts : List Nat) (ind : Nat) (cs : Array Code) : String :=
  "\n".intercalate (renderB muts ind [] [] cs).toList

mutual
/-- Two contexts' texts as one, where they differ only in the branches of compile-time `if`s each
took; with the lines' sites a `mut` of the second makes one of the first. -/
partial def mergeC (muts : List Nat) : Code → Code → Option (Code × List Nat)
  | .line s1 st1 ty, .line s2 st2 _ =>
      if s1 == s2 then
        let extra := match st1, st2 with
          | some a, some b => if muts.contains b && !muts.contains a then [a] else []
          | _, _ => []
        some (.line s1 st1 ty, extra)
      else none
  | .blk h1 b1 c1, .blk h2 b2 c2 =>
      if h1 == h2 && c1 == c2 then (mergeA muts b1 b2).map fun (b, e) => (.blk h1 b c1, e) else none
  | .sub n1 c1, .sub n2 c2 =>
      if n1 == n2 then (mergeC muts c1 c2).map fun (c, e) => (.sub n1 c, e) else none
  | .fold c1 t1 e1, .fold c2 t2 e2 =>
      if c1 == c2 then do
        let (t, x1) ← mergeO muts t1 t2
        let (e, x2) ← mergeO muts e1 e2
        some (.fold c1 t e, x1 ++ x2)
      else none
  | _, _ => none

partial def mergeA (muts : List Nat) (a b : Array Code) : Option (Array Code × List Nat) :=
  if a.size != b.size then none
  else (a.zip b).foldlM (init := (#[], [])) fun (acc, ex) (x, y) =>
    (mergeC muts x y).map fun (c, e) => (acc.push c, ex ++ e)

partial def mergeO (muts : List Nat) : Option (Array Code) → Option (Array Code) →
    Option (Option (Array Code) × List Nat)
  | none, x => some (x, [])
  | x, none => some (x, [])
  | some a, some b => (mergeA muts a b).map fun (m, e) => (some m, e)
end

/-- The words of a text, for "does it name `x`". -/
def words (s : String) : List String :=
  let (ws, cur) := s.toList.foldl (fun (ws, cur) c =>
    if c.isAlphanum || c == '_' || c == '\'' then (ws, cur.push c)
    else if cur.isEmpty then (ws, cur) else (ws.push cur, "")) ((#[] : Array String), "")
  (if cur.isEmpty then ws else ws.push cur).toList

/-! ## State -/

/-- What a name is in the Lean text. -/
inductive LK where
  | word | run | nat | fe | gpow | ptr
  deriving BEq, Inhabited, Repr

def LK.ty : LK → String
  | .word => "Word" | .run => "List V" | .nat => "Nat" | .fe => "E" | .gpow => "GPow"
  | .ptr => "Shifted"

/-- A source name's binding: `Expand`'s, and its Lean name. -/
structure Bind where
  b : Bound
  lk : LK
  id : String
  site : Option Nat := none
  depth : Nat := 0
  mutOk : Bool := true
  /-- The field reading's text, when it is not `lit id`. -/
  feT : Option Tm := none
  deriving Inhabited

/-- An `unroll` written as a `for`: the names its body carries across iterations. -/
structure Loop where
  iterStart : Nat
  carried : List String
  depth : Nat
  /-- Declared before the loop: name, site, kind, copied from the outer name (else `default`). -/
  psites : List (String × Nat × LK × Bool) := []
  ok : Bool := true
  deriving Inhabited

/-- An `@inline` function's Lean text, per text that no other merges with. -/
structure Variant where
  fn : String
  name : String
  /-- `#[.blk "def NAME ... do" body]`. -/
  code : Array Code
  deriving Inhabited

/-- A translated unit: a function, a family instance. -/
structure Unit' where
  fn : String
  /-- The core name (`f`, `f__L3`). -/
  core : String
  consts : List SE
  /-- `#[.blk "def NAME ... : GFn where ... body ps := do" body]`, or a stub's text. -/
  code : Array Code
  stub : String := ""
  gaps : List String
  calls : List String
  deriving Inhabited

structure TSt where
  est : Expand.St
  prog : Source.Program
  py : Array String
  globals : List (String × Nat)
  env : List (String × Bind) := []
  sym : List (String × SE × Tm) := []
  code : Array Code := #[]
  tmp : Nat := 0
  vtag : Nat := 0
  site : Nat := 1
  muts : List Nat := []
  depth : Nat := 0
  loops : List Loop := []
  live : List String := []
  lineConsts : List (String × Nat) := []
  lineNums : List Nat := []
  finalRet : Bool := false
  returned : Bool := false
  gaps : List String := []
  calls : List String := []
  variants : Array Variant := #[]
  insts : Array (String × String × List SE) := #[]
  usedConsts : List String := []
  usedArrays : List String := []
  chainNext : Option V := none
  chainIn : Option V := none
  deriving Inhabited

abbrev T := StateT TSt (Except String)

instance {α : Type} : Inhabited (T α) := ⟨throw "unreachable"⟩

/-- Run an `Expand` reading on the expansion state, which it does not change. -/
def q {α : Type} (m : Expand.M α) : T α := do
  match m.run (← get).est with
  | .ok (a, _) => pure a
  | .error e => throw e

/-- `e` as `Expand` sees it: the `unroll` counters and `Const` parameters substituted. -/
def resolve (e : SE) : T SE := do
  return (← get).sym.foldl (fun e (x, l, _) => e.subst x l) e

def resolveStmts (ss : List SS) : T (List SS) := do
  return (← get).sym.foldl (fun b (x, l, _) => Source.Stmt.substList x l b) ss

def emit (c : Code) : T Unit := modify fun s => { s with code := s.code.push c }

def line (l : String) : T Unit := emit (.line l)

def newSite : T Nat := modifyGet fun s => (s.site, { s with site := s.site + 1 })

def newTmp : T String := modifyGet fun s => (s!"t{s.tmp}", { s with tmp := s.tmp + 1 })

def dummy (t i : Nat) : V := ⟨[.u 1000000000], t, i⟩

def freshV : T V := modifyGet fun s => (dummy s.vtag 0, { s with vtag := s.vtag + 1 })

def freshRunV (n : Nat) : T (List V) :=
  modifyGet fun s => ((List.range n).map (dummy s.vtag ·), { s with vtag := s.vtag + 1 })

def gap (what : String) : T Unit := do
  modify fun s => { s with gaps := if s.gaps.contains what then s.gaps else s.gaps ++ [what] }
  line s!"pure () -- GAP({what})"

def codeSize : T Nat := return (← get).code.size

/-- The tokens of a text: identifiers and numerals. -/
def tokens (s : String) : List String := words s

/-- The source line `l` sets the names a literal of it may be written as: the global constants it
names (a literal is written as the one constant of its value, unless the line also has the
numeral). -/
def setLine (l : Nat) : T Unit := do
  let s ← get
  let text := (s.py[l - 1]?).getD ""
  let text := String.ofList (text.toList.takeWhile (· != '#'))
  let toks := tokens text
  let consts := toks.filterMap fun t => (s.globals.find? (·.1 == t))
  let nums := toks.filterMap fun t => if t.all Char.isDigit then t.toNat? else none
  set { s with lineConsts := consts, lineNums := nums }

/-- A literal's text: the global constant the source line wrote, else the numeral. -/
def natLit (n : Nat) : T Tm := do
  let s ← get
  let cands := ((s.lineConsts.filter (·.2 == n)).map (·.1)).eraseDups
  if cands.length == 1 && !s.lineNums.contains n then
    let c := cands.head!
    modify fun s => { s with usedConsts := if s.usedConsts.contains c then s.usedConsts else c :: s.usedConsts }
    return mk c
  return num n

/-- A literal's field reading (`litField`). -/
def feOfLit (n : Nat) (t : Tm) : Tm :=
  if n == 0 then mk "0" else if n == 1 then mk "1" else app "lit" [t]

/-! ## Readings -/

/-- An expression's compile-time readings (`Expand.eval`) and their texts. -/
structure Rd where
  k : Known
  int : Option Tm := none
  fe : Option Tm := none
  base : Option Tm := none
  exp : Option Tm := none
  deriving Inhabited

def bindTexts (bd : Bind) : Rd :=
  let id := bd.id
  match bd.lk with
  | .word => { k := {}, base := mk id, exp := mk "0" }
  | .run => { k := {} }
  | .nat =>
      { k := {}, int := mk id, fe := some (bd.feT.getD (app "lit" [mk id])),
        exp := match bd.b.val with
          | .gaddr _ => some (app "Nat.log2" [mk id])
          | _ => none }
  | .fe => { k := {}, fe := mk id }
  | .gpow => { k := {}, fe := app "gpowE" [mk s!"{id}.exp"], exp := mk s!"{id}.exp" }
  | .ptr => { k := {}, base := mk s!"{id}.base", exp := mk s!"{id}.exp" }

partial def txt (e : SE) : T Rd := do
  let k ← q (Expand.eval Expand.evalFuel (← resolve e))
  let r : Rd ← match e with
    | .lit n => do
        let t ← natLit n
        pure { k, int := t, fe := feOfLit n t,
               exp := if Expand.isPow2Below64 n then some (num (Nat.log2 n)) else none }
    | .gen => pure { k, fe := app "gpowE" [num 1], exp := num 1 }
    | .gpow n => do
        let t ← natLit n
        pure { k, fe := app "gpowE" [t], exp := t }
    | .genPow x => do
        let rx ← txt x
        pure { k, fe := rx.int.map fun t => app "gpowE" [t], exp := rx.int }
    | .var v => do
        let s ← get
        match s.sym.find? (·.1 == v) with
        | some (_, .lit n, t) =>
            pure { k, int := t, fe := app "lit" [t],
                   exp := if Expand.isPow2Below64 n then some (app "Nat.log2" [t]) else none }
        | some (_, .gpow _, t) => pure { k, fe := app "gpowE" [t], exp := t }
        | some _ => pure { k }
        | none =>
            match s.env.find? (·.1 == v) with
            | some (_, bd) => pure { bindTexts bd with k }
            | none => pure { k }
    | .add a b => do
        let ra ← txt a; let rb ← txt b
        pure { k, int := bin2 "+" ra.int rb.int, fe := bin2 "+" ra.fe rb.fe }
    | .sub a b => do
        let ra ← txt a; let rb ← txt b
        pure { k, int := bin2 "-" ra.int rb.int }
    | .mul a b => do
        let ra ← txt a; let rb ← txt b
        pure { k, int := bin2 "*" ra.int rb.int, fe := bin2 "*" ra.fe rb.fe,
               base := ra.base.orElse fun _ => rb.base, exp := bin2 "+" ra.exp rb.exp }
    | .div a b => do
        let ra ← txt a; let rb ← txt b
        pure { k, int := bin2 "/" ra.int rb.int }
    | .mod a b => do
        let ra ← txt a; let rb ← txt b
        pure { k, int := bin2 "%" ra.int rb.int }
    | .pow b x => do
        let rb ← txt b; let rx ← txt x
        pure { k, int := bin2 "^" rb.int rx.int, fe := bin2 "^" rb.fe rx.int }
    | .index (.var arr) i => do
        if (← get).prog.constArrays.any (·.1 == arr) then
          modify fun s => { s with usedArrays := if s.usedArrays.contains arr then s.usedArrays else arr :: s.usedArrays }
          let ri ← txt i
          pure { k, int := ri.int.map fun t => app "arrInt" [mk arr, t],
                 fe := ri.int.map fun t => app "arrWord" [mk arr, t] }
        else pure { k }
    | .call "const" [a] => do
        let ra ← txt a
        pure { k, int := ra.int, fe := ra.int.map fun t => app "lit" [t] }
    | .call "len" [.var arr] => do
        modify fun s => { s with usedArrays := if s.usedArrays.contains arr then s.usedArrays else arr :: s.usedArrays }
        pure { k, int := mk s!"{arr}.length" }
    | _ => pure { k }
  return { r with
    int := if k.int.isSome then r.int else none
    fe := if k.field.isSome then r.fe else none
    base := match k.addr with
      | some ⟨some _, _, _⟩ => r.base
      | _ => none
    exp := if k.addr.isSome then r.exp else none }

def intT (e : SE) : T Tm := do
  let rd ← txt e
  match rd.int with
  | some t => return t
  | none => throw s!"internal: no integer text for {repr e}"

/-! ## Words -/

/-- A runtime word's text: a term, or an action computing it, and `Expand`'s value. -/
structure WT where
  t : Tm
  act : Bool := false
  v : V := default
  deriving Inhabited

def WT.use (w : WT) : String := if w.act then s!"(← {w.t.s})" else w.t.arg

def WT.vv (w : WT) : String := if w.act then s!"(← {w.t.s}).v" else w.t.arg ++ ".v"

def actW (s : String) : T WT := do return ⟨cmp s, true, ← freshV⟩

/-- Bind an action to a temporary, so that it runs here. -/
def hoist (w : WT) : T WT := do
  if !w.act then return w
  let t ← newTmp
  line s!"let {t} ← {w.t.s}"
  return { w with t := mk t, act := false }

/-- Insert lines at position `n0` of the current block. -/
def insertAt (n0 : Nat) (ls : Array Code) : T Unit :=
  modify fun s => { s with code := s.code.extract 0 n0 ++ ls ++ s.code.extract n0 s.code.size }

/-- Lower in order: an earlier action is bound to a temporary before a later lowering's lines. -/
def seqW (fs : List (T WT)) : T (List WT) := do
  let mut out : Array WT := #[]
  for f in fs do
    let n0 ← codeSize
    let w ← f
    if (← codeSize) != n0 then
      let mut ls : Array Code := #[]
      let mut fixed : Array WT := #[]
      for p in out do
        if p.act then
          let t ← newTmp
          ls := ls.push (.line s!"let {t} ← {p.t.s}")
          fixed := fixed.push { p with t := mk t, act := false }
        else fixed := fixed.push p
      insertAt n0 ls
      out := fixed
    out := out.push w
  return out.toList

/-- A value a statement binds to a name. -/
structure Val where
  b : Binding
  int : Option Nat := none
  lk : LK
  t : Tm
  act : Bool := false
  feT : Option Tm := none
  deriving Inhabited

def estBind (n : String) (b : Bound) : T Unit := modify fun s =>
  { s with est := { s.est with names := (n, b) :: s.est.names.filter (·.1 != n) } }

def envBind (n : String) (bd : Bind) : T Unit := modify fun s =>
  { s with env := (n, bd) :: s.env.filter (·.1 != n), sym := s.sym.filter (·.1 != n) }

/-- Change context `i` (innermost first). -/
def modCtx (i : Nat) (f : Loop → Loop) : T Unit :=
  modify fun s => { s with loops := s.loops.mapIdx fun j l => if j == i then f l else l }

/-- Merge two texts (`mergeA`), recording the `mut`s it carries over. -/
def mergeT (a b : Array Code) : T (Option (Array Code)) := do
  match mergeA (← get).muts a b with
  | some (m, extra) =>
      modify fun s => { s with muts := extra ++ s.muts }
      return some m
  | none => return none

/-- Bind `n` to `v` (`rebind`, `setInt`): a `let`, or, when the value must outlive the scopes it
is made in (an `unroll` iteration whose next one or whose sequel reads it, a compile-time `if`
branch whose sequel reads it), an assignment of the `let mut` before the outermost of them. -/
def defineName (n : String) (v : Val) : T Unit := do
  let s ← get
  let id := camel n
  let arrow := if v.act then "←" else ":="
  let tyAnn := match v.lk with
    | .fe | .gpow | .ptr => s!" : {v.lk.ty}"
    | _ => ""
  let bound : Bound := ⟨v.b, v.int⟩
  -- the outermost of the innermost scopes, at this depth, that the value must leave
  let mut m : Option Nat := none
  for (c, i) in s.loops.zipIdx do
    if c.depth == s.depth && c.carried.contains n then m := some i else break
  let mut target : Option Nat := none
  if let some i := m then
    let lp := s.loops[i]!
    let isP := fun (st : Nat) => (s.loops.drop i).any (·.psites.any (·.2.1 == st))
    let predecl : Bool → T Nat := fun copy => do
      let p ← newSite
      modCtx i fun l => { l with psites := l.psites ++ [(n, p, v.lk, copy)] }
      return p
    match s.env.find? (·.1 == n) with
    | some (_, cur) =>
        let outside := match cur.site with
          | some st => st < lp.iterStart || isP st
          | none => true
        if outside then
          if cur.lk != v.lk then pure ()
          else
            match cur.site with
            | some st =>
                if isP st then target := some st
                else if cur.mutOk && cur.depth == lp.depth then
                  modify fun s => { s with muts := if s.muts.contains st then s.muts else st :: s.muts }
                  target := some st
                else target := some (← predecl true)
            | none => target := some (← predecl true)
    | none => target := some (← predecl false)
    -- a value that must leave these scopes but is a `let`: they are written out, not loops or `if`s
    if target.isNone then
      for j in [0:i + 1] do modCtx j fun l => { l with ok := false }
  let feT := if v.lk == .nat then v.feT else none
  match target with
  | some st =>
      line s!"{id} {arrow} {v.t.s}"
      envBind n { b := bound, lk := v.lk, id, site := some st, depth := (← get).depth, feT }
  | none =>
      let st ← newSite
      emit (.line s!"let {id}{tyAnn} {arrow} {v.t.s}" (some st) v.lk.ty)
      envBind n { b := bound, lk := v.lk, id, site := some st, depth := (← get).depth, feT }
  estBind n bound

def runText (e : SE) : T (Option Tm) := do
  match e with
  | .var v => return ((← get).env.find? (·.1 == v)).map fun (_, bd) => mk bd.id
  | _ => return none

/-- A materialized address (`Expand.materialize`). -/
def matRd (ga : GAddr) (rd : Rd) : T WT := do
  match ga.base with
  | none => actW s!"B.const (gpowE {(rd.exp.getD (num ga.exp)).arg})"
  | some c =>
      let some base := rd.base | throw "internal: no base text"
      let expT := rd.exp.getD (num ga.exp)
      if ga.exp == 0 && (expT.s == "0" || ga.base.isSome && rd.exp.isNone) then return ⟨base, false, c⟩
      actW s!"B.shifted {base.arg} {(rd.exp.getD (num ga.exp)).arg}"

/-- A block of its own (a branch, an arm, a closure): its lines, its names reverted after. -/
def closure (m : T Unit) : T (Array Code) := do
  let s ← get
  set { s with code := #[], depth := s.depth + 1, finalRet := false }
  m
  let s' ← get
  set { s' with code := s.code, depth := s.depth, env := s.env, sym := s.sym,
                est := { s'.est with names := s.est.names }, live := s.live, finalRet := s.finalRet }
  return s'.code

/-- The `let mut`s a scope's assignments need before it. -/
def emitPredecls (lp : Loop) : T Unit := do
  for (n, st, lk, copy) in lp.psites do
    let id := camel n
    modify fun s => { s with muts := st :: s.muts }
    if copy then emit (.line s!"let {id} := {id}" (some st) lk.ty)
    else emit (.line s!"let {id} : {lk.ty} := default" (some st) lk.ty)

/-- A cell run's text (`Expand.CellRun`). -/
inductive CR where
  | stack (run : Tm) (cells : List V)
  | heap (ptr : WT) (lo len : Tm)

def CR.dest : CR → String
  | .stack r _ => s!"(.stack {r.arg})"
  | .heap p lo len => s!"(.heap {p.vv} {lo.arg} {len.arg})"

def CR.cells : CR → String
  | .stack r _ => s!"(.frame {r.arg})"
  | .heap p lo len => s!"(.heap {p.vv} {lo.arg} {len.arg})"

/-- `a0` with the positions where it holds `0` and `a1` holds `1` made the arm index. -/
partial def gen2 : SE → SE → Option SE
  | .lit 0, .lit 1 => some (.var "__arm")
  | .add a b, .add c d => return .add (← gen2 a c) (← gen2 b d)
  | .mul a b, .mul c d => return .mul (← gen2 a c) (← gen2 b d)
  | .sub a b, .sub c d => return .sub (← gen2 a c) (← gen2 b d)
  | .div a b, .div c d => return .div (← gen2 a c) (← gen2 b d)
  | .mod a b, .mod c d => return .mod (← gen2 a c) (← gen2 b d)
  | .fdiv a b, .fdiv c d => return .fdiv (← gen2 a c) (← gen2 b d)
  | .index a b, .index c d => return .index (← gen2 a c) (← gen2 b d)
  | .pow a b, .pow c d => return .pow (← gen2 a c) (← gen2 b d)
  | .genPow a, .genPow b => return .genPow (← gen2 a b)
  | .call f as, .call g bs =>
      if f == g && as.length == bs.length then return .call f (← (as.zip bs).mapM fun (x, y) => gen2 x y)
      else none
  | .list as, .list bs =>
      if as.length == bs.length then return .list (← (as.zip bs).mapM fun (x, y) => gen2 x y) else none
  | a, b => if a == b then some a else none

/-- The arms as one expression of the arm index `__arm`, when they are. -/
def generalize (arms : List SE) : Option SE := do
  let a0 ← arms[0]?
  let a1 ← arms[1]?
  let t ← gen2 a0 a1
  if (arms.zipIdx.all fun (a, j) => t.subst "__arm" (.lit j) == a) then some t else none

/-! ## Liveness -/

def readsOf (ss : List SS) : List String :=
  ss.foldl (fun acc s => (Source.Stmt.freeVars false s (acc, [])).1) []

/-- The names a block reads before it binds them. -/
def exposed (ss : List SS) : List String := Id.run do
  let mut seen : List String := []
  let mut out : List String := []
  for s in ss do
    for r in (Source.Stmt.freeVars false s ([], [])).1 do
      if !seen.contains r && !out.contains r then out := out ++ [r]
    seen := seen ++ Source.Stmt.binds false s
  return out

def carriedOf (body : List SS) (live : List String) : List String :=
  let ex := exposed body
  (Source.Stmt.bindsList false body).eraseDups.filter fun n => ex.contains n || live.contains n

/-! ## Lowering -/

mutual

/-- A value holding `e` (`Expand.expr`). -/
partial def tExpr (e : SE) : T WT := do
  let re ← resolve e
  if (← q (Expand.tryFieldConst re)).isSome then
    let rd ← txt e
    let some fe := rd.fe | throw s!"internal: no field text for {repr e}"
    return ← actW s!"B.const {fe.arg}"
  match e with
  | .pow b x => powExpr b x
  | .var v => do
      match (← get).env.find? (·.1 == v) with
      | some (_, bd) =>
          match bd.b.val with
          | .scalar c => return ⟨mk bd.id, false, c⟩
          | .gaddr ga => matRd ga (bindTexts bd)
          | .stack _ => throw s!"StackBuf `{v}` used as a scalar"
          | .fconst _ => throw "internal: a constant folds"
      | none => throw s!"unbound variable `{v}`"
  | .add a b => do
      if (← q (Expand.tryFieldConst (← resolve a))) == some 0 then return ← tExpr b
      if (← q (Expand.tryFieldConst (← resolve b))) == some 0 then return ← tExpr a
      let ws ← tExprs [a, b]
      actW s!"B.add {ws[0]!.use} {ws[1]!.use}"
  | .mul a b => do
      if (← q (Expand.tryFieldConst (← resolve a))) == some 1 then return ← tExpr b
      if (← q (Expand.tryFieldConst (← resolve b))) == some 1 then return ← tExpr a
      if let some ga ← q (Expand.gaddrOf re) then
        if ga.base.isSome then return ← matRd ga (← txt e)
      let ws ← tExprs [a, b]
      actW s!"B.mul {ws[0]!.use} {ws[1]!.use}"
  | .fdiv a b => do
      let ws ← tExprs [a, b]
      actW s!"B.fdiv {ws[0]!.use} {ws[1]!.use}"
  | .call "addr" [a] => do
      let some rt ← runText a | throw "addr() takes a StackBuf"
      actW s!"B.addr {rt.arg}"
  | .call "hint_log2_ceil" [a0, a1, a2] => do
      let nT ← intT a1
      let fT ← intT a2
      let d ← bitsDest a0 nT
      actW s!"hinted (B.hintLog2Ceil {d} {nT.arg} {fT.arg})"
  | .call f args => do
      let vs ← call f args 1 false
      let some v := vs.head? | throw "internal: no return binding"
      valCell v
  | .heapBuf sz => do actW s!"B.heapBuf {(← natLit sz).arg}"
  | .heapBufDyn x => do
      let w ← tExpr x
      actW s!"B.heapBufDyn {w.use}"
  | .index arr idx => do
      if let some c ← frameCell arr idx then return c
      let (p, off) ← heapAddrSpan arr idx 1
      actW s!"B.load {p.use} {off.arg}"
  | _ => throw s!"cannot lower {repr e} as a scalar"

partial def tExprs (es : List SE) : T (List WT) := seqW (es.map tExpr)

/-- The one cell of a value (`Expand.bindingCell`). -/
partial def valCell (v : Val) : T WT := do
  match v.b with
  | .scalar c => return ⟨v.t, v.act, c⟩
  | _ =>
      let t ← if v.act then do
          let t ← newTmp
          line s!"let {t} ← {v.t.s}"
          pure (mk t)
        else pure v.t
      match v.b with
      | .stack (c :: _) => return ⟨app "cellOf" [t, num 0], false, c⟩
      | .fconst _ =>
          let fe := v.feT.getD (if v.lk == .nat then app "lit" [t] else t)
          actW s!"B.const {fe.arg}"
      | .gaddr ga =>
          match v.lk with
          | .gpow => actW s!"B.const (gpowE {t.arg}.exp)"
          | .nat => actW s!"B.const {(v.feT.getD (app "lit" [t])).arg}"
          | .ptr => if ga.exp == 0 then return ⟨mk s!"{t.arg}.base", false, ga.base.getD default⟩
                    else actW s!"B.shifted {t.arg}.base {t.arg}.exp"
          | _ => return ⟨t, false, ga.base.getD default⟩
      | _ => throw "a multi-cell StackBuf return needs a `let` binding"

/-- `b ** x` (`Expand.powExpr`). -/
partial def powExpr (b x : SE) : T WT := do
  let some k ← q (Expand.tryConstIndex (← resolve x)) | throw "`**` exponent must be a compile-time integer"
  let kT ← intT x
  if (← q (Expand.tryFieldConst (← resolve b))).isSome then
    let rb ← txt b
    return ← actW s!"B.const ({rb.fe.get!.arg} ^ {kT.arg})"
  if k == 0 then
    let w ← tExpr b
    if w.act then line s!"discard <| {w.t.s}"
    return ← actW "B.const 1"
  let w ← tExpr b
  actW s!"B.pow {w.use} {kT.arg}"

/-- Lower `e` into the cell `d` (`Expand.exprInto`). -/
partial def exprInto (e : SE) (d : WT) : T Unit := do
  let re ← resolve e
  if (← q (Expand.tryFieldConst re)).isSome then
    let rd ← txt e
    return ← line s!"B.constInto {d.use} {rd.fe.get!.arg}"
  match e with
  | .index arr idx => do
      match ← frameCell arr idx with
      | some c => line s!"B.copy {d.use} {c.use}"
      | none => do
          let (p, off) ← heapAddrSpan arr idx 1
          line s!"B.loadInto {d.use} {p.use} {off.arg}"
  | .pow b x => do
      let v ← powExpr b x
      line s!"B.copy {d.use} {v.use}"
  | .add a b => do
      if (← q (Expand.tryFieldConst (← resolve a))) == some 0 then return ← exprInto b d
      if (← q (Expand.tryFieldConst (← resolve b))) == some 0 then return ← exprInto a d
      let ws ← tExprs [a, b]
      line s!"B.addInto {d.use} {ws[0]!.use} {ws[1]!.use}"
  | .mul a b => do
      if (← q (Expand.tryFieldConst (← resolve a))) == some 1 then return ← exprInto b d
      if (← q (Expand.tryFieldConst (← resolve b))) == some 1 then return ← exprInto a d
      let ws ← tExprs [a, b]
      line s!"B.mulInto {d.use} {ws[0]!.use} {ws[1]!.use}"
  | .call f args => do
      if (← q (Expand.origDef f)).isSome then return ← callInto f args [d]
      let v ← tExpr e
      line s!"B.copy {d.use} {v.use}"
  | _ => do
      let v ← tExpr e
      line s!"B.copy {d.use} {v.use}"

/-- The frame cell `arr[idx]`, if `arr` is a `StackBuf` (`Expand.frameCell`). -/
partial def frameCell (arr idx : SE) : T (Option WT) := do
  match ← q (Expand.stackOf (← resolve arr)) with
  | none => return none
  | some cells =>
      let k ← q (Expand.constIndex (← resolve idx))
      let some rt ← runText arr | throw "internal: no run text"
      let kT ← intT idx
      return some ⟨app "cellOf" [rt, kT], false, cells.getD k default⟩

/-- `arr[idx]` as a pointer and a folded exponent (`Expand.heapAddrSpan`). -/
partial def heapAddrSpan (arr idx : SE) (span : Nat) : T (WT × Tm) := do
  let ridx ← resolve idx
  let known ← q (Expand.eval Expand.evalFuel ridx)
  let arrays := (← get).prog.constArrays
  let element := match idx with
    | .index (.var v) _ => arrays.any (·.1 == v)
    | _ => false
  let plainInt := (match known.int with
    | some k => k != 1
    | none => false) && !element
  if plainInt || known.addr.isNone then
    if let some c := known.field then
      if known.diverging.isNone && !plainInt then
        if let some k := Expand.smallGpow c then
          return ← heapBase arr k (num k) span
      throw "heap index is a plain integer or a constant that is no g-power"
  let rd ← txt idx
  match known.addr with
  | some ⟨none, exp, _⟩ => return ← heapBase arr exp (rd.exp.getD (num exp)) span
  | some ⟨some _, exp, _⟩ => do
      if let some ga ← q (Expand.gaddrOf (← resolve arr)) then
        if let (some _, some total) := (ga.base, Expand.chk (ga.exp + exp)) then
          if total ≤ Expand.foldMax then
            let ra ← txt arr
            let p ← actW s!"B.mul {ra.base.get!.arg} {rd.base.get!.arg}"
            return (p, bin "+" ra.exp.get! rd.exp.get!)
  | none => pure ()
  arrayPtr arr idx

/-- `arr·g^extra` (`Expand.heapBase`). -/
partial def heapBase (arr : SE) (extra : Nat) (extraT : Tm) (_span : Nat) : T (WT × Tm) := do
  if let some ga ← q (Expand.gaddrOf (← resolve arr)) then
    if let (some c, some exp) := (ga.base, Expand.chk (ga.exp + extra)) then
      if exp ≤ Expand.foldMax then
        let ra ← txt arr
        return (⟨ra.base.get!, false, c⟩, bin "+" ra.exp.get! extraT)
  let a ← tExpr arr
  if extra == 0 then return (a, num 0)
  let p ← actW s!"B.mul {a.use} (← B.const (gpowE {extraT.arg}))"
  return (p, num 0)

/-- A runtime heap index (`Expand.arrayPtr`). -/
partial def arrayPtr (arr idx : SE) : T (WT × Tm) := do
  if let .mul a b := idx then
    if let some k ← q (Expand.constGpow (← resolve a)) then
      let ws ← tExprs [arr, b]
      let ra ← txt a
      let p ← actW s!"B.mul {ws[0]!.use} {ws[1]!.use}"
      return (p, ra.exp.getD (num k))
    if let some k ← q (Expand.constGpow (← resolve b)) then
      let ws ← tExprs [arr, a]
      let rb ← txt b
      let p ← actW s!"B.mul {ws[0]!.use} {ws[1]!.use}"
      return (p, rb.exp.getD (num k))
  let ws ← tExprs [arr, idx]
  let p ← actW s!"B.mul {ws[0]!.use} {ws[1]!.use}"
  return (p, num 0)

/-- The run of cells `e` names (`Expand.cellRun`). -/
partial def cellRun (e : SE) : T CR := do
  match e with
  | .var _ => do
      let some cells ← q (Expand.stackOf (← resolve e)) | throw "only a StackBuf names a run of cells unsliced"
      let some rt ← runText e | throw "internal: no run text"
      return .stack rt cells
  | .slice arr lo hi => do
      match ← q (Expand.tryConstIndex (← resolve lo)), ← q (Expand.tryConstIndex (← resolve hi)) with
      | some l, some h => do
          let lT ← intT lo
          let hT ← intT hi
          let lenT := bin "-" hT lT
          match ← q (Expand.stackOf (← resolve arr)) with
          | some cells => do
              let some rt ← runText arr | throw "internal: no run text"
              let run := if lT.s == "0" then cmp s!"{rt.arg}.take {lenT.arg}"
                else cmp s!"({rt.arg}.drop {lT.arg}).take {lenT.arg}"
              return .stack run ((cells.drop l).take (h - l))
          | none => do
              let (p, off) ← heapBase arr l lT (h - l)
              return .heap p off lenT
      | _, _ => do
          let some k := Expand.plusK (← resolve lo) (← resolve hi) | throw "a runtime slice must be `buf[i:i + k]`"
          let (p, off) ← heapAddrSpan arr lo k
          return .heap p off (← natLit k)
  | _ => throw "expected a StackBuf, a StackBuf slice, or a HeapBuf slice"

/-- A hint's bit destination (`Expand.bitsDest`). -/
partial def bitsDest (e : SE) (nT : Tm) : T String := do
  match ← q (Expand.stackOf (← resolve e)) with
  | some _ => do
      let some rt ← runText e | throw "internal: no run text"
      return s!"(.stack ({rt.arg}.take {nT.arg}))"
  | none => do
      let w ← tExpr e
      return s!"(.heap {w.vv} 0 {nT.arg})"

/-- The core name of a call (a `Const` specialization's `instName`) and its runtime arguments. -/
partial def calleeName (f : String) (args : List SE) : T (String × List SE) := do
  let some d ← q (Expand.origDef f) | return (s!"\"{f}\"", args)
  if !d.hasConstParams then return (s!"\"{f}\"", args)
  let rargs ← args.mapM resolve
  let substs ← match ← q (Expand.constSubsts d rargs) with
    | .ok s => pure s
    | .error e => throw e
  let mut cs : Array String := #[]
  for (p, a) in d.params.zip args do
    if p.kind == .const then
      let c := ((substs.find? (·.1 == p.name)).map (·.2)).getD (.lit 0)
      let rd ← txt a
      match c with
      | .gpow k => cs := cs.push s!".G {(rd.exp.getD (num k)).arg}"
      | .lit n => cs := cs.push s!".L {(rd.int.getD (num n)).arg}"
      | _ => pure ()
  let name := Expand.specName f substs
  modify fun s => { s with
    insts := if s.insts.any (·.1 == name) then s.insts else s.insts.push (name, f, substs.map (·.2))
    calls := if s.calls.contains name then s.calls else s.calls ++ [name] }
  let rt := ((d.params.zip args).filter fun (p, _) => p.kind != .const).map (·.2)
  return (s!"(instName \"{f}\" [{", ".intercalate cs.toList}])", rt)

/-- The argument cells of a call, `StackBuf` parameters as their runs. -/
partial def argList (f : String) (args : List SE) : T String := do
  let some d ← q (Expand.origDef f) | throw s!"no function named `{f}`"
  let shapes := (d.params.filter (·.kind != .const)).map Source.Param.shape
  let flags := (shapes.zip args).map fun (s, _) => s != Source.Shape.scalar
  let ws ← seqW ((shapes.zip args).map fun (s, a) => match s with
    | .stackBuf _ => do
        let some rt ← runText a | throw s!"`{f}` takes a StackBuf"
        pure (⟨rt, false, default⟩ : WT)
    | .scalar => tExpr a)
  let mut parts : Array String := #[]
  let mut cur : Array String := #[]
  for (w, isRun) in ws.zip flags do
    if isRun then
      if !cur.isEmpty then parts := parts.push s!"[{", ".intercalate cur.toList}]"; cur := #[]
      parts := parts.push w.t.arg
    else cur := cur.push w.vv
  if !cur.isEmpty then parts := parts.push s!"[{", ".intercalate cur.toList}]"
  return if parts.isEmpty then "[]" else if parts.size == 1 then parts[0]! else "(" ++ " ++ ".intercalate parts.toList ++ ")"

/-- A call binding `nRet` values (`Expand.call`); with `stmt`, a statement whose values nothing
reads. -/
partial def call (f : String) (args : List SE) (nRet : Nat) (stmt : Bool) : T (List Val) := do
  if f == "keccak" || f == "keccak_cells" then throw s!"{f} is a statement"
  if let some vs ← tryInline f args none then
    if stmt then
      for v in vs do
        if v.act then line s!"let _ ← {v.t.s}"
    return vs
  let d ← q (Expand.origDef f)
  let shapes := (d.map (·.returnShapes)).getD (List.replicate nRet Source.Shape.scalar)
  let (name, rt) ← calleeName f args
  let argsT ← argList f rt
  if shapes.all (· == .scalar) then
    if stmt then
      line s!"let _ ← B.call {name} {argsT} {nRet}"
      return []
    if nRet == 1 then
      return [{ b := .scalar (← freshV), lk := .word, t := cmp s!"call1 {name} {argsT}", act := true }]
    let t ← newTmp
    line s!"let {t} ← B.call {name} {argsT} {nRet}"
    (List.range nRet).mapM fun i => do
      return { b := .scalar (← freshV), lk := .word, t := cmp s!"{t}[{i}]!" }
  else
    let t ← newTmp
    let shT := ", ".intercalate (shapes.map fun | .scalar => ".scalar" | .stackBuf n => s!".buf {n}")
    line s!"let {t} ← B.callShaped {name} {argsT} [{shT}]"
    if stmt then return []
    (shapes.zipIdx).mapM fun (sh, i) => do
      match sh with
      | .scalar => return { b := .scalar (← freshV), lk := .word, t := app "cellOf" [cmp s!"{t}[{i}]!", num 0] }
      | .stackBuf n => return { b := .stack (← freshRunV n), lk := .run, t := cmp s!"{t}[{i}]!" }

/-- A call writing its values into `dsts` (`Expand.callInto`). -/
partial def callInto (f : String) (args : List SE) (dsts : List WT) : T Unit := do
  if (← tryInline f args (some dsts)).isNone then
    let (name, rt) ← calleeName f args
    let argsT ← argList f rt
    line s!"B.callInto {name} {argsT} [{", ".intercalate (dsts.map WT.vv)}]"

/-- An `@inline` call (`Expand.tryInline`): the callee is a Lean function per distinct text,
called here. -/
partial def tryInline (f : String) (args : List SE) (into : Option (List WT)) : T (Option (List Val)) := do
  let some d := (← q (Expand.origDef f)).filter (·.inline) | return none
  let rargs ← args.mapM resolve
  let substs ← match ← q (Expand.constSubsts d rargs) with
    | .ok s => pure s
    | .error _ => throw s!"`@inline {f}`: bad arity or unresolved Const argument"
  let some (body, rets) := Source.splitTailReturn d.body
    | throw s!"`@inline {f}` requires one tail `return`"
  let mut sig : Array String := #[]
  let mut argFs : Array (T WT) := #[]
  let mut binds : Array (String × Bind) := #[]
  let mut scalarAt : Array (Nat × String) := #[]
  let mut syms : Array (String × SE × Tm) := #[]
  for (p, a) in d.params.zip args do
    let id := camel p.name
    if p.kind == .const then
      let c := ((substs.find? (·.1 == p.name)).map (·.2)).getD (.lit 0)
      let rd ← txt a
      let at' : Tm := match c with
        | .gpow k => rd.exp.getD (num k)
        | .lit n => rd.int.getD (num n)
        | _ => num 0
      sig := sig.push s!"({id} : Nat)"
      argFs := argFs.push (pure ⟨at', false, default⟩)
      syms := syms.push (p.name, c, mk id)
    else
      let ra ← resolve a
      match ← q (Expand.aliasOf ra) with
      | some (.stack cells) =>
          let some rt ← runText a | throw "internal: no run text"
          sig := sig.push s!"({id} : List V)"
          argFs := argFs.push (pure ⟨rt, false, default⟩)
          binds := binds.push (p.name, { b := ⟨.stack cells, none⟩, lk := .run, id, mutOk := false })
      | some (.gaddr ga) =>
          let rd ← txt a
          match ga.base with
          | none =>
              sig := sig.push s!"({id} : GPow)"
              argFs := argFs.push (pure ⟨mk s!"⟨{(rd.exp.getD (num ga.exp)).s}⟩", false, default⟩)
              binds := binds.push (p.name, { b := ⟨.gaddr ga, none⟩, lk := .gpow, id, mutOk := false })
          | some _ =>
              if ga.exp == 0 then
                sig := sig.push s!"({id} : Word)"
                argFs := argFs.push (pure ⟨rd.base.get!, false, default⟩)
                binds := binds.push (p.name, { b := ⟨.gaddr ga, none⟩, lk := .word, id, mutOk := false })
              else
                sig := sig.push s!"({id} : Shifted)"
                argFs := argFs.push (pure ⟨mk s!"⟨{rd.base.get!.s}, {rd.exp.get!.s}⟩", false, default⟩)
                binds := binds.push (p.name, { b := ⟨.gaddr ga, none⟩, lk := .ptr, id, mutOk := false })
      | some _ => throw "internal: an alias is a run or an address"
      | none =>
          match ← q (Expand.tryFieldConst ra) with
          | some c =>
              let rd ← txt a
              sig := sig.push s!"({id} : E)"
              argFs := argFs.push (pure ⟨rd.fe.get!, false, default⟩)
              binds := binds.push (p.name, { b := ⟨.fconst c, none⟩, lk := .fe, id, mutOk := false })
          | none =>
              sig := sig.push s!"({id} : Word)"
              scalarAt := scalarAt.push (argFs.size, p.name)
              argFs := argFs.push (tExpr a)
              binds := binds.push (p.name, { b := ⟨.scalar default, none⟩, lk := .word, id, mutOk := false })
  let ws ← seqW argFs.toList
  for (i, n) in scalarAt do
    binds := binds.map fun (m, bd) => if m == n then (m, { bd with b := ⟨.scalar (ws[i]!.v), none⟩ }) else (m, bd)
  let argTexts := ws.map WT.use
  -- the callee, in a scope of its own
  let saved ← get
  let dstT : List WT := match into with
    | some ds => (ds.zipIdx).map fun (dw, i) => ⟨app "cellOf" [mk "dsts", num i], false, dw.v⟩
    | none => []
  set { saved with
    env := binds.toList.reverse, sym := syms.toList, code := #[], loops := [], depth := 0, tmp := 0,
    est := { saved.est with names := binds.toList.reverse.map fun (nb : String × Bind) => (nb.1, nb.2.b) },
    live := rets.foldl (fun acc (e : SE) => e.freeVars acc) [], gaps := [], calls := [], finalRet := false }
  stmts body
  let vals ← match into with
    | none => rets.mapM fun e => do
        let v ← letVal e
        let v ← if v.act then do
            let t ← newTmp
            line s!"let {t} ← {v.t.s}"
            pure { v with t := mk t, act := false }
          else pure v
        -- the caller reads an integer constant as its field word
        if v.lk == .nat then
          return { v with lk := .fe, t := v.feT.getD (app "lit" [v.t]), int := none, feT := none }
        return v
    | some _ => do
        returnInto rets dstT
        pure []
  let after ← get
  let retT := match vals.map (·.lk.ty) with
    | [] => "Unit"
    | [t] => t
    | ts => " × ".intercalate ts
  let mut body := after.code
  match vals with
  | [] => pure ()
  | [v] => body := body.push (.line s!"return {v.t.s}")
  | vs => body := body.push (.line s!"return ({", ".intercalate (vs.map (·.t.s))})")
  let dstSig := if into.isSome then " (dsts : List V)" else ""
  let sigT := String.join (sig.toList.map (" " ++ ·))
  let head := s!"def NAME{sigT}{dstSig} : B ({retT}) := B.inline \"{f}\" do"
  let vcode : Array Code := #[.blk head body]
  set { after with
    env := saved.env, sym := saved.sym, code := saved.code, loops := saved.loops,
    depth := saved.depth, tmp := saved.tmp, live := saved.live,
    est := { after.est with names := saved.est.names },
    gaps := saved.gaps ++ after.gaps.filter (!saved.gaps.contains ·),
    calls := saved.calls ++ after.calls.filter (!saved.calls.contains ·),
    lineConsts := saved.lineConsts, lineNums := saved.lineNums, finalRet := saved.finalRet,
    returned := saved.returned }
  let s ← get
  let mut found : Option String := none
  for (vr, i) in s.variants.zipIdx do
    if found.isNone && vr.fn == f then
      if let some m ← mergeT vr.code vcode then
        modify fun s => { s with variants := s.variants.set! i { vr with code := m } }
        found := some vr.name
  let name ← match found with
    | some nm => pure nm
    | none => do
        let k := (s.variants.filter (·.fn == f)).size
        let nm := if k == 0 then camel f else s!"{camel f}_{k + 1}"
        modify fun s => { s with variants := s.variants.push { fn := f, name := nm, code := vcode } }
        pure nm
  let dstArg := match into with
    | some ds => [s!"[{", ".intercalate (ds.map WT.vv)}]"]
    | none => []
  let callT := " ".intercalate (name :: argTexts ++ dstArg)
  match into with
  | some _ =>
      line callT
      return some []
  | none =>
      match vals with
      | [] =>
          line callT
          return some []
      | [v] => return some [{ v with t := cmp callT, act := true }]
      | vs =>
          let ts ← vs.mapM fun _ => newTmp
          line s!"let ({", ".intercalate ts}) ← {callT}"
          return some ((vs.zip ts).map fun (v, t) => { v with t := mk t, act := false })

/-- An inlined `return` into cells (`Expand.returnInto`). -/
partial def returnInto (es : List SE) (dsts : List WT) : T Unit := do
  let mut aliased : Array (Binding × SE × WT) := #[]
  for (e, d) in es.zip dsts do
    match ← q (Expand.aliasOf (← resolve e)) with
    | some b => aliased := aliased.push (b, e, d)
    | none => exprInto e d
  for (b, e, d) in aliased do
    let c ← match b with
      | .stack (c :: _) => do
          let some rt ← runText e | throw "internal: no run text"
          pure (⟨app "cellOf" [rt, num 0], false, c⟩ : WT)
      | .gaddr ga => matRd ga (← txt e)
      | _ => throw "a multi-cell StackBuf return needs a `let` binding"
    if c.v != d.v then line s!"B.copy {d.use} {c.use}"

/-- What `name = e` binds (`Expand.letBinding`). -/
partial def letVal (e : SE) : T Val := do
  let re ← resolve e
  let known ← q (Expand.eval Expand.evalFuel re)
  match ← q (Expand.aliasOf re) with
  | some (.stack cells) =>
      let some rt ← runText e | throw "internal: no run text"
      return { b := .stack cells, lk := .run, t := rt }
  | some (.gaddr ga) =>
      let rd ← txt e
      match ga.base with
      | none =>
          if let some k := known.int then
            let feT := if known.field == some (litField k) then none else rd.fe
            return { b := .gaddr ga, int := k, lk := .nat, t := rd.int.get!, feT }
          return { b := .gaddr ga, lk := .gpow, t := mk s!"⟨{(rd.exp.getD (num ga.exp)).s}⟩" }
      | some _ =>
          if ga.exp == 0 then return { b := .gaddr ga, lk := .word, t := rd.base.get! }
          return { b := .gaddr ga, lk := .ptr, t := mk s!"⟨{rd.base.get!.s}, {rd.exp.get!.s}⟩" }
  | some _ => throw "internal: an alias is a run or an address"
  | none =>
  if let some c := known.field then
    let rd ← txt e
    if let some k := known.int then
      return { b := .fconst c, int := k, lk := .nat, t := rd.int.get!,
               feT := if c == litField k then none else rd.fe }
    return { b := .fconst c, lk := .fe, t := rd.fe.get! }
  if let some k := known.int then
    let rd ← txt e
    return { b := .fconst (litField k), int := k, lk := .nat, t := rd.int.get! }
  if let .call f args := e then
    if (← q (Expand.origDef f)).isSome then
      let vs ← call f args 1 false
      let some v := vs.head? | throw "internal: no return binding"
      return v
  let w ← tExpr e
  return { b := .scalar w.v, lk := .word, t := w.t, act := w.act }

/-- A returned value as a `Ret`: a pure one when lowering it writes nothing else, else the
lowering into the return cell, run in order (`Ret.into`). -/
partial def retOf (e : SE) : T String := do
  let re ← resolve e
  if (← q (Expand.tryFieldConst re)).isSome then
    return s!".c {(← txt e).fe.get!.arg}"
  let snap ← get
  let n0 ← codeSize
  let pureForm : Option String ← match e with
    | .var _ => do
        let w ← tExpr e
        pure (if w.act then none else some s!".v {w.vv}")
    | .index arr idx => do
        match ← frameCell arr idx with
        | some c => pure (some s!".v {c.vv}")
        | none => do
            let (p, off) ← heapAddrSpan arr idx 1
            pure (if p.act then none else some s!".load {p.vv} {off.arg}")
    | .add a b | .mul a b => do
        let ws ← tExprs [a, b]
        let op := match e with | .add .. => ".add" | _ => ".mul"
        pure (if ws.any (·.act) then none else some s!"{op} {ws[0]!.vv} {ws[1]!.vv}")
    | _ => pure none
  if let some r := pureForm then
    if (← codeSize) == n0 then return r
  set snap
  let rcell : WT := ⟨app "wordOf" [mk "rc"], false, ← freshV⟩
  let body ← closure (exprInto e rcell)
  let t ← newTmp
  emit (.blk s!"let {t} : V → B Unit := fun rc => do" body)
  return s!".into {t}"

/-- `return` of a function that is not `@inline` (`Expand.lowerReturn`). -/
partial def lowerReturn (es : List SE) : T Unit := do
  let c := (← get).est.ctx
  if c.isMain then return
  let mut parts : Array String := #[]
  for (e, shape) in es.zip c.returnShapes do
    match shape with
    | .scalar => parts := parts.push s!"[{← retOf e}]"
    | .stackBuf _ =>
        let some rt ← runText e | throw "expected a StackBuf return"
        parts := parts.push s!"{rt.arg}.map Ret.v"
  let lst := if parts.isEmpty then "[]" else " ++ ".intercalate parts.toList
  if (← get).finalRet then
    line s!"return {lst}"
    modify fun s => { s with returned := true }
  else line s!"B.ret ({lst})"

/-- A compile-time `if`: a Lean `if` on the condition's text, with the branch taken here (the
other one is filled when contexts merge); a name a branch binds and the sequel reads is a
`let mut` before it. Where a branch rebinds such a name with another kind, the taken branch is
written out instead. -/
partial def foldIf (eq : Bool) (lhs rhs : SE) (ints : Bool) (taken : Bool) (thn els : List SS) :
    T Unit := do
  let rl ← txt lhs
  let rr ← txt rhs
  let (lt, rt) := if ints then (rl.int, rr.int) else (rl.fe, rr.fe)
  let some lt := lt | throw "internal: no condition text"
  let some rt := rt | throw "internal: no condition text"
  let cond := s!"{lt.arg} {if eq then "=" else "≠"} {rt.arg}"
  let s ← get
  let carried := (Source.Stmt.bindsList false (thn ++ els)).eraseDups.filter s.live.contains
  modify fun s => { s with loops := { iterStart := s.site, carried, depth := s.depth } :: s.loops,
                           code := #[] }
  stmts (if taken then thn else els)
  let s' ← get
  let lp := s'.loops.head!
  set { s' with loops := s'.loops.drop 1, code := s.code }
  emitPredecls lp
  if lp.ok then emit (.fold cond (if taken then some s'.code else none) (if taken then none else some s'.code))
  else modify fun s => { s with code := s.code ++ s'.code }

/-- `if` (`Expand.lowerIf`): folded where `Expand` folds it, else a branch. -/
partial def lowerIf (eq : Bool) (lhs rhs : SE) (thn els : List SS) (fc : Bool) : T Unit := do
  let rl ← resolve lhs
  let rr ← resolve rhs
  let a ← q (Expand.eval Expand.evalFuel rl)
  let b ← q (Expand.eval Expand.evalFuel rr)
  if let (some ai, some bi) := (a.int, b.int) then
    if !fc then
      for kk in [a, b] do
        if let some (i, _) := kk.diverging then throw s!"a side reads as the integer {i} and another value"
    let taken := (ai == bi) == eq
    return ← foldIf eq lhs rhs true taken thn els
  if fc then
    if let (some fa, some fb) := (a.field, b.field) then
      let taken := (fa == fb) == eq
      return ← foldIf eq lhs rhs false taken thn els
    throw "`if const(...)` asks for a compile-time decision"
  let x ← if (← q (Expand.tryLit rr)) == some 0 then tExpr lhs
    else if (← q (Expand.tryLit rl)) == some 0 then tExpr rhs
    else do
      let ws ← tExprs [lhs, rhs]
      actW s!"B.add {ws[0]!.use} {ws[1]!.use}"
  let x ← hoist x
  let (zBlk, nBlk) := if eq then (thn, els) else (els, thn)
  let z ← closure (stmts zBlk)
  if nBlk.isEmpty then
    emit (.blk s!"B.ite0 {x.t.arg} do" z)
  else
    let nz ← closure (stmts nBlk)
    line s!"let _ ← B.ite {x.t.arg}"
    emit (.sub 2 (.blk "(do" z ")"))
    emit (.sub 2 (.blk "(do" nz ")"))

/-- `assert a != b` (`Expand.lowerAssertNe`). -/
partial def lowerAssertNe (a b : SE) : T Unit := do
  if let (.lit x, .lit y) := (← resolve a, ← resolve b) then
    if x == y then throw "assert a != b on equal literals"
    return
  let ws ← tExprs [a, b]
  line s!"B.assertNe {ws[0]!.use} {ws[1]!.use}"

/-- `assert log e < bound` (`Expand.lowerAssertLt`): the bound first. -/
partial def lowerAssertLt (e : SE) (bd : Source.LtBound) : T Unit := do
  match bd with
  | .const k => do
      let kT ← natLit k
      let snap ← get
      let x ← tExpr e
      if !x.act && (← codeSize) == snap.code.size then
        line s!"let _ ← B.rangeCheck {x.use} {kT.arg}"
      else
        set snap
        let t ← newTmp
        line s!"let {t} ← B.const (gpowE ({kT.arg} - 1))"
        let x ← tExpr e
        line s!"let _ ← B.rangeCheckK {x.use} {t}"
  | .runtime b => do
      let rb ← resolve b
      if (← q (Expand.tryFieldConst rb)).isSome then
        throw "a compile-time range-check bound must be written as `log GEN ** k`"
      let t ← newTmp
      match ← q (Expand.gaddrOf rb) with
      | some ⟨some _, _ + 1, none⟩ =>
          let rd ← txt b
          line s!"let {t} ← B.shifted {rd.base.get!.arg} ({rd.exp.get!.s} - 1)"
      | _ =>
          let bc ← tExpr b
          line s!"let {t} ← B.mul {bc.use} (← B.const (ofK gInv))"
      let x ← tExpr e
      line s!"let _ ← B.rangeCheckK {x.use} {t}"

/-- The cells of a `match`'s targets (`Expand.retTargets`): their texts, and the names to bind. -/
partial def targetsOf (targets : List SE) : T (String × List WT × List (String × Nat)) := do
  let nVars := (targets.filter Source.Expr.isVar).length
  let run ← freshRunV nVars
  let t ← newTmp
  let mut ts : Array String := #[]
  let mut cells : Array WT := #[]
  let mut names : Array (String × Nat) := #[]
  let mut k := 0
  for (tg, i) in targets.zipIdx do
    match tg with
    | .index arr idx => do
        let some c ← frameCell arr idx | throw "a multi-value target must be a name or a StackBuf element"
        ts := ts.push s!"some {c.vv}"
        cells := cells.push ⟨app "cellOf" [mk t, num i], false, c.v⟩
    | .var n =>
        ts := ts.push "none"
        cells := cells.push ⟨app "cellOf" [mk t, num i], false, run.getD k default⟩
        names := names.push (n, i)
        k := k + 1
    | _ => throw "a multi-value target must be a name or a StackBuf element"
  line s!"let {t} ← B.targets [{", ".intercalate ts.toList}]"
  return (t, cells.toList, names.toList)

partial def bindTargets (t : String) (cells : List WT) (names : List (String × Nat)) : T Unit := do
  for (n, i) in names do
    defineName n { b := .scalar (cells.getD i default).v, lk := .word, t := app "cellOf" [mk t, num i] }

/-- The arms of a `match`, as one function of the arm index where their texts agree. -/
partial def emitArms (head : String) (arms : List SE) (armF : SE → T Unit) : T Unit := do
  if let some tmpl := generalize arms then
    let mut merged : Option (Array Code) := none
    let mut all := true
    for j in List.range arms.length do
      let c ← closure do
        modify fun s => { s with sym := ("__arm", .lit j, mk "arm") :: s.sym }
        armF tmpl
      match merged with
      | none => merged := some c
      | some m =>
          match ← mergeT m c with
          | some m' => merged := some m'
          | none => all := false
    if let (true, some first) := (all, merged) then
      let nT ← natLit arms.length
      let armId := if (words (renderAll [] 0 first)).contains "arm" then "arm" else "_"
      emit (.blk s!"{head} ((List.range {nT.arg}).map fun {armId} => do" first ")")
      return
  let mut names : Array String := #[]
  let base ← newTmp
  for (arm, j) in arms.zipIdx do
    let c ← closure (armF arm)
    let nm := s!"{base}_{j}"
    emit (.blk s!"let {nm} : B Unit := do" c)
    names := names.push nm
  line s!"{head} [{", ".intercalate names.toList}]"

/-- `match` (`Expand.lowerMatch`). -/
partial def lowerMatch (targets : List SE) (x : SE) (arms : List SE) : T Unit := do
  let allCalls ← arms.allM fun a => do
    match a with
    | .call f _ => return (← q (Expand.origDef f)).any (!·.inline)
    | _ => return false
  if allCalls && !arms.isEmpty then
    let rts ← arms.mapM fun a => do
      match a with
      | .call f cargs => do
          let some d ← q (Expand.origDef f) | throw "internal"
          let rt := ((d.params.zip cargs).filter fun (p, _) => p.kind != .const).map (·.2)
          rt.mapM resolve
      | _ => throw "internal: a call arm"
    let rt0 := rts.head!
    if rts.all (· == rt0) then return ← lowerDispatch targets x arms
  let s ← get
  let (chainNext, chainIn) := (s.chainNext, s.chainIn)
  modify fun s => { s with chainNext := none, chainIn := none }
  let xo ← match chainIn with
    | some c => do
        let w ← tExpr x
        pure { w with v := c }
    | none => do hoist (← tExpr x)
  let (t, cells, names) ← targetsOf targets
  if chainNext.isSome then line "B.chain"
  let isInline : SE → T Bool := fun a => match a with
    | .call f _ => return (← q (Expand.origDef f)).any (·.inline)
    | _ => return false
  if chainIn.isNone && (← arms.allM isInline) then line "Keccak.inlineArms"
  let armF : SE → T Unit := fun arm => do
    match cells with
    | [rc] => exprInto arm rc
    | _ => do
        let .call f cargs := arm | throw "a multi-target match arm must be a function call"
        callInto f cargs cells
  emitArms s!"let _ ← B.matchArms {xo.t.arg}" arms armF
  modify fun s => { s with chainIn := chainNext }
  bindTargets t cells names

/-- A fused `match` of calls (`Expand.lowerDispatchedCall`). -/
partial def lowerDispatch (targets : List SE) (x : SE) (arms : List SE) : T Unit := do
  let (t, cells, names) ← targetsOf targets
  let .call f0 cargs0 := arms.head! | throw "internal"
  let some d0 ← q (Expand.origDef f0) | throw "internal"
  let rt0 := ((d0.params.zip cargs0).filter fun (p, _) => p.kind != .const).map (·.2)
  let ws ← tExprs rt0
  let ws ← ws.mapM hoist
  let xo ← tExpr x
  -- every arm's name (queueing each instance), and the list as a function of the arm index
  let mut armNames : Array String := #[]
  for a in arms do
    let .call f cargs := a | throw "internal"
    let snap ← get
    let (nm, _) ← calleeName f cargs
    let s' ← get
    set { snap with insts := s'.insts, calls := s'.calls, usedConsts := s'.usedConsts }
    armNames := armNames.push nm
  let namesT ← match generalize arms with
    | some (.call f cargs) => do
        let snap ← get
        modify fun s => { s with sym := ("__arm", .lit 0, mk "arm") :: s.sym }
        let (nm, _) ← calleeName f cargs
        set { snap with usedConsts := (← get).usedConsts }
        let nT ← natLit arms.length
        pure s!"((List.range {nT.arg}).map fun arm => {nm})"
    | _ => pure s!"[{", ".intercalate armNames.toList}]"
  line s!"B.dispatchInto {xo.use} {namesT} [{", ".intercalate (ws.map WT.vv)}] {t}"
  bindTargets t cells names

/-- `for var in mul_range(GEN ** lo, hi)` (`Expand.lowerFor`): a loop helper, its captures
lowered after the entry test. -/
partial def lowerFor (l : Nat) (var : String) (lo : Nat) (hi : Source.ForBound) (body : List SS) : T Unit := do
  let rbody ← resolveStmts body
  let (refs, bound) := Source.Stmt.freeVarsList false rbody ([], [var])
  let (liveRefs, liveBound) := Source.Stmt.freeVarsList true rbody ([], [var])
  let readsOuter : String → Bool := fun r => liveRefs.contains r && !liveBound.contains r
  let shadowed := Source.Stmt.bindsList false rbody
  let own := Source.Stmt.bindsList true rbody
  let mut caps : Array (String × Source.Shape) := #[]
  for r in refs do
    if bound.contains r && !readsOuter r then continue
    if let some cells ← q (Expand.stackOfName r) then
      if !shadowed.contains r || (readsOuter r && !own.contains r) then
        if !caps.any (·.1 == r) then caps := caps.push (r, .stackBuf cells.length)
        continue
    match ← q (Expand.lookup r) with
    | some ⟨.scalar _, _⟩ | some ⟨.gaddr _, _⟩ | some ⟨.fconst _, _⟩ =>
        if !caps.any (·.1 == r) then caps := caps.push (r, .scalar)
    | _ => pure ()
  let runtime := match hi with | .runtime _ => true | .const _ => false
  let ncaps := (caps.toList.map fun (_, s) => s.cells).sum
  -- the captures' cells, lowered in the caller when the loop is entered
  let capWs ← seqW (caps.toList.map fun (n, s) => match s with
    | .stackBuf _ => do
        let some rt ← runText (.var n) | throw "internal: no run text"
        pure (⟨rt, false, default⟩ : WT)
    | .scalar => tExpr (.var n))
  let mut parts : Array String := #[]
  let mut cur : Array String := #[]
  let mut anyAct := false
  for (w, (_, s)) in capWs.zip caps.toList do
    if w.act then anyAct := true
    match s with
    | .stackBuf _ =>
        if !cur.isEmpty then parts := parts.push s!"[{", ".intercalate cur.toList}]"; cur := #[]
        parts := parts.push w.t.arg
    | .scalar => cur := cur.push w.vv
  if !cur.isEmpty then parts := parts.push s!"[{", ".intercalate cur.toList}]"
  let capList := if parts.isEmpty then "[]" else " ++ ".intercalate parts.toList
  let capsT := if anyAct then s!"(do return {capList})" else s!"(pure ({capList}))"
  -- the entry bound
  let mut hiT := ""
  match hi with
  | .const _ => pure ()
  | .runtime e => do
      let mut be := e
      if Expand.callsOrAllocates (← resolve e) then
        let nm := s!"__entry_{(← get).site}"
        stmtKind l (.let_ nm e)
        be := .var nm
      let n0 ← codeSize
      let w ← tExpr be
      if (← codeSize) != n0 then throw "a loop bound that lowers to more than a value"
      hiT := if w.act then w.t.arg else s!"(pure {w.t.arg})"
  -- the helper's body, in its own scope; a capture its body binds is its own name
  let params : List Source.Param := [⟨var, .runtime .scalar⟩] ++
    (if runtime then [⟨"__bound", .runtime .scalar⟩] else []) ++ caps.toList.map fun (n, s) => ⟨n, .runtime s⟩
  let helper : Func := { name := "__loop", params, returnShapes := [], body := rbody, inline := false }
  let xId := camel var
  let saved ← get
  let mut ownNames : List String := []
  let mut bodyCode : Array Code := #[]
  for _ in List.range (params.length + 1) do
    let est := Expand.initState saved.prog helper #[] 0 ownNames
    let pb := (Expand.paramBindings helper).1
    set { saved with
      est := { est with tag := saved.est.tag }, env := [], code := #[], loops := [],
      depth := saved.depth + 1, tmp := 0, finalRet := false, live := [] }
    if let some (_, b) := pb.find? (·.1 == var) then
      envBind var { b, lk := .word, id := xId, mutOk := false }
    let mut pos := 0
    for (n, s) in caps do
      if !ownNames.contains n then
        if let some (_, b) := pb.find? (·.1 == n) then
          match s with
          | .scalar => defineName n { b := b.val, lk := .word, t := app "cellOf" [mk "caps", num pos] }
          | .stackBuf k => defineName n { b := b.val, lk := .run, t := cmp s!"(caps.drop {pos}).take {k}" }
      pos := pos + s.cells
    stmts body
    -- `settleLoopCaptures`: a capture not bound to the value it arrived in is the body's own
    let mut new : List String := []
    for (n, _) in caps do
      if ownNames.contains n then continue
      let arrived := (pb.find? (·.1 == n)).map (·.2.val)
      let now ← q (Expand.lookup n)
      let kept := match arrived, now.map (·.val) with
        | some (.scalar a), some (.scalar b) => a == b
        | some (.stack a), some (.stack b) => a == b
        | _, _ => false
      if !kept then new := new ++ [n]
    bodyCode := (← get).code
    if new.isEmpty then break
    ownNames := ownNames ++ new
  let after ← get
  set { after with
    env := saved.env, sym := saved.sym, code := saved.code, loops := saved.loops,
    depth := saved.depth, tmp := saved.tmp, live := saved.live, est := saved.est,
    lineConsts := saved.lineConsts, lineNums := saved.lineNums, finalRet := saved.finalRet,
    returned := saved.returned }
  let loT ← natLit lo
  match hi with
  | .const h =>
      let hT ← natLit h
      emit (.blk s!"B.loopConstF {loT.arg} {hT.arg} {ncaps} {capsT} fun {xId} caps => do" bodyCode)
  | .runtime _ =>
      emit (.blk s!"B.loopRtF {loT.arg} {hiT} {ncaps} {capsT} fun {xId} caps => do" bodyCode)

/-- A Keccak operand (`Expand.keccakWords`): a list of words, or a run. -/
partial def kOperand (e : SE) : T String := do
  if let .list ws := e then
    let ms ← seqW (ws.map fun w => do
      if (← q (Expand.tryConstInt (← resolve w))) == some 0 then return (⟨mk ".zero", false, default⟩ : WT)
      let x ← tExpr w
      return ⟨cmp s!".cell {x.vv}", false, x.v⟩)
    return s!"(.words [{", ".intercalate (ms.map (·.t.s))}])"
  let r ← cellRun e
  return s!"(.cells {r.cells})"

/-- `keccak(...)` (`Expand.lowerKeccak`). -/
partial def lowerKeccak (args : List SE) : T Unit := do
  let kw ← q (Expand.keccakKwargs args "keccak" ["a", "b", "out"] ["tail", "len", "cap", "pad_tail"])
  let a ← kOperand (args.getD 0 default)
  let b ← kOperand (args.getD 1 default)
  let tail ← match Expand.kwGet kw "tail" with
    | some t => do pure s!" (tail := some {← kOperand t})"
    | none => pure ""
  match Expand.kwGet kw "cap" with
  | some cap => do
      let c ← cellRun cap
      let out ← cellRun (args.getD 2 default)
      line s!"B.keccakDuplex (a := {a}) (b := {b}){tail} (cap := {c.cells}) (out := {out.cells})"
  | none => do
      let len ← match Expand.kwGet kw "len" with
        | some e => do pure s!" (len := some {(← intT e).arg})"
        | none => pure ""
      let padTail := if (Expand.kwGet kw "pad_tail").isSome then " (padTail := true)" else ""
      let out ← cellRun (args.getD 2 default)
      line s!"B.keccak (a := {a}) (b := {b}){tail}{len}{padTail} (out := {out.cells})"

/-- `keccak_cells(...)` (`Expand.lowerKeccakCells`). -/
partial def lowerKeccakCells (args : List SE) : T Unit := do
  let kw ← q (Expand.keccakKwargs args "keccak_cells" ["cells", "out"] ["state", "len", "final"])
  let cellsT ← match args.getD 0 default with
    | .listComp body var lo hi => do
        let some l ← q (Expand.tryConstInt (← resolve lo)) | throw "list comprehension bounds"
        let some h ← q (Expand.tryConstInt (← resolve hi)) | throw "list comprehension bounds"
        let ms ← seqW ((List.range' l (h - l)).map fun i => do
          modify fun s => { s with sym := (var, .lit i, num i) :: s.sym }
          let r ← do
            if (← q (Expand.tryConstInt (← resolve body))) == some 0 then pure (⟨mk ".zero", false, default⟩ : WT)
            else
              let x ← tExpr body
              pure ⟨cmp s!".cell {x.vv}", false, x.v⟩
          modify fun s => { s with sym := s.sym.drop 1 }
          return r)
        pure s!"(.words [{", ".intercalate (ms.map (·.t.s))}])"
    | e => kOperand e
  let st ← match Expand.kwGet kw "state" with
    | some e => do pure s!" (state := some {(← cellRun e).cells})"
    | none => pure ""
  let fin ← match Expand.kwGet kw "final" with
    | some e => do
        let some k ← q (Expand.tryConstInt (← resolve e)) | throw "keccak `final`"
        pure (if k != 0 then "" else " (final := false)")
    | none => pure ""
  let len ← match Expand.kwGet kw "len" with
    | some e => do pure s!" (len := some {(← intT e).arg})"
    | none => pure ""
  let out ← cellRun (args.getD 1 default)
  line s!"B.keccakCells (cells := {cellsT}){st}{len}{fin} (out := {out.cells})"

/-- The builtins (`Expand.lowerBuiltin`); `false` for another callee. -/
partial def lowerBuiltin (f : String) (args : List SE) : T Bool := do
  match f with
  | "hint_decompose_bits" | "hint_decompose_bits_exponent" => do
      let plain := f == "hint_decompose_bits"
      let nT ← intT args[2]!
      let d ← bitsDest args[0]! nT
      let x ← tExpr args[1]!
      if plain then
        let sT ← match args[3]? with
          | some s => intT s
          | none => pure (num 0)
        line s!"B.hintBits {d} {x.use} {sT.arg} {nT.arg}"
      else line s!"B.hintBitsExpTo {d} {x.use} {nT.arg}"
      return true
  | "hint_windows_exponent" => do
      let startT ← intT args[2]!
      let widthT ← intT args[3]!
      let countT ← intT args[4]!
      let skipT ← match args[5]? with
        | some a => intT a
        | none => pure (num 0)
      let d ← bitsDest args[0]! (bin "+" skipT countT)
      let x ← tExpr args[1]!
      line s!"B.hintWindowsExp {d} {x.use} {startT.arg} {widthT.arg} {countT.arg} {skipT.arg}"
      return true
  | "hint_decompose_digits_exponent" => do
      let [a0, a1, a2, a3, a4, a5] := args | throw s!"{f} takes six arguments"
      let nbitsT ← intT a2
      let ndT ← intT a3
      let dbT ← intT a4
      let d ← bitsDest a0 ndT
      let x ← tExpr a1
      match ← q (Expand.tryConstIndex (← resolve a5)) with
      | some _ =>
          let sT ← intT a5
          line s!"B.hintDigitsExp {d} {x.use} {nbitsT.arg} {ndT.arg} {dbT.arg} {sT.arg}"
      | none =>
          let sc ← tExpr a5
          line s!"B.hintDigitsExp {d} {x.use} {nbitsT.arg} {ndT.arg} {dbT.arg} 0 (startCell := some {sc.use})"
      return true
  | "assert_gpow" => do
      let [a0] := args | throw "assert_gpow(x) takes one scalar cell"
      let x ← tExpr a0
      line s!"let _ ← B.assertGpow {x.use}"
      return true
  | "keccak" => do lowerKeccak args; return true
  | "keccak_cells" => do lowerKeccakCells args; return true
  | "assert_in_k" => do
      let [a0, a1] := args | throw "assert_in_k(a, b) takes two scalar cells"
      let ws ← tExprs [a0, a1]
      line s!"B.assertInK {ws[0]!.use} {ws[1]!.use}"
      return true
  | "hint_f128_limbs" => do
      let [dd, v] := args | throw "hint_f128_limbs takes two arguments"
      let some rt ← runText dd | throw "hint_f128_limbs writes frame cells"
      let x ← tExpr v
      line s!"B.hintLimbs {x.use} {rt.arg}"
      return true
  | _ => return false

/-- One iteration of an `unroll` body at counter `j`, its counter written `kT`: its lines, and
whether it may be one of a `for` loop's (its carried names kept their kinds). -/
partial def iteration (var : String) (j h : Nat) (kT : Tm) (body : List SS) (loopMode : Bool) :
    T (Array Code × Bool) := do
  let s ← get
  set { s with code := #[], sym := (var, .lit j, kT) :: s.sym,
               loops := if loopMode then (match s.loops with
                 | l :: ls => { l with iterStart := s.site, ok := true } :: ls
                 | [] => []) else s.loops }
  let arr := body.toArray
  for i in [0:arr.size] do
    let st := arr[i]!
    -- a `match` whose next statement, in this iteration or the next, is one it chains into
    if let .match_ targets _ arms := st.kind then
      let symNow := (← get).sym
      let subst := fun (sy : List (String × SE × Tm)) (x : SS) =>
        (sy.foldl (fun b (n, l, _) => Source.Stmt.substList n l b) [x]).head!
      let nxt : Option SS :=
        if i + 1 < arr.size then some (subst symNow arr[i+1]!)
        else if j + 1 < h then some (subst ((var, .lit (j + 1), kT) :: symNow.drop 1) arr[0]!)
        else none
      if let some nxs := nxt then
        if let .match_ _ nxx narms := nxs.kind then
          let rarms ← arms.mapM resolve
          let rtargets ← targets.mapM resolve
          if (← q (Expand.allInline rarms)) && (← q (Expand.allInline narms)) then
            if let some c ← q (Expand.freeCell nxx rtargets) then
              modify fun s => { s with chainNext := some c }
    let rest := (arr.extract (i + 1) arr.size).toList
    modify fun s' => { s' with live := readsOf rest ++ readsOf body ++ s.live }
    stmtKind st.line st.kind
  let s' ← get
  let ok := if loopMode then (match s'.loops with
    | l :: _ => l.ok
    | [] => true) else true
  set { s' with code := s.code, sym := s.sym, live := s.live }
  return (s'.code, ok)

/-- `for var in unroll(lo, hi)`: the iterations whose texts agree as `for` loops. -/
partial def lowerUnroll (var : String) (lo hi : SE) (body : List SS) : T Unit := do
  let some l ← q (Expand.tryConstIndex (← resolve lo)) | throw "unroll bounds must be compile-time integers"
  let some h ← q (Expand.tryConstIndex (← resolve hi)) | throw "unroll bounds must be compile-time integers"
  if h < l then throw s!"unroll(a, b) needs a <= b, got ({l}, {h})"
  if h == l then return
  let loT ← intT lo
  let hiT ← intT hi
  -- the counter's Lean name, clear of every name in scope (a written-out iteration binds it with a
  -- `let` that outlives the `unroll`)
  let s0 ← get
  let mut kId := camel var
  while s0.env.any (·.2.id == kId) || s0.sym.any (·.2.2.s == kId) do kId := kId ++ "'"
  let carried := carriedOf body s0.live
  let loop : Loop := { iterStart := s0.site, carried, depth := s0.depth }
  -- every iteration, as one of a loop's: a carried name is assigned, a name it binds otherwise
  -- is a `let`; the code of an iteration is valid in a `for` with the others of its text, or
  -- written out after its counter's `let`
  modify fun s => { s with loops := loop :: s.loops }
  let mut codes : Array (Array Code) := #[]
  let mut oks : Array Bool := #[]
  let tmp0 := (← get).tmp
  let mut tmpMax := tmp0
  for j in [l:h] do
    modify fun s => { s with tmp := tmp0 }
    let (c, ok) ← iteration var j h (mk kId) body true
    tmpMax := max tmpMax (← get).tmp
    codes := codes.push c
    oks := oks.push ok
  modify fun s => { s with tmp := tmpMax }
  -- runs of iterations whose texts merge
  let mut segs : Array (Nat × Nat × Array Code) := #[]
  let mut start := l
  while start < h do
    let mut stop := start + 1
    let mut cur := codes[start - l]!
    if oks[start - l]! then
      let mut go := true
      while go && stop < h && oks[stop - l]! do
        match ← mergeT cur codes[stop - l]! with
        | some m => cur := m; stop := stop + 1
        | none => go := false
    segs := segs.push (start, stop, cur)
    start := stop
  let lp := (← get).loops.head!
  modify fun s => { s with loops := s.loops.drop 1 }
  emitPredecls lp
  for (a, b, c) in segs do
    let named := (words (renderAll [] 0 c)).contains kId
    if b - a == 1 then
      if named then line s!"let {kId} := {a}"
      modify fun s => { s with code := s.code ++ c }
    else
      let aT := if a == l then loT else num a
      let bT := if b == h then hiT else num b
      emit (.blk s!"for {if named then kId else "_"} in [{aT.s}:{bT.s}] do" c)

/-- A statement, its errors naming its source line. -/
partial def stmtKind (l : Nat) (k : SK) : T Unit := do
  try stmtKind' l k
  catch e => throw (if e.startsWith "line " then e else s!"line {l}: {e}")

/-- A statement (`Expand.stmtKind`). -/
partial def stmtKind' (l : Nat) (k : SK) : T Unit := do
  setLine l
  match k with
  | .let_ name e => do
      match e with
      | .stackBuf sz => do
          let cells ← freshRunV sz
          defineName name { b := .stack cells, lk := .run, t := cmp s!"B.stackBuf {(← natLit sz).arg}", act := true }
      | .list es => do
          let cells ← freshRunV es.length
          let t ← newTmp
          line s!"let {t} ← B.stackBuf {es.length}"
          for (el, i) in es.zipIdx do
            exprInto el ⟨app "cellOf" [mk t, num i], false, cells.getD i default⟩
          defineName name { b := .stack cells, lk := .run, t := mk t }
      | .call "addr" [a] => do
          let some cells ← q (Expand.stackOf (← resolve a)) | throw "addr() names a frame run"
          let some rt ← runText a | throw "internal: no run text"
          let p ← freshV
          defineName name { b := .gaddr ⟨some p, 0, some cells.length⟩, lk := .word, t := app "B.addr" [rt], act := true }
      | _ => do
          let known ← q (Expand.eval Expand.evalFuel (← resolve e))
          let v ← letVal e
          defineName name { v with int := known.int }
  | .letTuple names f args => do
      let vs ← call f args names.length false
      for (nm, v) in names.zip vs do defineName nm v
  | .assertEq a b => do
      let ws ← tExprs [a, b]
      line s!"B.assertEq {ws[0]!.use} {ws[1]!.use}"
  | .assertNe a b => lowerAssertNe a b
  | .assertLt e bd => lowerAssertLt e bd
  | .hintWitness dest stream => do
      let r ← cellRun dest
      line s!"B.witness \"{stream}\" {r.dest}"
  | .letHintWitness name stream => do
      defineName name { b := .scalar (← freshV), lk := .word, t := cmp s!"hinted (B.witnessCell \"{stream}\")", act := true }
  | .print _ value => do
      let w ← tExpr value
      if w.act then line s!"discard <| {w.t.s}"
      line "B.anchor"
  | .ite eq lhs rhs thn els fc => lowerIf eq lhs rhs thn els fc
  | .match_ targets x arms => lowerMatch targets x arms
  | .call f args => do
      if !(← lowerBuiltin f args) then
        let nRet := ((← q (Expand.origDef f)).map (·.returnShapes.length)).getD 0
        discard <| call f args nRet true
  | .store arr idx val => do
      match ← frameCell arr idx with
      | some c => exprInto val c
      | none => do
          let v ← tExpr val
          let n0 ← codeSize
          let (p, off) ← heapAddrSpan arr idx 1
          let v ← if v.act && (p.act || (← codeSize) != n0) then do
              let t ← newTmp
              insertAt n0 #[.line s!"let {t} ← {v.t.s}"]
              pure { v with t := mk t, act := false }
            else pure v
          line s!"B.store {p.use} {off.arg} {v.use}"
  | .ret es => lowerReturn es
  | .callIfNe .. => throw "internal: a loop's own call in the source"
  | .for_ var lo hi body => lowerFor l var lo hi body
  | .unroll var lo hi body => lowerUnroll var lo hi body

partial def stmts (ss : List SS) : T Unit := do
  let parent := (← get).live
  let arr := ss.toArray
  for i in [0:arr.size] do
    let st := arr[i]!
    modify fun s => { s with live := readsOf (arr.extract (i + 1) arr.size).toList ++ parent }
    stmtKind st.line st.kind
  modify fun s => { s with live := parent }

end

/-! ## Functions -/

/-- The source text of function `name`, and its line. -/
def sourceOf (py : Array String) (name : String) : Option (Nat × String) := do
  let i ← py.findIdx? (·.startsWith s!"def {name}(")
  let start := if i > 0 && (py[i - 1]!).startsWith "@inline" then i - 1 else i
  let mut j := i + 1
  while j < py.size && (py[j]!.isEmpty || py[j]!.startsWith " " || py[j]!.startsWith "\t") do j := j + 1
  let mut e := j
  while e > i + 1 && (py[e - 1]!).all Char.isWhitespace do e := e - 1
  return (i + 1, "\n".intercalate (py.extract start e).toList)

/-- A function's docstring. -/
def docOf (py : Array String) (name : String) (what : String) : String :=
  match sourceOf py name with
  | some (l, src) => s!"/-- {what} (`guests/lean_ethereum.py`, line {l}):\n\n```\n{src}\n```\n-/"
  | none => s!"/-- {what}. -/"

/-- The section of the guest a function's source is in. -/
def sectionOf (py : Array String) (name : String) : String := Id.run do
  let some i := py.findIdx? (·.startsWith s!"def {name}(") | return "Main"
  let mut j := i
  while j > 0 do
    j := j - 1
    let l := py[j]!
    if l.startsWith "# ===" then
      let title := String.ofList ((l.toList.dropWhile (fun c => c == '#' || c == '=' || c == ' ')).reverse.dropWhile
        (fun c => c == '=' || c == ' ')).reverse
      return String.join ((title.splitOn " ").filterMap fun w =>
        let w := String.ofList (w.toList.filter fun c => c.isAlphanum)
        match w.toList with
        | c :: cs => some (String.ofList (c.toUpper :: cs))
        | [] => none)
  return "Head"

/-- Translate a function (or a `Const` instance, `consts` its literals) to its `GFn` body. -/
def fnBody (f : Func) (consts : List SE) : T (Array Code) := do
  let s ← get
  let spec ← match Expand.specializeFn f consts with
    | .ok sp => pure (if consts.isEmpty then f else sp)
    | .error e => throw e
  let est := Expand.initState s.prog spec #[] 0 []
  let constPs := f.params.filter (·.kind == .const)
  set { s with
    est, env := [], sym := ((constPs.zip consts).map fun (pc : Source.Param × SE) => (pc.1.name, pc.2, mk (camel pc.1.name))),
    code := #[], tmp := 0, depth := 0, loops := [], live := [], finalRet := false,
    returned := false, gaps := [], calls := [], chainNext := none, chainIn := none }
  let pb := (Expand.paramBindings spec).1
  let mut pos := 0
  for p in spec.params do
    if let some (_, b) := pb.find? (·.1 == p.name) then
      match p.shape with
      | .scalar => defineName p.name { b := b.val, lk := .word, t := app "cellOf" [mk "ps", num pos] }
      | .stackBuf k => defineName p.name { b := b.val, lk := .run, t := cmp s!"(ps.drop {pos}).take {k}" }
    pos := pos + p.shape.cells
  match f.body.getLast? with
  | some (.mk l (.ret es)) =>
      modify fun s => { s with live := (Source.Stmt.freeVars false (.mk l (.ret es)) ([], [])).1 }
      stmts f.body.dropLast
      modify fun s => { s with finalRet := true }
      stmtKind l (.ret es)
  | _ => stmts f.body
  if !(← get).returned then line "return []"
  return (← get).code

/-- A `GFn`'s definition (`header` from `def` to before `where`, `NAME` its name). -/
def gfnCode (f : Func) (header : String) (nameT : String) (code : Array Code) : Array Code :=
  let arity := ((f.params.filter (·.kind != .const)).map fun p => p.shape.cells).sum
  let rets := (f.returnShapes.map Source.Shape.cells).sum
  #[.line s!"{header} where", .line s!"  name := {nameT}", .line s!"  arity := {arity}",
    .line s!"  rets := {rets}", .sub 2 (.blk "body ps := do" code)]

/-- A definition's text: its docstring, its code; a long one elaborates with a deeper recursion
limit (its `do` block is one nested term). -/
def defText (py : Array String) (muts : List Nat) (fn what name : String) (code : Array Code) : String :=
  let body := (renderAll muts 0 code).replace "def NAME" s!"def {name}"
  let deep := if (body.splitOn "\n").length > 300 then "set_option maxRecDepth 100000 in\nset_option maxHeartbeats 10000000 in\n" else ""
  s!"set_option linter.unusedVariables false in\n{deep}{docOf py fn what}\n" ++ body ++ "\n\n"

end DslTranslate

open DslTranslate

/-- The global constants of the configuration (`def const_NAME : Nat := v` in the generated
source data). -/
def readGlobals (text : String) : List (String × Nat) :=
  (text.splitOn "\n").filterMap fun l =>
    if l.startsWith "def const_" then
      let rest := String.ofList (l.toList.drop 10)
      match rest.splitOn " : Nat := " with
      | [n, v] => v.toNat?.map (n, ·)
      | _ => none
    else none

def modHeader (mod : String) (doc : String) (imports : List String) (opens : Bool := true) : String :=
  s!"/-\n  LeanVM.Dsl.Gen.{mod}\n\n  {doc}\n-/\n\nmodule\n\n" ++
  String.join (imports.map fun i => s!"public import {i}\n") ++
  "\nnamespace LeanVM.Dsl.Gen\n\n" ++ (if opens then "open LeanVM.Parameters LeanVM.Core LeanVM.Dsl\n\n" else "") ++
  "@[expose] public section\n\n"

def modFooter : String := "end\nend LeanVM.Dsl.Gen\n"

def main (args : List String) : IO UInt32 := do
  let outDir : System.FilePath := (args.head?.getD "LeanVM/Dsl/Gen")
  let pyText ← IO.FS.readFile "../../guests/lean_ethereum.py"
  let py := (pyText.splitOn "\n").toArray
  let globals := readGlobals (← IO.FS.readFile "LeanVM/Guest/Data/Source.lean")
  let bad := ["E", "V", "K", "B", "Word", "GPow", "Shifted", "Ret", "Msg", "Cells", "Operand", "Dest", "Shape"]
  let globals := globals.filter fun (n, _) => !bad.contains n
  let prog := LeanVM.Guest.Data.guest
  let st0 : TSt := { est := default, prog, py, globals }
  -- the functions `Expand` lowers as written, `main` first
  let some mainF := prog.funcs.find? (·.name == "main") | throw (IO.userError "no main")
  let originals := mainF :: (prog.funcs.filter fun f => f.name != "main" && !f.inline && !f.hasConstParams)
  let mut st := st0
  let mut units : Array Unit' := #[]
  for f in originals do
    IO.eprintln s!"{(← IO.monoMsNow)} {f.name}"
    match (fnBody f []).run st with
    | .ok (code, st') =>
        let code := gfnCode f "def NAME : GFn" s!"\"{f.name}\"" code
        units := units.push { fn := f.name, core := f.name, consts := [], gaps := st'.gaps, calls := st'.calls, code }
        st := st'
    | .error e =>
        IO.eprintln s!"{f.name}: {e}"
        let stub := s!"set_option linter.unusedVariables false in\n{docOf py f.name s!"`{f.name}`: not translated ({e})"}\ndef {camel f.name} : GFn where\n  name := \"{f.name}\"\n  arity := 0\n  rets := 0\n  body _ := do\n    pure () -- GAP(error)\n    return []\n\n"
        units := units.push { fn := f.name, core := f.name, consts := [], gaps := [s!"error: {e}"], calls := [], code := #[], stub }
  -- the `Const` instances, as they are found
  let mut done : List String := []
  let mut instUnits : Array Unit' := #[]
  let mut progress := true
  while progress do
    progress := false
    for (nm, fn, cs) in st.insts do
      if done.contains nm then continue
      done := nm :: done
      progress := true
      let some f := prog.funcs.find? (·.name == fn) | continue
      IO.eprintln s!"{(← IO.monoMsNow)} {nm}"
      let constPs := f.params.filter (·.kind == .const)
      let cargs := (constPs.zip cs).map fun (p, c) => match c with
        | .gpow _ => s!".G {camel p.name}"
        | _ => s!".L {camel p.name}"
      let nameT := s!"instName \"{fn}\" [{", ".intercalate cargs}]"
      let header := s!"def NAME{String.join (constPs.map fun p => s!" ({camel p.name} : Nat)")} : GFn"
      match (fnBody f cs).run st with
      | .ok (code, st') =>
          let code := gfnCode f header nameT code
          instUnits := instUnits.push { fn, core := nm, consts := cs, gaps := st'.gaps, calls := st'.calls, code }
          st := st'
      | .error e =>
          IO.eprintln s!"{nm}: {e}"
          instUnits := instUnits.push { fn, core := nm, consts := cs, code := #[], gaps := [s!"error: {e}"], calls := [] }
  -- families: one definition per text of the instances that no other merges with
  let mut famDefs : Array (String × String × Array Code × String) := #[]   -- section, name, code, fn
  let mut instTerm : List (String × String) := []
  for fn in (instUnits.toList.map (·.fn)).eraseDups do
    let mut groups : Array (Array Code) := #[]
    for u in instUnits.filter (fun u => u.fn == fn && !u.code.isEmpty) do
      let mut found : Option Nat := none
      for (g, i) in groups.zipIdx do
        if found.isNone then
          if let some (m, extra) := mergeA st.muts g u.code then
            groups := groups.set! i m
            st := { st with muts := extra ++ st.muts }
            found := some i
      let gi ← match found with
        | some i => pure i
        | none => do groups := groups.push u.code; pure (groups.size - 1)
      let dname := if gi == 0 then camel fn else s!"{camel fn}_{gi + 1}"
      let argsT := String.join (u.consts.map fun c => match c with
        | .lit n => s!" {n}"
        | .gpow k => s!" {k}"
        | _ => " 0")
      instTerm := (u.core, s!"({dname}{argsT})") :: instTerm
    for (g, gi) in groups.zipIdx do
      let dname := if gi == 0 then camel fn else s!"{camel fn}_{gi + 1}"
      famDefs := famDefs.push (sectionOf py fn, dname, g, fn)
  -- modules
  IO.FS.createDirAll outDir
  -- every global constant and constant array (a text abandoned and redone may have recorded its
  -- names only in the abandoned state)
  let consts := globals.map (·.1)
  let cfg := modHeader "Config" "The configuration's constants the translated guest names, from the generated source data." ["LeanVM.Guest.Data.Source"] (opens := false) ++
    String.join (consts.map fun c => s!"def {c} : Nat := LeanVM.Guest.Data.const_{c}\n") ++
    String.join (prog.constArrays.map fun (a, _) => s!"def {a} : List (Nat × Nat) := LeanVM.Guest.Data.arr_{a}\n") ++ "\n" ++ modFooter
  IO.FS.writeFile (outDir / "Config.lean") cfg
  -- the `@inline` functions, each after the ones it calls
  let vtexts := st.variants.toList.map fun vr => (vr.name, defText py st.muts vr.fn s!"`@inline {vr.fn}`" vr.name vr.code)
  let vnames := vtexts.map (·.1)
  let mut order : Array String := #[]
  let mut visiting : List String := []
  let mut stack : List (String × Bool) := vnames.reverse.map (·, false)
  while !stack.isEmpty do
    let (n, post) := stack.head!
    stack := stack.tail
    if post then
      if !order.contains n then order := order.push n
      continue
    if order.contains n || visiting.contains n then continue
    visiting := n :: visiting
    let deps := ((words ((vtexts.lookup n).getD "")).filter fun w => w != n && vnames.contains w).eraseDups
    stack := (n, true) :: stack
    stack := (deps.map (·, false)) ++ stack
  let inl := modHeader "Inline" "The guest's `@inline` functions, one Lean function per text of their calls that no other merges with." ["LeanVM.Dsl.Gen.Support", "LeanVM.Dsl.Gen.Config"] ++
    String.join (order.toList.map fun n => (vtexts.lookup n).getD "") ++ modFooter
  IO.FS.writeFile (outDir / "Inline.lean") inl
  let sections := ((units.toList.map fun u => sectionOf py u.fn) ++ (famDefs.toList.map (·.1))).eraseDups
  for sec in sections do
    let body := String.join ((units.toList.filter fun u => sectionOf py u.fn == sec).map fun u =>
        if u.code.isEmpty then u.stub else defText py st.muts u.fn s!"`{u.fn}`" (camel u.fn) u.code) ++
      String.join ((famDefs.toList.filter (·.1 == sec)).map fun (_, nm, g, fn) =>
        defText py st.muts fn s!"`{fn}`, a `Const` family" nm g)
    IO.FS.writeFile (outDir / s!"{sec}.lean") (modHeader sec s!"The guest's section `{sec}`, translated." ["LeanVM.Dsl.Gen.Inline"] ++ body ++ modFooter)
  -- the check
  let gapOf : String → List String := fun core =>
    ((units.toList ++ instUnits.toList).find? (·.core == core)).map (·.gaps) |>.getD ["missing"]
  let callsOf : String → List String := fun core =>
    ((units.toList ++ instUnits.toList).find? (·.core == core)).map (·.calls) |>.getD []
  let mut checks : Array String := #[]
  let mut skipped : Array String := #[]
  let mut nOk := 0
  for u in units do
    let mut closure : List String := []
    let mut todo := u.calls
    while !todo.isEmpty do
      let c := todo.head!
      todo := todo.tail
      if closure.contains c then continue
      closure := closure ++ [c]
      todo := todo ++ callsOf c
    let gaps := (u.core :: closure).flatMap gapOf
    if gaps.isEmpty then
      nOk := nOk + 1
      let terms := camel u.fn :: closure.map fun c => (instTerm.lookup c).getD s!"missingInstance_{c}"
      checks := checks.push s!"#guard sameProg [{", ".intercalate terms}] (expandedAll (src \"{u.fn}\"))"
    else skipped := skipped.push s!"-- {u.fn}: {", ".intercalate gaps.eraseDups}"
  let check := s!"/-\n  LeanVM.Dsl.Gen.Check\n\n  Every translated function against `Expand`: its core functions, its loop helpers and its `Const`\n  instances equal up to the numbering of values and the names of the loop helpers.\n-/\n\n" ++
    String.join (sections.map fun s => s!"import LeanVM.Dsl.Gen.{s}\n") ++ "import LeanVM.Dsl.Check\n\n" ++
    "/-!\n# The translated guest against `Expand`\n\nFor each function `Expand` lowers as written, `sameProg` compares the core functions elaborated\nfrom its translation, with its loop helpers and the `Const` instances it reaches, to those\n`Expand` makes from the exported source: both lists are walked from the function through its\ncallees, loop helpers renamed in that order, and compared by `sameCore` (values numbered by first\noccurrence). Functions with a gap are listed at the end.\n-/\n\n" ++
    "namespace LeanVM.Dsl.Gen.Check\n\nopen LeanVM.Core LeanVM.Dsl LeanVM.Dsl.Gen LeanVM.Dsl.Check\n\n" ++
    "/-- The callees of statements, in order. -/\npartial def callees : List Core.Stmt → List String\n  | [] => []\n  | s :: ss => (match s with\n      | .call f _ _ => [f]\n      | .callIf _ f _ => [f]\n      | .dispatch _ fs _ _ => fs\n      | .ite _ z nz => callees z ++ callees nz\n      | .match_ _ arms => arms.flatMap callees\n      | _ => []) ++ callees ss\n\n" ++
    "/-- Statements with their callees renamed. -/\npartial def renameIn (g : String → String) : List Core.Stmt → List Core.Stmt\n  | [] => []\n  | s :: ss => (match s with\n      | .call f a r => .call (g f) a r\n      | .callIf x f a => .callIf x (g f) a\n      | .dispatch x fs a r => .dispatch x (fs.map g) a r\n      | .ite c z nz => .ite c (renameIn g z) (renameIn g nz)\n      | .match_ x arms => .match_ x (arms.map (renameIn g))\n      | s => s) :: renameIn g ss\n\n" ++
    "/-- The functions of `fs` reached from the first, in order of first call, loop helpers named by\nthat order. -/\npartial def walk (fs : List Core.Fn) : List Core.Fn := Id.run do\n  let some root := fs.head? | return []\n  let mut order : Array String := #[root.name]\n  let mut i := 0\n  while i < order.size do\n    if let some f := fs.find? (·.name == order[i]!) then\n      for c in callees f.body do\n        if !order.contains c && fs.any (·.name == c) then order := order.push c\n    i := i + 1\n  let loops := order.filter (·.startsWith \"__loop\")\n  let g := fun (n : String) => match loops.findIdx? (· == n) with\n    | some k => s!\"__loop{k}\"\n    | none => n\n  return (order.toList.filterMap fun n => fs.find? (·.name == n)).map fun f =>\n    { f with name := g f.name, body := renameIn g f.body }\n\n" ++
    "/-- Every core function the translations elaborate. -/\ndef elabAll (fs : List GFn) : List Core.Fn := fs.flatMap fun f => f.elab.map (·.1.core)\n\n" ++
    "/-- The core functions `Expand` makes of `f` and queues (`Dsl.Check.expanded`, with room for every\ninstance `main` reaches). -/\ndef expandedAll (f : Source.Func) : List Core.Fn :=\n  match Expand.expandQueue LeanVM.Guest.Data.guest 100000 0 #[f] 0 #[] with\n  | .ok a => a.toList.map (·.1.core)\n  | .error _ => []\n\n" ++
    "/-- The translation of a function against `Expand`'s functions for it. -/\ndef sameProg (fs : List GFn) (ex : List Core.Fn) : Bool := sameCore (walk (elabAll fs)) (walk ex)\n\n" ++
    "\n".intercalate checks.toList ++ s!"\n\n/-! ## Not checked: functions with a gap ({skipped.size})\n" ++ "\n".intercalate (skipped.toList.map fun l => String.ofList (l.toList.drop 3)) ++ "\n-/\n\nend LeanVM.Dsl.Gen.Check\n"
  IO.FS.writeFile (outDir / "Check.lean") check
  IO.println s!"translated {units.size} functions, {instUnits.size} instances, {st.variants.size} inline variants; checked {nOk}, gaps in {skipped.size}"
  for l in skipped do IO.println l
  return 0
