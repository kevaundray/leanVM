/-
  LeanVM.Core.Text

  The canonical text of a core program, each function renumbered, and its digest.
-/

module

public import LeanVM.Core.Renumber
public import LeanVM.Core.Word
public import Statement.Keccak

/-!
# The canonical text of the core IR

`coreText` writes a program's functions one after another, each renumbered (`Fn.renumber`:
parameters first, then values in order of first occurrence), so two programs equal up to the
numbering of their values have the same text. `coreDigest` is the Keccak-256 of the digests of its
functions' texts, in order: the guest's input digest names the program by it
(`crates/aggregation/src/guest.rs`, `input_digest`; `guests/lean_ethereum.digest`).
-/

namespace LeanVM.Core.Text

open LeanVM.Parameters LeanVM.Core LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- A value of a renumbered function; any other is printed whole. -/
def ctV (v : V) : String :=
  if v.path.isEmpty && v.tag == 0 then s!"%{v.idx}" else s!"?{reprStr v}"

def ctVs (vs : List V) : String := "[" ++ " ".intercalate (vs.map ctV) ++ "]"

def ctDest : Dest → String
  | .stack cs => ctVs cs
  | .heap p off len => s!"heap({ctV p} {off} {len})"

def ctHint : Hint → String
  | .witness s d => s!"witness {s} {ctDest d}"
  | .bits v st n d => s!"bits {ctV v} {ctDest d} {st} {n}"
  | .bitsExp v n d => s!"bits_exp {ctV v} {ctDest d} {n}"
  | .digitsExp v nb nd db st sc d =>
      s!"digits_exp {ctV v} {(sc.map ctV).getD "-"} {ctDest d} {nb} {nd} {db} {st}"
  | .windowsExp v st w n d => s!"windows_exp {ctV v} {ctDest d} {st} {w} {n}"
  | .limbs v d => s!"limbs {ctV v} {ctVs d}"
  | .log2Ceil b n f d => s!"log2_ceil {ctDest b} {ctV d} {n} {f}"
  | .inverse x d => s!"inverse {ctV x} {ctV d}"
  | .alloc d n => s!"alloc {ctV d} {n}"
  | .allocDyn d s => s!"alloc_dyn {ctV d} {ctV s}"

def ctAtom : Atom → String
  | .const d c => let (c0, c1) := limbsOf c; s!"const {ctV d} {c0} {c1}"
  | .add d a b => s!"add {ctV d} {ctV a} {ctV b}"
  | .mul d a b => s!"mul {ctV d} {ctV a} {ctV b}"
  | .copy d s => s!"copy {ctV d} {ctV s}"
  | .load d p off => s!"load {ctV d} {ctV p} {off}"
  | .assertEq a b => s!"assert_eq {ctV a} {ctV b}"
  | .assertNe x inv p => s!"assert_ne {ctV x} {ctV inv} {ctV p}"
  | .rangeCheck x y t1 t2 k => s!"range_check {ctV x} {ctV y} {ctV t1} {ctV t2} {ctV k}"
  | .assertInK a b => s!"assert_in_k {ctV a} {ctV b}"
  | .keccak ins outs i o =>
      s!"keccak {ctVs ins} {ctVs outs} {if i then 1 else 0} {if o then 1 else 0}"
  | .frameAddr p run => s!"addr {ctV p} {ctVs run}"
  | .touch t p => s!"touch {ctV t} {ctV p}"
  | .hint h => s!"hint {ctHint h}"

mutual
def ctStmt (ind : String) : Stmt → List String
  | .atom a => [ind ++ ctAtom a]
  | .ite c z n => [s!"{ind}if_zero {ctV c}"] ++ ctStmts (ind ++ "  ") z ++ [s!"{ind}else"] ++
      ctStmts (ind ++ "  ") n ++ [s!"{ind}end"]
  | .match_ x arms => [s!"{ind}match {ctV x}"] ++ ctArms ind arms ++ [s!"{ind}end"]
  | .call f args rets => [s!"{ind}call {f} {ctVs args} {ctVs rets}"]
  | .callIf c f args => [s!"{ind}call_if {ctV c} {f} {ctVs args}"]
  | .dispatch x fs args rets =>
      [s!"{ind}dispatch {ctV x} [{" ".intercalate fs}] {ctVs args} {ctVs rets}"]
  | .ret vs => [s!"{ind}ret {ctVs vs}"]

def ctStmts (ind : String) : List Stmt → List String
  | [] => []
  | s :: ss => ctStmt ind s ++ ctStmts ind ss

def ctArms (ind : String) : List (List Stmt) → List String
  | [] => []
  | a :: as => [s!"{ind}arm"] ++ ctStmts (ind ++ "  ") a ++ ctArms ind as
end

/-- A function in the canonical text, renumbered. -/
def fnText (f : Fn) : String :=
  let f := f.renumber
  String.join ((s!"def {f.name} {ctVs f.params}" :: ctStmts "  " f.body).map (· ++ "\n"))

/-- A program in the canonical text: each function renumbered, one after another. -/
def coreText (P : Program) : String := String.join (P.map fnText)

/-- The digest of a program: Keccak-256 of its functions' digests, each the Keccak-256 of its
canonical text, in order. -/
def coreDigest (P : Program) : Digest :=
  keccak256 (P.flatMap fun f => KeccakHash.digestBytes (keccak256 (fnText f).toUTF8.toList))

/-- Bytes as lowercase hexadecimal, two digits each. -/
def hex (bytes : List UInt8) : String :=
  let digit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
  String.ofList (bytes.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)])

end
end LeanVM.Core.Text
