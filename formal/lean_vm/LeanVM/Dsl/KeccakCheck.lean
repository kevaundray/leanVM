/-
  LeanVM.Dsl.KeccakCheck

  The migration check of the Keccak builtins: each port of `LeanVM.Dsl.KeccakGuest`, elaborated,
  against what `Expand` makes of the zkDSL source it replaces, run on the exported guest.
-/

import LeanVM.Dsl.KeccakGuest
import LeanVM.Dsl.Check

/-!
# The Keccak ports against `Expand`

As in `LeanVM.Dsl.Check`: the core functions are equal once their values are numbered by first
occurrence (`Check.sameCore`). A real function is expanded from its exported source, a `Const`
instance from its specialization (`Expand.specializeFn`), and an `@inline` function or a single
builtin from a small source function calling it, written here as the zkDSL text in the port's
docstring parses. Every builtin's form the guest uses is reached: `keccak` with list, frame and
heap operands, a tail, `len=`, `pad_tail=1`, frame and heap destinations; the duplex step `cap=`
over a 13-cell output and a 5-cell capacity, at every count of waiting scalars; `keccak_cells`
over a frame run (four and sixteen blocks), a heap slice with a heap `state=` (one to five blocks,
`len=0`), and a list comprehension of `@inline` words.
-/

namespace LeanVM.Dsl.KeccakCheck

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl LeanVM.Dsl.Check LeanVM.Dsl.KeccakGuest
open LeanVM.Core.Source (Expr Func Param Shape)

/-- The exported guest. -/
abbrev guest : Source.Program := LeanVM.Guest.Data.guest

/-- What `Expand` makes of a source function `f` added to the guest. -/
def expandedWith (f : Func) : List Core.Fn :=
  expanded { guest with funcs := guest.funcs ++ [f] } f

/-- A statement at line `0`. -/
def st (k : Source.StmtKind) : Source.Stmt := .mk 0 k

/-- A runtime scalar parameter. -/
def scalar (n : String) : Param := ⟨n, .runtime .scalar⟩

/-- A runtime `StackBuf(k)` parameter. -/
def buf (n : String) (k : Nat) : Param := ⟨n, .runtime (.stackBuf k)⟩

/-- A keyword argument, as the parser writes `key=value`. -/
def kw (key : String) (v : Expr) : Expr := .call s!"__kw_{key}" [v]

/-! ## Real functions -/

#guard sameCore (elaborated [statementDigest]) (expanded guest (src "statement_digest"))

#guard sameCore (elaborated [daVerifyCell]) (expanded guest (src "da_verify_cell"))

/-- `claim_list_last` specialized at `k`, as the compiler queues it. -/
def claimListLastSrc (k : Nat) : Func :=
  (Expand.specializeFn (src "claim_list_last") [.lit k]).toOption.getD default

#guard (List.range CLAIM_GROUP).all fun k =>
  sameCore (elaborated [claimListLast k]) (expanded guest (claimListLastSrc k))

/-! ## `@inline` functions and single builtins, called from a function of their own -/

/-- `def fs_perm_at(sp: StackBuf(spCells), rate: StackBuf(8)): fs_perm(sp, rate, k)`. -/
def fsPermSrc (spCells k : Nat) : Func :=
  { name := s!"fs_perm_at_{spCells}_{k}", params := [buf "sp" spCells, buf "rate" 8],
    returnShapes := [], inline := false,
    body := [st (.call "fs_perm" [.var "sp", .var "rate", .lit k]), st (.ret [])] }

#guard (List.range 5).all fun k =>
  sameCore (elaborated [fsPermAt KECCAK_STATE k]) (expandedWith (fsPermSrc KECCAK_STATE k))

#guard sameCore (elaborated [fsPermAt 5 4]) (expandedWith (fsPermSrc 5 4))

/-- `def walk_window_at(n0, n1, path: StackBuf(4 * width)): return walk_window(n0, n1, path, 0,
width, k)`. -/
def walkWindowSrc (width k : Nat) : Func :=
  { name := s!"walk_window_at_{width}_{k}",
    params := [scalar "n0", scalar "n1", buf "path" (4 * width)],
    returnShapes := [.scalar, .scalar], inline := false,
    body := [st (.letTuple ["a", "b"] "walk_window"
        [.var "n0", .var "n1", .var "path", .lit 0, .lit width, .lit k]),
      st (.ret [.var "a", .var "b"])] }

#guard [(6, 37), (3, 0), (2, 3)].all fun (w, k) =>
  sameCore (elaborated [walkWindowAt w k]) (expandedWith (walkWindowSrc w k))

/-- `sp_word_leaf`, its source as in `spWordLeaf`'s docstring. -/
def spWordLeafSrc : Func :=
  { name := "sp_word_leaf",
    params := [scalar "pp", scalar "a0", scalar "a1", buf "walks" (SP_V * CHAIN_STEPS)],
    returnShapes := [.scalar], inline := false,
    body := [st (.let_ "leaf" (.stackBuf 1)),
      st (.call "keccak_cells"
        [.listComp (.call "sp_word" [.var "pp", .var "a0", .var "a1", .var "walks",
            .lit (CHAIN_STEPS - 1), .lit CHAIN_STEPS, .var "j"]) "j" (.lit 0) (.lit (SP_V + 3)),
          .var "leaf"]),
      st (.ret [.index (.var "leaf") (.lit 0)])] }

#guard sameCore (elaborated [spWordLeaf]) (expandedWith spWordLeafSrc)

/-- `pad_tail_at`, its source as in `padTailAt`'s docstring. -/
def padTailSrc : Func :=
  { name := "pad_tail_at", params := [scalar "pp", scalar "a0", scalar "node_at"],
    returnShapes := [.scalar], inline := false,
    body := [st (.let_ "kids" (.stackBuf 5)),
      st (.hintWitness (.slice (.var "kids") (.lit 0) (.lit 2)) "siblings"),
      st (.let_ "parent" (.stackBuf 1)),
      st (.call "keccak"
        [.list [.var "pp", .var "a0"], .list [.var "node_at", .index (.var "kids") (.lit 0)],
          .var "parent", kw "tail" (.slice (.var "kids") (.lit 1) (.lit 5)), kw "len" (.lit 80),
          kw "pad_tail" (.lit 1)]),
      st (.ret [.index (.var "parent") (.lit 0)])] }

#guard sameCore (elaborated [padTailAt]) (expandedWith padTailSrc)

/-- `heap_pair`, its source as in `heapPair`'s docstring. -/
def heapPairSrc : Func :=
  { name := "heap_pair", params := [scalar "a", scalar "b"], returnShapes := [], inline := false,
    body := [st (.call "keccak"
        [.slice (.var "a") (.lit 0) (.lit 2), .slice (.var "a") (.lit 2) (.lit 4),
          .slice (.var "b") (.lit 0) (.lit 2)]),
      st (.ret [])] }

#guard sameCore (elaborated [heapPair]) (expandedWith heapPairSrc)

end LeanVM.Dsl.KeccakCheck
