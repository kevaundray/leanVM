import LeanVMTests.Programs.Support
import LeanVM.Guest.Program

/-!
# The aggregation tests' snippets

Each a `main` over the guest's functions, compiled with what it reaches of the guest's program
list at the guest's placeholders (`lake exe guest-backend export snippets`), proved by
`crates/aggregation/src/tests.rs` (`guest_snippet`) on the streams and public input it gives.
-/

namespace LeanVMTests.Programs.Snippets

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl LeanVMTests.Programs LeanVM.Guest.Program

/-- A snippet: `body` as `main`, over the guest's functions. -/
def snippet (name : String) (body : B Unit) : TestProgram where
  name := name
  program := ("main", [mainOf body]) :: LeanVM.Guest.Program.program.filter (·.1 != "main")
  entry := some "main"

/-- Assert that the public words are `a` and `b`. -/
def assertPublic {σ τ : Ty} (a : Var σ) (b : Var τ) : B Unit := do
  let p ← publicPtr
  B.assertEq (← B.load p 0) a
  B.assertEq (← B.load p 1) b

/-- A hinted cell, as a word. -/
def hinted (stream : String) : B Word := do return ⟨(← B.witnessCell stream).v⟩

/-- `child_claim_list_digest` over a hinted table of eight claims and a hinted count. -/
def childWalk : TestProgram := snippet "child_walk" do
  let n ← hinted "n"
  let table ← B.heap 8
  B.witness "claims" (← table.slice 0 8)
  let cover ← B.heap 2
  let d ← B.call "child_claim_list_digest"
    [table.p.v, cover.p.v, (← k (gp 3)).v, (← k (gp 2)).v, n.v] 2
  assertPublic d[0]! d[1]!

/-- `column_selector` at a hinted column log, over the selector tables of a hinted point, its
nibbles past the stack zero. -/
def columnSelectors : TestProgram := snippet "column_selectors" do
  let point ← B.heap (4 * SEL_NIBBLES)
  B.witness "point" (.heap point.p.v 0 MAX_STACK_LOG)
  for j in List.range' MAX_STACK_LOG (4 * SEL_NIBBLES - MAX_STACK_LOG) do
    B.store point.p j (← k 0)
  let point1 ← B.heap (4 * SEL_NIBBLES)
  for j in List.range (4 * SEL_NIBBLES) do
    B.store point1.p j (← B.add (← k (lit 1)) (← B.load point.p j))
  let selEq ← B.call "selector_tables" [point.p.v, point1.p.v] 1
  let gSquares ← B.call "exponent_tables" [] 1
  let offset ← hinted "offset"
  let kappa ← hinted "kappa"
  let selG ← B.shifted gSquares[0]! SIZE_BITS
  let w ← B.dispatch kappa ((List.range N_COLUMN_LOGS).map fun j => instName "column_selector" [.L j])
    [offset.v, selEq[0]!.v, selG.v] 1
  let p ← publicPtr
  B.assertEq (← B.load p 0) w[0]!

/-- `da_verify` over the byte table, its roots and challenge hashed. -/
def daMembership : TestProgram := snippet "da_membership" do
  let byteBits ← B.heap SP_BYTE_VALUES
  for v in List.range SP_BYTE_VALUES do
    B.store byteBits.p v (← k (lit v))
  let r ← B.call "da_verify" [byteBits.p.v] 3
  let digest ← B.stackBuf 2
  B.keccak (.words [.cell r[0]!.v, .cell r[1]!.v]) (.words [.cell r[2]!.v, .zero]) (.frame digest)
  assertPublic (cell digest 0) (cell digest 1)

/-- `grind_check` of a hinted word at 3 bits. -/
def grindCheck : TestProgram := snippet "grind_check" do
  let w ← hinted "w"
  let t ← B.call "exponent_tables" [] 1
  let tab ← B.shifted t[0]! WIN_TAB_AT
  discard <| B.call (instName "grind_check" [.L 3]) [w.v, tab.v] 0

/-- `list_split` of a hinted count. -/
def listSplit : TestProgram := snippet "list_split" do
  let n ← hinted "n"
  let r ← B.call "list_split" [n.v] 3
  assertPublic r[1]! r[2]!

/-- The snippets. -/
def all : List TestProgram := [childWalk, columnSelectors, daMembership, grindCheck, listSplit]

end LeanVMTests.Programs.Snippets
