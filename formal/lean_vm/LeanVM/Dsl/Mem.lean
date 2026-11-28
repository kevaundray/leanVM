/-
  LeanVM.Dsl.Mem

  Memory in the embedded guest language beyond loads and stores: `addr` pointers to frame runs,
  shifted pointers materialized as `Expand` makes them, heap buffers with a static size whose
  slices are bounds-checked by a proof, runtime-start heap slices, `StackBuf` slices, dynamic
  `HeapBuf`s and constant arrays.
-/

module

public import LeanVM.Dsl.Hints

/-!
# Memory

A pointer is a runtime value; what the zkDSL keeps symbolic, a pointer shifted by a constant
power of `g`, is a Lean pair here, made a value only where one is needed, as `Expand.materialize`
makes it (`B.shifted`): the base itself (a `use`), the `addr` of the run from a cell on (a
`shift`), or a product with the constant from the nearest pointer of the same base already made in
this scope. A heap access folds its constant offset into the instruction up to `foldMax`, else
materializes the pointer (`B.ptrAt`, `Expand.heapBase`).

A `HeapBuf n` carries its size in its type: a slice or an element at a compile-time offset takes a
proof that it lies inside, the whole span of a slice at once, as `Expand.checkHeapBound` checks it
at compile time (main's b18e7d3c). A runtime-start slice `buf[i:i + k]` is the product `buf · i`
with the constant offset folded (`B.sliceRt`), unchecked at compile time as in the zkDSL.
-/

namespace LeanVM.Dsl

open LeanVM.Parameters LeanVM.Core LeanVM.Compiler

@[expose] public section

/-- The largest offset a `DEREF` folds (`Expand.foldMax`). -/
def foldMax : Nat := 2 ^ 16

/-- A heap buffer of `n` words. -/
structure HeapBuf (n : Nat) where
  p : Word
  deriving Inhabited

/-- Frame cells `lo ..< lo + len` of a `StackBuf`, as a hint's destination. -/
def stackSlice (run : List V) (lo len : Nat) (_h : lo + len ≤ run.length := by decide) : Dest :=
  .stack ((run.drop lo).take len)

/-- Element `i` of a constant array, as a field word. -/
def arrWord (a : List (Nat × Nat)) (i : Nat) : E :=
  let c := a.getD i (0, 0)
  word c.1 c.2

/-- Element `i` of a constant array, as an integer (`Expand.eval`'s reading). -/
def arrInt (a : List (Nat × Nat)) (i : Nat) : Nat :=
  let c := a.getD i (0, 0)
  c.1 + c.2 * 2 ^ 64

namespace B

/-- An `addr` atom, which is no instruction: a pending hint stays pending (`Expand.emitFrameAddr`). -/
def frameAddr (p : V) (run : List V) : B Unit := modify fun st =>
  { st with out := st.out.push (.atom (.frameAddr p run)), trace := st.trace.push .emit }

/-- `addr(run)`: a pointer to a frame run (`Expand.stackAddr`). -/
def addr (run : List V) : B Word := do
  let p ← fresh .addr
  frameAddr p run
  modify fun st => { st with addrRuns := (p, run) :: st.addrRuns }
  return ⟨p⟩

/-- The pointer `p · g^k` as a value (`Expand.materialize`). -/
def shifted {τ : Ty} (p : Var τ) (k : Nat) : B Word := do
  if k = 0 then return (← use p).word
  let st ← get
  if let some (_, cells) := st.addrRuns.find? (·.1 == p.v) then
    if st.faithful then event (.shift p.v k)
    let o ← fresh .pooled
    frameAddr o (cells.drop k)
    return ⟨o⟩
  let mats := ((st.mats.find? (·.1 == p.v)).map (·.2)).getD []
  if let some m := mats.find? (·.exp == k) then
    let c ← const (gpowE m.dist)
    return ← mul (⟨m.src⟩ : Word) c
  let best : Option Mat := if st.consts.contains (gpowE k) then none else
    mats.foldl (fun b m =>
      if m.exp < k && st.consts.contains (gpowE (k - m.exp)) && b.all (·.exp < m.exp) then some m
      else b) none
  let (src, dist) := match best with
    | some m => (m.out, k - m.exp)
    | none => (p.v, k)
  let c ← const (gpowE dist)
  let o ← mul (⟨src⟩ : Word) c
  modify fun st => { st with
    mats := (p.v, mats ++ [⟨k, o.v, src, dist⟩]) :: st.mats.filter (·.1 != p.v) }
  return o

/-- A pointer and a folded offset addressing `p · g^off` (`Expand.heapBase`): the offset itself up
to `foldMax`, else the pointer times `g^off` at offset `0`. -/
def ptrAt {τ : Ty} (p : Var τ) (off : Nat) : B (Word × Nat) :=
  if off ≤ foldMax then pure (p.word, off)
  else const (gpowE off) >>= fun c => mul p c >>= fun q => pure (q, 0)

/-- A heap buffer of `n` words (`HeapBuf(n)`). -/
def heap (n : Nat) : B (HeapBuf n) := do
  return ⟨← heapBuf n⟩

/-- `HeapBuf(e)` with the size in the exponent of the runtime value `size`. -/
def heapBufDyn {τ : Ty} (size : Var τ) : B Word := do
  let p ← fresh
  hint (.allocDyn p size.v)
  return ⟨p⟩

/-- A runtime-start heap slice `buf[i:i + len]`: the pointer `p · i`, `off` the constant exponent
folded with it. -/
def sliceRt {σ τ : Ty} (p : Var σ) (i : Var τ) (off len : Nat) : B Dest := do
  let q ← mul p i
  return .heap q.v off len

end B

namespace HeapBuf

variable {n : Nat}

/-- Words `lo ..< lo + len` of the buffer, the whole span inside it, as a hint's destination. -/
def slice (b : HeapBuf n) (lo len : Nat) (_h : lo + len ≤ n := by decide) : B Dest := do
  let (q, o) ← B.ptrAt b.p lo
  return .heap q.v o len

/-- Word `k` of the buffer. -/
def get (b : HeapBuf n) (k : Nat) (_h : k < n := by decide) : B Word := do
  let (q, o) ← B.ptrAt b.p k
  B.load q o

/-- Store `v` at word `k` of the buffer. -/
def put {τ : Ty} (b : HeapBuf n) (k : Nat) (v : Var τ) (_h : k < n := by decide) : B Unit := do
  let (q, o) ← B.ptrAt b.p k
  B.store q o v

end HeapBuf

end
end LeanVM.Dsl
