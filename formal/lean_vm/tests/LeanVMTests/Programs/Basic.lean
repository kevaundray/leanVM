import LeanVMTests.Programs.Support

/-!
# The compiler's test programs

Eighteen small programs over the builder's constructs, each proved and verified by the Rust
prover on the public input it publishes (`crates/zkdsl/tests/suite/programs.rs`) and run by the
interpreter on it (`LeanVMTests.Programs.Run`). `+` on words is `XOR`, and `g = 2`, so `3·g = 6`.
-/

namespace LeanVMTests.Programs.Basic

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl LeanVMTests.Programs

/-- Runtime branches on field equality, the `else if` a branch nested in the other one, and a
branch in a loop body (a helper's frame). Published: `(5, 13 + 17) = (5, 28)`. -/
def conditionals : TestProgram where
  name := "conditionals"
  publicInput := [lit 5, lit 28]
  program := [("main", [mainOf do
    let r ← B.heap 4
    let x ← k (gp 3)
    ifEq x (← k (gp 3)) (do r.put 0 (← k (lit 5))) (do r.put 0 (← k (lit 7)))
    ifEq x (← k (gp 1)) (do r.put 1 (← k (lit 11)))
      (ifEq x (← k (gp 3)) (do r.put 1 (← k (lit 13))) (do r.put 1 (← k (lit 15))))
    B.loopConstF 0 4 1 (pure [r.p.v]) fun i caps => do
      ifEq i (← k (gp 2)) (do B.store (cap caps 0) 2 (← k (lit 17))) (pure ())
    let a ← r.get 0
    let b ← B.add (← r.get 1) (← r.get 2)
    publish a b])]

/-- `hash_pair(buf, k)`, a family over the compile-time `k`: the digest of the heap pair at
`2k`, hashed with itself. -/
def hashPair (j : Nat) : GFn where
  name := instName "hash_pair" [.L j]
  arity := 1
  rets := 2
  body := fun ps => do
    let h ← B.stackBuf 2
    B.keccak (.heap ps[0]! (2 * j) 2) (.heap ps[0]! (2 * j) 2) (.frame h)
    return [.v h[0]!, .v h[1]!]

/-- A family called directly and from a fused `match` (a `dispatch`), its instance at `0` shared.
Published: `H(quad0, quad0) + H(quad1, quad1)`, cell by cell. -/
def constParams : TestProgram where
  name := "const_params"
  publicInput := [lit 157908933584918725715541133239856802159,
    lit 40624458567139149906120084677986376415]
  program := [("main", [mainOf do
    let buf ← B.heap 4
    buf.put 0 (← k (lit 5))
    buf.put 1 (← k (lit 7))
    buf.put 2 (← k (lit 11))
    buf.put 3 (← k (lit 13))
    let a ← B.call (hashPair 0).name [buf.p.v] 2
    let x ← k (gp 1)
    let b ← B.dispatch x [(hashPair 0).name, (hashPair 1).name] [buf.p.v] 2
    publish (← B.add a[0]! b[0]!) (← B.add a[1]! b[1]!)]),
    ("hash_pair", [hashPair 0, hashPair 1])]

/-- Fibonacci in the exponent: `fib[g^k]` holds `g^F_k`, one `MUL` per step, the state carried
through the heap. Published: `(g^89, g^89)`. -/
def fibonacci : TestProgram where
  name := "fibonacci"
  publicInput := [gp 89, gp 89]
  program := [("main", [mainOf do
    let fib ← B.heap 12
    fib.put 0 (← k (gp 0))
    fib.put 1 (← k (gp 1))
    B.loopConstF 0 10 1 (pure [fib.p.v]) fun i caps => do
      let q ← B.mul (cap caps 0) i
      B.store q 2 (← B.mul (← B.load q 0) (← B.load q 1))
    let out ← fib.get 11
    B.assertEq out (← k (gp 89))
    discard <| B.rangeCheck out 128
    publish out out])]

/-- The Fibonacci benchmark (`bench/`, `cargo leanvm-bench fibonacci --n N`): `N = 1000·B` steps in
the exponent, the block count read at run time from the second public word `g^B`, so one program
serves every `N`: block `j` reads its boundary pair at `g^{2j}`, `g^{2j+1}` of the heap, runs 1000
`MUL`s in frame cells and writes the next pair. Published: `(g^F(N), g^B)`; at `N = 2000`,
`F(2000) mod 2^64 - 1 = 4133460837788448765`. -/
def fibonacciBench : TestProgram where
  name := "fibonacci_bench"
  publicInput := [lit 8035997182686239527, gp 2]
  program := [("main", [mainOf do
    let pubP ← publicPtr
    let stop ← B.load pubP 1
    discard <| B.rangeCheck stop 16385
    let size ← B.mul (← B.mul stop stop) (← k (gp 2))
    let buff ← B.heapBufDyn size
    B.store buff 0 (← k (lit 1))
    B.store buff 1 (← k (gp 1))
    B.loopRtF 0 (pure stop) 1 (pure [buff.v]) fun x caps => do
      let q ← B.mul (cap caps 0) (← B.mul x x)
      let f ← B.stackBuf 1002
      B.loadInto (cell f 0) q 0
      B.loadInto (cell f 1) q 1
      for j in List.range' 2 1000 do
        B.mulInto (cell f j) (cell f (j - 2)) (cell f (j - 1))
      B.store q 2 (cell f 1000)
      B.store q 3 (cell f 1001)
    let q ← B.mul buff (← B.mul stop stop)
    B.store pubP 0 (← B.load q 0)])]

/-- A Keccak chain over heap pairs addressed by the loop counter: value `k` at `g^{2k}`, `g^{2k+1}`,
value `k + 1 = H(value k, value k)`. Published: `H^3(5, 7)`. -/
def hashHeapChain : TestProgram where
  name := "hash_heap_chain"
  publicInput := [lit 27240554859721455327970068208906002034,
    lit 119514610692047185288834508057685931752]
  program := [("main", [mainOf do
    let buf ← B.heap 8
    buf.put 0 (← k (lit 5))
    buf.put 1 (← k (lit 7))
    B.loopConstF 0 3 1 (pure [buf.p.v]) fun i caps => do
      let q ← B.mul (cap caps 0) (← B.mul i i)
      B.keccak (.heap q.v 0 2) (.heap q.v 0 2) (.heap q.v 2 2)
    publish (← buf.get 6) (← buf.get 7)])]

/-- Keccak over frame and heap slices, as inputs and as the output. Published:
`H(H(a[0:2], hb[0:2]), a[0:2])`, read back from the heap. -/
def hashSlices : TestProgram where
  name := "hash_slices"
  publicInput := [lit 21505378141451040915105957038093575295,
    lit 314243486001112001756598571412583305209]
  program := [("main", [mainOf do
    let a ← B.stackBuf 4
    B.constInto (cell a 0) (lit 5)
    B.constInto (cell a 1) (lit 7)
    B.constInto (cell a 2) 0
    B.constInto (cell a 3) 0
    let hb ← B.heap 4
    hb.put 0 (← k (lit 11))
    hb.put 1 (← k (lit 13))
    let h ← B.stackBuf 2
    B.keccak (.frame (a.take 2)) (.heap hb.p.v 0 2) (.frame h)
    B.keccak (.frame h) (.frame (a.take 2)) (.heap hb.p.v 2 2)
    publish (← hb.get 2) (← hb.get 3)])]

/-- A heap buffer sized at run time, the size in the exponent: a hinted `m = g^2` gives `m·m = g^4`
cells, filled from a stream and summed. Published: `(1 + 2 + 4 + 8, g^3) = (15, g^3)`. -/
def heapbufDyn : TestProgram where
  name := "heapbuf_dyn"
  publicInput := [lit 15, gp 3]
  streams := [("m", [[gp 2]]), ("vals", [[lit 1, lit 2, lit 4, lit 8]])]
  program := [("main", [mainOf do
    let mb ← B.stackBuf 1
    B.witness "m" (.stack mb)
    let m := cell mb 0
    let buf ← B.heapBufDyn (← B.mul m m)
    B.witness "vals" (.heap buf.v 0 4)
    let s ← B.add (← B.add (← B.add (← B.load buf 0) (← B.load buf 1)) (← B.load buf 2))
      (← B.load buf 3)
    publish s (← k (gp 3))])]

/-- Witness streams into frame cells and heap slices, each value pinned by the program (a range
check, equalities, an `XOR`), one stream read twice. Published: `(g^5, 6)`. -/
def hint : TestProgram where
  name := "hint"
  publicInput := [gp 5, lit 6]
  streams := [("r", [[gp 5, lit 12], [lit 9]]), ("h", [[lit 3, lit 5, lit 6]])]
  program := [("main", [mainOf do
    let sb ← B.stackBuf 2
    B.witness "r" (.stack sb)
    discard <| B.rangeCheck (cell sb 0) 8
    B.assertEq (cell sb 1) (← k (lit 12))
    let hb ← B.heap 4
    B.witness "h" (← hb.slice 0 3)
    B.assertEq (← B.add (← hb.get 0) (← hb.get 1)) (← hb.get 2)
    B.witness "r" (← hb.slice 3 1)
    B.assertEq (← hb.get 3) (← k (lit 9))
    publish (cell sb 0) (← hb.get 2)])]

/-- Field identities checked in the program, nothing published (the public input is two zeros). -/
def identities : TestProgram where
  name := "identities"
  program := [("main", [mainOf do
    let x ← k (gp 2)
    B.assertEq x (← k (gp 2))
    discard <| B.rangeCheck x 3
    let y ← B.add x x
    B.assertEq y (← k 0)])]

/-- What `@inline` was: Lean functions emitting into their caller's frame, one picking an operand
at a compile-time argument, called from a store and from the arms of a `match`. With `x = g^2` the
advanced pointer is `g^3` and arm 2 picks 10. Published: `(g^3, 10)`. -/
def inline : TestProgram where
  name := "inline"
  publicInput := [gp 3, lit 10]
  streams := [("x", [[gp 2]])]
  program :=
    let advance (cur : Word) (j : Nat) : B Word := do B.mul cur (← k (gp 1 * lit j))
    let pick (a : Word) (b : E) (j : Nat) (d : Word) : B Unit :=
      if j = 2 then B.constInto d b else B.copy d a
    [("main", [mainOf do
      let x : Word := ⟨(← B.witnessCell "x").v⟩
      discard <| B.rangeCheck x 3
      let y ← advance x 1
      let s ← B.stackBuf 1
      pick y (lit 5) 0 (cell s 0)
      let r ← B.match_ x [none] ((List.range 3).map fun j cells => pick (cell s 0) (lit 10) j (cell cells 0))
      publish (cell s 0) (cell r 0)])]

/-- A loop body's own values and the enclosing ones it reads: `acc` made in the body, `w` and the
`7` from outside, a frame-free store at a compile-time index. Published: `(g^4 + 7, g^5 + 7 + 9)
= (23, 46)`. -/
def loopScopes : TestProgram where
  name := "loop_scopes"
  publicInput := [lit 23, lit 46]
  program := [("main", [mainOf do
    let out ← B.heap 8
    B.loopConstF 0 2 1 (pure [out.p.v]) fun i caps => do
      let acc ← B.mul i (← k (gp 1))
      let q ← B.mul (cap caps 0) i
      B.store q 4 (← k 0)
      B.store q 0 (← B.add (← B.mul acc (← k (gp 3))) (← k (lit 7)))
    out.put 6 (← k (lit 9))
    publish (← out.get 0) (← B.add (← out.get 1) (← out.get 6))])]

/-- `match` on `log x`, in `main` and in a loop body (a helper of its own), each arm writing its
constant into the target cell. Published: `(21, 5 + 7 + 9) = (21, 11)`. -/
def «match» : TestProgram where
  name := "match"
  publicInput := [lit 21, lit 11]
  program :=
    let consts (cs : List Nat) : List (List V → B Unit) :=
      cs.map fun c cells => B.constInto (cell cells 0) (lit c)
    [("main", [mainOf do
      let r ← B.heap 4
      let x ← k (gp 2)
      let v ← B.match_ x [none] (consts [11, 17, 21, 27, 31, 37])
      r.put 0 (cell v 0)
      B.loopConstF 0 3 1 (pure [r.p.v]) fun i caps => do
        let w ← B.match_ i [none] (consts [5, 7, 9])
        B.store (← B.mul (cap caps 0) i) 1 (cell w 0)
      publish (← r.get 0) (← B.add (← B.add (← r.get 1) (← r.get 2)) (← r.get 3))])]

/-- `shift(v) = v·g`. -/
def shift : GFn where
  name := "shift"
  arity := 1
  rets := 1
  body := fun ps => do return [.mul ps[0]! (← k (gp 1)).v]

/-- `two(v) = (v, v·g)`. -/
def two : GFn where
  name := "two"
  arity := 1
  rets := 2
  body := fun ps => do return [.v ps[0]!, .mul ps[0]! (← k (gp 1)).v]

/-- `match` arms that call functions, each writing its returned values into the targets. With
`x = g^3`: `shift(3) = 6`, `two(3) = (3, 6)`. Published: `(6, 3 + 6) = (6, 5)`. -/
def matchArms : TestProgram where
  name := "match_arms"
  publicInput := [lit 6, lit 5]
  program := [("main", [mainOf do
    let x ← k (gp 3)
    let r ← B.match_ x [none] ((List.range 6).map fun i cells => do
      B.callInto "shift" [(← k (lit i)).v] [cells[0]!])
    B.assertEq (cell r 0) (← k (lit 6))
    let ab ← B.match_ x [none, none] ((List.range 6).map fun i cells => do
      B.callInto "two" [(← k (lit (if i < 2 then 1 else i))).v] [cells[0]!, cells[1]!])
    publish (cell r 0) (← B.add (cell ab 0) (cell ab 1))]),
    ("shift", [shift]), ("two", [two])]

/-- `geom(x) = x + geom(x·g)`, `x` at `g^4`: recursion five frames deep, its base case a `return`
inside a branch. -/
def geom : GFn where
  name := "geom"
  arity := 1
  rets := 1
  body := fun ps => do
    let x : Word := ⟨ps[0]!⟩
    let c ← B.add x (← k (gp 4))
    B.ite0 c (B.ret [.v x.v])
    let y ← B.call "geom" [(← B.mul x (← k (gp 1))).v] 1
    return [.add x.v y[0]!.v]

/-- A loop body that range-checks its counter, matches on it (one arm calling the recursive
`geom`) and branches in the same frame, the branch taken: the published values ride its
fall-through path. `geom(1) = 31`. Published: `(31 + 5, 9) = (26, 9)`. -/
def nested : TestProgram where
  name := "nested"
  publicInput := [lit 26, lit 9]
  program := [("main", [mainOf do
    let acc ← B.heap 6
    B.loopConstF 0 3 1 (pure [acc.p.v]) fun i caps => do
      discard <| B.rangeCheck i 3
      let v ← B.match_ i [none] [
        fun cells => do B.callInto "geom" [(← k (lit 1)).v] [cells[0]!],
        fun cells => B.constInto (cell cells 0) (lit 5),
        fun cells => B.constInto (cell cells 0) (lit 9)]
      ifEq i (← B.mul i (← k (gp 0)))
        (do B.store (← B.mul (cap caps 0) i) 0 (cell v 0))
        (do B.store (← B.mul (cap caps 0) i) 0 (← k 0))
    publish (← B.add (← acc.get 0) (← acc.get 1)) (← acc.get 2)]),
    ("geom", [geom])]

/-- Loops to a runtime bound: a hinted `n = g^5`, range-checked, squares five times
(`buf[g^k] = g^{2^k}`); a second loop's bound equals its start, so its impossible assertion never
runs. Published: `(g^32, g^5)`. -/
def runtimeLoop : TestProgram where
  name := "runtime_loop"
  publicInput := [gp 32, gp 5]
  streams := [("n", [[gp 5]]), ("m", [[lit 1]])]
  program := [("main", [mainOf do
    let nb ← B.stackBuf 1
    B.witness "n" (.stack nb)
    let n := cell nb 0
    discard <| B.rangeCheck n 16
    let buf ← B.heap 40
    buf.put 0 (← k (gp 1))
    B.loopRtF 0 (pure n) 1 (pure [buf.p.v]) fun i caps => do
      let q ← B.mul (cap caps 0) i
      let a ← B.load q 0
      B.store q 1 (← B.mul a a)
    let mb ← B.stackBuf 1
    B.witness "m" (.stack mb)
    let m := cell mb 0
    discard <| B.rangeCheck m 16
    B.loopRtF 0 (pure m) 0 (pure []) fun _ _ => do
      B.assertEq (← k (lit 1)) (← k 0)
    publish (← B.load (← B.mul buf.p n) 0) n])]

/-- Branch-local checks: a range check's bound constant made in a branch not taken is made again
after the join. Published: `(9, 6)`. -/
def scoping : TestProgram where
  name := "scoping"
  publicInput := [lit 9, lit 6]
  program := [("main", [mainOf do
    let x ← k (gp 3)
    discard <| B.rangeCheck x 8
    ifEq x (← k (gp 3)) (do
      B.assertEq (← k (lit 7)) (← k (lit 7))
      discard <| B.rangeCheck x 8) (pure ())
    B.assertEq (← k (lit 5)) (← k (lit 5))
    ifEq x (← k (gp 3)) (pure ()) (do discard <| B.rangeCheck x 16)
    let sb ← B.stackBuf 4
    B.constInto (cell sb 2) (lit 9)
    discard <| B.rangeCheck x 16
    let y ← k (lit 6)
    B.assertEq y (← k (lit 6))
    publish (cell sb 2) y])]

/-- `chain(buf, n)`: `n` Keccak steps over heap pairs, unrolled. -/
def chain (n : Nat) : GFn where
  name := instName "chain" [.L n]
  arity := 1
  rets := 0
  body := fun ps => do
    for i in List.range n do
      B.keccak (.heap ps[0]! (2 * i) 2) (.heap ps[0]! (2 * i) 2) (.heap ps[0]! (2 * i + 2) 2)
    return []

/-- Lean loops at compile time: frame cells `sb[k] = g^k`, and `chain(buf, 3)`, the chain of
`hash_heap_chain` unrolled. Published: `H^3(5, 7)`. -/
def unroll : TestProgram where
  name := "unroll"
  publicInput := [lit 27240554859721455327970068208906002034,
    lit 119514610692047185288834508057685931752]
  program := [("main", [mainOf do
    let sb ← B.stackBuf 8
    B.constInto (cell sb 0) (lit 1)
    for i in List.range 7 do
      B.mulInto (cell sb (i + 1)) (cell sb i) (← k (gp 1))
    B.assertEq (cell sb 7) (← k (gp 7))
    let buf ← B.heap 8
    buf.put 0 (← k (lit 5))
    buf.put 1 (← k (lit 7))
    discard <| B.call (chain 3).name [buf.p.v] 0
    publish (← buf.get 6) (← buf.get 7)]),
    ("chain", [chain 3])]

/-- `walk(buf, n)`: `n` Keccak steps over heap pairs, then the last pair. -/
def walk (n : Nat) : GFn where
  name := instName "walk" [.L n]
  arity := 1
  rets := 2
  body := fun ps => do
    for i in List.range n do
      B.keccak (.heap ps[0]! (2 * i) 2) (.heap ps[0]! (2 * i) 2) (.heap ps[0]! (2 * i + 2) 2)
    return [.load ps[0]! (2 * n), .load ps[0]! (2 * n + 1)]

/-- A WOTS-style walk: a range-checked runtime digit dispatches to a family's instance; the
recomputation at the end writes an already written pair, so write-once makes it a digest
assertion; a branch not taken holds an impossible assertion. Published: `H^2(5, 7)`. -/
def wotsWalk : TestProgram where
  name := "wots_walk"
  publicInput := [lit 208822183413446500621413149391147122921,
    lit 118328345503752981047975230716482008923]
  program := [("main", [mainOf do
    let buf ← B.heap 16
    buf.put 0 (← k (lit 5))
    buf.put 1 (← k (lit 7))
    let d ← k (gp 2)
    discard <| B.rangeCheck d 4
    let t ← B.dispatch d ((List.range 4).map fun i => (walk i).name) [buf.p.v] 2
    ifEq d (← k (gp 2)) (pure ()) (do B.assertEq (← k (lit 1)) (← k 0))
    let v ← B.stackBuf 2
    B.copy (cell v 0) t[0]!
    B.copy (cell v 1) t[1]!
    B.keccak (.heap buf.p.v 2 2) (.heap buf.p.v 2 2) (.frame v)
    publish t[0]! t[1]!]),
    ("walk", (List.range 4).map walk)]

/-- The compiler's test programs. -/
def all : List TestProgram := [conditionals, constParams, fibonacci, fibonacciBench,
  hashHeapChain, hashSlices, heapbufDyn, hint, identities, inline, loopScopes, «match», matchArms,
  nested, runtimeLoop, scoping, unroll, wotsWalk]

end LeanVMTests.Programs.Basic
