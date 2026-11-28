import LeanVMTests.Programs.Support

/-!
# The programs of the VM's and the prover's tests

Each proved, run or refused by `crates/zkdsl/tests/suite/vm.rs` and `vm_proofs.rs`, which say
what each run computes and what it must report; the public input and streams are the tests' own.
-/

namespace LeanVMTests.Programs.Vm

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl LeanVMTests.Programs

/-- A bare program: no public input or streams of its own (the tests give them). -/
def bare (name : String) (body : B Unit) (fns : List (String × List GFn) := []) : TestProgram :=
  { name, program := ("main", [mainOf body]) :: fns }

/-- A loop body reading the enclosing `w = g^3` (a word, or the first of a constant list), after a
binding of `w` that never runs: in a compile-time branch not taken (`0`, `3`), in a runtime branch
whose bindings are its own (`1`, `4`), in a loop over nothing (`2`, `5`). -/
def bindingNeverRuns (j : Nat) : TestProgram :=
  bare s!"binding_never_runs_{j}" do
    let hb ← B.heap 2
    let w ← k (gp 3)
    B.loopConstF 0 2 2 (pure [hb.p.v, w.v]) fun i caps => do
      if j % 3 = 1 then ifEq (← k (lit 1)) (← k (lit 2)) (do discard <| k (gp 1)) (pure ())
      for _ in List.range 0 do discard <| k (gp 1)
      B.store (← B.mul (cap caps 0) i) 0 (cap caps 1)
    B.assertEq (← hb.get 1) (← k (gp 3))

/-- A frame run the loop body never reads is not captured (copying an unwritten run would pin its
cells); it is written after the loop. -/
def bindingNeverRuns6 : TestProgram :=
  bare "binding_never_runs_6" do
    let s ← B.stackBuf 2
    let hb ← B.heap 2
    B.loopConstF 0 2 1 (pure [hb.p.v]) fun i caps => do
      B.store (← B.mul (cap caps 0) i) 0 (← k (lit 5))
    B.keccak (.words [.const (lit 1), .const (lit 2)]) (.words [.const (lit 3), .const (lit 4)])
      (.frame s)

/-- One overwrite-mode duplex step of the guest's Fiat-Shamir transcript over the capacity `seed`:
a scalar packed into the rate as `[x, 2^64·tag]`, then a step over nothing; the challenges are each
output's first cell. -/
def duplexStep : TestProgram :=
  bare "duplex_step" do
    let seed ← B.stackBuf 5
    for (c, i) in [17195033418914725426, 428513430413020027537992053012892565,
        257116918944239717510212610026684884823, 22419017885407545356794260588114009968,
        296961243940228212369120540763663007988].zipIdx do
      B.constInto (cell seed i) (lit c)
    let rate ← B.stackBuf 2
    B.constInto (cell rate 0) (lit 110680464442257309701)
    B.constInto (cell rate 1) (lit (2 ^ 64))
    let sp ← B.stackBuf 13
    B.keccakDuplex (.frame rate) (.words [.zero, .zero]) (.frame sp) (.frame seed)
    let nxt ← B.stackBuf 13
    B.keccakDuplex (.words [.zero, .zero]) (.words [.zero, .zero]) (.frame nxt) (.frame sp)
    publish (cell sp 0) (cell nxt 0)

/-- An assertion that cannot hold, at source line 5. -/
def failedAssert : TestProgram :=
  bare "failed_assert" do
    let x ← k (gp 3)
    B.line 5
    B.assertEq x (← k (gp 4))

/-- `a / b` and `1 / b`, each one `MUL` whose quotient the prover solves for. -/
def fieldDiv : TestProgram :=
  bare "field_div" do
    let a ← k (gp 20)
    let b ← k (gp 7)
    let q ← B.fdiv a b
    let r ← B.fdiv (← k (lit 1)) b
    publish (← B.mul q b) (← B.mul r b)

/-- Constant `g`-powers as heap indices: `hb[g^2] = 7`, `hb[g^5] = 7 + 1 = 6`. -/
def gPowerArrayIndex : TestProgram :=
  bare "g_power_array_index" do
    let hb ← B.heap 8
    for (o, j) in [2, 5].zipIdx do
      B.store hb.p o (← k (lit (7 ^^^ j)))
    B.assertEq (← hb.get 2) (← k (lit 7))
    B.assertEq (← hb.get 5) (← k (lit 6))

/-- A heap buffer sized by the first public word, written at the second. -/
def heapBufRuntimeSize : TestProgram :=
  bare "heap_buf_runtime_size" do
    let pubP ← publicPtr
    let n ← B.load pubP 0
    let i ← B.load pubP 1
    let buf ← B.heapBufDyn n
    B.store (← B.mul buf i) 0 (← k (lit 7))

/-- A hinted `g`-power past every cell the run touches: `assert_gpow` on it, and a range check at
it as a runtime bound. -/
def hintedGpowPastTheRun : TestProgram :=
  bare "hinted_gpow_past_the_run" do
    let nb ← B.stackBuf 1
    B.witness "n" (.stack nb)
    let n := cell nb 0
    discard <| B.assertGpow n
    let x ← k (gp 3)
    discard <| B.rangeCheckRt x n
    publish x x

/-- The cells `1 ..< 1 + n`. -/
def counting (r : List V) : B Unit :=
  r.zipIdx.forM fun (c, i) => B.constInto (⟨c⟩ : Word) (lit (i + 1))

/-- `keccak_cells` of a 20-cell frame run (three blocks) and of a 16-word heap run (two), whose
digest it asserts. -/
def keccakCellsRun : TestProgram :=
  bare "keccak_cells_run" do
    let run ← B.stackBuf 20
    counting run
    let out ← B.stackBuf 2
    B.keccakCells (.frame run) (.frame out)
    let hb ← B.heap 16
    for i in List.range 16 do B.store hb.p i (← k (lit (i + 1)))
    let heapOut ← B.stackBuf 2
    B.keccakCells (.heap hb.p.v 0 16) (.frame heapOut)
    B.assertEq (cell heapOut 0) (← k (lit 51840480322923128489450997007565169922))
    B.assertEq (cell heapOut 1) (← k (lit 33612726202150371068450760312134188472))
    publish (cell out 0) (cell out 1)

/-- Messages of 135 and 136 bytes, on either side of a block's end; the second's digest asserted. -/
def keccakFullFinalBlock : TestProgram :=
  bare "keccak_full_final_block" do
    let m ← B.stackBuf 9
    counting m
    let one ← B.stackBuf 2
    B.keccakCells (.frame m) (.frame one) (len := some 135)
    let two ← B.stackBuf 2
    B.keccakCells (.frame m) (.frame two) (len := some 136)
    B.assertEq (cell two 0) (← k (lit 130804811289604742947188209148972184226))
    B.assertEq (cell two 1) (← k (lit 120867053423954764924108221573135705778))
    publish (cell one 0) (cell one 1)

/-- A two-cell frame run hashed with itself. -/
def keccakSelfHash : TestProgram :=
  bare "keccak_self_hash" do
    let a ← B.stackBuf 2
    B.constInto (cell a 0) (lit 5)
    B.constInto (cell a 1) (lit 7)
    let c ← B.stackBuf 2
    B.keccak (.frame a) (.frame a) (.frame c)
    publish (cell c 0) (cell c 1)

/-- A 17-cell block pair absorbed unpadded into a 13-cell state, then a final block continuing it:
the state in the heap (`heap`) or in frame cells. -/
def keccakState (name : String) (heap : Bool) : TestProgram :=
  bare name do
    let pair ← B.stackBuf 17
    counting pair
    let st : Cells ← if heap then (do let h ← B.heap 13; pure (Cells.heap h.p.v 0 13))
      else (do let r ← B.stackBuf 13; pure (Cells.frame r))
    B.keccakCells (.frame pair) st (final := false)
    let out ← B.stackBuf 2
    B.keccakCells (.words [.const (lit 18), .const (lit 19)]) (.frame out) (state := some st)
    publish (cell out 0) (cell out 1)

/-- `n` chained self-hashes of the cells `[5, 7]`: a `KECCAK` table of `n` rows. -/
def keccakSteps (n : Nat) : TestProgram :=
  bare s!"keccak_steps{n}" do
    let h ← B.stackBuf (2 * n + 2)
    B.constInto (cell h 0) (lit 5)
    B.constInto (cell h 1) (lit 7)
    for i in List.range n do
      let pair := (h.drop (2 * i)).take 2
      B.keccak (.frame pair) (.frame pair) (.frame ((h.drop (2 * i + 2)).take 2))
    publish (cell h (2 * n)) (cell h (2 * n + 1))

/-- `hint_log2_ceil` of 8 hinted bits at the floor `floor`. -/
def log2Ceil (name : String) (floor : Nat) : TestProgram :=
  bare name do
    let bits ← B.heap 8
    B.witness "bits" (← bits.slice 0 8)
    let mu ← B.hintLog2Ceil (← bits.slice 0 8) 8 floor
    publish (⟨mu.v⟩ : Word) (← k (lit 1))

/-- A loop body whose own values shadow nothing it reads, and whose counter it moves: it runs at
`i = 1` and `i = g^2`, the step `i·g·g`; `out[g^5]` is written after it, which a run at `i = g`
would have written first. -/
def loopBodyBindsFirst : TestProgram :=
  bare "loop_body_binds_first" do
    let out ← B.heap 8
    let name ← B.loopName
    B.helper name 2 (fun ps => do
      let i : Word := ⟨ps[0]!⟩
      let o : Word := ⟨ps[1]!⟩
      let q ← B.mul o i
      ifEq i (← k (lit 1)) (do B.store q 0 (← k (lit 9))) (pure ())
      B.store q 1 (← B.mul i (← k (gp 1)))
      B.store q 4 (← k (lit 6))
      let nx ← B.mul (← B.mul i (← k (gp 1))) (← k (gp 1))
      let c ← B.add nx (← k (gp 4))
      B.emit (.callIf c.v name [nx.v, o.v])) none
    B.emit (.call name [(← k (gp 0)).v, out.p.v] [])
    out.put 5 (← k (lit 7))
    B.assertEq (← out.get 0) (← k (lit 9))
    B.assertEq (← out.get 1) (← k (gp 1))
    B.assertEq (← out.get 3) (← k (gp 3))
    B.assertEq (← out.get 4) (← k (lit 6))
    B.assertEq (← out.get 6) (← k (lit 6))

/-- What a debug print computed, without the print (the embedded language has none): the product
`5·g` and a heap word. -/
def print : TestProgram :=
  bare "print" do
    let y ← k (lit 5 * gp 1)
    let b ← B.heap 2
    b.put 0 (← k (lit 3))
    publish y (← b.get 0)

/-- A range check at the constant bound `2^16`, `x = g^0`: its complement read sizes the memory. -/
def rangeCheckComplement65536 : TestProgram :=
  bare "range_check_complement_65536" do
    let x ← k (gp 0)
    discard <| B.rangeCheck x 65536
    publish x x

/-- A range check of `x = g^x0` at a hinted runtime bound. -/
def rangeCheckRuntime (name : String) (x0 : Nat) (pub : Bool) : TestProgram :=
  bare name do
    let nb ← B.stackBuf 1
    B.witness "n" (.stack nb)
    let x ← k (gp x0)
    discard <| B.rangeCheckRt x (cell nb 0)
    if pub then publish x x

/-- A range check whose two touched cells nothing writes. -/
def rangeCheckUnwritten : TestProgram :=
  bare "range_check_unwritten" do
    let x ← k (gp 300)
    discard <| B.rangeCheck x 400
    publish x x

/-- A heap word nothing stores to, read and used. -/
def unwrittenHeapRead : TestProgram :=
  bare "unwritten_heap_read" do
    let h ← B.heap 2
    let x ← h.get 0
    B.store (← publicPtr) 0 (← B.mul x (← k (gp 1)))

/-- `one()`: a hinted value asserted to be `1`. -/
def one : GFn where
  name := "one"
  arity := 0
  rets := 1
  body := fun _ => do
    let x ← B.witnessCell "x"
    B.assertEq (⟨x.v⟩ : Word) (← k (lit 1))
    return [.v x.v]

/-- `one() ** 0`: the base is evaluated, so its assertion runs. -/
def zeroPowerBase : TestProgram :=
  bare "zero_power_base" (do discard <| B.call "one" [] 1) [("one", [one])]

/-- The step counts `keccak_steps` is compiled at. -/
def keccakStepCounts : List Nat := [0, 1, 3, 512, 513]

/-- The programs of the VM's and the prover's tests. -/
def all : List TestProgram :=
  (List.range 6).map bindingNeverRuns ++ [bindingNeverRuns6, duplexStep, bare "empty" (pure ()),
    failedAssert, fieldDiv, gPowerArrayIndex, heapBufRuntimeSize, hintedGpowPastTheRun,
    keccakCellsRun, keccakFullFinalBlock, keccakSelfHash, keccakState "keccak_state_heap" true] ++
  keccakStepCounts.map keccakSteps ++
  [keccakState "keccak_two_blocks" false, log2Ceil "log2_ceil" 0, log2Ceil "log2_ceil_floor" 5,
    loopBodyBindsFirst, print, rangeCheckComplement65536,
    rangeCheckRuntime "range_check_complement_runtime" 0 true,
    rangeCheckRuntime "range_check_past_the_prover" 5 false, rangeCheckUnwritten,
    unwrittenHeapRead, zeroPowerBase]

end LeanVMTests.Programs.Vm
