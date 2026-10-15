module

public import Gf2.Blake2s
public import Gf2.Xmss.Spec

/-!
The XMSS block: one BLAKE2s compression (`h`, `m`, counter word `t`, final flag `f0`, all private
signals) plus a register file carried from instance to instance by link pairs
`(in_j, out_j)`, and a one-hot role chosen by the prover. A batch of linked instances verifies
every signature of a signer set and leaves the signer-set digest in the last instance's `dig`
register; the first instance starts from all-zero registers.

Every role is a list of clauses, each gated by the role's selector (or a product refining it):
`bind` fixes a compression input bit to a linear form, `set` fixes an `out` register bit (or
leaves it free: prover data such as chain tips), `assert` requires a linear form to vanish. Each
becomes the row `gate · lhs = 0`; clauses with equal `lhs` from disjoint roles share one row with
the sum of their gates. A register bit no active clause sets passes through, `out = in`, by the
row `(1 + Σ gates of its setters) · (in + out) = 0`. Unbound compression inputs are free. The
helper signals (`Ctl`: counters, slot position carries, the digit sum, two gate products) are
defined by rows `a · b = s + c` that hold for any assignment of their operands, so they constrain
nothing by themselves.

Registers (bits LSB first within bytes, values little-endian, as the hashed byte strings):
* `dig`: the final digest, link pairs `0 .. 255`.
* state, one-hot inside a run and all zero outside: `qRun` (between groups), `qGrp` (inside a
  group, between signatures), `qE1` (encoding block 1 next), `qPath` (bits `0 .. 10`: WOTS public
  key block `j`; bits `11 .. 42`: Merkle level `l`), `qKld` (key list hashed).
* signature: `cv` (encoding, then WOTS public key chaining value, then Merkle node in its first
  128 bits), `slots` (the four 16-byte words of the current public key block: chain values),
  `pos` (each slot's chain position, 3 bits), `digq` (the digits of later blocks), `idx`
  (`leaf_index >> l`), `pp`, `root` (the claimed key).
* group: `leaf`, `msg`, `nkc` (claimed key count), `nk` (keys so far), `klcv` (key list chaining
  value, then digest), `kbuf` (up to two pending keys, `kc` their occupancy).
* run: `ng` (claimed group count), `gc` (groups so far), `sscv` (signer-set chaining value).
-/

@[expose] public section

namespace Gf2.Xmss.Block

open Gf2.Blake2s (symCompress compressBits nPrivate toVector)

inductive Reg where
  | dig | qRun | qGrp | qE1 | qPath | qKld | cv | slots | pos | digq | idx | pp | root
  | leaf | msg | nkc | nk | klcv | kbuf | kc | ng | gc | sscv
  deriving BEq, Repr, Inhabited

/-- Register order: the order of the link pairs. -/
def Reg.all : List Reg :=
  [.dig, .qRun, .qGrp, .qE1, .qPath, .qKld, .cv, .slots, .pos, .digq, .idx, .pp, .root,
   .leaf, .msg, .nkc, .nk, .klcv, .kbuf, .kc, .ng, .gc, .sscv]

def Reg.width : Reg → ℕ
  | .dig | .cv | .msg | .klcv | .sscv => 256
  | .qRun | .qGrp | .qE1 | .qKld => 1
  | .qPath => 43
  | .slots | .kbuf => 512
  | .pos => 12
  | .digq => 120
  | .idx | .leaf | .nkc | .nk | .ng | .gc => 32
  | .pp | .root => 128
  | .kc => 2

def Reg.index : Reg → ℕ
  | .dig => 0 | .qRun => 1 | .qGrp => 2 | .qE1 => 3 | .qPath => 4 | .qKld => 5 | .cv => 6
  | .slots => 7 | .pos => 8 | .digq => 9 | .idx => 10 | .pp => 11 | .root => 12 | .leaf => 13
  | .msg => 14 | .nkc => 15 | .nk => 16 | .klcv => 17 | .kbuf => 18 | .kc => 19 | .ng => 20
  | .gc => 21 | .sscv => 22

/-- First register bit of each register, in `Reg.all` order. -/
def regOffsets : Array ℕ := (Reg.all.foldl (fun (acc, o) r => (acc.push o, o + r.width)) (#[], 0)).1

def Reg.offset (r : Reg) : ℕ := regOffsets[r.index]!

def nReg : ℕ := (Reg.all.map Reg.width).sum

inductive Role where
  | idle | ssStart | groupStart | enc0 | enc1 | chain (s : ℕ) | pk | merkle | merkleLast
  | keys | groupEnd | ssKeys | final
  deriving BEq, Repr, Inhabited

def Role.all : Array Role :=
  #[.idle, .ssStart, .groupStart, .enc0, .enc1, .chain 0, .chain 1, .chain 2, .chain 3, .pk,
    .merkle, .merkleLast, .keys, .groupEnd, .ssKeys, .final]

def Role.index : Role → ℕ
  | .idle => 0 | .ssStart => 1 | .groupStart => 2 | .enc0 => 3 | .enc1 => 4 | .chain s => 5 + s
  | .pk => 9 | .merkle => 10 | .merkleLast => 11 | .keys => 12 | .groupEnd => 13 | .ssKeys => 14
  | .final => 15

def nRoles : ℕ := Role.all.size

/-! Signals (signal `0` is the constant one): the fixed part the scheduler assigns (selectors,
`in` and `out` registers, compression inputs), then the compression output and private bits, then
the `Ctl` helpers. -/

def selSig (k : ℕ) : ℕ := 1 + k
def inSig (r : Reg) (i : ℕ) : ℕ := 1 + nRoles + r.offset + i
def outSig (r : Reg) (i : ℕ) : ℕ := 1 + nRoles + nReg + r.offset + i
/-- `out` signal of register bit `j`. -/
def outBit (j : ℕ) : ℕ := 1 + nRoles + nReg + j
def hBase : ℕ := 1 + nRoles + 2 * nReg
def hSig (i : ℕ) : ℕ := hBase + i
def mSig (i : ℕ) : ℕ := hBase + 256 + i
def tSig (i : ℕ) : ℕ := hBase + 768 + i
def f0Sig : ℕ := hBase + 800
/-- Variables the scheduler assigns. -/
def nFixed : ℕ := nRoles + 2 * nReg + 801
def oSig (i : ℕ) : ℕ := 1 + nFixed + i
def privBase : ℕ := 1 + nFixed + 256
def auxBase : ℕ := privBase + nPrivate

def cst (b : Bool) : Lin := if b then #[0] else #[]
def sumL (ls : Array Lin) : Lin := ls.foldl Lin.add #[]
def selL (r : Role) : Lin := #[selSig r.index]
def natBits (x n : ℕ) : Array Lin := (Array.range n).map fun i => cst (x.testBit i)
def bytesBits (d : ByteArray) : Array Lin := (Array.range (8 * d.size)).map fun i => cst (bitAt d i)
def zerosL (n : ℕ) : Array Lin := Array.replicate n #[]
def regIn (r : Reg) : Array Lin := (Array.range r.width).map fun i => #[inSig r i]
def regOut (r : Reg) : Array Lin := (Array.range r.width).map fun i => #[outSig r i]
def oBits : Array Lin := (Array.range 256).map fun i => #[oSig i]

/-- The 128 tweak bits `[0 | ty | 0 | 0 | sub | 0 | index]`, `sub` and `index` 32 bits each. -/
def tweakL (ty : UInt8) (sub index : Array Lin) : Array Lin :=
  zerosL 8 ++ natBits ty.toNat 8 ++ zerosL 16 ++ sub ++ zerosL 32 ++ index

/-- Bit `b` of digit `i` of the encoding digest, as output bit. -/
def digitBit (i b : ℕ) : ℕ := 64 * (i / 21) + 3 * (i % 21) + b

/-! Helper signals. -/

/-- A helper signal `s` defined by the row `a · b = s + c`. -/
structure Def where
  a : Lin
  b : Lin
  c : Lin

structure AuxSt where
  next : ℕ
  defs : Array Def

abbrev AM := StateM AuxSt

def defSig (a b c : Lin) : AM Lin :=
  modifyGet fun st => (#[st.next], { next := st.next + 1, defs := st.defs.push { a, b, c } })

def mul (a b : Lin) : AM Lin := defSig a b #[]

/-- `x + 1` modulo `2^width`: carry `c_1 = x_0`, then `c_{i + 1} = x_i · c_i` witnessed. -/
def inc (x : Array Lin) : AM (Array Lin) := do
  let mut out := #[x[0]!.add (cst true)]
  let mut c := x[0]!
  for i in [1:x.size] do
    out := out.push (x[i]!.add c)
    if i + 1 < x.size then c ← mul x[i]! c
  return out

/--
Column compression of a sum of bits: column `b` holds the forms of weight `2^b`. A full adder
takes three forms `x, y, z` to their sum `x + y + z` (linear) and a witnessed carry
`maj(x, y, z) = (x + z)(y + z) + z`; a half adder takes two to `x + y` and carry `x y`. Returns
one form per column: the sum's binary digits.
-/
def sumColumns (cols0 : Array (Array Lin)) : AM (Array Lin) := do
  let mut cols := cols0 ++ Array.replicate 16 #[]
  for b in [0:cols.size - 1] do
    for _ in [0:cols[b]!.size] do
      let col := cols[b]!
      if col.size ≥ 3 then
        let (x, y, z) := (col[0]!, col[1]!, col[2]!)
        let carry ← defSig (x.add z) (y.add z) z
        cols := (cols.set! b ((col.extract 3 col.size).push ((x.add y).add z))).modify (b + 1) (·.push carry)
      else if col.size == 2 then
        let carry ← mul col[0]! col[1]!
        cols := (cols.set! b #[col[0]!.add col[1]!]).modify (b + 1) (·.push carry)
  return cols.map fun col => col[0]?.getD #[]

structure Ctl where
  gcInc : Array Lin
  nkInc : Array Lin
  /-- Per slot, `p_0 p_1` and `p_0 p_1 p_2` of its position. -/
  posA : Array Lin
  posB : Array Lin
  /-- `(sel_merkle + sel_merkleLast) · idx_0`: the node is the right child. -/
  dirR : Lin
  /-- `sel_merkleLast · kc_0`: the key goes to the second buffer slot. -/
  w1 : Lin
  /-- Binary digits of the sum of the 42 encoding digits. -/
  digitSum : Array Lin

def ctlM : AM Ctl := do
  let gcInc ← inc (regIn .gc)
  let nkInc ← inc (regIn .nk)
  let mut posA := #[]
  let mut posB := #[]
  for s in [0:4] do
    let p := (regIn .pos).extract (3 * s) (3 * s + 3)
    let a ← mul p[0]! p[1]!
    posA := posA.push a
    posB := posB.push (← mul a p[2]!)
  let dirR ← mul ((selL .merkle).add (selL .merkleLast)) (regIn .idx)[0]!
  let w1 ← mul (selL .merkleLast) (regIn .kc)[0]!
  let digitSum ← sumColumns ((Array.range 3).map fun b =>
    (Array.range V).map fun i => #[oSig (digitBit i b)])
  return { gcInc, nkInc, posA, posB, dirR, w1, digitSum }

def ctlRun : Ctl × AuxSt := ctlM.run { next := auxBase, defs := #[] }
def ctl : Ctl := ctlRun.1
def defs : Array Def := ctlRun.2.defs
def nAux : ℕ := defs.size
/-- Number of signals, the constant one included. -/
def nSignals : ℕ := auxBase + nAux

/-! Clauses. -/

inductive Kind where
  /-- Compression input signal `s` equals `v`. -/
  | bind (s : ℕ) (v : Lin)
  /-- `out` register bit `j` equals `v`, or is free (`none`). -/
  | set (j : ℕ) (v : Option Lin)
  /-- `l` vanishes. -/
  | assert (l : Lin)

structure Clause where
  /-- The roles whose selectors the gate refines: the clause is active only in them. -/
  roles : List ℕ
  gate : Lin
  kind : Kind

/-- Roles of a clause group and the gate refining their selectors (their sum by default). -/
structure G where
  roles : List Role
  sub : Option Lin := none

abbrev CM := StateM (Array Clause)

def addClause (g : G) (k : Kind) : CM Unit :=
  modify (·.push { roles := g.roles.map Role.index
                   gate := g.sub.getD (sumL (g.roles.map selL).toArray), kind := k })

def bindAt (g : G) (sig : ℕ → ℕ) (start : ℕ) (vals : Array Lin) : CM Unit := do
  for i in [0:vals.size] do addClause g (.bind (sig (start + i)) vals[i]!)

def bindH (g : G) (vals : Array Lin) : CM Unit := bindAt g hSig 0 vals
def bindM (g : G) (start : ℕ) (vals : Array Lin) : CM Unit := bindAt g mSig start vals
def bindT (g : G) (vals : Array Lin) : CM Unit := bindAt g tSig 0 vals
def bindF0 (g : G) (v : Lin) : CM Unit := addClause g (.bind f0Sig v)

def setR (g : G) (r : Reg) (start : ℕ) (vals : Array Lin) : CM Unit := do
  for i in [0:vals.size] do addClause g (.set (r.offset + start + i) (some vals[i]!))

def freeR (g : G) (r : Reg) (start n : ℕ) : CM Unit := do
  for i in [0:n] do addClause g (.set (r.offset + start + i) none)

def zeroR (g : G) (r : Reg) : CM Unit := setR g r 0 (zerosL r.width)
def assert0 (g : G) (l : Lin) : CM Unit := addClause g (.assert l)
def assertEq (g : G) (l : Lin) (b : Bool) : CM Unit := assert0 g (l.add (cst b))
def bit1 (r : Reg) : Lin := (regIn r)[0]!

def one (r : Role) : G := { roles := [r] }

def clausesM (c : Ctl) : CM Unit := do
  let iv0 := bytesBits (wordsBytes IV0)
  let o := oBits
  let path := regIn .qPath
  let J := path.extract 0 11
  let LV := path.extract 11 43
  let cv := regIn .cv
  -- SS_START: block 0 of the signer-set hash, with the claimed group count.
  let g := one .ssStart
  assert0 g (sumL (#[bit1 .qRun, bit1 .qGrp, bit1 .qE1, bit1 .qKld] ++ path))
  bindH g iv0
  bindM g 0 (bytesBits "signers1".toUTF8 ++ regOut .ng ++ zerosL 160 ++ bytesBits (blake2s .empty))
  bindT g (natBits 64 32)
  bindF0 g (cst false)
  setR g .sscv 0 o
  freeR g .ng 0 32
  setR g .qRun 0 #[cst true]
  -- GROUP_START: the group header block `(leaf, n_keys, message, 0, 0)`; opens the key list.
  let g := one .groupStart
  assertEq g (bit1 .qRun) true
  bindH g (regIn .sscv)
  bindM g 0 (regOut .leaf ++ zerosL 32 ++ regOut .nkc ++ zerosL 32 ++ regOut .msg ++ zerosL 128)
  bindT g (zerosL 7 ++ c.gcInc.extract 0 25)
  bindF0 g (cst false)
  setR g .sscv 0 o
  freeR g .leaf 0 32
  freeR g .nkc 0 32
  freeR g .msg 0 256
  setR g .gc 0 c.gcInc
  setR g .klcv 0 iv0
  zeroR g .nk
  zeroR g .kc
  zeroR g .kbuf
  setR g .qRun 0 #[cst false]
  setR g .qGrp 0 #[cst true]
  -- ENC_0: first block of the encoding hash, `tweak(ENCODING, 0, leaf) | pp | message`.
  let g := one .enc0
  assertEq g (bit1 .qGrp) true
  bindH g iv0
  bindM g 0 (tweakL TWEAK_ENCODING (natBits 0 32) (regIn .leaf) ++ regOut .pp ++ regIn .msg)
  bindT g (natBits 64 32)
  bindF0 g (cst false)
  setR g .cv 0 o
  freeR g .pp 0 128
  freeR g .root 0 128
  setR g .qGrp 0 #[cst false]
  setR g .qE1 0 #[cst true]
  -- ENC_1: last block `randomness | 0`; the digest's digits, top bits zero, sum 195.
  let g := one .enc1
  assertEq g (bit1 .qE1) true
  assertEq g #[oSig 63] false
  assertEq g #[oSig 127] false
  for b in [0:c.digitSum.size] do
    assertEq g c.digitSum[b]! (TARGET_SUM.testBit b)
  bindH g cv
  bindM g 192 (zerosL 320)
  bindT g (natBits 96 32)
  bindF0 g (cst true)
  setR g .cv 0 iv0
  setR g .slots 0 (tweakL TWEAK_WOTS_PK (natBits 0 32) (regIn .leaf) ++ regIn .pp)
  freeR g .slots 256 256
  let digit (i : ℕ) : Array Lin := (Array.range 3).map fun b => #[oSig (digitBit i b)]
  setR g .pos 0 (natBits 0x3F 6 ++ digit 0 ++ digit 1)
  setR g .digq 0 ((Array.range (V - 2)).flatMap fun i => digit (i + 2))
  setR g .idx 0 (regIn .leaf)
  setR g .qE1 0 #[cst false]
  setR g .qPath 0 #[cst true]
  -- CHAIN_s: one step of the chain in slot `s` of block `j`: chain `c = 4j - 2 + s`, from
  -- position `p` to `p + 1`, never past 7.
  for s in [0:4] do
    let g := one (.chain s)
    let p := (regIn .pos).extract (3 * s) (3 * s + 3)
    assertEq g (sumL J) true
    assert0 g c.posB[s]!
    let chainBits := (Array.range 6).map fun k => sumL ((Array.range 11).filterMap fun j =>
      if 4 * j + s ≥ 2 && (4 * j + s - 2).testBit k then some J[j]! else none)
    bindH g iv0
    bindM g 0 (tweakL TWEAK_CHAIN (p ++ chainBits ++ zerosL 23) (regIn .leaf) ++ regIn .pp ++
      (regIn .slots).extract (128 * s) (128 * s + 128) ++ zerosL 128)
    bindT g (natBits 48 32)
    bindF0 g (cst true)
    setR g .slots (128 * s) (o.extract 0 128)
    setR g .pos (3 * s) #[p[0]!.add (cst true), p[1]!.add p[0]!, p[2]!.add c.posA[s]!]
  -- PK: public key block `j` once every slot reached position 7; loads block `j + 1`.
  let g := one .pk
  assertEq g (sumL J) true
  for i in [0:12] do assertEq g (regIn .pos)[i]! true
  bindH g cv
  bindM g 0 (regIn .slots)
  bindT g ((Array.range 32).map fun k => sumL ((Array.range 11).filterMap fun j =>
    if (64 * (j + 1)).testBit k then some J[j]! else none))
  bindF0 g J[10]!
  setR g .cv 0 o
  freeR g .slots 0 512
  setR g .pos 0 ((regIn .digq).extract 0 12)
  setR g .digq 0 ((regIn .digq).extract 12 120 ++ zerosL 12)
  -- PK and MERKLE advance `qPath` by one.
  setR { roles := [.pk, .merkle] } .qPath 0 (#[#[]] ++ path.extract 0 42)
  -- MERKLE, MERKLE_LAST: node at level `l + 1`, index `idx >> 1`, the current node left or right
  -- by `idx_0`, the sibling free.
  let gm : G := { roles := [.merkle, .merkleLast] }
  let gmL := (selL .merkle).add (selL .merkleLast)
  bindH gm iv0
  let level := (Array.range 32).map fun k => sumL ((Array.range 32).filterMap fun l =>
    if (l + 1).testBit k then some LV[l]! else none)
  bindM gm 0 (tweakL TWEAK_MERKLE level ((regIn .idx).extract 1 32 ++ zerosL 1) ++ regIn .pp)
  bindM { gm with sub := some (gmL.add c.dirR) } 256 (cv.extract 0 128)
  bindM { gm with sub := some c.dirR } 384 (cv.extract 0 128)
  bindT gm (natBits 64 32)
  bindF0 gm (cst true)
  let g := one .merkle
  assertEq g (sumL (LV.extract 0 31)) true
  setR g .cv 0 (o.extract 0 128)
  setR g .idx 0 ((regIn .idx).extract 1 32 ++ zerosL 1)
  -- MERKLE_LAST: the root equals the claimed key, which joins the key buffer.
  let g := one .merkleLast
  assertEq g LV[31]! true
  assertEq g (regIn .kc)[1]! false
  for i in [0:128] do assert0 g (o[i]!.add (regIn .root)[i]!)
  let key := regIn .root ++ regIn .pp
  setR { g with sub := some ((selL .merkleLast).add c.w1) } .kbuf 0 key
  setR { g with sub := some c.w1 } .kbuf 256 key
  setR g .kc 0 #[cst true, (regIn .kc)[0]!]
  setR g .nk 0 c.nkInc
  setR g .qPath 42 #[cst false]
  setR g .qGrp 0 #[cst true]
  -- KEYS, GROUP_END: a key list block of the two buffered keys (non-final), or of the last one or
  -- two (final, with the claimed key count).
  let gk : G := { roles := [.keys, .groupEnd] }
  bindH gk (regIn .klcv)
  bindM gk 0 (regIn .kbuf)
  bindT gk (zerosL 5 ++ (regIn .nk).extract 0 27)
  setR gk .klcv 0 o
  let g := one .keys
  assertEq g (bit1 .qGrp) true
  assertEq g (regIn .kc)[1]! true
  bindF0 g (cst false)
  zeroR g .kbuf
  zeroR g .kc
  let g := one .groupEnd
  assertEq g (bit1 .qGrp) true
  assertEq g (regIn .kc)[0]! true
  for i in [0:32] do assert0 g ((regIn .nk)[i]!.add (regIn .nkc)[i]!)
  bindF0 g (cst true)
  setR g .qGrp 0 #[cst false]
  setR g .qKld 0 #[cst true]
  -- SS_KEYS, FINAL: the group's key list block `(key_list, 0, 0, 0, 0)`; FINAL closes the
  -- signer-set hash with the claimed group count, writes `dig` and clears every other register.
  let gs : G := { roles := [.ssKeys, .final] }
  assertEq gs (bit1 .qKld) true
  bindH gs (regIn .sscv)
  bindM gs 0 (regIn .klcv ++ zerosL 256)
  bindT gs (zerosL 6 ++ #[cst true] ++ (regIn .gc).extract 0 25)
  let g := one .ssKeys
  bindF0 g (cst false)
  setR g .sscv 0 o
  setR g .qKld 0 #[cst false]
  setR g .qRun 0 #[cst true]
  let g := one .final
  bindF0 g (cst true)
  for i in [0:32] do assert0 g ((regIn .gc)[i]!.add (regIn .ng)[i]!)
  setR g .dig 0 o
  for r in Reg.all do
    if r != .dig then zeroR g r

def clauses : Array Clause := (clausesM ctl).run #[] |>.2

/-- Clauses active in role `k`. -/
def roleClauses : Array (Array Clause) :=
  (Array.range nRoles).map fun k => clauses.filter (·.roles.contains k)

/-! Rows. -/

def disjoint (a b : List ℕ) : Bool := a.all fun x => !b.contains x

/-- The compression rows, pinning its output to `oSig`. -/
def compressionRows : Array Row × ℕ :=
  let word (sig : ℕ → ℕ) (w : ℕ) : Word := (Array.range 32).map fun i => #[sig (32 * w + i)]
  let h := (Array.range 8).map (word hSig)
  let msg := (Array.range 16).map (word mSig)
  let st := (symCompress h msg (word tSig 0) (Array.replicate 32 #[f0Sig]) (oSig 0)).run
    { next := privBase, rows := #[] } |>.2
  (st.rows, st.next)

/-- Exactly one selector: `Σ sel = 1`, and `(Σ_{i < k} sel_i) · sel_k = 0` for every `k`. -/
def oneHotRows : Array Row :=
  #[{ a := #[], b := #[], c := (sumL ((Array.range nRoles).map fun k => #[selSig k])).add (cst true) }] ++
  (Array.range nRoles).filterMap fun k =>
    if k == 0 then none
    else some { a := sumL ((Array.range k).map fun i => #[selSig i]), b := #[selSig k], c := #[] }

def defRows : Array Row :=
  defs.mapIdx fun i d => { a := d.a, b := d.b, c := d.c.add #[auxBase + i] }

def Clause.lhs (cl : Clause) : Option Lin :=
  match cl.kind with
  | .bind s v => some (v.add #[s])
  | .set j (some v) => some (v.add #[outBit j])
  | .set _ none => none
  | .assert l => some l

/-- One row per distinct `lhs`, gates of disjoint roles summed. -/
def clauseRows : Except String (Array Row) := do
  let mut index : Std.HashMap Lin ℕ := {}
  let mut groups : Array (Lin × Lin × List ℕ) := #[]
  for cl in clauses do
    let some lhs := cl.lhs | continue
    if lhs.isEmpty then continue
    match index[lhs]? with
    | some k =>
      let (l, g, rs) := groups[k]!
      unless disjoint rs cl.roles do throw s!"clause {lhs} repeated in roles {rs} and {cl.roles}"
      groups := groups.set! k (l, g.add cl.gate, rs ++ cl.roles)
    | none =>
      index := index.insert lhs groups.size
      groups := groups.push (lhs, cl.gate, cl.roles)
  return groups.map fun (lhs, g, _) => { a := g, b := lhs, c := #[] }

/-- `(1 + Σ gates of the clauses setting the bit) · (in + out) = 0` for every register bit. -/
def passRows : Except String (Array Row) := do
  let mut setters : Array (Lin × List ℕ) := Array.replicate nReg (#[], [])
  for cl in clauses do
    let .set j _ := cl.kind | continue
    let (g, rs) := setters[j]!
    unless disjoint rs cl.roles do throw s!"register bit {j} set twice in roles {rs} and {cl.roles}"
    setters := setters.set! j (g.add cl.gate, rs ++ cl.roles)
  return (Array.range nReg).map fun j =>
    { a := (cst true).add setters[j]!.1, b := #[1 + nRoles + j, 1 + nRoles + nReg + j], c := #[] }

/-- All rows at offset 0. -/
def build : Except String (Array Row) := do
  let (comp, next) := compressionRows
  unless next == auxBase do throw s!"compression ends at signal {next}, expected {auxBase}"
  unless ctlRun.2.next == nSignals do throw "helper signals out of order"
  return comp ++ oneHotRows ++ defRows ++ (← clauseRows) ++ (← passRows)

def rows : Array Row := match build with
  | .ok rs => rs
  | .error _ => #[]

/-- The rows after the compression's: everything the roles add. -/
def controlRows : Array Row := rows.extract compressionRows.1.size rows.size

/-- Link pair `j`: register bit `j` in and out. -/
def links : Array (ℕ × ℕ) := (Array.range nReg).map fun j => (1 + nRoles + j, 1 + nRoles + nReg + j)

/-! Clean circuit. -/

def shiftRow (offset : ℕ) (r : Row) : Row :=
  let f (l : Lin) : Lin := l.map fun s => if s == 0 then 0 else s + offset
  { a := f r.a, b := f r.b, c := f r.c }

def isOne (x : F) : Bool := x == 1

/-- The helper signals, from the signals before them (`get` by signal). -/
def evalDefs (get : ℕ → Bool) : Array Bool :=
  defs.foldl (fun acc d =>
    let v (s : ℕ) : Bool := if s ≥ auxBase then acc[s - auxBase]! else get s
    let e (l : Lin) : Bool := l.foldl (fun x s => x ^^ v s) false
    acc.push ((e d.a && e d.b) ^^ e d.c)) (Array.emptyWithCapacity nAux)

def fixedKey : String := "xmss.fixed"

def hintOf (fixed : Vector F nFixed) : ProverHint F := fun key n =>
  if h : key = fixedKey ∧ n = nFixed then #[h.2 ▸ fixed] else #[]

def word (get : ℕ → Bool) (base : ℕ) : UInt32 :=
  (List.range 32).foldl (fun x i => if get (base + i) then x ||| (1 <<< i.toUInt32) else x) 0

/-- The native compression's output then private bits, inputs read by signal. -/
def compressionWitness (get : ℕ → Bool) : Array F :=
  let h := (Array.range 8).map fun w => word get (hSig (32 * w))
  let m := (Array.range 16).map fun w => word get (mSig (32 * w))
  compressBits h m (word get (tSig 0)) (if get f0Sig then 0xFFFFFFFF else 0)

def circuit : Circuit F Unit := fun offset => (do
  let get (env : ProverEnvironment F) (s : ℕ) : Bool := s == 0 || isOne (env.get (offset + s - 1))
  let _ ← witnessVectorNative nFixed fun env =>
    (env.hint fixedKey nFixed)[0]?.getD (Vector.replicate nFixed 0)
  let _ ← witnessVectorNative (256 + nPrivate) fun env => toVector (compressionWitness (get env))
  let _ ← witnessVectorNative nAux fun env =>
    toVector ((evalDefs (get env)).map fun (b : Bool) => if b then (1 : F) else 0)
  for chunkRows in (rows.toList.toChunks 256) do
    chunk (asserts (chunkRows.map fun r => (shiftRow offset r).toE))) offset

/-- The circuit's operations at offset 0, built once. -/
def ops : List (Operation F) := (circuit 0).2

end Gf2.Xmss.Block
