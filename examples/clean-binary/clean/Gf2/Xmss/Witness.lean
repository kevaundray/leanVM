module

public import Gf2.R1CS
public import Gf2.Xmss.Block

/-!
Witness scheduling for the XMSS block. `steps` lays out the role sequence of a signer set: the
signer-set header, then per group its header, per signer (in order) a key list block whenever the
key buffer is full, `ENC_0`, `ENC_1`, the chain steps of each public key block in slot order, the
block's `PK`, 31 `MERKLE` and `MERKLE_LAST`; then the group's final key list block and its
signer-set block (`FINAL` for the last group); idle instances pad to a power of two, at least 8.
Each step carries only prover data: the role, the free register bits it loads (keys, tips,
group fields) and the free message bits (randomness, Merkle siblings).

`solve` assigns one instance from its step and the incoming registers by evaluating the role's
clauses: helper signals, then bound compression inputs, the compression, helpers again, then the
`out` registers (`out = in` where no clause sets them). It never checks a constraint, so a bad
signature still gets a witness, one that violates the constraint it fails.
-/

@[expose] public section

namespace Gf2.Xmss.Witness

open Block

/-- Free bits loaded into `out` register `reg` from bit `start`. -/
structure Free where
  reg : Reg
  start : ℕ
  bits : Array Bool
  deriving Inhabited

structure Step where
  role : Role
  free : Array Free := #[]
  /-- Message-block bits from bit 0; bound bits are overwritten. -/
  m : Array Bool := #[]
  /-- Tamper: swap the Merkle children after binding. -/
  swap : Bool := false
  deriving Inhabited

/-- Witness tampers for the checks (input tampers edit the signer instead). -/
structure Tamper where
  /-- Drop the first signature's first chain step. -/
  skipChainStep : Bool := false
  /-- Swap the first signature's level-0 Merkle children. -/
  swapMerkle : Bool := false

def bytesB (d : ByteArray) : Array Bool := (Array.range (8 * d.size)).map (bitAt d)
def natB (x n : ℕ) : Array Bool := (Array.range n).map x.testBit

/-- The steps of signer `k` of group `g`; `first` selects the signature the tampers hit. -/
def signatureSteps (g : Group) (k : ℕ) (s : Signer) (t : Tamper) (first : Bool) : Array Step := Id.run do
  let mut out : Array Step := #[]
  if k ≥ 2 && k % 2 == 0 then out := out.push { role := .keys }
  out := out.push { role := .enc0, free := #[⟨.pp, 0, bytesB s.pp⟩, ⟨.root, 0, bytesB s.root⟩] }
  out := out.push { role := .enc1, m := bytesB s.randomness,
                    free := #[⟨.slots, 256, bytesB s.tips[0]!⟩, ⟨.slots, 384, bytesB s.tips[1]!⟩] }
  let e := digits (encodingDigest g.message g.leaf s.pp s.randomness)
  let mut skip := t.skipChainStep && first
  for j in [0:11] do
    for sl in [0:4] do
      if 4 * j + sl ≥ 2 then
        for _ in [0:CHAIN_LENGTH - 1 - e[4 * j + sl - 2]!] do
          if skip then skip := false else out := out.push { role := .chain sl }
    let next : Array Free := if j < 10 then
      (Array.range 4).map fun sl => ⟨.slots, 128 * sl, bytesB s.tips[4 * (j + 1) + sl - 2]!⟩ else #[]
    out := out.push { role := .pk, free := next }
  for l in [0:LOG_LIFETIME] do
    let sib := bytesB s.proof[l]!
    out := out.push { role := if l + 1 == LOG_LIFETIME then .merkleLast else .merkle,
                      m := Array.replicate 256 false ++ sib ++ sib, swap := t.swapMerkle && first && l == 0 }
  return out

/-- Number of instances: a power of two, at least 8. -/
def padded (n : ℕ) : ℕ := max 8 n.nextPowerOfTwo

def steps (gs : Array Group) (t : Tamper := {}) : Array Step := Id.run do
  let mut out : Array Step := #[{ role := .ssStart, free := #[⟨.ng, 0, natB gs.size 32⟩] }]
  for gi in [0:gs.size] do
    let g := gs[gi]!
    out := out.push { role := .groupStart, free := #[⟨.leaf, 0, natB g.leaf 32⟩,
      ⟨.nkc, 0, natB g.signers.size 32⟩, ⟨.msg, 0, bytesB g.message⟩] }
    for k in [0:g.signers.size] do
      out := out ++ signatureSteps g k g.signers[k]! t (gi == 0 && k == 0)
    out := out.push { role := .groupEnd }
    out := out.push { role := if gi + 1 == gs.size then .final else .ssKeys }
  return out ++ Array.replicate (padded out.size - out.size) { role := .idle }

def evalLin (z : Array Bool) (l : Lin) : Bool := l.foldl (fun x s => x ^^ z[s]!) false

def withHelpers (z : Array Bool) : Array Bool :=
  (evalDefs (z[·]!)).foldl (fun (z, i) b => (z.set! i b, i + 1)) (z, auxBase) |>.1

/-- Every signal of one instance (by signal) from its step and incoming registers. -/
def solve (step : Step) (regs : Array Bool) : Array Bool := Id.run do
  let k := step.role.index
  let mut z := ((Array.replicate nSignals false).set! 0 true).set! (selSig k) true
  for j in [0:nReg] do z := z.set! (1 + nRoles + j) regs[j]!
  let mut written := Array.replicate nReg false
  for f in step.free do
    for i in [0:f.bits.size] do
      z := z.set! (outSig f.reg (f.start + i)) f.bits[i]!
      written := written.set! (f.reg.offset + f.start + i) true
  for i in [0:step.m.size] do z := z.set! (mSig i) step.m[i]!
  z := withHelpers z
  let cls := roleClauses[k]!
  for cl in cls do
    if let .bind s v := cl.kind then
      if evalLin z cl.gate then z := z.set! s (evalLin z v)
  if step.swap then
    for i in [0:128] do
      let (a, b) := (z[mSig (256 + i)]!, z[mSig (384 + i)]!)
      z := (z.set! (mSig (256 + i)) b).set! (mSig (384 + i)) a
  let out := Blake2s.compress ((Array.range 8).map fun w => word (z[·]!) (hSig (32 * w)))
    ((Array.range 16).map fun w => word (z[·]!) (mSig (32 * w))) (word (z[·]!) (tSig 0)).toUInt64
    (if z[f0Sig]! then 0xFFFFFFFF else 0) 0
  for i in [0:256] do z := z.set! (oSig i) ((out[i / 32]! >>> (i % 32).toUInt32) &&& 1 == 1)
  z := withHelpers z
  for cl in cls do
    if let .set j v := cl.kind then
      if evalLin z cl.gate then
        if let some v := v then z := z.set! (outBit j) (evalLin z v)
        written := written.set! j true
  for j in [0:nReg] do
    unless written[j]! do z := z.set! (1 + nRoles + nReg + j) z[1 + nRoles + j]!
  return z

def fixedOf (z : Array Bool) : Vector F nFixed := Vector.ofFn fun v => if z[v.val + 1]! then 1 else 0

def outRegs (z : Array Bool) : Array Bool := (Array.range nReg).map fun j => z[1 + nRoles + nReg + j]!

/-- One instance's variables through Clean witness generation. -/
def witness (z : Array Bool) : Array F := witgen (hintOf (fixedOf z)) ops

/-- Indices of the rows of `rs` the signals `z` violate. -/
def violated (rs : Array Row) (z : Array Bool) : Array ℕ :=
  let e (l : Lin) : Bool := evalLin z l
  rs.zipIdx.filterMap fun (r, i) => if (e r.a && e r.b) != e r.c then some i else none

/-- Rows of the block that `w` (variables) violates. -/
def violations (w : Array F) : Array ℕ := violated rows (#[true] ++ w.map isOne)

/-- The witnesses of a step sequence from all-zero registers, each with the registers it leaves. -/
def foldWitnesses {σ : Type} {m : Type → Type} [Monad m] (ss : Array Step) (init : σ)
    (f : σ → ℕ → Array Bool → Array F → m σ) : m σ := do
  let mut regs := Array.replicate nReg false
  let mut acc := init
  for i in [0:ss.size] do
    let z := solve ss[i]! regs
    acc ← f acc i regs (witness z)
    regs := outRegs z
  return acc

/-- The `out` registers a witness leaves. -/
def outOf (w : Array F) : Array Bool := (Array.range nReg).map fun j => isOne w[nRoles + nReg + j]!

/-- The `in` registers of a witness. -/
def inOf (w : Array F) : Array Bool := (Array.range nReg).map fun j => isOne w[nRoles + j]!

/-- The boundary the verifier expects: digest bits then zeros out, all zero in. -/
def finalRegs (digest : ByteArray) : Array Bool := bytesB digest ++ Array.replicate (nReg - 256) false

end Gf2.Xmss.Witness
