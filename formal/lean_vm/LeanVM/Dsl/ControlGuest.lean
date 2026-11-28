/-
  LeanVM.Dsl.ControlGuest

  Guest functions ported to the embedded language with the builder's runtime control, hints,
  checks and memory: `assert_small_g_power`, the `log2_ceil_in_the_exponent` family (a runtime
  branch), `rs_eq_run` with the `rs_eq_rows` family (a runtime loop and a fused dispatch),
  `certify_placement` (a heap slice) and `list_split`, each as the zkDSL compiles it today.
-/

module

public import LeanVM.Dsl.Mem
public import LeanVM.Dsl.Guest

/-!
# Ported guest functions: control, hints, memory

Each function is the faithful port of the zkDSL function in its docstring: the same core
statements as `Expand` makes, in its order, with the trace events it records (`B.use` where an
alias is read, `B.shifted` where a shifted pointer is made a value). What the zkDSL decides at
compile time is Lean here: an `if const(...)` or an `if` on two integers is a Lean `if`, a constant
array element a Lean value (`arrInt`).
-/

namespace LeanVM.Dsl.Guest

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## Configuration -/

def SIZE_BITS : Nat := LeanVM.Guest.Data.const_SIZE_BITS
def SEL_TAB_NIBBLES : Nat := LeanVM.Guest.Data.const_SEL_TAB_NIBBLES
def INV_GEN : Nat := LeanVM.Guest.Data.const_INV_GEN
def PCS_MIN_MU : Nat := LeanVM.Guest.Data.const_PCS_MIN_MU
def BASE_FIELD_BITS : Nat := LeanVM.Guest.Data.const_BASE_FIELD_BITS
def RS_CHUNK : Nat := LeanVM.Guest.Data.const_RS_CHUNK
def RS_CHUNK_BITS : Nat := LeanVM.Guest.Data.const_RS_CHUNK_BITS
def RS_COUNT_BITS : Nat := LeanVM.Guest.Data.const_RS_COUNT_BITS
def N_TABLES : Nat := LeanVM.Guest.Data.const_N_TABLES
def N_COL_GROUPS : Nat := LeanVM.Guest.Data.const_N_COL_GROUPS
def N_COMMITTED_COLS : Nat := LeanVM.Guest.Data.const_N_COMMITTED_COLS
def RANK_KEYS_AT : Nat := LeanVM.Guest.Data.const_RANK_KEYS_AT
def RANK_KEY_BOUND : Nat := LeanVM.Guest.Data.const_RANK_KEY_BOUND
def CLAIM_GROUP : Nat := LeanVM.Guest.Data.const_CLAIM_GROUP
def BIG_GROUPS : Nat := LeanVM.Guest.Data.const_BIG_GROUPS
def CLAIM_BIG : Nat := LeanVM.Guest.Data.const_CLAIM_BIG

/-- `COL_GROUP_START[i]`. -/
def COL_GROUP_START (i : Nat) : Nat := arrInt LeanVM.Guest.Data.arr_COL_GROUP_START i
/-- `COL_KAPPA_SRC[i]`. -/
def COL_KAPPA_SRC (i : Nat) : Nat := arrInt LeanVM.Guest.Data.arr_COL_KAPPA_SRC i
/-- `COL_KAPPA_ADJ[i]`. -/
def COL_KAPPA_ADJ (i : Nat) : Nat := arrInt LeanVM.Guest.Data.arr_COL_KAPPA_ADJ i

/-! ## `assert_small_g_power` -/

/-- `assert_small_g_power(x, g_squares)`:

```
digits = StackBuf(SEL_TAB_NIBBLES)
hint_decompose_digits_exponent(digits, x, 4 * SEL_TAB_NIBBLES, SEL_TAB_NIBBLES, 4, 0)
shares = g_squares * GEN ** SIZE_BITS
for j in unroll(0, SEL_TAB_NIBBLES):
    d = digits[j]
    assert log(d) < 16
    if const(j == 0):
        rebuilt = shares[d]
    else:
        rebuilt *= shares[GEN ** (16 * j) * d]
assert rebuilt == x
return
```
-/
def assertSmallGPower : GFn where
  name := "assert_small_g_power"
  arity := 2
  rets := 0
  body ps := do
    let x : Word := ⟨ps[0]!⟩
    let gsq : Word := ⟨ps[1]!⟩
    let digits ← B.stackBuf SEL_TAB_NIBBLES
    B.hintDigitsExp (.stack digits) x (4 * SEL_TAB_NIBBLES) SEL_TAB_NIBBLES 4 0
    let rebuilt ← (List.range SEL_TAB_NIBBLES).foldlM (init := x) fun acc j => do
      let d : Word := ⟨digits[j]!⟩
      discard <| B.rangeCheck d 16
      let q ← B.mul gsq d
      let l ← B.load q (SIZE_BITS + 16 * j)
      if j = 0 then return l else B.mul acc l
    B.assertEq rebuilt x
    return []

/-! ## `log2_ceil_in_the_exponent`: a runtime branch -/

/-- `log2_ceil_in_the_exponent(g_N, g_squares, floor: Const, nbits: Const)`, one function per
`(floor, nbits)`:

```
bits = HeapBuf(GEN ** nbits)
hint_decompose_bits_exponent(bits, g_N, nbits)
g_log = hint_log2_ceil(bits, nbits, floor)
assert log(g_log) < SIZE_BITS
assert log(g_log / GEN ** floor) < SIZE_BITS
assert_small_g_power(g_squares[g_log] / g_N, g_squares)
if g_log != GEN ** floor:
    assert_small_g_power(g_N * INV_GEN / g_squares[g_log * INV_GEN], g_squares)
return g_log
```

The `if` is a runtime branch: its zero block is the absent `else`, elaborated first. -/
def log2CeilInTheExponent (floor nbits : Nat) : GFn where
  name := instName "log2_ceil_in_the_exponent" [.L floor, .L nbits]
  arity := 2
  rets := 1
  body ps := do
    let gN : Word := ⟨ps[0]!⟩
    let gsq : Word := ⟨ps[1]!⟩
    let sz ← B.const (gpowE nbits)
    let bits ← B.heapBufDyn sz
    B.hintBitsExpTo (.heap bits.v 0 nbits) gN nbits
    let glog : Word := ⟨(← B.hintLog2Ceil (.heap bits.v 0 nbits) nbits floor).v⟩
    discard <| B.rangeCheck glog SIZE_BITS
    let k ← B.const (gpowE (SIZE_BITS - 1))
    let fl ← B.const (gpowE floor)
    let q ← B.fdiv glog fl
    discard <| B.rangeCheckK q k
    let p ← B.mul gsq glog
    let l ← B.load p 0
    let a ← B.fdiv l gN
    discard <| B.call assertSmallGPower.name [a.v, gsq.v] 0
    let fl' ← B.const (gpowE floor)
    let c ← B.add glog fl'
    discard <| B.ite c (pure ()) do
      let i1 ← B.const (litField INV_GEN)
      let m1 ← B.mul gN i1
      let i2 ← B.const (litField INV_GEN)
      let m2 ← B.mul glog i2
      let p2 ← B.mul gsq m2
      let l2 ← B.load p2 0
      let a2 ← B.fdiv m1 l2
      discard <| B.call assertSmallGPower.name [a2.v, gsq.v] 0
    return [.v glog.v]

/-! ## `rs_eq_run` and the `rs_eq_rows` family: a runtime loop and a fused dispatch -/

/-- `rs_eq_rows(row, zs, ps, n: Const)`, one function per `n`:

```
nxt = row * GEN ** BASE_FIELD_BITS
if const(n == 0):
    nxt = row
else:
    zv = StackBuf(RS_CHUNK * BASE_FIELD_BITS)
    a = StackBuf(RS_CHUNK)
    for i in unroll(0, n):
        zv[BASE_FIELD_BITS * i] = zs[GEN ** i]
        a[i] = ps[GEN ** i]
    for k in unroll(0, BASE_FIELD_BITS):
        acc = row[GEN ** k]
        for i in unroll(0, n):
            acc *= zv[BASE_FIELD_BITS * i + k] + a[i]
            if const(k != BASE_FIELD_BITS - 1):
                zv[BASE_FIELD_BITS * i + k + 1] = zv[BASE_FIELD_BITS * i + k] * zv[BASE_FIELD_BITS * i + k]
        nxt[GEN ** k] = acc
return nxt
```

`nxt` is a shifted pointer, made a value only by the `return`, after the return cell. -/
def rsEqRows (n : Nat) : GFn where
  name := instName "rs_eq_rows" [.L n]
  arity := 3
  rets := 1
  body ps := do
    let row : Word := ⟨ps[0]!⟩
    let zs : Word := ⟨ps[1]!⟩
    let pv : Word := ⟨ps[2]!⟩
    if n = 0 then
      return [.into fun r => do
        let v ← B.use row
        B.copy (⟨r⟩ : Word) v]
    let L := BASE_FIELD_BITS
    let zv ← B.stackBuf (RS_CHUNK * L)
    let a ← B.stackBuf RS_CHUNK
    (List.range n).forM fun i => do
      B.loadInto (⟨zv[L * i]!⟩ : Word) zs i
      B.loadInto (⟨a[i]!⟩ : Word) pv i
    (List.range L).forM fun k => do
      let acc0 ← B.load row k
      let acc ← (List.range n).foldlM (init := acc0) fun acc i => do
        let s ← B.add (⟨zv[L * i + k]!⟩ : Word) (⟨a[i]!⟩ : Word)
        let acc' ← B.mul acc s
        if k ≠ L - 1 then
          B.mulInto (⟨zv[L * i + k + 1]!⟩ : Word) (⟨zv[L * i + k]!⟩ : Word)
            (⟨zv[L * i + k]!⟩ : Word)
        return acc'
      B.store row (L + k) acc
    return [.into fun r => do
      let v ← B.shifted row L
      B.copy (⟨r⟩ : Word) v]

/-- `rs_eq_run(z_vals, point1, count_g)`:

```
bits = StackBuf(RS_COUNT_BITS)
hint_decompose_bits_exponent(bits, count_g, RS_COUNT_BITS)
r_g = GEN ** 0
q_g = GEN ** 0
for k in unroll(0, RS_COUNT_BITS):
    b = bits[k]
    bits[k] = b * b
    if const(k // RS_CHUNK_BITS == 0):
        r_g *= 1 + b * (1 + GEN ** (2 ** k))
    else:
        q_g *= 1 + b * (1 + GEN ** (2 ** (k - RS_CHUNK_BITS)))
assert q_g ** RS_CHUNK * r_g == count_g
chain = HeapBuf((q_g * GEN ** 2) ** BASE_FIELD_BITS)
for k in unroll(0, BASE_FIELD_BITS):
    chain[GEN ** k] = 1
for xq in mul_range(1, q_g):
    base = xq ** RS_CHUNK
    done = rs_eq_rows(chain * xq ** BASE_FIELD_BITS, z_vals * base, point1 * base, RS_CHUNK)
base = q_g ** RS_CHUNK
row = chain * q_g ** BASE_FIELD_BITS
last = match(log(r_g), range(0, RS_CHUNK), lambda n: rs_eq_rows(row, z_vals * base, point1 * base, n))
return last
```

`r_g` and `q_g` start as the constant `1`, so their first factor is the product itself. -/
def rsEqRun : GFn where
  name := "rs_eq_run"
  arity := 3
  rets := 1
  body ps := do
    let zv : Word := ⟨ps[0]!⟩
    let p1 : Word := ⟨ps[1]!⟩
    let cnt : Word := ⟨ps[2]!⟩
    let bits ← B.stackBuf RS_COUNT_BITS
    B.hintBitsExpTo (.stack bits) cnt RS_COUNT_BITS
    let step : Option Word → Word → B (Option Word) := fun acc f => match acc with
      | none => pure (some f)
      | some a => some <$> B.mul a f
    let (r, q) ← (List.range RS_COUNT_BITS).foldlM
      (init := ((none : Option Word), (none : Option Word)))
      fun (r, q) k => do
        let b : Var .bit := ⟨bits[k]!⟩
        B.mulInto b b b
        if k / RS_CHUNK_BITS = 0 then
          let f ← bitFactor b k
          return (← step r f, q)
        else
          let f ← bitFactor b (k - RS_CHUNK_BITS)
          return (r, ← step q f)
    let r := r.getD default
    let q := q.getD default
    let q8 ← B.pow q RS_CHUNK
    let t ← B.mul q8 r
    B.assertEq t cnt
    let s2 ← B.shifted q 2
    let sz ← B.pow s2 BASE_FIELD_BITS
    let chain ← B.heapBufDyn sz
    (List.range BASE_FIELD_BITS).forM fun k => do
      let one ← B.const 1
      B.store chain k one
    B.loopRtF 0 (pure q) 3 (pure [chain.v, zv.v, p1.v]) fun xq caps => do
      let base ← B.pow xq RS_CHUNK
      let dst ← B.fresh
      let x64 ← B.pow xq BASE_FIELD_BITS
      let a1 ← B.mul (⟨caps[0]!⟩ : Word) x64
      let a2 ← B.mul (⟨caps[1]!⟩ : Word) base
      let a3 ← B.mul (⟨caps[2]!⟩ : Word) base
      B.callInto (rsEqRows RS_CHUNK).name [a1.v, a2.v, a3.v] [dst]
    let base ← B.pow q RS_CHUNK
    let q64 ← B.pow q BASE_FIELD_BITS
    let row ← B.mul chain q64
    let last ← B.targets [none]
    let a2 ← B.mul zv base
    let a3 ← B.mul p1 base
    B.dispatchInto r ((List.range RS_CHUNK).map fun n => (rsEqRows n).name) [row.v, a2.v, a3.v]
      last
    return [.v last[0]!]

/-! ## `certify_placement`: heap buffers, a heap slice -/

/-- `rank_keys[kappa_g]`, `rank_keys = g_squares * GEN ** RANK_KEYS_AT`: the index folded with the
shift. -/
def rankKey (gsq kg : Word) : B Word := do
  let p ← B.mul gsq kg
  B.load p RANK_KEYS_AT

/-- `certify_placement(kappa_base, g_squares)`:

```
kb = StackBuf(N_TABLES + 2)
for i in unroll(0, N_TABLES + 2):
    kb[i] = kappa_base[GEN ** i]
rank_keys = g_squares * GEN ** RANK_KEYS_AT
group_key = HeapBuf(N_COL_GROUPS)
group_size = HeapBuf(N_COL_GROUPS)
for gi in unroll(0, N_COL_GROUPS):
    c0 = COL_GROUP_START[gi]
    kappa_g = kb[COL_KAPPA_SRC[c0]] * GEN ** COL_KAPPA_ADJ[c0]
    assert log(kappa_g) < SIZE_BITS
    group_key[GEN ** gi] = rank_keys[kappa_g] * INV_GEN ** c0
    group_size[GEN ** gi] = g_squares[kappa_g] ** (COL_GROUP_START[gi + 1] - c0)
group_order = HeapBuf(N_COL_GROUPS)
hint_witness(group_order[0:N_COL_GROUPS], "col_group_order")
group_base = HeapBuf(N_COL_GROUPS)
g_total = GEN ** 0
for rank in unroll(0, N_COL_GROUPS):
    gi = group_order[GEN ** rank]
    assert log(gi) < N_COL_GROUPS
    key = group_key[gi]
    if rank != 0:
        assert log(prev_key / key * INV_GEN) < RANK_KEY_BOUND
    group_base[gi] = g_total
    g_total *= group_size[gi]
    prev_key = key
col_off_g = HeapBuf(N_COMMITTED_COLS)
for gi in unroll(0, N_COL_GROUPS):
    c0 = COL_GROUP_START[gi]
    step = g_squares[kb[COL_KAPPA_SRC[c0]] * GEN ** COL_KAPPA_ADJ[c0]]
    off = group_base[GEN ** gi]
    for c in unroll(c0, COL_GROUP_START[gi + 1]):
        col_off_g[GEN ** c] = off
        if const(c + 1 != COL_GROUP_START[gi + 1]):
            off *= step
return g_total, col_off_g
```

The slice `group_order[0:N_COL_GROUPS]` is a typed `HeapBuf` slice, its span checked by a proof;
a factor `GEN ** 0` or `INV_GEN ** 0` is the identity the zkDSL drops. -/
def certifyPlacement : GFn where
  name := "certify_placement"
  arity := 2
  rets := 2
  body ps := do
    let kbase : Word := ⟨ps[0]!⟩
    let gsq : Word := ⟨ps[1]!⟩
    let kb ← B.stackBuf (N_TABLES + 2)
    (List.range (N_TABLES + 2)).forM fun i => B.loadInto (⟨kb[i]!⟩ : Word) kbase i
    let gk ← B.heap N_COL_GROUPS
    let gs ← B.heap N_COL_GROUPS
    (List.range N_COL_GROUPS).forM fun gi => do
      let c0 := COL_GROUP_START gi
      let src : Word := ⟨kb[COL_KAPPA_SRC c0]!⟩
      let adj := COL_KAPPA_ADJ c0
      let kg ← if adj = 0 then pure src else do
        let c ← B.const (gpowE adj)
        B.mul src c
      discard <| B.rangeCheck kg SIZE_BITS
      let v ← if c0 = 0 then rankKey gsq kg else do
        let rk ← rankKey gsq kg
        let c ← B.const (fieldPow (litField INV_GEN) c0)
        B.mul rk c
      B.store gk.p gi v
      let p ← B.mul gsq kg
      let l ← B.load p 0
      let w ← B.pow l (COL_GROUP_START (gi + 1) - c0)
      B.store gs.p gi w
    let go ← B.heap N_COL_GROUPS
    B.witness "col_group_order" (← go.slice 0 N_COL_GROUPS (by omega))
    let gb ← B.heap N_COL_GROUPS
    let (total, _) ← (List.range N_COL_GROUPS).foldlM
      (init := ((none : Option Word), (default : Word)))
      fun (total, prev) rank => do
        let gi ← B.load go.p rank
        discard <| B.rangeCheck gi N_COL_GROUPS
        let kp ← B.mul gk.p gi
        let key ← B.load kp 0
        if rank ≠ 0 then
          let k ← B.const (gpowE (RANK_KEY_BOUND - 1))
          let pk ← B.use prev
          let q ← B.fdiv pk key
          let c ← B.const (litField INV_GEN)
          let m ← B.mul q c
          discard <| B.rangeCheckK m k
        let v ← match total with
          | none => B.const (gpowE 0)
          | some t => pure t
        let bp ← B.mul gb.p gi
        B.store bp 0 v
        let sp ← B.mul gs.p gi
        let size ← B.load sp 0
        let total' ← match total with
          | none => pure size
          | some t => B.mul t size
        return (some total', key)
    let cog ← B.heap N_COMMITTED_COLS
    (List.range N_COL_GROUPS).forM fun gi => do
      let c0 := COL_GROUP_START gi
      let p ← B.mul gsq (⟨kb[COL_KAPPA_SRC c0]!⟩ : Word)
      let step ← B.load p (COL_KAPPA_ADJ c0)
      let off0 ← B.load gb.p gi
      discard <| (List.range' c0 (COL_GROUP_START (gi + 1) - c0)).foldlM (init := off0)
        fun off c => do
          B.store cog.p c off
          if c + 1 ≠ COL_GROUP_START (gi + 1) then B.mul off step else pure off
    return [.v (total.getD default).v, .v cog.p.v]

/-! ## `list_split` -/

/-- `list_split(n_g)`:

```
split = StackBuf(3)
hint_witness(split, "signers_split")
bigs = split[0]
groups = split[1]
rest = split[2]
assert log(rest) < CLAIM_GROUP
assert log(groups) < BIG_GROUPS
assert_gpow(bigs)
assert bigs ** CLAIM_BIG * groups ** CLAIM_GROUP * rest == n_g
return bigs, groups, rest
```
-/
def listSplit : GFn where
  name := "list_split"
  arity := 1
  rets := 3
  body ps := do
    let n : Word := ⟨ps[0]!⟩
    let split ← B.stackBuf 3
    B.witness "signers_split" (.stack split)
    let bigs : Word := ⟨split[0]!⟩
    let groups : Word := ⟨split[1]!⟩
    let rest : Word := ⟨split[2]!⟩
    discard <| B.rangeCheck rest CLAIM_GROUP
    discard <| B.rangeCheck groups BIG_GROUPS
    discard <| B.assertGpow bigs
    let pb ← B.pow bigs CLAIM_BIG
    let pg ← B.pow groups CLAIM_GROUP
    let m ← B.mul pb pg
    let t ← B.mul m rest
    B.assertEq t n
    return [.v bigs.v, .v groups.v, .v rest.v]

end
end LeanVM.Dsl.Guest
