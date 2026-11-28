/-
  LeanVM.Dsl.Gen.InnerproofVerification

  The guest's section `InnerproofVerification`, translated.
-/

module

public import LeanVM.Dsl.Gen.Inline

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

set_option linter.unusedVariables false in
/-- `verify_bus_gkr` (`guests/lean_ethereum.py`, line 1881):

```
def verify_bus_gkr(fs0, fs1, fs2, fs3, fs4, cursor, g_bus_mu, zeta, tabs):
    # ONE GKR grand product over the N_GKR_TREES trees (push, pull, then count), batched by powers of a combiner. Push and pull have
    # equal depth (matched blocks) and the count tree is padded with identity leaves
    # up to it (product unchanged), so a single sumcheck serves them all. Radix four
    # contracts two binary levels per layer, each batched by a fresh combiner drawn
    # after a grind. All the trees reduce to the one shared point `zeta`, which this
    # fills, returning their leaf values with the walked Fiat-Shamir state and stream
    # cursor. The root-most layer, which has no rounds and finds the roots waiting in
    # the sponge, runs on its own: a binary layer for an odd depth, else a radix-four
    # one. It is never the last, the depth being at least BUS_MIN_MU (`verify_sub`).
    assert log(g_bus_mu) < COUNT_BITS
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    # Push and pull's one root, then the count's.
    vals = StackBuf(N_GKR_TREES)
    root, cursor = fs_next(rate, 0, cursor)
    vals[PUSH_SIDE] = root
    vals[PULL_SIDE] = root
    root_count, cursor = fs_next(rate, 1, cursor)
    vals[COUNT_SIDE] = root_count
    assert root_count != 0  # count-tree root nonzero: no read count self-cancels
    sp, lam, cursor = fs_grind_squeeze(sp, rate, 2, cursor, tabs, GKR_COMBINER_GRIND_BITS)
    claim = gkr_combine(vals, lam)
    # k % 4 and its carry into k // 4 as layer k becomes k + 1, by g^(k % 4).
    k_mod_next = HeapBuf(8)
    for r in unroll(0, 4):
        k_mod_next[GEN ** r] = GEN ** ((r + 1) % 4)
        k_mod_next[GEN ** (4 + r)] = GEN ** ((r + 1) // 4)
    # Past the root-most layer, (depth - 1) // 2 radix-four layers; and g exactly when
    # the depth is odd.
    loop_bounds = HeapBuf(COUNT_BITS)
    depth_odd = HeapBuf(COUNT_BITS)
    loop_bounds[GEN ** 0] = GEN ** 0
    depth_odd[GEN ** 0] = GEN ** 0
    for depth in unroll(1, COUNT_BITS):
        loop_bounds[GEN ** depth] = GEN ** ((depth - 1) // 2)
        depth_odd[GEN ** depth] = GEN ** (depth % 2)
    # The round records' extent: radix-four layer k past the root runs 2k + odd rounds,
    # its records filling 2k + odd + 1 positions from 0, so n_quads = (depth - 1) // 2
    # layers fill n_quads^2 + n_quads + n_quads (1 - odd), ROUND_SLOTS cells each.
    rounds_len = HeapBuf(COUNT_BITS)
    rounds_len[GEN ** 0] = GEN ** ROUND_SLOTS
    for depth in unroll(1, COUNT_BITS):
        n_q = (depth - 1) // 2
        rounds_len[GEN ** depth] = GEN ** (ROUND_SLOTS * (n_q * n_q + n_q + n_q * (1 - depth % 2)))
    n_quads = loop_bounds[g_bus_mu]
    # A layer record per radix-four layer, the root's at 0; a point row per layer past
    # the root's, MU_CAP apart, the last holding all mu coordinates.
    layers = HeapBuf((n_quads * GEN) ** LAYER_SLOTS)
    rounds = HeapBuf(rounds_len[g_bus_mu])
    gkr_pts = HeapBuf((n_quads * GEN ** 2) ** MU_CAP)
    odd_g = depth_odd[g_bus_mu]
    if const(GKR_Y_GRIND_BITS != GKR_Y_LAST_GRIND_BITS):
        # g^1 at the last layer, whose start leaves two binary levels, else g^0.
        last_layer = HeapBuf(COUNT_BITS)
        for depth in unroll(0, COUNT_BITS):
            if const(depth == 2):
                last_layer[GEN ** depth] = GEN
            else:
                last_layer[GEN ** depth] = GEN ** 0
    nextrow = gkr_pts * GEN ** MU_CAP
    if odd_g != 1:
        # The binary root layer: two children a tree, y one coordinate.
        evals = StackBuf(2 * N_GKR_TREES)
        sp, rate, cursor = gkr_children(sp, cursor, evals, 2)
        gkr_product_check(evals, lam, claim, 2)
        sp, c0, cursor = fs_grind_squeeze(sp, rate, (2 * N_GKR_TREES + 3) % 4 + 1, cursor, tabs, GKR_Y1_GRIND_BITS)
        nextrow[GEN ** 0] = c0
        nxt = layers
        fs_store(nxt, LAYER_FS, 1, sp)
        nxt[GEN ** LAYER_CURSOR] = cursor
        for t in unroll(0, N_GKR_TREES):
            nxt[GEN ** (LAYER_VALS + t)] = evals[2 * t] + c0 * (evals[2 * t] + evals[2 * t + 1])
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = GEN ** 0
        nxt[GEN ** LAYER_HALF] = GEN ** 0
        nxt[GEN ** LAYER_PARITY] = GEN ** 0
    else:
        # The radix-four root layer: four children a tree, y two coordinates.
        evals = StackBuf(4 * N_GKR_TREES)
        sp, rate, cursor = gkr_children(sp, cursor, evals, 4)
        gkr_product_check(evals, lam, claim, 4)
        sp, c0, cursor = fs_grind_squeeze(sp, rate, (4 * N_GKR_TREES + 3) % 4 + 1, cursor, tabs, GKR_Y_GRIND_BITS)
        no_rate = StackBuf(8)
        sp, c1 = squeeze(sp, no_rate, 0)
        nextrow[GEN ** 0] = c0
        nextrow[GEN ** 1] = c1
        nxt = layers
        fs_store(nxt, LAYER_FS, 1, sp)
        nxt[GEN ** LAYER_CURSOR] = cursor
        for t in unroll(0, N_GKR_TREES):
            lo = evals[4 * t] + c0 * (evals[4 * t] + evals[4 * t + 1])
            hi = evals[4 * t + 2] + c0 * (evals[4 * t + 2] + evals[4 * t + 3])
            nxt[GEN ** (LAYER_VALS + t)] = lo + c1 * (lo + hi)
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = GEN ** 0
        nxt[GEN ** LAYER_HALF] = GEN ** 0
        nxt[GEN ** LAYER_PARITY] = GEN
    # Radix-four layer k (from 1 for an even depth) sits at binary layer 2k + odd and runs
    # that many rounds; its record is the k-th.
    start_g = GEN ** 2 / odd_g
    for x_pair in mul_range(1, n_quads):
        sq = x_pair * x_pair
        x_layer = sq * start_g
        layer = layers * x_pair ** LAYER_SLOTS
        layer_cap = fs_load(layer, LAYER_FS, 1)
        layer_rate = StackBuf(8)
        layer_sp, layer_lam, layer_cur = fs_grind_squeeze(layer_cap, layer_rate, 0, layer[GEN ** LAYER_CURSOR], tabs, GKR_COMBINER_GRIND_BITS)
        layer_vals = StackBuf(N_GKR_TREES)
        for t in unroll(0, N_GKR_TREES):
            layer_vals[t] = layer[GEN ** (LAYER_VALS + t)]
        point_row = layer[GEN ** LAYER_ROW]
        round_pos = layer[GEN ** LAYER_POS]  # g^(ROUND_SLOTS pos)
        nextrow = point_row * GEN ** MU_CAP
        # Round i's record is the ROUND_SLOTS cells from rounds * g^(ROUND_SLOTS i).
        head = rounds * round_pos
        fs_store(head, ROUND_FS, 1, layer_sp)
        head[GEN ** ROUND_CURSOR] = layer_cur
        head[GEN ** ROUND_CLAIM] = gkr_combine(layer_vals, layer_lam)
        # 2k rounds, or 2k + 1 when the depth is odd: eight a loop step, the state
        # between them staying in the frame, then 2 (k % 4), then the odd one.
        half = layer[GEN ** LAYER_HALF]
        parity = layer[GEN ** LAYER_PARITY]
        for x8 in mul_range(1, half):
            step = x8 ** 8
            rd = head * step ** ROUND_SLOTS
            pt = point_row * step
            round_sp = fs_load(rd, ROUND_FS, 1)
            cur = rd[GEN ** ROUND_CURSOR]
            claim = rd[GEN ** ROUND_CLAIM]
            for q in unroll(0, 8):
                # As in gkr_rounds.
                rate = StackBuf(8)
                c1, cur = fs_next(rate, 0, cur)
                c2, cur = fs_next(rate, 1, cur)
                c3, cur = fs_next(rate, 2, cur)
                c4, cur = fs_next(rate, 3, cur)
                round_sp, rk, cur = fs_grind_squeeze(round_sp, rate, 4, cur, tabs, ROUND5_GRIND_BITS)
                c0 = claim + pt[GEN ** q] * (c1 + c2 + c3 + c4)
                pt[GEN ** (MU_CAP + 2 + q)] = rk  # nextrow[round * g^2]
                claim = c0 + rk * (c1 + rk * (c2 + rk * (c3 + rk * c4)))
            rd_next = rd * GEN ** (8 * ROUND_SLOTS)
            fs_store(rd_next, ROUND_FS, 1, round_sp)
            rd_next[GEN ** ROUND_CURSOR] = cur
            rd_next[GEN ** ROUND_CLAIM] = claim
        octet = half ** 8
        rem_head = head * octet ** ROUND_SLOTS
        rem_row = point_row * octet
        done = match(log(parity), range(0, 4), lambda r: gkr_rounds(rem_head, rem_row, tabs, 2 * r))
        if odd_g != 1:
            done = gkr_rounds(head * sq ** ROUND_SLOTS, point_row * sq, tabs, 1)
        layer_span = x_layer ** ROUND_SLOTS
        tail = head * layer_span
        tail_sp = fs_load(tail, ROUND_FS, 1)
        tcur = tail[GEN ** ROUND_CURSOR]
        evals = StackBuf(4 * N_GKR_TREES)  # the four children of each tree, in tree order
        tail_sp, rate, tcur = gkr_children(tail_sp, tcur, evals, 4)
        gkr_product_check(evals, layer_lam, tail[GEN ** ROUND_CLAIM], 4)
        # y's grind: the last layer's coordinates are also zeta's, which the table
        # sumcheck's zerocheck reads, so its numerator doubles.
        if const(GKR_Y_GRIND_BITS == GKR_Y_LAST_GRIND_BITS):
            tail_sp, c0, tcur = fs_grind_squeeze(tail_sp, rate, (4 * N_GKR_TREES + 3) % 4 + 1, tcur, tabs, GKR_Y_GRIND_BITS)
        else:
            y_sp = StackBuf(KECCAK_STATE)
            y_cur = StackBuf(1)
            done = match(log(last_layer[g_bus_mu / x_layer]), range(0, 2), lambda last: gkr_y_grind(y_sp, y_cur, tail_sp, rate, tcur, tabs, last))  # a match needs a target
            tail_sp = y_sp
            c0 = y_sp[0]
            tcur = y_cur[0]
        no_rate = StackBuf(8)
        tail_sp, c1 = squeeze(tail_sp, no_rate, 0)
        nextrow[GEN ** 0] = c0
        nextrow[GEN ** 1] = c1
        nxt = layer * GEN ** LAYER_SLOTS
        fs_store(nxt, LAYER_FS, 1, tail_sp)
        nxt[GEN ** LAYER_CURSOR] = tcur
        for t in unroll(0, N_GKR_TREES):
            lo = evals[4 * t] + c0 * (evals[4 * t] + evals[4 * t + 1])
            hi = evals[4 * t + 2] + c0 * (evals[4 * t + 2] + evals[4 * t + 3])
            nxt[GEN ** (LAYER_VALS + t)] = lo + c1 * (lo + hi)
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = round_pos * layer_span * GEN ** ROUND_SLOTS
        nxt[GEN ** LAYER_HALF] = half * k_mod_next[GEN ** 4 * parity]
        nxt[GEN ** LAYER_PARITY] = k_mod_next[parity]
    last = layers * n_quads ** LAYER_SLOTS
    cursor = last[GEN ** LAYER_CURSOR]
    final_point_row = last[GEN ** LAYER_ROW]
    for xt in mul_range(1, g_bus_mu):
        zeta[xt] = final_point_row[xt]  # the ONE shared point
    leaves = HeapBuf(N_GKR_TREES)
    for t in unroll(0, N_GKR_TREES):
        leaves[GEN ** t] = last[GEN ** (LAYER_VALS + t)]
    return last[GEN ** LAYER_FS], last[GEN ** (LAYER_FS + 1)], last[GEN ** (LAYER_FS + 2)], last[GEN ** (LAYER_FS + 3)], last[GEN ** (LAYER_FS + 4)], cursor, leaves
```
-/
def verifyBusGkr : GFn where
  name := "verify_bus_gkr"
  arity := 9
  rets := 7
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let cursor := cellOf ps 5
    let gBusMu := cellOf ps 6
    let zeta := cellOf ps 7
    let tabs := cellOf ps 8
    let _ ← B.rangeCheck gBusMu COUNT_BITS
    let sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let rate ← B.stackBuf 8
    let vals ← B.stackBuf N_GKR_TREES
    let (t0, t1) ← fsNext rate 0 cursor
    let root := t0
    let cursor_ptr : Shifted := t1
    B.copy (cellOf vals PUSH_SIDE) root
    B.copy (cellOf vals PULL_SIDE) root
    let (t2, t3) ← fsNext_2 rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let rootCount := t2
    let cursor_ptr : Shifted := t3
    B.copy (cellOf vals COUNT_SIDE) rootCount
    B.assertNe rootCount (← B.const 0)
    let (t4, t5, t6) ← fsGrindSqueeze sp rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs GKR_COMBINER_GRIND_BITS
    let sp := t4
    let lam := t5
    let cursor_ptr : Shifted := t6
    let claim ← gkrCombine vals lam
    let kModNext ← B.heapBuf 8
    for r_k in [0:4] do
      B.store kModNext r_k (← B.const (gpowE ((r_k + 1) % 4)))
      B.store kModNext (4 + r_k) (← B.const (gpowE ((r_k + 1) / 4)))
    let loopBounds ← B.heapBuf COUNT_BITS
    let depthOdd ← B.heapBuf COUNT_BITS
    B.store loopBounds 0 (← B.const (gpowE 0))
    B.store depthOdd 0 (← B.const (gpowE 0))
    for depth_k in [1:COUNT_BITS] do
      B.store loopBounds depth_k (← B.const (gpowE ((depth_k - 1) / 2)))
      B.store depthOdd depth_k (← B.const (gpowE (depth_k % 2)))
    let roundsLen ← B.heapBuf COUNT_BITS
    B.store roundsLen 0 (← B.const (gpowE ROUND_SLOTS))
    for depth_k in [1:COUNT_BITS] do
      let nQ := (depth_k - 1) / 2
      B.store roundsLen depth_k (← B.const (gpowE (ROUND_SLOTS * (((nQ * nQ) + nQ) + (nQ * (1 - (depth_k % 2)))))))
    let nQuads ← B.load (← B.mul loopBounds gBusMu) 0
    let layers ← B.heapBufDyn (← B.pow (← B.shifted nQuads 1) LAYER_SLOTS)
    let rounds ← B.heapBufDyn (← B.load (← B.mul roundsLen gBusMu) 0)
    let gkrPts ← B.heapBufDyn (← B.pow (← B.shifted nQuads 2) MU_CAP)
    let oddG ← B.load (← B.mul depthOdd gBusMu) 0
    if 0 ≠ 0 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    let nextrow : Shifted := ⟨gkrPts, MU_CAP⟩
    let t7 ← B.add oddG (← B.const 1)
    let _ ← B.ite t7
      (do
        let evals ← B.stackBuf 12
        let (t8, t9, t10) ← gkrChildren sp (⟨cursor_ptr.base, cursor_ptr.exp⟩) evals 4
        let sp := t8
        let rate := t9
        let cursor_ptr : Shifted := t10
        gkrProductCheck evals lam claim 4
        let (t11, t12, t13) ← fsGrindSqueeze sp rate ((((4 * 3) + 3) % 4) + 1) (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs GKR_Y_GRIND_BITS
        let sp := t11
        let c0 := t12
        let cursor_ptr : Shifted := t13
        let noRate ← B.stackBuf 8
        let (t14, t15) ← squeeze sp noRate 0
        let sp := t14
        let c1 := t15
        B.store nextrow.base nextrow.exp c0
        B.store nextrow.base (nextrow.exp + 1) c1
        let nxt := layers
        fsStore_2 nxt LAYER_FS 1 sp
        B.store nxt LAYER_CURSOR (← B.shifted cursor_ptr.base cursor_ptr.exp)
        let mut lo : Word := default
        let mut hi : Word := default
        for t_k in [0:N_GKR_TREES] do
          lo ← B.add (cellOf evals (4 * t_k)) (← B.mul c0 (← B.add (cellOf evals (4 * t_k)) (cellOf evals ((4 * t_k) + 1))))
          hi ← B.add (cellOf evals ((4 * t_k) + 2)) (← B.mul c0 (← B.add (cellOf evals ((4 * t_k) + 2)) (cellOf evals ((4 * t_k) + 3))))
          B.store nxt (LAYER_VALS + t_k) (← B.add lo (← B.mul c1 (← B.add lo hi)))
        B.store nxt LAYER_ROW (← B.shifted nextrow.base nextrow.exp)
        B.store nxt LAYER_POS (← B.const (gpowE 0))
        B.store nxt LAYER_HALF (← B.const (gpowE 0))
        B.store nxt LAYER_PARITY (← B.const (gpowE 1)))
      (do
        let evals ← B.stackBuf 6
        let (t16, t17, t18) ← gkrChildren sp (⟨cursor_ptr.base, cursor_ptr.exp⟩) evals 2
        let sp := t16
        let rate := t17
        let cursor_ptr : Shifted := t18
        gkrProductCheck_2 evals lam claim 2
        let (t19, t20, t21) ← fsGrindSqueeze sp rate ((((2 * 3) + 3) % 4) + 1) (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs GKR_Y1_GRIND_BITS
        let sp := t19
        let c0 := t20
        let cursor_ptr : Shifted := t21
        B.store nextrow.base nextrow.exp c0
        let nxt := layers
        fsStore_2 nxt LAYER_FS 1 sp
        B.store nxt LAYER_CURSOR (← B.shifted cursor_ptr.base cursor_ptr.exp)
        for t_k in [0:N_GKR_TREES] do
          B.store nxt (LAYER_VALS + t_k) (← B.add (cellOf evals (2 * t_k)) (← B.mul c0 (← B.add (cellOf evals (2 * t_k)) (cellOf evals ((2 * t_k) + 1)))))
        B.store nxt LAYER_ROW (← B.shifted nextrow.base nextrow.exp)
        B.store nxt LAYER_POS (← B.const (gpowE 0))
        B.store nxt LAYER_HALF (← B.const (gpowE 0))
        B.store nxt LAYER_PARITY (← B.const (gpowE 0)))
    let startG ← B.fdiv (← B.const (gpowE 2)) oddG
    B.loopRtF 0 (pure nQuads) 8 (pure ([startG.v, layers.v, tabs.v, rounds.v, claim.v, oddG.v, gBusMu.v, kModNext.v])) fun xPair caps => do
      let startG := cellOf caps 0
      let layers := cellOf caps 1
      let tabs := cellOf caps 2
      let rounds := cellOf caps 3
      let claim := cellOf caps 4
      let oddG := cellOf caps 5
      let gBusMu := cellOf caps 6
      let kModNext := cellOf caps 7
      let sq ← B.mul xPair xPair
      let xLayer ← B.mul sq startG
      let layer ← B.mul layers (← B.pow xPair LAYER_SLOTS)
      let layerCap ← fsLoad layer LAYER_FS 1
      let layerRate ← B.stackBuf 8
      let (t0, t1, t2) ← fsGrindSqueeze_2 layerCap layerRate 0 (← B.load layer LAYER_CURSOR) tabs 0
      let layerSp := t0
      let layerLam := t1
      let layerCur := t2
      let layerVals ← B.stackBuf N_GKR_TREES
      for t_k in [0:N_GKR_TREES] do
        B.loadInto (cellOf layerVals t_k) layer (LAYER_VALS + t_k)
      let pointRow ← B.load layer LAYER_ROW
      let roundPos ← B.load layer LAYER_POS
      let nextrow : Shifted := ⟨pointRow, MU_CAP⟩
      let head ← B.mul rounds roundPos
      fsStore_2 head ROUND_FS 1 layerSp
      B.store head ROUND_CURSOR layerCur
      let t3 ← gkrCombine layerVals layerLam
      B.store head ROUND_CLAIM t3
      let half ← B.load layer LAYER_HALF
      let parity ← B.load layer LAYER_PARITY
      B.loopRtF 0 (pure half) 3 (pure ([head.v, pointRow.v, tabs.v])) fun x8 caps => do
        let head := cellOf caps 0
        let pointRow := cellOf caps 1
        let tabs := cellOf caps 2
        let step ← B.pow x8 8
        let rd ← B.mul head (← B.pow step ROUND_SLOTS)
        let pt ← B.mul pointRow step
        let mut roundSp ← fsLoad rd ROUND_FS 1
        let cur ← B.load rd ROUND_CURSOR
        let mut claim ← B.load rd ROUND_CLAIM
        let mut cur_ptr : Shifted := default
        let q_k := 0
        let rate ← B.stackBuf 8
        let (t0, t1) ← fsNext rate 0 cur
        let c1 := t0
        cur_ptr := t1
        let (t2, t3) ← fsNext_2 rate 1 (⟨cur_ptr.base, cur_ptr.exp⟩)
        let c2 := t2
        cur_ptr := t3
        let (t4, t5) ← fsNext_2 rate 2 (⟨cur_ptr.base, cur_ptr.exp⟩)
        let c3 := t4
        cur_ptr := t5
        let (t6, t7) ← fsNext_2 rate 3 (⟨cur_ptr.base, cur_ptr.exp⟩)
        let c4 := t6
        cur_ptr := t7
        let (t8, t9, t10) ← fsGrindSqueeze roundSp rate 4 (⟨cur_ptr.base, cur_ptr.exp⟩) tabs ROUND5_GRIND_BITS
        roundSp := t8
        let rk := t9
        cur_ptr := t10
        let c0 ← B.add claim (← B.mul (← B.load pt q_k) (← B.add (← B.add (← B.add c1 c2) c3) c4))
        B.store pt ((MU_CAP + 2) + q_k) rk
        claim ← B.add c0 (← B.mul rk (← B.add c1 (← B.mul rk (← B.add c2 (← B.mul rk (← B.add c3 (← B.mul rk c4)))))))
        for q_k in [1:8] do
          let rate ← B.stackBuf 8
          let (t0, t1) ← fsNext_2 rate 0 (⟨cur_ptr.base, cur_ptr.exp⟩)
          let c1 := t0
          cur_ptr := t1
          let (t2, t3) ← fsNext_2 rate 1 (⟨cur_ptr.base, cur_ptr.exp⟩)
          let c2 := t2
          cur_ptr := t3
          let (t4, t5) ← fsNext_2 rate 2 (⟨cur_ptr.base, cur_ptr.exp⟩)
          let c3 := t4
          cur_ptr := t5
          let (t6, t7) ← fsNext_2 rate 3 (⟨cur_ptr.base, cur_ptr.exp⟩)
          let c4 := t6
          cur_ptr := t7
          let (t8, t9, t10) ← fsGrindSqueeze roundSp rate 4 (⟨cur_ptr.base, cur_ptr.exp⟩) tabs ROUND5_GRIND_BITS
          roundSp := t8
          let rk := t9
          cur_ptr := t10
          let c0 ← B.add claim (← B.mul (← B.load pt q_k) (← B.add (← B.add (← B.add c1 c2) c3) c4))
          B.store pt ((MU_CAP + 2) + q_k) rk
          claim ← B.add c0 (← B.mul rk (← B.add c1 (← B.mul rk (← B.add c2 (← B.mul rk (← B.add c3 (← B.mul rk c4)))))))
        let rdNext : Shifted := ⟨rd, 56⟩
        fsStore (⟨rdNext.base, rdNext.exp⟩) ROUND_FS 1 roundSp
        B.store rdNext.base (rdNext.exp + ROUND_CURSOR) (← B.shifted cur_ptr.base cur_ptr.exp)
        B.store rdNext.base (rdNext.exp + ROUND_CLAIM) claim
      let octet ← B.pow half 8
      let remHead ← B.mul head (← B.pow octet ROUND_SLOTS)
      let remRow ← B.mul pointRow octet
      let t4 ← B.targets [none]
      B.dispatchInto parity ((List.range 4).map fun arm => (instName "gkr_rounds" [.L (2 * arm)])) [remHead.v, remRow.v, tabs.v] t4
      let done := cellOf t4 0
      let t5 ← B.add oddG (← B.const 1)
      let _ ← B.ite t5
        (do
          pure ())
        (do
          let done ← call1 (instName "gkr_rounds" [.L 1]) [(← B.mul head (← B.pow sq ROUND_SLOTS)).v, (← B.mul pointRow sq).v, tabs.v]
          pure ())
      let layerSpan ← B.pow xLayer ROUND_SLOTS
      let tail ← B.mul head layerSpan
      let tailSp ← fsLoad tail ROUND_FS 1
      let tcur ← B.load tail ROUND_CURSOR
      let evals ← B.stackBuf 12
      let (t6, t7, t8) ← gkrChildren_2 tailSp tcur evals 4
      let mut tailSp := t6
      let rate := t7
      let mut tcur_ptr : Shifted := t8
      gkrProductCheck evals layerLam (← B.load tail ROUND_CLAIM) 4
      let mut c0 : Word := default
      if 0 = 0 then
        let (t9, t10, t11) ← fsGrindSqueeze tailSp rate ((((4 * 3) + 3) % 4) + 1) (⟨tcur_ptr.base, tcur_ptr.exp⟩) tabs GKR_Y_GRIND_BITS
        tailSp := t9
        c0 := t10
        tcur_ptr := t11
      else
        pure () -- no use of this definition takes this branch
      let noRate ← B.stackBuf 8
      let (t12, t13) ← squeeze tailSp noRate 0
      tailSp := t12
      let c1 := t13
      B.store nextrow.base nextrow.exp c0
      B.store nextrow.base (nextrow.exp + 1) c1
      let nxt : Shifted := ⟨layer, LAYER_SLOTS⟩
      fsStore (⟨nxt.base, nxt.exp⟩) LAYER_FS 1 tailSp
      B.store nxt.base (nxt.exp + LAYER_CURSOR) (← B.shifted tcur_ptr.base tcur_ptr.exp)
      for t_k in [0:N_GKR_TREES] do
        let lo ← B.add (cellOf evals (4 * t_k)) (← B.mul c0 (← B.add (cellOf evals (4 * t_k)) (cellOf evals ((4 * t_k) + 1))))
        let hi ← B.add (cellOf evals ((4 * t_k) + 2)) (← B.mul c0 (← B.add (cellOf evals ((4 * t_k) + 2)) (cellOf evals ((4 * t_k) + 3))))
        B.store nxt.base (nxt.exp + (LAYER_VALS + t_k)) (← B.add lo (← B.mul c1 (← B.add lo hi)))
      B.store nxt.base (nxt.exp + LAYER_ROW) (← B.shifted nextrow.base nextrow.exp)
      B.store nxt.base (nxt.exp + LAYER_POS) (← B.mul (← B.mul roundPos layerSpan) (← B.const (gpowE ROUND_SLOTS)))
      B.store nxt.base (nxt.exp + LAYER_HALF) (← B.mul half (← B.load (← B.mul kModNext parity) 4))
      B.store nxt.base (nxt.exp + LAYER_PARITY) (← B.load (← B.mul kModNext parity) 0)
    let last ← B.mul layers (← B.pow nQuads LAYER_SLOTS)
    let cursor ← B.load last LAYER_CURSOR
    let finalPointRow ← B.load last LAYER_ROW
    B.loopRtF 0 (pure gBusMu) 2 (pure ([zeta.v, finalPointRow.v])) fun xt caps => do
      let zeta := cellOf caps 0
      let finalPointRow := cellOf caps 1
      let t0 ← B.load (← B.mul finalPointRow xt) 0
      B.store (← B.mul zeta xt) 0 t0
    let leaves ← B.heapBuf N_GKR_TREES
    for t_k in [0:N_GKR_TREES] do
      B.store leaves t_k (← B.load last (LAYER_VALS + t_k))
    return [.load last.v LAYER_FS] ++ [.load last.v 1] ++ [.load last.v 2] ++ [.load last.v 3] ++ [.load last.v 4] ++ [.v cursor.v] ++ [.v leaves.v]

set_option linter.unusedVariables false in
/-- `selector_run_nibbles` (`guests/lean_ethereum.py`, line 2128):

```
def selector_run_nibbles(len_g):
    # A selector run of length n = 4q + r, r < 4, split into its q full nibbles
    # (coordinates 4j..4j+3 past κ) and a last one r wide. The split is advice,
    # each bit pinned and the whole tied back to len_g. Returns g^q.
    nb = StackBuf(6)
    hint_decompose_bits_exponent(nb, len_g, 6)
    for k in unroll(0, 6):
        b = nb[k]
        nb[k] = b * b
    r_g = (1 + nb[0] * (1 + GEN)) * (1 + nb[1] * (1 + GEN ** 2))
    q_g = GEN ** 0
    for k in unroll(2, 6):
        q_g *= 1 + nb[k] * (1 + GEN ** (2 ** (k - 2)))
    q4 = q_g ** 4
    assert q4 * r_g == len_g
    return q_g
```
-/
def selectorRunNibbles : GFn where
  name := "selector_run_nibbles"
  arity := 1
  rets := 1
  body ps := do
    let lenG := cellOf ps 0
    let nb ← B.stackBuf 6
    B.hintBitsExpTo (.stack (nb.take 6)) lenG 6
    for k_k in [0:6] do
      let b := cellOf nb k_k
      B.mulInto (cellOf nb k_k) b b
    let rG ← B.mul (← B.add (← B.const 1) (← B.mul (cellOf nb 0) (← B.const (1 + (gpowE 1))))) (← B.add (← B.const 1) (← B.mul (cellOf nb 1) (← B.const (1 + (gpowE 2)))))
    let qG : GPow := ⟨0⟩
    let mut qG_word : Word := default
    let k_k := 2
    qG_word ← B.add (← B.const 1) (← B.mul (cellOf nb k_k) (← B.const (1 + (gpowE (2 ^ (k_k - 2))))))
    for k_k in [3:6] do
      qG_word ← B.mul qG_word (← B.add (← B.const 1) (← B.mul (cellOf nb k_k) (← B.const (1 + (gpowE (2 ^ (k_k - 2)))))))
    let q4 ← B.pow qG_word 4
    B.assertEq (← B.mul q4 rG) lenG
    return [.v qG_word.v]

set_option linter.unusedVariables false in
/-- `shared_selector_tables` (`guests/lean_ethereum.py`, line 2146):

```
def shared_selector_tables(eq_tab, g_tab, zeta_hi, zeta1_hi, gsq_hi, len_g, q_g):
    # Per nibble j of a selector run of length n = 4q + r split by
    # selector_run_nibbles (q_g = g^q), the eq tables over its low 1..4
    # coordinates and the g-powers of its indices' offset shares, into the
    # caller's tables of q + 1 nibbles, SEL_TAB_EQ_STRIDE and 16 cells a nibble.
    q4 = q_g ** 4
    r_g = len_g / q4
    for xq in mul_range(1, q_g):
        x4 = xq ** 4
        x16 = x4 ** 4
        sel_eq_nibble(eq_tab * x16 * x16, zeta_hi * x4, zeta1_hi * x4, 4)
        sel_g_nibble(g_tab * x16, gsq_hi * x4, 4)
    q16 = q4 ** 4
    # r_g = g^r with r < 4 as a range check: the back end's selector analysis
    # bounds the match's selector by it (it cannot bound a quotient).
    assert log(r_g) < 4
    done = match(log(r_g), range(0, 4), lambda w: sel_partial_nibble(eq_tab * q16 * q16, g_tab * q16, zeta_hi * q4, zeta1_hi * q4, gsq_hi * q4, w))  # a match needs a target
    return
```
-/
def sharedSelectorTables : GFn where
  name := "shared_selector_tables"
  arity := 7
  rets := 0
  body ps := do
    let eqTab := cellOf ps 0
    let gTab := cellOf ps 1
    let zetaHi := cellOf ps 2
    let zeta1Hi := cellOf ps 3
    let gsqHi := cellOf ps 4
    let lenG := cellOf ps 5
    let qG := cellOf ps 6
    let q4 ← B.pow qG 4
    let rG ← B.fdiv lenG q4
    B.loopRtF 0 (pure qG) 5 (pure ([eqTab.v, zetaHi.v, zeta1Hi.v, gTab.v, gsqHi.v])) fun xq caps => do
      let eqTab := cellOf caps 0
      let zetaHi := cellOf caps 1
      let zeta1Hi := cellOf caps 2
      let gTab := cellOf caps 3
      let gsqHi := cellOf caps 4
      let x4 ← B.pow xq 4
      let x16 ← B.pow x4 4
      selEqNibble (← B.mul (← B.mul eqTab x16) x16) (← B.mul zetaHi x4) (← B.mul zeta1Hi x4) 4
      selGNibble (← B.mul gTab x16) (← B.mul gsqHi x4) 4
    let q16 ← B.pow q4 4
    let _ ← B.rangeCheck rG 4
    let t0 ← B.targets [none]
    let t1 ← B.mul (← B.mul eqTab q16) q16
    let t2 ← B.mul gTab q16
    let t3 ← B.mul zetaHi q4
    let t4 ← B.mul zeta1Hi q4
    let t5 ← B.mul gsqHi q4
    B.dispatchInto rG ((List.range 4).map fun arm => (instName "sel_partial_nibble" [.L arm])) [t1.v, t2.v, t3.v, t4.v, t5.v] t0
    let done := cellOf t0 0
    return []

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `verify_tables` (`guests/lean_ethereum.py`, line 2254):

```
def verify_tables(fs0, fs1, fs2, fs3, fs4, cursor, pi_0, pi_1, zeta, g_bus_mu, dims_g, table_rows, g_squares, fp_w, beta, claim_pool, chi, gkr_leaves, tabs, bc_point):
    # Settle the bus against the six tables, in four steps: certify each side's
    # leaf-cube tiling, decompose the sides' GKR leaf values over it, run the ONE
    # table sumcheck they all reduce to, and bind the public input. Pooled claims land
    # in claim_pool, the reduced point in `chi` and the bytecode sumcheck's in
    # `bc_point`; the batch's round count g^n, the bytecode value there (the deferred
    # claim) and the PI point come back.
    #
    # Bus-leaf packing offsets, for the selector certification. Each side's blocks
    # tile its leaf cube, block b at offset_b, and offsets accumulate as
    # g^offset = Π_{earlier} g^(2^κ). The hinted order is certified to be the
    # native one, as certify_placement does for the columns: descending κ, then
    # ascending block index, the guest's per-side block order being the native
    # verifier's (framework blocks, then each table's in table order). The
    # decompose below pins each block's selector bits against this offset, forcing
    # κ-alignment. Pull's blocks mirror push's and share zeta, so only push and
    # count need offsets (pull's slots go unread).
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    kb = StackBuf(N_TABLES + 2)  # kappa_base, in the frame
    kb[0] = 1
    for t in unroll(0, N_TABLES + 1):
        kb[1 + t] = dims_g[GEN ** t]
    # A block group, a run of a side's blocks sharing one kappa source, is consecutive
    # in its side's order, so a hinted order of the groups, certified strictly
    # descending in its rank key (descending κ, then ascending first index: a side's
    # blocks share one base, so the native ascending index), places every block.
    group_side_tab = g_squares * GEN ** SIDE_TAB_AT  # group -> its side (exponent_tables)
    rank_keys = g_squares * GEN ** RANK_KEYS_AT
    group_key = HeapBuf(N_BLOCK_GROUPS)
    group_size = HeapBuf(N_BLOCK_GROUPS)
    group_base = HeapBuf(N_BLOCK_GROUPS)
    group_order = HeapBuf(N_BLOCK_GROUPS)
    hint_witness(group_order[0:N_BLOCK_GROUPS], "block_group_order")
    block_off = StackBuf(N_BLOCKS)  # g^offset per push and count block
    for cert in unroll(0, 2):
        s = COUNT_SIDE * cert  # PUSH_SIDE (0), then COUNT_SIDE (2)
        for gi in unroll(SIDE_GROUP_START[s], SIDE_GROUP_START[s + 1]):
            b0 = BLOCK_GROUP_START[gi]
            kappa_g = kb[BLOCK_KAPPA_SRC[b0]] * GEN ** BLOCK_KAPPA_ADJ[b0]
            group_key[GEN ** gi] = rank_keys[kappa_g] * INV_GEN ** b0
            group_size[GEN ** gi] = g_squares[kappa_g] ** (BLOCK_GROUP_START[gi + 1] - b0)
        g_off = GEN ** 0
        for r in unroll(SIDE_GROUP_START[s], SIDE_GROUP_START[s + 1]):
            gi = group_order[GEN ** r]
            assert log(gi) < N_BLOCK_GROUPS  # a valid group...
            group_side_tab[gi] = s           # ...of THIS side
            key = group_key[gi]
            if r != SIDE_GROUP_START[s]:
                assert log(prev_key / key * INV_GEN) < RANK_KEY_BOUND
            # write-once: a repeat collides (g_off has grown since), so the side's
            # ranks name as many distinct groups of the side as it has, omitting none
            group_base[gi] = g_off
            g_off *= group_size[gi]
            prev_key = key
        for gi in unroll(SIDE_GROUP_START[s], SIDE_GROUP_START[s + 1]):
            b0 = BLOCK_GROUP_START[gi]
            step = g_squares[kb[BLOCK_KAPPA_SRC[b0]] * GEN ** BLOCK_KAPPA_ADJ[b0]]
            block_off[b0] = group_base[GEN ** gi]
            for b in unroll(b0 + 1, BLOCK_GROUP_START[gi + 1]):
                block_off[b] = block_off[b - 1] * step

    # ---- the leaf decomposition (claims pooled; bytecode Public DEFERRED) ----
    # Reconstruct Ṽ₀(ζ) per side and assert it equals the GKR leaf value. The
    # committed-coordinate values ride the stream (observed, pooled); Index
    # coordinates use the factored index MLE; and the program's whole share of a
    # bytecode leaf, its slots being aligned with the tuple, is ONE sum over the
    # slots of the stacked polynomial at ζ_lo, which rides the stream after the
    # framework values and a sumcheck reduces to one evaluation, the deferred claim
    # (doc sec:e2e-bc).
    #
    # Pull's blocks mirror push's (same kappas, same offsets, generator-asserted
    # pairing) and share zeta, so each pull block REUSES its push twin's eq_hi and
    # Index-MLE value instead of recomputing them; its column values are mostly
    # deduped pool reads (COORD_FRESH). The identity check against pull's own GKR
    # claim still binds everything.
    # Each table's padding rows: their weight on a claim at zeta[..tau], dispatched on
    # its hinted log height tau, which this certifies: the least holding its rows, or
    # its floor. A table is at most the stack, so tau has an arm.
    pad_weight = StackBuf(N_TABLES)
    for t in unroll(0, N_TABLES):
        tau_g = kb[2 + t]
        assert log(tau_g) < N_COLUMN_LOGS
        rows = table_rows[GEN ** t]
        pad_weight[t], lead, rest = match(log(tau_g), range(0, N_COLUMN_LOGS), lambda tau: padding_weight(rows, zeta, tau))
        if FLOORS[t] == 0:
            assert lead == 1
            assert rest != 0
        else:
            assert log(tau_g / GEN ** FLOORS[t]) < N_COLUMN_LOGS
            if tau_g != GEN ** FLOORS[t]:
                assert lead == 1
                assert rest != 0
    idxc_tab = HeapBuf(SIZE_BITS)  # INDEX_MLE_FACTORS[t] = 1 + g^(2^t)
    for t in unroll(0, SIZE_BITS):
        idxc_tab[GEN ** t] = INDEX_MLE_FACTORS[t]
    zeta1 = HeapBuf(g_bus_mu)  # 1 + zeta, so an eq factor 1 + b + z is one XOR
    zeta1_done = match(log(g_bus_mu), range(0, SIZE_BITS), lambda n: plus_one_run(zeta1, zeta, n))  # a match needs a target
    # A block sized by table t's tau (kappa source 2 + t, unadjusted) has
    # block_kappa = kappa_base[2 + t] = dims_g[t + 1] (verify_sub), so all of one
    # table's blocks walk the same selector run and read the same tables.
    shared_len = StackBuf(N_TABLES)
    shared_eq = StackBuf(N_TABLES)
    shared_g = StackBuf(N_TABLES)
    for t in unroll(0, N_TABLES):
        tau_g = kb[2 + t]
        shared_len[t] = g_bus_mu / tau_g
        assert log(shared_len[t]) < SIZE_BITS
        # Each table sized to its run, q + 1 nibbles of SEL_TAB_EQ_STRIDE and 16 cells.
        q_g = selector_run_nibbles(shared_len[t])
        g_len = (q_g * GEN) ** 16
        eq_t = HeapBuf(g_len * g_len)
        g_t = HeapBuf(g_len)
        shared_selector_tables(eq_t, g_t, zeta * tau_g, zeta1 * tau_g, g_squares * tau_g, shared_len[t], q_g)
        shared_eq[t] = eq_t
        shared_g[t] = g_t
    block_eq_hi = StackBuf(N_BLOCKS)         # every block's eq_hi, reused below
    block_index_mle = HeapBuf(N_BLOCKS)      # per push block with an Index coord
    # A framework coordinate's value at zeta, and a table coordinate's at the table
    # sumcheck's point (a pull one's less its push twin's), by coordinate index.
    coord_vals = StackBuf(N_COORDS)
    selector_sums = StackBuf(N_GKR_SIDES)    # per side, its blocks' eq_hi summed
    public_eqs = StackBuf(N_GKR_SIDES)       # per side, the eq_hi of its blocks with public slots
    for s in unroll(0, N_GKR_SIDES):
        selector_sum = 0
        public_eq = 0
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            block_has_public = 0
            kappa_g = kb[BLOCK_KAPPA_SRC[b]] * GEN ** BLOCK_KAPPA_ADJ[b]
            # Every certified log is under SIZE_BITS (log_mem below COUNT_BITS, a tau
            # below N_COLUMN_LOGS), so only an adjusted one needs bounding.
            if const(BLOCK_KAPPA_SRC[b] != 0):
                if const(BLOCK_KAPPA_ADJ[b] != 0):
                    assert log(kappa_g) < SIZE_BITS
            if s == PULL_SIDE:
                eq_hi = block_eq_hi[b - SIDE_BLOCK_START[PULL_SIDE]]
            else:
                # eq_hi over the ζ coords above κ against the selector bits, whose
                # run is mu_s − κ = g^mu_s / g^κ long. Selector bits = offset >> κ:
                # advice-decompose the offset and read it shifted by κ. Rebuilding
                # g^offset from those high bits alone (weights g^(2^(κ+k))) and
                # asserting it equals block_off_g pins the bits AND the κ-alignment
                # in one shot; the low κ bit cells are written but never read.
                shared = 0
                if const(BLOCK_KAPPA_SRC[b] // 2 != 0):
                    if const(BLOCK_KAPPA_ADJ[b] == 0):
                        shared = 1
                if const(shared == 1):
                    t = BLOCK_KAPPA_SRC[b] - 2
                    digits = HeapBuf(SEL_TAB_NIBBLES)
                    hint_decompose_digits_exponent(digits, block_off[b], SIZE_BITS, SEL_TAB_NIBBLES, 4, kb[2 + t])
                    len_g = shared_len[t]
                    tab_eq = shared_eq[t]
                    tab_g = shared_g[t]
                    eq_hi, goff = match(log(len_g), range(0, SIZE_BITS), lambda n: block_selector_tab(digits, tab_eq, tab_g, n))
                else:
                    sel_len_g = g_bus_mu / kappa_g  # g^(mu - κ)
                    assert log(sel_len_g) < SIZE_BITS
                    offset_bits = HeapBuf(GEN ** SIZE_BITS)
                    hint_decompose_bits_exponent(offset_bits, block_off[b], SIZE_BITS)
                    sel_bits = offset_bits * kappa_g
                    zeta1_hi = zeta1 * kappa_g
                    idxc_hi = idxc_tab * kappa_g
                    eq_hi, goff = match(log(sel_len_g), range(0, SIZE_BITS), lambda n: block_selector(sel_bits, zeta1_hi, idxc_hi, n))
                assert goff == block_off[b]  # bits == offset >> κ, κ-aligned
            selector_sum += eq_hi
            block_eq_hi[b] = eq_hi
            # A TABLE's block streams no value here: the table sumcheck settles its
            # fingerprint from that table's column evaluations. Only the framework
            # blocks (boundary, memory, bytecode) still decompose.
            if BLOCK_TABLE[b] == NO_TABLE:
                for i in unroll(0, BLOCK_COORD_COUNT[b]):
                    ci = BLOCK_COORD_OFF[b] + i  # a compile-time index, so `ci` costs nothing
                    if COORD_TYPE[ci] == COORD_KIND_CONST:
                        coord_vals[ci] = COORD_CONST[ci]
                    if COORD_TYPE[ci] == COORD_KIND_COL:
                        if COORD_FRESH[ci] == 1:
                            if COORD_FRESH_POS[ci] % 4 == 0:
                                if COORD_FRESH_POS[ci] != 0:
                                    sp = fs_perm(sp, rate, 4)
                                    rate = StackBuf(8)
                            coord_val, cursor = fs_next(rate, COORD_FRESH_POS[ci] % 4, cursor)
                            claim_pool[GEN ** COORD_CLAIM_SLOT[ci]] = coord_val
                        else:
                            coord_val = claim_pool[GEN ** COORD_CLAIM_SLOT[ci]]
                        coord_vals[ci] = coord_val
                    if COORD_TYPE[ci] == COORD_KIND_GCOL:
                        if COORD_FRESH[ci] == 1:
                            if COORD_FRESH_POS[ci] % 4 == 0:
                                if COORD_FRESH_POS[ci] != 0:
                                    sp = fs_perm(sp, rate, 4)
                                    rate = StackBuf(8)
                            rawv, cursor = fs_next(rate, COORD_FRESH_POS[ci] % 4, cursor)
                            claim_pool[GEN ** COORD_CLAIM_SLOT[ci]] = rawv
                        else:
                            rawv = claim_pool[GEN ** COORD_CLAIM_SLOT[ci]]
                        coord_vals[ci] = COORD_CONST[ci] * rawv
                    if COORD_TYPE[ci] == COORD_KIND_INDEX:
                        if s == PULL_SIDE:
                            coord_vals[ci] = block_index_mle[GEN ** (b - SIDE_BLOCK_START[PULL_SIDE])]
                        else:
                            coord_val = match(log(kappa_g), range(0, SIZE_BITS), lambda n: index_mle(zeta, n))
                            coord_vals[ci] = coord_val
                            if s == PUSH_SIDE:
                                block_index_mle[GEN ** b] = coord_val
                    if COORD_TYPE[ci] == COORD_KIND_PUBLIC:
                        # The public slots carry no value of their own here: their
                        # weighted sum IS bc_share, added once per block below
                        # (push and pull share zeta, so both get the same one).
                        coord_vals[ci] = 0
                        block_has_public = 1
                if const(block_has_public == 1):
                    public_eq += eq_hi
        selector_sums[s] = selector_sum
        public_eqs[s] = public_eq

    # ---- the bytecode's share (verifier::bus) ----
    # S = sum_x fp_w[x] P(ζ_lo, x) over the stacked bytecode P's slots x, after the
    # framework values, then a sumcheck over x, low bit first, of degree two: each
    # round sends c0 and c2, and the first round's two join S in the rate.
    bc_msg = StackBuf(3)  # S, then the first round's c0 and c2
    for j in unroll(0, 3):
        if const((N_FRESH + j) % 4 == 0):
            sp = fs_perm(sp, rate, 4)
            rate = StackBuf(8)
        bc_word, cursor = fs_next(rate, (N_FRESH + j) % 4, cursor)
        bc_msg[j] = bc_word
    bc_share = bc_msg[0]
    sp, bc_r, cursor = fs_grind_squeeze(sp, rate, (N_FRESH + 2) % 4 + 1, cursor, tabs, ROUND2_GRIND_BITS)
    bc_point[GEN ** 0] = bc_r
    bc_claim = bc_msg[1] + bc_r * (bc_share + (1 + bc_r) * bc_msg[2])
    bfs0 = sp[8]
    bfs1 = sp[9]
    bfs2 = sp[10]
    bfs3 = sp[11]
    bfs4 = sp[12]
    for x in unroll(1, N_TUPLE_BITS):
        bfs0, bfs1, bfs2, bfs3, bfs4, cursor, bc_claim, bc_r = opening_tail_round(bfs0, bfs1, bfs2, bfs3, bfs4, cursor, bc_claim, tabs)
        bc_point[GEN ** x] = bc_r
    # It ends on fp_w's multilinear at bc_point times P(ζ_lo, bc_point), the value read
    # next, which the deferred claim pins. fp_w folds a round at a time: round j's
    # 2^(3 - j) values from offset N_TUPLE_SLOTS - 2^(4 - j).
    sp = fs_cap(bfs0, bfs1, bfs2, bfs3, bfs4)
    rate = StackBuf(8)
    bc_value, cursor = fs_next(rate, 0, cursor)
    w_fold = StackBuf(N_TUPLE_SLOTS - 1)
    r0 = bc_point[GEN ** 0]
    for i in unroll(0, N_TUPLE_SLOTS // 2):
        w_lo = fp_w[GEN ** (2 * i)]
        w_fold[i] = w_lo + r0 * (w_lo + fp_w[GEN ** (2 * i + 1)])
    for j in unroll(1, N_TUPLE_BITS):
        rj = bc_point[GEN ** j]
        for i in unroll(0, 2 ** (N_TUPLE_BITS - 1 - j)):
            w_lo = w_fold[N_TUPLE_SLOTS - 2 ** (N_TUPLE_BITS + 1 - j) + 2 * i]
            w_hi = w_fold[N_TUPLE_SLOTS - 2 ** (N_TUPLE_BITS + 1 - j) + 2 * i + 1]
            w_fold[N_TUPLE_SLOTS - 2 ** (N_TUPLE_BITS - j) + i] = w_lo + rj * (w_lo + w_hi)
    assert bc_claim == w_fold[N_TUPLE_SLOTS - 2] * bc_value

    # ---- the sides' framework decomposition ----
    # Per side, what its tables' blocks owe: its GKR leaf value less the framework
    # blocks' fingerprints and the padding mass. DERIVED, not read: a transmitted
    # total would be a free value in its own check. The table sumcheck's target pins
    # it below. Pull's padding is push's (same blocks, same padding tuples), and the
    # count side weighs its counts alone, at beta = 0.
    bus_table_total = StackBuf(N_GKR_SIDES)
    beta_1 = beta + 1
    for s in unroll(0, N_GKR_SIDES):
        acc = 0
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            if BLOCK_TABLE[b] == NO_TABLE:
                inner_sum = 0
                for i in unroll(0, BLOCK_COORD_COUNT[b]):
                    ci = BLOCK_COORD_OFF[b] + i
                    if const(COORD_TYPE[ci] != COORD_KIND_PUBLIC):
                        if s == COUNT_SIDE:
                            inner_sum += coord_vals[ci]
                        else:
                            inner_sum += fp_w[GEN ** i] * coord_vals[ci]
                if s == COUNT_SIDE:
                    acc += block_eq_hi[b] * inner_sum
                else:
                    acc += block_eq_hi[b] * (beta + inner_sum)
        if const(s != COUNT_SIDE):
            acc += public_eqs[s] * bc_share
        # The table sumcheck sums a table block's form phi over every row, padding
        # rows included, whose leaves are 1 instead: the difference, (1 - phi(p_j))
        # times the table's pad_weight, is public and joins the padding mass.
        if s == PULL_SIDE:
            acc += push_padding
        else:
            padding_sum = 0
            for t in unroll(0, N_TABLES):
                table_sum = 0
                for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
                    if BLOCK_TABLE[b] == t:
                        if s == COUNT_SIDE:
                            coeff = 1
                        else:
                            coeff = beta_1
                        for i in unroll(0, BLOCK_COORD_COUNT[b]):
                            ci = BLOCK_COORD_OFF[b] + i
                            if const(COORD_PADDING[ci] != 0):
                                if s == COUNT_SIDE:
                                    coeff += COORD_PADDING[ci]
                                else:
                                    coeff += fp_w[GEN ** i] * COORD_PADDING[ci]
                        table_sum += block_eq_hi[b] * coeff
                padding_sum += pad_weight[t] * table_sum
            acc += padding_sum
            if s == PUSH_SIDE:
                push_padding = padding_sum
        acc += 1 + selector_sums[s]
        bus_table_total[s] = acc + gkr_leaves[GEN ** s]
    claim_idx = N_BUS_CLAIMS  # the table and public-input claims follow the deduped bus claims

    # ---- ONE table sumcheck for all six tables ----
    # Mirrors crates/verifier's table_sumcheck. zc_xi ONCE, each table folding its own
    # identities with a DISJOINT range of its powers (ETA_OFFSET[t]); one shared
    # point zeta (the bus GKR's); n = max_t tau_t rounds. Rounds bind the HIGHEST
    # variable first, so a 2^tau table sits out the first n - tau and joins carrying
    # the challenges it sat out, weighing cprod[n - tau] * peq[tau] where peq[tau] =
    # eq(zeta[..tau], chi[..tau]); the zc_xi-powers are inside constraint_eval.
    #
    # g^n is hinted, then pinned exactly: the range-checked division slacks force it
    # to dominate every certified tau and the product identity forces it to BE one.
    g_zc_n = hint_witness("zc_tau_max")
    zc_is_a_tau = 1
    for t in unroll(0, N_TABLES):
        tau_g = kb[2 + t]
        assert log(g_zc_n / tau_g) < COUNT_BITS
        zc_is_a_tau *= g_zc_n + tau_g
    assert zc_is_a_tau == 0
    # n <= mu, the `Error::Truncated` of constraints.rs. Every table pushes at
    # kappa = tau, so it holds structurally, but zc_peq below reads zeta[..n] and
    # zeta only holds mu coords: unwritten heap there is prover-chosen.
    assert log(g_bus_mu / g_zc_n) < COUNT_BITS
    # xi, after its grind, the bytecode value waiting: the batch is of degree
    # N_ETA_POWS - 1 in it.
    sp, zc_xi, cursor = fs_grind_squeeze(sp, rate, 1, cursor, tabs, XI_GRIND_BITS)
    zc_xi_pows = StackBuf(N_ETA_POWS)
    zc_xi_pows[0] = 1
    for k in unroll(1, N_ETA_POWS):
        zc_xi_pows[k] = zc_xi_pows[k - 1] * zc_xi
    # The eq point is the bus GKR's zeta, NOT a fresh one, which is what lets the
    # batch settle the bus forms alongside the constraints. It is also why no target
    # is read: what the three sides' tables owe, each in its own shared power of
    # zc_xi, IS the sum the batch must reach, and zc_xi is squeezed after those
    # totals are fixed, so hitting one number forces all three side equations.
    bus_target = 0
    for sd in unroll(0, N_GKR_SIDES):
        bus_target += zc_xi_pows[ETA_FORM_BASE + sd] * bus_table_total[sd]
    # n vanilla sumcheck rounds: the round polynomial arrives whole, so a round is
    # `h(0) + h(1) == claim` and a fold, with no eq to reapply. The tables still
    # waiting ride inside h, so nothing here is indexed by height; the heights enter
    # only the per-table weights below.
    zc_rounds = HeapBuf((g_zc_n * GEN) ** ROUND_SLOTS)
    zc_cprod = HeapBuf(g_zc_n * GEN)  # the challenges bound so far, multiplied
    fs_store(zc_rounds, ROUND_FS, 1, sp)
    zc_rounds[GEN ** ROUND_CURSOR] = cursor
    zc_rounds[GEN ** ROUND_CLAIM] = bus_target
    zc_cprod[GEN ** 0] = 1
    for xk in mul_range(1, g_zc_n):
        rd = zc_rounds * xk ** ROUND_SLOTS
        ncur, nclaim, rk = sumcheck_round4(rd, rd[GEN ** ROUND_CURSOR], rd[GEN ** ROUND_CLAIM], tabs)
        chi[g_zc_n * INV_GEN / xk] = rk  # g^(n-1-j): the variable round j binds
        nxt = rd * GEN ** ROUND_SLOTS
        nxt[GEN ** ROUND_CURSOR] = ncur
        nxt[GEN ** ROUND_CLAIM] = nclaim
        # cprod is the weight of a table that joins here; peq below is the rest
        zc_cprod[xk * GEN] = zc_cprod[xk] * rk
    zc_last = zc_rounds * g_zc_n ** ROUND_SLOTS
    sp = fs_load(zc_last, ROUND_FS, 1)
    rate = StackBuf(8)
    cursor = zc_last[GEN ** ROUND_CURSOR]
    claim = zc_last[GEN ** ROUND_CLAIM]
    # peq[g^tau] = eq(zeta[..tau], chi[..tau]), as a prefix chain.
    zc_peq = HeapBuf(g_zc_n * GEN)
    eq_prefix_chain(zc_peq, 1, chi, zeta1, g_zc_n)
    # Per table: every committed column's evaluation (pooled), its AIR constraint
    # at its own reduced point chi[..tau_t], weighted into the batch's final claim.
    air_acc = 0
    # The column evaluations stay where the stream holds them, N_COL_EVALS
    # consecutive words that fs_next bound: the pool's slots from N_BUS_CLAIMS on are
    # read there rather than copied.
    col_eval_words = cursor
    for t in unroll(0, N_TABLES):
        tau_g = kb[2 + t]
        col_evals = StackBuf(TABLE_COLS_CAP)
        for pos in unroll(TABLE_COL_BASE[t], TABLE_COL_BASE[t] + N_TABLE_COLS[t]):
            if pos % 4 == 0:
                if pos != 0:
                    sp = fs_perm(sp, rate, 4)
                    rate = StackBuf(8)
            e, cursor = fs_next(rate, pos % 4, cursor)
            col_evals[pos - TABLE_COL_BASE[t]] = e
            claim_idx += 1
        # The table's AIR constraint at the final point (col_evals is indexed by
        # local column index; the formulas mirror tables.rs Table::constraint). Every
        # value relation now rides the bus as a degree-2 coordinate, so only JUMP's
        # is-nonzero indicator is left with an identity of its own.
        constraint_eval = 0
        if t == TABLE_JUMP:
            # `b = c*w` and `c*(b+1) = 0`. The condition is K-valued, its memory read
            # carrying literal zeros above the low limb, so both identities are
            # single-lane (tables.rs JumpTable::constraint). Local columns: v_cond at 5, w at
            # 12, the indicator b at 13.
            c = col_evals[5]
            b = col_evals[13]
            constraint_eval = zc_xi_pows[ETA_OFFSET[t] + 0] * (b + c * col_evals[12])
            constraint_eval += zc_xi_pows[ETA_OFFSET[t] + 1] * (c * (b + 1))
        # The table's bus coordinates, evaluated at the SAME column evaluations, each
        # the sum of its terms over this table's column evaluations (a product term, an
        # address or an arithmetic result, is degree 2, which the batch's round
        # polynomial already allows); a pull coordinate as its difference from its push
        # twin's, where the two differ. This is what replaces opening those columns at ζ.
        for b in unroll(0, N_BLOCKS):
            if BLOCK_TABLE[b] == t:
                for i in unroll(0, BLOCK_COORD_COUNT[b]):
                    ci = BLOCK_COORD_OFF[b] + i  # a compile-time index, so `ci` costs nothing
                    if const(BLOCK_SIDE[b] == PULL_SIDE):
                        n_terms = COORD_DIFF_COUNT[ci]
                        first = COORD_DIFF_OFF[ci]
                    else:
                        n_terms = COORD_TERM_COUNT[ci]
                        first = COORD_TERM_OFF[ci]
                    if const(n_terms != 0):
                        cv = 0
                        for j in unroll(0, n_terms):
                            tj = first + j
                            if TERM_TYPE[tj] == COORD_KIND_CONST:
                                cv += TERM_CONST[tj]
                            if TERM_TYPE[tj] == COORD_KIND_COL:
                                cv += col_evals[TERM_COL_A[tj]]
                            if TERM_TYPE[tj] == COORD_KIND_GCOL:
                                cv += TERM_CONST[tj] * col_evals[TERM_COL_A[tj]]
                            if TERM_TYPE[tj] == COORD_KIND_PROD:
                                cv += TERM_CONST[tj] * (col_evals[TERM_COL_A[tj]] * col_evals[TERM_COL_B[tj]])
                        coord_vals[ci] = cv
        # Its forms, one a side: Σ_b eq_hi(b) · (β + Σ_i w(i) · coord_i). A pull
        # block shares its push twin's eq_hi, so a pull form is push's plus the
        # coordinates where the two differ.
        for sd in unroll(0, N_GKR_SIDES):
            form = 0
            for b in unroll(SIDE_BLOCK_START[sd], SIDE_BLOCK_START[sd + 1]):
                if BLOCK_TABLE[b] == t:
                    inner = 0
                    for i in unroll(0, BLOCK_COORD_COUNT[b]):
                        ci = BLOCK_COORD_OFF[b] + i
                        if const(sd == PULL_SIDE):
                            n_terms = COORD_DIFF_COUNT[ci]
                        else:
                            n_terms = COORD_TERM_COUNT[ci]
                        if const(n_terms != 0):
                            if sd == COUNT_SIDE:
                                inner += coord_vals[ci]
                            else:
                                inner += fp_w[GEN ** i] * coord_vals[ci]
                    if sd == PUSH_SIDE:
                        form += block_eq_hi[b] * (beta + inner)
                    else:
                        form += block_eq_hi[b] * inner
            if const(sd == PUSH_SIDE):
                push_form = form
            if const(sd == PULL_SIDE):
                form = push_form + form
            constraint_eval += zc_xi_pows[ETA_FORM_BASE + sd] * form
        air_acc += zc_cprod[g_zc_n / tau_g] * zc_peq[tau_g] * constraint_eval  # cprod[n - tau] * peq[tau]
    assert air_acc == claim

    # ---- public-input binding claim: one per MEM limb, read off no stream ----
    # The VM's bind_pi_claim claims each committed MEM limb at [rm, 0..] equals
    # that limb's line through the public words, lo_0 + rm*(lo_0 + lo_1) and so
    # on, which the statement alone determines. split_limbs binds each word's
    # limbs (doc sec:e2e-pi).
    sp, rm = squeeze(sp, rate, (N_COL_EVALS + 3) % 4 + 1)
    lo_0, hi_0 = split_limbs(pi_0)
    lo_1, hi_1 = split_limbs(pi_1)
    claim_pool[GEN ** claim_idx] = lo_0 + rm * (lo_0 + lo_1)
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = hi_0 + rm * (hi_0 + hi_1)
    claim_idx += 1
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, g_zc_n, bc_value, rm, col_eval_words
```
-/
def verifyTables : GFn where
  name := "verify_tables"
  arity := 20
  rets := 10
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let mut cursor := cellOf ps 5
    let pi0 := cellOf ps 6
    let pi1 := cellOf ps 7
    let zeta := cellOf ps 8
    let gBusMu := cellOf ps 9
    let dimsG := cellOf ps 10
    let tableRows := cellOf ps 11
    let gSquares := cellOf ps 12
    let fpW := cellOf ps 13
    let beta := cellOf ps 14
    let claimPool := cellOf ps 15
    let chi := cellOf ps 16
    let gkrLeaves := cellOf ps 17
    let tabs := cellOf ps 18
    let bcPoint := cellOf ps 19
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut rate ← B.stackBuf 8
    let kb ← B.stackBuf 8
    B.constInto (cellOf kb 0) 1
    for t_k in [0:N_TABLES + 1] do
      B.loadInto (cellOf kb (1 + t_k)) dimsG t_k
    let groupSideTab : Shifted := ⟨gSquares, SIDE_TAB_AT⟩
    let rankKeys : Shifted := ⟨gSquares, RANK_KEYS_AT⟩
    let groupKey ← B.heapBuf N_BLOCK_GROUPS
    let groupSize ← B.heapBuf N_BLOCK_GROUPS
    let groupBase ← B.heapBuf N_BLOCK_GROUPS
    let groupOrder ← B.heapBuf N_BLOCK_GROUPS
    B.witness "block_group_order" (.heap groupOrder.v 0 N_BLOCK_GROUPS)
    let blockOff ← B.stackBuf N_BLOCKS
    let mut s : Nat := default
    let mut b0 : Nat := default
    let mut kappaG : Word := default
    let mut gi : Word := default
    let mut key : Word := default
    let mut prevKey : Word := default
    let mut step : Word := default
    let cert_k := 0
    s := COUNT_SIDE * cert_k
    let gi_k := 0
    b0 := arrInt BLOCK_GROUP_START gi_k
    kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b0)
    B.store groupKey gi_k (← B.load (← B.mul rankKeys.base kappaG) rankKeys.exp)
    B.store groupSize gi_k (← B.pow (← B.load (← B.mul gSquares kappaG) 0) ((arrInt BLOCK_GROUP_START (gi_k + 1)) - b0))
    let gi_k := 1
    b0 := arrInt BLOCK_GROUP_START gi_k
    kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b0)
    B.store groupKey gi_k (← B.mul (← B.load (← B.mul rankKeys.base kappaG) rankKeys.exp) (← B.const ((lit INV_GEN) ^ b0)))
    B.store groupSize gi_k (← B.pow (← B.load (← B.mul gSquares kappaG) 0) ((arrInt BLOCK_GROUP_START (gi_k + 1)) - b0))
    let gi_k := 2
    b0 := arrInt BLOCK_GROUP_START gi_k
    kappaG ← B.mul (cellOf kb (arrInt BLOCK_KAPPA_SRC b0)) (← B.const (gpowE (arrInt BLOCK_KAPPA_ADJ b0)))
    B.store groupKey gi_k (← B.mul (← B.load (← B.mul rankKeys.base kappaG) rankKeys.exp) (← B.const ((lit INV_GEN) ^ b0)))
    B.store groupSize gi_k (← B.pow (← B.load (← B.mul gSquares kappaG) 0) ((arrInt BLOCK_GROUP_START (gi_k + 1)) - b0))
    for gi_k in [3:arrInt SIDE_GROUP_START (s + 1)] do
      b0 := arrInt BLOCK_GROUP_START gi_k
      kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b0)
      B.store groupKey gi_k (← B.mul (← B.load (← B.mul rankKeys.base kappaG) rankKeys.exp) (← B.const ((lit INV_GEN) ^ b0)))
      B.store groupSize gi_k (← B.pow (← B.load (← B.mul gSquares kappaG) 0) ((arrInt BLOCK_GROUP_START (gi_k + 1)) - b0))
    let gOff : GPow := ⟨0⟩
    let mut gOff_word : Word := default
    let r_k := 0
    gi ← B.load groupOrder r_k
    let _ ← B.rangeCheck gi N_BLOCK_GROUPS
    let t0 ← B.const (lit s)
    B.store (← B.mul groupSideTab.base gi) groupSideTab.exp t0
    key ← B.load (← B.mul groupKey gi) 0
    if r_k ≠ (arrInt SIDE_GROUP_START s) then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    let t1 ← B.const (gpowE gOff.exp)
    B.store (← B.mul groupBase gi) 0 t1
    gOff_word ← B.load (← B.mul groupSize gi) 0
    prevKey := key
    for r_k in [1:arrInt SIDE_GROUP_START (s + 1)] do
      gi ← B.load groupOrder r_k
      let _ ← B.rangeCheck gi N_BLOCK_GROUPS
      let t0 ← B.const (lit s)
      B.store (← B.mul groupSideTab.base gi) groupSideTab.exp t0
      key ← B.load (← B.mul groupKey gi) 0
      if r_k ≠ (arrInt SIDE_GROUP_START s) then
        let t1 ← B.const (gpowE (RANK_KEY_BOUND - 1))
        let _ ← B.rangeCheckK (← B.mul (← B.fdiv prevKey key) (← B.const (lit INV_GEN))) t1
        pure ()
      else
        pure () -- no use of this definition takes this branch
      B.store (← B.mul groupBase gi) 0 gOff_word
      gOff_word ← B.mul gOff_word (← B.load (← B.mul groupSize gi) 0)
      prevKey := key
    for gi_k in [arrInt SIDE_GROUP_START s:3] do
      b0 := arrInt BLOCK_GROUP_START gi_k
      step ← B.load (← B.mul gSquares (cellOf kb (arrInt BLOCK_KAPPA_SRC b0))) (arrInt BLOCK_KAPPA_ADJ b0)
      B.loadInto (cellOf blockOff b0) groupBase gi_k
    for gi_k in [3:arrInt SIDE_GROUP_START (s + 1)] do
      b0 := arrInt BLOCK_GROUP_START gi_k
      step ← B.load (← B.mul gSquares (cellOf kb (arrInt BLOCK_KAPPA_SRC b0))) (arrInt BLOCK_KAPPA_ADJ b0)
      B.loadInto (cellOf blockOff b0) groupBase gi_k
      for b_k in [b0 + 1:arrInt BLOCK_GROUP_START (gi_k + 1)] do
        B.mulInto (cellOf blockOff b_k) (cellOf blockOff (b_k - 1)) step
    let cert_k := 1
    s := COUNT_SIDE * cert_k
    for gi_k in [arrInt SIDE_GROUP_START s:arrInt SIDE_GROUP_START (s + 1)] do
      b0 := arrInt BLOCK_GROUP_START gi_k
      kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b0)
      B.store groupKey gi_k (← B.mul (← B.load (← B.mul rankKeys.base kappaG) rankKeys.exp) (← B.const ((lit INV_GEN) ^ b0)))
      B.store groupSize gi_k (← B.pow (← B.load (← B.mul gSquares kappaG) 0) ((arrInt BLOCK_GROUP_START (gi_k + 1)) - b0))
    let gOff : GPow := ⟨0⟩
    let r_k := 18
    gi ← B.load groupOrder r_k
    let _ ← B.rangeCheck gi N_BLOCK_GROUPS
    let t0 ← B.const (gpowE (Nat.log2 s))
    B.store (← B.mul groupSideTab.base gi) groupSideTab.exp t0
    key ← B.load (← B.mul groupKey gi) 0
    if r_k ≠ (arrInt SIDE_GROUP_START s) then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    let t1 ← B.const (gpowE gOff.exp)
    B.store (← B.mul groupBase gi) 0 t1
    gOff_word ← B.load (← B.mul groupSize gi) 0
    prevKey := key
    for r_k in [19:arrInt SIDE_GROUP_START (s + 1)] do
      gi ← B.load groupOrder r_k
      let _ ← B.rangeCheck gi N_BLOCK_GROUPS
      let t0 ← B.const (gpowE (Nat.log2 s))
      B.store (← B.mul groupSideTab.base gi) groupSideTab.exp t0
      key ← B.load (← B.mul groupKey gi) 0
      if r_k ≠ (arrInt SIDE_GROUP_START s) then
        let t1 ← B.const (gpowE (RANK_KEY_BOUND - 1))
        let _ ← B.rangeCheckK (← B.mul (← B.fdiv prevKey key) (← B.const (lit INV_GEN))) t1
        pure ()
      else
        pure () -- no use of this definition takes this branch
      B.store (← B.mul groupBase gi) 0 gOff_word
      gOff_word ← B.mul gOff_word (← B.load (← B.mul groupSize gi) 0)
      prevKey := key
    for gi_k in [arrInt SIDE_GROUP_START s:20] do
      b0 := arrInt BLOCK_GROUP_START gi_k
      step ← B.load (← B.mul gSquares (cellOf kb (arrInt BLOCK_KAPPA_SRC b0))) (arrInt BLOCK_KAPPA_ADJ b0)
      B.loadInto (cellOf blockOff b0) groupBase gi_k
      for b_k in [b0 + 1:arrInt BLOCK_GROUP_START (gi_k + 1)] do
        B.mulInto (cellOf blockOff b_k) (cellOf blockOff (b_k - 1)) step
    let gi_k := 20
    b0 := arrInt BLOCK_GROUP_START gi_k
    step ← B.load (← B.mul gSquares (cellOf kb (arrInt BLOCK_KAPPA_SRC b0))) (arrInt BLOCK_KAPPA_ADJ b0)
    B.loadInto (cellOf blockOff b0) groupBase gi_k
    let b_k := 117
    B.mulInto (cellOf blockOff b_k) (cellOf blockOff (b_k - 1)) step
    for gi_k in [21:arrInt SIDE_GROUP_START (s + 1)] do
      b0 := arrInt BLOCK_GROUP_START gi_k
      step ← B.load (← B.mul gSquares (cellOf kb (arrInt BLOCK_KAPPA_SRC b0))) (arrInt BLOCK_KAPPA_ADJ b0)
      B.loadInto (cellOf blockOff b0) groupBase gi_k
      for b_k in [b0 + 1:arrInt BLOCK_GROUP_START (gi_k + 1)] do
        B.mulInto (cellOf blockOff b_k) (cellOf blockOff (b_k - 1)) step
    let padWeight ← B.stackBuf N_TABLES
    let mut tauG : Word := default
    for t_k in [0:N_TABLES] do
      tauG := cellOf kb (2 + t_k)
      let _ ← B.rangeCheck tauG N_COLUMN_LOGS
      let rows ← B.load tableRows t_k
      let t2 ← B.targets [some (cellOf padWeight t_k).v, none, none]
      B.dispatchInto tauG ((List.range N_COLUMN_LOGS).map fun arm => (instName "padding_weight" [.L arm])) [rows.v, zeta.v] t2
      let lead := cellOf t2 1
      let rest := cellOf t2 2
      if (arrInt FLOORS t_k) = 0 then
        B.assertEq lead (← B.const 1)
        B.assertNe rest (← B.const 0)
      else
        let t3 ← B.const (gpowE (N_COLUMN_LOGS - 1))
        let _ ← B.rangeCheckK (← B.fdiv tauG (← B.const (gpowE (arrInt FLOORS t_k)))) t3
        let t4 ← B.add tauG (← B.const (gpowE (arrInt FLOORS t_k)))
        let _ ← B.ite t4
          (do
            pure ())
          (do
            B.assertEq lead (← B.const 1)
            B.assertNe rest (← B.const 0))
        pure ()
    let idxcTab ← B.heapBuf SIZE_BITS
    for t_k in [0:SIZE_BITS] do
      B.store idxcTab t_k (← B.const (arrWord INDEX_MLE_FACTORS t_k))
    let zeta1 ← B.heapBufDyn gBusMu
    let t5 ← B.targets [none]
    B.dispatchInto gBusMu ((List.range SIZE_BITS).map fun arm => (instName "plus_one_run" [.L arm])) [zeta1.v, zeta.v] t5
    let zeta1Done := cellOf t5 0
    let sharedLen ← B.stackBuf N_TABLES
    let sharedEq ← B.stackBuf N_TABLES
    let sharedG ← B.stackBuf N_TABLES
    for t_k in [0:N_TABLES] do
      tauG := cellOf kb (2 + t_k)
      B.copy (cellOf sharedLen t_k) (← B.fdiv gBusMu tauG)
      let _ ← B.rangeCheck (cellOf sharedLen t_k) SIZE_BITS
      let qG ← call1 "selector_run_nibbles" [(cellOf sharedLen t_k).v]
      let gLen ← B.pow (← B.shifted qG 1) 16
      let eqT ← B.heapBufDyn (← B.mul gLen gLen)
      let gT ← B.heapBufDyn gLen
      let _ ← B.call "shared_selector_tables" [eqT.v, gT.v, (← B.mul zeta tauG).v, (← B.mul zeta1 tauG).v, (← B.mul gSquares tauG).v, (cellOf sharedLen t_k).v, qG.v] 0
      B.copy (cellOf sharedEq t_k) eqT
      B.copy (cellOf sharedG t_k) gT
    let blockEqHi ← B.stackBuf N_BLOCKS
    let blockIndexMle ← B.heapBuf N_BLOCKS
    let coordVals ← B.stackBuf N_COORDS
    let selectorSums ← B.stackBuf N_GKR_SIDES
    let publicEqs ← B.stackBuf N_GKR_SIDES
    let mut blockHasPublic : Nat := default
    let mut shared : Nat := default
    let mut selLenG : Word := default
    let mut offsetBits : Word := default
    let mut selBits : Word := default
    let mut zeta1Hi : Word := default
    let mut idxcHi : Word := default
    let mut eqHi : Word := default
    let mut goff : Word := default
    let mut ci : Nat := default
    let mut coordVal : Word := default
    let mut cursor_ptr : Shifted := default
    let mut t : Nat := default
    let mut digits : Word := default
    let mut lenG : Word := default
    let mut tabEq : Word := default
    let mut tabG : Word := default
    let s_k := 0
    let selectorSum := 0
    let publicEq := 0
    let mut selectorSum_word : Word := default
    let mut publicEq_word : Word := default
    let b_k := 0
    blockHasPublic := 0
    kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b_k)
    if (arrInt BLOCK_KAPPA_SRC b_k) ≠ 0 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if s_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      shared := 0
      if ((arrInt BLOCK_KAPPA_SRC b_k) / 2) ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      if shared = 1 then
        pure () -- no use of this definition takes this branch
      else
        selLenG ← B.fdiv gBusMu kappaG
        let _ ← B.rangeCheck selLenG SIZE_BITS
        offsetBits ← B.heapBufDyn (← B.const (gpowE SIZE_BITS))
        B.hintBitsExpTo (.heap offsetBits.v 0 SIZE_BITS) (cellOf blockOff b_k) SIZE_BITS
        selBits ← B.mul offsetBits kappaG
        zeta1Hi ← B.mul zeta1 kappaG
        idxcHi ← B.mul idxcTab kappaG
        let t6 ← B.targets [none, none]
        B.dispatchInto selLenG ((List.range SIZE_BITS).map fun arm => (instName "block_selector" [.L arm])) [selBits.v, zeta1Hi.v, idxcHi.v] t6
        eqHi := cellOf t6 0
        goff := cellOf t6 1
      B.assertEq goff (cellOf blockOff b_k)
    selectorSum_word := eqHi
    B.copy (cellOf blockEqHi b_k) eqHi
    if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
      for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_TYPE ci) = COORD_KIND_CONST then
          B.constInto (cellOf coordVals ci) (arrWord COORD_CONST ci)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt COORD_TYPE ci) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_INDEX then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_PUBLIC then
          pure () -- no use of this definition takes this branch
        else
          pure ()
      if blockHasPublic = 1 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    let b_k := 1
    blockHasPublic := 0
    kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b_k)
    if (arrInt BLOCK_KAPPA_SRC b_k) ≠ 0 then
      if (arrInt BLOCK_KAPPA_ADJ b_k) ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    if s_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      shared := 0
      if ((arrInt BLOCK_KAPPA_SRC b_k) / 2) ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      if shared = 1 then
        pure () -- no use of this definition takes this branch
      else
        selLenG ← B.fdiv gBusMu kappaG
        let _ ← B.rangeCheck selLenG SIZE_BITS
        offsetBits ← B.heapBufDyn (← B.const (gpowE SIZE_BITS))
        B.hintBitsExpTo (.heap offsetBits.v 0 SIZE_BITS) (cellOf blockOff b_k) SIZE_BITS
        selBits ← B.mul offsetBits kappaG
        zeta1Hi ← B.mul zeta1 kappaG
        idxcHi ← B.mul idxcTab kappaG
        let t6 ← B.targets [none, none]
        B.dispatchInto selLenG ((List.range SIZE_BITS).map fun arm => (instName "block_selector" [.L arm])) [selBits.v, zeta1Hi.v, idxcHi.v] t6
        eqHi := cellOf t6 0
        goff := cellOf t6 1
      B.assertEq goff (cellOf blockOff b_k)
    selectorSum_word ← B.add selectorSum_word eqHi
    B.copy (cellOf blockEqHi b_k) eqHi
    if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
      for i_k in [0:4] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_TYPE ci) = COORD_KIND_CONST then
          B.constInto (cellOf coordVals ci) (arrWord COORD_CONST ci)
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_COL then
          if (arrInt COORD_FRESH ci) = 1 then
            if ((arrInt COORD_FRESH_POS ci) % 4) = 0 then
              if (arrInt COORD_FRESH_POS ci) ≠ 0 then
                pure () -- no use of this definition takes this branch
              else
                pure ()
            else
              pure () -- no use of this definition takes this branch
            let (t7, t8) ← fsNext rate ((arrInt COORD_FRESH_POS ci) % 4) cursor
            coordVal := t7
            cursor_ptr := t8
            B.store claimPool (arrInt COORD_CLAIM_SLOT ci) coordVal
          else
            pure () -- no use of this definition takes this branch
          B.copy (cellOf coordVals ci) coordVal
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_INDEX then
          if s_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            let t7 ← B.targets [none]
            B.dispatchInto kappaG ((List.range SIZE_BITS).map fun arm => (instName "index_mle" [.L arm])) [zeta.v] t7
            coordVal := cellOf t7 0
            B.copy (cellOf coordVals ci) coordVal
            if s_k = PUSH_SIDE then
              B.store blockIndexMle b_k coordVal
            else
              pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_PUBLIC then
          pure () -- no use of this definition takes this branch
        else
          pure ()
      let i_k := 4
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt COORD_TYPE ci) = COORD_KIND_CONST then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      if (arrInt COORD_TYPE ci) = COORD_KIND_COL then
        if (arrInt COORD_FRESH ci) = 1 then
          if ((arrInt COORD_FRESH_POS ci) % 4) = 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          let (t7, t8) ← fsNext_2 rate ((arrInt COORD_FRESH_POS ci) % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
          coordVal := t7
          cursor_ptr := t8
          B.store claimPool (arrInt COORD_CLAIM_SLOT ci) coordVal
        else
          pure () -- no use of this definition takes this branch
        B.copy (cellOf coordVals ci) coordVal
      else
        pure () -- no use of this definition takes this branch
      if (arrInt COORD_TYPE ci) = COORD_KIND_GCOL then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      if (arrInt COORD_TYPE ci) = COORD_KIND_INDEX then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      if (arrInt COORD_TYPE ci) = COORD_KIND_PUBLIC then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      if blockHasPublic = 1 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    let b_k := 2
    blockHasPublic := 0
    kappaG ← B.mul (cellOf kb (arrInt BLOCK_KAPPA_SRC b_k)) (← B.const (gpowE (arrInt BLOCK_KAPPA_ADJ b_k)))
    if (arrInt BLOCK_KAPPA_SRC b_k) ≠ 0 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if s_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      shared := 0
      if ((arrInt BLOCK_KAPPA_SRC b_k) / 2) ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      if shared = 1 then
        pure () -- no use of this definition takes this branch
      else
        selLenG ← B.fdiv gBusMu kappaG
        let _ ← B.rangeCheck selLenG SIZE_BITS
        offsetBits ← B.heapBufDyn (← B.const (gpowE SIZE_BITS))
        B.hintBitsExpTo (.heap offsetBits.v 0 SIZE_BITS) (cellOf blockOff b_k) SIZE_BITS
        selBits ← B.mul offsetBits kappaG
        zeta1Hi ← B.mul zeta1 kappaG
        idxcHi ← B.mul idxcTab kappaG
        let t6 ← B.targets [none, none]
        B.dispatchInto selLenG ((List.range SIZE_BITS).map fun arm => (instName "block_selector" [.L arm])) [selBits.v, zeta1Hi.v, idxcHi.v] t6
        eqHi := cellOf t6 0
        goff := cellOf t6 1
      B.assertEq goff (cellOf blockOff b_k)
    selectorSum_word ← B.add selectorSum_word eqHi
    B.copy (cellOf blockEqHi b_k) eqHi
    if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
      for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_TYPE ci) = COORD_KIND_CONST then
          B.constInto (cellOf coordVals ci) (arrWord COORD_CONST ci)
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_INDEX then
          if s_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            let t7 ← B.targets [none]
            B.dispatchInto kappaG ((List.range SIZE_BITS).map fun arm => (instName "index_mle" [.L arm])) [zeta.v] t7
            coordVal := cellOf t7 0
            B.copy (cellOf coordVals ci) coordVal
            if s_k = PUSH_SIDE then
              B.store blockIndexMle b_k coordVal
            else
              pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_PUBLIC then
          B.constInto (cellOf coordVals ci) 0
          blockHasPublic := 1
        else
          pure ()
      if blockHasPublic = 1 then
        publicEq_word := eqHi
      else
        pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [3:arrInt SIDE_BLOCK_START (s_k + 1)] do
      blockHasPublic := 0
      kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b_k)
      if (arrInt BLOCK_KAPPA_SRC b_k) ≠ 0 then
        if (arrInt BLOCK_KAPPA_ADJ b_k) ≠ 0 then
          pure () -- no use of this definition takes this branch
        else
          pure ()
      else
        pure () -- no use of this definition takes this branch
      if s_k = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        shared := 0
        if ((arrInt BLOCK_KAPPA_SRC b_k) / 2) ≠ 0 then
          if (arrInt BLOCK_KAPPA_ADJ b_k) = 0 then
            shared := 1
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if shared = 1 then
          t := (arrInt BLOCK_KAPPA_SRC b_k) - 2
          digits ← B.heapBuf SEL_TAB_NIBBLES
          B.hintDigitsExp (.heap digits.v 0 SEL_TAB_NIBBLES) (cellOf blockOff b_k) SIZE_BITS SEL_TAB_NIBBLES 4 0 (startCell := some (cellOf kb (2 + t)))
          lenG := cellOf sharedLen t
          tabEq := cellOf sharedEq t
          tabG := cellOf sharedG t
          let t6 ← B.targets [none, none]
          B.dispatchInto lenG ((List.range SIZE_BITS).map fun arm => (instName "block_selector_tab" [.L arm])) [digits.v, tabEq.v, tabG.v] t6
          eqHi := cellOf t6 0
          goff := cellOf t6 1
        else
          pure () -- no use of this definition takes this branch
        B.assertEq goff (cellOf blockOff b_k)
      selectorSum_word ← B.add selectorSum_word eqHi
      B.copy (cellOf blockEqHi b_k) eqHi
      if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    B.copy (cellOf selectorSums s_k) selectorSum_word
    B.copy (cellOf publicEqs s_k) publicEq_word
    let s_k := 1
    let selectorSum := 0
    let publicEq := 0
    let b_k := 54
    blockHasPublic := 0
    kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b_k)
    if (arrInt BLOCK_KAPPA_SRC b_k) ≠ 0 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if s_k = PULL_SIDE then
      eqHi := cellOf blockEqHi (b_k - (arrInt SIDE_BLOCK_START PULL_SIDE))
    else
      pure () -- no use of this definition takes this branch
    selectorSum_word := eqHi
    B.copy (cellOf blockEqHi b_k) eqHi
    if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
      for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_TYPE ci) = COORD_KIND_CONST then
          B.constInto (cellOf coordVals ci) (arrWord COORD_CONST ci)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt COORD_TYPE ci) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_INDEX then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_PUBLIC then
          pure () -- no use of this definition takes this branch
        else
          pure ()
      if blockHasPublic = 1 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    let b_k := 55
    blockHasPublic := 0
    kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b_k)
    if (arrInt BLOCK_KAPPA_SRC b_k) ≠ 0 then
      if (arrInt BLOCK_KAPPA_ADJ b_k) ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    if s_k = PULL_SIDE then
      eqHi := cellOf blockEqHi (b_k - (arrInt SIDE_BLOCK_START PULL_SIDE))
    else
      pure () -- no use of this definition takes this branch
    selectorSum_word ← B.add selectorSum_word eqHi
    B.copy (cellOf blockEqHi b_k) eqHi
    if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
      for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_TYPE ci) = COORD_KIND_CONST then
          B.constInto (cellOf coordVals ci) (arrWord COORD_CONST ci)
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_COL then
          if (arrInt COORD_FRESH ci) = 1 then
            if ((arrInt COORD_FRESH_POS ci) % 4) = 0 then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            let (t6, t7) ← fsNext_2 rate ((arrInt COORD_FRESH_POS ci) % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
            coordVal := t6
            cursor_ptr := t7
            B.store claimPool (arrInt COORD_CLAIM_SLOT ci) coordVal
          else
            coordVal ← B.load claimPool (arrInt COORD_CLAIM_SLOT ci)
          B.copy (cellOf coordVals ci) coordVal
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_INDEX then
          if s_k = PULL_SIDE then
            B.loadInto (cellOf coordVals ci) blockIndexMle (b_k - (arrInt SIDE_BLOCK_START PULL_SIDE))
          else
            pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_PUBLIC then
          pure () -- no use of this definition takes this branch
        else
          pure ()
      if blockHasPublic = 1 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    let b_k := 56
    blockHasPublic := 0
    kappaG ← B.mul (cellOf kb (arrInt BLOCK_KAPPA_SRC b_k)) (← B.const (gpowE (arrInt BLOCK_KAPPA_ADJ b_k)))
    if (arrInt BLOCK_KAPPA_SRC b_k) ≠ 0 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if s_k = PULL_SIDE then
      eqHi := cellOf blockEqHi (b_k - (arrInt SIDE_BLOCK_START PULL_SIDE))
    else
      pure () -- no use of this definition takes this branch
    selectorSum_word ← B.add selectorSum_word eqHi
    B.copy (cellOf blockEqHi b_k) eqHi
    if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
      for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_TYPE ci) = COORD_KIND_CONST then
          B.constInto (cellOf coordVals ci) (arrWord COORD_CONST ci)
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_COL then
          if (arrInt COORD_FRESH ci) = 1 then
            if ((arrInt COORD_FRESH_POS ci) % 4) = 0 then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            let (t6, t7) ← fsNext_2 rate ((arrInt COORD_FRESH_POS ci) % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
            coordVal := t6
            cursor_ptr := t7
            B.store claimPool (arrInt COORD_CLAIM_SLOT ci) coordVal
          else
            pure () -- no use of this definition takes this branch
          B.copy (cellOf coordVals ci) coordVal
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_INDEX then
          if s_k = PULL_SIDE then
            B.loadInto (cellOf coordVals ci) blockIndexMle (b_k - (arrInt SIDE_BLOCK_START PULL_SIDE))
          else
            pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt COORD_TYPE ci) = COORD_KIND_PUBLIC then
          B.constInto (cellOf coordVals ci) 0
          blockHasPublic := 1
        else
          pure ()
      if blockHasPublic = 1 then
        publicEq_word := eqHi
      else
        pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [57:arrInt SIDE_BLOCK_START (s_k + 1)] do
      blockHasPublic := 0
      kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b_k)
      if (arrInt BLOCK_KAPPA_SRC b_k) ≠ 0 then
        if (arrInt BLOCK_KAPPA_ADJ b_k) ≠ 0 then
          pure () -- no use of this definition takes this branch
        else
          pure ()
      else
        pure () -- no use of this definition takes this branch
      if s_k = PULL_SIDE then
        eqHi := cellOf blockEqHi (b_k - (arrInt SIDE_BLOCK_START PULL_SIDE))
      else
        pure () -- no use of this definition takes this branch
      selectorSum_word ← B.add selectorSum_word eqHi
      B.copy (cellOf blockEqHi b_k) eqHi
      if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    B.copy (cellOf selectorSums s_k) selectorSum_word
    B.copy (cellOf publicEqs s_k) publicEq_word
    let s_k := 2
    let selectorSum := 0
    let publicEq := 0
    let b_k := 108
    blockHasPublic := 0
    kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b_k)
    if (arrInt BLOCK_KAPPA_SRC b_k) ≠ 0 then
      if (arrInt BLOCK_KAPPA_ADJ b_k) ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    if s_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      shared := 0
      if ((arrInt BLOCK_KAPPA_SRC b_k) / 2) ≠ 0 then
        if (arrInt BLOCK_KAPPA_ADJ b_k) = 0 then
          shared := 1
        else
          pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
      if shared = 1 then
        t := (arrInt BLOCK_KAPPA_SRC b_k) - 2
        digits ← B.heapBuf SEL_TAB_NIBBLES
        B.hintDigitsExp (.heap digits.v 0 SEL_TAB_NIBBLES) (cellOf blockOff b_k) SIZE_BITS SEL_TAB_NIBBLES 4 0 (startCell := some (cellOf kb (2 + t)))
        lenG := cellOf sharedLen t
        tabEq := cellOf sharedEq t
        tabG := cellOf sharedG t
        let t6 ← B.targets [none, none]
        B.dispatchInto lenG ((List.range SIZE_BITS).map fun arm => (instName "block_selector_tab" [.L arm])) [digits.v, tabEq.v, tabG.v] t6
        eqHi := cellOf t6 0
        goff := cellOf t6 1
      else
        pure () -- no use of this definition takes this branch
      B.assertEq goff (cellOf blockOff b_k)
    selectorSum_word := eqHi
    B.copy (cellOf blockEqHi b_k) eqHi
    if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    for b_k in [109:arrInt SIDE_BLOCK_START (s_k + 1)] do
      blockHasPublic := 0
      kappaG := cellOf kb (arrInt BLOCK_KAPPA_SRC b_k)
      if (arrInt BLOCK_KAPPA_SRC b_k) ≠ 0 then
        if (arrInt BLOCK_KAPPA_ADJ b_k) ≠ 0 then
          pure () -- no use of this definition takes this branch
        else
          pure ()
      else
        pure () -- no use of this definition takes this branch
      if s_k = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        shared := 0
        if ((arrInt BLOCK_KAPPA_SRC b_k) / 2) ≠ 0 then
          if (arrInt BLOCK_KAPPA_ADJ b_k) = 0 then
            shared := 1
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if shared = 1 then
          t := (arrInt BLOCK_KAPPA_SRC b_k) - 2
          digits ← B.heapBuf SEL_TAB_NIBBLES
          B.hintDigitsExp (.heap digits.v 0 SEL_TAB_NIBBLES) (cellOf blockOff b_k) SIZE_BITS SEL_TAB_NIBBLES 4 0 (startCell := some (cellOf kb (2 + t)))
          lenG := cellOf sharedLen t
          tabEq := cellOf sharedEq t
          tabG := cellOf sharedG t
          let t6 ← B.targets [none, none]
          B.dispatchInto lenG ((List.range SIZE_BITS).map fun arm => (instName "block_selector_tab" [.L arm])) [digits.v, tabEq.v, tabG.v] t6
          eqHi := cellOf t6 0
          goff := cellOf t6 1
        else
          pure () -- no use of this definition takes this branch
        B.assertEq goff (cellOf blockOff b_k)
      selectorSum_word ← B.add selectorSum_word eqHi
      B.copy (cellOf blockEqHi b_k) eqHi
      if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    B.copy (cellOf selectorSums s_k) selectorSum_word
    B.constInto (cellOf publicEqs s_k) (lit publicEq)
    let bcMsg ← B.stackBuf 3
    for j_k in [0:3] do
      if ((4 + j_k) % 4) = 0 then
        sp ← fsPerm sp rate 4
        rate ← B.stackBuf 8
      else
        pure ()
      let (t9, t10) ← fsNext_2 rate ((4 + j_k) % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      let bcWord := t9
      cursor_ptr := t10
      B.copy (cellOf bcMsg j_k) bcWord
    let bcShare := cellOf bcMsg 0
    let (t11, t12, t13) ← fsGrindSqueeze sp rate (((4 + 2) % 4) + 1) (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs ROUND2_GRIND_BITS
    sp := t11
    let bcR := t12
    cursor_ptr := t13
    B.store bcPoint 0 bcR
    let mut bcClaim ← B.add (cellOf bcMsg 1) (← B.mul bcR (← B.add bcShare (← B.mul (← B.add (← B.const 1) bcR) (cellOf bcMsg 2))))
    let mut bfs0 := cellOf sp 8
    let mut bfs1 := cellOf sp 9
    let mut bfs2 := cellOf sp 10
    let mut bfs3 := cellOf sp 11
    let mut bfs4 := cellOf sp 12
    let x_k := 1
    let t14 ← B.call "opening_tail_round" [bfs0.v, bfs1.v, bfs2.v, bfs3.v, bfs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, bcClaim.v, tabs.v] 8
    bfs0 := t14[0]!
    bfs1 := t14[1]!
    bfs2 := t14[2]!
    bfs3 := t14[3]!
    bfs4 := t14[4]!
    cursor := t14[5]!
    bcClaim := t14[6]!
    let bcR := t14[7]!
    B.store bcPoint x_k bcR
    for x_k in [2:N_TUPLE_BITS] do
      let t14 ← B.call "opening_tail_round" [bfs0.v, bfs1.v, bfs2.v, bfs3.v, bfs4.v, cursor.v, bcClaim.v, tabs.v] 8
      bfs0 := t14[0]!
      bfs1 := t14[1]!
      bfs2 := t14[2]!
      bfs3 := t14[3]!
      bfs4 := t14[4]!
      cursor := t14[5]!
      bcClaim := t14[6]!
      let bcR := t14[7]!
      B.store bcPoint x_k bcR
    sp ← fsCap bfs0 bfs1 bfs2 bfs3 bfs4
    rate ← B.stackBuf 8
    let (t15, t16) ← fsNext rate 0 cursor
    let bcValue := t15
    cursor_ptr := t16
    let wFold ← B.stackBuf 15
    let r0 ← B.load bcPoint 0
    let mut wLo : Word := default
    for i_k in [0:N_TUPLE_SLOTS / 2] do
      wLo ← B.load fpW (2 * i_k)
      B.addInto (cellOf wFold i_k) wLo (← B.mul r0 (← B.add wLo (← B.load fpW ((2 * i_k) + 1))))
    let mut wHi : Word := default
    for j_k in [1:3] do
      let rj ← B.load bcPoint j_k
      for i_k in [0:2 ^ ((N_TUPLE_BITS - 1) - j_k)] do
        wLo := cellOf wFold ((N_TUPLE_SLOTS - (2 ^ ((N_TUPLE_BITS + 1) - j_k))) + (2 * i_k))
        wHi := cellOf wFold (((N_TUPLE_SLOTS - (2 ^ ((N_TUPLE_BITS + 1) - j_k))) + (2 * i_k)) + 1)
        B.addInto (cellOf wFold ((N_TUPLE_SLOTS - (2 ^ (N_TUPLE_BITS - j_k))) + i_k)) wLo (← B.mul rj (← B.add wLo wHi))
    let j_k := 3
    let rj ← B.load bcPoint j_k
    let i_k := 0
    wLo := cellOf wFold ((N_TUPLE_SLOTS - (2 ^ ((N_TUPLE_BITS + 1) - j_k))) + (2 * i_k))
    wHi := cellOf wFold (((N_TUPLE_SLOTS - (2 ^ ((N_TUPLE_BITS + 1) - j_k))) + (2 * i_k)) + 1)
    B.addInto (cellOf wFold ((N_TUPLE_SLOTS - (2 ^ (N_TUPLE_BITS - j_k))) + i_k)) wLo (← B.mul rj (← B.add wLo wHi))
    B.assertEq bcClaim (← B.mul (cellOf wFold (N_TUPLE_SLOTS - 2)) bcValue)
    let busTableTotal ← B.stackBuf N_GKR_SIDES
    let beta1 ← B.add beta (← B.const 1)
    let mut innerSum : Nat := default
    let mut innerSum_word : Word := default
    let mut paddingSum : Nat := default
    let mut tableSum : Nat := default
    let mut coeff : Word := default
    let mut tableSum_word : Word := default
    let mut paddingSum_word : Word := default
    let mut pushPadding : Word := default
    let mut coeff_nat : Nat := default
    let s_k := 0
    let acc := 0
    let mut acc_word : Word := default
    let b_k := 0
    if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
      innerSum := 0
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt COORD_TYPE ci) ≠ COORD_KIND_PUBLIC then
        if s_k = COUNT_SIDE then
          pure () -- no use of this definition takes this branch
        else
          innerSum_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_TYPE ci) ≠ COORD_KIND_PUBLIC then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            innerSum_word ← B.add innerSum_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
        else
          pure () -- no use of this definition takes this branch
      if s_k = COUNT_SIDE then
        pure () -- no use of this definition takes this branch
      else
        acc_word ← B.mul (cellOf blockEqHi b_k) (← B.add beta innerSum_word)
    else
      pure () -- no use of this definition takes this branch
    for b_k in [1:arrInt SIDE_BLOCK_START (s_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
        innerSum := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_TYPE ci) ≠ COORD_KIND_PUBLIC then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            innerSum_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_TYPE ci) ≠ COORD_KIND_PUBLIC then
            if s_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              innerSum_word ← B.add innerSum_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure ()
        if s_k = COUNT_SIDE then
          pure () -- no use of this definition takes this branch
        else
          acc_word ← B.add acc_word (← B.mul (cellOf blockEqHi b_k) (← B.add beta innerSum_word))
      else
        pure ()
    if s_k ≠ COUNT_SIDE then
      acc_word ← B.add acc_word (← B.mul (cellOf publicEqs s_k) bcShare)
    else
      pure () -- no use of this definition takes this branch
    if s_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      paddingSum := 0
      let t_k := 0
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:4] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.load fpW i_k)
            else
              pure ()
          tableSum_word ← B.mul (cellOf blockEqHi b_k) coeff
        else
          pure ()
      let b_k := 4
      if (arrInt BLOCK_TABLE b_k) = t_k then
        if s_k = COUNT_SIDE then
          pure () -- no use of this definition takes this branch
        else
          coeff := beta1
        for i_k in [0:3] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            if s_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              coeff ← B.add coeff (← B.mul (← B.load fpW i_k) (← B.const (arrWord COORD_PADDING ci)))
          else
            pure ()
        for i_k in [3:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            if s_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              coeff ← B.add coeff (← B.load fpW i_k)
          else
            pure ()
        tableSum_word ← B.add tableSum_word (← B.mul (cellOf blockEqHi b_k) coeff)
      else
        pure () -- no use of this definition takes this branch
      for b_k in [5:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.mul (← B.load fpW i_k) (← B.const (arrWord COORD_PADDING ci)))
            else
              pure ()
          tableSum_word ← B.add tableSum_word (← B.mul (cellOf blockEqHi b_k) coeff)
        else
          pure ()
      paddingSum_word ← B.mul (cellOf padWeight t_k) tableSum_word
      let t_k := 1
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:9] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.load fpW i_k)
            else
              pure ()
          tableSum_word ← B.mul (cellOf blockEqHi b_k) coeff
        else
          pure ()
      for b_k in [9:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.mul (← B.load fpW i_k) (← B.const (arrWord COORD_PADDING ci)))
            else
              pure ()
          tableSum_word ← B.add tableSum_word (← B.mul (cellOf blockEqHi b_k) coeff)
        else
          pure ()
      paddingSum_word ← B.add paddingSum_word (← B.mul (cellOf padWeight t_k) tableSum_word)
      let t_k := 2
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:14] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.load fpW i_k)
            else
              pure ()
          tableSum_word ← B.mul (cellOf blockEqHi b_k) coeff
        else
          pure ()
      for b_k in [14:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.mul (← B.load fpW i_k) (← B.const (arrWord COORD_PADDING ci)))
            else
              pure ()
          tableSum_word ← B.add tableSum_word (← B.mul (cellOf blockEqHi b_k) coeff)
        else
          pure ()
      paddingSum_word ← B.add paddingSum_word (← B.mul (cellOf padWeight t_k) tableSum_word)
      let t_k := 3
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:17] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.load fpW i_k)
            else
              pure ()
          tableSum_word ← B.mul (cellOf blockEqHi b_k) coeff
        else
          pure ()
      for b_k in [17:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.mul (← B.load fpW i_k) (← B.const (arrWord COORD_PADDING ci)))
            else
              pure ()
          tableSum_word ← B.add tableSum_word (← B.mul (cellOf blockEqHi b_k) coeff)
        else
          pure ()
      paddingSum_word ← B.add paddingSum_word (← B.mul (cellOf padWeight t_k) tableSum_word)
      let t_k := 4
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:22] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.load fpW i_k)
            else
              pure ()
          tableSum_word ← B.mul (cellOf blockEqHi b_k) coeff
        else
          pure ()
      for b_k in [22:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.mul (← B.load fpW i_k) (← B.const (arrWord COORD_PADDING ci)))
            else
              pure ()
          tableSum_word ← B.add tableSum_word (← B.mul (cellOf blockEqHi b_k) coeff)
        else
          pure ()
      paddingSum_word ← B.add paddingSum_word (← B.mul (cellOf padWeight t_k) tableSum_word)
      let t_k := 5
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:27] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.load fpW i_k)
            else
              pure ()
          tableSum_word ← B.mul (cellOf blockEqHi b_k) coeff
        else
          pure ()
      for b_k in [27:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            coeff := beta1
          for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
            ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
            if (arrInt COORD_PADDING ci) ≠ 0 then
              if s_k = COUNT_SIDE then
                pure () -- no use of this definition takes this branch
              else
                coeff ← B.add coeff (← B.mul (← B.load fpW i_k) (← B.const (arrWord COORD_PADDING ci)))
            else
              pure ()
          tableSum_word ← B.add tableSum_word (← B.mul (cellOf blockEqHi b_k) coeff)
        else
          pure () -- no use of this definition takes this branch
      paddingSum_word ← B.add paddingSum_word (← B.mul (cellOf padWeight t_k) tableSum_word)
      acc_word ← B.add acc_word paddingSum_word
      if s_k = PUSH_SIDE then
        pushPadding := paddingSum_word
      else
        pure () -- no use of this definition takes this branch
    acc_word ← B.add acc_word (← B.add (← B.const 1) (cellOf selectorSums s_k))
    B.addInto (cellOf busTableTotal s_k) acc_word (← B.load gkrLeaves s_k)
    let s_k := 1
    let acc := 0
    let b_k := 54
    if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
      innerSum := 0
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt COORD_TYPE ci) ≠ COORD_KIND_PUBLIC then
        if s_k = COUNT_SIDE then
          pure () -- no use of this definition takes this branch
        else
          innerSum_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_TYPE ci) ≠ COORD_KIND_PUBLIC then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            innerSum_word ← B.add innerSum_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
        else
          pure () -- no use of this definition takes this branch
      if s_k = COUNT_SIDE then
        pure () -- no use of this definition takes this branch
      else
        acc_word ← B.mul (cellOf blockEqHi b_k) (← B.add beta innerSum_word)
    else
      pure () -- no use of this definition takes this branch
    for b_k in [55:arrInt SIDE_BLOCK_START (s_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
        innerSum := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_TYPE ci) ≠ COORD_KIND_PUBLIC then
          if s_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            innerSum_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_TYPE ci) ≠ COORD_KIND_PUBLIC then
            if s_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              innerSum_word ← B.add innerSum_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure ()
        if s_k = COUNT_SIDE then
          pure () -- no use of this definition takes this branch
        else
          acc_word ← B.add acc_word (← B.mul (cellOf blockEqHi b_k) (← B.add beta innerSum_word))
      else
        pure ()
    if s_k ≠ COUNT_SIDE then
      acc_word ← B.add acc_word (← B.mul (cellOf publicEqs s_k) bcShare)
    else
      pure () -- no use of this definition takes this branch
    if s_k = PULL_SIDE then
      acc_word ← B.add acc_word pushPadding
    else
      pure () -- no use of this definition takes this branch
    acc_word ← B.add acc_word (← B.add (← B.const 1) (cellOf selectorSums s_k))
    B.addInto (cellOf busTableTotal s_k) acc_word (← B.load gkrLeaves s_k)
    let s_k := 2
    let acc := 0
    for b_k in [arrInt SIDE_BLOCK_START s_k:arrInt SIDE_BLOCK_START (s_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = NO_TABLE then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    if s_k ≠ COUNT_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if s_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      paddingSum := 0
      let t_k := 0
      tableSum := 0
      let b_k := 108
      if (arrInt BLOCK_TABLE b_k) = t_k then
        if s_k = COUNT_SIDE then
          coeff_nat := 1
        else
          pure () -- no use of this definition takes this branch
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt COORD_PADDING ci) ≠ 0 then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        tableSum_word := cellOf blockEqHi b_k
      else
        pure () -- no use of this definition takes this branch
      for b_k in [109:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word ← B.add tableSum_word (cellOf blockEqHi b_k)
        else
          pure ()
      paddingSum_word ← B.mul (cellOf padWeight t_k) tableSum_word
      let t_k := 1
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:113] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word := cellOf blockEqHi b_k
        else
          pure ()
      for b_k in [113:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word ← B.add tableSum_word (cellOf blockEqHi b_k)
        else
          pure ()
      paddingSum_word ← B.add paddingSum_word (← B.mul (cellOf padWeight t_k) tableSum_word)
      let t_k := 2
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:117] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word := cellOf blockEqHi b_k
        else
          pure ()
      for b_k in [117:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word ← B.add tableSum_word (cellOf blockEqHi b_k)
        else
          pure ()
      paddingSum_word ← B.add paddingSum_word (← B.mul (cellOf padWeight t_k) tableSum_word)
      let t_k := 3
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:119] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word := cellOf blockEqHi b_k
        else
          pure ()
      for b_k in [119:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word ← B.add tableSum_word (cellOf blockEqHi b_k)
        else
          pure ()
      paddingSum_word ← B.add paddingSum_word (← B.mul (cellOf padWeight t_k) tableSum_word)
      let t_k := 4
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:123] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word := cellOf blockEqHi b_k
        else
          pure ()
      for b_k in [123:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word ← B.add tableSum_word (cellOf blockEqHi b_k)
        else
          pure ()
      paddingSum_word ← B.add paddingSum_word (← B.mul (cellOf padWeight t_k) tableSum_word)
      let t_k := 5
      tableSum := 0
      for b_k in [arrInt SIDE_BLOCK_START s_k:127] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word := cellOf blockEqHi b_k
        else
          pure ()
      for b_k in [127:arrInt SIDE_BLOCK_START (s_k + 1)] do
        if (arrInt BLOCK_TABLE b_k) = t_k then
          if s_k = COUNT_SIDE then
            coeff_nat := 1
          else
            pure () -- no use of this definition takes this branch
          let i_k := 0
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt COORD_PADDING ci) ≠ 0 then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          tableSum_word ← B.add tableSum_word (cellOf blockEqHi b_k)
        else
          pure () -- no use of this definition takes this branch
      paddingSum_word ← B.add paddingSum_word (← B.mul (cellOf padWeight t_k) tableSum_word)
      acc_word := paddingSum_word
      if s_k = PUSH_SIDE then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    acc_word ← B.add acc_word (← B.add (← B.const 1) (cellOf selectorSums s_k))
    B.addInto (cellOf busTableTotal s_k) acc_word (← B.load gkrLeaves s_k)
    let mut claimIdx := N_BUS_CLAIMS
    let gZcN ← hinted (B.witnessCell "zc_tau_max")
    let zcIsATau := 1
    let mut zcIsATau_word : Word := default
    let t_k := 0
    tauG := cellOf kb (2 + t_k)
    let t17 ← B.const (gpowE (COUNT_BITS - 1))
    let _ ← B.rangeCheckK (← B.fdiv gZcN tauG) t17
    zcIsATau_word ← B.add gZcN tauG
    for t_k in [1:N_TABLES] do
      tauG := cellOf kb (2 + t_k)
      let t17 ← B.const (gpowE (COUNT_BITS - 1))
      let _ ← B.rangeCheckK (← B.fdiv gZcN tauG) t17
      zcIsATau_word ← B.mul zcIsATau_word (← B.add gZcN tauG)
    B.assertEq zcIsATau_word (← B.const 0)
    let t18 ← B.const (gpowE (COUNT_BITS - 1))
    let _ ← B.rangeCheckK (← B.fdiv gBusMu gZcN) t18
    let (t19, t20, t21) ← fsGrindSqueeze sp rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs XI_GRIND_BITS
    sp := t19
    let zcXi := t20
    cursor_ptr := t21
    let zcXiPows ← B.stackBuf N_ETA_POWS
    B.constInto (cellOf zcXiPows 0) 1
    for k_k in [1:N_ETA_POWS] do
      B.mulInto (cellOf zcXiPows k_k) (cellOf zcXiPows (k_k - 1)) zcXi
    let busTarget := 0
    let mut busTarget_word : Word := default
    let sd_k := 0
    busTarget_word ← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) (cellOf busTableTotal sd_k)
    for sd_k in [1:N_GKR_SIDES] do
      busTarget_word ← B.add busTarget_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) (cellOf busTableTotal sd_k))
    let zcRounds ← B.heapBufDyn (← B.pow (← B.shifted gZcN 1) ROUND_SLOTS)
    let zcCprod ← B.heapBufDyn (← B.shifted gZcN 1)
    fsStore_2 zcRounds ROUND_FS 1 sp
    B.store zcRounds ROUND_CURSOR (← B.shifted cursor_ptr.base cursor_ptr.exp)
    B.store zcRounds ROUND_CLAIM busTarget_word
    B.store zcCprod 0 (← B.const 1)
    B.loopRtF 0 (pure gZcN) 5 (pure ([zcRounds.v, tabs.v, chi.v, gZcN.v, zcCprod.v])) fun xk caps => do
      let zcRounds := cellOf caps 0
      let tabs := cellOf caps 1
      let chi := cellOf caps 2
      let gZcN := cellOf caps 3
      let zcCprod := cellOf caps 4
      let rd ← B.mul zcRounds (← B.pow xk ROUND_SLOTS)
      let t0 ← B.call "sumcheck_round4" [rd.v, (← B.load rd ROUND_CURSOR).v, (← B.load rd ROUND_CLAIM).v, tabs.v] 3
      let ncur := t0[0]!
      let nclaim := t0[1]!
      let rk := t0[2]!
      B.store (← B.mul chi (← B.fdiv (← B.mul gZcN (← B.const (lit INV_GEN))) xk)) 0 rk
      let nxt : Shifted := ⟨rd, ROUND_SLOTS⟩
      B.store nxt.base (nxt.exp + ROUND_CURSOR) ncur
      B.store nxt.base (nxt.exp + ROUND_CLAIM) nclaim
      let t1 ← B.mul (← B.load (← B.mul zcCprod xk) 0) rk
      B.store (← B.mul zcCprod xk) 1 t1
    let zcLast ← B.mul zcRounds (← B.pow gZcN ROUND_SLOTS)
    sp ← fsLoad zcLast ROUND_FS 1
    rate ← B.stackBuf 8
    cursor ← B.load zcLast ROUND_CURSOR
    let claim ← B.load zcLast ROUND_CLAIM
    let zcPeq ← B.heapBufDyn (← B.shifted gZcN 1)
    let _ ← B.call "eq_prefix_chain" [zcPeq.v, (← B.const 1).v, chi.v, zeta1.v, gZcN.v] 0
    let airAcc := 0
    let colEvalWords := cursor
    let mut e : Word := default
    let mut nTerms : Nat := default
    let mut first : Nat := default
    let mut cv : Nat := default
    let mut tj : Nat := default
    let mut cv_word : Word := default
    let mut form : Nat := default
    let mut inner : Nat := default
    let mut inner_word : Word := default
    let mut form_word : Word := default
    let mut pushForm : Word := default
    let mut airAcc_word : Word := default
    let mut c : Word := default
    let mut b : Word := default
    let t_k := 0
    tauG := cellOf kb (2 + t_k)
    let colEvals ← B.stackBuf TABLE_COLS_CAP
    let pos_k := 0
    if (pos_k % 4) = 0 then
      if pos_k ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    let (t22, t23) ← fsNext rate (pos_k % 4) cursor
    e := t22
    cursor_ptr := t23
    B.copy (cellOf colEvals (pos_k - (arrInt TABLE_COL_BASE t_k))) e
    claimIdx := claimIdx + 1
    for pos_k in [1:(arrInt TABLE_COL_BASE t_k) + (arrInt N_TABLE_COLS t_k)] do
      if (pos_k % 4) = 0 then
        if pos_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      let (t22, t23) ← fsNext_2 rate (pos_k % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      e := t22
      cursor_ptr := t23
      B.copy (cellOf colEvals (pos_k - (arrInt TABLE_COL_BASE t_k))) e
      claimIdx := claimIdx + 1
    let constraintEval := 0
    if t_k = TABLE_JUMP then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    for b_k in [0:4] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure ()
    let b_k := 4
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:3] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      let i_k := 3
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [4:7] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      for i_k in [7:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [5:7] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
    for b_k in [7:57] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:3] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
        for i_k in [3:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure () -- no use of this definition takes this branch
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            let j_k := 1
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word ← B.add cv_word (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure () -- no use of this definition takes this branch
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [57:108] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
            first := arrInt COORD_DIFF_OFF ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure () -- no use of this definition takes this branch
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure ()
      else
        pure ()
    for b_k in [108:N_BLOCKS] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    let mut constraintEval_word : Word := default
    let sd_k := 0
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:4] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word)
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [4:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word))
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pushForm := form_word
    else
      pure () -- no use of this definition takes this branch
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word
    let sd_k := 1
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:58] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [58:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      form_word ← B.add pushForm form_word
    else
      pure () -- no use of this definition takes this branch
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    let sd_k := 2
    form := 0
    let b_k := 108
    if (arrInt BLOCK_TABLE b_k) = t_k then
      inner := 0
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if sd_k = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
      if nTerms ≠ 0 then
        if sd_k = COUNT_SIDE then
          inner_word := cellOf coordVals ci
        else
          pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
      if sd_k = PUSH_SIDE then
        pure () -- no use of this definition takes this branch
      else
        form_word ← B.mul (cellOf blockEqHi b_k) inner_word
    else
      pure () -- no use of this definition takes this branch
    for b_k in [109:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    airAcc_word ← B.mul (← B.mul (← B.load (← B.mul zcCprod (← B.fdiv gZcN tauG)) 0) (← B.load (← B.mul zcPeq tauG) 0)) constraintEval_word
    let t_k := 1
    tauG := cellOf kb (2 + t_k)
    let colEvals ← B.stackBuf TABLE_COLS_CAP
    for pos_k in [arrInt TABLE_COL_BASE t_k:(arrInt TABLE_COL_BASE t_k) + (arrInt N_TABLE_COLS t_k)] do
      if (pos_k % 4) = 0 then
        if pos_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      let (t22, t23) ← fsNext_2 rate (pos_k % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      e := t22
      cursor_ptr := t23
      B.copy (cellOf colEvals (pos_k - (arrInt TABLE_COL_BASE t_k))) e
      claimIdx := claimIdx + 1
    let constraintEval := 0
    if t_k = TABLE_JUMP then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    for b_k in [0:9] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure ()
    let b_k := 9
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:3] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      let i_k := 3
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [4:7] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      for i_k in [7:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [10:12] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
    for b_k in [12:62] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:3] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
        let i_k := 3
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
          else
            pure () -- no use of this definition takes this branch
          let j_k := 1
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
          else
            pure () -- no use of this definition takes this branch
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
        let i_k := 4
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
          else
            pure () -- no use of this definition takes this branch
          let j_k := 1
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
          else
            pure () -- no use of this definition takes this branch
          let j_k := 2
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.add cv_word (← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))))
          else
            pure () -- no use of this definition takes this branch
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [62:112] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
            first := arrInt COORD_DIFF_OFF ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure () -- no use of this definition takes this branch
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure ()
      else
        pure ()
    for b_k in [112:N_BLOCKS] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    let sd_k := 0
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:9] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word)
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [9:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word))
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pushForm := form_word
    else
      pure () -- no use of this definition takes this branch
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word
    let sd_k := 1
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:63] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [63:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      form_word ← B.add pushForm form_word
    else
      pure () -- no use of this definition takes this branch
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    let sd_k := 2
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:113] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [113:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    airAcc_word ← B.add airAcc_word (← B.mul (← B.mul (← B.load (← B.mul zcCprod (← B.fdiv gZcN tauG)) 0) (← B.load (← B.mul zcPeq tauG) 0)) constraintEval_word)
    let t_k := 2
    tauG := cellOf kb (2 + t_k)
    let colEvals ← B.stackBuf TABLE_COLS_CAP
    for pos_k in [arrInt TABLE_COL_BASE t_k:(arrInt TABLE_COL_BASE t_k) + (arrInt N_TABLE_COLS t_k)] do
      if (pos_k % 4) = 0 then
        if pos_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      let (t22, t23) ← fsNext_2 rate (pos_k % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      e := t22
      cursor_ptr := t23
      B.copy (cellOf colEvals (pos_k - (arrInt TABLE_COL_BASE t_k))) e
      claimIdx := claimIdx + 1
    let constraintEval := 0
    if t_k = TABLE_JUMP then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    for b_k in [0:14] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure ()
    let b_k := 14
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:3] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      let i_k := 3
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [4:7] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      for i_k in [7:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [15:67] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [67:116] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
            first := arrInt COORD_DIFF_OFF ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure () -- no use of this definition takes this branch
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure ()
      else
        pure ()
    for b_k in [116:N_BLOCKS] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    let sd_k := 0
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:14] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word)
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [14:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word))
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pushForm := form_word
    else
      pure () -- no use of this definition takes this branch
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word
    let sd_k := 1
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:68] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [68:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      form_word ← B.add pushForm form_word
    else
      pure () -- no use of this definition takes this branch
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    let sd_k := 2
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:117] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [117:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    airAcc_word ← B.add airAcc_word (← B.mul (← B.mul (← B.load (← B.mul zcCprod (← B.fdiv gZcN tauG)) 0) (← B.load (← B.mul zcPeq tauG) 0)) constraintEval_word)
    let t_k := 3
    tauG := cellOf kb (2 + t_k)
    let colEvals ← B.stackBuf TABLE_COLS_CAP
    for pos_k in [arrInt TABLE_COL_BASE t_k:(arrInt TABLE_COL_BASE t_k) + (arrInt N_TABLE_COLS t_k)] do
      if (pos_k % 4) = 0 then
        if pos_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      let (t22, t23) ← fsNext_2 rate (pos_k % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      e := t22
      cursor_ptr := t23
      B.copy (cellOf colEvals (pos_k - (arrInt TABLE_COL_BASE t_k))) e
      claimIdx := claimIdx + 1
    let constraintEval := 0
    if t_k = TABLE_JUMP then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    for b_k in [0:17] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure ()
    let b_k := 17
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:3] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      let i_k := 3
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [4:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    let b_k := 18
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:4] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      let i_k := 4
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    let b_k := 19
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:3] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      let i_k := 3
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        for j_k in [0:3] do
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
          else
            pure ()
        let j_k := 3
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          cv_word ← B.add cv_word (← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))))
        else
          pure () -- no use of this definition takes this branch
        let j_k := 4
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
        else
          pure () -- no use of this definition takes this branch
        B.copy (cellOf coordVals ci) cv_word
      else
        pure () -- no use of this definition takes this branch
      let i_k := 4
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        for j_k in [0:nTerms] do
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
          else
            pure ()
        B.copy (cellOf coordVals ci) cv_word
      else
        pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [20:70] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [70:118] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
            first := arrInt COORD_DIFF_OFF ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure () -- no use of this definition takes this branch
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure ()
      else
        pure ()
    for b_k in [118:N_BLOCKS] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    let sd_k := 0
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:17] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word)
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [17:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word))
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pushForm := form_word
    else
      pure () -- no use of this definition takes this branch
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word
    let sd_k := 1
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:71] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [71:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      form_word ← B.add pushForm form_word
    else
      pure () -- no use of this definition takes this branch
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    let sd_k := 2
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:119] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [119:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    airAcc_word ← B.add airAcc_word (← B.mul (← B.mul (← B.load (← B.mul zcCprod (← B.fdiv gZcN tauG)) 0) (← B.load (← B.mul zcPeq tauG) 0)) constraintEval_word)
    let t_k := 4
    tauG := cellOf kb (2 + t_k)
    let colEvals ← B.stackBuf TABLE_COLS_CAP
    for pos_k in [arrInt TABLE_COL_BASE t_k:(arrInt TABLE_COL_BASE t_k) + (arrInt N_TABLE_COLS t_k)] do
      if (pos_k % 4) = 0 then
        if pos_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      let (t22, t23) ← fsNext_2 rate (pos_k % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      e := t22
      cursor_ptr := t23
      B.copy (cellOf colEvals (pos_k - (arrInt TABLE_COL_BASE t_k))) e
      claimIdx := claimIdx + 1
    let constraintEval := 0
    if t_k = TABLE_JUMP then
      c := cellOf colEvals 5
      b := cellOf colEvals 13
      constraintEval_word ← B.mul (cellOf zcXiPows (arrInt ETA_OFFSET t_k)) (← B.add b (← B.mul c (cellOf colEvals 12)))
      constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows ((arrInt ETA_OFFSET t_k) + 1)) (← B.mul c (← B.add b (← B.const 1))))
    else
      pure () -- no use of this definition takes this branch
    for b_k in [0:22] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
          else
            pure () -- no use of this definition takes this branch
          for j_k in [1:nTerms] do
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.add cv_word (← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj)))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.add cv_word (← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))))
            else
              pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
        let i_k := 2
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
          else
            pure () -- no use of this definition takes this branch
          for j_k in [1:nTerms] do
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word ← B.add cv_word (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
            else
              pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    let b_k := 22
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:3] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      let i_k := 3
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [4:7] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      for i_k in [7:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [23:75] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:4] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
        let i_k := 4
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    let b_k := 75
    if (arrInt BLOCK_TABLE b_k) = t_k then
      for i_k in [0:2] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          nTerms := arrInt COORD_DIFF_COUNT ci
          first := arrInt COORD_DIFF_OFF ci
        else
          pure () -- no use of this definition takes this branch
        if nTerms ≠ 0 then
          cv := 0
          for j_k in [0:2] do
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.add cv_word (← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))))
            else
              pure ()
          let j_k := 2
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
          else
            pure () -- no use of this definition takes this branch
          B.copy (cellOf coordVals ci) cv_word
        else
          pure ()
      let i_k := 2
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        nTerms := arrInt COORD_DIFF_COUNT ci
        first := arrInt COORD_DIFF_OFF ci
      else
        pure () -- no use of this definition takes this branch
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
        else
          pure () -- no use of this definition takes this branch
        let j_k := 1
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
        else
          pure () -- no use of this definition takes this branch
        B.copy (cellOf coordVals ci) cv_word
      else
        pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [76:122] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
            first := arrInt COORD_DIFF_OFF ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure () -- no use of this definition takes this branch
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure ()
      else
        pure ()
    for b_k in [122:N_BLOCKS] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    let sd_k := 0
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:22] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word)
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [22:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word))
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pushForm := form_word
    else
      pure () -- no use of this definition takes this branch
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    let sd_k := 1
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:76] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:2] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        let i_k := 2
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          nTerms := arrInt COORD_DIFF_COUNT ci
        else
          pure () -- no use of this definition takes this branch
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [76:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      form_word ← B.add pushForm form_word
    else
      pure () -- no use of this definition takes this branch
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    let sd_k := 2
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:123] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [123:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure ()
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    airAcc_word ← B.add airAcc_word (← B.mul (← B.mul (← B.load (← B.mul zcCprod (← B.fdiv gZcN tauG)) 0) (← B.load (← B.mul zcPeq tauG) 0)) constraintEval_word)
    let t_k := 5
    tauG := cellOf kb (2 + t_k)
    let colEvals ← B.stackBuf TABLE_COLS_CAP
    for pos_k in [arrInt TABLE_COL_BASE t_k:(arrInt TABLE_COL_BASE t_k) + (arrInt N_TABLE_COLS t_k)] do
      if (pos_k % 4) = 0 then
        if pos_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      let (t22, t23) ← fsNext_2 rate (pos_k % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      e := t22
      cursor_ptr := t23
      B.copy (cellOf colEvals (pos_k - (arrInt TABLE_COL_BASE t_k))) e
      claimIdx := claimIdx + 1
    let constraintEval := 0
    if t_k = TABLE_JUMP then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    for b_k in [0:27] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure ()
    let b_k := 27
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:3] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      let i_k := 3
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [4:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [28:33] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:3] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
        for i_k in [3:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            for j_k in [0:nTerms] do
              tj := first + j_k
              if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
                pure () -- no use of this definition takes this branch
              else
                pure ()
              if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
                cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
              else
                pure ()
              if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
                pure () -- no use of this definition takes this branch
              else
                pure ()
              if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
                cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
              else
                pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
    for b_k in [33:36] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:3] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
        for i_k in [3:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            for j_k in [0:nTerms] do
              tj := first + j_k
              if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
                pure () -- no use of this definition takes this branch
              else
                pure ()
              if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
                cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
              else
                pure ()
              if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
                pure () -- no use of this definition takes this branch
              else
                pure ()
              if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
                cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
              else
                pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
    let b_k := 36
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:3] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      for i_k in [3:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          for j_k in [0:nTerms] do
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
            else
              pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    let b_k := 37
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [38:41] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
    let b_k := 41
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      for i_k in [1:3] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      for i_k in [3:arrInt BLOCK_COORD_COUNT b_k] do
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          for j_k in [0:nTerms] do
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
            else
              pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [42:49] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
          else
            pure () -- no use of this definition takes this branch
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
        let i_k := 2
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          for j_k in [0:2] do
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.add cv_word (← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))))
            else
              pure ()
          let j_k := 2
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
          else
            pure () -- no use of this definition takes this branch
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
        for i_k in [3:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            for j_k in [0:nTerms] do
              tj := first + j_k
              if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
                pure () -- no use of this definition takes this branch
              else
                pure ()
              if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
                cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
              else
                pure ()
              if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
                pure () -- no use of this definition takes this branch
              else
                pure ()
              if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
                cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
              else
                pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
    let b_k := 49
    if (arrInt BLOCK_TABLE b_k) = t_k then
      let i_k := 0
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          cv := cv + (arrInt TERM_CONST tj)
        else
          pure () -- no use of this definition takes this branch
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        B.constInto (cellOf coordVals ci) (lit cv)
      else
        pure () -- no use of this definition takes this branch
      let i_k := 1
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
        else
          pure () -- no use of this definition takes this branch
        B.copy (cellOf coordVals ci) cv_word
      else
        pure () -- no use of this definition takes this branch
      let i_k := 2
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        for j_k in [0:2] do
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.add cv_word (← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))))
          else
            pure ()
        let j_k := 2
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
        else
          pure () -- no use of this definition takes this branch
        B.copy (cellOf coordVals ci) cv_word
      else
        pure () -- no use of this definition takes this branch
      let i_k := 3
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        for j_k in [0:nTerms] do
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
          else
            pure ()
        B.copy (cellOf coordVals ci) cv_word
      else
        pure () -- no use of this definition takes this branch
      let i_k := 4
      ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
      if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
        pure () -- no use of this definition takes this branch
      else
        nTerms := arrInt COORD_TERM_COUNT ci
        first := arrInt COORD_TERM_OFF ci
      if nTerms ≠ 0 then
        cv := 0
        let j_k := 0
        tj := first + j_k
        if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
          cv_word ← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))
        else
          pure () -- no use of this definition takes this branch
        B.copy (cellOf coordVals ci) cv_word
      else
        pure () -- no use of this definition takes this branch
    else
      pure () -- no use of this definition takes this branch
    for b_k in [50:80] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            cv := cv + (arrInt TERM_CONST tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.constInto (cellOf coordVals ci) (lit cv)
        else
          pure () -- no use of this definition takes this branch
        let i_k := 1
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
          else
            pure () -- no use of this definition takes this branch
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
        let i_k := 2
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          for j_k in [0:2] do
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.add cv_word (← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj))))
            else
              pure ()
          let j_k := 2
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            cv_word ← B.add cv_word (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
          else
            pure () -- no use of this definition takes this branch
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
        for i_k in [3:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
            first := arrInt COORD_TERM_OFF ci
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
            else
              pure () -- no use of this definition takes this branch
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [80:126] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
            first := arrInt COORD_DIFF_OFF ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            cv := 0
            let j_k := 0
            tj := first + j_k
            if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
              pure () -- no use of this definition takes this branch
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (cellOf colEvals (arrInt TERM_COL_A tj))
            else
              pure ()
            if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
              cv_word ← B.mul (← B.const (arrWord TERM_CONST tj)) (← B.mul (cellOf colEvals (arrInt TERM_COL_A tj)) (cellOf colEvals (arrInt TERM_COL_B tj)))
            else
              pure ()
            B.copy (cellOf coordVals ci) cv_word
          else
            pure ()
      else
        pure ()
    for b_k in [126:N_BLOCKS] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if (arrInt BLOCK_SIDE b_k) = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
          first := arrInt COORD_TERM_OFF ci
        if nTerms ≠ 0 then
          cv := 0
          let j_k := 0
          tj := first + j_k
          if (arrInt TERM_TYPE tj) = COORD_KIND_CONST then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_COL then
            cv_word := cellOf colEvals (arrInt TERM_COL_A tj)
          else
            pure () -- no use of this definition takes this branch
          if (arrInt TERM_TYPE tj) = COORD_KIND_GCOL then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          if (arrInt TERM_TYPE tj) = COORD_KIND_PROD then
            pure () -- no use of this definition takes this branch
          else
            pure ()
          B.copy (cellOf coordVals ci) cv_word
        else
          pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
    let sd_k := 0
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:27] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word)
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    for b_k in [27:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            pure () -- no use of this definition takes this branch
          else
            inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
        else
          pure () -- no use of this definition takes this branch
        for i_k in [1:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            pure () -- no use of this definition takes this branch
          else
            nTerms := arrInt COORD_TERM_COUNT ci
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.add inner_word (← B.mul (← B.load fpW i_k) (cellOf coordVals ci))
          else
            pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) (← B.add beta inner_word))
        else
          pure () -- no use of this definition takes this branch
      else
        pure () -- no use of this definition takes this branch
    if sd_k = PUSH_SIDE then
      pushForm := form_word
    else
      pure () -- no use of this definition takes this branch
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word
    let sd_k := 1
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:81] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [81:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        for i_k in [0:arrInt BLOCK_COORD_COUNT b_k] do
          ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
          if sd_k = PULL_SIDE then
            nTerms := arrInt COORD_DIFF_COUNT ci
          else
            pure () -- no use of this definition takes this branch
          if nTerms ≠ 0 then
            if sd_k = COUNT_SIDE then
              pure () -- no use of this definition takes this branch
            else
              inner_word ← B.mul (← B.load fpW i_k) (cellOf coordVals ci)
          else
            pure ()
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure () -- no use of this definition takes this branch
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      form_word ← B.add pushForm form_word
    else
      pure () -- no use of this definition takes this branch
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    let sd_k := 2
    form := 0
    for b_k in [arrInt SIDE_BLOCK_START sd_k:127] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.mul (cellOf blockEqHi b_k) inner_word
      else
        pure ()
    for b_k in [127:arrInt SIDE_BLOCK_START (sd_k + 1)] do
      if (arrInt BLOCK_TABLE b_k) = t_k then
        inner := 0
        let i_k := 0
        ci := (arrInt BLOCK_COORD_OFF b_k) + i_k
        if sd_k = PULL_SIDE then
          pure () -- no use of this definition takes this branch
        else
          nTerms := arrInt COORD_TERM_COUNT ci
        if nTerms ≠ 0 then
          if sd_k = COUNT_SIDE then
            inner_word := cellOf coordVals ci
          else
            pure () -- no use of this definition takes this branch
        else
          pure () -- no use of this definition takes this branch
        if sd_k = PUSH_SIDE then
          pure () -- no use of this definition takes this branch
        else
          form_word ← B.add form_word (← B.mul (cellOf blockEqHi b_k) inner_word)
      else
        pure () -- no use of this definition takes this branch
    if sd_k = PUSH_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    if sd_k = PULL_SIDE then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    constraintEval_word ← B.add constraintEval_word (← B.mul (cellOf zcXiPows (ETA_FORM_BASE + sd_k)) form_word)
    airAcc_word ← B.add airAcc_word (← B.mul (← B.mul (← B.load (← B.mul zcCprod (← B.fdiv gZcN tauG)) 0) (← B.load (← B.mul zcPeq tauG) 0)) constraintEval_word)
    B.assertEq airAcc_word claim
    let (t24, t25) ← squeeze sp rate (((N_COL_EVALS + 3) % 4) + 1)
    sp := t24
    let rm := t25
    let (t26, t27) ← splitLimbs pi0
    let lo0 := t26
    let hi0 := t27
    let (t28, t29) ← splitLimbs pi1
    let lo1 := t28
    let hi1 := t29
    B.store claimPool claimIdx (← B.add lo0 (← B.mul rm (← B.add lo0 lo1)))
    claimIdx := claimIdx + 1
    B.store claimPool claimIdx (← B.add hi0 (← B.mul rm (← B.add hi0 hi1)))
    claimIdx := claimIdx + 1
    let t30 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted cursor_ptr.base cursor_ptr.exp)
    return [.v (cellOf sp 8).v] ++ [.v (cellOf sp 9).v] ++ [.v (cellOf sp 10).v] ++ [.v (cellOf sp 11).v] ++ [.v (cellOf sp 12).v] ++ [.into t30] ++ [.v gZcN.v] ++ [.v bcValue.v] ++ [.v rm.v] ++ [.v colEvalWords.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `verify_keccak` (`guests/lean_ethereum.py`, line 3117):

```
def verify_keccak(fs0, fs1, fs2, fs3, fs4, cursor, tau_g, chi, output_lanes, z_vals, slices, tabs):
    # KECCAK validity (verifier::keccak::verify_keccak): a random claim on every segment's output,
    # KECCAK_DEPTH layers down to the committed inputs, every segment at once. The
    # last segment's output is the permutation's: the table's claims on its output
    # lanes, `output_lanes`, at the table's point chi[..tau], give that part of the
    # claim, and the prover sends the committed outputs' part. It leaves two
    # openings of q_keccak, at the two points written to `z_vals` (tau +
    # QKECCAK_SLOT_LOG coordinates each, QKECCAK_VARS_CAP apart): the committed
    # outputs as words at the first, returned, and the 64 `slices` at the second.
    # tau >= FLOORS[TABLE_KECCAK] is certified, so the pack count is a real count.
    # The ring-switching map's challenges are drawn after it, by the caller, under
    # the batch grind.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    no_rate = StackBuf(8)
    pack_g = tau_g * INV_GEN ** KECCAK_PACK_LOG
    y_g = pack_g * GEN ** KECCAK_SEG_LOG
    # A layer runs y = log(y_g) rounds KR_STEP at a time: y_g = step_g^KR_STEP rem_g,
    # from y's bits, pinned boolean and tied back (y = tau - 3 < 2^5 as tau < COUNT_BITS).
    y_bits = StackBuf(5)
    hint_decompose_bits_exponent(y_bits, y_g, 5)
    for j in unroll(0, 5):
        bit = y_bits[j]
        y_bits[j] = bit * bit
    step_g = GEN ** 0
    for j in unroll(KR_STEP_LOG, 5):
        step_g *= 1 + y_bits[j] * (1 + GEN ** (2 ** (j - KR_STEP_LOG)))
    rem_g = GEN ** 0
    for j in unroll(0, KR_STEP_LOG):
        rem_g *= 1 + y_bits[j] * (1 + GEN ** (2 ** j))
    assert step_g ** KR_STEP * rem_g == y_g
    out_point = z_vals
    in_point = z_vals * GEN ** QKECCAK_VARS_CAP
    for i in unroll(0, KECCAK_PACK_LOG):
        out_point[GEN ** i] = chi[GEN ** i]
    # The claim's point: chi's pack coordinates, then a fresh segment.
    point = HeapBuf(y_g)
    chi_pack = chi * GEN ** KECCAK_PACK_LOG
    for xt in mul_range(1, pack_g):
        point[xt] = chi_pack[xt]
    # One message, the segment then the lane, after its grind: the first claim is
    # multilinear in them.
    segment = point * pack_g
    sp, r, cursor = fs_grind_squeeze(sp, no_rate, 0, cursor, tabs, KECCAK_SEG_GRIND_BITS)
    segment[GEN ** 0] = r
    for i in unroll(1, KECCAK_SEG_LOG):
        sp, r = squeeze(sp, no_rate, 0)
        segment[GEN ** i] = r
    r_lane = HeapBuf(KECCAK_LANE_BITS)
    for i in unroll(0, KECCAK_LANE_BITS):
        sp, r = squeeze(sp, no_rate, 0)
        r_lane[GEN ** i] = r
    # The committed outputs' value waits in the sponge until the first layer's words.
    value_rate = StackBuf(8)
    value, cursor = fs_next(value_rate, 0, cursor)
    fs0 = sp[8]
    fs1 = sp[9]
    fs2 = sp[10]
    fs3 = sp[11]
    fs4 = sp[12]

    # The first claim combines the output lanes as words: instance weights
    # eq(chi_low), position weights eq(r_lane) on the lane times x^z on the bit.
    claims = HeapBuf((KECCAK_DEPTH + 1) * KC_SIZE)
    claims[GEN ** KC_KAPPA] = 1
    claims[GEN ** KC_POINT] = point
    mu_tree = HeapBuf(2 ** (KECCAK_PACK_LOG + 1) - 2)
    eqtree(out_point, mu_tree, KECCAK_PACK_LOG)
    for i in unroll(0, KECCAK_PACK):
        claims[GEN ** (KC_MU + i)] = mu_tree[GEN ** (2 ** KECCAK_PACK_LOG - 2 + i)]
    lane_tree = HeapBuf(2 ** (KECCAK_LANE_BITS + 1) - 2)
    eqtree(r_lane, lane_tree, KECCAK_LANE_BITS)
    first_lanes = lane_tree * GEN ** (2 ** KECCAK_LANE_BITS - 2)
    claims[GEN ** KC_LANES] = first_lanes
    # `value` is the committed outputs' part; the last segment's is the table's.
    segment_tree = HeapBuf(2 ** (KECCAK_SEG_LOG + 1) - 2)
    eqtree(segment, segment_tree, KECCAK_SEG_LOG)
    output = 0
    for lane in unroll(0, KECCAK_LANES):
        output += first_lanes[GEN ** lane] * output_lanes[GEN ** lane]
    claims[GEN ** KC_VALUE] = value + segment_tree[GEN ** (2 ** KECCAK_SEG_LOG - 2 + KECCAK_SEGMENTS - 1)] * output

    for step in unroll(0, KECCAK_DEPTH):
        claim = claims * GEN ** (step * KC_SIZE)
        # iota flips known positions of lane 0, per segment a different round's.
        claim_point = claim[GEN ** KC_POINT]
        segment_tree = StackBuf(2 ** (KECCAK_SEG_LOG + 1) - 2)
        eqtree_frame(claim_point * pack_g, segment_tree, KECCAK_SEG_LOG, 2 ** KECCAK_SEG_LOG)
        # The claim's weights where iota can flip, slice 2^i - 1 of lane 0, for the
        # i this step's round constants set: the first claim's are a word's,
        # x^(2^i - 1) on lane 0; a later claim's come from its lane and slice
        # weights through the linear layer's transpose.
        flips = StackBuf(KECCAK_IOTA_BITS)
        for i in unroll(0, KECCAK_IOTA_BITS):
            used = 0
            for t in unroll(KECCAK_IOTA_START[KECCAK_SEGMENTS * step], KECCAK_IOTA_START[KECCAK_SEGMENTS * step + KECCAK_SEGMENTS]):
                if const(KECCAK_IOTA_IDX[t] == i):
                    used = 1
            if const(used == 1):
                if step == 0:
                    flips[i] = first_lanes[GEN ** 0] * GEN ** (2 ** i - 1)
                else:
                    claim_flips = claim[GEN ** KC_FLIPS]
                    flips[i] = claim_flips[GEN ** i]
        iota = 0
        for m in unroll(0, KECCAK_SEGMENTS):
            flipped = 0
            for t in unroll(KECCAK_IOTA_START[KECCAK_SEGMENTS * step + m], KECCAK_IOTA_START[KECCAK_SEGMENTS * step + m + 1]):
                flipped += flips[KECCAK_IOTA_IDX[t]]
            iota += segment_tree[2 ** KECCAK_SEG_LOG - 2 + m] * flipped
        if step == 0:
            fs0, fs1, fs2, fs3, fs4, cursor = keccak_layer(fs0, fs1, fs2, fs3, fs4, value_rate[0], value_rate[1], cursor, y_g, step_g, rem_g, claim, claim * GEN ** KC_SIZE, iota, tabs, 1)
        else:
            fs0, fs1, fs2, fs3, fs4, cursor = keccak_layer(fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, y_g, step_g, rem_g, claim, claim * GEN ** KC_SIZE, iota, tabs, 0)

    # ---- the outputs, whose instance weights are an eq already ----
    # Their position weights are a word's, so the 64 slices are only needed as
    # the word they add up to: q_keccak itself at the point.
    out_slot = out_point * tau_g
    fs0, fs1, fs2, fs3, fs4, cursor, out_value = keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, value, out_slot, tabs, QKECCAK_SLOT_LOG, 0)
    word_rate = StackBuf(8)
    word, cursor = fs_next(word_rate, 0, cursor)
    out_lanes = StackBuf(KECCAK_LANES)
    keccak_slot_lanes(out_slot, point * pack_g, out_lanes, 1, KECCAK_SEGMENTS - 1)
    lanes_sum = 0
    for lane in unroll(0, KECCAK_LANES):
        lanes_sum += out_lanes[lane] * first_lanes[GEN ** lane]
    assert lanes_sum * word == out_value
    out_pack = out_point * GEN ** KECCAK_PACK_LOG
    for xt in mul_range(1, pack_g):
        out_pack[xt] = point[xt]

    # ---- the inputs: the instances of a pack first, then the slot ----
    last = claims * GEN ** (KECCAK_DEPTH * KC_SIZE)
    fs0, fs1, fs2, fs3, fs4, cursor, low_value = keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, word_rate[0], word_rate[1], cursor, last[GEN ** KC_VALUE], in_point, tabs, KECCAK_PACK_LOG, 1)
    low_tree = HeapBuf(2 ** (KECCAK_PACK_LOG + 1) - 2)
    eqtree(in_point, low_tree, KECCAK_PACK_LOG)
    mu_at_low = 0
    for i in unroll(0, KECCAK_PACK):
        mu_at_low += low_tree[GEN ** (2 ** KECCAK_PACK_LOG - 2 + i)] * last[GEN ** (KC_MU + i)]
    in_slot = in_point * tau_g
    fs0, fs1, fs2, fs3, fs4, cursor, in_value = keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, low_value, in_slot, tabs, QKECCAK_SLOT_LOG, 0)
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    for z in unroll(0, BASE_FIELD_BITS):
        if z % 4 == 0:
            if z != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        w, cursor = fs_next(rate, z % 4, cursor)
        slices[GEN ** z] = w
    sp = fs_perm(sp, rate, 4)
    last_point = last[GEN ** KC_POINT]
    in_lanes = StackBuf(KECCAK_LANES)
    keccak_slot_lanes(in_slot, last_point * pack_g, in_lanes, 0, KECCAK_SEGMENTS)
    # shifts[r] = sum_z slices[z] eq(a, z + r), a the last layer's slice point:
    # folded a bit at a time for every r at once.
    last_local = last[GEN ** KC_LOCAL]
    level = StackBuf(64)
    for z in unroll(0, BASE_FIELD_BITS):
        level[z] = slices[GEN ** z]
    for t in unroll(0, KECCAK_Z_BITS):
        folded = StackBuf(64)
        fold_shifts(level, folded, last_local[GEN ** t], t)
        level = folded
    shifts = level
    last_lanes = last[GEN ** KC_LANES]
    assert mu_at_low * keccak_form(last_lanes, shifts, in_lanes, 0) == in_value
    in_pack = in_point * GEN ** KECCAK_PACK_LOG
    for xt in mul_range(1, pack_g):
        in_pack[xt] = last_point[xt]
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, word
```
-/
def verifyKeccak : GFn where
  name := "verify_keccak"
  arity := 12
  rets := 7
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let cursor := cellOf ps 5
    let tauG := cellOf ps 6
    let chi := cellOf ps 7
    let outputLanes := cellOf ps 8
    let zVals := cellOf ps 9
    let slices := cellOf ps 10
    let tabs := cellOf ps 11
    let sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let noRate ← B.stackBuf 8
    let packG ← B.mul tauG (← B.const ((lit INV_GEN) ^ KECCAK_PACK_LOG))
    let yG : Shifted := ⟨packG, KECCAK_SEG_LOG⟩
    let yBits ← B.stackBuf 5
    B.hintBitsExpTo (.stack (yBits.take 5)) (← B.shifted yG.base yG.exp) 5
    for j_k in [0:5] do
      let bit := cellOf yBits j_k
      B.mulInto (cellOf yBits j_k) bit bit
    let stepG : GPow := ⟨0⟩
    let mut stepG_word : Word := default
    let j_k := 3
    stepG_word ← B.add (← B.const 1) (← B.mul (cellOf yBits j_k) (← B.const (1 + (gpowE (2 ^ (j_k - KR_STEP_LOG))))))
    let j_k := 4
    stepG_word ← B.mul stepG_word (← B.add (← B.const 1) (← B.mul (cellOf yBits j_k) (← B.const (1 + (gpowE (2 ^ (j_k - KR_STEP_LOG)))))))
    let remG : GPow := ⟨0⟩
    let mut remG_word : Word := default
    let j_k := 0
    remG_word ← B.add (← B.const 1) (← B.mul (cellOf yBits j_k) (← B.const (1 + (gpowE (2 ^ j_k)))))
    for j_k in [1:KR_STEP_LOG] do
      remG_word ← B.mul remG_word (← B.add (← B.const 1) (← B.mul (cellOf yBits j_k) (← B.const (1 + (gpowE (2 ^ j_k))))))
    B.assertEq (← B.mul (← B.pow stepG_word KR_STEP) remG_word) (← B.shifted yG.base yG.exp)
    let outPoint := zVals
    let inPoint : Shifted := ⟨zVals, QKECCAK_VARS_CAP⟩
    for i_k in [0:KECCAK_PACK_LOG] do
      B.store outPoint i_k (← B.load chi i_k)
    let point ← B.heapBufDyn (← B.shifted yG.base yG.exp)
    let chiPack : Shifted := ⟨chi, KECCAK_PACK_LOG⟩
    B.loopRtF 0 (pure packG) 2 (do return [point.v, (← B.shifted chiPack.base chiPack.exp).v]) fun xt caps => do
      let point := cellOf caps 0
      let chiPack := cellOf caps 1
      let t0 ← B.load (← B.mul chiPack xt) 0
      B.store (← B.mul point xt) 0 t0
    let segment ← B.mul point packG
    let (t0, t1, t2) ← fsGrindSqueeze_2 sp noRate 0 cursor tabs 0
    let mut sp := t0
    let r := t1
    let mut cursor := t2
    B.store segment 0 r
    let rLane ← B.heapBuf KECCAK_LANE_BITS
    for i_k in [0:KECCAK_LANE_BITS] do
      let (t3, t4) ← squeeze sp noRate 0
      sp := t3
      let r := t4
      B.store rLane i_k r
    let valueRate ← B.stackBuf 8
    let (t5, t6) ← fsNext valueRate 0 cursor
    let value := t5
    let cursor_ptr : Shifted := t6
    let mut fs0 := cellOf sp 8
    let mut fs1 := cellOf sp 9
    let mut fs2 := cellOf sp 10
    let mut fs3 := cellOf sp 11
    let mut fs4 := cellOf sp 12
    let claims ← B.heapBuf 286
    B.store claims 1 (← B.const 1)
    B.store claims KC_POINT point
    let muTree ← B.heapBuf 30
    eqtree outPoint muTree KECCAK_PACK_LOG
    for i_k in [0:KECCAK_PACK] do
      B.store claims (KC_MU + i_k) (← B.load muTree (((2 ^ KECCAK_PACK_LOG) - 2) + i_k))
    let laneTree ← B.heapBuf 62
    eqtree rLane laneTree KECCAK_LANE_BITS
    let firstLanes : Shifted := ⟨laneTree, 30⟩
    B.store claims KC_LANES (← B.shifted firstLanes.base firstLanes.exp)
    let segmentTree ← B.heapBuf 2
    eqtree_2 segment segmentTree KECCAK_SEG_LOG
    let output := 0
    let mut output_word : Word := default
    let lane_k := 0
    output_word ← B.mul (← B.load firstLanes.base (firstLanes.exp + lane_k)) (← B.load outputLanes lane_k)
    for lane_k in [1:KECCAK_LANES] do
      output_word ← B.add output_word (← B.mul (← B.load firstLanes.base (firstLanes.exp + lane_k)) (← B.load outputLanes lane_k))
    B.store claims KC_VALUE (← B.add value (← B.mul (← B.load segmentTree 1) output_word))
    let mut used : Nat := default
    let mut flipped : Nat := default
    let mut flipped_word : Word := default
    let mut claimFlips : Word := default
    let step_k := 0
    let claim := claims
    let claimPoint ← B.load claim KC_POINT
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          B.mulInto (cellOf flips i_k) (← B.load firstLanes.base firstLanes.exp) (← B.const (gpowE ((2 ^ i_k) - 1)))
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
    let iota := 0
    let mut iota_word : Word := default
    let m_k := 0
    flipped := 0
    let t_k := 0
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [1:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 3
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [4:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      let t7 ← B.call (instName "keccak_layer" [.L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (cellOf valueRate 0).v, (cellOf valueRate 1).v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, claim.v, (← B.shifted claim KC_SIZE).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    else
      pure () -- no use of this definition takes this branch
    let step_k := 1
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure ()
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 7
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [8:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 11
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    let t_k := 12
    flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let step_k := 2
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure ()
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 13
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    let t_k := 14
    flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 15
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [16:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let step_k := 3
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure () -- no use of this definition takes this branch
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 18
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [19:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 21
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [22:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let step_k := 4
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure ()
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 26
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [27:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 30
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [31:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let step_k := 5
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure () -- no use of this definition takes this branch
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 34
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [35:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 39
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [40:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let step_k := 6
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure ()
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 42
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    let t_k := 43
    flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 44
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    let t_k := 45
    flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let step_k := 7
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure ()
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 46
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [47:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 51
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [52:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let step_k := 8
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure ()
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 54
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [55:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 57
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [58:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let step_k := 9
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure ()
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 61
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [62:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 66
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [67:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let step_k := 10
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure ()
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 71
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [72:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 74
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [75:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let step_k := 11
    let claim_ptr : Shifted := ⟨claims, step_k * KC_SIZE⟩
    let claimPoint ← B.load claim_ptr.base (claim_ptr.exp + KC_POINT)
    let segmentTree_run ← B.stackBuf 2
    eqtreeFrame (← B.mul claimPoint packG) segmentTree_run KECCAK_SEG_LOG (2 ^ KECCAK_SEG_LOG)
    let flips ← B.stackBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      used := 0
      for t_k in [arrInt KECCAK_IOTA_START (KECCAK_SEGMENTS * step_k):arrInt KECCAK_IOTA_START ((KECCAK_SEGMENTS * step_k) + KECCAK_SEGMENTS)] do
        if (arrInt KECCAK_IOTA_IDX t_k) = i_k then
          used := 1
        else
          pure ()
      if used = 1 then
        if step_k = 0 then
          pure () -- no use of this definition takes this branch
        else
          claimFlips ← B.load claim_ptr.base (claim_ptr.exp + KC_FLIPS)
          B.loadInto (cellOf flips i_k) claimFlips i_k
      else
        pure ()
    let iota := 0
    let m_k := 0
    flipped := 0
    let t_k := 79
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    iota_word ← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word
    let m_k := 1
    flipped := 0
    let t_k := 80
    flipped_word := cellOf flips (arrInt KECCAK_IOTA_IDX t_k)
    for t_k in [81:arrInt KECCAK_IOTA_START (((KECCAK_SEGMENTS * step_k) + m_k) + 1)] do
      flipped_word ← B.add flipped_word (cellOf flips (arrInt KECCAK_IOTA_IDX t_k))
    iota_word ← B.add iota_word (← B.mul (cellOf segmentTree_run (((2 ^ KECCAK_SEG_LOG) - 2) + m_k)) flipped_word)
    if step_k = 0 then
      pure () -- no use of this definition takes this branch
    else
      let t7 ← B.call (instName "keccak_layer" [.L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, (← B.shifted yG.base yG.exp).v, stepG_word.v, remG_word.v, (← B.shifted claim_ptr.base claim_ptr.exp).v, (← B.shifted claim_ptr.base (claim_ptr.exp + KC_SIZE)).v, iota_word.v, tabs.v] 6
      fs0 := t7[0]!
      fs1 := t7[1]!
      fs2 := t7[2]!
      fs3 := t7[3]!
      fs4 := t7[4]!
      cursor := t7[5]!
    let outSlot ← B.mul outPoint tauG
    let t8 ← B.call (instName "keccak_plain_rounds" [.L QKECCAK_SLOT_LOG, .L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, value.v, outSlot.v, tabs.v] 7
    fs0 := t8[0]!
    fs1 := t8[1]!
    fs2 := t8[2]!
    fs3 := t8[3]!
    fs4 := t8[4]!
    cursor := t8[5]!
    let outValue := t8[6]!
    let wordRate ← B.stackBuf 8
    let (t9, t10) ← fsNext wordRate 0 cursor
    let word' := t9
    let mut cursor_ptr : Shifted := t10
    let outLanes ← B.stackBuf KECCAK_LANES
    keccakSlotLanes outSlot (← B.mul point packG) outLanes 1 (KECCAK_SEGMENTS - 1)
    let lanesSum := 0
    let mut lanesSum_word : Word := default
    let lane_k := 0
    lanesSum_word ← B.mul (cellOf outLanes lane_k) (← B.load firstLanes.base (firstLanes.exp + lane_k))
    for lane_k in [1:KECCAK_LANES] do
      lanesSum_word ← B.add lanesSum_word (← B.mul (cellOf outLanes lane_k) (← B.load firstLanes.base (firstLanes.exp + lane_k)))
    B.assertEq (← B.mul lanesSum_word word') outValue
    let outPack : Shifted := ⟨outPoint, KECCAK_PACK_LOG⟩
    B.loopRtF 0 (pure packG) 2 (do return [(← B.shifted outPack.base outPack.exp).v, point.v]) fun xt caps => do
      let outPack := cellOf caps 0
      let point := cellOf caps 1
      let t0 ← B.load (← B.mul point xt) 0
      B.store (← B.mul outPack xt) 0 t0
    let last : Shifted := ⟨claims, 264⟩
    let t11 ← B.call (instName "keccak_plain_rounds" [.L KECCAK_PACK_LOG, .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (cellOf wordRate 0).v, (cellOf wordRate 1).v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, (← B.load last.base last.exp).v, (← B.shifted inPoint.base inPoint.exp).v, tabs.v] 7
    fs0 := t11[0]!
    fs1 := t11[1]!
    fs2 := t11[2]!
    fs3 := t11[3]!
    fs4 := t11[4]!
    cursor := t11[5]!
    let lowValue := t11[6]!
    let lowTree ← B.heapBuf 30
    eqtree_3 (⟨inPoint.base, inPoint.exp⟩) lowTree KECCAK_PACK_LOG
    let muAtLow := 0
    let mut muAtLow_word : Word := default
    let i_k := 0
    muAtLow_word ← B.mul (← B.load lowTree (((2 ^ KECCAK_PACK_LOG) - 2) + i_k)) (← B.load last.base (last.exp + (KC_MU + i_k)))
    for i_k in [1:KECCAK_PACK] do
      muAtLow_word ← B.add muAtLow_word (← B.mul (← B.load lowTree (((2 ^ KECCAK_PACK_LOG) - 2) + i_k)) (← B.load last.base (last.exp + (KC_MU + i_k))))
    let inSlot ← B.mul (← B.shifted inPoint.base inPoint.exp) tauG
    let t12 ← B.call (instName "keccak_plain_rounds" [.L QKECCAK_SLOT_LOG, .L 0]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.const 0).v, (← B.const 0).v, cursor.v, lowValue.v, inSlot.v, tabs.v] 7
    fs0 := t12[0]!
    fs1 := t12[1]!
    fs2 := t12[2]!
    fs3 := t12[3]!
    fs4 := t12[4]!
    cursor := t12[5]!
    let inValue := t12[6]!
    sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut rate ← B.stackBuf 8
    let z_k := 0
    if (z_k % 4) = 0 then
      if z_k ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    let (t13, t14) ← fsNext rate (z_k % 4) cursor
    let w := t13
    cursor_ptr := t14
    B.store slices z_k w
    for z_k in [1:BASE_FIELD_BITS] do
      if (z_k % 4) = 0 then
        if z_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      let (t13, t14) ← fsNext_2 rate (z_k % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      let w := t13
      cursor_ptr := t14
      B.store slices z_k w
    sp ← fsPerm sp rate 4
    let lastPoint ← B.load last.base (last.exp + KC_POINT)
    let inLanes ← B.stackBuf KECCAK_LANES
    keccakSlotLanes_2 inSlot (← B.mul lastPoint packG) inLanes 0 KECCAK_SEGMENTS
    let lastLocal ← B.load last.base (last.exp + KC_LOCAL)
    let mut level ← B.stackBuf 64
    for z_k in [0:BASE_FIELD_BITS] do
      B.loadInto (cellOf level z_k) slices z_k
    let t_k := 0
    let folded ← B.stackBuf 64
    foldShifts level folded (← B.load lastLocal t_k) t_k
    level := folded
    for t_k in [1:KECCAK_Z_BITS] do
      let folded ← B.stackBuf 64
      foldShifts_2 level folded (← B.load lastLocal t_k) t_k
      level := folded
    let shifts := level
    let lastLanes ← B.load last.base (last.exp + KC_LANES)
    let t15 ← keccakForm lastLanes shifts inLanes 0
    B.assertEq (← B.mul muAtLow_word t15) inValue
    let inPack : Shifted := ⟨inPoint.base, inPoint.exp + KECCAK_PACK_LOG⟩
    B.loopRtF 0 (pure packG) 2 (do return [(← B.shifted inPack.base inPack.exp).v, lastPoint.v]) fun xt caps => do
      let inPack := cellOf caps 0
      let lastPoint := cellOf caps 1
      let t0 ← B.load (← B.mul lastPoint xt) 0
      B.store (← B.mul inPack xt) 0 t0
    let t16 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted cursor_ptr.base cursor_ptr.exp)
    return [.v (cellOf sp 8).v] ++ [.v (cellOf sp 9).v] ++ [.v (cellOf sp 10).v] ++ [.v (cellOf sp 11).v] ++ [.v (cellOf sp 12).v] ++ [.into t16] ++ [.v word'.v]

set_option linter.unusedVariables false in
/-- `ring_switch_target` (`guests/lean_ethereum.py`, line 3302):

```
def ring_switch_target(slices, map_challenges):
    # T = sum_i x^i Phi(s_i) = sum_p f_p (sum_i z_p^i Psi(s_i))^(2^(8p)), z_p = x^(2^(64 - 8p))
    # in K, so a slice takes Psi alone. The eight sums run Horner over the slices from
    # the bottom, RS_CHUNK an iteration, in w_p = 1/z_p: they come out as
    # sum_i w_p^(63 - i) Psi(s_i), and the final x^63 = (z_p^63)^(2^(8p)) restores them all.
    rs_chain = HeapBuf((BASE_FIELD_BITS // RS_CHUNK + 1) * RING_MAP_WIDTH)
    for p in unroll(0, RING_MAP_WIDTH):
        rs_chain[GEN ** p] = 0
    for x_round in mul_range(1, GEN ** (BASE_FIELD_BITS // RS_CHUNK)):
        g = StackBuf(RING_MAP_WIDTH)  # read once an iteration, not once a row
        for b in unroll(0, RING_MAP_WIDTH):
            g[b] = map_challenges[GEN ** (RING_MAP_WIDTH + b)]
        rows = slices * x_round ** RS_CHUNK
        psi = StackBuf(RS_CHUNK)
        for r in unroll(0, RS_CHUNK):
            ring_psi(psi, r, rows[GEN ** r], g)
        row = rs_chain * x_round ** RING_MAP_WIDTH
        for p in unroll(0, RING_MAP_WIDTH):
            acc = row[GEN ** p]
            for r in unroll(0, RS_CHUNK):
                acc = acc * RING_W[p] + psi[r]
            row[GEN ** (RING_MAP_WIDTH + p)] = acc
    sums = rs_chain * (GEN ** (BASE_FIELD_BITS // RS_CHUNK)) ** RING_MAP_WIDTH
    total = map_challenges[GEN ** 0] * sums[GEN ** 0]
    for p in unroll(1, RING_MAP_WIDTH):
        h = sums[GEN ** p]
        for t in unroll(0, RING_MAP_WIDTH * p):
            h = h * h
        total += map_challenges[GEN ** p] * h
    return total * GEN ** (BASE_FIELD_BITS - 1)
```
-/
def ringSwitchTarget : GFn where
  name := "ring_switch_target"
  arity := 2
  rets := 1
  body ps := do
    let slices := cellOf ps 0
    let mapChallenges := cellOf ps 1
    let rsChain ← B.heapBuf 72
    for p_k in [0:RING_MAP_WIDTH] do
      B.store rsChain p_k (← B.const 0)
    B.loopConstF 0 RS_CHUNK 3 (pure ([mapChallenges.v, slices.v, rsChain.v])) fun xRound caps => do
      let mapChallenges := cellOf caps 0
      let slices := cellOf caps 1
      let rsChain := cellOf caps 2
      let g ← B.stackBuf RING_MAP_WIDTH
      for b_k in [0:RING_MAP_WIDTH] do
        B.loadInto (cellOf g b_k) mapChallenges (RING_MAP_WIDTH + b_k)
      let rows ← B.mul slices (← B.pow xRound RS_CHUNK)
      let psi ← B.stackBuf RS_CHUNK
      for r_k in [0:RS_CHUNK] do
        ringPsi psi r_k (← B.load rows r_k) g
      let row ← B.mul rsChain (← B.pow xRound RING_MAP_WIDTH)
      for p_k in [0:RING_MAP_WIDTH] do
        let mut acc ← B.load row p_k
        for r_k in [0:RS_CHUNK] do
          acc ← B.add (← B.mul acc (← B.const (arrWord RING_W p_k))) (cellOf psi r_k)
        B.store row (RING_MAP_WIDTH + p_k) acc
    let sums ← B.mul rsChain (← B.const ((gpowE 8) ^ 8))
    let mut total ← B.mul (← B.load mapChallenges 0) (← B.load sums 0)
    for p_k in [1:RING_MAP_WIDTH] do
      let mut h ← B.load sums p_k
      for _ in [0:RING_MAP_WIDTH * p_k] do
        h ← B.mul h h
      total ← B.add total (← B.mul (← B.load mapChallenges p_k) h)
    let t0 : V → B Unit := fun rc => do
      B.mulInto (wordOf rc) total (← B.const (gpowE 63))
    return [.into t0]

set_option linter.unusedVariables false in
/-- `ring_switch_weight` (`guests/lean_ethereum.py`, line 3334):

```
def ring_switch_weight(z_vals, point1, c_table, qkeccakv_g):
    # One ring-switched claim's transparent weight at the opening point.
    prod_final = rs_eq_run(z_vals, point1, qkeccakv_g)
    rs_weight = 0
    for k in unroll(0, BASE_FIELD_BITS):
        rs_weight += c_table[GEN ** k] * prod_final[GEN ** k]
    return rs_weight
```
-/
def ringSwitchWeight : GFn where
  name := "ring_switch_weight"
  arity := 4
  rets := 1
  body ps := do
    let zVals := cellOf ps 0
    let point1 := cellOf ps 1
    let cTable := cellOf ps 2
    let qkeccakvG := cellOf ps 3
    let prodFinal ← call1 "rs_eq_run" [zVals.v, point1.v, qkeccakvG.v]
    let rsWeight := 0
    let mut rsWeight_word : Word := default
    let k_k := 0
    rsWeight_word ← B.mul (← B.load cTable k_k) (← B.load prodFinal k_k)
    for k_k in [1:BASE_FIELD_BITS] do
      rsWeight_word ← B.add rsWeight_word (← B.mul (← B.load cTable k_k) (← B.load prodFinal k_k))
    return [.v rsWeight_word.v]

set_option linter.unusedVariables false in
/-- `certify_placement` (`guests/lean_ethereum.py`, line 3343):

```
def certify_placement(kappa_base, g_squares):
    # Certify the native order (descending kappa, then ascending column index) group
    # by group: a column group, a run of columns sharing one kappa source, is
    # consecutive in it, so a hinted order of the groups, certified strictly
    # descending in its rank key, places every column. Returns g^(sum 2^kappa) and
    # each column's g^offset.
    kb = StackBuf(N_TABLES + 2)
    for i in unroll(0, N_TABLES + 2):
        kb[i] = kappa_base[GEN ** i]
    rank_keys = g_squares * GEN ** RANK_KEYS_AT
    group_key = HeapBuf(N_COL_GROUPS)
    group_size = HeapBuf(N_COL_GROUPS)
    for gi in unroll(0, N_COL_GROUPS):
        c0 = COL_GROUP_START[gi]
        kappa_g = kb[COL_KAPPA_SRC[c0]] * GEN ** COL_KAPPA_ADJ[c0]
        # g_squares spans SIZE_BITS, and every kappa is under it: a certified log
        # <= 30 (log_mem or a tau), the baked bytecode log, or q_keccak's tau_5 + QKECCAK_SLOT_LOG.
        assert log(kappa_g) < SIZE_BITS
        # Descending kappa, then the group's first (compact, native-order) index ascending.
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
        # A negative step wraps around the order of GEN and cannot pass this check.
        if rank != 0:
            assert log(prev_key / key * INV_GEN) < RANK_KEY_BOUND
        group_base[gi] = g_total  # write-once: a repeated group collides
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
-/
def certifyPlacement : GFn where
  name := "certify_placement"
  arity := 2
  rets := 2
  body ps := do
    let kappaBase := cellOf ps 0
    let gSquares := cellOf ps 1
    let kb ← B.stackBuf 8
    for i_k in [0:N_TABLES + 2] do
      B.loadInto (cellOf kb i_k) kappaBase i_k
    let rankKeys : Shifted := ⟨gSquares, RANK_KEYS_AT⟩
    let groupKey ← B.heapBuf N_COL_GROUPS
    let groupSize ← B.heapBuf N_COL_GROUPS
    let mut c0 : Nat := default
    let gi_k := 0
    c0 := arrInt COL_GROUP_START gi_k
    let kappaG := cellOf kb (arrInt COL_KAPPA_SRC c0)
    let _ ← B.rangeCheck kappaG SIZE_BITS
    B.store groupKey gi_k (← B.load (← B.mul rankKeys.base kappaG) rankKeys.exp)
    B.store groupSize gi_k (← B.pow (← B.load (← B.mul gSquares kappaG) 0) ((arrInt COL_GROUP_START (gi_k + 1)) - c0))
    for gi_k in [1:3] do
      c0 := arrInt COL_GROUP_START gi_k
      let kappaG ← B.mul (cellOf kb (arrInt COL_KAPPA_SRC c0)) (← B.const (gpowE (arrInt COL_KAPPA_ADJ c0)))
      let _ ← B.rangeCheck kappaG SIZE_BITS
      B.store groupKey gi_k (← B.mul (← B.load (← B.mul rankKeys.base kappaG) rankKeys.exp) (← B.const ((lit INV_GEN) ^ c0)))
      B.store groupSize gi_k (← B.pow (← B.load (← B.mul gSquares kappaG) 0) ((arrInt COL_GROUP_START (gi_k + 1)) - c0))
    for gi_k in [3:N_COL_GROUPS] do
      c0 := arrInt COL_GROUP_START gi_k
      let kappaG := cellOf kb (arrInt COL_KAPPA_SRC c0)
      let _ ← B.rangeCheck kappaG SIZE_BITS
      B.store groupKey gi_k (← B.mul (← B.load (← B.mul rankKeys.base kappaG) rankKeys.exp) (← B.const ((lit INV_GEN) ^ c0)))
      B.store groupSize gi_k (← B.pow (← B.load (← B.mul gSquares kappaG) 0) ((arrInt COL_GROUP_START (gi_k + 1)) - c0))
    let groupOrder ← B.heapBuf N_COL_GROUPS
    B.witness "col_group_order" (.heap groupOrder.v 0 N_COL_GROUPS)
    let groupBase ← B.heapBuf N_COL_GROUPS
    let gTotal : GPow := ⟨0⟩
    let mut gi : Word := default
    let mut gTotal_word : Word := default
    let mut prevKey : Word := default
    let rank_k := 0
    gi ← B.load groupOrder rank_k
    let _ ← B.rangeCheck gi N_COL_GROUPS
    let key ← B.load (← B.mul groupKey gi) 0
    if rank_k ≠ 0 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    let t0 ← B.const (gpowE gTotal.exp)
    B.store (← B.mul groupBase gi) 0 t0
    gTotal_word ← B.load (← B.mul groupSize gi) 0
    prevKey := key
    for rank_k in [1:N_COL_GROUPS] do
      gi ← B.load groupOrder rank_k
      let _ ← B.rangeCheck gi N_COL_GROUPS
      let key ← B.load (← B.mul groupKey gi) 0
      if rank_k ≠ 0 then
        let t0 ← B.const (gpowE (RANK_KEY_BOUND - 1))
        let _ ← B.rangeCheckK (← B.mul (← B.fdiv prevKey key) (← B.const (lit INV_GEN))) t0
        pure ()
      else
        pure () -- no use of this definition takes this branch
      B.store (← B.mul groupBase gi) 0 gTotal_word
      gTotal_word ← B.mul gTotal_word (← B.load (← B.mul groupSize gi) 0)
      prevKey := key
    let colOffG ← B.heapBuf N_COMMITTED_COLS
    let gi_k := 0
    c0 := arrInt COL_GROUP_START gi_k
    let step ← B.load (← B.mul gSquares (cellOf kb (arrInt COL_KAPPA_SRC c0))) (arrInt COL_KAPPA_ADJ c0)
    let mut off ← B.load groupBase gi_k
    for c_k in [c0:arrInt COL_GROUP_START (gi_k + 1)] do
      B.store colOffG c_k off
      if (c_k + 1) ≠ (arrInt COL_GROUP_START (gi_k + 1)) then
        off ← B.mul off step
      else
        pure ()
    let gi_k := 1
    c0 := arrInt COL_GROUP_START gi_k
    let step ← B.load (← B.mul gSquares (cellOf kb (arrInt COL_KAPPA_SRC c0))) (arrInt COL_KAPPA_ADJ c0)
    off ← B.load groupBase gi_k
    let c_k := 3
    B.store colOffG c_k off
    if (c_k + 1) ≠ (arrInt COL_GROUP_START (gi_k + 1)) then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    let gi_k := 2
    c0 := arrInt COL_GROUP_START gi_k
    let step ← B.load (← B.mul gSquares (cellOf kb (arrInt COL_KAPPA_SRC c0))) (arrInt COL_KAPPA_ADJ c0)
    off ← B.load groupBase gi_k
    let c_k := 4
    B.store colOffG c_k off
    if (c_k + 1) ≠ (arrInt COL_GROUP_START (gi_k + 1)) then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    for gi_k in [3:N_COL_GROUPS] do
      c0 := arrInt COL_GROUP_START gi_k
      let step ← B.load (← B.mul gSquares (cellOf kb (arrInt COL_KAPPA_SRC c0))) (arrInt COL_KAPPA_ADJ c0)
      off ← B.load groupBase gi_k
      for c_k in [c0:arrInt COL_GROUP_START (gi_k + 1)] do
        B.store colOffG c_k off
        if (c_k + 1) ≠ (arrInt COL_GROUP_START (gi_k + 1)) then
          off ← B.mul off step
        else
          pure ()
    return [.v gTotal_word.v] ++ [.v colOffG.v]

set_option linter.unusedVariables false in
/-- `selector_tables` (`guests/lean_ethereum.py`, line 3420):

```
def selector_tables(point, point1):
    # Per nibble j of the selector bits, the eq tables over its top 1..4 coordinates,
    # the level-w one at 16 (w - 1), strided: entry u, a multiple of 2^(4 - w), holds
    # the eq of bit t of u against coordinate 4j + t for t >= 4 - w.
    sel_eq = HeapBuf(SEL_NIBBLES * SEL_EQ_STRIDE)
    for j in unroll(0, SEL_NIBBLES):
        levels = StackBuf(64)
        levels[0] = point1[GEN ** (4 * j + 3)]
        levels[8] = point[GEN ** (4 * j + 3)]
        for w in unroll(1, 4):
            r = point[GEN ** (4 * j + 3 - w)]
            r1 = point1[GEN ** (4 * j + 3 - w)]
            for i in unroll(0, 2 ** w):
                e = i * 2 ** (4 - w)
                levels[16 * w + e] = levels[16 * (w - 1) + e] * r1
                levels[16 * w + e + 2 ** (3 - w)] = levels[16 * (w - 1) + e] * r
        for w in unroll(0, 4):
            for i in unroll(0, 2 ** (w + 1)):
                e = i * 2 ** (3 - w)
                sel_eq[GEN ** (SEL_EQ_STRIDE * j + 16 * w + e)] = levels[16 * w + e]
    return sel_eq
```
-/
def selectorTables : GFn where
  name := "selector_tables"
  arity := 2
  rets := 1
  body ps := do
    let point := cellOf ps 0
    let point1 := cellOf ps 1
    let selEq ← B.heapBuf 512
    let mut r : Word := default
    let mut r1 : Word := default
    let mut e : Nat := default
    for j_k in [0:SEL_NIBBLES] do
      let levels ← B.stackBuf 64
      B.loadInto (cellOf levels 0) point1 ((4 * j_k) + 3)
      B.loadInto (cellOf levels 8) point ((4 * j_k) + 3)
      for w_k in [1:4] do
        r ← B.load point (((4 * j_k) + 3) - w_k)
        r1 ← B.load point1 (((4 * j_k) + 3) - w_k)
        for i_k in [0:2 ^ w_k] do
          e := i_k * (2 ^ (4 - w_k))
          B.mulInto (cellOf levels ((16 * w_k) + e)) (cellOf levels ((16 * (w_k - 1)) + e)) r1
          B.mulInto (cellOf levels (((16 * w_k) + e) + (2 ^ (3 - w_k)))) (cellOf levels ((16 * (w_k - 1)) + e)) r
      for w_k in [0:4] do
        for i_k in [0:2 ^ (w_k + 1)] do
          e := i_k * (2 ^ (3 - w_k))
          B.store selEq (((SEL_EQ_STRIDE * j_k) + (16 * w_k)) + e) (cellOf levels ((16 * w_k) + e))
    return [.v selEq.v]

set_option linter.unusedVariables false in
/-- `check_opening_terminal` (`guests/lean_ethereum.py`, line 3443):

```
def check_opening_terminal(g_squares, zeta, chi, rm, g_bus_mu, g_zc_n, g_log_mem, tau_keccak_g, kappa_base, lam_cl, col_offsets, z_vals, c_table, point, point1, inner_total, yr_at_tail, sumcheck_target, ood_z, gmv):
    # Evaluate each transparent weight at the complete point in witness order.
    # A claim is its low point followed by the certified column's selector bits;
    # a q_keccak lane puts its slot's bits between the two.
    # point1 = 1 + point holds each coordinate's eq factor against a zero bit.
    zeta_eq_chain = HeapBuf(SIZE_BITS + 1)
    eq_prefix_chain(zeta_eq_chain, 1, zeta, point1, g_bus_mu)
    chi_eq_chain = HeapBuf(SIZE_BITS + 1)
    eq_prefix_chain(chi_eq_chain, 1, chi, point1, g_zc_n)
    slot_point = point * tau_keccak_g
    slot_point1 = point1 * tau_keccak_g
    pi_chain = HeapBuf(SIZE_BITS + 1)
    pi_chain[GEN ** 0] = 1
    pi_chain[GEN ** 1] = rm + point1[GEN ** 0]
    for xk in mul_range(GEN, g_log_mem):
        pi_chain[xk * GEN] = pi_chain[xk] * point1[xk]
    pi_eq = pi_chain[g_log_mem]

    # Every low dimension here is a certified log at a baked kappa source, as
    # certify_placement derives the columns'.
    kb = StackBuf(N_TABLES + 2)
    for i in unroll(0, N_TABLES + 2):
        kb[i] = kappa_base[GEN ** i]
    sel_eq = selector_tables(point, point1)
    sel_g = g_squares * GEN ** SIZE_BITS  # exponent_tables' constant nibble shares
    selectors = StackBuf(N_COMMITTED_COLS)
    for c in unroll(0, N_COMMITTED_COLS):
        offset = col_offsets[GEN ** c]
        kappa_g = kb[COL_KAPPA_SRC[c]] * GEN ** COL_KAPPA_ADJ[c]
        selectors[c] = match(log(kappa_g), range(0, N_COLUMN_LOGS), lambda kappa: column_selector(offset, sel_eq, sel_g, kappa))

    inner_sum = inner_total
    lam_pow = lam_cl  # the pool's powers, as verify_sub batched it
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] != POINT_BUF_KECCAK_OUT:
            col = CLAIM_COMMITTED_COL[j]
            cplen_g = kb[CLAIM_KAPPA_SRC[j]] * GEN ** CLAIM_KAPPA_ADJ[j]
            nlow_adj = CLAIM_KAPPA_ADJ[j]
            if CLAIM_POINT_BUF[j] == POINT_BUF_PI:
                low_eq = pi_eq
            if CLAIM_POINT_BUF[j] == POINT_BUF_ZETA:
                low_eq = zeta_eq_chain[cplen_g]
            if CLAIM_POINT_BUF[j] == POINT_BUF_RHO:
                low_eq = chi_eq_chain[cplen_g]
            if CLAIM_POINT_BUF[j] == POINT_BUF_QKECCAK_RHO:
                # Top bit first, so claims sharing high slot bits share partial products.
                slot_eq = GEN ** 0
                for kk in unroll(0, QKECCAK_SLOT_LOG):
                    k = QKECCAK_SLOT_LOG - 1 - kk
                    if CLAIM_QKECCAK_SLOT_BITS[QKECCAK_SLOT_LOG * j + k] == 1:
                        slot_factor = slot_point[GEN ** k]
                    else:
                        slot_factor = slot_point1[GEN ** k]
                    if kk == 0:
                        slot_eq = slot_factor
                    else:
                        slot_eq *= slot_factor
                low_eq = slot_eq * chi_eq_chain[cplen_g]
                nlow_adj = CLAIM_KAPPA_ADJ[j] + QKECCAK_SLOT_LOG
            # The claim's low dimension is its column's kappa: by construction when
            # the two share a kappa source, else checked.
            if const(CLAIM_KAPPA_SRC[j] != COL_KAPPA_SRC[col]):
                assert kb[CLAIM_KAPPA_SRC[j]] * GEN ** nlow_adj == kb[COL_KAPPA_SRC[col]] * GEN ** COL_KAPPA_ADJ[col]
            else:
                if const(nlow_adj != COL_KAPPA_ADJ[col]):
                    assert kb[CLAIM_KAPPA_SRC[j]] * GEN ** nlow_adj == kb[COL_KAPPA_SRC[col]] * GEN ** COL_KAPPA_ADJ[col]
            inner_sum += lam_pow * low_eq * selectors[col]
            lam_pow *= lam_cl
    lam_out = lam_pow

    # The Keccak reduction's two claims on q_keccak, each over the whole column:
    # the ring-switched one leads the batch at lam_cl^0, the plain one closes it.
    # A lane claim's low point is tau_keccak long, the kappa check above holding it
    # to this column.
    qkeccakv_g = tau_keccak_g * GEN ** QKECCAK_SLOT_LOG
    if const(COL_KAPPA_SRC[QKECCAK_COMMITTED_COL] != TABLE_KECCAK + 2):
        assert qkeccakv_g == kb[COL_KAPPA_SRC[QKECCAK_COMMITTED_COL]] * GEN ** COL_KAPPA_ADJ[QKECCAK_COMMITTED_COL]
    else:
        if const(COL_KAPPA_ADJ[QKECCAK_COMMITTED_COL] != QKECCAK_SLOT_LOG):
            assert qkeccakv_g == kb[COL_KAPPA_SRC[QKECCAK_COMMITTED_COL]] * GEN ** COL_KAPPA_ADJ[QKECCAK_COMMITTED_COL]
    out_eq_chain = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG + 1)
    eq_prefix_chain(out_eq_chain, 1, z_vals, point1, qkeccakv_g)
    rs_weight = ring_switch_weight(z_vals * GEN ** QKECCAK_VARS_CAP, point1, c_table, qkeccakv_g)
    inner_sum += (rs_weight + lam_out * out_eq_chain[qkeccakv_g]) * selectors[QKECCAK_COMMITTED_COL]
    # The OOD sample's claim, after the output word's: eq(z, .) over the stack's m variables.
    ood_chain = HeapBuf(MAX_STACK_LOG + 1)
    eq_prefix_chain(ood_chain, lam_out * lam_cl, ood_z, point1, gmv)
    assert (inner_sum + ood_chain[gmv]) * yr_at_tail == sumcheck_target
```
-/
def checkOpeningTerminal : GFn where
  name := "check_opening_terminal"
  arity := 20
  rets := 0
  body ps := do
    let gSquares := cellOf ps 0
    let zeta := cellOf ps 1
    let chi := cellOf ps 2
    let rm := cellOf ps 3
    let gBusMu := cellOf ps 4
    let gZcN := cellOf ps 5
    let gLogMem := cellOf ps 6
    let tauKeccakG := cellOf ps 7
    let kappaBase := cellOf ps 8
    let lamCl := cellOf ps 9
    let colOffsets := cellOf ps 10
    let zVals := cellOf ps 11
    let cTable := cellOf ps 12
    let point := cellOf ps 13
    let point1 := cellOf ps 14
    let innerTotal := cellOf ps 15
    let yrAtTail := cellOf ps 16
    let sumcheckTarget := cellOf ps 17
    let oodZ := cellOf ps 18
    let gmv := cellOf ps 19
    let zetaEqChain ← B.heapBuf 35
    let _ ← B.call "eq_prefix_chain" [zetaEqChain.v, (← B.const 1).v, zeta.v, point1.v, gBusMu.v] 0
    let chiEqChain ← B.heapBuf 35
    let _ ← B.call "eq_prefix_chain" [chiEqChain.v, (← B.const 1).v, chi.v, point1.v, gZcN.v] 0
    let slotPoint ← B.mul point tauKeccakG
    let slotPoint1 ← B.mul point1 tauKeccakG
    let piChain ← B.heapBuf 35
    B.store piChain 0 (← B.const 1)
    B.store piChain 1 (← B.add rm (← B.load point1 0))
    B.loopRtF 1 (pure gLogMem) 2 (pure ([piChain.v, point1.v])) fun xk caps => do
      let piChain := cellOf caps 0
      let point1 := cellOf caps 1
      let t0 ← B.mul (← B.load (← B.mul piChain xk) 0) (← B.load (← B.mul point1 xk) 0)
      B.store (← B.mul piChain xk) 1 t0
    let piEq ← B.load (← B.mul piChain gLogMem) 0
    let kb ← B.stackBuf 8
    for i_k in [0:N_TABLES + 2] do
      B.loadInto (cellOf kb i_k) kappaBase i_k
    let selEq ← call1 "selector_tables" [point.v, point1.v]
    let selG : Shifted := ⟨gSquares, SIZE_BITS⟩
    let selectors ← B.stackBuf N_COMMITTED_COLS
    for c_k in [0:3] do
      let offset ← B.load colOffsets c_k
      let kappaG := cellOf kb (arrInt COL_KAPPA_SRC c_k)
      let t0 ← B.targets [some (cellOf selectors c_k).v]
      let t1 ← B.shifted selG.base selG.exp
      B.dispatchInto kappaG ((List.range N_COLUMN_LOGS).map fun arm => (instName "column_selector" [.L arm])) [offset.v, selEq.v, t1.v] t0
    for c_k in [3:5] do
      let offset ← B.load colOffsets c_k
      let kappaG ← B.mul (cellOf kb (arrInt COL_KAPPA_SRC c_k)) (← B.const (gpowE (arrInt COL_KAPPA_ADJ c_k)))
      let t0 ← B.targets [some (cellOf selectors c_k).v]
      let t1 ← B.shifted selG.base selG.exp
      B.dispatchInto kappaG ((List.range N_COLUMN_LOGS).map fun arm => (instName "column_selector" [.L arm])) [offset.v, selEq.v, t1.v] t0
    for c_k in [5:N_COMMITTED_COLS] do
      let offset ← B.load colOffsets c_k
      let kappaG := cellOf kb (arrInt COL_KAPPA_SRC c_k)
      let t0 ← B.targets [some (cellOf selectors c_k).v]
      let t1 ← B.shifted selG.base selG.exp
      B.dispatchInto kappaG ((List.range N_COLUMN_LOGS).map fun arm => (instName "column_selector" [.L arm])) [offset.v, selEq.v, t1.v] t0
    let mut innerSum := innerTotal
    let mut lamPow := lamCl
    let mut col : Nat := default
    let mut cplenG : Word := default
    let mut nlowAdj : Nat := default
    let mut lowEq : Word := default
    let mut slotEq : GPow := default
    let mut k : Nat := default
    let mut slotFactor : Word := default
    let mut slotEq_word : Word := default
    for j_k in [0:3] do
      if (arrInt CLAIM_POINT_BUF j_k) ≠ POINT_BUF_KECCAK_OUT then
        col := arrInt CLAIM_COMMITTED_COL j_k
        cplenG := cellOf kb (arrInt CLAIM_KAPPA_SRC j_k)
        nlowAdj := arrInt CLAIM_KAPPA_ADJ j_k
        if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_PI then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_ZETA then
          lowEq ← B.load (← B.mul zetaEqChain cplenG) 0
        else
          pure () -- no use of this definition takes this branch
        if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_RHO then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_QKECCAK_RHO then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt CLAIM_KAPPA_SRC j_k) ≠ (arrInt COL_KAPPA_SRC col) then
          pure () -- no use of this definition takes this branch
        else
          if nlowAdj ≠ (arrInt COL_KAPPA_ADJ col) then
            pure () -- no use of this definition takes this branch
          else
            pure ()
        innerSum ← B.add innerSum (← B.mul (← B.mul lamPow lowEq) (cellOf selectors col))
        lamPow ← B.mul lamPow lamCl
      else
        pure () -- no use of this definition takes this branch
    let j_k := 3
    if (arrInt CLAIM_POINT_BUF j_k) ≠ POINT_BUF_KECCAK_OUT then
      col := arrInt CLAIM_COMMITTED_COL j_k
      cplenG ← B.mul (cellOf kb (arrInt CLAIM_KAPPA_SRC j_k)) (← B.const (gpowE (arrInt CLAIM_KAPPA_ADJ j_k)))
      nlowAdj := arrInt CLAIM_KAPPA_ADJ j_k
      if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_PI then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_ZETA then
        lowEq ← B.load (← B.mul zetaEqChain cplenG) 0
      else
        pure () -- no use of this definition takes this branch
      if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_RHO then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_QKECCAK_RHO then
        pure () -- no use of this definition takes this branch
      else
        pure ()
      if (arrInt CLAIM_KAPPA_SRC j_k) ≠ (arrInt COL_KAPPA_SRC col) then
        pure () -- no use of this definition takes this branch
      else
        if nlowAdj ≠ (arrInt COL_KAPPA_ADJ col) then
          pure () -- no use of this definition takes this branch
        else
          pure ()
      innerSum ← B.add innerSum (← B.mul (← B.mul lamPow lowEq) (cellOf selectors col))
      lamPow ← B.mul lamPow lamCl
    else
      pure () -- no use of this definition takes this branch
    for j_k in [4:N_CLAIMS] do
      if (arrInt CLAIM_POINT_BUF j_k) ≠ POINT_BUF_KECCAK_OUT then
        col := arrInt CLAIM_COMMITTED_COL j_k
        cplenG := cellOf kb (arrInt CLAIM_KAPPA_SRC j_k)
        nlowAdj := arrInt CLAIM_KAPPA_ADJ j_k
        if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_PI then
          lowEq := piEq
        else
          pure ()
        if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_ZETA then
          pure () -- no use of this definition takes this branch
        else
          pure ()
        if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_RHO then
          lowEq ← B.load (← B.mul chiEqChain cplenG) 0
        else
          pure ()
        if (arrInt CLAIM_POINT_BUF j_k) = POINT_BUF_QKECCAK_RHO then
          slotEq := ⟨0⟩
          for kk_k in [0:QKECCAK_SLOT_LOG] do
            k := (QKECCAK_SLOT_LOG - 1) - kk_k
            if (arrInt CLAIM_QKECCAK_SLOT_BITS ((QKECCAK_SLOT_LOG * j_k) + k)) = 1 then
              slotFactor ← B.load slotPoint k
            else
              slotFactor ← B.load slotPoint1 k
            if kk_k = 0 then
              slotEq_word := slotFactor
            else
              slotEq_word ← B.mul slotEq_word slotFactor
          lowEq ← B.mul slotEq_word (← B.load (← B.mul chiEqChain cplenG) 0)
          nlowAdj := (arrInt CLAIM_KAPPA_ADJ j_k) + QKECCAK_SLOT_LOG
        else
          pure ()
        if (arrInt CLAIM_KAPPA_SRC j_k) ≠ (arrInt COL_KAPPA_SRC col) then
          pure () -- no use of this definition takes this branch
        else
          if nlowAdj ≠ (arrInt COL_KAPPA_ADJ col) then
            pure () -- no use of this definition takes this branch
          else
            pure ()
        innerSum ← B.add innerSum (← B.mul (← B.mul lamPow lowEq) (cellOf selectors col))
        lamPow ← B.mul lamPow lamCl
      else
        pure ()
    let lamOut := lamPow
    let qkeccakvG : Shifted := ⟨tauKeccakG, QKECCAK_SLOT_LOG⟩
    if (arrInt COL_KAPPA_SRC QKECCAK_COMMITTED_COL) ≠ (TABLE_KECCAK + 2) then
      pure () -- no use of this definition takes this branch
    else
      if (arrInt COL_KAPPA_ADJ QKECCAK_COMMITTED_COL) ≠ QKECCAK_SLOT_LOG then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    let outEqChain ← B.heapBuf 41
    let _ ← B.call "eq_prefix_chain" [outEqChain.v, (← B.const 1).v, zVals.v, point1.v, (← B.shifted qkeccakvG.base qkeccakvG.exp).v] 0
    let rsWeight ← call1 "ring_switch_weight" [(← B.shifted zVals QKECCAK_VARS_CAP).v, point1.v, cTable.v, (← B.shifted qkeccakvG.base qkeccakvG.exp).v]
    innerSum ← B.add innerSum (← B.mul (← B.add rsWeight (← B.mul lamOut (← B.load (← B.mul outEqChain qkeccakvG.base) qkeccakvG.exp))) (cellOf selectors QKECCAK_COMMITTED_COL))
    let oodChain ← B.heapBuf 31
    let _ ← B.call "eq_prefix_chain" [oodChain.v, (← B.mul lamOut lamCl).v, oodZ.v, point1.v, gmv.v] 0
    B.assertEq (← B.mul (← B.add innerSum (← B.load (← B.mul oodChain gmv) 0)) yrAtTail) sumcheckTarget
    return []

set_option linter.unusedVariables false in
/-- `verify_sub` (`guests/lean_ethereum.py`, line 3539):

```
def verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, defer_out):
    # In-circuit verification of ONE inner proof for the statement (pi_0, pi_1),
    # mirroring `crates/verifier` step for step; the `# ---- ... ----` headers below run
    # in that order. All proof data is hinted HERE, so each call pops the next
    # sub-proof's entry of every witness stream and the body lowers once. The
    # exponent tables are shared read-only; the deferred claim goes to `defer_out`.
    #
    # The pool holds every committed-coordinate claim's value in decompose order
    # (the points are the GKR zetas, resolvable from the baked block structure) and
    # its certified low dimension, which the terminal pins its lengths against.
    claim_pool = HeapBuf(N_CLAIMS)
    tabs = g_squares * GEN ** WIN_TAB_AT

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    # The sponge's first permutation takes the program digest and the statement as
    # its rate, from the zero state.
    sp = StackBuf(KECCAK_STATE)
    keccak_cells([seed_0, seed_1, pi_0, pi_1], sp, final=0)
    stream = HeapBuf(STREAM_CAP)
    hint_witness(stream[0:STREAM_CAP], "stream")
    cursor = stream  # the proof stream, replayed word by word (advance = * g)

    # ---- announced layout and PCS rate (observed, then certified) ----
    # The stream announces the memory's log size and each table's row count as
    # integer WORDS; the shape-generic phases need logs as G-POWERS (loop bounds,
    # match scrutinees). log_mem is reassembled from its advice-decomposed bits, with
    # no hint and no g^j -> j lookup. A table's log height is advice, which
    # verify_tables certifies to be the least holding its rows, above its floor.
    table_rows = HeapBuf(N_TABLES)
    rate = StackBuf(8)
    for i in unroll(0, N_TABLES + 1):
        if i % 4 == 0:
            if i != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        x, cursor = fs_next(rate, i % 4, cursor)
        if i == 0:
            log_mem_word = x
        else:
            table_rows[GEN ** (i - 1)] = x
    if const((N_TABLES + 1) % 4 == 0):
        sp = fs_perm(sp, rate, 4)
        rate = StackBuf(8)
    log_inv_rate, cursor = fs_next(rate, (N_TABLES + 1) % 4, cursor)
    rate_sel = g_power_of_word(log_inv_rate) / GEN
    assert log(rate_sel) < LIG_N_RATES
    dims_g = HeapBuf(N_TABLES + 1)  # [g^log_mem, g^tau_0 .. g^tau_{N_TABLES-1}]
    g_log_mem = g_power_of_word(log_mem_word)
    assert log(g_log_mem) < MAX_LOG_MEM + 1  # native log_mem <= MAX_LOG_MEM
    assert log(g_log_mem / GEN ** MIN_LOG_MEM) < COUNT_BITS  # native MIN_LOG_MEM <= log_mem
    dims_g[GEN ** 0] = g_log_mem
    hint_witness(dims_g[1:1 + N_TABLES], "table_logs")  # certified in verify_tables
    # kappa_base maps a kappa source index to its certified log (source 0
    # = const via the baked adj). Each block's kappa then DERIVES from its
    # structural source as a compile-time offset off a certified log: no hint, and
    # nothing left free.
    kappa_base = HeapBuf(N_TABLES + 2)
    kb = StackBuf(N_TABLES + 2)  # the same, in the frame
    kb[0] = 1
    kb[1] = g_log_mem
    for t in unroll(0, N_TABLES):
        kb[2 + t] = dims_g[GEN ** (t + 1)]
    for i in unroll(0, N_TABLES + 2):
        kappa_base[GEN ** i] = kb[i]
    # The ONE bus depth, COMPUTED (not hinted): mu = log2_ceil(Σ_b 2^κ_b) over
    # PUSH's blocks; pull matches by pairing, the count tree is padded to it.
    push_total = GEN ** 0
    for b in unroll(SIDE_BLOCK_START[PUSH_SIDE], SIDE_BLOCK_START[PUSH_SIDE + 1]):
        push_total *= g_squares[kb[BLOCK_KAPPA_SRC[b]] * GEN ** BLOCK_KAPPA_ADJ[b]]  # g^(sum of 2^kappa)
    g_bus_mu = log2_ceil_in_the_exponent(push_total, g_squares, 0, SIZE_BITS)
    zeta = HeapBuf(g_bus_mu)  # the ONE shared GKR point: exactly mu coords

    # ---- commitment root (2 words), kept for the opening phase ----
    # The announcement's N_TABLES + 2 words, then the root's two, wait as one run.
    if const((N_TABLES + 2) % 4 == 0):
        sp = fs_perm(sp, rate, 4)
        rate = StackBuf(8)
    commit_root_0, cursor = fs_next(rate, (N_TABLES + 2) % 4, cursor)
    if const((N_TABLES + 3) % 4 == 0):
        sp = fs_perm(sp, rate, 4)
        rate = StackBuf(8)
    commit_root_1, cursor = fs_next(rate, (N_TABLES + 3) % 4, cursor)

    # ---- the committed size: placement, then g^m, m = max(log2_ceil(sum_cols 2^kappa), PCS_MIN_MU) ----
    # g_total is g^(sum 2^kappa) from the certified placement walk.
    g_total, col_offsets = certify_placement(kappa_base, g_squares)
    gmv = log2_ceil_in_the_exponent(g_total, g_squares, PCS_MIN_MU, SIZE_BITS)  # g^m
    size_sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN)
    assert log(size_sel) < LIG_N_LOG_SIZES

    # ---- the level-0 OOD sample (verifier read_ood) ----
    # A grind, then z of the stack's m variables, the first drawn by the grind's
    # permutation, then the stack's value at z.
    sp, z_first, cursor = fs_grind_squeeze(sp, rate, (N_TABLES + 3) % 4 + 1, cursor, tabs, OOD_GRIND_BITS)
    ood_z = HeapBuf(MAX_STACK_LOG)
    fs0, fs1, fs2, fs3, fs4 = match(log(size_sel), range(0, LIG_N_LOG_SIZES), lambda s: squeeze_point_from(sp[8], sp[9], sp[10], sp[11], sp[12], z_first, ood_z, LIG_MIN_LOG_SIZE + s))
    ood_value = HeapBuf(1)
    # The bus's grind nonce joins the value: its permutation draws the first weight.
    word0, pow_word, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, ood_value, 1, 1)

    # ---- bus challenges ----
    # They fail with probability at most 2^mu / |E| (verifier::bus), so a grind of
    # BUS_GRIND_BITS[mu] comes first, mu the push side's depth: at least BUS_MIN_MU,
    # its least over executions of this bytecode. A tuple is fingerprinted linearly: slot x weighs its own
    # challenge fp_w[x] (doc sec:gp).
    bus_grind = g_bus_mu * INV_GEN ** BUS_MIN_MU
    assert log(bus_grind) < BUS_GRIND_ARMS
    done = match(log(bus_grind), range(0, BUS_GRIND_ARMS), lambda d: bus_grind_check(pow_word, tabs, d))  # a match needs a target
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    no_rate = StackBuf(8)
    fp_w = HeapBuf(N_TUPLE_SLOTS)
    fp_w[GEN ** 0] = word0
    for x in unroll(1, N_TUPLE_SLOTS):
        sp, wx = squeeze(sp, no_rate, 0)
        fp_w[GEN ** x] = wx
    sp, beta = squeeze(sp, no_rate, 0)

    # ---- ONE GKR grand product: every tree batched ----
    fs0, fs1, fs2, fs3, fs4, cursor, gkr_leaves = verify_bus_gkr(sp[8], sp[9], sp[10], sp[11], sp[12], cursor, g_bus_mu, zeta, tabs)

    # ---- the bus leaves, the table sumcheck, and the public-input claim ----
    chi = HeapBuf(SIZE_BITS)  # chi[i] = the challenge that bound variable i
    bc_point = HeapBuf(N_TUPLE_BITS)
    fs0, fs1, fs2, fs3, fs4, cursor, g_zc_n, bc_value, rm, col_eval_words = verify_tables(fs0, fs1, fs2, fs3, fs4, cursor, pi_0, pi_1, zeta, g_bus_mu, dims_g, table_rows, g_squares, fp_w, beta, claim_pool, chi, gkr_leaves, tabs, bc_point)

    # ---- KECCAK validity, by GKR over the rounds ----
    tau_keccak_g = dims_g[GEN ** (TABLE_KECCAK + 1)]  # the KECCAK table's certified tau
    z_vals = HeapBuf(2 * QKECCAK_VARS_CAP)
    slices = HeapBuf(BASE_FIELD_BITS)
    fs0, fs1, fs2, fs3, fs4, cursor, keccak_word = verify_keccak(fs0, fs1, fs2, fs3, fs4, cursor, tau_keccak_g, chi, col_eval_words * GEN ** (KECCAK_OUT_POOL - N_BUS_CLAIMS), z_vals, slices, tabs)
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)

    # ---- stacked mixed opening: ring-switch front + claim combination ----
    # The input opening's slices were read and bound above; this block only binds
    # them to the commitment. Phi(v) = sum_p f_p Psi(v)^(2^(8p)), Psi(v) = sum_b g_b v^(2^b):
    # its expansion has all 64 Frobenius terms soundness needs.
    # One grind covers the map's challenges and the batching challenge lam_cl, drawn
    # next: one verifier message.
    rate = StackBuf(8)
    ch = StackBuf(2 * RING_MAP_WIDTH)  # f_0 .. f_7, then g_0 .. g_7
    sp, map_first, cursor = fs_grind_squeeze(sp, rate, 0, cursor, tabs, BATCH_GRIND_BITS)
    ch[0] = map_first
    for i in unroll(1, 2 * RING_MAP_WIDTH):
        sp, map_challenge = squeeze(sp, rate, 0)
        ch[i] = map_challenge
    map_challenges = HeapBuf(2 * RING_MAP_WIDTH)
    for i in unroll(0, 2 * RING_MAP_WIDTH):
        map_challenges[GEN ** i] = ch[i]
    # The same map as a Frobenius sum, for the transparent weight: c_(8p+b) = f_p g_b^(2^(8p)).
    c_table = HeapBuf(BASE_FIELD_BITS)
    for b in unroll(0, RING_MAP_WIDTH):
        power = ch[RING_MAP_WIDTH + b]
        for p in unroll(0, RING_MAP_WIDTH):
            c_table[GEN ** (RING_MAP_WIDTH * p + b)] = ch[p] * power
            if const(p + 1 != RING_MAP_WIDTH):
                for t in unroll(0, RING_MAP_WIDTH):
                    power = power * power
    target_in = ring_switch_target(slices, map_challenges)
    # ONE batching challenge for the whole pool: N_CLAIMS - 1 fewer Fiat-Shamir
    # hashes than a challenge per claim, and none for the values themselves,
    # `fs_next` having bound every one it read and the public-input ones deriving
    # from the seeded statement and rm, so `lam_cl` already depends on all of
    # them. Disjoint power ranges, as for the zc_xi-powers above:
    # the ring-switch claim takes lam_cl^0, the pool lam_cl^1 onward (bar the output
    # lanes' claims, which the Keccak reduction consumed), and the Keccak reduction's
    # claim on its committed outputs the power after the pool's last.
    sp, lam_cl = squeeze(sp, rate, 0)
    target = target_in
    lam_pow = lam_cl
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] != POINT_BUF_KECCAK_OUT:
            if const(j // N_BUS_CLAIMS == 0):
                target += lam_pow * claim_pool[GEN ** j]
            else:
                if const((j - N_BUS_CLAIMS) // N_COL_EVALS == 0):
                    target += lam_pow * col_eval_words[GEN ** (j - N_BUS_CLAIMS)]
                else:
                    target += lam_pow * claim_pool[GEN ** j]
            lam_pow *= lam_cl
    target += lam_pow * keccak_word
    # The OOD sample's claim closes the batch.
    target += lam_pow * lam_cl * ood_value[1]
    # One arm per size, the rate passed on. Both are transcript-bound and range-checked
    # above, so a single compiled guest dispatches independently for every inner proof
    # in a mixed-rate batch.
    sumcheck_target, point, point1, inner_total, yr_at_tail = match(log(size_sel), range(0, LIG_N_LOG_SIZES), lambda m_idx: open_stacked(m_idx, rate_sel, sp[8], sp[9], sp[10], sp[11], sp[12], target, commit_root_0, commit_root_1, cursor, tabs))
    # `stream` is a fixed-capacity witness transport. The shape fixes the exact
    # consumed prefix, whose every word is transcript-bound; the unused suffix
    # is outside the recursively verified proof and intentionally unconstrained.

    # ---- generalized eval_b terminal (runtime claim shapes) ----
    check_opening_terminal(g_squares, zeta, chi, rm, g_bus_mu, g_zc_n, g_log_mem, tau_keccak_g, kappa_base, lam_cl, col_offsets, z_vals, c_table, point, point1, inner_total, yr_at_tail, sumcheck_target, ood_z, gmv)

    # ---- export this sub-proof's deferred-claim data to the caller (FRESH_*) ----
    for k in unroll(0, BYTECODE_LOG):
        defer_out[GEN ** k] = zeta[GEN ** k]
    for k in unroll(0, LOG2_BYTECODE_COLS):
        defer_out[GEN ** (BYTECODE_LOG + k)] = bc_point[GEN ** k]
    defer_out[GEN ** FRESH_BC_VALUE] = bc_value
    return
```
-/
def verifySub : GFn where
  name := "verify_sub"
  arity := 6
  rets := 0
  body ps := do
    let pi0 := cellOf ps 0
    let pi1 := cellOf ps 1
    let seed0 := cellOf ps 2
    let seed1 := cellOf ps 3
    let gSquares := cellOf ps 4
    let deferOut := cellOf ps 5
    let claimPool ← B.heapBuf N_CLAIMS
    let tabs : Shifted := ⟨gSquares, WIN_TAB_AT⟩
    let mut sp ← B.stackBuf KECCAK_STATE
    B.keccakCells (cells := (.words [.cell seed0.v, .cell seed1.v, .cell pi0.v, .cell pi1.v])) (final := false) (out := (.frame sp))
    let stream ← B.heapBuf STREAM_CAP
    B.witness "stream" (.heap stream.v 0 STREAM_CAP)
    let cursor := stream
    let tableRows ← B.heapBuf N_TABLES
    let mut rate ← B.stackBuf 8
    let mut x : Word := default
    let mut cursor_ptr : Shifted := default
    let mut logMemWord : Word := default
    let i_k := 0
    if (i_k % 4) = 0 then
      if i_k ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    let (t0, t1) ← fsNext rate (i_k % 4) cursor
    x := t0
    cursor_ptr := t1
    if i_k = 0 then
      logMemWord := x
    else
      pure () -- no use of this definition takes this branch
    for i_k in [1:N_TABLES + 1] do
      if (i_k % 4) = 0 then
        if i_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      let (t0, t1) ← fsNext_2 rate (i_k % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      x := t0
      cursor_ptr := t1
      if i_k = 0 then
        pure () -- no use of this definition takes this branch
      else
        B.store tableRows (i_k - 1) x
    if ((N_TABLES + 1) % 4) = 0 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    let (t2, t3) ← fsNext_2 rate ((N_TABLES + 1) % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let logInvRate := t2
    cursor_ptr := t3
    let rateSel ← B.fdiv (← call1 "g_power_of_word" [logInvRate.v]) (← B.const (gpowE 1))
    let _ ← B.rangeCheck rateSel LIG_N_RATES
    let dimsG ← B.heapBuf 7
    let gLogMem ← call1 "g_power_of_word" [logMemWord.v]
    let _ ← B.rangeCheck gLogMem 31
    let t4 ← B.const (gpowE (COUNT_BITS - 1))
    let _ ← B.rangeCheckK (← B.fdiv gLogMem (← B.const (gpowE MIN_LOG_MEM))) t4
    B.store dimsG 0 gLogMem
    B.witness "table_logs" (.heap dimsG.v 1 ((1 + N_TABLES) - 1))
    let kappaBase ← B.heapBuf 8
    let kb ← B.stackBuf 8
    B.constInto (cellOf kb 0) 1
    B.copy (cellOf kb 1) gLogMem
    for t_k in [0:N_TABLES] do
      B.loadInto (cellOf kb (2 + t_k)) dimsG (t_k + 1)
    for i_k in [0:N_TABLES + 2] do
      B.store kappaBase i_k (cellOf kb i_k)
    let pushTotal : GPow := ⟨0⟩
    let mut pushTotal_word : Word := default
    let b_k := 0
    pushTotal_word ← B.load (← B.mul gSquares (cellOf kb (arrInt BLOCK_KAPPA_SRC b_k))) (arrInt BLOCK_KAPPA_ADJ b_k)
    for b_k in [1:arrInt SIDE_BLOCK_START (PUSH_SIDE + 1)] do
      pushTotal_word ← B.mul pushTotal_word (← B.load (← B.mul gSquares (cellOf kb (arrInt BLOCK_KAPPA_SRC b_k))) (arrInt BLOCK_KAPPA_ADJ b_k))
    let gBusMu ← call1 (instName "log2_ceil_in_the_exponent" [.L 0, .L SIZE_BITS]) [pushTotal_word.v, gSquares.v]
    let zeta ← B.heapBufDyn gBusMu
    if ((N_TABLES + 2) % 4) = 0 then
      sp ← fsPerm sp rate 4
      rate ← B.stackBuf 8
    else
      pure () -- no use of this definition takes this branch
    let (t5, t6) ← fsNext_2 rate ((N_TABLES + 2) % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let commitRoot0 := t5
    cursor_ptr := t6
    if ((N_TABLES + 3) % 4) = 0 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    let (t7, t8) ← fsNext_2 rate ((N_TABLES + 3) % 4) (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let commitRoot1 := t7
    cursor_ptr := t8
    let t9 ← B.call "certify_placement" [kappaBase.v, gSquares.v] 2
    let gTotal := t9[0]!
    let colOffsets := t9[1]!
    let gmv ← call1 (instName "log2_ceil_in_the_exponent" [.L PCS_MIN_MU, .L SIZE_BITS]) [gTotal.v, gSquares.v]
    let sizeSel ← B.mul gmv (← B.const (lit LIG_MIN_SHIFT_INV))
    let _ ← B.rangeCheck sizeSel LIG_N_LOG_SIZES
    let (t10, t11, t12) ← fsGrindSqueeze_3 sp rate (((N_TABLES + 3) % 4) + 1) (⟨cursor_ptr.base, cursor_ptr.exp⟩) (⟨tabs.base, tabs.exp⟩) OOD_GRIND_BITS
    sp := t10
    let zFirst := t11
    cursor_ptr := t12
    let oodZ ← B.heapBuf MAX_STACK_LOG
    let t13 ← B.targets [none, none, none, none, none]
    B.dispatchInto sizeSel ((List.range 11).map fun arm => (instName "squeeze_point_from" [.L (LIG_MIN_LOG_SIZE + arm)])) [(cellOf sp 8).v, (cellOf sp 9).v, (cellOf sp 10).v, (cellOf sp 11).v, (cellOf sp 12).v, zFirst.v, oodZ.v] t13
    let fs0 := cellOf t13 0
    let fs1 := cellOf t13 1
    let fs2 := cellOf t13 2
    let fs3 := cellOf t13 3
    let fs4 := cellOf t13 4
    let oodValue ← B.heapBuf 1
    let t14 ← B.call (instName "opening_message" [.L 1, .L 1]) [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, (← B.shifted cursor_ptr.base cursor_ptr.exp).v, oodValue.v] 8
    let word0 := t14[0]!
    let powWord := t14[1]!
    let fs0 := t14[2]!
    let fs1 := t14[3]!
    let fs2 := t14[4]!
    let fs3 := t14[5]!
    let fs4 := t14[6]!
    let cursor := t14[7]!
    let busGrind ← B.mul gBusMu (← B.const ((lit INV_GEN) ^ BUS_MIN_MU))
    let _ ← B.rangeCheck busGrind BUS_GRIND_ARMS
    let t15 ← B.targets [none]
    let t16 ← B.shifted tabs.base tabs.exp
    B.dispatchInto busGrind ((List.range BUS_GRIND_ARMS).map fun arm => (instName "bus_grind_check" [.L arm])) [powWord.v, t16.v] t15
    let done := cellOf t15 0
    sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let noRate ← B.stackBuf 8
    let fpW ← B.heapBuf N_TUPLE_SLOTS
    B.store fpW 0 word0
    for x_k in [1:N_TUPLE_SLOTS] do
      let (t17, t18) ← squeeze sp noRate 0
      sp := t17
      let wx := t18
      B.store fpW x_k wx
    let (t19, t20) ← squeeze sp noRate 0
    sp := t19
    let beta := t20
    let t21 ← B.call "verify_bus_gkr" [(cellOf sp 8).v, (cellOf sp 9).v, (cellOf sp 10).v, (cellOf sp 11).v, (cellOf sp 12).v, cursor.v, gBusMu.v, zeta.v, (← B.shifted tabs.base tabs.exp).v] 7
    let fs0 := t21[0]!
    let fs1 := t21[1]!
    let fs2 := t21[2]!
    let fs3 := t21[3]!
    let fs4 := t21[4]!
    let cursor := t21[5]!
    let gkrLeaves := t21[6]!
    let chi ← B.heapBuf SIZE_BITS
    let bcPoint ← B.heapBuf N_TUPLE_BITS
    let t22 ← B.call "verify_tables" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, pi0.v, pi1.v, zeta.v, gBusMu.v, dimsG.v, tableRows.v, gSquares.v, fpW.v, beta.v, claimPool.v, chi.v, gkrLeaves.v, (← B.shifted tabs.base tabs.exp).v, bcPoint.v] 10
    let fs0 := t22[0]!
    let fs1 := t22[1]!
    let fs2 := t22[2]!
    let fs3 := t22[3]!
    let fs4 := t22[4]!
    let cursor := t22[5]!
    let gZcN := t22[6]!
    let bcValue := t22[7]!
    let rm := t22[8]!
    let colEvalWords := t22[9]!
    let tauKeccakG ← B.load dimsG 6
    let zVals ← B.heapBuf 78
    let slices ← B.heapBuf BASE_FIELD_BITS
    let t23 ← B.call "verify_keccak" [fs0.v, fs1.v, fs2.v, fs3.v, fs4.v, cursor.v, tauKeccakG.v, chi.v, (← B.shifted colEvalWords 101).v, zVals.v, slices.v, (← B.shifted tabs.base tabs.exp).v] 7
    let fs0 := t23[0]!
    let fs1 := t23[1]!
    let fs2 := t23[2]!
    let fs3 := t23[3]!
    let fs4 := t23[4]!
    let cursor := t23[5]!
    let keccakWord := t23[6]!
    sp ← fsCap fs0 fs1 fs2 fs3 fs4
    rate ← B.stackBuf 8
    let ch ← B.stackBuf 16
    let (t24, t25, t26) ← fsGrindSqueeze_4 sp rate 0 cursor (⟨tabs.base, tabs.exp⟩) BATCH_GRIND_BITS
    sp := t24
    let mapFirst := t25
    cursor_ptr := t26
    B.copy (cellOf ch 0) mapFirst
    for i_k in [1:2 * RING_MAP_WIDTH] do
      let (t27, t28) ← squeeze sp rate 0
      sp := t27
      let mapChallenge := t28
      B.copy (cellOf ch i_k) mapChallenge
    let mapChallenges ← B.heapBuf 16
    for i_k in [0:2 * RING_MAP_WIDTH] do
      B.store mapChallenges i_k (cellOf ch i_k)
    let cTable ← B.heapBuf BASE_FIELD_BITS
    for b_k in [0:RING_MAP_WIDTH] do
      let mut power := cellOf ch (RING_MAP_WIDTH + b_k)
      for p_k in [0:RING_MAP_WIDTH] do
        B.store cTable ((RING_MAP_WIDTH * p_k) + b_k) (← B.mul (cellOf ch p_k) power)
        if (p_k + 1) ≠ RING_MAP_WIDTH then
          for _ in [0:RING_MAP_WIDTH] do
            power ← B.mul power power
        else
          pure ()
    let targetIn ← call1 "ring_switch_target" [slices.v, mapChallenges.v]
    let (t29, t30) ← squeeze sp rate 0
    sp := t29
    let lamCl := t30
    let mut target := targetIn
    let mut lamPow := lamCl
    for j_k in [0:N_CLAIMS] do
      if (arrInt CLAIM_POINT_BUF j_k) ≠ POINT_BUF_KECCAK_OUT then
        if (j_k / N_BUS_CLAIMS) = 0 then
          target ← B.add target (← B.mul lamPow (← B.load claimPool j_k))
        else
          if ((j_k - N_BUS_CLAIMS) / N_COL_EVALS) = 0 then
            target ← B.add target (← B.mul lamPow (← B.load colEvalWords (j_k - N_BUS_CLAIMS)))
          else
            target ← B.add target (← B.mul lamPow (← B.load claimPool j_k))
        lamPow ← B.mul lamPow lamCl
      else
        pure ()
    target ← B.add target (← B.mul lamPow keccakWord)
    target ← B.add target (← B.mul (← B.mul lamPow lamCl) (← B.load oodValue 0))
    let t31 ← B.targets [none, none, none, none, none]
    let t32 ← B.shifted cursor_ptr.base cursor_ptr.exp
    let t33 ← B.shifted tabs.base tabs.exp
    B.dispatchInto sizeSel ((List.range 11).map fun arm => (instName "open_stacked" [.L arm])) [rateSel.v, (cellOf sp 8).v, (cellOf sp 9).v, (cellOf sp 10).v, (cellOf sp 11).v, (cellOf sp 12).v, target.v, commitRoot0.v, commitRoot1.v, t32.v, t33.v] t31
    let sumcheckTarget := cellOf t31 0
    let point := cellOf t31 1
    let point1 := cellOf t31 2
    let innerTotal := cellOf t31 3
    let yrAtTail := cellOf t31 4
    let _ ← B.call "check_opening_terminal" [gSquares.v, zeta.v, chi.v, rm.v, gBusMu.v, gZcN.v, gLogMem.v, tauKeccakG.v, kappaBase.v, lamCl.v, colOffsets.v, zVals.v, cTable.v, point.v, point1.v, innerTotal.v, yrAtTail.v, sumcheckTarget.v, oodZ.v, gmv.v] 0
    for k_k in [0:BYTECODE_LOG] do
      B.store deferOut k_k (← B.load zeta k_k)
    for k_k in [0:LOG2_BYTECODE_COLS] do
      B.store deferOut (BYTECODE_LOG + k_k) (← B.load bcPoint k_k)
    B.store deferOut FRESH_BC_VALUE bcValue
    return []

set_option linter.unusedVariables false in
/-- `sel_partial_nibble`, a `Const` family (`guests/lean_ethereum.py`, line 2121):

```
def sel_partial_nibble(eq_out, g_out, z, z1, gs, width: Const):
    if const(width != 0):
        sel_eq_nibble(eq_out, z, z1, width)
        sel_g_nibble(g_out, gs, width)
    return 0
```
-/
def selPartialNibble (width : Nat) : GFn where
  name := instName "sel_partial_nibble" [.L width]
  arity := 5
  rets := 1
  body ps := do
    let eqOut := cellOf ps 0
    let gOut := cellOf ps 1
    let z := cellOf ps 2
    let z1 := cellOf ps 3
    let gs := cellOf ps 4
    if width ≠ 0 then
      selEqNibble_2 eqOut z z1 width
      selGNibble_2 gOut gs width
    else
      pure ()
    return [.c 0]

set_option linter.unusedVariables false in
/-- `sel_partial_nibble`, a `Const` family (`guests/lean_ethereum.py`, line 2121):

```
def sel_partial_nibble(eq_out, g_out, z, z1, gs, width: Const):
    if const(width != 0):
        sel_eq_nibble(eq_out, z, z1, width)
        sel_g_nibble(g_out, gs, width)
    return 0
```
-/
def selPartialNibble_2 (width : Nat) : GFn where
  name := instName "sel_partial_nibble" [.L width]
  arity := 5
  rets := 1
  body ps := do
    let eqOut := cellOf ps 0
    let gOut := cellOf ps 1
    let z := cellOf ps 2
    let z1 := cellOf ps 3
    let gs := cellOf ps 4
    if width ≠ 0 then
      selEqNibble_3 eqOut z z1 width
      selGNibble_3 gOut gs width
    else
      pure () -- no use of this definition takes this branch
    return [.c 0]

set_option linter.unusedVariables false in
/-- `sel_partial_nibble`, a `Const` family (`guests/lean_ethereum.py`, line 2121):

```
def sel_partial_nibble(eq_out, g_out, z, z1, gs, width: Const):
    if const(width != 0):
        sel_eq_nibble(eq_out, z, z1, width)
        sel_g_nibble(g_out, gs, width)
    return 0
```
-/
def selPartialNibble_3 (width : Nat) : GFn where
  name := instName "sel_partial_nibble" [.L width]
  arity := 5
  rets := 1
  body ps := do
    let eqOut := cellOf ps 0
    let gOut := cellOf ps 1
    let z := cellOf ps 2
    let z1 := cellOf ps 3
    let gs := cellOf ps 4
    if width ≠ 0 then
      selEqNibble eqOut z z1 width
      selGNibble gOut gs width
    else
      pure () -- no use of this definition takes this branch
    return [.c 0]

set_option linter.unusedVariables false in
/-- `padding_weight`, a `Const` family (`guests/lean_ethereum.py`, line 2220):

```
def padding_weight(rows, zeta, tau: Const):
    # pad_n(zeta[..tau]) for n = rows <= 2^tau (doc lem:suffix). The advice is the bits
    # of n + (2^tau - 1): the complements of n's low bits, as the step reads them, then
    # n's bit tau, set only alone.
    word = rows + const(2 ** tau - 1)
    bits = StackBuf(N_COLUMN_LOGS)
    hint_decompose_bits(bits, word, tau + 1)
    pad = 1
    for k in unroll(0, tau):
        c = bits[k]
        bits[k] = c * c
        z = zeta[GEN ** k]
        pad = c * z + (c + z) * pad
    top = bits[tau]
    bits[tau] = top * top
    # tau is the least height holding n iff lead == 1 and rest != 0: n's highest
    # bit is tau - 1 with more below it, or n = 2^tau.
    if tau == 0:
        low = 0
        lead = 1
        rest = 1
    else:
        # The bits below bit tau - 1, by Horner from their high end: one constant, 2.
        below = 0
        for k in unroll(1, tau):
            below = below * 2 + bits[tau - 1 - k]
        low = below + bits[tau - 1] * (2 ** (tau - 1))
        lead = top + 1 + bits[tau - 1]
        rest = top + below + const(2 ** (tau - 1) - 1)
    assert low + top * (2 ** tau) == word
    assert top * (low + const(2 ** tau - 1)) == 0
    return (1 + top) * pad, lead, rest
```
-/
def paddingWeight (tau : Nat) : GFn where
  name := instName "padding_weight" [.L tau]
  arity := 2
  rets := 3
  body ps := do
    let rows := cellOf ps 0
    let zeta := cellOf ps 1
    let word' := rows
    let bits ← B.stackBuf N_COLUMN_LOGS
    B.hintBits (.stack (bits.take (tau + 1))) word' 0 (tau + 1)
    let pad := 1
    let top := cellOf bits tau
    B.mulInto (cellOf bits tau) top top
    let mut low : Nat := default
    let mut lead : Nat := default
    let mut rest : Nat := default
    if tau = 0 then
      low := 0
      lead := 1
      rest := 1
    else
      pure () -- no use of this definition takes this branch
    B.assertEq top word'
    B.assertEq (← B.mul top (← B.const ((lit low) + (lit ((2 ^ tau) - 1))))) (← B.const 0)
    let t0 : V → B Unit := fun rc => do
      B.addInto (wordOf rc) (← B.const 1) top
    return [.into t0] ++ [.c (gpowE (Nat.log2 lead))] ++ [.c (gpowE (Nat.log2 rest))]

set_option linter.unusedVariables false in
/-- `padding_weight`, a `Const` family (`guests/lean_ethereum.py`, line 2220):

```
def padding_weight(rows, zeta, tau: Const):
    # pad_n(zeta[..tau]) for n = rows <= 2^tau (doc lem:suffix). The advice is the bits
    # of n + (2^tau - 1): the complements of n's low bits, as the step reads them, then
    # n's bit tau, set only alone.
    word = rows + const(2 ** tau - 1)
    bits = StackBuf(N_COLUMN_LOGS)
    hint_decompose_bits(bits, word, tau + 1)
    pad = 1
    for k in unroll(0, tau):
        c = bits[k]
        bits[k] = c * c
        z = zeta[GEN ** k]
        pad = c * z + (c + z) * pad
    top = bits[tau]
    bits[tau] = top * top
    # tau is the least height holding n iff lead == 1 and rest != 0: n's highest
    # bit is tau - 1 with more below it, or n = 2^tau.
    if tau == 0:
        low = 0
        lead = 1
        rest = 1
    else:
        # The bits below bit tau - 1, by Horner from their high end: one constant, 2.
        below = 0
        for k in unroll(1, tau):
            below = below * 2 + bits[tau - 1 - k]
        low = below + bits[tau - 1] * (2 ** (tau - 1))
        lead = top + 1 + bits[tau - 1]
        rest = top + below + const(2 ** (tau - 1) - 1)
    assert low + top * (2 ** tau) == word
    assert top * (low + const(2 ** tau - 1)) == 0
    return (1 + top) * pad, lead, rest
```
-/
def paddingWeight_2 (tau : Nat) : GFn where
  name := instName "padding_weight" [.L tau]
  arity := 2
  rets := 3
  body ps := do
    let rows := cellOf ps 0
    let zeta := cellOf ps 1
    let word' ← B.add rows (← B.const (lit ((2 ^ tau) - 1)))
    let bits ← B.stackBuf N_COLUMN_LOGS
    B.hintBits (.stack (bits.take (tau + 1))) word' 0 (tau + 1)
    let pad := 1
    let mut pad_word : Word := default
    let k_k := 0
    let c := cellOf bits k_k
    B.mulInto (cellOf bits k_k) c c
    let z ← B.load zeta k_k
    pad_word ← B.add (← B.mul c z) (← B.add c z)
    let top := cellOf bits tau
    B.mulInto (cellOf bits tau) top top
    let mut low : Word := default
    let mut lead : Word := default
    let mut rest : Word := default
    if tau = 0 then
      pure () -- no use of this definition takes this branch
    else
      let below := 0
      low := cellOf bits (tau - 1)
      lead ← B.add (← B.add top (← B.const 1)) (cellOf bits (tau - 1))
      rest := top
    B.assertEq (← B.add low (← B.mul top (← B.const ((lit 2) ^ tau)))) word'
    B.assertEq (← B.mul top (← B.add low (← B.const (lit ((2 ^ tau) - 1))))) (← B.const 0)
    let t0 : V → B Unit := fun rc => do
      B.mulInto (wordOf rc) (← B.add (← B.const 1) top) pad_word
    return [.into t0] ++ [.v lead.v] ++ [.v rest.v]

set_option linter.unusedVariables false in
/-- `padding_weight`, a `Const` family (`guests/lean_ethereum.py`, line 2220):

```
def padding_weight(rows, zeta, tau: Const):
    # pad_n(zeta[..tau]) for n = rows <= 2^tau (doc lem:suffix). The advice is the bits
    # of n + (2^tau - 1): the complements of n's low bits, as the step reads them, then
    # n's bit tau, set only alone.
    word = rows + const(2 ** tau - 1)
    bits = StackBuf(N_COLUMN_LOGS)
    hint_decompose_bits(bits, word, tau + 1)
    pad = 1
    for k in unroll(0, tau):
        c = bits[k]
        bits[k] = c * c
        z = zeta[GEN ** k]
        pad = c * z + (c + z) * pad
    top = bits[tau]
    bits[tau] = top * top
    # tau is the least height holding n iff lead == 1 and rest != 0: n's highest
    # bit is tau - 1 with more below it, or n = 2^tau.
    if tau == 0:
        low = 0
        lead = 1
        rest = 1
    else:
        # The bits below bit tau - 1, by Horner from their high end: one constant, 2.
        below = 0
        for k in unroll(1, tau):
            below = below * 2 + bits[tau - 1 - k]
        low = below + bits[tau - 1] * (2 ** (tau - 1))
        lead = top + 1 + bits[tau - 1]
        rest = top + below + const(2 ** (tau - 1) - 1)
    assert low + top * (2 ** tau) == word
    assert top * (low + const(2 ** tau - 1)) == 0
    return (1 + top) * pad, lead, rest
```
-/
def paddingWeight_3 (tau : Nat) : GFn where
  name := instName "padding_weight" [.L tau]
  arity := 2
  rets := 3
  body ps := do
    let rows := cellOf ps 0
    let zeta := cellOf ps 1
    let word' ← B.add rows (← B.const (lit ((2 ^ tau) - 1)))
    let bits ← B.stackBuf N_COLUMN_LOGS
    B.hintBits (.stack (bits.take (tau + 1))) word' 0 (tau + 1)
    let pad := 1
    let mut pad_word : Word := default
    let k_k := 0
    let c := cellOf bits k_k
    B.mulInto (cellOf bits k_k) c c
    let z ← B.load zeta k_k
    pad_word ← B.add (← B.mul c z) (← B.add c z)
    let k_k := 1
    let c := cellOf bits k_k
    B.mulInto (cellOf bits k_k) c c
    let z ← B.load zeta k_k
    pad_word ← B.add (← B.mul c z) (← B.mul (← B.add c z) pad_word)
    let top := cellOf bits tau
    B.mulInto (cellOf bits tau) top top
    let mut low : Word := default
    let mut lead : Word := default
    let mut rest : Word := default
    if tau = 0 then
      pure () -- no use of this definition takes this branch
    else
      let below := 0
      let mut below_word : Word := default
      let k_k := 1
      below_word := cellOf bits ((tau - 1) - k_k)
      low ← B.add below_word (← B.mul (cellOf bits (tau - 1)) (← B.const ((lit 2) ^ (tau - 1))))
      lead ← B.add (← B.add top (← B.const 1)) (cellOf bits (tau - 1))
      rest ← B.add (← B.add top below_word) (← B.const (lit ((2 ^ (tau - 1)) - 1)))
    B.assertEq (← B.add low (← B.mul top (← B.const ((lit 2) ^ tau)))) word'
    B.assertEq (← B.mul top (← B.add low (← B.const (lit ((2 ^ tau) - 1))))) (← B.const 0)
    let t0 : V → B Unit := fun rc => do
      B.mulInto (wordOf rc) (← B.add (← B.const 1) top) pad_word
    return [.into t0] ++ [.v lead.v] ++ [.v rest.v]

set_option linter.unusedVariables false in
/-- `padding_weight`, a `Const` family (`guests/lean_ethereum.py`, line 2220):

```
def padding_weight(rows, zeta, tau: Const):
    # pad_n(zeta[..tau]) for n = rows <= 2^tau (doc lem:suffix). The advice is the bits
    # of n + (2^tau - 1): the complements of n's low bits, as the step reads them, then
    # n's bit tau, set only alone.
    word = rows + const(2 ** tau - 1)
    bits = StackBuf(N_COLUMN_LOGS)
    hint_decompose_bits(bits, word, tau + 1)
    pad = 1
    for k in unroll(0, tau):
        c = bits[k]
        bits[k] = c * c
        z = zeta[GEN ** k]
        pad = c * z + (c + z) * pad
    top = bits[tau]
    bits[tau] = top * top
    # tau is the least height holding n iff lead == 1 and rest != 0: n's highest
    # bit is tau - 1 with more below it, or n = 2^tau.
    if tau == 0:
        low = 0
        lead = 1
        rest = 1
    else:
        # The bits below bit tau - 1, by Horner from their high end: one constant, 2.
        below = 0
        for k in unroll(1, tau):
            below = below * 2 + bits[tau - 1 - k]
        low = below + bits[tau - 1] * (2 ** (tau - 1))
        lead = top + 1 + bits[tau - 1]
        rest = top + below + const(2 ** (tau - 1) - 1)
    assert low + top * (2 ** tau) == word
    assert top * (low + const(2 ** tau - 1)) == 0
    return (1 + top) * pad, lead, rest
```
-/
def paddingWeight_4 (tau : Nat) : GFn where
  name := instName "padding_weight" [.L tau]
  arity := 2
  rets := 3
  body ps := do
    let rows := cellOf ps 0
    let zeta := cellOf ps 1
    let word' ← B.add rows (← B.const (lit ((2 ^ tau) - 1)))
    let bits ← B.stackBuf N_COLUMN_LOGS
    B.hintBits (.stack (bits.take (tau + 1))) word' 0 (tau + 1)
    let pad := 1
    let mut pad_word : Word := default
    let k_k := 0
    let c := cellOf bits k_k
    B.mulInto (cellOf bits k_k) c c
    let z ← B.load zeta k_k
    pad_word ← B.add (← B.mul c z) (← B.add c z)
    for k_k in [1:tau] do
      let c := cellOf bits k_k
      B.mulInto (cellOf bits k_k) c c
      let z ← B.load zeta k_k
      pad_word ← B.add (← B.mul c z) (← B.mul (← B.add c z) pad_word)
    let top := cellOf bits tau
    B.mulInto (cellOf bits tau) top top
    let mut low : Word := default
    let mut lead : Word := default
    let mut rest : Word := default
    if tau = 0 then
      pure () -- no use of this definition takes this branch
    else
      let below := 0
      let mut below_word : Word := default
      let k_k := 1
      below_word := cellOf bits ((tau - 1) - k_k)
      let k_k := 2
      below_word ← B.add (← B.shifted below_word 1) (cellOf bits ((tau - 1) - k_k))
      low ← B.add below_word (← B.mul (cellOf bits (tau - 1)) (← B.const ((lit 2) ^ (tau - 1))))
      lead ← B.add (← B.add top (← B.const 1)) (cellOf bits (tau - 1))
      rest ← B.add (← B.add top below_word) (← B.const (lit ((2 ^ (tau - 1)) - 1)))
    B.assertEq (← B.add low (← B.mul top (← B.const ((lit 2) ^ tau)))) word'
    B.assertEq (← B.mul top (← B.add low (← B.const (lit ((2 ^ tau) - 1))))) (← B.const 0)
    let t0 : V → B Unit := fun rc => do
      B.mulInto (wordOf rc) (← B.add (← B.const 1) top) pad_word
    return [.into t0] ++ [.v lead.v] ++ [.v rest.v]

set_option linter.unusedVariables false in
/-- `padding_weight`, a `Const` family (`guests/lean_ethereum.py`, line 2220):

```
def padding_weight(rows, zeta, tau: Const):
    # pad_n(zeta[..tau]) for n = rows <= 2^tau (doc lem:suffix). The advice is the bits
    # of n + (2^tau - 1): the complements of n's low bits, as the step reads them, then
    # n's bit tau, set only alone.
    word = rows + const(2 ** tau - 1)
    bits = StackBuf(N_COLUMN_LOGS)
    hint_decompose_bits(bits, word, tau + 1)
    pad = 1
    for k in unroll(0, tau):
        c = bits[k]
        bits[k] = c * c
        z = zeta[GEN ** k]
        pad = c * z + (c + z) * pad
    top = bits[tau]
    bits[tau] = top * top
    # tau is the least height holding n iff lead == 1 and rest != 0: n's highest
    # bit is tau - 1 with more below it, or n = 2^tau.
    if tau == 0:
        low = 0
        lead = 1
        rest = 1
    else:
        # The bits below bit tau - 1, by Horner from their high end: one constant, 2.
        below = 0
        for k in unroll(1, tau):
            below = below * 2 + bits[tau - 1 - k]
        low = below + bits[tau - 1] * (2 ** (tau - 1))
        lead = top + 1 + bits[tau - 1]
        rest = top + below + const(2 ** (tau - 1) - 1)
    assert low + top * (2 ** tau) == word
    assert top * (low + const(2 ** tau - 1)) == 0
    return (1 + top) * pad, lead, rest
```
-/
def paddingWeight_5 (tau : Nat) : GFn where
  name := instName "padding_weight" [.L tau]
  arity := 2
  rets := 3
  body ps := do
    let rows := cellOf ps 0
    let zeta := cellOf ps 1
    let word' ← B.add rows (← B.const (lit ((2 ^ tau) - 1)))
    let bits ← B.stackBuf N_COLUMN_LOGS
    B.hintBits (.stack (bits.take (tau + 1))) word' 0 (tau + 1)
    let pad := 1
    let mut pad_word : Word := default
    let k_k := 0
    let c := cellOf bits k_k
    B.mulInto (cellOf bits k_k) c c
    let z ← B.load zeta k_k
    pad_word ← B.add (← B.mul c z) (← B.add c z)
    for k_k in [1:tau] do
      let c := cellOf bits k_k
      B.mulInto (cellOf bits k_k) c c
      let z ← B.load zeta k_k
      pad_word ← B.add (← B.mul c z) (← B.mul (← B.add c z) pad_word)
    let top := cellOf bits tau
    B.mulInto (cellOf bits tau) top top
    let mut low : Word := default
    let mut lead : Word := default
    let mut rest : Word := default
    if tau = 0 then
      pure () -- no use of this definition takes this branch
    else
      let below := 0
      let mut below_word : Word := default
      let k_k := 1
      below_word := cellOf bits ((tau - 1) - k_k)
      for k_k in [2:tau] do
        below_word ← B.add (← B.shifted below_word 1) (cellOf bits ((tau - 1) - k_k))
      low ← B.add below_word (← B.mul (cellOf bits (tau - 1)) (← B.const ((lit 2) ^ (tau - 1))))
      lead ← B.add (← B.add top (← B.const 1)) (cellOf bits (tau - 1))
      rest ← B.add (← B.add top below_word) (← B.const (lit ((2 ^ (tau - 1)) - 1)))
    B.assertEq (← B.add low (← B.mul top (← B.const ((lit 2) ^ tau)))) word'
    B.assertEq (← B.mul top (← B.add low (← B.const (lit ((2 ^ tau) - 1))))) (← B.const 0)
    let t0 : V → B Unit := fun rc => do
      B.mulInto (wordOf rc) (← B.add (← B.const 1) top) pad_word
    return [.into t0] ++ [.v lead.v] ++ [.v rest.v]

set_option linter.unusedVariables false in
/-- `block_selector`, a `Const` family (`guests/lean_ethereum.py`, line 2202):

```
def block_selector(sel_bits, zeta1_hi, idxc_hi, n: Const):
    # A bus block's eq over its n = mu - κ selector bits, the offset's bits above κ,
    # each boolean-pinned, and g^offset rebuilt from those bits alone (weights
    # g^(2^(κ+k)) = idxc_hi[k] + 1), which the caller pins to the certified offset.
    eq = GEN ** 0
    rebuilt = GEN ** 0
    for k in unroll(0, n):
        sbit = sel_bits[GEN ** k]
        sel_bits[GEN ** k] = sbit * sbit  # booleanity as a write-once pin
        if k == 0:
            eq = sbit + zeta1_hi[GEN ** k]  # eq over GF(2) is 1 + b + z
            rebuilt = 1 + sbit * idxc_hi[GEN ** k]
        else:
            eq *= sbit + zeta1_hi[GEN ** k]
            rebuilt *= 1 + sbit * idxc_hi[GEN ** k]
    return eq, rebuilt
```
-/
def blockSelector (n : Nat) : GFn where
  name := instName "block_selector" [.L n]
  arity := 3
  rets := 2
  body ps := do
    let selBits := cellOf ps 0
    let zeta1Hi := cellOf ps 1
    let idxcHi := cellOf ps 2
    let eq : GPow := ⟨0⟩
    let rebuilt : GPow := ⟨0⟩
    return [.c (gpowE eq.exp)] ++ [.c (gpowE rebuilt.exp)]

set_option linter.unusedVariables false in
/-- `block_selector`, a `Const` family (`guests/lean_ethereum.py`, line 2202):

```
def block_selector(sel_bits, zeta1_hi, idxc_hi, n: Const):
    # A bus block's eq over its n = mu - κ selector bits, the offset's bits above κ,
    # each boolean-pinned, and g^offset rebuilt from those bits alone (weights
    # g^(2^(κ+k)) = idxc_hi[k] + 1), which the caller pins to the certified offset.
    eq = GEN ** 0
    rebuilt = GEN ** 0
    for k in unroll(0, n):
        sbit = sel_bits[GEN ** k]
        sel_bits[GEN ** k] = sbit * sbit  # booleanity as a write-once pin
        if k == 0:
            eq = sbit + zeta1_hi[GEN ** k]  # eq over GF(2) is 1 + b + z
            rebuilt = 1 + sbit * idxc_hi[GEN ** k]
        else:
            eq *= sbit + zeta1_hi[GEN ** k]
            rebuilt *= 1 + sbit * idxc_hi[GEN ** k]
    return eq, rebuilt
```
-/
def blockSelector_2 (n : Nat) : GFn where
  name := instName "block_selector" [.L n]
  arity := 3
  rets := 2
  body ps := do
    let selBits := cellOf ps 0
    let zeta1Hi := cellOf ps 1
    let idxcHi := cellOf ps 2
    let eq : GPow := ⟨0⟩
    let rebuilt : GPow := ⟨0⟩
    let mut eq_word : Word := default
    let mut rebuilt_word : Word := default
    let k_k := 0
    let sbit ← B.load selBits k_k
    B.store selBits k_k (← B.mul sbit sbit)
    if k_k = 0 then
      eq_word ← B.add sbit (← B.load zeta1Hi k_k)
      rebuilt_word ← B.add (← B.const 1) (← B.mul sbit (← B.load idxcHi k_k))
    else
      pure () -- no use of this definition takes this branch
    return [.v eq_word.v] ++ [.v rebuilt_word.v]

set_option linter.unusedVariables false in
/-- `block_selector`, a `Const` family (`guests/lean_ethereum.py`, line 2202):

```
def block_selector(sel_bits, zeta1_hi, idxc_hi, n: Const):
    # A bus block's eq over its n = mu - κ selector bits, the offset's bits above κ,
    # each boolean-pinned, and g^offset rebuilt from those bits alone (weights
    # g^(2^(κ+k)) = idxc_hi[k] + 1), which the caller pins to the certified offset.
    eq = GEN ** 0
    rebuilt = GEN ** 0
    for k in unroll(0, n):
        sbit = sel_bits[GEN ** k]
        sel_bits[GEN ** k] = sbit * sbit  # booleanity as a write-once pin
        if k == 0:
            eq = sbit + zeta1_hi[GEN ** k]  # eq over GF(2) is 1 + b + z
            rebuilt = 1 + sbit * idxc_hi[GEN ** k]
        else:
            eq *= sbit + zeta1_hi[GEN ** k]
            rebuilt *= 1 + sbit * idxc_hi[GEN ** k]
    return eq, rebuilt
```
-/
def blockSelector_3 (n : Nat) : GFn where
  name := instName "block_selector" [.L n]
  arity := 3
  rets := 2
  body ps := do
    let selBits := cellOf ps 0
    let zeta1Hi := cellOf ps 1
    let idxcHi := cellOf ps 2
    let eq : GPow := ⟨0⟩
    let rebuilt : GPow := ⟨0⟩
    let mut eq_word : Word := default
    let mut rebuilt_word : Word := default
    for k_k in [0:n] do
      let sbit ← B.load selBits k_k
      B.store selBits k_k (← B.mul sbit sbit)
      if k_k = 0 then
        eq_word ← B.add sbit (← B.load zeta1Hi k_k)
        rebuilt_word ← B.add (← B.const 1) (← B.mul sbit (← B.load idxcHi k_k))
      else
        eq_word ← B.mul eq_word (← B.add sbit (← B.load zeta1Hi k_k))
        rebuilt_word ← B.mul rebuilt_word (← B.add (← B.const 1) (← B.mul sbit (← B.load idxcHi k_k)))
    return [.v eq_word.v] ++ [.v rebuilt_word.v]

set_option linter.unusedVariables false in
/-- `index_mle`, a `Const` family (`guests/lean_ethereum.py`, line 2076):

```
def index_mle(zeta, n: Const):
    # The Index coordinate's MLE over the block's n = κ low coords:
    # prod_t (1 + zeta_t * (1 + g^(2^t))).
    v = GEN ** 0
    for t in unroll(0, n):
        if t == 0:
            v = 1 + zeta[GEN ** t] * INDEX_MLE_FACTORS[t]
        else:
            v *= 1 + zeta[GEN ** t] * INDEX_MLE_FACTORS[t]
    return v
```
-/
def indexMle (n : Nat) : GFn where
  name := instName "index_mle" [.L n]
  arity := 1
  rets := 1
  body ps := do
    let zeta := cellOf ps 0
    let v : GPow := ⟨0⟩
    return [.c (gpowE v.exp)]

set_option linter.unusedVariables false in
/-- `index_mle`, a `Const` family (`guests/lean_ethereum.py`, line 2076):

```
def index_mle(zeta, n: Const):
    # The Index coordinate's MLE over the block's n = κ low coords:
    # prod_t (1 + zeta_t * (1 + g^(2^t))).
    v = GEN ** 0
    for t in unroll(0, n):
        if t == 0:
            v = 1 + zeta[GEN ** t] * INDEX_MLE_FACTORS[t]
        else:
            v *= 1 + zeta[GEN ** t] * INDEX_MLE_FACTORS[t]
    return v
```
-/
def indexMle_2 (n : Nat) : GFn where
  name := instName "index_mle" [.L n]
  arity := 1
  rets := 1
  body ps := do
    let zeta := cellOf ps 0
    let v : GPow := ⟨0⟩
    let mut v_word : Word := default
    let t_k := 0
    if t_k = 0 then
      v_word ← B.add (← B.const 1) (← B.mul (← B.load zeta t_k) (← B.const (arrWord INDEX_MLE_FACTORS t_k)))
    else
      pure () -- no use of this definition takes this branch
    return [.v v_word.v]

set_option linter.unusedVariables false in
/-- `index_mle`, a `Const` family (`guests/lean_ethereum.py`, line 2076):

```
def index_mle(zeta, n: Const):
    # The Index coordinate's MLE over the block's n = κ low coords:
    # prod_t (1 + zeta_t * (1 + g^(2^t))).
    v = GEN ** 0
    for t in unroll(0, n):
        if t == 0:
            v = 1 + zeta[GEN ** t] * INDEX_MLE_FACTORS[t]
        else:
            v *= 1 + zeta[GEN ** t] * INDEX_MLE_FACTORS[t]
    return v
```
-/
def indexMle_3 (n : Nat) : GFn where
  name := instName "index_mle" [.L n]
  arity := 1
  rets := 1
  body ps := do
    let zeta := cellOf ps 0
    let v : GPow := ⟨0⟩
    let mut v_word : Word := default
    for t_k in [0:n] do
      if t_k = 0 then
        v_word ← B.add (← B.const 1) (← B.mul (← B.load zeta t_k) (← B.const (arrWord INDEX_MLE_FACTORS t_k)))
      else
        v_word ← B.mul v_word (← B.add (← B.const 1) (← B.mul (← B.load zeta t_k) (← B.const (arrWord INDEX_MLE_FACTORS t_k))))
    return [.v v_word.v]

set_option linter.unusedVariables false in
/-- `block_selector_tab`, a `Const` family (`guests/lean_ethereum.py`, line 2180):

```
def block_selector_tab(digits, eq_tab, g_tab, n: Const):
    # block_selector off the shared tables: per nibble, a hinted g-power digit g^u,
    # range-checked below the nibble's table size, reads its eq factor and its share
    # of g^offset. The caller pins the shares' product to the certified offset, which
    # makes every digit the offset's own (a base-16 representation is unique).
    eq = GEN ** 0
    rebuilt = GEN ** 0
    for j in unroll(0, (n + 3) // 4):
        width = 4
        if const(j == n // 4):
            width = n - 4 * j
        d = digits[GEN ** j]
        assert_digit(d, width)
        if const(j == 0):
            eq = eq_tab[GEN ** (SEL_TAB_EQ_STRIDE * j + 2 ** width - 2) * d]
            rebuilt = g_tab[GEN ** (16 * j) * d]
        else:
            eq *= eq_tab[GEN ** (SEL_TAB_EQ_STRIDE * j + 2 ** width - 2) * d]
            rebuilt *= g_tab[GEN ** (16 * j) * d]
    return eq, rebuilt
```
-/
def blockSelectorTab (n : Nat) : GFn where
  name := instName "block_selector_tab" [.L n]
  arity := 3
  rets := 2
  body ps := do
    let digits := cellOf ps 0
    let eqTab := cellOf ps 1
    let gTab := cellOf ps 2
    let eq : GPow := ⟨0⟩
    let rebuilt : GPow := ⟨0⟩
    return [.c (gpowE eq.exp)] ++ [.c (gpowE rebuilt.exp)]

set_option linter.unusedVariables false in
/-- `block_selector_tab`, a `Const` family (`guests/lean_ethereum.py`, line 2180):

```
def block_selector_tab(digits, eq_tab, g_tab, n: Const):
    # block_selector off the shared tables: per nibble, a hinted g-power digit g^u,
    # range-checked below the nibble's table size, reads its eq factor and its share
    # of g^offset. The caller pins the shares' product to the certified offset, which
    # makes every digit the offset's own (a base-16 representation is unique).
    eq = GEN ** 0
    rebuilt = GEN ** 0
    for j in unroll(0, (n + 3) // 4):
        width = 4
        if const(j == n // 4):
            width = n - 4 * j
        d = digits[GEN ** j]
        assert_digit(d, width)
        if const(j == 0):
            eq = eq_tab[GEN ** (SEL_TAB_EQ_STRIDE * j + 2 ** width - 2) * d]
            rebuilt = g_tab[GEN ** (16 * j) * d]
        else:
            eq *= eq_tab[GEN ** (SEL_TAB_EQ_STRIDE * j + 2 ** width - 2) * d]
            rebuilt *= g_tab[GEN ** (16 * j) * d]
    return eq, rebuilt
```
-/
def blockSelectorTab_2 (n : Nat) : GFn where
  name := instName "block_selector_tab" [.L n]
  arity := 3
  rets := 2
  body ps := do
    let digits := cellOf ps 0
    let eqTab := cellOf ps 1
    let gTab := cellOf ps 2
    let eq : GPow := ⟨0⟩
    let rebuilt : GPow := ⟨0⟩
    let mut eq_word : Word := default
    let mut rebuilt_word : Word := default
    let j_k := 0
    let mut width := 4
    if j_k = (n / 4) then
      width := n - (4 * j_k)
    else
      pure ()
    let d ← B.load digits j_k
    assertDigit d width
    if j_k = 0 then
      eq_word ← B.load (← B.mul eqTab d) (((SEL_TAB_EQ_STRIDE * j_k) + (2 ^ width)) - 2)
      rebuilt_word ← B.load (← B.mul gTab d) (16 * j_k)
    else
      pure () -- no use of this definition takes this branch
    return [.v eq_word.v] ++ [.v rebuilt_word.v]

set_option linter.unusedVariables false in
/-- `block_selector_tab`, a `Const` family (`guests/lean_ethereum.py`, line 2180):

```
def block_selector_tab(digits, eq_tab, g_tab, n: Const):
    # block_selector off the shared tables: per nibble, a hinted g-power digit g^u,
    # range-checked below the nibble's table size, reads its eq factor and its share
    # of g^offset. The caller pins the shares' product to the certified offset, which
    # makes every digit the offset's own (a base-16 representation is unique).
    eq = GEN ** 0
    rebuilt = GEN ** 0
    for j in unroll(0, (n + 3) // 4):
        width = 4
        if const(j == n // 4):
            width = n - 4 * j
        d = digits[GEN ** j]
        assert_digit(d, width)
        if const(j == 0):
            eq = eq_tab[GEN ** (SEL_TAB_EQ_STRIDE * j + 2 ** width - 2) * d]
            rebuilt = g_tab[GEN ** (16 * j) * d]
        else:
            eq *= eq_tab[GEN ** (SEL_TAB_EQ_STRIDE * j + 2 ** width - 2) * d]
            rebuilt *= g_tab[GEN ** (16 * j) * d]
    return eq, rebuilt
```
-/
def blockSelectorTab_3 (n : Nat) : GFn where
  name := instName "block_selector_tab" [.L n]
  arity := 3
  rets := 2
  body ps := do
    let digits := cellOf ps 0
    let eqTab := cellOf ps 1
    let gTab := cellOf ps 2
    let eq : GPow := ⟨0⟩
    let rebuilt : GPow := ⟨0⟩
    let mut eq_word : Word := default
    let mut rebuilt_word : Word := default
    for j_k in [0:(n + 3) / 4] do
      let mut width := 4
      if j_k = (n / 4) then
        width := n - (4 * j_k)
      else
        pure ()
      let d ← B.load digits j_k
      assertDigit d width
      if j_k = 0 then
        eq_word ← B.load (← B.mul eqTab d) (((SEL_TAB_EQ_STRIDE * j_k) + (2 ^ width)) - 2)
        rebuilt_word ← B.load (← B.mul gTab d) (16 * j_k)
      else
        eq_word ← B.mul eq_word (← B.load (← B.mul eqTab d) (((SEL_TAB_EQ_STRIDE * j_k) + (2 ^ width)) - 2))
        rebuilt_word ← B.mul rebuilt_word (← B.load (← B.mul gTab d) (16 * j_k))
    return [.v eq_word.v] ++ [.v rebuilt_word.v]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `keccak_layer`, a `Const` family (`guests/lean_ethereum.py`, line 2894):

```
def keccak_layer(fs0, fs1, fs2, fs3, fs4, p0, p1, cursor, y_g, step_g, rem_g, claim, out, iota, tabs, first: Const):
    # One layer (verifier::keccak::verify_layer): the claim on the states after
    # a round becomes one on the states before it. A claim's position weights are
    # never written out: they are the transpose of the linear layer applied to a
    # lane table times the eq table of six slice coordinates, which is all the
    # record keeps, and what `keccak_form` evaluates them from.
    # The first layer starts with the committed outputs' value waiting in the sponge, its
    # two rate cells p0 and p1.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    if first == 1:
        rate[0] = p0
        rate[1] = p1
    # Each product coefficient's reader, a straight line of sums over the instance weights.
    readers = StackBuf(KECCAK_PROJ_CELLS)
    for i in unroll(0, KECCAK_PACK):
        readers[i] = claim[GEN ** (KC_MU + i)]
    for t in unroll(0, len(KECCAK_PROJ_A)):
        readers[KECCAK_PACK + t] = readers[KECCAK_PROJ_A[t]] + readers[KECCAK_PROJ_B[t]]
    # The product polynomial carries the claim.
    product = StackBuf(KECCAK_PROD_BITS)
    projected = 0
    for pos in unroll(first, first + KECCAK_PROD_BITS):
        # fs_next, the word read straight into its cell, k = pos - first.
        product[pos - first] = cursor[GEN ** (pos - first)]
        coefficient = product[pos - first]
        if pos % 4 == 0:
            if pos != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        fs_pack(rate, pos % 4, coefficient, DS_OBSERVE)
        projected += readers[KECCAK_PROJ_OUT[pos - first]] * coefficient
    cursor = cursor * GEN ** KECCAK_PROD_BITS
    assert projected + iota * claim[GEN ** KC_KAPPA] == claim[GEN ** KC_VALUE]
    # At a random point a pack is one field element, after a grind: the polynomial has
    # degree KECCAK_PROD_BITS - 1.
    sp, s, cursor = fs_grind_squeeze(sp, rate, (first + KECCAK_PROD_BITS + 3) % 4 + 1, cursor, tabs, KECCAK_S_GRIND_BITS)
    # mu[i] = emb_i(s), each embedding a product of small irreducible factors.
    s_powers = StackBuf(KECCAK_FAC_DEG)
    s_powers[0] = 1
    s_powers[1] = s
    for b in unroll(2, KECCAK_FAC_DEG):
        s_powers[b] = s_powers[b - 1] * s
    factors = StackBuf(KECCAK_EMB_CELLS)
    for f in unroll(0, KECCAK_FAC_N):
        acc = 0
        for t in unroll(KECCAK_FAC_START[f], KECCAK_FAC_START[f + 1]):
            acc += s_powers[KECCAK_FAC_IDX[t]]
        factors[f] = acc
    for t in unroll(0, len(KECCAK_EMB_A)):
        factors[KECCAK_FAC_N + t] = factors[KECCAK_EMB_A[t]] * factors[KECCAK_EMB_B[t]]
    kappa = 0  # the sum of the weights
    for i in unroll(0, KECCAK_PACK):
        out[GEN ** (KC_MU + i)] = factors[KECCAK_EMB_OUT[i]]
        kappa += factors[KECCAK_EMB_OUT[i]]
    out[GEN ** KC_KAPPA] = kappa
    value = product[KECCAK_PROD_BITS - 1]
    for k in unroll(1, KECCAK_PROD_BITS):
        value = value * s + product[KECCAK_PROD_BITS - 1 - k]
    # The pack and the segment, a runtime number of rounds: KR_STEP step_g, KR_STEP a
    # loop step, then rem_g, one a loop step (a loop rather than an unrolled arm per remainder,
    # whose shared frame would grow every layer's).
    prev_point = claim[GEN ** KC_POINT]
    point = HeapBuf(y_g)
    rounds = HeapBuf(KR_SLOTS * KR_CAP)
    fs_store(rounds, KR_FS, KR_CAP, sp)
    rounds[GEN ** (KR_CURSOR * KR_CAP)] = cursor
    rounds[GEN ** (KR_CLAIM * KR_CAP)] = value
    for xs in mul_range(1, step_g):
        rd = rounds * xs
        pp = prev_point * xs ** KR_STEP
        pt = point * xs ** KR_STEP
        round_sp = fs_load(rd, KR_FS, KR_CAP)
        cur_i = rd[GEN ** (KR_CURSOR * KR_CAP)]
        run = rd[GEN ** (KR_CLAIM * KR_CAP)]
        for q in unroll(0, KR_STEP):
            # q has degree two with the eq factor pulled out, and the prover sends its
            # coefficients c1 and c2 (g_1, g_2), c0 being fixed by the claim. With r the
            # round's coordinate and c its challenge, q(c) = claim + (r + c) c1 +
            # (r + c^2) c2, which is the next normalized claim. The round grinds for
            # degree three, the eq factor included.
            r_eq = pp[GEN ** q]
            rate = StackBuf(8)
            g_1, cur_i = fs_next(rate, 0, cur_i)
            g_2, cur_i = fs_next(rate, 1, cur_i)
            round_sp, challenge, cur_i = fs_grind_squeeze(round_sp, rate, 2, cur_i, tabs, ROUND3_GRIND_BITS)
            pt[GEN ** q] = challenge
            gap = r_eq + challenge
            run = run + gap * g_1 + (r_eq + challenge * challenge) * g_2
        nxt = rd * GEN
        fs_store(nxt, KR_FS, KR_CAP, round_sp)
        nxt[GEN ** (KR_CURSOR * KR_CAP)] = cur_i
        nxt[GEN ** (KR_CLAIM * KR_CAP)] = run
    rem_rounds = rounds * step_g
    rem_prev = prev_point * step_g ** KR_STEP
    rem_point = point * step_g ** KR_STEP
    for x1 in mul_range(1, rem_g):
        rd = rem_rounds * x1
        r_eq = rem_prev[x1]
        round_sp = fs_load(rd, KR_FS, KR_CAP)
        cur_i = rd[GEN ** (KR_CURSOR * KR_CAP)]
        rate = StackBuf(8)
        g_1, cur_i = fs_next(rate, 0, cur_i)
        g_2, cur_i = fs_next(rate, 1, cur_i)
        round_sp, challenge, cur_i = fs_grind_squeeze(round_sp, rate, 2, cur_i, tabs, ROUND3_GRIND_BITS)
        rem_point[x1] = challenge
        gap = r_eq + challenge
        nxt = rd * GEN
        fs_store(nxt, KR_FS, KR_CAP, round_sp)
        nxt[GEN ** (KR_CURSOR * KR_CAP)] = cur_i
        nxt[GEN ** (KR_CLAIM * KR_CAP)] = rd[GEN ** (KR_CLAIM * KR_CAP)] + gap * g_1 + (r_eq + challenge * challenge) * g_2
    last = rem_rounds * rem_g
    sp = fs_load(last, KR_FS, KR_CAP)
    cursor = last[GEN ** (KR_CURSOR * KR_CAP)]
    value = last[GEN ** (KR_CLAIM * KR_CAP)]
    # The bit position: degree three, the weights being one more multilinear factor.
    local = HeapBuf(KECCAK_LOCAL_BITS)
    for i in unroll(0, KECCAK_LOCAL_BITS):
        rate = StackBuf(8)
        c0, cursor = fs_next(rate, 0, cursor)
        c2, cursor = fs_next(rate, 1, cursor)
        c3, cursor = fs_next(rate, 2, cursor)
        sp, challenge, cursor = fs_grind_squeeze(sp, rate, 3, cursor, tabs, ROUND3_GRIND_BITS)
        local[GEN ** i] = challenge
        # c1 = value + c2 + c3, so h(c) = c0 + c (value + (1 + c) (c2 + (1 + c) c3)).
        challenge1 = 1 + challenge
        value = c0 + challenge * (value + challenge1 * (c2 + challenge1 * c3))
    rate = StackBuf(8)
    t0, cursor = fs_next(rate, 0, cursor)
    t1, cursor = fs_next(rate, 1, cursor)
    t2, cursor = fs_next(rate, 2, cursor)
    # The claim's weights at the local point.
    f_lanes = StackBuf(2 ** (KECCAK_LANE_BITS + 1) - 2)
    eqtree_frame(local * GEN ** KECCAK_Z_BITS, f_lanes, KECCAK_LANE_BITS, KECCAK_LANES)
    prev_lanes = claim[GEN ** KC_LANES]
    weight_at_local = StackBuf(1)
    if first == 1:
        # The first claim weighs a lane table times the bits of a word, x^z.
        lanes_eq = 0
        for lane in unroll(0, KECCAK_LANES):
            lanes_eq += f_lanes[LANE_OFF + lane] * prev_lanes[GEN ** lane]
        for t in unroll(0, KECCAK_Z_BITS):
            lanes_eq *= 1 + local[GEN ** t] * (1 + GEN ** (2 ** t))
        weight_at_local[0] = lanes_eq
    else:
        shifts = StackBuf(64)
        keccak_shifts_eq(claim[GEN ** KC_LOCAL], local, shifts)
        weight_at_local[0] = keccak_form(prev_lanes, shifts, f_lanes, LANE_OFF)
    assert weight_at_local[0] * (kappa * t0 + (kappa + t1) * t2) == value
    # t[k] = sum_j eq[j] T[j + k]: one claim on the state before chi, quadratic in beta.
    sp, beta, cursor = fs_grind_squeeze(sp, rate, 3, cursor, tabs, KECCAK_BETA_GRIND_BITS)
    out[GEN ** KC_VALUE] = t0 + beta * (t1 + beta * t2)
    out[GEN ** KC_POINT] = point
    out[GEN ** KC_LOCAL] = local
    lanes = HeapBuf(KECCAK_LANES)
    for y in unroll(0, 5):
        for x in unroll(0, 5):
            lanes[GEN ** (x + 5 * y)] = f_lanes[LANE_OFF + x + 5 * y] + beta * (f_lanes[LANE_OFF + (x + 4) % 5 + 5 * y] + beta * f_lanes[LANE_OFF + (x + 3) % 5 + 5 * y])
    out[GEN ** KC_LANES] = lanes
    # The next layer's iota term: for every i, the new claim's weight on slice 2^i - 1
    # of lane 0, through the linear layer's transpose, from its lane and slice weights.
    # The slice weights are an eq tree on the low five coordinates, times the top
    # one's factor where a weight is read.
    slices = StackBuf(2 ** KECCAK_Z_BITS - 2)
    eqtree_frame(local, slices, KECCAK_Z_BITS - 1, 2 ** (KECCAK_Z_BITS - 1))
    top = local[GEN ** (KECCAK_Z_BITS - 1)]
    top1 = 1 + top
    flips = HeapBuf(KECCAK_IOTA_BITS)
    for i in unroll(0, KECCAK_IOTA_BITS):
        flipped = lanes[GEN ** KECCAK_PI[0]] * slice_weight(slices, top, top1, (2 ** i - 1 + KECCAK_RHO[0]) % 64)
        for y in unroll(0, 5):
            flipped += lanes[GEN ** KECCAK_PI[1 + 5 * y]] * slice_weight(slices, top, top1, (2 ** i - 1 + KECCAK_RHO[1 + 5 * y]) % 64)
            flipped += lanes[GEN ** KECCAK_PI[4 + 5 * y]] * slice_weight(slices, top, top1, (2 ** i + KECCAK_RHO[4 + 5 * y]) % 64)
        flips[GEN ** i] = flipped
    out[GEN ** KC_FLIPS] = flips
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor
```
-/
def keccakLayer (first : Nat) : GFn where
  name := instName "keccak_layer" [.L first]
  arity := 15
  rets := 6
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let p0 := cellOf ps 5
    let p1 := cellOf ps 6
    let cursor := cellOf ps 7
    let yG := cellOf ps 8
    let stepG := cellOf ps 9
    let remG := cellOf ps 10
    let claim := cellOf ps 11
    let out := cellOf ps 12
    let iota := cellOf ps 13
    let tabs := cellOf ps 14
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut rate ← B.stackBuf 8
    if first = 1 then
      B.copy (cellOf rate 0) p0
      B.copy (cellOf rate 1) p1
    else
      pure () -- no use of this definition takes this branch
    let readers ← B.stackBuf KECCAK_PROJ_CELLS
    for i_k in [0:KECCAK_PACK] do
      B.loadInto (cellOf readers i_k) claim (KC_MU + i_k)
    for t_k in [0:KECCAK_PROJ_A.length] do
      B.addInto (cellOf readers (KECCAK_PACK + t_k)) (cellOf readers (arrInt KECCAK_PROJ_A t_k)) (cellOf readers (arrInt KECCAK_PROJ_B t_k))
    let product ← B.stackBuf KECCAK_PROD_BITS
    let projected := 0
    let mut projected_word : Word := default
    let pos_k := 1
    B.loadInto (cellOf product (pos_k - first)) cursor (pos_k - first)
    let coefficient := cellOf product (pos_k - first)
    if (pos_k % 4) = 0 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    fsPack rate (pos_k % 4) coefficient DS_OBSERVE
    projected_word ← B.mul (cellOf readers (arrInt KECCAK_PROJ_OUT (pos_k - first))) coefficient
    for pos_k in [2:first + KECCAK_PROD_BITS] do
      B.loadInto (cellOf product (pos_k - first)) cursor (pos_k - first)
      let coefficient := cellOf product (pos_k - first)
      if (pos_k % 4) = 0 then
        if pos_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      fsPack rate (pos_k % 4) coefficient DS_OBSERVE
      projected_word ← B.add projected_word (← B.mul (cellOf readers (arrInt KECCAK_PROJ_OUT (pos_k - first))) coefficient)
    let cursor_ptr : Shifted := ⟨cursor, KECCAK_PROD_BITS⟩
    B.assertEq (← B.add projected_word (← B.mul iota (← B.load claim KC_KAPPA))) (← B.load claim KC_VALUE)
    let (t0, t1, t2) ← fsGrindSqueeze sp rate ((((first + KECCAK_PROD_BITS) + 3) % 4) + 1) (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs 3
    sp := t0
    let s := t1
    let mut cursor_ptr : Shifted := t2
    let sPowers ← B.stackBuf KECCAK_FAC_DEG
    B.constInto (cellOf sPowers 0) 1
    B.copy (cellOf sPowers 1) s
    for b_k in [2:KECCAK_FAC_DEG] do
      B.mulInto (cellOf sPowers b_k) (cellOf sPowers (b_k - 1)) s
    let factors ← B.stackBuf KECCAK_EMB_CELLS
    let f_k := 0
    let acc := 0
    let mut acc_word : Word := default
    let t_k := 0
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    B.copy (cellOf factors f_k) acc_word
    let f_k := 1
    let acc := 0
    let t_k := 1
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    let t_k := 2
    acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 2
    let acc := 0
    let t_k := 3
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [4:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 3
    let acc := 0
    let t_k := 6
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [7:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 4
    let acc := 0
    let t_k := 9
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [10:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 5
    let acc := 0
    let t_k := 12
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [13:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 6
    let acc := 0
    let t_k := 15
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [16:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 7
    let acc := 0
    let t_k := 18
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [19:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    for t_k in [0:KECCAK_EMB_A.length] do
      B.mulInto (cellOf factors (KECCAK_FAC_N + t_k)) (cellOf factors (arrInt KECCAK_EMB_A t_k)) (cellOf factors (arrInt KECCAK_EMB_B t_k))
    let kappa := 0
    let mut kappa_word : Word := default
    let i_k := 0
    B.store out (KC_MU + i_k) (cellOf factors (arrInt KECCAK_EMB_OUT i_k))
    kappa_word := cellOf factors (arrInt KECCAK_EMB_OUT i_k)
    for i_k in [1:KECCAK_PACK] do
      B.store out (KC_MU + i_k) (cellOf factors (arrInt KECCAK_EMB_OUT i_k))
      kappa_word ← B.add kappa_word (cellOf factors (arrInt KECCAK_EMB_OUT i_k))
    B.store out KC_KAPPA kappa_word
    let mut value := cellOf product (KECCAK_PROD_BITS - 1)
    for k_k in [1:KECCAK_PROD_BITS] do
      value ← B.add (← B.mul value s) (cellOf product ((KECCAK_PROD_BITS - 1) - k_k))
    let prevPoint ← B.load claim KC_POINT
    let point ← B.heapBufDyn yG
    let rounds ← B.heapBuf 77
    fsStore_2 rounds KR_FS KR_CAP sp
    B.store rounds 55 (← B.shifted cursor_ptr.base cursor_ptr.exp)
    B.store rounds 66 value
    B.loopRtF 0 (pure stepG) 4 (pure ([rounds.v, prevPoint.v, point.v, tabs.v])) fun xs caps => do
      let rounds := cellOf caps 0
      let prevPoint := cellOf caps 1
      let point := cellOf caps 2
      let tabs := cellOf caps 3
      let rd ← B.mul rounds xs
      let pp ← B.mul prevPoint (← B.pow xs KR_STEP)
      let pt ← B.mul point (← B.pow xs KR_STEP)
      let mut roundSp ← fsLoad rd KR_FS KR_CAP
      let curI ← B.load rd 55
      let mut run ← B.load rd 66
      let mut curI_ptr : Shifted := default
      let q_k := 0
      let rEq ← B.load pp q_k
      let rate ← B.stackBuf 8
      let (t0, t1) ← fsNext rate 0 curI
      let g1 := t0
      curI_ptr := t1
      let (t2, t3) ← fsNext_2 rate 1 (⟨curI_ptr.base, curI_ptr.exp⟩)
      let g2 := t2
      curI_ptr := t3
      let (t4, t5, t6) ← fsGrindSqueeze roundSp rate 2 (⟨curI_ptr.base, curI_ptr.exp⟩) tabs ROUND3_GRIND_BITS
      roundSp := t4
      let challenge := t5
      curI_ptr := t6
      B.store pt q_k challenge
      let gap ← B.add rEq challenge
      run ← B.add (← B.add run (← B.mul gap g1)) (← B.mul (← B.add rEq (← B.mul challenge challenge)) g2)
      for q_k in [1:KR_STEP] do
        let rEq ← B.load pp q_k
        let rate ← B.stackBuf 8
        let (t0, t1) ← fsNext_2 rate 0 (⟨curI_ptr.base, curI_ptr.exp⟩)
        let g1 := t0
        curI_ptr := t1
        let (t2, t3) ← fsNext_2 rate 1 (⟨curI_ptr.base, curI_ptr.exp⟩)
        let g2 := t2
        curI_ptr := t3
        let (t4, t5, t6) ← fsGrindSqueeze roundSp rate 2 (⟨curI_ptr.base, curI_ptr.exp⟩) tabs ROUND3_GRIND_BITS
        roundSp := t4
        let challenge := t5
        curI_ptr := t6
        B.store pt q_k challenge
        let gap ← B.add rEq challenge
        run ← B.add (← B.add run (← B.mul gap g1)) (← B.mul (← B.add rEq (← B.mul challenge challenge)) g2)
      let nxt : Shifted := ⟨rd, 1⟩
      fsStore (⟨nxt.base, nxt.exp⟩) KR_FS KR_CAP roundSp
      B.store nxt.base (nxt.exp + 55) (← B.shifted curI_ptr.base curI_ptr.exp)
      B.store nxt.base (nxt.exp + 66) run
    let remRounds ← B.mul rounds stepG
    let remPrev ← B.mul prevPoint (← B.pow stepG KR_STEP)
    let remPoint ← B.mul point (← B.pow stepG KR_STEP)
    B.loopRtF 0 (pure remG) 4 (pure ([remRounds.v, remPrev.v, tabs.v, remPoint.v])) fun x1 caps => do
      let remRounds := cellOf caps 0
      let remPrev := cellOf caps 1
      let tabs := cellOf caps 2
      let remPoint := cellOf caps 3
      let rd ← B.mul remRounds x1
      let rEq ← B.load (← B.mul remPrev x1) 0
      let roundSp ← fsLoad rd KR_FS KR_CAP
      let curI ← B.load rd 55
      let rate ← B.stackBuf 8
      let (t0, t1) ← fsNext rate 0 curI
      let g1 := t0
      let curI_ptr : Shifted := t1
      let (t2, t3) ← fsNext_2 rate 1 (⟨curI_ptr.base, curI_ptr.exp⟩)
      let g2 := t2
      let curI_ptr : Shifted := t3
      let (t4, t5, t6) ← fsGrindSqueeze roundSp rate 2 (⟨curI_ptr.base, curI_ptr.exp⟩) tabs ROUND3_GRIND_BITS
      let roundSp := t4
      let challenge := t5
      let curI_ptr : Shifted := t6
      B.store (← B.mul remPoint x1) 0 challenge
      let gap ← B.add rEq challenge
      let nxt : Shifted := ⟨rd, 1⟩
      fsStore (⟨nxt.base, nxt.exp⟩) KR_FS KR_CAP roundSp
      B.store nxt.base (nxt.exp + 55) (← B.shifted curI_ptr.base curI_ptr.exp)
      B.store nxt.base (nxt.exp + 66) (← B.add (← B.add (← B.load rd 66) (← B.mul gap g1)) (← B.mul (← B.add rEq (← B.mul challenge challenge)) g2))
    let last ← B.mul remRounds remG
    sp ← fsLoad last KR_FS KR_CAP
    let cursor ← B.load last 55
    value ← B.load last 66
    let local' ← B.heapBuf KECCAK_LOCAL_BITS
    let i_k := 0
    rate ← B.stackBuf 8
    let (t3, t4) ← fsNext rate 0 cursor
    let c0 := t3
    cursor_ptr := t4
    let (t5, t6) ← fsNext_2 rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let c2 := t5
    cursor_ptr := t6
    let (t7, t8) ← fsNext_2 rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let c3 := t7
    cursor_ptr := t8
    let (t9, t10, t11) ← fsGrindSqueeze sp rate 3 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs ROUND3_GRIND_BITS
    sp := t9
    let challenge := t10
    cursor_ptr := t11
    B.store local' i_k challenge
    let challenge1 ← B.add (← B.const 1) challenge
    value ← B.add c0 (← B.mul challenge (← B.add value (← B.mul challenge1 (← B.add c2 (← B.mul challenge1 c3)))))
    for i_k in [1:KECCAK_LOCAL_BITS] do
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext_2 rate 0 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      let c0 := t3
      cursor_ptr := t4
      let (t5, t6) ← fsNext_2 rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      let c2 := t5
      cursor_ptr := t6
      let (t7, t8) ← fsNext_2 rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      let c3 := t7
      cursor_ptr := t8
      let (t9, t10, t11) ← fsGrindSqueeze sp rate 3 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs ROUND3_GRIND_BITS
      sp := t9
      let challenge := t10
      cursor_ptr := t11
      B.store local' i_k challenge
      let challenge1 ← B.add (← B.const 1) challenge
      value ← B.add c0 (← B.mul challenge (← B.add value (← B.mul challenge1 (← B.add c2 (← B.mul challenge1 c3)))))
    rate ← B.stackBuf 8
    let (t12, t13) ← fsNext_2 rate 0 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let t0 := t12
    cursor_ptr := t13
    let (t14, t15) ← fsNext_2 rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let t1 := t14
    cursor_ptr := t15
    let (t16, t17) ← fsNext_2 rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let t2 := t16
    cursor_ptr := t17
    let fLanes ← B.stackBuf 62
    eqtreeFrame_3 (⟨local', KECCAK_Z_BITS⟩) fLanes KECCAK_LANE_BITS KECCAK_LANES
    let prevLanes ← B.load claim KC_LANES
    let weightAtLocal ← B.stackBuf 1
    if first = 1 then
      let lanesEq := 0
      let mut lanesEq_word : Word := default
      let lane_k := 0
      lanesEq_word ← B.mul (cellOf fLanes (LANE_OFF + lane_k)) (← B.load prevLanes lane_k)
      for lane_k in [1:KECCAK_LANES] do
        lanesEq_word ← B.add lanesEq_word (← B.mul (cellOf fLanes (LANE_OFF + lane_k)) (← B.load prevLanes lane_k))
      for t_k in [0:KECCAK_Z_BITS] do
        lanesEq_word ← B.mul lanesEq_word (← B.add (← B.const 1) (← B.mul (← B.load local' t_k) (← B.const (1 + (gpowE (2 ^ t_k))))))
      B.copy (cellOf weightAtLocal 0) lanesEq_word
    else
      pure () -- no use of this definition takes this branch
    B.assertEq (← B.mul (cellOf weightAtLocal 0) (← B.add (← B.mul kappa_word t0) (← B.mul (← B.add kappa_word t1) t2))) value
    let (t18, t19, t20) ← fsGrindSqueeze sp rate 3 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs KECCAK_BETA_GRIND_BITS
    sp := t18
    let beta := t19
    cursor_ptr := t20
    B.store out KC_VALUE (← B.add t0 (← B.mul beta (← B.add t1 (← B.mul beta t2))))
    B.store out KC_POINT point
    B.store out KC_LOCAL local'
    let lanes ← B.heapBuf KECCAK_LANES
    for y_k in [0:5] do
      for x_k in [0:5] do
        B.store lanes (x_k + (5 * y_k)) (← B.add (cellOf fLanes ((LANE_OFF + x_k) + (5 * y_k))) (← B.mul beta (← B.add (cellOf fLanes ((LANE_OFF + ((x_k + 4) % 5)) + (5 * y_k))) (← B.mul beta (cellOf fLanes ((LANE_OFF + ((x_k + 3) % 5)) + (5 * y_k)))))))
    B.store out KC_LANES lanes
    let slices ← B.stackBuf 62
    eqtreeFrame_2 local' slices (KECCAK_Z_BITS - 1) (2 ^ (KECCAK_Z_BITS - 1))
    let top ← B.load local' 5
    let top1 ← B.add (← B.const 1) top
    let flips ← B.heapBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      let t22 ← B.load lanes (arrInt KECCAK_PI 0)
      let t21 ← sliceWeight slices top top1 ((((2 ^ i_k) - 1) + (arrInt KECCAK_RHO 0)) % 64)
      let mut flipped ← B.mul t22 t21
      for y_k in [0:5] do
        let t24 ← B.load lanes (arrInt KECCAK_PI (1 + (5 * y_k)))
        let t23 ← sliceWeight slices top top1 ((((2 ^ i_k) - 1) + (arrInt KECCAK_RHO (1 + (5 * y_k)))) % 64)
        flipped ← B.add flipped (← B.mul t24 t23)
        let t26 ← B.load lanes (arrInt KECCAK_PI (4 + (5 * y_k)))
        let t25 ← sliceWeight slices top top1 (((2 ^ i_k) + (arrInt KECCAK_RHO (4 + (5 * y_k)))) % 64)
        flipped ← B.add flipped (← B.mul t26 t25)
      B.store flips i_k flipped
    B.store out KC_FLIPS flips
    let t27 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted cursor_ptr.base cursor_ptr.exp)
    return [.v (cellOf sp 8).v] ++ [.v (cellOf sp 9).v] ++ [.v (cellOf sp 10).v] ++ [.v (cellOf sp 11).v] ++ [.v (cellOf sp 12).v] ++ [.into t27]

set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- `keccak_layer`, a `Const` family (`guests/lean_ethereum.py`, line 2894):

```
def keccak_layer(fs0, fs1, fs2, fs3, fs4, p0, p1, cursor, y_g, step_g, rem_g, claim, out, iota, tabs, first: Const):
    # One layer (verifier::keccak::verify_layer): the claim on the states after
    # a round becomes one on the states before it. A claim's position weights are
    # never written out: they are the transpose of the linear layer applied to a
    # lane table times the eq table of six slice coordinates, which is all the
    # record keeps, and what `keccak_form` evaluates them from.
    # The first layer starts with the committed outputs' value waiting in the sponge, its
    # two rate cells p0 and p1.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    if first == 1:
        rate[0] = p0
        rate[1] = p1
    # Each product coefficient's reader, a straight line of sums over the instance weights.
    readers = StackBuf(KECCAK_PROJ_CELLS)
    for i in unroll(0, KECCAK_PACK):
        readers[i] = claim[GEN ** (KC_MU + i)]
    for t in unroll(0, len(KECCAK_PROJ_A)):
        readers[KECCAK_PACK + t] = readers[KECCAK_PROJ_A[t]] + readers[KECCAK_PROJ_B[t]]
    # The product polynomial carries the claim.
    product = StackBuf(KECCAK_PROD_BITS)
    projected = 0
    for pos in unroll(first, first + KECCAK_PROD_BITS):
        # fs_next, the word read straight into its cell, k = pos - first.
        product[pos - first] = cursor[GEN ** (pos - first)]
        coefficient = product[pos - first]
        if pos % 4 == 0:
            if pos != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        fs_pack(rate, pos % 4, coefficient, DS_OBSERVE)
        projected += readers[KECCAK_PROJ_OUT[pos - first]] * coefficient
    cursor = cursor * GEN ** KECCAK_PROD_BITS
    assert projected + iota * claim[GEN ** KC_KAPPA] == claim[GEN ** KC_VALUE]
    # At a random point a pack is one field element, after a grind: the polynomial has
    # degree KECCAK_PROD_BITS - 1.
    sp, s, cursor = fs_grind_squeeze(sp, rate, (first + KECCAK_PROD_BITS + 3) % 4 + 1, cursor, tabs, KECCAK_S_GRIND_BITS)
    # mu[i] = emb_i(s), each embedding a product of small irreducible factors.
    s_powers = StackBuf(KECCAK_FAC_DEG)
    s_powers[0] = 1
    s_powers[1] = s
    for b in unroll(2, KECCAK_FAC_DEG):
        s_powers[b] = s_powers[b - 1] * s
    factors = StackBuf(KECCAK_EMB_CELLS)
    for f in unroll(0, KECCAK_FAC_N):
        acc = 0
        for t in unroll(KECCAK_FAC_START[f], KECCAK_FAC_START[f + 1]):
            acc += s_powers[KECCAK_FAC_IDX[t]]
        factors[f] = acc
    for t in unroll(0, len(KECCAK_EMB_A)):
        factors[KECCAK_FAC_N + t] = factors[KECCAK_EMB_A[t]] * factors[KECCAK_EMB_B[t]]
    kappa = 0  # the sum of the weights
    for i in unroll(0, KECCAK_PACK):
        out[GEN ** (KC_MU + i)] = factors[KECCAK_EMB_OUT[i]]
        kappa += factors[KECCAK_EMB_OUT[i]]
    out[GEN ** KC_KAPPA] = kappa
    value = product[KECCAK_PROD_BITS - 1]
    for k in unroll(1, KECCAK_PROD_BITS):
        value = value * s + product[KECCAK_PROD_BITS - 1 - k]
    # The pack and the segment, a runtime number of rounds: KR_STEP step_g, KR_STEP a
    # loop step, then rem_g, one a loop step (a loop rather than an unrolled arm per remainder,
    # whose shared frame would grow every layer's).
    prev_point = claim[GEN ** KC_POINT]
    point = HeapBuf(y_g)
    rounds = HeapBuf(KR_SLOTS * KR_CAP)
    fs_store(rounds, KR_FS, KR_CAP, sp)
    rounds[GEN ** (KR_CURSOR * KR_CAP)] = cursor
    rounds[GEN ** (KR_CLAIM * KR_CAP)] = value
    for xs in mul_range(1, step_g):
        rd = rounds * xs
        pp = prev_point * xs ** KR_STEP
        pt = point * xs ** KR_STEP
        round_sp = fs_load(rd, KR_FS, KR_CAP)
        cur_i = rd[GEN ** (KR_CURSOR * KR_CAP)]
        run = rd[GEN ** (KR_CLAIM * KR_CAP)]
        for q in unroll(0, KR_STEP):
            # q has degree two with the eq factor pulled out, and the prover sends its
            # coefficients c1 and c2 (g_1, g_2), c0 being fixed by the claim. With r the
            # round's coordinate and c its challenge, q(c) = claim + (r + c) c1 +
            # (r + c^2) c2, which is the next normalized claim. The round grinds for
            # degree three, the eq factor included.
            r_eq = pp[GEN ** q]
            rate = StackBuf(8)
            g_1, cur_i = fs_next(rate, 0, cur_i)
            g_2, cur_i = fs_next(rate, 1, cur_i)
            round_sp, challenge, cur_i = fs_grind_squeeze(round_sp, rate, 2, cur_i, tabs, ROUND3_GRIND_BITS)
            pt[GEN ** q] = challenge
            gap = r_eq + challenge
            run = run + gap * g_1 + (r_eq + challenge * challenge) * g_2
        nxt = rd * GEN
        fs_store(nxt, KR_FS, KR_CAP, round_sp)
        nxt[GEN ** (KR_CURSOR * KR_CAP)] = cur_i
        nxt[GEN ** (KR_CLAIM * KR_CAP)] = run
    rem_rounds = rounds * step_g
    rem_prev = prev_point * step_g ** KR_STEP
    rem_point = point * step_g ** KR_STEP
    for x1 in mul_range(1, rem_g):
        rd = rem_rounds * x1
        r_eq = rem_prev[x1]
        round_sp = fs_load(rd, KR_FS, KR_CAP)
        cur_i = rd[GEN ** (KR_CURSOR * KR_CAP)]
        rate = StackBuf(8)
        g_1, cur_i = fs_next(rate, 0, cur_i)
        g_2, cur_i = fs_next(rate, 1, cur_i)
        round_sp, challenge, cur_i = fs_grind_squeeze(round_sp, rate, 2, cur_i, tabs, ROUND3_GRIND_BITS)
        rem_point[x1] = challenge
        gap = r_eq + challenge
        nxt = rd * GEN
        fs_store(nxt, KR_FS, KR_CAP, round_sp)
        nxt[GEN ** (KR_CURSOR * KR_CAP)] = cur_i
        nxt[GEN ** (KR_CLAIM * KR_CAP)] = rd[GEN ** (KR_CLAIM * KR_CAP)] + gap * g_1 + (r_eq + challenge * challenge) * g_2
    last = rem_rounds * rem_g
    sp = fs_load(last, KR_FS, KR_CAP)
    cursor = last[GEN ** (KR_CURSOR * KR_CAP)]
    value = last[GEN ** (KR_CLAIM * KR_CAP)]
    # The bit position: degree three, the weights being one more multilinear factor.
    local = HeapBuf(KECCAK_LOCAL_BITS)
    for i in unroll(0, KECCAK_LOCAL_BITS):
        rate = StackBuf(8)
        c0, cursor = fs_next(rate, 0, cursor)
        c2, cursor = fs_next(rate, 1, cursor)
        c3, cursor = fs_next(rate, 2, cursor)
        sp, challenge, cursor = fs_grind_squeeze(sp, rate, 3, cursor, tabs, ROUND3_GRIND_BITS)
        local[GEN ** i] = challenge
        # c1 = value + c2 + c3, so h(c) = c0 + c (value + (1 + c) (c2 + (1 + c) c3)).
        challenge1 = 1 + challenge
        value = c0 + challenge * (value + challenge1 * (c2 + challenge1 * c3))
    rate = StackBuf(8)
    t0, cursor = fs_next(rate, 0, cursor)
    t1, cursor = fs_next(rate, 1, cursor)
    t2, cursor = fs_next(rate, 2, cursor)
    # The claim's weights at the local point.
    f_lanes = StackBuf(2 ** (KECCAK_LANE_BITS + 1) - 2)
    eqtree_frame(local * GEN ** KECCAK_Z_BITS, f_lanes, KECCAK_LANE_BITS, KECCAK_LANES)
    prev_lanes = claim[GEN ** KC_LANES]
    weight_at_local = StackBuf(1)
    if first == 1:
        # The first claim weighs a lane table times the bits of a word, x^z.
        lanes_eq = 0
        for lane in unroll(0, KECCAK_LANES):
            lanes_eq += f_lanes[LANE_OFF + lane] * prev_lanes[GEN ** lane]
        for t in unroll(0, KECCAK_Z_BITS):
            lanes_eq *= 1 + local[GEN ** t] * (1 + GEN ** (2 ** t))
        weight_at_local[0] = lanes_eq
    else:
        shifts = StackBuf(64)
        keccak_shifts_eq(claim[GEN ** KC_LOCAL], local, shifts)
        weight_at_local[0] = keccak_form(prev_lanes, shifts, f_lanes, LANE_OFF)
    assert weight_at_local[0] * (kappa * t0 + (kappa + t1) * t2) == value
    # t[k] = sum_j eq[j] T[j + k]: one claim on the state before chi, quadratic in beta.
    sp, beta, cursor = fs_grind_squeeze(sp, rate, 3, cursor, tabs, KECCAK_BETA_GRIND_BITS)
    out[GEN ** KC_VALUE] = t0 + beta * (t1 + beta * t2)
    out[GEN ** KC_POINT] = point
    out[GEN ** KC_LOCAL] = local
    lanes = HeapBuf(KECCAK_LANES)
    for y in unroll(0, 5):
        for x in unroll(0, 5):
            lanes[GEN ** (x + 5 * y)] = f_lanes[LANE_OFF + x + 5 * y] + beta * (f_lanes[LANE_OFF + (x + 4) % 5 + 5 * y] + beta * f_lanes[LANE_OFF + (x + 3) % 5 + 5 * y])
    out[GEN ** KC_LANES] = lanes
    # The next layer's iota term: for every i, the new claim's weight on slice 2^i - 1
    # of lane 0, through the linear layer's transpose, from its lane and slice weights.
    # The slice weights are an eq tree on the low five coordinates, times the top
    # one's factor where a weight is read.
    slices = StackBuf(2 ** KECCAK_Z_BITS - 2)
    eqtree_frame(local, slices, KECCAK_Z_BITS - 1, 2 ** (KECCAK_Z_BITS - 1))
    top = local[GEN ** (KECCAK_Z_BITS - 1)]
    top1 = 1 + top
    flips = HeapBuf(KECCAK_IOTA_BITS)
    for i in unroll(0, KECCAK_IOTA_BITS):
        flipped = lanes[GEN ** KECCAK_PI[0]] * slice_weight(slices, top, top1, (2 ** i - 1 + KECCAK_RHO[0]) % 64)
        for y in unroll(0, 5):
            flipped += lanes[GEN ** KECCAK_PI[1 + 5 * y]] * slice_weight(slices, top, top1, (2 ** i - 1 + KECCAK_RHO[1 + 5 * y]) % 64)
            flipped += lanes[GEN ** KECCAK_PI[4 + 5 * y]] * slice_weight(slices, top, top1, (2 ** i + KECCAK_RHO[4 + 5 * y]) % 64)
        flips[GEN ** i] = flipped
    out[GEN ** KC_FLIPS] = flips
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor
```
-/
def keccakLayer_2 (first : Nat) : GFn where
  name := instName "keccak_layer" [.L first]
  arity := 15
  rets := 6
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let p0 := cellOf ps 5
    let p1 := cellOf ps 6
    let cursor := cellOf ps 7
    let yG := cellOf ps 8
    let stepG := cellOf ps 9
    let remG := cellOf ps 10
    let claim := cellOf ps 11
    let out := cellOf ps 12
    let iota := cellOf ps 13
    let tabs := cellOf ps 14
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut rate ← B.stackBuf 8
    if first = 1 then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    let readers ← B.stackBuf KECCAK_PROJ_CELLS
    for i_k in [0:KECCAK_PACK] do
      B.loadInto (cellOf readers i_k) claim (KC_MU + i_k)
    for t_k in [0:KECCAK_PROJ_A.length] do
      B.addInto (cellOf readers (KECCAK_PACK + t_k)) (cellOf readers (arrInt KECCAK_PROJ_A t_k)) (cellOf readers (arrInt KECCAK_PROJ_B t_k))
    let product ← B.stackBuf KECCAK_PROD_BITS
    let projected := 0
    let mut projected_word : Word := default
    let pos_k := 0
    B.loadInto (cellOf product (pos_k - first)) cursor (pos_k - first)
    let coefficient := cellOf product (pos_k - first)
    if (pos_k % 4) = 0 then
      if pos_k ≠ 0 then
        pure () -- no use of this definition takes this branch
      else
        pure ()
    else
      pure () -- no use of this definition takes this branch
    fsPack rate (pos_k % 4) coefficient DS_OBSERVE
    projected_word ← B.mul (cellOf readers (arrInt KECCAK_PROJ_OUT (pos_k - first))) coefficient
    for pos_k in [1:first + KECCAK_PROD_BITS] do
      B.loadInto (cellOf product (pos_k - first)) cursor (pos_k - first)
      let coefficient := cellOf product (pos_k - first)
      if (pos_k % 4) = 0 then
        if pos_k ≠ 0 then
          sp ← fsPerm sp rate 4
          rate ← B.stackBuf 8
        else
          pure () -- no use of this definition takes this branch
      else
        pure ()
      fsPack rate (pos_k % 4) coefficient DS_OBSERVE
      projected_word ← B.add projected_word (← B.mul (cellOf readers (arrInt KECCAK_PROJ_OUT (pos_k - first))) coefficient)
    let cursor_ptr : Shifted := ⟨cursor, KECCAK_PROD_BITS⟩
    B.assertEq (← B.add projected_word (← B.mul iota (← B.load claim KC_KAPPA))) (← B.load claim KC_VALUE)
    let (t0, t1, t2) ← fsGrindSqueeze sp rate ((((first + KECCAK_PROD_BITS) + 3) % 4) + 1) (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs 3
    sp := t0
    let s := t1
    let mut cursor_ptr : Shifted := t2
    let sPowers ← B.stackBuf KECCAK_FAC_DEG
    B.constInto (cellOf sPowers 0) 1
    B.copy (cellOf sPowers 1) s
    for b_k in [2:KECCAK_FAC_DEG] do
      B.mulInto (cellOf sPowers b_k) (cellOf sPowers (b_k - 1)) s
    let factors ← B.stackBuf KECCAK_EMB_CELLS
    let f_k := 0
    let acc := 0
    let mut acc_word : Word := default
    let t_k := 0
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    B.copy (cellOf factors f_k) acc_word
    let f_k := 1
    let acc := 0
    let t_k := 1
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    let t_k := 2
    acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 2
    let acc := 0
    let t_k := 3
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [4:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 3
    let acc := 0
    let t_k := 6
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [7:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 4
    let acc := 0
    let t_k := 9
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [10:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 5
    let acc := 0
    let t_k := 12
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [13:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 6
    let acc := 0
    let t_k := 15
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [16:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    let f_k := 7
    let acc := 0
    let t_k := 18
    acc_word := cellOf sPowers (arrInt KECCAK_FAC_IDX t_k)
    for t_k in [19:arrInt KECCAK_FAC_START (f_k + 1)] do
      acc_word ← B.add acc_word (cellOf sPowers (arrInt KECCAK_FAC_IDX t_k))
    B.copy (cellOf factors f_k) acc_word
    for t_k in [0:KECCAK_EMB_A.length] do
      B.mulInto (cellOf factors (KECCAK_FAC_N + t_k)) (cellOf factors (arrInt KECCAK_EMB_A t_k)) (cellOf factors (arrInt KECCAK_EMB_B t_k))
    let kappa := 0
    let mut kappa_word : Word := default
    let i_k := 0
    B.store out (KC_MU + i_k) (cellOf factors (arrInt KECCAK_EMB_OUT i_k))
    kappa_word := cellOf factors (arrInt KECCAK_EMB_OUT i_k)
    for i_k in [1:KECCAK_PACK] do
      B.store out (KC_MU + i_k) (cellOf factors (arrInt KECCAK_EMB_OUT i_k))
      kappa_word ← B.add kappa_word (cellOf factors (arrInt KECCAK_EMB_OUT i_k))
    B.store out KC_KAPPA kappa_word
    let mut value := cellOf product (KECCAK_PROD_BITS - 1)
    for k_k in [1:KECCAK_PROD_BITS] do
      value ← B.add (← B.mul value s) (cellOf product ((KECCAK_PROD_BITS - 1) - k_k))
    let prevPoint ← B.load claim KC_POINT
    let point ← B.heapBufDyn yG
    let rounds ← B.heapBuf 77
    fsStore_2 rounds KR_FS KR_CAP sp
    B.store rounds 55 (← B.shifted cursor_ptr.base cursor_ptr.exp)
    B.store rounds 66 value
    B.loopRtF 0 (pure stepG) 4 (pure ([rounds.v, prevPoint.v, point.v, tabs.v])) fun xs caps => do
      let rounds := cellOf caps 0
      let prevPoint := cellOf caps 1
      let point := cellOf caps 2
      let tabs := cellOf caps 3
      let rd ← B.mul rounds xs
      let pp ← B.mul prevPoint (← B.pow xs KR_STEP)
      let pt ← B.mul point (← B.pow xs KR_STEP)
      let mut roundSp ← fsLoad rd KR_FS KR_CAP
      let curI ← B.load rd 55
      let mut run ← B.load rd 66
      let mut curI_ptr : Shifted := default
      let q_k := 0
      let rEq ← B.load pp q_k
      let rate ← B.stackBuf 8
      let (t0, t1) ← fsNext rate 0 curI
      let g1 := t0
      curI_ptr := t1
      let (t2, t3) ← fsNext_2 rate 1 (⟨curI_ptr.base, curI_ptr.exp⟩)
      let g2 := t2
      curI_ptr := t3
      let (t4, t5, t6) ← fsGrindSqueeze roundSp rate 2 (⟨curI_ptr.base, curI_ptr.exp⟩) tabs ROUND3_GRIND_BITS
      roundSp := t4
      let challenge := t5
      curI_ptr := t6
      B.store pt q_k challenge
      let gap ← B.add rEq challenge
      run ← B.add (← B.add run (← B.mul gap g1)) (← B.mul (← B.add rEq (← B.mul challenge challenge)) g2)
      for q_k in [1:KR_STEP] do
        let rEq ← B.load pp q_k
        let rate ← B.stackBuf 8
        let (t0, t1) ← fsNext_2 rate 0 (⟨curI_ptr.base, curI_ptr.exp⟩)
        let g1 := t0
        curI_ptr := t1
        let (t2, t3) ← fsNext_2 rate 1 (⟨curI_ptr.base, curI_ptr.exp⟩)
        let g2 := t2
        curI_ptr := t3
        let (t4, t5, t6) ← fsGrindSqueeze roundSp rate 2 (⟨curI_ptr.base, curI_ptr.exp⟩) tabs ROUND3_GRIND_BITS
        roundSp := t4
        let challenge := t5
        curI_ptr := t6
        B.store pt q_k challenge
        let gap ← B.add rEq challenge
        run ← B.add (← B.add run (← B.mul gap g1)) (← B.mul (← B.add rEq (← B.mul challenge challenge)) g2)
      let nxt : Shifted := ⟨rd, 1⟩
      fsStore (⟨nxt.base, nxt.exp⟩) KR_FS KR_CAP roundSp
      B.store nxt.base (nxt.exp + 55) (← B.shifted curI_ptr.base curI_ptr.exp)
      B.store nxt.base (nxt.exp + 66) run
    let remRounds ← B.mul rounds stepG
    let remPrev ← B.mul prevPoint (← B.pow stepG KR_STEP)
    let remPoint ← B.mul point (← B.pow stepG KR_STEP)
    B.loopRtF 0 (pure remG) 4 (pure ([remRounds.v, remPrev.v, tabs.v, remPoint.v])) fun x1 caps => do
      let remRounds := cellOf caps 0
      let remPrev := cellOf caps 1
      let tabs := cellOf caps 2
      let remPoint := cellOf caps 3
      let rd ← B.mul remRounds x1
      let rEq ← B.load (← B.mul remPrev x1) 0
      let roundSp ← fsLoad rd KR_FS KR_CAP
      let curI ← B.load rd 55
      let rate ← B.stackBuf 8
      let (t0, t1) ← fsNext rate 0 curI
      let g1 := t0
      let curI_ptr : Shifted := t1
      let (t2, t3) ← fsNext_2 rate 1 (⟨curI_ptr.base, curI_ptr.exp⟩)
      let g2 := t2
      let curI_ptr : Shifted := t3
      let (t4, t5, t6) ← fsGrindSqueeze roundSp rate 2 (⟨curI_ptr.base, curI_ptr.exp⟩) tabs ROUND3_GRIND_BITS
      let roundSp := t4
      let challenge := t5
      let curI_ptr : Shifted := t6
      B.store (← B.mul remPoint x1) 0 challenge
      let gap ← B.add rEq challenge
      let nxt : Shifted := ⟨rd, 1⟩
      fsStore (⟨nxt.base, nxt.exp⟩) KR_FS KR_CAP roundSp
      B.store nxt.base (nxt.exp + 55) (← B.shifted curI_ptr.base curI_ptr.exp)
      B.store nxt.base (nxt.exp + 66) (← B.add (← B.add (← B.load rd 66) (← B.mul gap g1)) (← B.mul (← B.add rEq (← B.mul challenge challenge)) g2))
    let last ← B.mul remRounds remG
    sp ← fsLoad last KR_FS KR_CAP
    let cursor ← B.load last 55
    value ← B.load last 66
    let local' ← B.heapBuf KECCAK_LOCAL_BITS
    let i_k := 0
    rate ← B.stackBuf 8
    let (t3, t4) ← fsNext rate 0 cursor
    let c0 := t3
    cursor_ptr := t4
    let (t5, t6) ← fsNext_2 rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let c2 := t5
    cursor_ptr := t6
    let (t7, t8) ← fsNext_2 rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let c3 := t7
    cursor_ptr := t8
    let (t9, t10, t11) ← fsGrindSqueeze sp rate 3 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs ROUND3_GRIND_BITS
    sp := t9
    let challenge := t10
    cursor_ptr := t11
    B.store local' i_k challenge
    let challenge1 ← B.add (← B.const 1) challenge
    value ← B.add c0 (← B.mul challenge (← B.add value (← B.mul challenge1 (← B.add c2 (← B.mul challenge1 c3)))))
    for i_k in [1:KECCAK_LOCAL_BITS] do
      rate ← B.stackBuf 8
      let (t3, t4) ← fsNext_2 rate 0 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      let c0 := t3
      cursor_ptr := t4
      let (t5, t6) ← fsNext_2 rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      let c2 := t5
      cursor_ptr := t6
      let (t7, t8) ← fsNext_2 rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
      let c3 := t7
      cursor_ptr := t8
      let (t9, t10, t11) ← fsGrindSqueeze sp rate 3 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs ROUND3_GRIND_BITS
      sp := t9
      let challenge := t10
      cursor_ptr := t11
      B.store local' i_k challenge
      let challenge1 ← B.add (← B.const 1) challenge
      value ← B.add c0 (← B.mul challenge (← B.add value (← B.mul challenge1 (← B.add c2 (← B.mul challenge1 c3)))))
    rate ← B.stackBuf 8
    let (t12, t13) ← fsNext_2 rate 0 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let t0 := t12
    cursor_ptr := t13
    let (t14, t15) ← fsNext_2 rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let t1 := t14
    cursor_ptr := t15
    let (t16, t17) ← fsNext_2 rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
    let t2 := t16
    cursor_ptr := t17
    let fLanes ← B.stackBuf 62
    eqtreeFrame_3 (⟨local', KECCAK_Z_BITS⟩) fLanes KECCAK_LANE_BITS KECCAK_LANES
    let prevLanes ← B.load claim KC_LANES
    let weightAtLocal ← B.stackBuf 1
    if first = 1 then
      pure () -- no use of this definition takes this branch
    else
      let shifts ← B.stackBuf 64
      keccakShiftsEq (← B.load claim KC_LOCAL) local' shifts
      keccakForm_2 prevLanes shifts fLanes LANE_OFF [(cellOf weightAtLocal 0).v]
    B.assertEq (← B.mul (cellOf weightAtLocal 0) (← B.add (← B.mul kappa_word t0) (← B.mul (← B.add kappa_word t1) t2))) value
    let (t18, t19, t20) ← fsGrindSqueeze sp rate 3 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs KECCAK_BETA_GRIND_BITS
    sp := t18
    let beta := t19
    cursor_ptr := t20
    B.store out KC_VALUE (← B.add t0 (← B.mul beta (← B.add t1 (← B.mul beta t2))))
    B.store out KC_POINT point
    B.store out KC_LOCAL local'
    let lanes ← B.heapBuf KECCAK_LANES
    for y_k in [0:5] do
      for x_k in [0:5] do
        B.store lanes (x_k + (5 * y_k)) (← B.add (cellOf fLanes ((LANE_OFF + x_k) + (5 * y_k))) (← B.mul beta (← B.add (cellOf fLanes ((LANE_OFF + ((x_k + 4) % 5)) + (5 * y_k))) (← B.mul beta (cellOf fLanes ((LANE_OFF + ((x_k + 3) % 5)) + (5 * y_k)))))))
    B.store out KC_LANES lanes
    let slices ← B.stackBuf 62
    eqtreeFrame_2 local' slices (KECCAK_Z_BITS - 1) (2 ^ (KECCAK_Z_BITS - 1))
    let top ← B.load local' 5
    let top1 ← B.add (← B.const 1) top
    let flips ← B.heapBuf KECCAK_IOTA_BITS
    for i_k in [0:KECCAK_IOTA_BITS] do
      let t22 ← B.load lanes (arrInt KECCAK_PI 0)
      let t21 ← sliceWeight slices top top1 ((((2 ^ i_k) - 1) + (arrInt KECCAK_RHO 0)) % 64)
      let mut flipped ← B.mul t22 t21
      for y_k in [0:5] do
        let t24 ← B.load lanes (arrInt KECCAK_PI (1 + (5 * y_k)))
        let t23 ← sliceWeight slices top top1 ((((2 ^ i_k) - 1) + (arrInt KECCAK_RHO (1 + (5 * y_k)))) % 64)
        flipped ← B.add flipped (← B.mul t24 t23)
        let t26 ← B.load lanes (arrInt KECCAK_PI (4 + (5 * y_k)))
        let t25 ← sliceWeight slices top top1 (((2 ^ i_k) + (arrInt KECCAK_RHO (4 + (5 * y_k)))) % 64)
        flipped ← B.add flipped (← B.mul t26 t25)
      B.store flips i_k flipped
    B.store out KC_FLIPS flips
    let t27 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted cursor_ptr.base cursor_ptr.exp)
    return [.v (cellOf sp 8).v] ++ [.v (cellOf sp 9).v] ++ [.v (cellOf sp 10).v] ++ [.v (cellOf sp 11).v] ++ [.v (cellOf sp 12).v] ++ [.into t27]

set_option linter.unusedVariables false in
/-- `keccak_plain_rounds`, a `Const` family (`guests/lean_ethereum.py`, line 3072):

```
def keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, p0, p1, cursor, value, point, tabs, n: Const, k0: Const):
    # n rounds of a degree-2 sumcheck with no equality factor, each grinding for its
    # degree. With k0 = 1 one scalar already waits in the sponge, rate cells p0 and p1,
    # and the first round's words join it.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    for i in unroll(0, n):
        rate = StackBuf(8)
        if i == 0:
            if k0 == 1:
                rate[0] = p0
                rate[1] = p1
                c0, cursor = fs_next(rate, 1, cursor)
                c2, cursor = fs_next(rate, 2, cursor)
                sp, challenge, cursor = fs_grind_squeeze(sp, rate, 3, cursor, tabs, ROUND2_GRIND_BITS)
            else:
                c0, cursor = fs_next(rate, 0, cursor)
                c2, cursor = fs_next(rate, 1, cursor)
                sp, challenge, cursor = fs_grind_squeeze(sp, rate, 2, cursor, tabs, ROUND2_GRIND_BITS)
        else:
            c0, cursor = fs_next(rate, 0, cursor)
            c2, cursor = fs_next(rate, 1, cursor)
            sp, challenge, cursor = fs_grind_squeeze(sp, rate, 2, cursor, tabs, ROUND2_GRIND_BITS)
        c1 = value + c2
        point[GEN ** i] = challenge
        value = c0 + challenge * (c1 + challenge * c2)
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, value
```
-/
def keccakPlainRounds (n : Nat) (k0 : Nat) : GFn where
  name := instName "keccak_plain_rounds" [.L n, .L k0]
  arity := 11
  rets := 7
  body ps := do
    let fs0 := cellOf ps 0
    let fs1 := cellOf ps 1
    let fs2 := cellOf ps 2
    let fs3 := cellOf ps 3
    let fs4 := cellOf ps 4
    let p0 := cellOf ps 5
    let p1 := cellOf ps 6
    let cursor := cellOf ps 7
    let mut value := cellOf ps 8
    let point := cellOf ps 9
    let tabs := cellOf ps 10
    let mut sp ← fsCap fs0 fs1 fs2 fs3 fs4
    let mut cursor_ptr : Shifted := default
    let i_k := 0
    let rate ← B.stackBuf 8
    let mut c0 : Word := default
    let mut c2 : Word := default
    let mut challenge : Word := default
    if i_k = 0 then
      if k0 = 1 then
        B.copy (cellOf rate 0) p0
        B.copy (cellOf rate 1) p1
        let (t0, t1) ← fsNext rate 1 cursor
        c0 := t0
        cursor_ptr := t1
        let (t2, t3) ← fsNext_2 rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
        c2 := t2
        cursor_ptr := t3
        let (t4, t5, t6) ← fsGrindSqueeze sp rate 3 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs ROUND2_GRIND_BITS
        sp := t4
        challenge := t5
        cursor_ptr := t6
      else
        let (t0, t1) ← fsNext rate 0 cursor
        c0 := t0
        cursor_ptr := t1
        let (t2, t3) ← fsNext_2 rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
        c2 := t2
        cursor_ptr := t3
        let (t4, t5, t6) ← fsGrindSqueeze sp rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs ROUND2_GRIND_BITS
        sp := t4
        challenge := t5
        cursor_ptr := t6
    else
      pure () -- no use of this definition takes this branch
    let c1 ← B.add value c2
    B.store point i_k challenge
    value ← B.add c0 (← B.mul challenge (← B.add c1 (← B.mul challenge c2)))
    for i_k in [1:n] do
      let rate ← B.stackBuf 8
      if i_k = 0 then
        pure () -- no use of this definition takes this branch
      else
        let (t0, t1) ← fsNext_2 rate 0 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
        c0 := t0
        cursor_ptr := t1
        let (t2, t3) ← fsNext_2 rate 1 (⟨cursor_ptr.base, cursor_ptr.exp⟩)
        c2 := t2
        cursor_ptr := t3
        let (t4, t5, t6) ← fsGrindSqueeze sp rate 2 (⟨cursor_ptr.base, cursor_ptr.exp⟩) tabs ROUND2_GRIND_BITS
        sp := t4
        challenge := t5
        cursor_ptr := t6
      let c1 ← B.add value c2
      B.store point i_k challenge
      value ← B.add c0 (← B.mul challenge (← B.add c1 (← B.mul challenge c2)))
    let t7 : V → B Unit := fun rc => do
      B.copy (wordOf rc) (← B.shifted cursor_ptr.base cursor_ptr.exp)
    return [.v (cellOf sp 8).v] ++ [.v (cellOf sp 9).v] ++ [.v (cellOf sp 10).v] ++ [.v (cellOf sp 11).v] ++ [.v (cellOf sp 12).v] ++ [.into t7] ++ [.v value.v]

set_option linter.unusedVariables false in
/-- `column_selector`, a `Const` family (`guests/lean_ethereum.py`, line 3390):

```
def column_selector(offset, sel_eq, sel_g, kappa: Const):
    # The column's selector at the complete opening point, from hinted g-power digits
    # of its offset's nibbles at and above kappa // 4, each range-checked below 16.
    # Pinning their weighted product to the certified offset makes them its own
    # nibbles (a base-16 representation is unique), and that offset is 2^kappa-aligned
    # (certify_placement orders kappa descending), so the lowest digit, kappa's own
    # nibble, is a multiple of 2^(4 - width): the strided level-width table holds it.
    # Both offset and point are zero above m, so extending to 4 * SEL_NIBBLES adds
    # only factors eq(0, 0) = 1.
    digits = StackBuf(SEL_NIBBLES)
    hint_decompose_digits_exponent(digits, offset, 4 * SEL_NIBBLES, SEL_NIBBLES - kappa // 4, 4, 4 * (kappa // 4))
    if const(kappa // 4 == SEL_NIBBLES):
        selector = GEN ** 0
        rebuilt = GEN ** 0
    for j in unroll(kappa // 4, SEL_NIBBLES):
        width = 4
        if const(j == kappa // 4):
            width = 4 * j + 4 - kappa
        d = digits[j - kappa // 4]
        assert log(d) < 16
        if const(j == kappa // 4):
            selector = sel_eq[GEN ** (SEL_EQ_STRIDE * j + 16 * (width - 1)) * d]
            rebuilt = sel_g[GEN ** (16 * j) * d]
        else:
            selector *= sel_eq[GEN ** (SEL_EQ_STRIDE * j + 16 * (width - 1)) * d]
            rebuilt *= sel_g[GEN ** (16 * j) * d]
    assert rebuilt == offset
    return selector
```
-/
def columnSelector (kappa : Nat) : GFn where
  name := instName "column_selector" [.L kappa]
  arity := 3
  rets := 1
  body ps := do
    let offset := cellOf ps 0
    let selEq := cellOf ps 1
    let selG := cellOf ps 2
    let digits ← B.stackBuf SEL_NIBBLES
    B.hintDigitsExp (.stack (digits.take (SEL_NIBBLES - (kappa / 4)))) offset (4 * SEL_NIBBLES) (SEL_NIBBLES - (kappa / 4)) 4 (4 * (kappa / 4))
    if (kappa / 4) = SEL_NIBBLES then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    let mut selector : Word := default
    let mut rebuilt : Word := default
    for j_k in [kappa / 4:SEL_NIBBLES] do
      let mut width := 4
      if j_k = (kappa / 4) then
        width := ((4 * j_k) + 4) - kappa
      else
        pure ()
      let d := cellOf digits (j_k - (kappa / 4))
      let _ ← B.rangeCheck d 16
      if j_k = (kappa / 4) then
        selector ← B.load (← B.mul selEq d) ((SEL_EQ_STRIDE * j_k) + (16 * (width - 1)))
        rebuilt ← B.load (← B.mul selG d) (16 * j_k)
      else
        selector ← B.mul selector (← B.load (← B.mul selEq d) ((SEL_EQ_STRIDE * j_k) + (16 * (width - 1))))
        rebuilt ← B.mul rebuilt (← B.load (← B.mul selG d) (16 * j_k))
    B.assertEq rebuilt offset
    return [.v selector.v]

set_option linter.unusedVariables false in
/-- `column_selector`, a `Const` family (`guests/lean_ethereum.py`, line 3390):

```
def column_selector(offset, sel_eq, sel_g, kappa: Const):
    # The column's selector at the complete opening point, from hinted g-power digits
    # of its offset's nibbles at and above kappa // 4, each range-checked below 16.
    # Pinning their weighted product to the certified offset makes them its own
    # nibbles (a base-16 representation is unique), and that offset is 2^kappa-aligned
    # (certify_placement orders kappa descending), so the lowest digit, kappa's own
    # nibble, is a multiple of 2^(4 - width): the strided level-width table holds it.
    # Both offset and point are zero above m, so extending to 4 * SEL_NIBBLES adds
    # only factors eq(0, 0) = 1.
    digits = StackBuf(SEL_NIBBLES)
    hint_decompose_digits_exponent(digits, offset, 4 * SEL_NIBBLES, SEL_NIBBLES - kappa // 4, 4, 4 * (kappa // 4))
    if const(kappa // 4 == SEL_NIBBLES):
        selector = GEN ** 0
        rebuilt = GEN ** 0
    for j in unroll(kappa // 4, SEL_NIBBLES):
        width = 4
        if const(j == kappa // 4):
            width = 4 * j + 4 - kappa
        d = digits[j - kappa // 4]
        assert log(d) < 16
        if const(j == kappa // 4):
            selector = sel_eq[GEN ** (SEL_EQ_STRIDE * j + 16 * (width - 1)) * d]
            rebuilt = sel_g[GEN ** (16 * j) * d]
        else:
            selector *= sel_eq[GEN ** (SEL_EQ_STRIDE * j + 16 * (width - 1)) * d]
            rebuilt *= sel_g[GEN ** (16 * j) * d]
    assert rebuilt == offset
    return selector
```
-/
def columnSelector_2 (kappa : Nat) : GFn where
  name := instName "column_selector" [.L kappa]
  arity := 3
  rets := 1
  body ps := do
    let offset := cellOf ps 0
    let selEq := cellOf ps 1
    let selG := cellOf ps 2
    let digits ← B.stackBuf SEL_NIBBLES
    B.hintDigitsExp (.stack (digits.take (SEL_NIBBLES - (kappa / 4)))) offset (4 * SEL_NIBBLES) (SEL_NIBBLES - (kappa / 4)) 4 (4 * (kappa / 4))
    if (kappa / 4) = SEL_NIBBLES then
      pure () -- no use of this definition takes this branch
    else
      pure ()
    let mut selector : Word := default
    let mut rebuilt : Word := default
    let j_k := 7
    let mut width := 4
    if j_k = (kappa / 4) then
      width := ((4 * j_k) + 4) - kappa
    else
      pure () -- no use of this definition takes this branch
    let d := cellOf digits (j_k - (kappa / 4))
    let _ ← B.rangeCheck d 16
    if j_k = (kappa / 4) then
      selector ← B.load (← B.mul selEq d) ((SEL_EQ_STRIDE * j_k) + (16 * (width - 1)))
      rebuilt ← B.load (← B.mul selG d) (16 * j_k)
    else
      pure () -- no use of this definition takes this branch
    B.assertEq rebuilt offset
    return [.v selector.v]

set_option linter.unusedVariables false in
/-- `bus_grind_check`, a `Const` family (`guests/lean_ethereum.py`, line 3533):

```
def bus_grind_check(word, tabs, d: Const):
    # The bus's grind at a push depth of BUS_MIN_MU + d.
    grind_check(word, tabs, BUS_GRIND_BITS[BUS_MIN_MU + d])
    return 0
```
-/
def busGrindCheck (d : Nat) : GFn where
  name := instName "bus_grind_check" [.L d]
  arity := 2
  rets := 1
  body ps := do
    let word' := cellOf ps 0
    let tabs := cellOf ps 1
    let _ ← B.call (instName "grind_check" [.L (arrInt BUS_GRIND_BITS (BUS_MIN_MU + d))]) [word'.v, tabs.v] 0
    return [.c 0]

end
end LeanVM.Dsl.Gen
