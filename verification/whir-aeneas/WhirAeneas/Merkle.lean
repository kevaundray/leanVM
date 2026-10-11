import WhirAeneas.Generated.Merkle.Funs

/-! The generated `pcs::merkle` opening surface: `PrunedMerklePaths::from_hint` decodes a hint
into rows and siblings, and `PrunedMerklePaths::open` accepts exactly when rebuilding every node
on the queried paths consumes every supplied sibling and reproduces the root, returning each
query's leaf image and sibling path. The hash kernels `hash_rows` and `hash_pairs` are the hash
boundary: `RowHash` and `PairHash` state their content contracts over abstract leaf and pair
hashes. Index and length premises are stated where the source would otherwise wrap. -/
namespace WhirAeneas.Merkle
open Aeneas Aeneas.Std MerkleSource

abbrev Digest := Aeneas.Std.Array U8 32#usize

private theorem loop_cont {α β : Type} {body : α → Result (ControlFlow α β)} {x x' : α}
    (h : body x = .ok (.cont x')) : loop body x = loop body x' := by
  rw [loop]; simp [h]

private theorem loop_done {α β : Type} {body : α → Result (ControlFlow α β)} {x : α} {y : β}
    (h : body x = .ok (.done y)) : loop body x = .ok y := by
  rw [loop]; simp [h]

theorem usize_lt_size (i : Usize) : i.val < UScalar.size .Usize := by
  have := Usize.max_def
  simp only [UScalar.size] at *
  scalar_tac

theorem add_val (a b : Usize) (h : a.val + b.val ≤ Usize.max) :
    (Std.Usize.wrapping_add a b).val = a.val + b.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have := Usize.max_def; simp only [UScalar.size] at *; scalar_tac

theorem sub_val (a b : Usize) (h : b.val ≤ a.val) :
    (Std.Usize.wrapping_sub a b).val = a.val - b.val := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have hs := usize_lt_size a
  rw [show a.val + (UScalar.size .Usize - b.val) = (a.val - b.val) + UScalar.size .Usize by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem mul_val (a b : Usize) (h : a.val * b.val ≤ Usize.max) :
    (Std.Usize.wrapping_mul a b).val = a.val * b.val := by
  rw [Std.Usize.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  have := Usize.max_def; simp only [UScalar.size] at *; scalar_tac

theorem slice_index {α : Type} (s : Slice α) (i : Usize) (hi : i.val < s.val.length) :
    Slice.index_usize s i = .ok s.val[i.val] := by
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, hi]

theorem vec_index {α : Type} (v : alloc.vec.Vec α) (i : Usize) (hi : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = .ok v.val[i.val] := by
  rw [alloc.vec.Vec.index_slice_index]
  simp [alloc.vec.Vec.index_usize, hi]

theorem push_ok {α : Type} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    ∃ w, alloc.vec.Vec.push v x = .ok w ∧ w.val = v.val ++ [x] := by
  have : v.val.length + 1 ≤ Usize.max := by omega
  refine ⟨alloc.vec.Vec.from (v.val ++ [x]) (by simp; omega), ?_, alloc.vec.Vec.from_val _ _⟩
  unfold alloc.vec.Vec.push
  simp [this, List.concat_eq_append]

theorem slice_range {α : Type} (s : Slice α) (a b : Usize) (hab : a.val ≤ b.val)
    (hb : b.val ≤ s.val.length) :
    ∃ t, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice α)
      s { start := a, «end» := b } = .ok t ∧ t.val = (s.val.drop a.val).take (b.val - a.val) := by
  have h : a ≤ b ∧ b ≤ s.length := ⟨by scalar_tac, by simpa using hb⟩
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, h,
    and_self, ↓reduceIte]
  exact ⟨_, rfl, by simp [List.slice]⟩
/-! ## Decoding a hint -/

/-- The little-endian word at byte `o` of the hint, as `u64::from_le_bytes` reads it. -/
def wordAt (hint : List U8) (o : Nat) : U64 :=
  core.num.U64.from_le_bytes (Array.make 8#usize
    [hint[o]!, hint[o+1]!, hint[o+2]!, hint[o+3]!, hint[o+4]!, hint[o+5]!, hint[o+6]!, hint[o+7]!])

/-- The 32-byte digest at byte `o` of the hint. -/
def digestBytes (hint : List U8) (o : Nat) : List U8 := (hint.drop o).take 32

theorem word_at_eq (hint : Slice U8) (o : Usize) (h : o.val + 8 ≤ hint.val.length) :
    merkle.word_at hint o = .ok (wordAt hint.val o.val) := by
  have hl := hint.property
  have e1 : (Std.Usize.wrapping_add o 1#usize).val = o.val + 1 := add_val _ _ (by simp; omega)
  have e2 : (Std.Usize.wrapping_add o 2#usize).val = o.val + 2 := add_val _ _ (by simp; omega)
  have e3 : (Std.Usize.wrapping_add o 3#usize).val = o.val + 3 := add_val _ _ (by simp; omega)
  have e4 : (Std.Usize.wrapping_add o 4#usize).val = o.val + 4 := add_val _ _ (by simp; omega)
  have e5 : (Std.Usize.wrapping_add o 5#usize).val = o.val + 5 := add_val _ _ (by simp; omega)
  have e6 : (Std.Usize.wrapping_add o 6#usize).val = o.val + 6 := add_val _ _ (by simp; omega)
  have e7 : (Std.Usize.wrapping_add o 7#usize).val = o.val + 7 := add_val _ _ (by simp; omega)
  unfold merkle.word_at
  simp [lift, slice_index hint o (by omega),
    slice_index hint (Std.Usize.wrapping_add o 1#usize) (by rw [e1]; omega),
    slice_index hint (Std.Usize.wrapping_add o 2#usize) (by rw [e2]; omega),
    slice_index hint (Std.Usize.wrapping_add o 3#usize) (by rw [e3]; omega),
    slice_index hint (Std.Usize.wrapping_add o 4#usize) (by rw [e4]; omega),
    slice_index hint (Std.Usize.wrapping_add o 5#usize) (by rw [e5]; omega),
    slice_index hint (Std.Usize.wrapping_add o 6#usize) (by rw [e6]; omega),
    slice_index hint (Std.Usize.wrapping_add o 7#usize) (by rw [e7]; omega), wordAt, e1, e2, e3, e4, e5, e6, e7,
    getElem!_pos hint.val o.val (by omega),
    getElem!_pos hint.val (o.val + 1) (by omega),
    getElem!_pos hint.val (o.val + 2) (by omega),
    getElem!_pos hint.val (o.val + 3) (by omega),
    getElem!_pos hint.val (o.val + 4) (by omega),
    getElem!_pos hint.val (o.val + 5) (by omega),
    getElem!_pos hint.val (o.val + 6) (by omega),
    getElem!_pos hint.val (o.val + 7) (by omega)]

theorem from_hint_loop0_eq (hint : Slice U8) (nw : Usize) (h8 : 8 * nw.val ≤ hint.val.length) :
    ∀ (k : Nat) (i : Usize) (rows : alloc.vec.Vec primitives.field.gf2_64.F64), nw.val - i.val = k →
      i.val ≤ nw.val → rows.val = (List.range i.val).map (fun t => wordAt hint.val (8 * t)) →
      ∃ rows', merkle.PrunedMerklePaths.from_hint_loop0 hint nw rows i = .ok rows' ∧
        rows'.val = (List.range nw.val).map (fun t => wordAt hint.val (8 * t)) := by
  have hl := hint.property
  intro k
  induction k with
  | zero =>
    intro i rows hk hi hrows
    refine ⟨rows, ?_, by rw [hrows, show i.val = nw.val by omega]⟩
    unfold merkle.PrunedMerklePaths.from_hint_loop0
    apply loop_done
    have : ¬ (i < nw) := by scalar_tac
    simp [merkle.PrunedMerklePaths.from_hint_loop0.body, this]
  | succ k ih =>
    intro i rows hk hi hrows
    have hlt : i.val < nw.val := by omega
    have e8 : (Std.Usize.wrapping_mul 8#usize i).val = 8 * i.val := mul_val _ _ (by simp; omega)
    have ei : (Std.Usize.wrapping_add i 1#usize).val = i.val + 1 := add_val _ _ (by simp; omega)
    obtain ⟨rows1, hpush, erows1⟩ := push_ok rows (wordAt hint.val (8 * i.val))
      (by rw [hrows]; simp; omega)
    have hbody : merkle.PrunedMerklePaths.from_hint_loop0.body hint nw rows i =
        .ok (.cont (rows1, Std.Usize.wrapping_add i 1#usize)) := by
      have : i < nw := by scalar_tac
      have hw := word_at_eq hint (Std.Usize.wrapping_mul 8#usize i) (by rw [e8]; omega)
      rw [e8] at hw
      simp [merkle.PrunedMerklePaths.from_hint_loop0.body, this, lift, hw, hpush]
    unfold merkle.PrunedMerklePaths.from_hint_loop0
    rw [loop_cont hbody]
    exact ih _ _ (by rw [ei]; omega) (by rw [ei]; omega)
      (by rw [erows1, hrows, ei, List.range_succ, List.map_append]; rfl)

theorem from_hint_loop1_eq (hint : Slice U8) (rb ns : Usize) (hb : rb.val + 32 * ns.val ≤ hint.val.length) :
    ∀ (k : Nat) (j : Usize) (sibs : alloc.vec.Vec Digest), ns.val - j.val = k →
      j.val ≤ ns.val → sibs.val.map (·.val) = (List.range j.val).map (fun t => digestBytes hint.val (rb.val + 32 * t)) →
      ∃ sibs', merkle.PrunedMerklePaths.from_hint_loop1 hint rb ns sibs j = .ok sibs' ∧
        sibs'.val.map (·.val) = (List.range ns.val).map (fun t => digestBytes hint.val (rb.val + 32 * t)) := by
  have hl := hint.property
  intro k
  induction k with
  | zero =>
    intro j sibs hk hj hs
    refine ⟨sibs, ?_, by rw [hs, show j.val = ns.val by omega]⟩
    unfold merkle.PrunedMerklePaths.from_hint_loop1
    apply loop_done
    have : ¬ (j < ns) := by scalar_tac
    simp [merkle.PrunedMerklePaths.from_hint_loop1.body, this]
  | succ k ih =>
    intro j sibs hk hj hs
    have hlt : j.val < ns.val := by omega
    have e1 : (Std.Usize.wrapping_mul 32#usize j).val = 32 * j.val := mul_val _ _ (by simp; omega)
    have ej : (Std.Usize.wrapping_add j 1#usize).val = j.val + 1 := add_val _ _ (by simp; omega)
    have e2 : (Std.Usize.wrapping_mul 32#usize (Std.Usize.wrapping_add j 1#usize)).val = 32 * (j.val + 1) :=
      by rw [mul_val _ _ (by rw [ej]; simp; omega), ej]; simp
    have ea : (Std.Usize.wrapping_add rb (Std.Usize.wrapping_mul 32#usize j)).val = rb.val + 32 * j.val :=
      by rw [add_val _ _ (by rw [e1]; omega), e1]
    have eb : (Std.Usize.wrapping_add rb (Std.Usize.wrapping_mul 32#usize (Std.Usize.wrapping_add j 1#usize))).val =
        rb.val + 32 * (j.val + 1) := by rw [add_val _ _ (by rw [e2]; omega), e2]
    obtain ⟨t, ht, et⟩ := slice_range hint (Std.Usize.wrapping_add rb (Std.Usize.wrapping_mul 32#usize j))
      (Std.Usize.wrapping_add rb (Std.Usize.wrapping_mul 32#usize (Std.Usize.wrapping_add j 1#usize)))
      (by rw [ea, eb]; omega) (by rw [eb]; omega)
    rw [ea, eb, show rb.val + 32 * (j.val + 1) - (rb.val + 32 * j.val) = 32 by omega] at et
    have htlen : t.val.length = 32 := by rw [et]; simp; omega
    let d : Digest := Array.from_slice (Array.repeat 32#usize 0#u8) t
    have hd : d.val = digestBytes hint.val (rb.val + 32 * j.val) := by
      simp only [d]; rw [Array.from_slice_val _ _ (by simpa using htlen), et]; rfl
    obtain ⟨sibs1, hpush, es1⟩ := push_ok sibs d (by
      have := congrArg List.length hs; simp at this; omega)
    have hbody : merkle.PrunedMerklePaths.from_hint_loop1.body hint rb ns sibs j =
        .ok (.cont (sibs1, Std.Usize.wrapping_add j 1#usize)) := by
      have : j < ns := by scalar_tac
      have hcopy : core.slice.Slice.copy_from_slice core.marker.CopyU8
          (Array.to_slice (Array.repeat 32#usize 0#u8)) t = .ok t := by
        simp [core.slice.Slice.copy_from_slice, Array.to_slice, Slice.len, htlen]
      simp only [core.slice.index.Slice.index] at ht
      simp [merkle.PrunedMerklePaths.from_hint_loop1.body, this, lift, Array.to_slice_mut, ht, hcopy,
        hpush, d]
    unfold merkle.PrunedMerklePaths.from_hint_loop1
    rw [loop_cont hbody]
    exact ih _ _ (by rw [ej]; omega) (by rw [ej]; omega)
      (by rw [es1, List.map_append, hs, ej, List.range_succ, List.map_append, List.map_singleton, hd]; rfl)

/-- Decoding: a hint of `n` rows of `w` words is the rows' `8nw` bytes, read as little-endian
words in order, followed by whole 32-byte siblings. -/
theorem from_hint_some (hint : Slice U8) (n w : Usize)
    (h8 : 8 * (n.val * w.val) ≤ hint.val.length) (h32 : (hint.val.length - 8 * (n.val * w.val)) % 32 = 0) :
    ∃ p, merkle.PrunedMerklePaths.from_hint hint n w = .ok (some p) ∧
      p.rows.val = (List.range (n.val * w.val)).map (fun t => wordAt hint.val (8 * t)) ∧
      p.sibling_hashes.val.map (·.val) = (List.range ((hint.val.length - 8 * (n.val * w.val)) / 32)).map
        (fun t => digestBytes hint.val (8 * (n.val * w.val) + 32 * t)) := by
  have hl := hint.property
  have c1 := Usize.checked_mul_bv_spec n w
  cases hc1 : Usize.checked_mul n w with
  | none => rw [hc1] at c1; simp only at c1; omega
  | some m =>
    rw [hc1] at c1
    obtain ⟨-, hm, -⟩ := c1
    have c2 := Usize.checked_mul_bv_spec m 8#usize
    cases hc2 : Usize.checked_mul m 8#usize with
    | none => rw [hc2] at c2; simp only at c2; simp at c2; omega
    | some r =>
      rw [hc2] at c2
      obtain ⟨-, hr, -⟩ := c2
      have hr' : r.val = 8 * (n.val * w.val) := by rw [hr, hm]; simp; ring
      have hsub : (Std.Usize.wrapping_sub (Slice.len hint) r).val = hint.val.length - 8 * (n.val * w.val) := by
        rw [sub_val _ _ (by simp; omega)]; simp [hr']
      obtain ⟨q, hq, eq⟩ : ∃ q : Usize, Std.Usize.wrapping_sub (Slice.len hint) r / 32#usize = Result.ok q ∧
          q.val = (hint.val.length - 8 * (n.val * w.val)) / 32 := by
        obtain ⟨z, hz, hp⟩ := UScalar.div_bv_spec (Std.Usize.wrapping_sub (Slice.len hint) r)
          (y := 32#usize) (by simp)
        exact ⟨z, hz, by rw [hp.1, hsub]; simp⟩
      obtain ⟨rows, hrows, erows⟩ := from_hint_loop0_eq hint m (by rw [hm]; omega) _ 0#usize
        (alloc.vec.Vec.with_capacity _ m) rfl (by simp) (by simp [alloc.vec.Vec.with_capacity])
      obtain ⟨sibs, hsibs, esibs⟩ := from_hint_loop1_eq hint r q (by rw [hr', eq]; omega) _ 0#usize
        (alloc.vec.Vec.with_capacity _ q) rfl (by simp) (by simp [alloc.vec.Vec.with_capacity])
      refine ⟨{ rows := rows, sibling_hashes := sibs }, ?_, by rw [erows, hm], by rw [esibs, eq, hr']⟩
      have hlt : ¬ (Slice.len hint < r) := by scalar_tac
      have hmul : core.num.Usize.is_multiple_of (Std.Usize.wrapping_sub (Slice.len hint) r) 32#usize =
          .ok true := by
        simp [core.num.Usize.is_multiple_of, UScalar.is_multiple_of, hsub, h32]
      simp [merkle.PrunedMerklePaths.from_hint, lift, hc1, hc2,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch, hmul, hrows, hq, hsibs]
      omega

/-- A hint that does not split into the rows' bytes and whole siblings decodes to nothing. -/
theorem from_hint_none (hint : Slice U8) (n w : Usize)
    (h : ¬ (8 * (n.val * w.val) ≤ hint.val.length ∧ (hint.val.length - 8 * (n.val * w.val)) % 32 = 0)) :
    merkle.PrunedMerklePaths.from_hint hint n w = .ok none := by
  have hl := hint.property
  have c1 := Usize.checked_mul_bv_spec n w
  cases hc1 : Usize.checked_mul n w with
  | none =>
    simp [merkle.PrunedMerklePaths.from_hint, lift, hc1, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  | some m =>
    rw [hc1] at c1
    obtain ⟨-, hm, -⟩ := c1
    have c2 := Usize.checked_mul_bv_spec m 8#usize
    cases hc2 : Usize.checked_mul m 8#usize with
    | none =>
      simp [merkle.PrunedMerklePaths.from_hint, lift, hc1, hc2,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
    | some r =>
      rw [hc2] at c2
      obtain ⟨-, hr, -⟩ := c2
      have hr' : r.val = 8 * (n.val * w.val) := by rw [hr, hm]; simp; ring
      by_cases hlt : hint.val.length < r.val
      · have : Slice.len hint < r := by scalar_tac
        simp [merkle.PrunedMerklePaths.from_hint, lift, hc1, hc2,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch]
        intro; omega
      · have hsub : (Std.Usize.wrapping_sub (Slice.len hint) r).val =
            hint.val.length - 8 * (n.val * w.val) := by
          rw [sub_val _ _ (by simp; omega)]; simp [hr']
        have hmod : (hint.val.length - 8 * (n.val * w.val)) % 32 ≠ 0 := by omega
        have hmul : core.num.Usize.is_multiple_of (Std.Usize.wrapping_sub (Slice.len hint) r) 32#usize =
            .ok false := by
          simp [core.num.Usize.is_multiple_of, UScalar.is_multiple_of, hsub, hmod]
        have : ¬ (Slice.len hint < r) := by scalar_tac
        simp [merkle.PrunedMerklePaths.from_hint, lift, hc1, hc2,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch, this, hmul]

/-! ## Rebuilding the queried paths -/

theorem shr_val (hword : UScalarTy.Usize.numBits = 64) (x : Usize) {Rhs : Type} [WrappingShiftRhs Rhs]
    (s : Rhs) : (Std.Usize.wrapping_shr x s).val = x.val / 2 ^ (WrappingShiftRhs.amount 64 s) := by
  simp only [Std.Usize.wrapping_shr, UScalar.wrapping_shr_rhs, UScalar.val, hword]
  exact (BitVec.toNat_ushiftRight _ _).trans (Nat.shiftRight_eq_div_pow _ _)

theorem shr_one (hword : UScalarTy.Usize.numBits = 64) (x : Usize) :
    (Std.Usize.wrapping_shr x 1#i32).val = x.val / 2 := by
  rw [shr_val hword]; simp

theorem and_one (x : Usize) : (x &&& 1#usize).val = x.val % 2 := by
  simp [UScalar.val_and, Nat.and_one_is_mod]

/-- A node and its supplied sibling as left and right child: the even index is the left. -/
def side (i : Nat) (h d : Digest) : Digest × Digest := if i % 2 = 0 then (h, d) else (d, h)

/-- One level of the rebuild over nodes ascending by index: a node and the next one pair up when
they are the two children of one parent; otherwise the node takes the next supplied sibling,
`sibs[u]`. Returns each parent with its left and right child, in order, and the siblings used. -/
def pairSpec (sibs : List Digest) : List (Nat × Digest) → Nat → Option (List (Nat × Digest × Digest) × Nat)
  | [], u => some ([], u)
  | [(i, h)], u => match sibs[u]? with
    | none => none
    | some d => some ([(i / 2, side i h d)], u + 1)
  | (i, h) :: (j, h') :: rest, u =>
    if i % 2 = 0 ∧ j = i + 1 then
      (pairSpec sibs rest u).map fun r => ((i / 2, h, h') :: r.1, r.2)
    else match sibs[u]? with
      | none => none
      | some d => (pairSpec sibs ((j, h') :: rest) (u + 1)).map fun r => ((i / 2, side i h d) :: r.1, r.2)

/-- Both children of each pair, with their indices: the level's known nodes. -/
def knownOf (ps : List (Nat × Digest × Digest)) : List (Nat × Digest) :=
  ps.flatMap fun p => [(2 * p.1, p.2.1), (2 * p.1 + 1, p.2.2)]

def natNode (x : Usize × Digest) : Nat × Digest := (x.1.val, x.2)

theorem pairSpec_unpaired (sibs : List Digest) (i : Nat) (h : Digest) (rest : List (Nat × Digest)) (u : Nat)
    (hp : ¬ (i % 2 = 0 ∧ ∃ h', rest.head? = some (i + 1, h'))) :
    pairSpec sibs ((i, h) :: rest) u = match sibs[u]? with
      | none => none
      | some d => (pairSpec sibs rest (u + 1)).map fun r => ((i / 2, side i h d) :: r.1, r.2) := by
  match rest with
  | [] => simp only [pairSpec]; cases sibs[u]? <;> rfl
  | (j, h') :: rest =>
    have : ¬ (i % 2 = 0 ∧ j = i + 1) := by
      rintro ⟨h1, rfl⟩; exact hp ⟨h1, h', rfl⟩
    simp only [pairSpec, this, ↓reduceIte]

theorem pairSpec_paired (sibs : List Digest) (i : Nat) (h h' : Digest) (rest : List (Nat × Digest)) (u : Nat)
    (hi : i % 2 = 0) :
    pairSpec sibs ((i, h) :: (i + 1, h') :: rest) u =
      (pairSpec sibs rest u).map fun r => ((i / 2, h, h') :: r.1, r.2) := by
  simp [pairSpec, hi]

/-- What `pair_level` returns after `parents`, `pairs` and `known`, against `pairSpec`'s answer. -/
def PairOut (parents : alloc.vec.Vec Usize) (pairs : alloc.vec.Vec (Aeneas.Std.Array Digest 2#usize))
    (known : alloc.vec.Vec (Usize × Digest))
    (res : Option Usize × alloc.vec.Vec Usize × alloc.vec.Vec (Aeneas.Std.Array Digest 2#usize) ×
      alloc.vec.Vec (Usize × Digest)) : Option (List (Nat × Digest × Digest) × Nat) → Prop
  | none => res.1 = none
  | some (ps, u) => res.1.map (·.val) = some u ∧
      res.2.1.val.map (·.val) = parents.val.map (·.val) ++ ps.map (·.1) ∧
      res.2.2.1.val.map (·.val) = pairs.val.map (·.val) ++ ps.map (fun p => [p.2.1, p.2.2]) ∧
      res.2.2.2.val.map natNode = known.val.map natNode ++ knownOf ps

theorem PairOut_cons {parents parents' : alloc.vec.Vec Usize}
    {pairs pairs' : alloc.vec.Vec (Aeneas.Std.Array Digest 2#usize)}
    {known known' : alloc.vec.Vec (Usize × Digest)} {res} {o} (p : Nat) (l r : Digest)
    (hp : parents'.val.map (·.val) = parents.val.map (·.val) ++ [p])
    (hq : pairs'.val.map (·.val) = pairs.val.map (·.val) ++ [[l, r]])
    (hk : known'.val.map natNode = known.val.map natNode ++ [(2 * p, l), (2 * p + 1, r)])
    (h : PairOut parents' pairs' known' res o) :
    PairOut parents pairs known res (o.map fun x => ((p, l, r) :: x.1, x.2)) := by
  match o with
  | none => exact h
  | some (ps, u) =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, ?_, ?_, ?_⟩
    · rw [h2, hp]; simp
    · rw [h3, hq]; simp
    · rw [h4, hk]; simp [knownOf]

theorem pair_level_loop_eq (hword : UScalarTy.Usize.numBits = 64) (nodes : Slice (Usize × Digest))
    (sibs : Slice Digest) (hidx : ∀ x ∈ nodes.val, x.1.val < 2 ^ 62) :
    ∀ (k : Nat) (i used : Usize) parents pairs known, nodes.val.length - i.val ≤ k →
      i.val ≤ nodes.val.length → used.val ≤ sibs.val.length →
      parents.val.length + (nodes.val.length - i.val) < Usize.max →
      pairs.val.length + (nodes.val.length - i.val) < Usize.max →
      known.val.length + 2 * (nodes.val.length - i.val) < Usize.max →
      ∃ res, merkle.pair_level_loop nodes sibs used parents pairs known i = .ok res ∧
        PairOut parents pairs known res (pairSpec sibs.val ((nodes.val.drop i.val).map natNode) used.val) := by
  have hmax : Usize.max = 2 ^ 64 - 1 := by rw [Usize.max_def, Usize.numBits_def, hword]
  have hsl := sibs.property
  have hnl := nodes.property
  intro k
  induction k with
  | zero =>
    intro i used parents pairs known hk hi hu hP hQ hK
    have hend : i.val = nodes.val.length := by omega
    refine ⟨(some used, parents, pairs, known), ?_, ?_⟩
    · unfold merkle.pair_level_loop
      apply loop_done
      have : ¬ (i < Slice.len nodes) := by scalar_tac
      simp [merkle.pair_level_loop.body, this]
    · rw [hend, List.drop_length]
      simp [pairSpec, PairOut, knownOf]
  | succ k ih =>
    intro i used parents pairs known hk hi hu hP hQ hK
    by_cases hend : i.val = nodes.val.length
    · refine ⟨(some used, parents, pairs, known), ?_, ?_⟩
      · unfold merkle.pair_level_loop
        apply loop_done
        have : ¬ (i < Slice.len nodes) := by scalar_tac
        simp [merkle.pair_level_loop.body, this]
      · rw [hend, List.drop_length]
        simp [pairSpec, PairOut, knownOf]
    have hlt : i.val < nodes.val.length := by omega
    have hlt' : i < Slice.len nodes := by scalar_tac
    obtain ⟨⟨xi, xa⟩, hxd⟩ : ∃ x, nodes.val[i.val] = x := ⟨_, rfl⟩
    set x : Usize × Digest := (xi, xa) with hxdef
    have hx : x.1.val < 2 ^ 62 := hidx x (hxd ▸ List.getElem_mem _)
    have hix : Slice.index_usize nodes i = .ok x := by rw [slice_index nodes i hlt]; exact congrArg _ hxd
    have ei1 : (Std.Usize.wrapping_add i 1#usize).val = i.val + 1 := add_val _ _ (by simp; omega)
    have ex1 : (Std.Usize.wrapping_add x.1 1#usize).val = x.1.val + 1 := add_val _ _ (by simp; omega)
    have epar : (Std.Usize.wrapping_shr x.1 1#i32).val = x.1.val / 2 := shr_one hword x.1
    have e2p : (Std.Usize.wrapping_mul 2#usize (Std.Usize.wrapping_shr x.1 1#i32)).val = 2 * (x.1.val / 2) :=
      by rw [mul_val _ _ (by rw [epar]; simp; omega), epar]; simp
    have e2p1 : (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 2#usize (Std.Usize.wrapping_shr x.1 1#i32))
        1#usize).val = 2 * (x.1.val / 2) + 1 := by rw [add_val _ _ (by rw [e2p]; simp; omega), e2p]; simp
    have hdrop : nodes.val.drop i.val = x :: nodes.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt]; exact congrArg (· :: _) hxd
    have hand := and_one x.1
    by_cases hpaired : x.1.val % 2 = 0 ∧ ∃ y, nodes.val[i.val + 1]? = some y ∧ y.1.val = x.1.val + 1
    · obtain ⟨hev, ⟨yi, ya⟩, hyd, hnext⟩ := hpaired
      set y : Usize × Digest := (yi, ya) with hydef
      have hlt2 : i.val + 1 < nodes.val.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hyd; cases hyd
      have hiy : Slice.index_usize nodes (Std.Usize.wrapping_add i 1#usize) = .ok y := by
        rw [slice_index nodes _ (by rw [ei1]; omega)]
        rw [List.getElem?_eq_getElem hlt2] at hyd
        simp only [ei1]; exact congrArg _ (Option.some.inj hyd)
      have h0 : (x.1 &&& 1#usize) = 0#usize := by scalar_tac
      have hlt1 : Std.Usize.wrapping_add i 1#usize < Slice.len nodes := by scalar_tac
      have hyeq : y.1 = Std.Usize.wrapping_add x.1 1#usize := by scalar_tac
      have ei2 : (Std.Usize.wrapping_add i 2#usize).val = i.val + 2 := add_val _ _ (by simp; omega)
      obtain ⟨p1, hp1, ep1⟩ := push_ok parents (Std.Usize.wrapping_shr x.1 1#i32) (by omega)
      obtain ⟨q1, hq1, eq1⟩ := push_ok pairs (Array.make 2#usize [x.2, y.2]) (by omega)
      obtain ⟨k1, hk1, ek1⟩ := push_ok known
        (Std.Usize.wrapping_mul 2#usize (Std.Usize.wrapping_shr x.1 1#i32), x.2) (by omega)
      obtain ⟨k2, hk2, ek2⟩ := push_ok k1
        (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 2#usize (Std.Usize.wrapping_shr x.1 1#i32)) 1#usize, y.2)
        (by rw [ek1]; simp; omega)
      have hbody : merkle.pair_level_loop.body nodes sibs used parents pairs known i =
          .ok (.cont (used, p1, q1, k2, Std.Usize.wrapping_add i 2#usize)) := by
        simp only [merkle.pair_level_loop.body, hlt', ↓reduceIte, hix, lift, bind_tc_ok]
        have hm1 : (i.val + 1) % Usize.size = i.val + 1 := Nat.mod_eq_of_lt (by
          have := usize_lt_size i; simp only [UScalar.size] at this; scalar_tac)
        have hyeq2 : yi = Std.Usize.wrapping_add xi 1#usize := hyeq
        simp [x, y, h0, hlt1, hiy, hyeq2, hp1, hq1, hk1, hk2, hm1, hlt2]
      obtain ⟨res, hres, hout⟩ := ih (Std.Usize.wrapping_add i 2#usize) used p1 q1 k2
        (by rw [ei2]; omega) (by rw [ei2]; omega) hu
        (by rw [ep1, ei2]; simp; omega) (by rw [eq1, ei2]; simp; omega) (by rw [ek2, ek1, ei2]; simp; omega)
      refine ⟨res, ?_, ?_⟩
      · unfold merkle.pair_level_loop; rw [loop_cont hbody]; exact hres
      · have hdrop2 : nodes.val.drop (i.val + 1) = y :: nodes.val.drop (i.val + 2) := by
          rw [List.drop_eq_getElem_cons hlt2]
          rw [List.getElem?_eq_getElem hlt2] at hyd
          rw [Option.some.inj hyd]
        rw [hdrop, hdrop2, List.map_cons, List.map_cons]
        simp only [natNode, hnext]
        rw [pairSpec_paired _ _ _ _ _ _ hev]
        rw [ei2] at hout
        refine PairOut_cons (x.1.val / 2) x.2 y.2 ?_ ?_ ?_ hout
        · simp [ep1, epar, x]
        · simp [eq1, y]
        · simp [ek2, ek1, e2p1, e2p, natNode, x, y]
    · have hspec := pairSpec_unpaired sibs.val xi.val xa ((nodes.val.drop (i.val + 1)).map natNode) used.val (by
        rintro ⟨hev, h', hh⟩
        apply hpaired; refine ⟨hev, ?_⟩
        rw [List.head?_map, List.head?_drop] at hh
        cases hn : nodes.val[i.val + 1]? with
        | none => rw [hn] at hh; cases hh
        | some y =>
          rw [hn] at hh
          simp only [Option.map_some, Option.some.injEq, natNode, Prod.mk.injEq] at hh
          exact ⟨y, rfl, hh.1⟩)
      have hgoal_drop : (nodes.val.drop i.val).map natNode = (xi.val, xa) :: (nodes.val.drop (i.val + 1)).map natNode := by
        rw [hdrop]; rfl
      -- The two outcomes of the unpaired step.
      have none_tail : used.val = sibs.val.length →
          merkle.pair_level_loop.body nodes sibs used parents pairs known i = .ok (.done (none, parents, pairs, known)) →
          ∃ res, merkle.pair_level_loop nodes sibs used parents pairs known i = .ok res ∧
            PairOut parents pairs known res (pairSpec sibs.val ((nodes.val.drop i.val).map natNode) used.val) := by
        intro hu' hbody
        refine ⟨_, by unfold merkle.pair_level_loop; exact loop_done hbody, ?_⟩
        rw [hgoal_drop, hspec, List.getElem?_eq_none (by omega)]
        rfl
      have some_tail : ∀ (l r : Digest), used.val < sibs.val.length → side xi.val xa sibs.val[used.val]! = (l, r) →
          ∀ (p1 : alloc.vec.Vec Usize) (q1 : alloc.vec.Vec (Aeneas.Std.Array Digest 2#usize))
            (k1 k2 : alloc.vec.Vec (Usize × Digest)),
            p1.val = parents.val ++ [Std.Usize.wrapping_shr xi 1#i32] →
            q1.val.map (·.val) = pairs.val.map (·.val) ++ [[l, r]] →
            k1.val = known.val ++ [(Std.Usize.wrapping_mul 2#usize (Std.Usize.wrapping_shr xi 1#i32), l)] →
            k2.val = k1.val ++ [(Std.Usize.wrapping_add (Std.Usize.wrapping_mul 2#usize
              (Std.Usize.wrapping_shr xi 1#i32)) 1#usize, r)] →
            merkle.pair_level_loop.body nodes sibs used parents pairs known i =
              .ok (.cont (Std.Usize.wrapping_add used 1#usize, p1, q1, k2, Std.Usize.wrapping_add i 1#usize)) →
            ∃ res, merkle.pair_level_loop nodes sibs used parents pairs known i = .ok res ∧
              PairOut parents pairs known res (pairSpec sibs.val ((nodes.val.drop i.val).map natNode) used.val) := by
        intro l r hu' hside p1 q1 k1 k2 ep1 eq1 ek1 ek2 hbody
        have eu1 : (Std.Usize.wrapping_add used 1#usize).val = used.val + 1 := add_val _ _ (by simp; omega)
        obtain ⟨res, hres, hout⟩ := ih (Std.Usize.wrapping_add i 1#usize) (Std.Usize.wrapping_add used 1#usize)
          p1 q1 k2 (by rw [ei1]; omega) (by rw [ei1]; omega) (by rw [eu1]; omega)
          (by rw [ep1, ei1]; simp; omega)
          (by have := congrArg List.length eq1; simp only [List.length_map, List.length_append] at this
              rw [ei1]; simp at this; omega) (by rw [ek2, ek1, ei1]; simp; omega)
        refine ⟨res, by unfold merkle.pair_level_loop; rw [loop_cont hbody]; exact hres, ?_⟩
        rw [hgoal_drop, hspec, List.getElem?_eq_getElem hu']
        rw [getElem!_pos sibs.val used.val hu'] at hside
        simp only [hside]
        rw [ei1, eu1] at hout
        refine PairOut_cons (xi.val / 2) l r ?_ ?_ ?_ hout
        · simp [ep1, shr_one hword]
        · rw [eq1]
        · have e2 : (Std.Usize.wrapping_mul 2#usize (Std.Usize.wrapping_shr xi 1#i32)).val = 2 * (xi.val / 2) := e2p
          have e3 : (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 2#usize (Std.Usize.wrapping_shr xi 1#i32))
            1#usize).val = 2 * (xi.val / 2) + 1 := e2p1
          simp [ek2, ek1, natNode, e2, e3]
      have hm1 : (i.val + 1) % Usize.size = i.val + 1 := Nat.mod_eq_of_lt (by
        have := usize_lt_size i; simp only [UScalar.size] at this; scalar_tac)
      -- Why the node is unpaired: odd, last, or its successor is not its sibling.
      have hreason : xi.val % 2 ≠ 0 ∨ (xi.val % 2 = 0 ∧ ¬ i.val + 1 < nodes.val.length) ∨
          (xi.val % 2 = 0 ∧ ∃ (h2 : i.val + 1 < nodes.val.length),
            (nodes.val[i.val + 1]'h2).1 ≠ Std.Usize.wrapping_add xi 1#usize) := by
        by_cases hev : xi.val % 2 = 0
        · by_cases hlt2 : i.val + 1 < nodes.val.length
          · refine Or.inr (Or.inr ⟨hev, hlt2, fun he => hpaired ⟨hev, nodes.val[i.val + 1], ?_, ?_⟩⟩)
            · exact List.getElem?_eq_getElem hlt2
            · have := congrArg UScalar.val he; rw [this]; exact ex1
          · exact Or.inr (Or.inl ⟨hev, hlt2⟩)
        · exact Or.inl hev
      have hi1 : ∀ (h2 : i.val + 1 < nodes.val.length),
          Slice.index_usize nodes (Std.Usize.wrapping_add i 1#usize) = .ok (nodes.val[i.val + 1]'h2) := by
        intro h2; rw [slice_index nodes _ (by rw [ei1]; omega)]; simp [ei1]
      by_cases hu' : used.val = sibs.val.length
      · have hus : used = Slice.len sibs := by scalar_tac
        apply none_tail hu'
        rcases hreason with hodd | ⟨hev, hlt2⟩ | ⟨hev, hlt2, hne⟩
        · have h1 : (xi &&& 1#usize) ≠ 0#usize := by intro h; have := congrArg UScalar.val h; simp_all
          simp [merkle.pair_level_loop.body, hlt', hix, lift, h1, hus, x]
        · have h0 : (xi &&& 1#usize) = 0#usize := by scalar_tac
          simp [merkle.pair_level_loop.body, hlt', hix, lift, h0, hm1, hlt2, hus, x]
        · have h0 : (xi &&& 1#usize) = 0#usize := by scalar_tac
          obtain ⟨⟨yi, ya⟩, hyd⟩ : ∃ y, nodes.val[i.val + 1]'hlt2 = y := ⟨_, rfl⟩
          rw [hyd] at hne
          have hiy := hi1 hlt2; rw [hyd] at hiy
          simp [merkle.pair_level_loop.body, hlt', hix, lift, h0, hm1, hlt2, hus, x, hiy, hne]
      · have hu2 : used.val < sibs.val.length := by omega
        have hus : ¬ used = Slice.len sibs := by intro h; apply hu'; rw [h]; simp
        have eu1 : (Std.Usize.wrapping_add used 1#usize).val = used.val + 1 := add_val _ _ (by simp; omega)
        obtain ⟨d, hdd⟩ : ∃ d, sibs.val[used.val] = d := ⟨_, rfl⟩
        have hsd : Slice.index_usize sibs (Std.Usize.wrapping_sub (Std.Usize.wrapping_add used 1#usize) 1#usize) =
            .ok d := by
          rw [slice_index sibs _ (by rw [sub_val _ _ (by rw [eu1]; simp), eu1]; simp; omega)]
          simp [sub_val _ _ (show (1#usize).val ≤ (Std.Usize.wrapping_add used 1#usize).val by rw [eu1]; simp), eu1, hdd]
        have hd! : sibs.val[used.val]! = d := by rw [getElem!_pos sibs.val used.val hu2]; exact hdd
        obtain ⟨p1, hp1, ep1⟩ := push_ok parents (Std.Usize.wrapping_shr xi 1#i32) (by omega)
        rcases hreason with hodd | ⟨hev, hlt2⟩ | ⟨hev, hlt2, hne⟩
        · have h1 : (xi &&& 1#usize) ≠ 0#usize := by intro h; have := congrArg UScalar.val h; simp_all
          obtain ⟨q1, hq1, eq1⟩ := push_ok pairs (Array.make 2#usize [d, xa]) (by omega)
          obtain ⟨k1, hk1, ek1⟩ := push_ok known
            (Std.Usize.wrapping_mul 2#usize (Std.Usize.wrapping_shr xi 1#i32), d) (by omega)
          obtain ⟨k2, hk2, ek2⟩ := push_ok k1 (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 2#usize
            (Std.Usize.wrapping_shr xi 1#i32)) 1#usize, xa) (by rw [ek1]; simp; omega)
          refine some_tail d xa hu2 (by simp [side, hd!, hodd]) p1 q1 k1 k2 ep1 (by rw [eq1]; simp) ek1 ek2 ?_
          simp [merkle.pair_level_loop.body, hlt', hix, lift, h1, hus, x, hsd, hp1, hq1, hk1, hk2]
        all_goals
          have h0 : (xi &&& 1#usize) = 0#usize := by scalar_tac
          obtain ⟨q1, hq1, eq1⟩ := push_ok pairs (Array.make 2#usize [xa, d]) (by omega)
          obtain ⟨k1, hk1, ek1⟩ := push_ok known
            (Std.Usize.wrapping_mul 2#usize (Std.Usize.wrapping_shr xi 1#i32), xa) (by omega)
          obtain ⟨k2, hk2, ek2⟩ := push_ok k1 (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 2#usize
            (Std.Usize.wrapping_shr xi 1#i32)) 1#usize, d) (by rw [ek1]; simp; omega)
          refine some_tail xa d hu2 (by simp [side, hd!, hev]) p1 q1 k1 k2 ep1 (by rw [eq1]; simp) ek1 ek2 ?_
        · simp [merkle.pair_level_loop.body, hlt', hix, lift, h0, hm1, hlt2, hus, x, hsd, hp1, hq1, hk1, hk2]
        · obtain ⟨⟨yi, ya⟩, hyd⟩ : ∃ y, nodes.val[i.val + 1]'hlt2 = y := ⟨_, rfl⟩
          rw [hyd] at hne
          have hiy := hi1 hlt2; rw [hyd] at hiy
          simp [merkle.pair_level_loop.body, hlt', hix, lift, h0, hm1, hlt2, hus, x, hiy, hne, hsd, hp1, hq1,
            hk1, hk2]

end WhirAeneas.Merkle
