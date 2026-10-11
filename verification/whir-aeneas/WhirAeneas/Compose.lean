import WhirAeneas.Replay

/-! The composed replay: the generated `verify` returns `Ok` exactly when the model's
`nativeVerify` accepts the challenges and opening the transcript answered. -/
namespace WhirAeneas.Replay
open Aeneas Aeneas.Std ReplaySource Whir Whir.Concrete WhirAeneas.Fold WhirAeneas.Query

/-! ## Saved-context counts -/

section Counts
open AccumulatedTerminalRefinement WHIRNativeArithmetic

theorem foldModel_saved {E : Type} (encode : E → Concrete.E) (rounds : List (E × E × E)) (st : State) :
    (foldModel encode rounds st).source.saved = st.source.saved := by
  induction rounds generalizing st with
  | nil => rfl
  | cons x rounds ih =>
    simp only [foldModel, List.foldl_cons] at ih ⊢
    rw [ih]; rfl

theorem foldModel_ris {E : Type} (encode : E → Concrete.E) (rounds : List (E × E × E)) (st : State) :
    (foldModel encode rounds st).source.ris = st.source.ris ++ rounds.map fun x => encode x.1 := by
  induction rounds generalizing st with
  | nil => simp [foldModel]
  | cons x rounds ih =>
    simp only [foldModel, List.foldl_cons] at ih ⊢
    rw [ih]; simp [foldScalar, SourceState.step]

theorem foldModel_n {E : Type} (encode : E → Concrete.E) (rounds : List (E × E × E)) (st : State) :
    (foldModel encode rounds st).n = st.n - rounds.length := by
  induction rounds generalizing st with
  | nil => simp [foldModel]
  | cons x rounds ih =>
    simp only [foldModel, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih]; simp only [foldScalar]; omega

theorem oodFold_counts (lam : Concrete.E)
    (data : List (Array Concrete.E × Concrete.E × Protocol.Message Concrete.E)) (acc : State × Concrete.E) :
    ((Query.oodFold lam data acc).1.source.saved.filter Query.isOod).length =
        (acc.1.source.saved.filter Query.isOod).length + data.length ∧
      ((Query.oodFold lam data acc).1.source.saved.filter fun sv => !Query.isOod sv).length =
        (acc.1.source.saved.filter fun sv => !Query.isOod sv).length ∧
      (Query.oodFold lam data acc).1.source.ris = acc.1.source.ris ∧
      (Query.oodFold lam data acc).1.n = acc.1.n := by
  induction data generalizing acc with
  | nil => simp [Query.oodFold]
  | cons d data ih =>
    obtain ⟨st, b⟩ := acc
    obtain ⟨z, y, m⟩ := d
    obtain ⟨e1, e2, e3, e4⟩ := ih (batchScalar st (.ood z) y (b * lam) m, b * lam)
    have hsv : (batchScalar st (.ood z) y (b * lam) m).source.saved =
        st.source.saved ++ [⟨st.source.ris.length, .ood z, b * lam⟩] := rfl
    simp only [Query.oodFold]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1, hsv, List.filter_append]
      simp only [List.filter_cons, Query.isOod_ood, List.filter_nil, ↓reduceIte, List.length_append,
        List.length_singleton, List.length_cons, List.length_nil]
      omega
    · rw [e2, hsv, List.filter_append]; simp
    · rw [e3]; rfl
    · rw [e4]; rfl

theorem batch_query_counts (s : State) (n : Nat) (qs : Array Nat) (lam value beta : Concrete.E)
    (m : Protocol.Message Concrete.E) :
    ((batchScalar s (.query n qs lam) value beta m).source.saved.filter Query.isOod).length =
        (s.source.saved.filter Query.isOod).length ∧
      ((batchScalar s (.query n qs lam) value beta m).source.saved.filter fun sv => !Query.isOod sv).length =
        (s.source.saved.filter fun sv => !Query.isOod sv).length + 1 := by
  simp [batchScalar, SourceState.step, List.filter_append]

end Counts

/-! ## The level-0 row reversal -/

theorem run_loop0_eq {K : Type} (L0 : List (List K)) :
    ∀ (m : Nat) (r : Usize) (rows : alloc.vec.Vec (alloc.vec.Vec K)), L0.length - r.val = m →
      r.val ≤ L0.length → rows.val.map (·.val) = (L0.take r.val).map List.reverse ++ L0.drop r.val →
      ∃ rows', whir.verify.WhirReplay.run_loop0 rows r = .ok rows' ∧
        rows'.val.map (·.val) = L0.map List.reverse := by
  intro m
  induction m with
  | zero =>
    intro r rows hm hr hrows
    refine ⟨rows, ?_, ?_⟩
    · unfold whir.verify.WhirReplay.run_loop0
      apply loop_done
      have hlen : rows.val.length = L0.length := by
        have := congrArg List.length hrows; simp at this; omega
      have hle : L0.length ≤ r.val := by omega
      have : ¬ (r < alloc.vec.Vec.len rows) := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; simp [hlen]; exact hle
      simp [whir.verify.WhirReplay.run_loop0.body, this]
    · rw [hrows, List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]; simp
  | succ m ih =>
    intro r rows hm hr hrows
    have hlen : rows.val.length = L0.length := by
      have := congrArg List.length hrows; simp at this; omega
    have hlt : r.val < L0.length := by omega
    have hsucc := succ_val r L0.length hlt (by have := rows.property; omega)
    let row := rows.val[r.val]'(by omega)
    have hrow : row.val = L0[r.val] := by
      have := congrArg (fun l => l[r.val]?) hrows
      simp only [List.getElem?_map] at this
      rw [List.getElem?_append_right (by simp <;> omega)] at this
      simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt), Nat.sub_self,
        List.getElem?_drop, Nat.add_zero] at this
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hlt] at this
      simpa [row] using this
    let rows1 := alloc.vec.Vec.set rows r (alloc.vec.Vec.mk (core.slice.Slice.reverse row.slice))
    have hbody : whir.verify.WhirReplay.run_loop0.body rows r =
        .ok (.cont (rows1, Std.Usize.wrapping_add r 1#usize)) := by
      have : r < alloc.vec.Vec.len rows := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; simp [hlen, hlt]
      simp [whir.verify.WhirReplay.run_loop0.body, this, alloc.vec.Vec.index_mut_usize,
        vec_index_usize rows r (by omega), lift, alloc.vec.Vec.deref_mut, rows1, row]
    obtain ⟨rows', hloop, erows⟩ := ih (Std.Usize.wrapping_add r 1#usize) rows1 (by rw [hsucc]; omega)
      (by rw [hsucc]; omega) (by
        rw [hsucc]
        simp only [rows1, alloc.vec.Vec.set_val_eq]
        rw [List.map_set, hrows, List.set_append_right _ _ (by simp <;> omega)]
        simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt), Nat.sub_self]
        rw [List.drop_eq_getElem_cons hlt, List.set_cons_zero, List.take_add_one,
          List.getElem?_eq_getElem hlt]
        have hx : (alloc.vec.Vec.mk (core.slice.Slice.reverse row.slice)).val = L0[r.val].reverse := by
          rw [← hrow]; simp [core.slice.Slice.reverse, alloc.vec.Vec.val, Slice.from_val]
        rw [hx]
        simp only [List.map_append, List.append_assoc, Option.toList, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append])
    refine ⟨rows', ?_, erows⟩
    unfold whir.verify.WhirReplay.run_loop0
    rw [loop_cont hbody]
    unfold whir.verify.WhirReplay.run_loop0 at hloop
    exact hloop

/-! ## A level's model state -/

section LevelModel
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (encode : E → Concrete.E) (encodeK : K → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E) (index : Q → Nat)

/-- The interpreted out-of-domain claims of a level. -/
def oodList (oods : List (List E × E × E × E)) :
    List (Array Concrete.E × Concrete.E × Protocol.Message Concrete.E) :=
  oods.map fun o => ((o.1.map encode).toArray, encode o.2.1, ⟨encode o.2.2.1, encode o.2.2.2⟩)

theorem oodData_of_forall₂ (ws : List (whir.verify.Ood E)) (l : List (List E × E × E × E))
    (h : List.Forall₂ (OodIs encode) ws l) : Query.oodData encode ws = oodList encode l := by
  induction h with
  | nil => rfl
  | @cons o d _ _ hod _ ih =>
    obtain ⟨hz, hy, hc, ha, _⟩ := hod
    simp only [Query.oodData, oodList, List.map_cons] at ih ⊢
    rw [ih, hz, hy, hc, ha]

theorem oodBatch_level (l : SLevel E Q R K) (base : Bool) (st : State) :
    oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs base) st =
      Query.oodFold (encode l.lambda) (oodList encode l.oods) (st, 1) := by
  rw [oodBatch_eq (oodList encode l.oods) _ _ st (by simp [SLevel.chal, oodList])
    (by simp [SLevel.prf, oodList])]
  rfl

theorem foldBlock_level (l : SLevel E Q R K) (base : Bool) (st : State) :
    foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs base) st = foldModel encode l.folds st :=
  foldBlock_eq encode l.folds _ _ st rfl rfl

/-- A later level's batch, as `finish_query_eq` states it, is the model's `queryBatch`. -/
theorem level_model_eq (l : SLevel E Q R K) (st : State) (j : Nat) (hj : j ≠ 0)
    (b : whir.verify.PendingQuery Q E) (sum : E) (intro : whir.verify.Quad E) (oods : List (whir.verify.Ood E))
    (rowsV : List (alloc.vec.Vec E)) (hbq : b.queries.val = l.queries) (hbl : b.lambda = l.lambda)
    (hbw : b.weights.val.map encode = (Concrete.powers (encode l.lambda) l.queries.length).toList)
    (hoods : List.Forall₂ (OodIs encode) oods l.oods)
    (hsum : encode sum = Protocol.enforced (rowsV.map fun r => (r.val.map encode).toArray).toArray
      ((l.folds.map (·.1)).map encode).toArray (b.weights.val.map encode).toArray false)
    (hrowsV : rowsV.map (fun r => r.val.map encode) = l.rows.map (eRow encodeK ofLimbs))
    (hic : intro.c = l.intro.1) (hia : intro.a = l.intro.2) (n1 : Nat)
    (hn1 : n1 = (foldModel encode l.folds st).n) :
    batchScalar (Query.oodFold (encode b.lambda) (Query.oodData encode oods) (foldModel encode l.folds st, 1)).1
        (.query n1 (b.queries.val.map index).toArray (encode b.lambda)) (encode sum)
        ((Query.oodFold (encode b.lambda) (Query.oodData encode oods) (foldModel encode l.folds st, 1)).2 *
          encode b.lambda) ⟨encode intro.c, encode intro.a⟩ =
      queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n j (l.chal encode)
        (l.prf encode encodeK ofLimbs false) (l.queries.map index).toArray
        (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs false)
          (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st)) := by
  rw [foldBlock_level, oodBatch_level, oodData_of_forall₂ encode oods l.oods hoods, hbl, hbq, hn1, hsum, hic, hia]
  have hw' : (b.weights.val.map encode).toArray = Concrete.powers (encode l.lambda) l.queries.length := by
    rw [hbw]
  have hrw : (rowsV.map fun r => (r.val.map encode).toArray) = (l.rows.map (eRow encodeK ofLimbs)).map
      List.toArray := by rw [← hrowsV]; simp
  have hj' : (j == 0) = false := by simpa using hj
  simp only [queryBatch, hw', hrw, hj', SLevel.prf, SLevel.chal, List.map_map, List.size_toArray,
    List.length_map, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The last level has no out-of-domain claims; its batch is `lastState`. -/
theorem last_model_eq (l : SLevel E Q R K) (st : State) (j : Nat) (hj : j ≠ 0) (hoods : l.oods = []) :
    queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n j (l.chal encode)
        (l.prf encode encodeK ofLimbs false) (l.queries.map index).toArray
        (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs false)
          (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st)) =
      lastState encode encodeK ofLimbs index (foldModel encode l.folds st) (foldModel encode l.folds st).n
        l.queries l.lambda l.rows (l.folds.map (·.1)) l.intro.1 l.intro.2 := by
  rw [foldBlock_level, oodBatch_level, hoods]
  have hj' : (j == 0) = false := by simpa using hj
  simp only [queryBatch, lastState, oodList, List.map_nil, Query.oodFold, hj', SLevel.prf, SLevel.chal,
    List.size_toArray, List.length_map, Bool.false_eq_true, ↓reduceIte, List.map_map]
  rfl

/-- What a level does to the model state's size, fit and saved-context counts. -/
theorem level_state_facts (l : SLevel E Q R K) (base : Bool) (st : State) (j : Nat) (qs : Array Nat)
    (hfits : ModelFits st) (hk : l.folds.length ≤ st.n) (h64 : st.n < 64)
    (hz : ∀ o ∈ l.oods, o.1.length = st.n - l.folds.length) :
    let s' := queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs base) st).n j (l.chal encode)
      (l.prf encode encodeK ofLimbs base) qs (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs base)
        (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs base) st))
    ModelFits s' ∧ s'.n = st.n - l.folds.length ∧
      (s'.source.saved.filter Query.isOod).length = (st.source.saved.filter Query.isOod).length + l.oods.length ∧
      (s'.source.saved.filter fun sv => !Query.isOod sv).length =
        (st.source.saved.filter fun sv => !Query.isOod sv).length + 1 := by
  intro s'
  have hf := ModelFits.ofFold encode l.folds st hfits hk
  have hn1 : (foldModel encode l.folds st).n = st.n - l.folds.length := foldModel_n encode l.folds st
  obtain ⟨hof, hon⟩ := ModelFits.ofOodFold (encode l.lambda) (oodList encode l.oods) (foldModel encode l.folds st, 1)
    hf (fun d hd => by
      simp only [oodList, List.mem_map] at hd
      obtain ⟨o, ho, rfl⟩ := hd
      simp [hz o ho, hn1]) (by rw [hn1]; omega)
  obtain ⟨c1, c2, -, c4⟩ := oodFold_counts (encode l.lambda) (oodList encode l.oods) (foldModel encode l.folds st, 1)
  have hs' : s' = batchScalar (Query.oodFold (encode l.lambda) (oodList encode l.oods) (foldModel encode l.folds st, 1)).1
      (.query (foldModel encode l.folds st).n qs (encode l.lambda))
      (Protocol.enforced (l.prf encode encodeK ofLimbs base).rows (l.chal encode).folds
        (Concrete.powers (encode l.lambda) qs.size) (j == 0))
      ((Query.oodFold (encode l.lambda) (oodList encode l.oods) (foldModel encode l.folds st, 1)).2 * encode l.lambda)
      (l.prf encode encodeK ofLimbs base).intro := by
    simp only [s', foldBlock_level, oodBatch_level, queryBatch]; rfl
  obtain ⟨b1, b2⟩ := batch_query_counts (Query.oodFold (encode l.lambda) (oodList encode l.oods)
    (foldModel encode l.folds st, 1)).1 (foldModel encode l.folds st).n qs (encode l.lambda) _ _ _
  rw [hs']
  refine ⟨ModelFits.batch _ hof _ (by simp [Basis.dimension, hon]) (by rw [hon, hn1]; omega) _ _ _, ?_, ?_, ?_⟩
  · simp only [batchScalar]; rw [hon, hn1]
  · rw [b1, c1, foldModel_saved]; simp [oodList]
  · rw [b2, c2, foldModel_saved]

end LevelModel

/-! ## A middle level of the replay loop -/

section Mid
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : K → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Q → Nat) (tape : V → List (Event E Q R K))

theorem mid_level_eq {T1 : Type}
    (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (config : whir.config.Config) (oracle : whir.verify.Oracle R) (iter : core.ops.range.Range Usize)
    (w : whir.verify.WhirReplay V R K Q E) (st : State) (hrel : Query.StateRel encode index w st)
    (v : V) (n : Usize) (hst : st.n = n.val)
    (l : SLevel E Q R K) (root : R) (hhead : l.head = .inl root) (rest : List (Event E Q R K))
    (hv : tape v = levelTape l ++ rest)
    (hit : iter.start.val < iter.end.val) (hiend : iter.end = alloc.vec.Vec.len config.level_ks)
    (hmid : iter.start.val + 1 < config.level_ks.val.length)
    (hfl : l.folds.length = (config.level_ks.val[iter.start.val]'(by omega)).val)
    (hkn : l.folds.length ≤ n.val)
    (hol : iter.start.val + 2 < config.ood_samples.val.length)
    (hoodn : l.oods.length = (config.ood_samples.val[iter.start.val + 2]'hol).val)
    (hoodz : ∀ o ∈ l.oods, o.1.length = n.val - l.folds.length)
    (hgl : iter.start.val + 1 < config.grinding_bits.val.length)
    (hql : iter.start.val + 1 < config.queries.val.length)
    (hg : config.grinding_bits.val[iter.start.val + 1] ≤ U32.max)
    (hcount : l.queries.length = (config.queries.val[iter.start.val + 1]).val)
    (hrows : l.rows.length = l.queries.length) (hne : l.rows ≠ [])
    (hwidth : ∀ r ∈ l.rows, r.length = 3 * 2 ^ l.folds.length) (hk64 : l.folds.length < 64)
    (hrl : iter.start.val + 2 < config.log_inv_rates.val.length)
    (hk2 : (config.level_ks.val[iter.start.val + 1]).val ≤ n.val - l.folds.length)
    (hcap : w.ris.val.length + l.folds.length ≤ Usize.max)
    (hcapo : w.oods.val.length + l.oods.length < Usize.max) (hcapl : w.levels.val.length < Usize.max)
    (j : Nat) (hj : j ≠ 0) :
    ∃ iter' v' w' n' oracle',
      whir.verify.WhirReplay.run_loop1.body inst W config weight_at iter v w n oracle =
        .ok (.cont (iter', v', w', n', oracle')) ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧ tape v' = rest ∧
      n'.val = n.val - l.folds.length ∧ w'.ris.val = w.ris.val ++ l.folds.map (·.1) ∧
      Query.StateRel encode index w'
        (queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n j (l.chal encode)
          (l.prf encode encodeK ofLimbs false) (l.queries.map index).toArray
          (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs false)
            (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st))) := by
  have hlk := config.level_ks.property
  have hi1 := succ_val iter.start config.level_ks.val.length (by omega) (by omega)
  have hi2 : (Std.Usize.wrapping_add iter.start 2#usize).val = iter.start.val + 2 := by
    have := config.ood_samples.property
    rw [Std.Usize.wrapping_add_val_eq]
    have : iter.start.val + 2 < UScalar.size .Usize := by
      have := Usize.max_def; simp only [UScalar.size] at *; scalar_tac
    have h2 : (2#usize).val = 2 := by simp
    rw [h2]
    exact Nat.mod_eq_of_lt this
  obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some iter hit
  set k := config.level_ks.val[iter.start.val]'(by omega) with hkdef
  have hidx : Slice.index_usize (alloc.vec.Vec.deref config.level_ks) iter.start = .ok k := by
    rw [slice_index _ _ (by simp only [alloc.vec.Vec.deref, Slice.from_val]; omega)]
    simp [alloc.vec.Vec.deref, hkdef]
  have hnk : ¬ (n.val < k.val) := by omega
  -- fold rounds
  obtain ⟨rs, w1, v1, hfold, hv1, ers, eris1, elev1, eoods1, hrel1, hn1⟩ :=
    fold_rounds_eq inst encode const index tape h ht hclone w st hrel v k l.folds _ hfl
      (by rw [hv, levelTape, List.append_assoc]) hcap
  -- root
  have hv1' : tape v1 = .root root :: (oodTape l.oods ++ (batchTape l ++ rest)) := by
    rw [hv1, hhead]; simp [headTape]
  obtain ⟨v2, hroot, hv2⟩ := ht.root v1 root _ hv1'
  -- out-of-domain claims
  have hsub : (Std.Usize.wrapping_sub n k).val = n.val - k.val := Fold.sub_val _ _ (by omega)
  obtain ⟨n1, hn1e⟩ : ∃ n1, Std.Usize.wrapping_sub n k = n1 := ⟨_, rfl⟩
  rw [hn1e] at hsub
  set cnt := config.ood_samples.val[iter.start.val + 2]'hol with hcnt
  have hidxo : Slice.index_usize (alloc.vec.Vec.deref config.ood_samples)
      (Std.Usize.wrapping_add iter.start 2#usize) = .ok cnt := by
    rw [slice_index _ _ (by simp only [alloc.vec.Vec.deref, Slice.from_val]; omega)]
    simp [alloc.vec.Vec.deref, hcnt, hi2]
  obtain ⟨oodsV, v3, hrep, hv3, eoods⟩ := replay_all_eq inst encode tape ht
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v2 cnt n1 l.oods _ hoodn
    (fun d hd => by rw [hsub, hoodz d hd, hfl]) hv2
  -- query phase
  obtain ⟨ph, hph, hphc⟩ : ∃ ph, whir.verify.WhirReplay.phase inst config (Std.Usize.wrapping_add iter.start 1#usize)
      (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate) = .ok ph ∧
      ph.count = config.queries.val[(Std.Usize.wrapping_add iter.start 1#usize).val]'(by rw [hi1]; exact hql) :=
    ⟨_, phase_eq inst config (Std.Usize.wrapping_add iter.start 1#usize)
      (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate) (by rw [hi1]; exact hgl)
      (by rw [hi1]; exact hql) (by simp only [hi1]; exact hg), rfl⟩
  obtain ⟨b, v4, hbq, hv4, ebq, ebl, ebw⟩ := begin_query_eq inst encode const tape h ht v3 ph l.queries l.lambda _
    (by rw [hphc]; simp only [hi1]; exact hcount) (by rw [hv3]; rfl)
  obtain ⟨rowsV, v5, hopen, hv5, erows⟩ := open_e_rows_eq inst encode encodeK ofLimbs index tape hr ht oracle v4
    (alloc.vec.Vec.deref b.queries) l.rows _ (fun r hr' => by rw [hwidth r hr']; omega) hv4
  have hlenrows : rowsV.val.length = l.rows.length := by simpa using congrArg List.length erows
  have hrows_ne : rowsV.val ≠ [] := by
    intro hnil; apply hne; rw [hnil] at hlenrows; exact List.eq_nil_of_length_eq_zero hlenrows.symm
  have hwidthV : ∀ r ∈ rowsV.val, r.val.length = 2 ^ rs.val.length := by
    intro r hr'
    have hmem : r.val.map encode ∈ l.rows.map (eRow encodeK ofLimbs) := by
      rw [← erows]; exact List.mem_map_of_mem hr'
    obtain ⟨wd, hwd, hwe⟩ := List.mem_map.mp hmem
    have := congrArg List.length hwe
    simp only [eRow, List.length_map, List.length_range] at this
    rw [hwidth wd hwd] at this
    rw [ers]; simp at this ⊢
    omega
  obtain ⟨sum, hsum, esum⟩ := Query.ext_enforced_eq inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst
    inst encode const h v5 rowsV (alloc.vec.Vec.deref rs) (alloc.vec.Vec.deref b.weights) (2 ^ rs.val.length)
    hrows_ne (by simpa [alloc.vec.Vec.deref] using hwidthV) (by simp [alloc.vec.Vec.deref, ers] <;> omega)
    (by simp [alloc.vec.Vec.deref]) (by
      have := congrArg List.length ebw
      simp only [List.length_map, Array.length_toList, BatchingRefinement.size_powers] at this
      simp [alloc.vec.Vec.deref, this, hlenrows, hrows])
  have hv5' : tape v5 = .poly l.intro.1 l.intro.2 :: rest := by rw [hv5]; rfl
  obtain ⟨intro, v6, hrecv, hic, hia, hib, hv6⟩ := recv_eq inst encode tape ht
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v5 sum l.intro.1 l.intro.2 _ hv5'
  have hoodsI : ∀ o ∈ oodsV.val, encode o.intro.b = encode o.y + encode o.intro.a := by
    intro o ho
    obtain ⟨d, _, hod⟩ := forall₂_mem eoods o ho
    obtain ⟨_, hy, _, ha, hb⟩ := hod
    rw [hb, hy, ha]
  have hcapo' : w1.oods.val.length + oodsV.val.length < Usize.max := by
    rw [eoods1, eoods.length_eq]; exact hcapo
  obtain ⟨w2, hfin, hris2, hrel2⟩ := Query.finish_query_eq inst encode const index h w1
    (foldModel encode l.folds st) hrel1 v5 v5 v6 b oodsV n1 sum intro (ht.end_scope v5) hrecv
    (by rw [hib, hia]) hoodsI (by rw [ebw, ebq, ebl]) hcapo' (by rw [elev1]; exact hcapl)
  -- next oracle
  obtain ⟨o', horacle, -⟩ := oracle_eq inst config root (Std.Usize.wrapping_add iter.start 1#usize) n1
    (by rw [hi1]; exact hmid) (by simp only [hi1, hsub]; omega) (by rw [hi1]; exact hrl)
  refine ⟨iter1, v6, w2, n1, o', ?_, hs1, he1, hv6, by rw [hsub, hfl], by rw [hris2, eris1, ers], ?_⟩
  · have hne1 : ¬ (Std.Usize.wrapping_add iter.start 1#usize = alloc.vec.Vec.len config.level_ks) := by
      intro he; have := congrArg UScalar.val he; rw [hi1] at this; simp at this; omega
    simp [whir.verify.WhirReplay.run_loop1.body, hnext, whir.config.Config.impl.level_ks, hidx, hnk, hfold,
      core.result.Result.Insts.CoreOpsTry.branch, lift, whir.config.Config.level_steps, hne1, hroot,
      whir.config.Config.impl.ood_samples, hidxo, hn1e, hrep, whir.verify.Oracle.depth, hph, hbq, hopen, hsum,
      hfin, horacle]
  · rw [← level_model_eq encode encodeK ofLimbs index l st j hj b sum intro oodsV.val rowsV.val ebq ebl
      (by rw [ebw]) eoods (by rw [esum, ← ers]; simp [alloc.vec.Vec.deref]) erows hic hia n1.val
      (by rw [hsub, hn1, hst])]
    exact hrel2

/-- The loop's last iteration replays the last level against the model's last level and
the closing rounds. -/
theorem last_iter_eq {T1 : Type} (hw : System.Platform.numBits = 64)
    (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : whir.config.Config) (oracle : whir.verify.Oracle R) (iter : core.ops.range.Range Usize)
    (w : whir.verify.WhirReplay V R K Q E) (st : State) (hrel : Query.StateRel encode index w st)
    (hfits : ModelFits st) (v : V) (n : Usize) (hst : st.n = n.val) (hn64 : n.val < 64)
    (l : SLevel E Q R K) (ys : List E) (hhead : l.head = .inr ys) (hoods : l.oods = [])
    (tail : List E) (msgs : List (E × E)) (rest : List (Event E Q R K))
    (hv : tape v = levelTape l ++ (tailTape tail msgs ++ rest))
    (hit : iter.start.val < iter.end.val) (hiend : iter.end = alloc.vec.Vec.len config.level_ks)
    (hlast : iter.start.val + 1 = config.level_ks.val.length)
    (hfl : l.folds.length = (config.level_ks.val[iter.start.val]'(by omega)).val)
    (hkn : l.folds.length ≤ n.val) (hys : ys.length = 2 ^ (n.val - l.folds.length))
    (hgl : config.level_ks.val.length < config.grinding_bits.val.length)
    (hql : config.level_ks.val.length < config.queries.val.length)
    (hg : config.grinding_bits.val[config.level_ks.val.length] ≤ U32.max)
    (hcount : l.queries.length = (config.queries.val[config.level_ks.val.length]).val)
    (hrows : l.rows.length = l.queries.length) (hne : l.rows ≠ [])
    (hwidth : ∀ r ∈ l.rows, r.length = 3 * 2 ^ l.folds.length)
    (htail : tail.length = n.val - l.folds.length) (hmsgs : msgs.length + 1 = tail.length)
    (hk : config.initial_k.val ≤ w.ris.val.length + l.folds.length + tail.length)
    (hcap : w.ris.val.length + l.folds.length + tail.length + 1 ≤ Usize.max)
    (hcapo : w.oods.val.length < Usize.max) (hcapl : w.levels.val.length < Usize.max)
    (ch : Protocol.Challenges) (pf : Protocol.Opening) (hch : ch.tail = (tail.map encode).toArray)
    (hpf : pf.tailMessages = (msgs.map fun m => (⟨encode m.1, encode m.2⟩ : Protocol.Message Concrete.E)).toArray)
    (j : Nat) (hj : j ≠ 0) :
    ∃ r v', whir.verify.WhirReplay.run_loop1.body inst W config weight_at iter v w n oracle =
        .ok (.done (r, v')) ∧
      let sF := queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n j
        (l.chal encode) (l.prf encode encodeK ofLimbs false) (l.queries.map index).toArray
        (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs false)
          (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st))
      (r = .Ok () ↔ (closeTail ch pf sF).claim =
        sourceTerminal (callerAt (rotatePoint config.initial_k.val (sF.source.ris ++ tail.map encode).toArray))
          sF.source.saved sF.source.ris (tail.map encode) (ys.map encode).toArray) := by
  have hlk := config.level_ks.property
  have hi1 := succ_val iter.start config.level_ks.val.length (by omega) (by omega)
  obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some iter hit
  set k := config.level_ks.val[iter.start.val]'(by omega) with hkdef
  have hidx : Slice.index_usize (alloc.vec.Vec.deref config.level_ks) iter.start = .ok k := by
    rw [slice_index _ _ (by simp only [alloc.vec.Vec.deref, Slice.from_val]; omega)]
    simp [alloc.vec.Vec.deref, hkdef]
  have hnk : ¬ (n.val < k.val) := by omega
  obtain ⟨rs, w1, v1, hfold, hv1, ers, eris1, elev1, eoods1, hrel1, hn1⟩ :=
    fold_rounds_eq inst encode const index tape h ht hclone w st hrel v k l.folds _ hfl
      (by rw [hv, levelTape, List.append_assoc]) (by omega)
  have hsub : (Std.Usize.wrapping_sub n k).val = n.val - k.val := Fold.sub_val _ _ (by omega)
  obtain ⟨n1, hn1e⟩ : ∃ n1, Std.Usize.wrapping_sub n k = n1 := ⟨_, rfl⟩
  rw [hn1e] at hsub
  have heq1 : Std.Usize.wrapping_add iter.start 1#usize = alloc.vec.Vec.len config.level_ks :=
    UScalar.eq_of_val_eq (by rw [hi1, alloc.vec.Vec.len_val]; simpa using hlast)
  have hv1' : tape v1 = [.scalars ys, .grind, .queries l.queries, .sample l.lambda, .rows l.rows,
      .poly l.intro.1 l.intro.2] ++ (tailTape tail msgs ++ rest) := by
    rw [hv1, hhead, hoods]; simp [headTape, oodTape, batchTape]
  have hlen : (alloc.vec.Vec.len config.level_ks).val = config.level_ks.val.length := by simp
  have hfits1 := ModelFits.ofFold encode l.folds st hfits (by omega)
  have hrsl : (alloc.vec.Vec.deref rs).val.length = l.folds.length := by simp [alloc.vec.Vec.deref, ers]
  obtain ⟨r, v', wF, hll, hrelF, hrisF, hiff⟩ := last_level_eq inst encode const encodeK ofLimbs index tape hw h hr hn
    ht hclone hens W weight_at callerAt hcall config oracle (alloc.vec.Vec.deref rs) w1 (foldModel encode l.folds st)
    hrel1 hfits1 v1 n1 (by rw [hn1, hst, hsub]) (by omega) ys l.queries l.lambda l.rows l.intro.1 l.intro.2
    tail msgs rest hv1' (by rw [hys, hsub, hfl]) (by rw [hlen]; exact hgl) (by rw [hlen]; exact hql)
    (by simp only [hlen]; exact hg) (by simp only [hlen]; exact hcount) hrows hne
    (fun r hr' => by rw [hwidth r hr', hrsl]) (by omega) (by rw [htail, hsub, hfl])
    hmsgs (by rw [eris1, ers]; simp; omega) (by rw [eris1, ers]; simp; omega) (by rw [eoods1]; exact hcapo)
    (by rw [elev1]; exact hcapl) ch pf hch hpf
  refine ⟨r, v', ?_, ?_⟩
  · simp [whir.verify.WhirReplay.run_loop1.body, hnext, whir.config.Config.impl.level_ks, hidx, hnk, hfold,
      core.result.Result.Insts.CoreOpsTry.branch, lift, whir.config.Config.level_steps, heq1, hn1e, hll]
  · intro sF
    have hsF : sF = lastState encode encodeK ofLimbs index (foldModel encode l.folds st) n1.val l.queries l.lambda
        l.rows (alloc.vec.Vec.deref rs).val l.intro.1 l.intro.2 := by
      simp only [sF]
      rw [last_model_eq encode encodeK ofLimbs index l st j hj hoods, hn1, hst, hsub]
      simp [alloc.vec.Vec.deref, ers]
    rw [hsF, hiff, terminal_link encode index wF _ hrelF callerAt config.initial_k.val ys tail, eq_comm]

end Mid

/-! ## A script level in the model's checked replay -/

section ScriptLevel
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {R K Q E : Type} (encode : E → Concrete.E) (encodeK : K → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E) (index : Q → Nat)

theorem residual_last (s : Script E Q R K) (hl : 0 < s.levels.length) (ys : List E)
    (hys : (s.levels[s.levels.length - 1]'(by omega)).head = .inr ys) :
    (s.prf encode encodeK ofLimbs).residual = (ys.map encode).toArray := by
  have : s.levels.getLast? = some (s.levels[s.levels.length - 1]'(by omega)) := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem]
  simp [Script.prf, this, hys, residualOf]

/-- A later level of a valid script passes the model's level check and returns the
level's query batch. -/
theorem script_level_ok (c : Protocol.Config) (s : Script E Q R K) (lanes : Nat)
    (hch : (s.chal encode).valid c = true) (hS : ScriptShape index c s lanes) (init st : State) (j : Nat)
    (hj : j < c.folds.size) (hj0 : j ≠ 0)
    (hrun : Protocol.runChecked (verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs)) j 0 init = .ok st)
    (hst : st.n = WHIRNativeGuards.before c j) :
    let l := s.levels[j]'(by rw [hS.len]; exact hj)
    Protocol.runChecked (verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs)) (j + 1) 0 init =
      .ok (queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n j (l.chal encode)
        (l.prf encode encodeK ofLimbs false) (l.queries.map index).toArray
        (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs false)
          (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st))) := by
  intro l
  have hjl : j < s.levels.length := by rw [hS.len]; exact hj
  obtain ⟨hfl, hol, hoz, qsA, hqA, eqA, hql⟩ := level_facts encode index c s lanes hch hS j hj
  have hcv := WHIRNativeGuards.challenges_config c _ hch
  have hstep := WHIRNativeGuards.before_step c j hj
  have hfb : (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n =
      CausalGame.remaining c j := by
    rw [foldBlock_level, foldModel_n, hst, ← hstep, hfl]
  have hqs : qsA = (l.queries.map index).toArray := by
    rw [← eqA]
  have hc : (s.chal encode).levels[j]! = l.chal encode := chal_get encode s j hjl
  have hp : (s.prf encode encodeK ofLimbs).levels[j]! = l.prf encode encodeK ofLimbs false := by
    have h0 : (j == 0) = false := by simpa using hj0
    rw [prf_get encode encodeK ofLimbs s j hjl, h0]
  rw [runChecked_last, hrun]
  show verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs) (0 + j) st = _
  rw [Nat.zero_add]
  have hok := verifyLevel_ok c (s.chal encode) (s.prf encode encodeK ofLimbs) j st qsA
    (by rw [hc, hp]; simp [SLevel.prf, SLevel.chal])
    (by rw [hc, hp]; simp [SLevel.prf, SLevel.chal])
    (by
      rw [hc, hp]
      by_cases hm : j + 1 < c.folds.size
      · rw [if_pos hm]
        obtain ⟨r, hr⟩ := hS.head j (by rw [hS.len]; exact hm)
        simp [SLevel.prf, l, hr]
      · rw [if_neg hm]
        have hjL : j = s.levels.length - 1 := by rw [hS.len]; omega
        obtain ⟨ys, hys, hyl⟩ := hS.last (by omega)
        have hl : l = s.levels[s.levels.length - 1]'(by omega) := by simp only [l, hjL]
        refine ⟨by simp [SLevel.prf, hl, hys], ?_⟩
        rw [residual_last encode encodeK ofLimbs s (by omega) ys hys, hfb]
        simp [hyl, show c.folds.size - 1 = j by omega])
    (by rw [hc, hp, hfb]; simpa [SLevel.chal] using hqA)
    (by rw [hp, hqs]; simp [SLevel.prf, l, hS.rows j hjl])
  rw [hc, hp, hqs] at hok
  exact hok

end ScriptLevel

end WhirAeneas.Replay
