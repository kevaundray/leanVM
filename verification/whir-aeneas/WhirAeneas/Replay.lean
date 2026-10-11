import WhirAeneas.Query

namespace WhirAeneas.Replay
open Aeneas Aeneas.Std ReplaySource Whir Whir.Concrete WhirAeneas.Fold WhirAeneas.Query

theorem range_next_some (r : core.ops.range.Range Usize) (h : r.start.val < r.end.val) :
    ∃ r', core.iter.range.IteratorRange.next core.iter.range.StepUsize r = .ok (some r.start, r') ∧
      r'.start.val = r.start.val + 1 ∧ r'.end = r.end := by
  have hl : core.cmp.impls.PartialOrdUsize.lt r.start r.end = true := by
    simp [core.cmp.impls.PartialOrdUsize.lt, h]
  have hm : r.start.val < UScalar.max .Usize := by scalar_tac
  simp only [core.iter.range.IteratorRange.next, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked, bind_tc_ok]
  simp only [hl, ↓reduceIte]
  simp [hm, UScalar.ofNatCore_val_eq]

theorem range_next_none (r : core.ops.range.Range Usize) (h : r.end.val ≤ r.start.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r = .ok (none, r) := by
  have hl : core.cmp.impls.PartialOrdUsize.lt r.start r.end = false := by
    simp [core.cmp.impls.PartialOrdUsize.lt]; omega
  simp only [core.iter.range.IteratorRange.next, core.iter.range.UScalarStep]
  simp [hl]

theorem list_clone_id {α : Type} (c : α → Result α) (hc : ∀ x, c x = .ok x) (l : List α) :
    List.clone c l = .ok ⟨l, rfl⟩ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.clone, List.mapM_with_length] at ih ⊢
    simp only [ih, hc, bind_tc_ok]
    rfl

theorem extend_ok {α : Type} (c : core.clone.Clone α) (hc : ∀ x, c.clone x = .ok x)
    (v : alloc.vec.Vec α) (s : Slice α) (h : v.val.length + s.val.length ≤ Usize.max) :
    ∃ w, alloc.vec.Vec.extend_from_slice c v s = .ok w ∧ w.val = v.val ++ s.val := by
  have h' : v.length + s.length ≤ Usize.max := by simpa using h
  simp only [alloc.vec.Vec.extend_from_slice, h', ↓reduceDIte, list_clone_id c.clone hc, bind_tc_ok]
  exact ⟨_, rfl, alloc.vec.Vec.from_val _ _⟩

theorem to_vec_ok {α : Type} (c : core.clone.Clone α) (hc : ∀ x, c.clone x = .ok x) (s : Slice α) :
    ∃ w, alloc.slice.Slice.to_vec c s = .ok w ∧ w.val = s.val := by
  simp only [alloc.slice.Slice.to_vec, Slice.clone, list_clone_id c.clone hc, bind_tc_ok]
  exact ⟨_, rfl, by simp [alloc.vec.Vec.val]⟩

theorem clone_vec_ok {α : Type} (c : core.clone.Clone α) (hc : ∀ x, c.clone x = .ok x)
    (v : alloc.vec.Vec α) : ∃ w, alloc.vec.CloneVec.clone c v = .ok w ∧ w.val = v.val := by
  simp only [alloc.vec.CloneVec.clone, Slice.clone, list_clone_id c.clone hc, bind_tc_ok]
  exact ⟨_, rfl, by simp⟩

theorem vec_index_usize {α : Type} (v : alloc.vec.Vec α) (i : Usize) (hi : i.val < v.val.length) :
    v.index_usize i = .ok v.val[i.val] := by
  simp [alloc.vec.Vec.index_usize, hi]

theorem slice_range {α : Type} (s : Slice α) (a b : Usize) (hab : a.val ≤ b.val)
    (hb : b.val ≤ s.val.length) :
    ∃ t, core.slice.index.SliceIndexRangeUsizeSlice.index { start := a, «end» := b } s = .ok t ∧
      t.val = (s.val.drop a.val).take (b.val - a.val) := by
  have h : a ≤ b ∧ b ≤ s.length := ⟨by scalar_tac, by simpa using hb⟩
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, h, and_self, ↓reduceIte]
  exact ⟨_, rfl, by simp [List.slice]⟩

/-! ## The transcript interface

`tape v` is what the opening verifier in state `v` answers next, as source values, in the
replay's read order. The interface assumes nothing about how the answers are produced
(proof bytes, Fiat-Shamir duplex, proof of work, Merkle authentication); those are
separate contracts of the concrete verifier. -/

inductive Event (E Q R K : Type) where
  | sample (e : E)
  | sampleVec (zs : List E)
  | scalar (y : E)
  | scalars (ys : List E)
  | poly (u0 u2 : E)
  | root (r : R)
  | grind
  | queries (qs : List Q)
  | rows (ws : List (List K))

/-- Each read returns the tape's next answer and leaves the rest; a round polynomial is
its two transmitted coefficients with the linear one fixed by the claim; scopes change
nothing. -/
structure Transcript {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
    (encode : E → Concrete.E) (tape : V → List (Event E Q R K)) : Prop where
  sample : ∀ v e rest, tape v = .sample e :: rest →
    ∃ v', inst.fiat_shamirarithVerifierInst.sample v = .ok (e, v') ∧ tape v' = rest
  sample_vec : ∀ v (n : Usize) zs rest, tape v = .sampleVec zs :: rest → zs.length = n.val →
    ∃ w v', inst.fiat_shamirarithVerifierInst.sample_vec v n = .ok (w, v') ∧ w.val = zs ∧
      tape v' = rest
  scalar : ∀ v y rest, tape v = .scalar y :: rest →
    ∃ v', inst.fiat_shamirarithVerifierInst.next_scalar v = .ok (.Ok y, v') ∧ tape v' = rest
  scalars : ∀ v (n : Usize) ys rest, tape v = .scalars ys :: rest → ys.length = n.val →
    ∃ w v', inst.fiat_shamirarithVerifierInst.next_scalars v n = .ok (.Ok w, v') ∧ w.val = ys ∧
      tape v' = rest
  poly : ∀ v claim u0 u2 rest, tape v = .poly u0 u2 :: rest →
    ∃ h b v', inst.fiat_shamirarithVerifierInst.next_round_poly v 3#usize claim none = .ok (.Ok h, v') ∧
      h.val = [u0, b, u2] ∧ encode b = encode claim + encode u2 ∧ tape v' = rest
  root : ∀ v r rest, tape v = .root r :: rest →
    ∃ v', inst.next_root v = .ok (.Ok r, v') ∧ tape v' = rest
  grind : ∀ v bits rest, tape v = .grind :: rest →
    ∃ v', inst.fiat_shamirarithVerifierInst.grind_check v bits = .ok (.Ok (), v') ∧ tape v' = rest
  queries : ∀ v depth (count : Usize) qs rest, tape v = .queries qs :: rest → qs.length = count.val →
    ∃ w v', inst.sample_queries v depth count = .ok (w, v') ∧ w.val = qs ∧ tape v' = rest
  rows : ∀ v root depth queries a b ws rest, tape v = .rows ws :: rest →
    ∃ w v', inst.open_rows v root depth queries a b = .ok (.Ok w, v') ∧
      w.val.map (·.val) = ws ∧ tape v' = rest
  begin_scope : ∀ v stage, inst.fiat_shamirarithVerifierInst.begin_scope v stage = .ok v
  end_scope : ∀ v, inst.fiat_shamirarithVerifierInst.end_scope v = .ok v

section Steps
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E) (index : Q → Nat)
  (tape : V → List (Event E Q R K))

/-- `Quad::recv` reads the next round polynomial: the transmitted `u0` and `u2`, with the
linear coefficient `claim + u2`. -/
theorem recv_eq (ht : Transcript inst encode tape) (copy : core.marker.Copy E) (v : V)
    (claim u0 u2 : E) (rest : List (Event E Q R K)) (hv : tape v = .poly u0 u2 :: rest) :
    ∃ q v', whir.verify.Quad.recv copy inst v claim = .ok (.Ok q, v') ∧ q.c = u0 ∧ q.a = u2 ∧
      encode q.b = encode claim + encode u2 ∧ tape v' = rest := by
  obtain ⟨h, b, v', hpoly, hh, hb, hrest⟩ := ht.poly v claim u0 u2 rest hv
  have h0 : (0#usize).val < h.val.length := by simp [hh]
  have h1 : (1#usize).val < h.val.length := by simp [hh]
  have h2 : (2#usize).val < h.val.length := by simp [hh]
  refine ⟨{ c := u0, b := b, a := u2 }, v', ?_, rfl, rfl, hb, hrest⟩
  simp only [whir.verify.Quad.recv, hpoly, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  simp [alloc.vec.Vec.index_usize, hh]

/-- The tape of fold rounds: each samples its challenge, then reads its polynomial. -/
def foldTape (rounds : List (E × E × E)) : List (Event E Q R K) :=
  rounds.flatMap fun (r, u0, u2) => [.sample r, .poly u0 u2]

/-- The model's fold rounds over the interpreted challenges and messages. -/
def foldModel (rounds : List (E × E × E)) (st : State) : State :=
  rounds.foldl (fun s (r, u0, u2) => foldScalar s (encode r) ⟨encode u0, encode u2⟩) st

theorem fold_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x) :
    ∀ (rounds : List (E × E × E)) (iter : core.ops.range.Range Std.Usize)
      (self : whir.verify.WhirReplay V R K Q E) (v : V) (rs : alloc.vec.Vec E) (st : State)
      (rest : List (Event E Q R K)),
      iter.start.val + rounds.length = iter.end.val →
      tape v = foldTape rounds ++ rest →
      encode self.t_r = st.claim →
      (⟨encode self.quad.c, encode self.quad.a⟩ : Protocol.Message Concrete.E) = st.message →
      encode self.quad.b = st.claim + encode self.quad.a →
      (self.ris.val ++ rs.val).map encode = st.source.ris →
      self.ris.val.length + rs.val.length + rounds.length ≤ Usize.max →
      ∃ rs' t' q' ris' v',
        whir.verify.WhirReplay.fold_rounds_loop inst iter self v rs =
          .ok (.Ok rs', t', q', ris', self.levels, self.oods, v') ∧
        tape v' = rest ∧ rs'.val = rs.val ++ rounds.map (·.1) ∧ ris'.val = self.ris.val ++ rs'.val ∧
        encode t' = (foldModel encode rounds st).claim ∧
        (⟨encode q'.c, encode q'.a⟩ : Protocol.Message Concrete.E) = (foldModel encode rounds st).message ∧
        encode q'.b = (foldModel encode rounds st).claim + encode q'.a ∧
        ris'.val.map encode = (foldModel encode rounds st).source.ris ∧
        (foldModel encode rounds st).source.saved = st.source.saved ∧
        (foldModel encode rounds st).n = st.n - rounds.length := by
  intro rounds
  induction rounds with
  | nil =>
    intro iter self v rs st rest hlen hv hc hm hb hris hcap
    obtain ⟨w, hw, ew⟩ := extend_ok _ hclone self.ris (alloc.vec.Vec.deref rs)
      (by simp [alloc.vec.Vec.deref]; simp at hcap; omega)
    refine ⟨rs, self.t_r, self.quad, w, v, ?_, by simpa [foldTape] using hv, by simp,
      by rw [ew]; simp [alloc.vec.Vec.deref], hc, hm, hb,
      by rw [ew]; simpa [alloc.vec.Vec.deref, foldModel] using hris,
      rfl, by simp [foldModel]⟩
    unfold whir.verify.WhirReplay.fold_rounds_loop
    apply loop_done
    simp [whir.verify.WhirReplay.fold_rounds_loop.body, range_next_none iter (by simp at hlen; omega), hw]
  | cons rd rounds ih =>
    intro iter self v rs st rest hlen hv hc hm hb hris hcap
    obtain ⟨r, u0, u2⟩ := rd
    obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some iter (by simp at hlen; omega)
    obtain ⟨v1, hsample, hv1⟩ := ht.sample v r (.poly u0 u2 :: (foldTape rounds ++ rest))
      (by simp [hv, foldTape])
    obtain ⟨t, het, et⟩ := quad_eval inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst inst
      encode const h self.quad v1 r st.claim hb
    obtain ⟨q, v3, hrecv, hqc, hqa, hqb, hv3⟩ := recv_eq inst encode tape ht
      inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v1 t u0 u2
      (foldTape rounds ++ rest) (by rw [hv1])
    obtain ⟨rs1, hpush, ers1⟩ := push_ok rs r (by simp at hcap; omega)
    have hbody : whir.verify.WhirReplay.fold_rounds_loop.body inst iter self v rs =
        .ok (.cont (iter1, { self with t_r := t, quad := q }, v3, rs1)) := by
      simp [whir.verify.WhirReplay.fold_rounds_loop.body, hnext, hsample, het, hrecv,
        core.result.Result.Insts.CoreOpsTry.branch, hpush]
    let st1 := foldScalar st (encode r) ⟨encode u0, encode u2⟩
    obtain ⟨rs', t', q', ris', v', hloop, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ :=
      ih iter1 { self with t_r := t, quad := q } v3 rs1 st1 rest
        (by simp at hlen; rw [hs1, he1]; omega) hv3
        (by rw [et, hm]; rfl)
        (by simp only [st1, foldScalar, hqc, hqa])
        (by rw [hqb, hqa, et, hm]; rfl)
        (by simp only [ers1, st1, foldScalar, SourceState.step, ← hris]; simp)
        (by simp only [ers1]; simp at hcap ⊢; omega)
    refine ⟨rs', t', q', ris', v', ?_, e1, by rw [e2, ers1]; simp, e3, e4, e5, e6, e7, e8, ?_⟩
    · unfold whir.verify.WhirReplay.fold_rounds_loop
      rw [loop_cont hbody]
      unfold whir.verify.WhirReplay.fold_rounds_loop at hloop
      exact hloop
    · change (foldModel encode rounds st1).n = _
      rw [e9]; simp only [st1, foldScalar, List.length_cons]; omega

/-- `fold_rounds` reads `k` rounds, folds the running claim and quadratic exactly as the
model's `foldScalar`, and appends the challenges to the transcript's fold point. -/
theorem fold_rounds_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (self : whir.verify.WhirReplay V R K Q E) (st : State) (hrel : StateRel encode index self st)
    (v : V) (k : Usize) (rounds : List (E × E × E)) (rest : List (Event E Q R K))
    (hk : rounds.length = k.val) (hv : tape v = foldTape rounds ++ rest)
    (hcap : self.ris.val.length + rounds.length ≤ Usize.max) :
    ∃ rs self' v', whir.verify.WhirReplay.fold_rounds inst self v k = .ok (.Ok rs, self', v') ∧
      tape v' = rest ∧ rs.val = rounds.map (·.1) ∧ self'.ris.val = self.ris.val ++ rs.val ∧
      self'.levels = self.levels ∧ self'.oods = self.oods ∧
      StateRel encode index self' (foldModel encode rounds st) ∧
      (foldModel encode rounds st).n = st.n - k.val := by
  obtain ⟨rs', t', q', ris', v', hloop, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ :=
    fold_loop_eq inst encode const tape h ht hclone rounds { start := 0#usize, «end» := k } self v
      (alloc.vec.Vec.with_capacity E k) st rest (by simp [hk]) hv hrel.claim hrel.message hrel.linear
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, ← hrel.ris])
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; omega)
  refine ⟨rs', { t_r := t', quad := q', ris := ris', levels := self.levels, oods := self.oods }, v', ?_,
    e1, by simpa [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using e2, e3, rfl, rfl,
    ⟨e4, e5, e6, e7, by simpa [e8] using hrel.oods, by simpa [e8] using hrel.levels⟩, by rw [e9, hk]⟩
  simp [whir.verify.WhirReplay.fold_rounds, hloop]

/-- The tape of a level's out-of-domain claims: each point, its value, its intro round. -/
def oodTape (oods : List (List E × E × E × E)) : List (Event E Q R K) :=
  oods.flatMap fun (z, y, u0, u2) => [.sampleVec z, .scalar y, .poly u0 u2]

/-- A replayed out-of-domain claim is the tape's, with the intro's linear coefficient
fixed by the claimed value. -/
def OodIs (o : whir.verify.Ood E) (d : List E × E × E × E) : Prop :=
  o.z.val = d.1 ∧ o.y = d.2.1 ∧ o.intro.c = d.2.2.1 ∧ o.intro.a = d.2.2.2 ∧
    encode o.intro.b = encode d.2.1 + encode d.2.2.2

theorem ood_replay_eq (ht : Transcript inst encode tape) (copy : core.marker.Copy E) (v : V)
    (n : Usize) (z : List E) (y u0 u2 : E) (rest : List (Event E Q R K)) (hz : z.length = n.val)
    (hv : tape v = .sampleVec z :: .scalar y :: .poly u0 u2 :: rest) :
    ∃ o v', whir.verify.Ood.replay copy inst v n = .ok (.Ok o, v') ∧ OodIs encode o (z, y, u0, u2) ∧
      tape v' = rest := by
  obtain ⟨w, v1, h1, ew, hv1⟩ := ht.sample_vec v n z _ hv hz
  obtain ⟨v2, h2, hv2⟩ := ht.scalar v1 y _ hv1
  obtain ⟨q, v3, h3, hqc, hqa, hqb, hv3⟩ := recv_eq inst encode tape ht copy v2 y u0 u2 rest hv2
  refine ⟨{ z := w, y := y, intro := q }, v3, ?_, ⟨ew, rfl, hqc, hqa, by rw [hqb, ← hqa]⟩, hv3⟩
  simp [whir.verify.Ood.replay, h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch]

theorem replay_all_loop_eq (ht : Transcript inst encode tape) (copy : core.marker.Copy E)
    (count n : Usize) :
    ∀ (l : List (List E × E × E × E)) (i : Usize) (oods : alloc.vec.Vec (whir.verify.Ood E)) (v : V)
      (rest : List (Event E Q R K)),
      i.val + l.length = count.val → (∀ d ∈ l, d.1.length = n.val) → tape v = oodTape l ++ rest →
      oods.val.length + l.length ≤ Usize.max →
      ∃ w v', whir.verify.Ood.replay_all_loop copy inst v count n oods i = .ok (.Ok w, v') ∧
        tape v' = rest ∧ ∃ ws, w.val = oods.val ++ ws ∧ List.Forall₂ (OodIs encode) ws l := by
  intro l
  induction l with
  | nil =>
    intro i oods v rest hi _ hv _
    refine ⟨oods, v, ?_, by simpa [oodTape] using hv, [], by simp, List.Forall₂.nil⟩
    unfold whir.verify.Ood.replay_all_loop
    apply loop_done
    have : ¬ (i < count) := by simp at hi; scalar_tac
    simp [whir.verify.Ood.replay_all_loop.body, this]
  | cons d l ih =>
    intro i oods v rest hi hz hv hcap
    obtain ⟨z, y, u0, u2⟩ := d
    obtain ⟨o, v1, h1, eo, hv1⟩ := ood_replay_eq inst encode tape ht copy v n z y u0 u2
      (oodTape l ++ rest) (hz (z, y, u0, u2) (by simp)) (by simp [hv, oodTape])
    obtain ⟨oods1, hpush, eoods1⟩ := push_ok oods o (by simp at hcap; omega)
    have hlt : i.val < count.val := by simp at hi; omega
    have hsucc := succ_val i count.val hlt (by scalar_tac)
    have hbody : whir.verify.Ood.replay_all_loop.body copy inst count n v oods i =
        .ok (.cont (v1, oods1, Std.Usize.wrapping_add i 1#usize)) := by
      have : i < count := by scalar_tac
      simp [whir.verify.Ood.replay_all_loop.body, this, h1, hpush,
        core.result.Result.Insts.CoreOpsTry.branch, lift]
    obtain ⟨w, v', hloop, hv', ws, ew, hws⟩ := ih (Std.Usize.wrapping_add i 1#usize) oods1 v1 rest
      (by rw [hsucc]; simp at hi; omega) (fun d hd => hz d (by simp [hd])) hv1
      (by rw [eoods1]; simp at hcap ⊢; omega)
    refine ⟨w, v', ?_, hv', o :: ws, by rw [ew, eoods1]; simp, List.Forall₂.cons eo hws⟩
    unfold whir.verify.Ood.replay_all_loop
    rw [loop_cont hbody]
    unfold whir.verify.Ood.replay_all_loop at hloop
    exact hloop

theorem replay_all_eq (ht : Transcript inst encode tape) (copy : core.marker.Copy E)
    (v : V) (count n : Usize) (l : List (List E × E × E × E)) (rest : List (Event E Q R K))
    (hl : l.length = count.val) (hz : ∀ d ∈ l, d.1.length = n.val) (hv : tape v = oodTape l ++ rest) :
    ∃ w v', whir.verify.Ood.replay_all copy inst v count n = .ok (.Ok w, v') ∧ tape v' = rest ∧
      List.Forall₂ (OodIs encode) w.val l := by
  obtain ⟨w, v', hloop, hv', ws, ew, hws⟩ := replay_all_loop_eq inst encode tape ht copy count n l
    0#usize (alloc.vec.Vec.new _) v rest (by simp [hl]) hz hv (by simp [alloc.vec.Vec.new]; scalar_tac)
  refine ⟨w, v', hloop, hv', ?_⟩
  simpa [ew, alloc.vec.Vec.new] using hws

/-- `begin_query` checks grinding, reads the batch's queries, draws its challenge and
takes the challenge's powers as the query weights. -/
theorem begin_query_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape) (v : V) (phase : whir.verify.QueryPhase) (qs : List Q) (lam : E)
    (rest : List (Event E Q R K)) (hq : qs.length = phase.count.val)
    (hv : tape v = .grind :: .queries qs :: .sample lam :: rest) :
    ∃ b v', whir.verify.WhirReplay.begin_query inst v phase = .ok (.Ok b, v') ∧ tape v' = rest ∧
      b.queries.val = qs ∧ b.lambda = lam ∧
      b.weights.val.map encode = (Concrete.powers (encode lam) qs.length).toList := by
  obtain ⟨v1, h1, hv1⟩ := ht.grind v phase.grinding _ hv
  obtain ⟨w, v2, h2, ew, hv2⟩ := ht.queries v1 phase.depth phase.count qs _ hv1 hq
  obtain ⟨v3, h3, hv3⟩ := ht.sample v2 lam _ hv2
  obtain ⟨ws, h4, ews⟩ := h.powers v3 lam phase.count
  refine ⟨{ queries := w, weights := ws, lambda := lam }, v3, ?_, hv3, ew, rfl, by rw [ews, hq]⟩
  simp [whir.verify.WhirReplay.begin_query, h1, h2, h3, h4, whir.verify.QueryPhase.sample,
    core.result.Result.Insts.CoreOpsTry.branch, ht.begin_scope]

end Steps

/-! ## Opened rows of elements -/

section Rows
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (encodeK : K → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E) (index : Q → Nat)
  (tape : V → List (Event E Q R K))

/-- A row of words read as elements, three limbs each, lowest first. -/
def eRow (ws : List K) : List Concrete.E :=
  (List.range (ws.length / 3)).map fun i =>
    ofLimbs (ws.map encodeK)[3 * i]! (ws.map encodeK)[3 * i + 1]! (ws.map encodeK)[3 * i + 2]!

theorem e_row_loop_eq (hr : RowModel inst encode encodeK ofLimbs index) (words : Slice K) (n : Usize)
    (hn : 3 * n.val ≤ words.val.length) :
    ∀ (m : Nat) (i : Usize) (row : alloc.vec.Vec E) (v : V), n.val - i.val = m → i.val ≤ n.val →
      row.val.map encode = (List.range i.val).map (fun j =>
        ofLimbs (words.val.map encodeK)[3 * j]! (words.val.map encodeK)[3 * j + 1]!
          (words.val.map encodeK)[3 * j + 2]!) →
      ∃ row', whir.verify.e_row_loop inst v words n row i = .ok (row', v) ∧
        row'.val.map encode = (List.range n.val).map (fun j =>
          ofLimbs (words.val.map encodeK)[3 * j]! (words.val.map encodeK)[3 * j + 1]!
            (words.val.map encodeK)[3 * j + 2]!) := by
  intro m
  induction m with
  | zero =>
    intro i row v hm hi hrow
    refine ⟨row, ?_, by rw [show n.val = i.val by omega]; exact hrow⟩
    unfold whir.verify.e_row_loop
    apply loop_done
    have : ¬ (i < n) := by scalar_tac
    simp [whir.verify.e_row_loop.body, this]
  | succ m ih =>
    intro i row v hm hi hrow
    have hin : i.val < n.val := by omega
    have hat : (Std.Usize.wrapping_mul 3#usize i).val = 3 * i.val := by
      rw [Std.Usize.wrapping_mul_val_eq]
      apply Nat.mod_eq_of_lt
      have := words.property
      have := Usize.max_def
      simp only [UScalar.size] at *
      scalar_tac
    have h1 : (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 3#usize i) 1#usize).val = 3 * i.val + 1 := by
      rw [succ_val _ words.val.length (by rw [hat]; omega) (by have := words.property; scalar_tac), hat]
    have h2 : (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 3#usize i) 2#usize).val = 3 * i.val + 2 := by
      rw [Std.Usize.wrapping_add_val_eq, hat]
      apply Nat.mod_eq_of_lt
      have := words.property
      have := Usize.max_def
      simp only [UScalar.size] at *
      scalar_tac
    have i0 : 3 * i.val < words.val.length := by omega
    have i1 : 3 * i.val + 1 < words.val.length := by omega
    have i2 : 3 * i.val + 2 < words.val.length := by omega
    obtain ⟨y, hy, ey⟩ := hr.e_of_limbs v (Array.make 3#usize [words.val[3 * i.val],
      words.val[3 * i.val + 1], words.val[3 * i.val + 2]]) _ _ _ rfl
    obtain ⟨row1, hpush, erow1⟩ := push_ok row y (by
      have : row.val.length = i.val := by simpa using congrArg List.length hrow
      have := words.property
      scalar_tac)
    have hbody : whir.verify.e_row_loop.body inst words n v row i =
        .ok (.cont (v, row1, Std.Usize.wrapping_add i 1#usize)) := by
      have hlt : i < n := by scalar_tac
      simp only [whir.verify.e_row_loop.body, hlt, ↓reduceIte, lift, Std.bind_ok,
        slice_index words _ (by rw [hat]; omega), slice_index words _ (by rw [h1]; omega),
        slice_index words _ (by rw [h2]; omega)]
      simp only [hat, h1, h2]
      simp [hy, hpush]
    have hsucc := succ_val i n.val hin (by scalar_tac)
    obtain ⟨row', hloop, erow'⟩ := ih (Std.Usize.wrapping_add i 1#usize) row1 v (by omega) (by omega) (by
      rw [erow1, hsucc, List.range_succ]
      simp [hrow, ey, List.getElem?_eq_getElem i0, List.getElem?_eq_getElem i1,
        List.getElem?_eq_getElem i2])
    refine ⟨row', ?_, erow'⟩
    unfold whir.verify.e_row_loop
    rw [loop_cont hbody]
    unfold whir.verify.e_row_loop at hloop
    exact hloop

/-- `e_row` on a row of a multiple of three words is the row's elements. -/
theorem e_row_eq (hr : RowModel inst encode encodeK ofLimbs index) (copyK : core.marker.Copy K)
    (v : V) (words : Slice K) (h3 : words.val.length % 3 = 0) :
    ∃ row, whir.verify.e_row copyK inst v words = .ok (row, v) ∧
      row.val.map encode = eRow encodeK ofLimbs words.val := by
  have h3ne : ¬ ((3#usize : Usize).val = 0) := by simp
  simp only [whir.verify.e_row, core.num.Usize.div_ceil, h3ne, ↓reduceIte, Std.bind_ok]
  generalize hn : (⟨BitVec.ofNat _ (((Slice.len words).val + (3#usize : Usize).val - 1) /
    (3#usize : Usize).val)⟩ : Usize) = n
  have hd : n.val = words.val.length / 3 := by
    have := words.property
    have hl : (Slice.len words).bv.toNat = words.val.length := by
      exact Slice.len_val words
    rw [← hn]
    simp only [UScalar.val, BitVec.toNat_ofNat, hl]
    have h3v : (3#usize : Usize).val = 3 := by simp
    simp only [UScalar.val] at h3v
    rw [h3v, Nat.mod_eq_of_lt]
    · omega
    · have := Usize.max_def
      simp only [Usize.max, Usize.numBits] at *
      have : 0 < 2 ^ UScalarTy.Usize.numBits := by positivity
      omega
  obtain ⟨row, hloop, erow⟩ := e_row_loop_eq inst encode encodeK ofLimbs index hr words n
    (by rw [hd]; omega) _ 0#usize (alloc.vec.Vec.with_capacity E n) v rfl (by simp)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
  exact ⟨row, hloop, by rw [erow, hd]; rfl⟩

theorem open_e_rows_loop_eq (hr : RowModel inst encode encodeK ofLimbs index)
    (words : alloc.vec.Vec (alloc.vec.Vec K)) (h3 : ∀ w ∈ words.val, w.val.length % 3 = 0) :
    ∀ (m : Nat) (q : Usize) (rows : alloc.vec.Vec (alloc.vec.Vec E)) (v : V),
      words.val.length - q.val = m → q.val ≤ words.val.length →
      rows.val.map (fun r => r.val.map encode) = (words.val.take q.val).map (fun w => eRow encodeK ofLimbs w.val) →
      ∃ rows', whir.verify.Oracle.open_e_rows_loop inst v words rows q = .ok (v, rows') ∧
        rows'.val.map (fun r => r.val.map encode) = words.val.map (fun w => eRow encodeK ofLimbs w.val) := by
  intro m
  induction m with
  | zero =>
    intro q rows v hm hq hrows
    refine ⟨rows, ?_, by rw [hrows, show q.val = words.val.length by omega, List.take_length]⟩
    unfold whir.verify.Oracle.open_e_rows_loop
    apply loop_done
    have : ¬ (q < alloc.vec.Vec.len words) := by simp; omega
    simp [whir.verify.Oracle.open_e_rows_loop.body, this]
  | succ m ih =>
    intro q rows v hm hq hrows
    have hlt : q.val < words.val.length := by omega
    obtain ⟨row, hrow, erow⟩ := e_row_eq inst encode encodeK ofLimbs index hr inst.coremarkerCopyInst1 v
      (alloc.vec.Vec.deref words.val[q.val]) (by simpa [alloc.vec.Vec.deref] using h3 _ (List.getElem_mem hlt))
    obtain ⟨rows1, hpush, erows1⟩ := push_ok rows row (by
      have : rows.val.length = q.val := by
        simpa [List.length_take, show min q.val words.val.length = q.val by omega] using congrArg List.length hrows
      have := words.property
      scalar_tac)
    have hbody : whir.verify.Oracle.open_e_rows_loop.body inst words v rows q =
        .ok (.cont (v, rows1, Std.Usize.wrapping_add q 1#usize)) := by
      have : q < alloc.vec.Vec.len words := by simp; omega
      simp [whir.verify.Oracle.open_e_rows_loop.body, this, vec_index words q hlt, hrow, hpush, lift]
    have hsucc := succ_val q words.val.length hlt (by have := words.property; scalar_tac)
    obtain ⟨rows', hloop, erows'⟩ := ih (Std.Usize.wrapping_add q 1#usize) rows1 v (by omega) (by omega) (by
      rw [erows1, hsucc, List.map_append, hrows, List.take_succ_eq_append_getElem hlt, List.map_append]
      simp [erow, alloc.vec.Vec.deref])
    refine ⟨rows', ?_, erows'⟩
    unfold whir.verify.Oracle.open_e_rows_loop
    rw [loop_cont hbody]
    unfold whir.verify.Oracle.open_e_rows_loop at hloop
    exact hloop

/-- `open_e_rows` returns the transcript's opened rows, each read as elements. -/
theorem open_e_rows_eq (hr : RowModel inst encode encodeK ofLimbs index) (ht : Transcript inst encode tape)
    (oracle : whir.verify.Oracle R) (v : V) (queries : Slice Q) (ws : List (List K))
    (rest : List (Event E Q R K)) (h3 : ∀ w ∈ ws, w.length % 3 = 0) (hv : tape v = .rows ws :: rest) :
    ∃ rows v', whir.verify.Oracle.open_e_rows inst oracle v queries = .ok (.Ok rows, v') ∧ tape v' = rest ∧
      rows.val.map (fun r => r.val.map encode) = ws.map (eRow encodeK ofLimbs) := by
  obtain ⟨w, v1, h1, ew, hv1⟩ := ht.rows v oracle.root
    (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate) queries
    (Std.Usize.wrapping_shl 3#usize oracle.log_num_interleaved)
    (Std.Usize.wrapping_shl 3#usize oracle.log_num_interleaved) ws rest hv
  have h3' : ∀ x ∈ w.val, x.val.length % 3 = 0 := by
    intro x hx
    exact h3 _ (by rw [← ew]; exact List.mem_map_of_mem hx)
  obtain ⟨rows, hloop, erows⟩ := open_e_rows_loop_eq inst encode encodeK ofLimbs index hr w h3' _ 0#usize
    (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len w)) v1 rfl (by simp)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
  refine ⟨rows, v1, ?_, hv1, by rw [erows, ← ew]; simp⟩
  simp [whir.verify.Oracle.open_e_rows, whir.verify.Oracle.depth, h1, lift,
    core.result.Result.Insts.CoreOpsTry.branch, hloop]

end Rows

section Config
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)

theorem phase_eq (config : whir.config.Config) (level depth : Usize)
    (hl : level.val < config.grinding_bits.val.length) (hq : level.val < config.queries.val.length)
    (hg : config.grinding_bits.val[level.val] ≤ U32.max) :
    whir.verify.WhirReplay.phase inst config level depth =
      .ok (whir.verify.QueryPhase.mk (UScalar.cast .U32 config.grinding_bits.val[level.val]) depth
        config.queries.val[level.val]) := by
  simp only [whir.verify.WhirReplay.phase, whir.config.Config.impl.grinding_bits,
    whir.config.Config.impl.queries, Std.bind_ok]
  rw [slice_index _ level (by simpa [alloc.vec.Vec.deref] using hl)]
  simp only [Std.bind_ok, core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from,
    core.num.tryFromUScalar]
  simp only [alloc.vec.Vec.deref, Slice.from_val] at hg ⊢
  rw [if_pos (by simpa using hg)]
  simp only [Std.bind_ok]
  rw [slice_index _ level (by simpa using hq)]
  simp

theorem oracle_eq (config : whir.config.Config) (root : R) (level n : Usize)
    (hl : level.val < config.level_ks.val.length) (hk : config.level_ks.val[level.val] ≤ n.val)
    (hr : level.val + 1 < config.log_inv_rates.val.length) :
    ∃ o : whir.verify.Oracle R, whir.verify.WhirReplay.oracle inst config root level n = .ok (.Ok o) ∧
      o.root = root ∧ o.log_num_interleaved = config.level_ks.val[level.val] ∧
      o.log_msg_cols.val = n.val - (config.level_ks.val[level.val]).val ∧
      o.log_inv_rate = config.log_inv_rates.val[level.val + 1] := by
  have hspec := Usize.checked_sub_bv_spec n config.level_ks.val[level.val]
  cases hcs : Usize.checked_sub n config.level_ks.val[level.val] with
  | none => simp only [hcs] at hspec; omega
  | some z =>
    simp only [hcs] at hspec
    have hsucc := succ_val level config.log_inv_rates.val.length (by omega)
      (by have := config.log_inv_rates.property; scalar_tac)
    refine ⟨whir.verify.Oracle.mk root config.level_ks.val[level.val] z
      config.log_inv_rates.val[level.val + 1], ?_, rfl, rfl, hspec.2.1, rfl⟩
    simp only [whir.verify.WhirReplay.oracle, whir.config.Config.impl.level_ks,
      whir.config.Config.impl.log_inv_rates, Std.bind_ok]
    rw [slice_index _ level (by simpa [alloc.vec.Vec.deref] using hl)]
    simp only [Std.bind_ok, lift, alloc.vec.Vec.deref, Slice.from_val, hcs]
    simp only [core.option.Option.ok_or_some, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rw [slice_index _ _ (by simpa [hsucc] using hr)]
    simp [hsucc]

end Config

/-! ## A level's induced basis at the terminal point -/

/-- The normalizers' interpretation: `Normalizers::new n` holds the model's subspace roots
`s_k(v_k)` and their inverses (zero at zero), read as `F192` constants through `const`, and
`const` reads the constant one as one. -/
structure NormalizerModel (const : primitives.field.gf2_64x3.F192 → Concrete.E) : Prop where
  new : ∀ n : Usize, n.val < 64 → ∃ nz, whir.query.Normalizers.new n = .ok nz ∧
    n.val ≤ nz.at_roots.val.length ∧ n.val ≤ nz.inverses.val.length ∧
    (∀ i (hi : i < nz.at_roots.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from nz.at_roots.val[i] = .ok f →
        const f = Concrete.E.ofK (subspaceRoots n.val)[i]!) ∧
    (∀ i (hi : i < nz.inverses.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from nz.inverses.val[i] = .ok f →
        const f = Concrete.E.ofK (InducedTerminalRefinement.nativeInverse (subspaceRoots n.val)[i]!))
  one : const primitives.field.gf2_64x3.F192.ONE = 1

section Basis
variable {S E : Type} (copy : core.marker.Copy E) (A : fiat_shamir.arith.Arith S E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)

/-- The model's affine factors of a point, as a list. -/
def linList (n : Nat) (pt : List Concrete.E) (k : Nat) : List (Concrete.E × Concrete.E) :=
  (List.range k).map fun j =>
    (pt[j]! + 1, pt[j]! * Concrete.E.ofK (InducedTerminalRefinement.nativeInverse (subspaceRoots n)[j]!))

theorem affine_loop_eq (h : ArithModel A encode const) (hone : const primitives.field.gf2_64x3.F192.ONE = 1)
    (n : Nat) (point : Slice E) (inverses : Slice primitives.field.gf2_64.F64)
    (hlen : point.val.length ≤ inverses.val.length)
    (hinv : ∀ i (hi : i < inverses.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from inverses.val[i] = .ok f →
        const f = Concrete.E.ofK (InducedTerminalRefinement.nativeInverse (subspaceRoots n)[i]!)) :
    ∀ (m : Nat) (k : Usize) (lin : alloc.vec.Vec (E × E)) (a : S), point.val.length - k.val = m →
      k.val ≤ point.val.length →
      lin.val.map (fun p => (encode p.1, encode p.2)) = linList n (point.val.map encode) k.val →
      ∃ lin', whir.verify.affine_factors_loop A a point inverses lin k = .ok (lin', a) ∧
        lin'.val.map (fun p => (encode p.1, encode p.2)) =
          linList n (point.val.map encode) point.val.length := by
  intro m
  induction m with
  | zero =>
    intro k lin a hm hk hlin
    refine ⟨lin, ?_, by rw [hlin, show k.val = point.val.length by omega]⟩
    unfold whir.verify.affine_factors_loop
    apply loop_done
    have : ¬ (k < Slice.len point) := by simp; omega
    simp [whir.verify.affine_factors_loop.body, this]
  | succ m ih =>
    intro k lin a hm hk hlin
    have hkp : k.val < point.val.length := by omega
    have hki : k.val < inverses.val.length := by omega
    obtain ⟨one_plus, h1, e1⟩ := h.add_const a point.val[k.val] primitives.field.gf2_64x3.F192.ONE
    obtain ⟨c, h2, e2⟩ := h.mul_const a point.val[k.val]
      { c0 := inverses.val[k.val], c1 := 0#u64, c2 := 0#u64 }
    obtain ⟨lin1, hpush, elin1⟩ := push_ok lin (one_plus, c) (by
      have : lin.val.length = k.val := by simpa [linList] using congrArg List.length hlin
      have := point.property
      scalar_tac)
    have hbody : whir.verify.affine_factors_loop.body A point inverses a lin k =
        .ok (.cont (a, lin1, Std.Usize.wrapping_add k 1#usize)) := by
      have : k < Slice.len point := by simp; omega
      simp [whir.verify.affine_factors_loop.body, this, slice_index point k hkp,
        slice_index inverses k hki, h1, primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from, h2,
        hpush, lift]
    have hsucc := succ_val k point.val.length hkp (by have := point.property; scalar_tac)
    obtain ⟨lin', hloop, elin'⟩ := ih (Std.Usize.wrapping_add k 1#usize) lin1 a (by omega) (by omega) (by
      rw [elin1, hsucc, List.map_append, hlin]
      simp only [linList, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [e1, e2, hone, hinv k.val hki _ rfl, map_getElem! _ _ _ hkp])
    refine ⟨lin', ?_, elin'⟩
    unfold whir.verify.affine_factors_loop
    rw [loop_cont hbody]
    unfold whir.verify.affine_factors_loop at hloop
    exact hloop

theorem linList_eq (n : Nat) (pt : List Concrete.E) :
    (linList n pt pt.length).toArray = InducedTerminalRefinement.nativeLinear n pt.toArray := by
  apply Array.ext
  · simp [linList, InducedTerminalRefinement.nativeLinear]
  · intro i h1 h2
    simp only [linList, List.size_toArray, List.length_map, List.length_range] at h1
    simp [linList, InducedTerminalRefinement.nativeLinear, getElem!_pos, h1, add_comm]

/-- `affine_factors` is the model's `nativeLinear` on the interpreted point. -/
theorem affine_factors_eq (h : ArithModel A encode const) (hone : const primitives.field.gf2_64x3.F192.ONE = 1)
    (n : Nat) (a : S) (point : Slice E) (inverses : Slice primitives.field.gf2_64.F64)
    (hlen : point.val.length ≤ inverses.val.length)
    (hinv : ∀ i (hi : i < inverses.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from inverses.val[i] = .ok f →
        const f = Concrete.E.ofK (InducedTerminalRefinement.nativeInverse (subspaceRoots n)[i]!)) :
    ∃ lin, whir.verify.affine_factors copy A a point inverses = .ok (lin, a) ∧
      lin.val.length = point.val.length ∧
      factors encode (alloc.vec.Vec.deref lin) =
        InducedTerminalRefinement.nativeLinear n (point.val.map encode).toArray := by
  obtain ⟨lin, hloop, elin⟩ := affine_loop_eq A encode const h hone n point inverses hlen hinv _ 0#usize
    (alloc.vec.Vec.with_capacity _ (Slice.len point)) a rfl (by simp)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, linList])
  refine ⟨lin, by simpa [whir.verify.affine_factors] using hloop, ?_, ?_⟩
  · simpa [linList] using congrArg List.length elin
  · rw [factors, ← linList_eq]
    simp only [alloc.vec.Vec.deref, Slice.from_val, List.length_map] at elin ⊢
    rw [elin]

end Basis

section BasisAt
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : K → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Q → Nat)

/-- One query's term of `nativeBasisAt`. -/
def queryProduct (n : Nat) (pt : Array Concrete.E) (q : Nat) : Concrete.E :=
  ((List.range pt.size).foldl (InducedTerminalRefinement.nativeStep (subspaceRoots n)
    (InducedTerminalRefinement.nativeLinear n pt)) (Concrete.E.ofK (UInt64.ofNat q), 1)).2

theorem basis_at_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (copy : core.marker.Copy E) (n : Nat)
    (queries : alloc.vec.Vec Q) (weights : alloc.vec.Vec E) (nz : whir.query.Normalizers)
    (lin : alloc.vec.Vec (E × E)) (pt : Array Concrete.E) (stop : Usize)
    (hstop : stop.val = min queries.val.length weights.val.length)
    (hlin : factors encode (alloc.vec.Vec.deref lin) = InducedTerminalRefinement.nativeLinear n pt)
    (hsize : lin.val.length = pt.size) (hsks : lin.val.length ≤ nz.at_roots.val.length + 1)
    (hroots : ∀ i (hi : i < nz.at_roots.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from nz.at_roots.val[i] = .ok f →
        const f = Concrete.E.ofK (subspaceRoots n)[i]!) :
    ∀ (m : Nat) (i : Usize) (acc : E) (v : V), stop.val - i.val = m → i.val ≤ stop.val →
      encode acc = (List.range i.val).foldl (fun acc j =>
        (weights.val.map encode)[j]! * queryProduct n pt (queries.val.map index)[j]! + acc) 0 →
      ∃ y, whir.verify.LevelCtx.basis_at_loop copy inst { start := i, «end» := stop } queries weights v nz
          lin acc = .ok (y, v) ∧
        encode y = (List.range stop.val).foldl (fun acc j =>
          (weights.val.map encode)[j]! * queryProduct n pt (queries.val.map index)[j]! + acc) 0 := by
  intro m
  induction m with
  | zero =>
    intro i acc v hm hi hacc
    refine ⟨acc, ?_, by rw [show stop.val = i.val by omega]; exact hacc⟩
    unfold whir.verify.LevelCtx.basis_at_loop
    apply loop_done
    simp [whir.verify.LevelCtx.basis_at_loop.body,
      range_next_none { start := i, «end» := stop } (show stop.val ≤ i.val by omega)]
  | succ m ih =>
    intro i acc v hm hi hacc
    have hlt : i.val < stop.val := by omega
    have hq : i.val < queries.val.length := by omega
    have hw : i.val < weights.val.length := by omega
    obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some { start := i, «end» := stop } hlt
    obtain ⟨s, hs, es⟩ := hr.query_point v queries.val[i.val]
    obtain ⟨prod, hprod, eprod⟩ := basis_product_eq copy inst.fiat_shamirarithVerifierInst.ArithInst encode
      const h v (alloc.vec.Vec.deref lin) (alloc.vec.Vec.deref nz.at_roots) (subspaceRoots n) s
      (by simpa [alloc.vec.Vec.deref] using hsks)
      (by simpa [alloc.vec.Vec.deref] using hroots)
    obtain ⟨acc1, hacc1, eacc1⟩ := h.mul_add v weights.val[i.val] prod acc
    have hbody : whir.verify.LevelCtx.basis_at_loop.body copy inst queries weights nz lin
        { start := i, «end» := stop } v acc = .ok (.cont (iter1, v, acc1)) := by
      simp [whir.verify.LevelCtx.basis_at_loop.body, hnext, vec_index_usize queries i hq, hs,
        whir.query.Normalizers.impl.at_roots, hprod, vec_index_usize weights i hw, hacc1]
    have hiter : iter1 = { start := Std.Usize.wrapping_add i 1#usize, «end» := stop } := by
      have hsucc := succ_val i stop.val hlt (by scalar_tac)
      cases iter1
      simp only at hs1 he1
      subst he1
      congr 1
      apply UScalar.eq_of_val_eq
      rw [hs1, hsucc]
    have hsucc := succ_val i stop.val hlt (by scalar_tac)
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add i 1#usize) acc1 v (by omega) (by omega) (by
      rw [hsucc, List.range_succ, List.foldl_append, ← hacc]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [eacc1, eprod, map_getElem! _ _ _ hw, map_getElem! _ _ _ hq, es, queryProduct]
      congr 2
      simp only [factors, alloc.vec.Vec.deref, Slice.from_val] at hlin ⊢
      rw [show (List.map (fun p => (encode p.1, encode p.2)) lin.val).toArray =
        InducedTerminalRefinement.nativeLinear n pt from hlin, hsize])
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.LevelCtx.basis_at_loop
    rw [loop_cont hbody, hiter]
    unfold whir.verify.LevelCtx.basis_at_loop at hy
    exact hy

/-- `LevelCtx::basis_at` at a point of the level's cube is the model's `nativeBasisAt`. -/
theorem basis_at_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (copy : core.marker.Copy E) (ctx : whir.verify.LevelCtx Q E) (v : V) (point : Slice E)
    (hp : point.val.length = ctx.log_msg_cols.val) (h64 : ctx.log_msg_cols.val < 64) :
    ∃ y, whir.verify.LevelCtx.basis_at copy inst ctx v point = .ok (y, v) ∧
      encode y = InducedTerminalRefinement.nativeBasisAt ctx.log_msg_cols.val
        (ctx.queries.val.map index).toArray (ctx.weights.val.map encode).toArray
        (point.val.map encode).toArray := by
  obtain ⟨nz, hnz, hroots_len, hinv_len, hroots, hinv⟩ := hn.new ctx.log_msg_cols h64
  obtain ⟨lin, hlin, hlen, elin⟩ := affine_factors_eq copy
    inst.fiat_shamirarithVerifierInst.ArithInst encode const h hn.one ctx.log_msg_cols.val v point
    (alloc.vec.Vec.deref nz.inverses) (by simp [alloc.vec.Vec.deref]; omega)
    (by simpa [alloc.vec.Vec.deref] using hinv)
  obtain ⟨zero, hzero, ezero⟩ := h.zero v
  have hmin : (core.cmp.impls.OrdUsize.min (alloc.vec.Vec.len ctx.queries) (alloc.vec.Vec.len ctx.weights)).val =
      min ctx.queries.val.length ctx.weights.val.length := by
    simp [core.cmp.impls.OrdUsize.min_val]
  obtain ⟨y, hy, ey⟩ := basis_at_loop_eq inst encode const encodeK ofLimbs index h hr copy ctx.log_msg_cols.val
    ctx.queries ctx.weights nz lin (point.val.map encode).toArray _ hmin elin (by simp [hlen])
    (by omega) hroots _ 0#usize zero v rfl (by simp) (by simp [ezero])
  refine ⟨y, ?_, ?_⟩
  · have hpl : Slice.len point = ctx.log_msg_cols := by
      apply UScalar.eq_of_val_eq; simp [hp]
    simp only [whir.verify.LevelCtx.basis_at, hpl, ↓reduceIte, hnz, Std.bind_ok,
      whir.query.Normalizers.impl.inverses, hlin, lift]
    generalize core.cmp.impls.OrdUsize.min ctx.queries.len ctx.weights.len = stop at hy ⊢
    simp [hzero, hy]
  · rw [ey, InducedTerminalRefinement.nativeBasisAt, hmin]
    simp only [List.size_toArray, List.length_map]
    congr 1
    funext acc j
    rw [queryProduct, Query.toArray_getElem!, Query.toArray_getElem!]
    simp

end BasisAt

theorem vec_range {α : Type} (v : alloc.vec.Vec α) (a b : Usize) (hab : a.val ≤ b.val)
    (hb : b.val ≤ v.val.length) :
    ∃ t, alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice α) v { start := a, «end» := b } =
      .ok t ∧ t.val = (v.val.drop a.val).take (b.val - a.val) := by
  simp only [alloc.vec.Vec.index]
  exact slice_range v.slice a b hab hb

/-! ## The terminal weight -/

section Terminal
open AccumulatedTerminalRefinement
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : K → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Q → Nat)

/-- A level context's term at the terminal point: its induced basis at its suffix of the
fold challenges followed by the residual challenges, at its power. -/
def levelTerm (c : whir.verify.LevelCtx Q E) (ris tail : List Concrete.E) : Concrete.E :=
  encode c.beta * InducedTerminalRefinement.nativeBasisAt c.log_msg_cols.val
    (c.queries.val.map index).toArray (c.weights.val.map encode).toArray
    ((ris.drop c.ris_start.val).take (c.log_msg_cols.val - tail.length) ++ tail).toArray

/-- An out-of-domain context's term at the terminal point. -/
def oodTerm (c : whir.verify.OodCtx E) (ris tail : List Concrete.E) : Concrete.E :=
  encode c.beta * AccumulatedTerminalAlgebra.equalityProduct (c.z.val.map encode)
    ((ris.drop c.ris_start.val).take (c.z.val.length - tail.length) ++ tail)

/-- What the terminal reads of a saved level context: it fits the transcript's fold point. -/
def LevelFits (ris tail : Nat) (c : whir.verify.LevelCtx Q E) : Prop :=
  tail ≤ c.log_msg_cols.val ∧ c.ris_start.val + (c.log_msg_cols.val - tail) ≤ ris ∧ c.log_msg_cols.val < 64

def OodFits (ris tail : Nat) (c : whir.verify.OodCtx E) : Prop :=
  tail ≤ c.z.val.length ∧ c.ris_start.val + (c.z.val.length - tail) ≤ ris

theorem terminal_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (ris : alloc.vec.Vec E) (levels : alloc.vec.Vec (whir.verify.LevelCtx Q E)) (ris_tail : Slice E)
    (hfit : ∀ c ∈ levels.val, LevelFits ris.val.length ris_tail.val.length c) :
    ∀ (m : Nat) (i : Usize) (weight : E) (v : V), levels.val.length - i.val = m → i.val ≤ levels.val.length →
      encode weight = ((levels.val.take i.val).map fun c =>
        levelTerm encode index c (ris.val.map encode) (ris_tail.val.map encode)).sum →
      ∃ w, whir.verify.WhirReplay.terminal_loop inst { start := i, «end» := alloc.vec.Vec.len levels }
          ris levels v ris_tail (Slice.len ris_tail) weight = .ok (v, w) ∧
        encode w = (levels.val.map fun c =>
          levelTerm encode index c (ris.val.map encode) (ris_tail.val.map encode)).sum := by
  intro m
  induction m with
  | zero =>
    intro i weight v hm hi hw
    refine ⟨weight, ?_, by rw [hw, show i.val = levels.val.length by omega, List.take_length]⟩
    unfold whir.verify.WhirReplay.terminal_loop
    apply loop_done
    simp [whir.verify.WhirReplay.terminal_loop.body,
      range_next_none { start := i, «end» := alloc.vec.Vec.len levels } (by simp; omega)]
  | succ m ih =>
    intro i weight v hm hi hw
    have hlt : i.val < levels.val.length := by omega
    set c := levels.val[i.val] with hc
    obtain ⟨ht, hs, h64⟩ := hfit c (List.getElem_mem hlt)
    obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some { start := i, «end» := alloc.vec.Vec.len levels }
      (by simpa using hlt)
    have hfold : (Std.Usize.wrapping_sub c.log_msg_cols (Slice.len ris_tail)).val =
        c.log_msg_cols.val - ris_tail.val.length :=
      Fold.sub_val _ _ (by simpa using ht)
    have hend : (Std.Usize.wrapping_add c.ris_start (Std.Usize.wrapping_sub c.log_msg_cols
        (Slice.len ris_tail))).val = c.ris_start.val + (c.log_msg_cols.val - ris_tail.val.length) := by
      rw [Std.Usize.wrapping_add_val_eq, hfold]
      apply Nat.mod_eq_of_lt
      have := ris.property
      have := Usize.max_def
      simp only [UScalar.size] at *
      scalar_tac
    obtain ⟨s, hsl, es⟩ := vec_range ris c.ris_start _ (by rw [hend]; omega) (by rw [hend]; omega)
    obtain ⟨pt, hpt, ept⟩ := to_vec_ok _ hclone s
    obtain ⟨pt1, hpt1, ept1⟩ := extend_ok _ hclone pt ris_tail (by
      rw [ept, es]; simp only [List.length_take, List.length_drop]
      have := ris_tail.property; scalar_tac)
    have hptv : (alloc.vec.Vec.deref pt1).val =
        (ris.val.drop c.ris_start.val).take (c.log_msg_cols.val - ris_tail.val.length) ++ ris_tail.val := by
      simp only [alloc.vec.Vec.deref, Slice.from_val, ept1, ept, es, hend]
      congr 2
      omega
    have hlen : (alloc.vec.Vec.deref pt1).val.length = c.log_msg_cols.val := by
      rw [hptv]
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    obtain ⟨at_, hat, eat⟩ := basis_at_eq inst encode const encodeK ofLimbs index h hr hn
      inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst c v (alloc.vec.Vec.deref pt1) hlen h64
    rw [hptv] at eat
    obtain ⟨w1, hw1, ew1⟩ := h.mul_add v c.beta at_ weight
    have hbody : whir.verify.WhirReplay.terminal_loop.body inst ris levels ris_tail (Slice.len ris_tail)
        { start := i, «end» := alloc.vec.Vec.len levels } v weight = .ok (.cont (iter1, v, w1)) := by
      simp [whir.verify.WhirReplay.terminal_loop.body, hnext, vec_index_usize levels i hlt, ← hc, lift,
        hsl, hpt, hpt1, hat, hw1]
    have hiter : iter1 = { start := Std.Usize.wrapping_add i 1#usize, «end» := alloc.vec.Vec.len levels } := by
      have hsucc := succ_val i levels.val.length hlt (by have := levels.property; scalar_tac)
      cases iter1
      simp only at hs1 he1
      subst he1
      congr 1
      apply UScalar.eq_of_val_eq
      rw [hs1, hsucc]
    have hsucc := succ_val i levels.val.length hlt (by have := levels.property; scalar_tac)
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add i 1#usize) w1 v (by omega) (by omega) (by
      rw [hsucc, List.take_succ_eq_append_getElem hlt, List.map_append, List.sum_append, ew1, eat, hw]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ← hc]
      rw [add_comm]
      simp [levelTerm, List.map_take, List.map_drop])
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.WhirReplay.terminal_loop
    rw [loop_cont hbody, hiter]
    unfold whir.verify.WhirReplay.terminal_loop at hy
    exact hy

theorem add_ood_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (copy : core.marker.Copy E) (oods : Slice (whir.verify.OodCtx E)) (ris ris_tail : Slice E)
    (weight0 : E) (hfit : ∀ c ∈ oods.val, OodFits ris.val.length ris_tail.val.length c) :
    ∀ (m : Nat) (i : Usize) (weight : E) (v : V), oods.val.length - i.val = m → i.val ≤ oods.val.length →
      encode weight = encode weight0 + ((oods.val.take i.val).map fun c =>
        oodTerm encode c (ris.val.map encode) (ris_tail.val.map encode)).sum →
      ∃ w, whir.verify.add_ood_terms_loop copy inst.fiat_shamirarithVerifierInst.ArithInst v oods ris ris_tail
          weight (Slice.len ris_tail) i = .ok (w, v) ∧
        encode w = encode weight0 + (oods.val.map fun c =>
          oodTerm encode c (ris.val.map encode) (ris_tail.val.map encode)).sum := by
  intro m
  induction m with
  | zero =>
    intro i weight v hm hi hw
    refine ⟨weight, ?_, by rw [hw, show i.val = oods.val.length by omega, List.take_length]⟩
    unfold whir.verify.add_ood_terms_loop
    apply loop_done
    have : ¬ (i < Slice.len oods) := by simp; omega
    simp [whir.verify.add_ood_terms_loop.body, this]
  | succ m ih =>
    intro i weight v hm hi hw
    have hlt : i.val < oods.val.length := by omega
    set c := oods.val[i.val] with hc
    obtain ⟨ht, hs⟩ := hfit c (List.getElem_mem hlt)
    have hfold : (Std.Usize.wrapping_sub (alloc.vec.Vec.len c.z) (Slice.len ris_tail)).val =
        c.z.val.length - ris_tail.val.length := by
      rw [Fold.sub_val _ _ (by simpa using ht)]; simp
    have hend : (Std.Usize.wrapping_add c.ris_start (Std.Usize.wrapping_sub (alloc.vec.Vec.len c.z)
        (Slice.len ris_tail))).val = c.ris_start.val + (c.z.val.length - ris_tail.val.length) := by
      rw [Std.Usize.wrapping_add_val_eq, hfold]
      apply Nat.mod_eq_of_lt
      have := ris.property
      have := Usize.max_def
      simp only [UScalar.size] at *
      scalar_tac
    obtain ⟨s, hsl, es⟩ := slice_range ris c.ris_start _ (by rw [hend]; omega) (by rw [hend]; omega)
    have hsv : s.val = (ris.val.drop c.ris_start.val).take (c.z.val.length - ris_tail.val.length) := by
      rw [es, hend]
      congr 1
      omega
    obtain ⟨t, ht', et⟩ := Fold.term_eq copy inst.fiat_shamirarithVerifierInst.ArithInst encode const h c v s
      ris_tail (by
        rw [hsv]; simp only [List.length_take, List.length_drop]
        have := ris_tail.property; scalar_tac)
    obtain ⟨w1, hw1, ew1⟩ := h.add v weight t
    have hbody : whir.verify.add_ood_terms_loop.body copy inst.fiat_shamirarithVerifierInst.ArithInst oods ris
        ris_tail (Slice.len ris_tail) v weight i = .ok (.cont (v, w1, Std.Usize.wrapping_add i 1#usize)) := by
      have : i < Slice.len oods := by simp; omega
      simp only [whir.verify.add_ood_terms_loop.body, this, ↓reduceIte, slice_index oods i hlt, ← hc, lift,
        Std.bind_ok, Slice.index_SliceIndexRangeUsizeSliceInst, hsl, ht']
      simp [hw1]
    have hsucc := succ_val i oods.val.length hlt (by have := oods.property; scalar_tac)
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add i 1#usize) w1 v (by omega) (by omega) (by
      rw [hsucc, List.take_succ_eq_append_getElem hlt, List.map_append, List.sum_append, ew1, et, hw, hsv]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ← hc, add_assoc]
      simp [oodTerm, List.map_take, List.map_drop])
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.add_ood_terms_loop
    rw [loop_cont hbody]
    unfold whir.verify.add_ood_terms_loop at hy
    exact hy

theorem rotate_toArray (k : Nat) (l : List Concrete.E) :
    (l.drop k ++ l.take k).toArray = rotatePoint k l.toArray := by
  apply Array.toList_inj.mp
  simp [rotatePoint, List.take_of_length_le]

/-- The equality check the terminal ends with returns `Ok` exactly when the interpreted
operands are equal. -/
def EnsureModel (inst : verifier.OpeningVerifier V R K Q E) (encode : E → Concrete.E) : Prop :=
  ∀ {Er T2 : Type} (f : core.ops.function.FnOnce T2 Unit Er) (v : V) (a b : E) (c : T2),
    ∃ r v', inst.fiat_shamirarithVerifierInst.ensure_eq f v a b c = .ok (r, v') ∧
      (r = .Ok () ↔ encode a = encode b)

/-- The caller's weight is `callerAt` of the interpreted point it is given. -/
def CallerModel {T1 : Type} (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (encode : E → Concrete.E) (callerAt : Array Concrete.E → Concrete.E) : Prop :=
  ∀ v (pt : Slice E), ∃ y v', W.call weight_at v pt = .ok (y, v') ∧
    encode y = callerAt (pt.val.map encode).toArray

/-- The terminal check accepts exactly when the running claim equals the level terms, the
out-of-domain terms and the caller's weight at the rotated point, times the residual's
multilinear extension at the residual challenges. -/
theorem terminal_eq {T1 : Type} (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (self : whir.verify.WhirReplay V R K Q E) (v : V) (config : whir.config.Config)
    (yr ris_tail : Slice E)
    (hlev : ∀ c ∈ self.levels.val, LevelFits self.ris.val.length ris_tail.val.length c)
    (hood : ∀ c ∈ self.oods.val, OodFits self.ris.val.length ris_tail.val.length c)
    (hk : config.initial_k.val ≤ self.ris.val.length + ris_tail.val.length)
    (hcap : self.ris.val.length + ris_tail.val.length ≤ Usize.max)
    (h64 : ris_tail.val.length < 64) (hyr : yr.val.length = 2 ^ ris_tail.val.length) :
    ∃ r v', whir.verify.WhirReplay.terminal inst W self v config yr ris_tail weight_at = .ok (r, v') ∧
      (r = .Ok () ↔
        ((self.levels.val.map fun c => levelTerm encode index c (self.ris.val.map encode)
            (ris_tail.val.map encode)).sum +
          (self.oods.val.map fun c => oodTerm encode c (self.ris.val.map encode)
            (ris_tail.val.map encode)).sum +
          callerAt (rotatePoint config.initial_k.val
            ((self.ris.val ++ ris_tail.val).map encode).toArray)) *
          Concrete.mle (yr.val.map encode).toArray (ris_tail.val.map encode).toArray =
        encode self.t_r) := by
  obtain ⟨zero, hzero, ezero⟩ := h.zero v
  obtain ⟨w, hw, ew⟩ := terminal_loop_eq inst encode const encodeK ofLimbs index h hr hn hclone self.ris
    self.levels ris_tail hlev _ 0#usize zero v rfl (by simp) (by simp [ezero])
  obtain ⟨w1, hw1, ew1⟩ := add_ood_loop_eq inst encode const h
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst (alloc.vec.Vec.deref self.oods)
    (alloc.vec.Vec.deref self.ris) ris_tail w (by simpa [alloc.vec.Vec.deref] using hood) _ 0#usize w v rfl
    (by simp) (by simp)
  obtain ⟨fp, hfp, efp⟩ := clone_vec_ok _ hclone self.ris
  obtain ⟨fp1, hfp1, efp1⟩ := extend_ok _ hclone fp ris_tail (by rw [efp]; exact hcap)
  have hrot : config.initial_k.val ≤ fp1.slice.val.length := by
    have : fp1.slice.val = fp1.val := rfl
    rw [this, efp1, efp]; simpa using hk
  let rot : Slice E := Slice.from (fp1.slice.val.drop config.initial_k.val ++ fp1.slice.val.take config.initial_k.val)
    (by have := fp1.slice.property; simp; omega)
  have hrl : core.slice.Slice.rotate_left fp1.slice config.initial_k = .ok rot := by
    simp [core.slice.Slice.rotate_left, hrot, rot]
  obtain ⟨caller, v4, hc4, ec4⟩ := hcall v (alloc.vec.Vec.deref { slice := rot })
  simp only [alloc.vec.Vec.deref] at hc4
  obtain ⟨w2, hw2, ew2⟩ := h.add v4 w1 caller
  obtain ⟨fy, hfy, efy⟩ := h.mle v4 yr ris_tail h64 hyr
  obtain ⟨lhs, hlhs, elhs⟩ := h.mul v4 w2 fy
  obtain ⟨r, v', hens', er⟩ := hens
    (whir.verify.WhirReplay.terminal.closure.Insts.CoreOpsFunctionFnOnceTupleWhirError inst W) v4 lhs self.t_r ()
  refine ⟨r, v', ?_, ?_⟩
  · simp only [whir.verify.WhirReplay.terminal, hzero, Std.bind_ok, alloc.vec.Vec.deref]
    simp [hw, whir.verify.add_ood_terms, alloc.vec.Vec.deref] at hw1 ⊢
    simp [hw1, hfp, hfp1, lift, alloc.vec.Vec.deref_mut, whir.config.Config.impl.initial_k, hrl, hc4, hw2,
      hfy, hlhs, hens']
  · rw [er, elhs, ew2, ew1, ew, efy, ec4]
    have hpt : ((alloc.vec.Vec.deref ({ slice := rot } : alloc.vec.Vec E)).val.map encode).toArray =
        rotatePoint config.initial_k.val ((self.ris.val ++ ris_tail.val).map encode).toArray := by
      rw [← rotate_toArray]
      have hv : (alloc.vec.Vec.deref ({ slice := rot } : alloc.vec.Vec E)).val =
          fp1.val.drop config.initial_k.val ++ fp1.val.take config.initial_k.val := by
        simp only [alloc.vec.Vec.deref, rot, Slice.from_val]
        simp [alloc.vec.Vec.val]
      rw [hv, efp1, efp]
      simp [List.map_drop, List.map_take]
    rw [hpt]
    simp [alloc.vec.Vec.deref]

end Terminal

/-! ## Model-side iteration -/

theorem runSteps_foldl {S : Type} (f : Nat → S → S) (n start : Nat) (s : S) :
    Protocol.runSteps f n start s = (List.range' start n).foldl (fun s j => f j s) s := by
  induction n generalizing start s with
  | zero => rfl
  | succ n ih => simp [Protocol.runSteps, ih, List.range'_succ]

theorem runSteps_succ {S : Type} (f : Nat → S → S) (n : Nat) (s : S) :
    Protocol.runSteps f (n + 1) 0 s = f n (Protocol.runSteps f n 0 s) := by
  rw [runSteps_foldl, runSteps_foldl, List.range'_concat]
  simp

/-! ## The residual rounds -/

section Tail
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : K → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Q → Nat) (tape : V → List (Event E Q R K))

/-- A residual round's reads: its challenge, then its polynomial unless it is the last. -/
def tailEvents : E × Option (E × E) → List (Event E Q R K)
  | (r, some (u0, u2)) => [.sample r, .poly u0 u2]
  | (r, none) => [.sample r]

def tailPairs (tail : List E) (msgs : List (E × E)) : List (E × Option (E × E)) :=
  tail.zip (msgs.map some ++ [none])

/-- The tape of the residual rounds. -/
def tailTape (tail : List E) (msgs : List (E × E)) : List (Event E Q R K) :=
  (tailPairs tail msgs).flatMap tailEvents

theorem tailPairs_drop (tail : List E) (msgs : List (E × E)) (hlen : msgs.length + 1 = tail.length)
    (j : Nat) (hj : j < tail.length) :
    (tailPairs tail msgs).drop j =
      (tail[j], if h : j + 1 < tail.length then some msgs[j] else none) :: (tailPairs tail msgs).drop (j + 1) := by
  have hl : j < (tailPairs tail msgs).length := by simp [tailPairs]; omega
  rw [List.drop_eq_getElem_cons hl]
  congr 1
  simp only [tailPairs, List.getElem_zip]
  congr 1
  by_cases h : j + 1 < tail.length
  · simp only [h, ↓reduceDIte]
    rw [List.getElem_append_left (by simp; omega)]
    simp
  · simp only [h, ↓reduceDIte]
    rw [List.getElem_append_right (by simp; omega)]
    simp

/-- The terminal formula of `terminal_eq`. -/
def terminalValue (callerAt : Array Concrete.E → Concrete.E) (initialK : Nat)
    (ris : List E) (levels : List (whir.verify.LevelCtx Q E)) (oods : List (whir.verify.OodCtx E))
    (yr tail : List E) : Concrete.E :=
  ((levels.map fun c => levelTerm encode index c (ris.map encode) (tail.map encode)).sum +
    (oods.map fun c => oodTerm encode c (ris.map encode) (tail.map encode)).sum +
    callerAt (rotatePoint initialK ((ris ++ tail).map encode).toArray)) *
    Concrete.mle (yr.map encode).toArray (tail.map encode).toArray

theorem tail_loop_eq {T1 : Type} (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : whir.config.Config) (nc : Usize) (yr : alloc.vec.Vec E)
    (ris0 : alloc.vec.Vec E) (levels0 : alloc.vec.Vec (whir.verify.LevelCtx Q E))
    (oods0 : alloc.vec.Vec (whir.verify.OodCtx E))
    (tail : List E) (msgs : List (E × E)) (rest : List (Event E Q R K))
    (ch : Protocol.Challenges) (pf : Protocol.Opening) (st0 : State)
    (hch : ch.tail = (tail.map encode).toArray)
    (hpf : pf.tailMessages = (msgs.map fun m => (⟨encode m.1, encode m.2⟩ : Protocol.Message Concrete.E)).toArray)
    (hlen : msgs.length + 1 = tail.length) (hnc : nc.val = tail.length)
    (hlev : ∀ c ∈ levels0.val, LevelFits ris0.val.length tail.length c)
    (hood : ∀ c ∈ oods0.val, OodFits ris0.val.length tail.length c)
    (hk : config.initial_k.val ≤ ris0.val.length + tail.length)
    (hcap : ris0.val.length + tail.length ≤ Usize.max)
    (h64 : tail.length < 64) (hyr : yr.val.length = 2 ^ tail.length) :
    ∀ (m j : Nat) (iter : core.ops.range.Range Usize) (self : whir.verify.WhirReplay V R K Q E) (v : V)
      (rt : alloc.vec.Vec E),
      iter.start.val = j → iter.end = nc → tail.length - j = m → j ≤ tail.length →
      tape v = ((tailPairs tail msgs).drop j).flatMap tailEvents ++ rest →
      self.ris = ris0 → self.levels = levels0 → self.oods = oods0 → rt.val = tail.take j →
      encode self.t_r = (Protocol.runSteps (tailStep ch pf) j 0 st0).claim →
      (⟨encode self.quad.c, encode self.quad.a⟩ : Protocol.Message Concrete.E) =
        (Protocol.runSteps (tailStep ch pf) j 0 st0).message →
      (j < tail.length → encode self.quad.b =
        (Protocol.runSteps (tailStep ch pf) j 0 st0).claim + encode self.quad.a) →
      ∃ r v', whir.verify.WhirReplay.last_level_loop inst W iter self v config nc weight_at yr rt =
          .ok (r, v') ∧
        (r = .Ok () ↔ terminalValue encode index callerAt config.initial_k.val ris0.val levels0.val oods0.val
          yr.val tail = (Protocol.runSteps (tailStep ch pf) tail.length 0 st0).claim) := by
  intro m
  induction m with
  | zero =>
    intro j iter self v rt hs he hm hj hv hris hlevs hoods hrt hc hmsg hb
    have hjn : j = tail.length := by omega
    subst hjn
    have hnone : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (none, iter) :=
      range_next_none iter (by rw [he, hnc, hs])
    have hrt' : rt.val = tail := by rw [hrt, List.take_length]
    obtain ⟨r, v', hterm, er⟩ := terminal_eq inst encode const encodeK ofLimbs index h hr hn hclone hens W
      weight_at callerAt hcall self v config (alloc.vec.Vec.deref yr) (alloc.vec.Vec.deref rt)
      (by simpa [hris, hlevs, alloc.vec.Vec.deref, hrt'] using hlev)
      (by simpa [hris, hoods, alloc.vec.Vec.deref, hrt'] using hood)
      (by simpa [hris, alloc.vec.Vec.deref, hrt'] using hk)
      (by simpa [hris, alloc.vec.Vec.deref, hrt'] using hcap)
      (by simpa [alloc.vec.Vec.deref, hrt'] using h64)
      (by simpa [alloc.vec.Vec.deref, hrt'] using hyr)
    refine ⟨r, v', ?_, ?_⟩
    · unfold whir.verify.WhirReplay.last_level_loop
      apply loop_done
      simp [whir.verify.WhirReplay.last_level_loop.body, hnone, ht.begin_scope, hterm, ht.end_scope]
    · rw [er, ← hc]
      simp only [terminalValue, alloc.vec.Vec.deref, Slice.from_val, hrt', hris, hlevs, hoods]
  | succ m ih =>
    intro j iter self v rt hs he hm hj hv hris hlevs hoods hrt hc hmsg hb
    have hjt : j < tail.length := by omega
    have hjn : j < nc.val := by omega
    obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some iter (by rw [he, hs]; exact hjn)
    rw [tailPairs_drop tail msgs hlen j hjt] at hv
    set sj := Protocol.runSteps (tailStep ch pf) j 0 st0 with hsj
    have hstep : Protocol.runSteps (tailStep ch pf) (j + 1) 0 st0 = tailStep ch pf j sj := runSteps_succ _ _ _
    have htj : ch.tail[j]! = encode tail[j] := by rw [hch]; simp [getElem!_pos, hjt]
    have hsize : ch.tail.size = tail.length := by rw [hch]; simp
    have hmod : (iter.start.val + 1) % Usize.size = j + 1 := by
      rw [hs]; apply Nat.mod_eq_of_lt
      have := Usize.max_def; have := nc.hBounds
      simp only [Usize.size, Usize.max] at *
      omega
    obtain ⟨rt1, hpush, ert1⟩ := push_ok rt tail[j] (by
      rw [hrt]; simp only [List.length_take]; have := Usize.max_def; scalar_tac)
    have hrt1 : rt1.val = tail.take (j + 1) := by rw [ert1, hrt, List.take_succ_eq_append_getElem hjt]
    by_cases hl : j + 1 < tail.length
    · have hmj : j < msgs.length := by omega
      simp only [hl, ↓reduceDIte, tailEvents, List.flatMap_cons, List.cons_append, List.nil_append] at hv
      obtain ⟨v1, hsample, hv1⟩ := ht.sample v tail[j] _ hv
      obtain ⟨t, het, et⟩ := quad_eval inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst inst
        encode const h self.quad v1 tail[j] sj.claim (hb hjt)
      obtain ⟨q, v3, hrecv, hqc, hqa, hqb, hv3⟩ := recv_eq inst encode tape ht
        inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v1 t msgs[j].1 msgs[j].2 _ hv1
      have hbody : whir.verify.WhirReplay.last_level_loop.body inst W config nc weight_at yr iter self v rt =
          .ok (.cont (iter1, { self with t_r := t, quad := q }, v3, rt1)) := by
        simp [whir.verify.WhirReplay.last_level_loop.body, hnext, hsample, het, hpush, lift, hmod, hnc, hl,
          hrecv, core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨r, v', hloop, er⟩ := ih (j + 1) iter1 { self with t_r := t, quad := q } v3 rt1
        (by rw [hs1, hs]) (by rw [he1, he]) (by omega) (by omega) hv3 hris hlevs hoods hrt1
        (by rw [hstep, et, hmsg]; simp [tailStep, htj])
        (by rw [hstep]; simp [tailStep, hsize, hl, hpf, getElem!_pos, hmj, hqc, hqa])
        (fun _ => by rw [hstep, hqb, hqa, et, hmsg]; simp [tailStep, htj])
      refine ⟨r, v', ?_, er⟩
      unfold whir.verify.WhirReplay.last_level_loop
      rw [loop_cont hbody]
      unfold whir.verify.WhirReplay.last_level_loop at hloop
      exact hloop
    · simp only [hl, ↓reduceDIte, tailEvents, List.flatMap_cons, List.cons_append, List.nil_append] at hv
      obtain ⟨v1, hsample, hv1⟩ := ht.sample v tail[j] _ hv
      obtain ⟨t, het, et⟩ := quad_eval inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst inst
        encode const h self.quad v1 tail[j] sj.claim (hb hjt)
      have hbody : whir.verify.WhirReplay.last_level_loop.body inst W config nc weight_at yr iter self v rt =
          .ok (.cont (iter1, { self with t_r := t }, v1, rt1)) := by
        simp [whir.verify.WhirReplay.last_level_loop.body, hnext, hsample, het, hpush, lift, hmod, hnc, hl]
      obtain ⟨r, v', hloop, er⟩ := ih (j + 1) iter1 { self with t_r := t } v1 rt1
        (by rw [hs1, hs]) (by rw [he1, he]) (by omega) (by omega) hv1 hris hlevs hoods hrt1
        (by rw [hstep, et, hmsg]; simp [tailStep, htj])
        (by rw [hstep]; simp [tailStep, hsize, hl, hmsg])
        (fun h' => absurd h' (by omega))
      refine ⟨r, v', ?_, er⟩
      unfold whir.verify.WhirReplay.last_level_loop
      rw [loop_cont hbody]
      unfold whir.verify.WhirReplay.last_level_loop at hloop
      exact hloop

end Tail

end WhirAeneas.Replay
