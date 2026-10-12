import WhirAeneas.NativeReads
import WhirAeneas.Authenticated

/-! The composed theorem for the generated native opening verifier (`OpeningVerifier` for
`VerifierState` over the BLAKE2s duplex, extracted with the replay), without assuming its
transcript reads: `NativeReads.native_transcript` derives `Transcript` from the duplex,
proof-of-work hash and Merkle hash content contracts, so `verify_eq` holds when the proof answers
the script (`NativeAnswers`). Under injective leaf and pair hashes, openings against committed
trees authenticate the script's rows: `AuthenticatedRows` holds for the script's opening with the
committed tables, the per-level accepting hints read off the same `NativeAnswers`. -/
namespace WhirAeneas.Native
open Aeneas Aeneas.Std Whir Whir.Concrete Whir.WHIRNativeArithmetic WhirAeneas.Merkle
  WhirAeneas.MerkleNative WhirAeneas.Replay WhirAeneas.Fold WhirAeneas.Query WhirAeneas.NativeReads

section Loop
variable (encode : NativeReads.F192 → Concrete.E)
  (const : ReplaySource.primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : U64 → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Usize → Nat)

/-- The composed theorem for the generated native opening verifier: `verify_eq` with every read
derived from the extracted transcript, the duplex, proof-of-work and Merkle hash contracts, and
what the proof holds (`NativeAnswers`), instead of assumed. -/
theorem verify_eq_native {T1 : Type} (hw : System.Platform.numBits = 64)
    (h : ArithModel nativeInst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel nativeInst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    {out : List DOp → Nat → List U8} {R : ReplaySource.fiat_shamir.duplex.Blake2sDuplex → List DOp → Prop}
    (hD : Duplex out R) {H : List U8 → Digest} (hH : PowHash H)
    {leaf : List U64 → Digest} {node : Digest → Digest → Digest} (hR : RowHash leaf) (hP : PairHash node)
    (hclone : ∀ x, nativeInst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel nativeInst encode)
    (W : ReplaySource.whir.verify.WeightAt T1 NativeReads.F192 VS Digest ReplaySource.primitives.field.gf2_64.F64 Usize)
    (weight_at : T1) (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : ReplaySource.whir.config.Config) (c : Protocol.Config) (log_n : Usize) (hcfg : ConfigRel config c log_n)
    (s : Script NativeReads.F192 Usize Digest ReplaySource.primitives.field.gf2_64.F64) (n_lanes : Usize)
    (hch : (s.chal encode).valid c = true) (hS : ScriptShape index c s n_lanes.val) (hgs : GrindShape config s)
    (target : NativeReads.F192) (root : Digest) (v : VS) (rest : List NEvent)
    (hroot : ∀ (hl : 0 < s.levels.length), (s.levels[0]'hl).root = root)
    (hv : NativeAnswers out R H leaf node v (s.tape ++ rest)) :
    ∃ r v', ReplaySource.whir.verify.verify nativeInst W v config log_n n_lanes target root weight_at = .ok (r, v') ∧
      (r = .Ok () ↔ nativeVerify c (s.chal encode) n_lanes.val (encode target) callerAt
        (s.prf encode encodeK ofLimbs) = .ok ()) :=
  verify_eq nativeInst encode const encodeK ofLimbs index _ hw h hr hn
    (native_transcript hw hD hH hR hP encode) hclone hens W weight_at callerAt hcall
    config c log_n hcfg s n_lanes hch hS hgs target root v rest hroot hv

end Loop

/-! ## Authentication against committed trees -/

section Auth
variable {E : Type} (encode : E → Concrete.E) (encodeK : U64 → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)

/-- A committed oracle table: `2 ^ depth` rows, row `k` the model's reading of `C k`. -/
def tableOf (base : Bool) (depth : Nat) (C : Nat → List U64) : Protocol.Oracle :=
  ((List.range (2 ^ depth)).map fun k => encRow encodeK ofLimbs base (C k)).toArray

/-- Level `j`'s recorded depth. -/
def depthOf (s : Script E Usize Digest U64) (j : Nat) : Nat := (s.levels[j]?.map SLevel.depth).getD 0

/-- Under injective leaf and pair hashes: if every level's rows are opened by a hint against
the root of that level's committed tree `T j` over rows `C j`, the script's opening with the
committed tables satisfies `AuthenticatedRows` against the first table. -/
theorem authenticated_native (c : Protocol.Config) (s : Script E Usize Digest U64) (lanes : Nat)
    (hS : ScriptShape (fun q : Usize => q.val) c s lanes)
    (leaf : List U64 → Digest) (node : Digest → Digest → Digest)
    (hleaf : ∀ a b, leaf a = leaf b → a = b) (hnode : ∀ a b c d, node a b = node c d → a = c ∧ b = d)
    (C : Nat → Nat → List U64) (T : Nat → Nat → Nat → Digest)
    (hT0 : ∀ j (hj : j < s.levels.length) i, T j 0 i =
      leaf (List.replicate (s.levels[j].leafWords - s.levels[j].rowWords)
        ReplaySource.primitives.field.gf2_64.F64.ZERO ++ C j i))
    (hT : ∀ j l i, T j (l + 1) i = node (T j l (2 * i)) (T j l (2 * i + 1)))
    (hroots : ∀ j (hj : j < s.levels.length), s.levels[j].root = T j s.levels[j].depth 0)
    (hopen : ∀ j (hj : j < s.levels.length), ∃ hint, HintOpens leaf node s.levels[j].root s.levels[j].depth
      (s.levels[j].queries.map (·.val)) s.levels[j].rowWords s.levels[j].leafWords s.levels[j].rows hint) :
    AuthenticatedRows c (s.chal encode) (withOracles (s.prf encode encodeK ofLimbs)
      fun j => tableOf encodeK ofLimbs (j == 0) (depthOf s j) (C j))
      (tableOf encodeK ofLimbs true (depthOf s 0) (C 0)) := by
  have key := authenticated_withOracles encode encodeK ofLimbs (fun q : Usize => q.val) c s lanes hS
    (fun j => tableOf encodeK ofLimbs (j == 0) (depthOf s j) (C j)) ?_
  · simpa using key
  intro j hj i hi
  obtain ⟨hint, hh⟩ := hopen j hj
  rw [hroots j hj] at hh
  obtain ⟨hws, hin⟩ := hint_binding leaf node hleaf hnode _ _ _ _ _ hint (C j) (T j) (hT0 j hj) (hT j) hh
  have hiq : i < s.levels[j].queries.length := by rw [← hS.rows j hj]; exact hi
  have hrow : s.levels[j].rows[i] = C j (s.levels[j].queries[i]).val := by
    have := List.getElem_of_eq hws (i := i) hi
    simpa using this
  have hlt : (s.levels[j].queries[i]).val < 2 ^ depthOf s j := by
    rw [depthOf, List.getElem?_eq_getElem hj]
    exact hin _ (List.mem_map_of_mem (List.getElem_mem hiq))
  rw [hrow]
  simp only [tableOf]
  rw [getElem!_pos _ _ (by simpa using hlt)]
  simp

end Auth

/-- Every rows event a proof answers is opened by its hint. -/
theorem answers_rows {out : List DOp → Nat → List U8} {H : List U8 → Digest} {leaf : List U64 → Digest}
    {node : Digest → Digest → Digest} :
    ∀ (evs : List NEvent) (h : List DOp) (n hs : List U8), Answers out H leaf node h n hs evs →
      ∀ root depth qs rw lw ws, Event.rows root depth qs rw lw ws ∈ evs →
        ∃ hint, HintOpens leaf node root depth (qs.map (·.val)) rw lw ws hint := by
  intro evs
  induction evs with
  | nil => intro _ _ _ _ _ _ _ _ _ _ hm; simp at hm
  | cons e evs ih =>
    intro h n hs hA root depth qs rw lw ws hm
    rcases List.mem_cons.mp hm with he | htl
    · subst he
      simp only [Answers] at hA
      obtain ⟨_, hint, _, _, _, hh, _⟩ := hA
      exact ⟨hint, hh⟩
    · cases e with
      | sample _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | sampleVec _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | scalar _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | scalars _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | poly _ _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | root _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | grind b =>
        simp only [Answers] at hA
        by_cases hb : b = 0
        · exact ih _ _ _ (hA.2.1 hb) _ _ _ _ _ _ htl
        · exact ih _ _ _ (hA.2.2 hb).2.2.2 _ _ _ _ _ _ htl
      | queries _ _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2.2.2 _ _ _ _ _ _ htl
      | rows _ _ _ _ _ _ =>
        simp only [Answers] at hA
        obtain ⟨_, _, _, _, _, _, hrest⟩ := hA
        exact ih _ _ _ hrest _ _ _ _ _ _ htl

/-- The per-level accepting hints of `authenticated_native`, read off the proof that answers the
script: each level's rows event is in the script's reads, so its hint opens its rows. -/
theorem level_hints {out : List DOp → Nat → List U8} {R : ReplaySource.fiat_shamir.duplex.Blake2sDuplex → List DOp → Prop}
    {H : List U8 → Digest} {leaf : List U64 → Digest} {node : Digest → Digest → Digest}
    (s : Script NativeReads.F192 Usize Digest U64) (v : VS) (rest : List NEvent)
    (hv : NativeAnswers out R H leaf node v (s.tape ++ rest)) :
    ∀ j (hj : j < s.levels.length), ∃ hint, HintOpens leaf node s.levels[j].root s.levels[j].depth
      (s.levels[j].queries.map (·.val)) s.levels[j].rowWords s.levels[j].leafWords s.levels[j].rows hint := by
  intro j hj
  obtain ⟨_, h, _, hA⟩ := hv
  apply answers_rows _ h _ _ hA
  simp only [Script.tape, List.mem_append, List.mem_cons, List.mem_flatMap]
  refine Or.inl (Or.inr (Or.inl ⟨s.levels[j], List.getElem_mem hj, ?_⟩))
  simp [levelTape, batchTape]

end WhirAeneas.Native
