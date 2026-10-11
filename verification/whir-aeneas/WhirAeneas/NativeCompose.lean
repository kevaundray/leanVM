import WhirAeneas.MerkleRows
import WhirAeneas.Authenticated

/-! The composed theorem for the native opening verifier, without assuming its rows read. The
opening verifier's `open_rows` is the extracted native `open_rows_native` (`NativeOpenRows`), and
each rows event of the tape is answered by a length-prefixed hint whose content opens the
event's rows (`NativeTape`, with `HintOpens`); under the leaf and pair hash content contracts
(`RowHash`, `PairHash`) these give the rows read of `Transcript`, so `verify_eq` holds with the
remaining reads (`Reads`) as its only transcript premise. Under injective leaf and pair hashes,
openings against committed trees authenticate the script's rows: `AuthenticatedRows` holds for
the script's opening with the committed tables. -/
namespace WhirAeneas.Native
open Aeneas Aeneas.Std Whir Whir.Concrete Whir.WHIRNativeArithmetic WhirAeneas.Merkle
  WhirAeneas.MerkleNative WhirAeneas.Replay WhirAeneas.Fold WhirAeneas.Query

/-- The replay extraction's copy of a transcript error from the Merkle extraction. -/
def errOf : MerkleSource.fiat_shamir.error.TranscriptError → ReplaySource.fiat_shamir.error.TranscriptError
  | .Malformed i => .Malformed i
  | .MissingHint i => .MissingHint i
  | .InvalidHint i => .InvalidHint i
  | .PowFailed b => .PowFailed b
  | .TrailingBytes a b => .TrailingBytes a b

/-- A result with its error carried across. -/
def resOf {T : Type} : core.result.Result T MerkleSource.fiat_shamir.error.TranscriptError →
    core.result.Result T ReplaySource.fiat_shamir.error.TranscriptError
  | .Ok x => .Ok x
  | .Err e => .Err (errOf e)

/-- The opening verifier's `open_rows` is the extracted native one (the body of
`OpeningVerifier::open_rows` for `VerifierState`), up to the copy of its error type. -/
def NativeOpenRows {E : Type} (inst : ReplaySource.verifier.OpeningVerifier VS Digest U64 Usize E) : Prop :=
  ∀ v root depth queries a b, inst.open_rows v root depth queries a b = (do
    let (r, v') ← MerkleSource.verifier.open_rows_native v root depth queries a b
    .ok (resOf r, v'))

/-- Every rows event of the tape is the next hint of an unpoisoned transcript, length-prefixed
as the prover writes it, whose content opens the event's rows against its root over `2 ^ depth`
leaves; the transcript after the hint answers the rest. -/
def NativeTape {E : Type} (leaf : List U64 → Digest) (node : Digest → Digest → Digest)
    (tape : VS → List (Event E Usize Digest U64)) : Prop :=
  ∀ v root depth qs rw lw ws rest, tape v = .rows root depth qs rw lw ws :: rest →
    v.poison = none ∧ ∃ (L : U32) (hint more : Slice U8), L.val = hint.val.length ∧
      v.hints.val = (core.num.U32.to_le_bytes L).val ++ hint.val ++ more.val ∧
      tape { v with hints := more, hints_read := Std.Usize.wrapping_add v.hints_read 1#usize } = rest ∧
      HintOpens leaf node root depth (qs.map (·.val)) rw lw ws hint.val

/-- The rows read of `Transcript` for the native opening verifier. -/
theorem transcript_native (hword : UScalarTy.Usize.numBits = 64) {E : Type}
    (inst : ReplaySource.verifier.OpeningVerifier VS Digest U64 Usize E) (encode : E → Concrete.E)
    (tape : VS → List (Event E Usize Digest U64)) {leaf : List U64 → Digest} {node : Digest → Digest → Digest}
    (hR : RowHash leaf) (hP : PairHash node) (ht : Reads inst encode tape) (hnat : NativeOpenRows inst)
    (htape : NativeTape leaf node tape) : Transcript inst encode tape := by
  refine { ht with rows := ?_ }
  intro v root depth queries a b ws rest hv
  obtain ⟨hp, L, hint, more, hL, hb, hrest, hh⟩ := htape v root depth.val queries.val a.val b.val ws rest hv
  obtain ⟨rows, hrun, erows⟩ := open_rows_ok hword hR hP v hp root depth queries a b L hint more hL hb ws hh
  refine ⟨rows, _, ?_, erows, hrest⟩
  rw [hnat, hrun]
  simp [resOf]

section Loop
variable {E : Type} (inst : ReplaySource.verifier.OpeningVerifier VS Digest U64 Usize E)
  (encode : E → Concrete.E) (const : ReplaySource.primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : U64 → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Usize → Nat) (tape : VS → List (Event E Usize Digest U64))

/-- The composed theorem for the native opening verifier: `verify_eq` with the rows read derived
from the extracted native `open_rows`, the hint content of each rows event and the hash content
contracts, instead of assumed. -/
theorem verify_eq_native {T1 : Type} (hw : System.Platform.numBits = 64)
    (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (ht : Reads inst encode tape) (hnat : NativeOpenRows inst)
    {leaf : List U64 → Digest} {node : Digest → Digest → Digest} (hR : RowHash leaf) (hP : PairHash node)
    (htape : NativeTape leaf node tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : ReplaySource.whir.verify.WeightAt T1 E VS Digest U64 Usize)
    (weight_at : T1) (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : ReplaySource.whir.config.Config) (c : Protocol.Config) (log_n : Usize) (hcfg : ConfigRel config c log_n)
    (s : Script E Usize Digest U64) (n_lanes : Usize) (hch : (s.chal encode).valid c = true)
    (hS : ScriptShape index c s n_lanes.val) (target : E) (root : Digest) (v : VS)
    (rest : List (Event E Usize Digest U64))
    (hroot : ∀ (hl : 0 < s.levels.length), (s.levels[0]'hl).root = root)
    (hv : tape v = s.tape ++ rest) :
    ∃ r v', ReplaySource.whir.verify.verify inst W v config log_n n_lanes target root weight_at = .ok (r, v') ∧
      (r = .Ok () ↔ nativeVerify c (s.chal encode) n_lanes.val (encode target) callerAt
        (s.prf encode encodeK ofLimbs) = .ok ()) :=
  have hword : UScalarTy.Usize.numBits = 64 := by simp only [UScalarTy.numBits]; exact hw
  verify_eq inst encode const encodeK ofLimbs index tape hw h hr hn
    (transcript_native hword inst encode tape hR hP ht hnat htape) hclone hens W weight_at callerAt hcall
    config c log_n hcfg s n_lanes hch hS target root v rest hroot hv

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
      leaf (List.replicate (s.levels[j].leafWords - s.levels[j].rowWords) MerkleSource.primitives.field.gf2_64.F64.ZERO ++ C j i))
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

end WhirAeneas.Native
