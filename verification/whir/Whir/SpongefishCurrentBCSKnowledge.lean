import Whir.SpongefishCurrentRoundPackets
import Whir.SpongefishCurrentSourceJoinProbability
import Whir.PCSBCSSourceKnowledgeComposition
import Whir.PCSBCSChallengeOracleEnteredGames
import Whir.PCSBCSPublicPrimitiveOpening
import Whir.PCSBCSNativePhysicalMerkleBad

/-! Basic full-prefix BCS knowledge composition for the current #607 transcript
(`remark:bcs-with-basic-fs` of the pinned book source). The basic variant has
no hash-chain term, so the final bound has exactly three summands:

* the additive source RBR term `Q * rbrError` on the current round packets,
* the initialized byte-mode coupling `min(1,(2Q^2-Q)/2^256)`,
* the complete public Merkle trace alarm `(Q^3+3Q^2-2Q)/2^256`.

The generic part holds for any packet partition and node model with a proved
conditional hazard. The current instance uses `SpongefishCurrentRoundPackets`.
Two refinement obligations remain explicit hypotheses of the current endpoint:
real native acceptance with extraction failure reduces to a public good event
or the Merkle alarm, and the good event in every ideal table yields a state
path of the current node model. Neither is an assumed probability bound. -/
namespace Whir.SpongefishCurrentBCSKnowledge
open Concrete FiatShamirGame DuplexModeGame DuplexFraming RawOracleCoupling
open PCSBCSChallengeOracle PCSStateRestoration.Latent TypedOracleCompiler SpongefishPCSRoundFrames
set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## Generic packet composition -/

section Generic
variable {Packet : Type} [Fintype Packet] [DecidableEq Packet] {Block : Packet → Type}
  [∀ x, Fintype (Block x)] {Q : Nat}
  (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)

/-- The compiled source program with one grouped packet allocation at first
physical disclosure, exactly as in the whole-view coupling. -/
noncomputable def source {R : Type} (iv : Digest32) (program : Program R) (counted : Counts Q program) :
    Sampling part.Key (part.Answer (D := Digest32)) (View R) Q :=
  Atomic.program part (PublicCompressionCouplingMixed.compile Q iv [] program Q (by rfl) counted)

/-- Every ideal table on which the observer fires exposes a state path from an
undoomed to a doomed state. -/
def Refines {P R : Type} (model : NodeModel part.Key (part.Answer (D := Digest32)) P)
    (iv : Digest32) (program : Program R) (counted : Counts Q program) (observe : View R → Bool) :
    Prop :=
  ∀ table, observe (Sampling.eval table (source part iv program counted)) = true →
    StatePath model table (Sampling.execute table (source part iv program counted)).2 false true

private theorem average_indicator {T : Type} [Fintype T] (test : T → Bool) :
    average (fun t => if test t then (1 : ℚ) else 0) =
      Soundness.uniformProb (Finset.univ.filter fun t => test t = true) := by
  classical
  simp only [average,Soundness.uniformProb,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

variable [Fintype part.Key] [DecidableEq part.Key]
  [∀ key, Fintype (part.Answer (D := Digest32) key)] [∀ key, Nonempty (part.Answer (D := Digest32) key)]

open Classical in
/-- Ideal packet experiment: at most `Q * epsilon`. -/
theorem ideal_bound {P AdvCoins R : Type} [Fintype AdvCoins] [Nonempty AdvCoins]
    (model : NodeModel part.Key (part.Answer (D := Digest32)) P) (epsilon : ℚ)
    (nonnegative : 0 ≤ epsilon) (hazard : ConditionalHazard model epsilon) (iv : Digest32)
    (adversary : AdvCoins → Program R) (counted : ∀ a, Counts Q (adversary a))
    (observe : View R → Bool)
    (refines : ∀ a, Refines part model iv (adversary a) (counted a) observe) :
    atomicIdealProbability part iv adversary counted observe ≤ (Q : ℚ) * epsilon := by
  unfold atomicIdealProbability
  have each (a : AdvCoins) :
      Sampling.expectation (fun result => if observe result.1 then (1 : ℚ) else 0)
        (RawOracleCoupling.memo (source part iv (adversary a) (counted a)) (fun _ => none)) ≤
        (Q : ℚ) * epsilon := by
    have tableMemo := RawOracleCoupling.empty_table_eq_memo
      (source part iv (adversary a) (counted a)) (fun view => if observe view then (1 : ℚ) else 0)
    rw [← tableMemo,average_indicator]
    have bound := accepted_path_failure_probability model Q 0 (source part iv (adversary a) (counted a))
      epsilon nonnegative hazard
      (fun table => observe (Sampling.eval table (source part iv (adversary a) (counted a))) = true)
      (refines a)
    simp only [Nat.add_zero] at bound
    convert bound using 2
    ext t
    simp only [Finset.mem_filter]
  have summed := average_mono each
  rw [average_const] at summed
  convert summed using 1
  congr 1
  funext a
  unfold source
  congr 2 <;> exact Subsingleton.elim _ _

/-- Real primitive experiment: ideal packet bound plus the whole-view coupling. -/
theorem real_bound {P AdvCoins R : Type} [Fintype AdvCoins] [Nonempty AdvCoins]
    (model : NodeModel part.Key (part.Answer (D := Digest32)) P) (epsilon : ℚ)
    (nonnegative : 0 ≤ epsilon) (hazard : ConditionalHazard model epsilon) (iv : Digest32)
    (adversary : AdvCoins → Program R) (counted : ∀ a, Counts Q (adversary a))
    (observe : View R → Bool)
    (refines : ∀ a, Refines part model iv (adversary a) (counted a) observe) :
    realProbability iv adversary observe ≤ (Q : ℚ) * epsilon + duplexModeLoss Q := by
  have coupling := actual_source_atomic_game_bound part iv adversary counted observe
  have deviation := (abs_le.mp coupling).2
  have ideal := ideal_bound part model epsilon nonnegative hazard iv adversary counted observe refines
  linarith

end Generic

/-! ## Complete public Merkle trace alarm for an arbitrary root policy -/

noncomputable def merkleProbability {Coins R : Type} [Fintype Coins] {Q : Nat}
    (roots : PublicMerkleProbability.RootPolicy) (iv : Digest32)
    (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins)) : ℚ :=
  average fun coins => average fun C : PrimitiveOracle =>
    if PublicMerkleProbability.traceAlarm roots []
      (PublicCompressionProgram.primitiveLog C iv (adversary coins) Q (counted coins)) then 1 else 0

theorem merkle_bound {Coins R : Type} [Fintype Coins] [Nonempty Coins] {Q : Nat}
    (roots : PublicMerkleProbability.RootPolicy)
    (rootCap : ∀ log : PublicMerkleLog.PublicLog, log.length ≤ Q → (roots log).card ≤ Q*(Q+1))
    (iv : Digest32) (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins)) :
    merkleProbability roots iv adversary counted ≤ ((Q : ℚ)^3+3*(Q : ℚ)^2-2*(Q : ℚ))/2^256 := by
  unfold merkleProbability
  have each (coins : Coins) := PublicMerkleProbability.random_compression_bound roots Q (Q*(Q+1))
    rootCap (PublicCompressionProgram.compile iv (adversary coins) Q (counted coins))
  simp only [PublicMerkleProbability.alarm_trace] at each
  have bound := average_mono each
  rw [average_const,PCSBCSActualMerkleBound.exact_merkle_loss] at bound
  exact bound

/-- Pointwise reduction of an arbitrary real event to the public good event or
the complete Merkle trace alarm. -/
def Reduction {Coins R : Type} {Q : Nat} (roots : PublicMerkleProbability.RootPolicy) (iv : Digest32)
    (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins))
    (event : PrimitiveOracle → Coins → Prop) (good : View R → Bool) : Prop :=
  ∀ C coins, event C coins →
    good (runReal C iv (adversary coins)).view = true ∨
    PublicMerkleProbability.traceAlarm roots []
      (PublicCompressionProgram.primitiveLog C iv (adversary coins) Q (counted coins)) = true

open Classical in
theorem reduction_union {Coins R : Type} [Fintype Coins] [Nonempty Coins] {Q : Nat}
    (roots : PublicMerkleProbability.RootPolicy) (iv : Digest32)
    (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins))
    (event : PrimitiveOracle → Coins → Prop) (good : View R → Bool)
    (reduction : Reduction roots iv adversary counted event good) :
    average (fun coins : PrimitiveOracle × Coins => if event coins.1 coins.2 then (1 : ℚ) else 0) ≤
      realProbability iv adversary good + merkleProbability roots iv adversary counted := by
  unfold realProbability
  rw [distinguish_average (inferInstance : Fintype (PrimitiveOracle × Coins))]
  simp only [WHIRObservableSecurity.average_product]
  rw [RawOracleCoupling.average_comm (X := PrimitiveOracle) (Y := Coins),
    RawOracleCoupling.average_comm (X := PrimitiveOracle) (Y := Coins)]
  unfold merkleProbability
  rw [← average_add]
  apply average_mono
  intro coins
  rw [← average_add]
  apply average_mono
  intro C
  by_cases happened : event C coins
  · rcases reduction C coins happened with publicGood | alarm
    · simp only [happened,publicGood,↓reduceIte]
      split <;> norm_num
    · simp only [happened,alarm,↓reduceIte]
      split <;> norm_num
  · simp only [happened,↓reduceIte]
    split <;> split <;> norm_num

/-- Any program: an ordinary output collision in the PUBLIC log of the real view
raises the complete primitive trace alarm, for every root policy. The historical
packet partition is used only as a proof device; it is not part of the claim. -/
theorem collision_alarm {R : Type} (C : PrimitiveOracle) (iv : Digest32) (program : Program R)
    (Q : Nat) (counted : Counts Q program) (roots : PublicMerkleProbability.RootPolicy)
    (collision : PublicMerkleLog.OutputCollision
      (PCSBCSPublicPrimitiveOpening.publicOrdinaryLog Q iv (runReal C iv program).view)) :
    PublicMerkleProbability.traceAlarm roots []
      (PublicCompressionProgram.primitiveLog C iv program Q counted) = true := by
  have ordinary := PCSBCSPublicPrimitiveOpening.publicOrdinaryLog_actual
    (p := (⟨0,by decide⟩,⟨0,by decide⟩)) (iv := iv) (boundary := 0)
    C (WHIRRealSimulator.rawTable Q C) program Q (le_refl Q) counted
  simp only [Atomic.eval_program,Partition.join_split] at ordinary
  have view : Sampling.eval (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable Q C))
      (PublicCompressionCouplingMixed.compile Q iv [] program Q (le_refl Q) counted) =
      (runReal C iv program).view := by
    rw [PublicCompressionCouplingMixed.compile_actual]
    exact WHIRRealSimulator.runIdeal_view C iv _ ⟨rfl,by simp⟩ _ _ (le_refl Q) _
  rw [view] at ordinary
  rw [ordinary] at collision
  exact PCSBCSNativePhysicalMerkleBad.mixed_atomic_collision_alarm
    (p := (⟨0,by decide⟩,⟨0,by decide⟩)) (boundary := 0) C iv program Q (le_refl Q) counted roots
    collision

/-! ## Current #607 endpoint -/

section Current
open SpongefishCurrentRoundPackets SpongefishCurrentSourceJoinProbability
variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

noncomputable local instance (Q : Nat) (iv : Digest32) (grinding : Fin (cfg).folds.size → Fin 64)
    (boundary : Nat) (key : SpongefishCurrentRoundPackets.Key p Q iv grinding boundary) :
    Fintype (SpongefishCurrentRoundPackets.Answer p Q iv grinding boundary key) :=
  match key with
  | .inl _ => inferInstance
  | .inr _ => inferInstance

open Classical in
/-- The current #607 basic full-prefix knowledge endpoint. The real event is
native acceptance of the whole current caller path and opening, with the
property `Bad` (for example failed public extraction) of the prepared original.
Every summand of the bound is explicit; the two refinement obligations are
named hypotheses, not probability premises. -/
theorem current_knowledge_bound {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (decode : List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin))
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop)
    (boundary : Nat)
    (build : Builder p (budget tag instanceBytes layout before payloadCalls messages grinding A) iv
      grinding boundary)
    (good : View SourceResult → Bool)
    (roots : PublicMerkleProbability.RootPolicy)
    (rootCap : ∀ log : PublicMerkleLog.PublicLog,
      log.length ≤ budget tag instanceBytes layout before payloadCalls messages grinding A →
      (roots log).card ≤ budget tag instanceBytes layout before payloadCalls messages grinding A *
        (budget tag instanceBytes layout before payloadCalls messages grinding A + 1))
    (reduction : Reduction roots iv
      (fun coin => program iv tag instanceBytes layout before payloadCalls messages grinding
        (prefixProgram coin))
      (fun coin => SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
        (prefixProgram coin) (calls layout before payloadCalls messages grinding) A (attacker coin))
      (fun C coin => NativeAcceptedBad C iv tag instanceBytes layout before payloadCalls messages
        decode grinding (prefixProgram coin) Bad) good)
    (refines : ∀ coin, Refines (partition p (budget tag instanceBytes layout before payloadCalls
        messages grinding A) iv grinding boundary)
      (model p _ iv grinding boundary build) iv
      (program iv tag instanceBytes layout before payloadCalls messages grinding (prefixProgram coin))
      (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
        (prefixProgram coin) (calls layout before payloadCalls messages grinding) A (attacker coin))
      good) :
    let Q := budget tag instanceBytes layout before payloadCalls messages grinding A
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedBad coins.1 iv tag instanceBytes layout before payloadCalls messages decode
        grinding (prefixProgram coins.2) Bad then (1 : ℚ) else 0) ≤
      (Q : ℚ) * ((17/32 : ℚ)^56 + 1/2^78) + min 1 ((2*(Q : ℚ)^2-(Q : ℚ))/2^256) +
        ((Q : ℚ)^3+3*(Q : ℚ)^2-2*(Q : ℚ))/2^256 := by
  dsimp only
  classical
  have union := reduction_union roots iv _ _ _ good reduction
  have merkle := merkle_bound roots rootCap iv
    (fun coin => program iv tag instanceBytes layout before payloadCalls messages grinding
      (prefixProgram coin))
    (fun coin => SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
      (prefixProgram coin) (calls layout before payloadCalls messages grinding) A (attacker coin))
  have nonnegative : (0 : ℚ) ≤ PCSRoundByRoundKnowledge.rbrError := by
    unfold PCSRoundByRoundKnowledge.rbrError SupportedCandidateExtraction.radiusEnvelope
    positivity
  have real := real_bound _ _ PCSRoundByRoundKnowledge.rbrError nonnegative
    (conditional_hazard p _ iv grinding boundary build) iv _ _ good refines
  have rbr : PCSRoundByRoundKnowledge.rbrError = (17/32 : ℚ)^56 + 1/2^78 := by
    simp only [PCSRoundByRoundKnowledge.rbrError,SupportedCandidateExtraction.radiusEnvelope]
  rw [rbr,duplexModeLoss_eq] at real
  exact union.trans (add_le_add real merkle)

open Classical in
/-- Canonical public good event: the public original join with `Bad`, no
ordinary output collision in the public log, and a public opening predicate. -/
noncomputable def canonicalGood (Q : Nat) (iv : Digest32) (instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout)
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop)
    (quiet : View SourceResult → Bool) (view : View SourceResult) : Bool :=
  publicObserver Q iv instanceBytes layout Bad view &&
    decide (¬ PublicMerkleLog.OutputCollision
      (PCSBCSPublicPrimitiveOpening.publicOrdinaryLog Q iv view)) && quiet view

/-- The reduction obligation narrows to opening coverage: native acceptance
with `Bad` already gives the public join (`native_public`) and every public
ordinary collision raises the alarm (`collision_alarm`). -/
theorem reduction_of_openingCover {Coins : Type}
    (iv : Digest32) (tag instanceBytes : List Byte) (nonempty : instanceBytes ≠ [])
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (decode : List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin))
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop)
    (roots : PublicMerkleProbability.RootPolicy) (quiet : View SourceResult → Bool)
    (openingCover : ∀ C coin, NativeAcceptedBad C iv tag instanceBytes layout before payloadCalls
        messages decode grinding (prefixProgram coin) Bad →
      quiet (runReal C iv (program iv tag instanceBytes layout before payloadCalls messages grinding
        (prefixProgram coin))).view = false →
      PublicMerkleProbability.traceAlarm roots []
        (PublicCompressionProgram.primitiveLog C iv
          (program iv tag instanceBytes layout before payloadCalls messages grinding (prefixProgram coin))
          (budget tag instanceBytes layout before payloadCalls messages grinding A)
          (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
            (prefixProgram coin) (calls layout before payloadCalls messages grinding) A (attacker coin))) =
        true) :
    Reduction roots iv
      (fun coin => program iv tag instanceBytes layout before payloadCalls messages grinding
        (prefixProgram coin))
      (fun coin => SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
        (prefixProgram coin) (calls layout before payloadCalls messages grinding) A (attacker coin))
      (fun C coin => NativeAcceptedBad C iv tag instanceBytes layout before payloadCalls messages
        decode grinding (prefixProgram coin) Bad)
      (canonicalGood (budget tag instanceBytes layout before payloadCalls messages grinding A) iv
        instanceBytes layout Bad quiet) := by
  classical
  intro C coin native
  have joined := native_public C iv tag instanceBytes nonempty layout before payloadCalls messages
    beforeEq payloadEq decode grinding (prefixProgram coin) A (attacker coin) Bad native
  by_cases collision : PublicMerkleLog.OutputCollision
      (PCSBCSPublicPrimitiveOpening.publicOrdinaryLog
        (budget tag instanceBytes layout before payloadCalls messages grinding A) iv
        (runReal C iv (program iv tag instanceBytes layout before payloadCalls messages grinding
          (prefixProgram coin))).view)
  · exact Or.inr (collision_alarm C iv _ _ _ roots collision)
  · cases quietEq : quiet (runReal C iv (program iv tag instanceBytes layout before payloadCalls
        messages grinding (prefixProgram coin))).view with
    | false => exact Or.inr (openingCover C coin native quietEq)
    | true =>
      left
      simp only [canonicalGood,quietEq,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨decide_eq_true joined,collision⟩

open Classical in
/-- The current endpoint with the reduction narrowed to opening coverage. The
remaining obligations are `openingCover` (a native accepted opening whose
public opening predicate fails raises the Merkle trace alarm) and `Refines` for
the canonical good event. -/
theorem current_knowledge_cover {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (iv : Digest32) (tag instanceBytes : List Byte) (nonempty : instanceBytes ≠ [])
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (decode : List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin))
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop)
    (boundary : Nat)
    (build : Builder p (budget tag instanceBytes layout before payloadCalls messages grinding A) iv
      grinding boundary)
    (quiet : View SourceResult → Bool)
    (roots : PublicMerkleProbability.RootPolicy)
    (rootCap : ∀ log : PublicMerkleLog.PublicLog,
      log.length ≤ budget tag instanceBytes layout before payloadCalls messages grinding A →
      (roots log).card ≤ budget tag instanceBytes layout before payloadCalls messages grinding A *
        (budget tag instanceBytes layout before payloadCalls messages grinding A + 1))
    (openingCover : ∀ C coin, NativeAcceptedBad C iv tag instanceBytes layout before payloadCalls
        messages decode grinding (prefixProgram coin) Bad →
      quiet (runReal C iv (program iv tag instanceBytes layout before payloadCalls messages grinding
        (prefixProgram coin))).view = false →
      PublicMerkleProbability.traceAlarm roots []
        (PublicCompressionProgram.primitiveLog C iv
          (program iv tag instanceBytes layout before payloadCalls messages grinding (prefixProgram coin))
          (budget tag instanceBytes layout before payloadCalls messages grinding A)
          (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
            (prefixProgram coin) (calls layout before payloadCalls messages grinding) A (attacker coin))) =
        true)
    (refines : ∀ coin, Refines (partition p (budget tag instanceBytes layout before payloadCalls
        messages grinding A) iv grinding boundary)
      (model p _ iv grinding boundary build) iv
      (program iv tag instanceBytes layout before payloadCalls messages grinding (prefixProgram coin))
      (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
        (prefixProgram coin) (calls layout before payloadCalls messages grinding) A (attacker coin))
      (canonicalGood (budget tag instanceBytes layout before payloadCalls messages grinding A) iv
        instanceBytes layout Bad quiet)) :
    let Q := budget tag instanceBytes layout before payloadCalls messages grinding A
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedBad coins.1 iv tag instanceBytes layout before payloadCalls messages decode
        grinding (prefixProgram coins.2) Bad then (1 : ℚ) else 0) ≤
      (Q : ℚ) * ((17/32 : ℚ)^56 + 1/2^78) + min 1 ((2*(Q : ℚ)^2-(Q : ℚ))/2^256) +
        ((Q : ℚ)^3+3*(Q : ℚ)^2-2*(Q : ℚ))/2^256 :=
  current_knowledge_bound iv tag instanceBytes layout before payloadCalls messages decode grinding
    prefixProgram A attacker Bad boundary build _ roots rootCap
    (reduction_of_openingCover iv tag instanceBytes nonempty layout before payloadCalls messages
      beforeEq payloadEq decode grinding prefixProgram A attacker Bad roots quiet openingCover)
    refines

end Current

/-! ## Concrete level from the deployed parameters -/

/-- The three explicit summands of the current endpoint. -/
def finalBound (Q : ℚ) : ℚ :=
  Q * ((17/32 : ℚ)^56 + 1/2^78) + min 1 ((2*Q^2-Q)/2^256) + (Q^3+3*Q^2-2*Q)/2^256

/-- For every aggregate budget up to `2^64` primitive-work units the complete
bound is at most `Q / 2^51`: each unit of attacker plus verifier work buys at
most `2^-51` knowledge error, with no proof-of-work credit. -/
theorem finalBound_le (Q : ℚ) (positive : 0 ≤ Q) (cap : Q ≤ 2^64) : finalBound Q ≤ Q / 2^51 := by
  unfold finalBound
  have square : Q^2 ≤ 2^64 * Q := by nlinarith
  have cube : Q^3 ≤ 2^128 * Q := by nlinarith
  have coupling : min 1 ((2*Q^2-Q)/2^256) ≤ (2*Q^2-Q)/2^256 := min_le_right _ _
  have numeric : (17/32 : ℚ)^56 + 1/2^78 + 2*2^64/2^256 + (2^128+3*2^64)/2^256 ≤ 1/2^51 := by
    norm_num
  nlinarith

/-- Concrete levels: `2^20` units give at most `2^-31`, `2^40` units at most `2^-11`. -/
theorem finalBound_levels :
    finalBound (2^20) ≤ 1/2^31 ∧ finalBound (2^40) ≤ 1/2^11 := by
  constructor
  · have h := finalBound_le (2^20) (by norm_num) (by norm_num)
    calc finalBound (2^20) ≤ 2^20/2^51 := h
      _ = 1/2^31 := by norm_num
  · have h := finalBound_le (2^40) (by norm_num) (by norm_num)
    calc finalBound (2^40) ≤ 2^40/2^51 := h
      _ = 1/2^11 := by norm_num

/-- Deployed query grinding: `QUERY_GRINDING_BITS = 17` at every level. -/
def deployedGrinding (p : ParameterBounds.Profile) : Fin (ParameterBounds.config p).folds.size → Fin 64 :=
  fun _ => ⟨17,by decide⟩

open Classical SpongefishCurrentRoundPackets SpongefishCurrentSourceJoinProbability in
/-- The current endpoint at the deployed grinding, evaluated numerically: with
an aggregate budget of at most `2^64` units the real probability of native
acceptance with `Bad` is at most `Q / 2^51`, under the same two refinement
obligations. -/
theorem current_knowledge_level {p : ParameterBounds.Profile} {Coins : Type} [Fintype Coins]
    [Nonempty Coins] (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (decode : List Byte → Option MerkleTransport.PrunedMerklePaths)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin))
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop)
    (boundary : Nat)
    (build : Builder p (budget tag instanceBytes layout before payloadCalls messages
      (deployedGrinding p) A) iv (deployedGrinding p) boundary)
    (good : View SourceResult → Bool)
    (roots : PublicMerkleProbability.RootPolicy)
    (rootCap : ∀ log : PublicMerkleLog.PublicLog,
      log.length ≤ budget tag instanceBytes layout before payloadCalls messages (deployedGrinding p) A →
      (roots log).card ≤ budget tag instanceBytes layout before payloadCalls messages (deployedGrinding p) A *
        (budget tag instanceBytes layout before payloadCalls messages (deployedGrinding p) A + 1))
    (reduction : Reduction roots iv
      (fun coin => program iv tag instanceBytes layout before payloadCalls messages (deployedGrinding p)
        (prefixProgram coin))
      (fun coin => SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
        (prefixProgram coin) (calls layout before payloadCalls messages (deployedGrinding p)) A
        (attacker coin))
      (fun C coin => NativeAcceptedBad C iv tag instanceBytes layout before payloadCalls messages
        decode (deployedGrinding p) (prefixProgram coin) Bad) good)
    (refines : ∀ coin, Refines (partition p (budget tag instanceBytes layout before payloadCalls
        messages (deployedGrinding p) A) iv (deployedGrinding p) boundary)
      (model p _ iv (deployedGrinding p) boundary build) iv
      (program iv tag instanceBytes layout before payloadCalls messages (deployedGrinding p)
        (prefixProgram coin))
      (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
        (prefixProgram coin) (calls layout before payloadCalls messages (deployedGrinding p)) A
        (attacker coin))
      good)
    (cap : budget tag instanceBytes layout before payloadCalls messages (deployedGrinding p) A ≤ 2^64) :
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedBad coins.1 iv tag instanceBytes layout before payloadCalls messages decode
        (deployedGrinding p) (prefixProgram coins.2) Bad then (1 : ℚ) else 0) ≤
      (budget tag instanceBytes layout before payloadCalls messages (deployedGrinding p) A : ℚ) / 2^51 := by
  have bound := current_knowledge_bound iv tag instanceBytes layout before payloadCalls messages decode
    (deployedGrinding p) prefixProgram A attacker Bad boundary build good roots rootCap reduction refines
  have numeric := finalBound_le
    (budget tag instanceBytes layout before payloadCalls messages (deployedGrinding p) A : ℚ)
    (by positivity) (by exact_mod_cast cap)
  unfold finalBound at numeric
  exact bound.trans numeric

#print axioms ideal_bound
#print axioms real_bound
#print axioms merkle_bound
#print axioms reduction_union
#print axioms current_knowledge_bound
#print axioms finalBound_le
#print axioms finalBound_levels
#print axioms current_knowledge_level
#print axioms collision_alarm
#print axioms reduction_of_openingCover
#print axioms current_knowledge_cover

end Whir.SpongefishCurrentBCSKnowledge
