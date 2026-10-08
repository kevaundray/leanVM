import Whir.WHIRSourceChronology
import Whir.DuplexPublicSimulator

namespace Whir.WHIRSourceObserver
open FiatShamirGame DuplexModeGame
open WHIRSourceChronology

/-- Only the returned source trace and public observations are inspected. The current missing raw reply, and metadata derived after it, are excluded. -/
def publicEvents (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (view : View (Result cap R)) : List (Event cap) :=
  beforeAnswers (DuplexPublicSimulator.publicCut Q iv cache [] view.observations).length
    view.result.events

/-- The causal experiment can rerun its fixed source from its fixed simulator coins, but stops at the first unavailable raw answer. This definition has no total-oracle argument. -/
def privateEvents (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source) :
    List (Event cap) :=
  (recover source (DuplexPublicSimulator.runPartial cache iv
    ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
      ((compile_counted source Q).mpr counted)).observations).events

theorem publicEvents_actual (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (agrees : DuplexPublicSimulator.CacheAgrees cache ro)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source) :
    publicEvents Q iv cache (runIdeal (DuplexPublicSimulator.simulator Q) ro iv
      ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
        ((compile_counted source Q).mpr counted)).view =
      privateEvents Q iv cache seed source counted := by
  unfold publicEvents privateEvents
  have cut := DuplexPublicSimulator.publicCut_runPartial cache ro agrees iv
    ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
    ((compile_counted source Q).mpr counted)
  change DuplexPublicSimulator.publicCut Q iv cache [] _ = _ at cut
  rw [cut]
  apply beforeAnswers_ideal_prefix (DuplexPublicSimulator.simulator Q) ro iv
    ((DuplexPublicSimulator.simulator Q).initial seed) source Q (by omega) counted
  obtain ⟨suffix,eq⟩ := DuplexPublicSimulator.runPartial_prefix cache ro agrees iv
    ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
    ((compile_counted source Q).mpr counted)
  exact ⟨suffix,eq.symm⟩

/-- Failed commitment-order bookkeeping is sticky. Previously captured commitments remain available, but an invalid source chronology is never silently repaired by later announcements. -/
def replayTracked (state : CausalBindingState.State cap) :
    List (Event cap) → CausalBindingState.State cap
  | [] => state
  | event :: rest =>
      match state.sourceError with
      | some _ => state
      | none =>
          match step state event with
          | .error root => {state with sourceError := some root}
          | .ok next => replayTracked next rest

theorem replayTracked_extends (state : CausalBindingState.State cap) (events : List (Event cap)) :
    CausalBindingState.Extends state (replayTracked state events) := by
  induction events generalizing state with
  | nil => exact .refl _
  | cons event rest ih =>
      unfold replayTracked
      cases failed : state.sourceError with
      | some root => exact .refl _
      | none =>
          cases progress : step state event with
          | error root => exact ⟨fun _ _ h => h,fun _ _ h => h,fun _ _ _ => rfl,
              fun _ _ _ h => h,fun _ _ _ => rfl⟩
          | ok next => exact (step_extends state next event progress).trans (ih next)

theorem replayTracked_failed (state : CausalBindingState.State cap) (events : List (Event cap))
    (root : Digest32) (failed : state.sourceError = some root) :
    replayTracked state events = state := by
  cases events <;> simp [replayTracked,failed]

def publicReplay (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (view : View (Result cap R)) (state : CausalBindingState.State cap) :
    CausalBindingState.State cap :=
  replayTracked state (publicEvents Q iv cache view)

def privateReplay (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) : CausalBindingState.State cap :=
  replayTracked state (privateEvents Q iv cache seed source counted)

theorem publicReplay_actual (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (agrees : DuplexPublicSimulator.CacheAgrees cache ro)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) :
    publicReplay Q iv cache (runIdeal (DuplexPublicSimulator.simulator Q) ro iv
      ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
        ((compile_counted source Q).mpr counted)).view state =
      privateReplay Q iv cache seed source counted state := by
  unfold publicReplay privateReplay
  rw [publicEvents_actual Q iv cache ro agrees seed source counted]

theorem publicReplay_extends (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (view : View (Result cap R)) (state : CausalBindingState.State cap) :
    CausalBindingState.Extends state (publicReplay Q iv cache view state) :=
  replayTracked_extends _ _

theorem privateReplay_extends (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) :
    CausalBindingState.Extends state (privateReplay Q iv cache seed source counted state) :=
  replayTracked_extends _ _

end Whir.WHIRSourceObserver
