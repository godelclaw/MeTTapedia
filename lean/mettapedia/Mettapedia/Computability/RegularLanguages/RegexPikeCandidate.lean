import Mettapedia.Computability.RegularLanguages.RegexPikeSimple
import Mettapedia.Computability.RegularLanguages.RegexPriorityCycleCut

/-!
# A globally least candidate survives the actual remaining Pike execution

Active threads before a saved terminal have strictly preferred histories.
If any later phase produced another acceptance, its independent simple trace
would contradict global leastness. Thus the actual driver retains the saved
candidate; the argument does not mistake provisional acceptance for completion.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPikeCandidate

open RegexTaggedGraph RegexSelectionCorrespondence RegexPikeSelection RegexPikeSimple
open RegexClosureComposition RegexPriorityCycleCut
open OrderedGraphSearch (Point Probe)
open RegexMatchObservations (HigherPriority)

universe u v w z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

theorem higher_after_edge (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first target reference : Thread State length)
    (higher : HigherPriority first.choices reference.choices) (edge : target ∈ edges graph probe first) :
    HigherPriority target.choices reference.choices := by
  obtain ⟨code, history⟩ := prefix_of_edge graph probe first target edge
  rw [history.choices]
  simpa only [List.append_nil] using priority_append higher code []

theorem least_rejects_higher_accept (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool)
    (initial reference candidate : Thread State length) (tag : Tag)
    (least : LeastSimple graph probe eligible initial reference)
    (accepted : SimpleAccept graph probe eligible initial candidate tag) :
    ¬ HigherPriority candidate.choices reference.choices := by
  intro higher
  obtain ⟨referenceCode, referencePoints, referenceTag, referenceTrace, _, minimal⟩ := least
  obtain ⟨code, points, trace, simple⟩ := accepted
  rw [trace.choices, referenceTrace.choices] at higher
  have priority := priority_cancel_common_prefix initial.choices higher
  rcases minimal code points candidate tag trace simple with same | reverse
  · exact higherPriority_irrefl code (by simpa only [same] using priority)
  · exact higherPriority_asymm priority reverse

/-- Once the globally least independent reference is the saved candidate,
the actual remaining execute call cannot replace it. Completing the call is
still required: a cutoff is not promoted to a successful retained result. -/
theorem retain_least_candidate [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (initial reference : Thread State length) (tag : Tag)
    (least : LeastSimple graph probe (fun thread => eligible thread.point) initial reference)
    (closureFuel fuel : Nat) :
    ∀ pending selected,
      (∀ thread ∈ pending, History graph probe initial ∅ thread) →
      (∀ thread ∈ pending, HigherPriority thread.choices reference.choices) →
      RegexPikeVM.execute (fun thread => thread.point.1) (epsilonChildren graph probe)
        (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
        (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
        closureFuel fuel pending (some (reference, tag)) = .finished selected →
      selected = some (reference, tag) := by
  induction fuel with
  | zero => intro pending selected histories preferred finished; cases finished
  | succ fuel ih =>
      intro pending selected histories preferred finished
      cases closed : firstVisits (fun thread : Thread State length => thread.point.1)
          (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
          closureFuel pending ∅ with
      | none => simp [RegexPikeVM.execute, closed] at finished
      | some frontier =>
          obtain ⟨final, derivation⟩ := firstVisits_derivation closureFuel pending ∅ frontier closed
          have frontierHistories := closure_simple graph probe initial derivation histories
          have frontierPreferred : ∀ thread ∈ frontier,
              HigherPriority thread.choices reference.choices := by
            have sound := firstVisits_sound (fun thread : Thread State length => thread.point.1)
              (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
              (fun thread => HigherPriority thread.choices reference.choices)
              (fun source valid target edge => higher_after_edge graph probe source target reference valid
                (epsilon_edge graph probe source target edge)) closureFuel pending ∅ frontier preferred closed
            exact fun thread member => (sound thread member).1
          let active := (RegexPikeVM.candidates (RegexPikeVM.terminal graph)
            (fun thread => eligible thread.point) frontier).1
          let candidate := (RegexPikeVM.candidates (RegexPikeVM.terminal graph)
            (fun thread => eligible thread.point) frontier).2
          let advancing := active.flatMap (edges graph probe)
          have candidateAbsent : candidate = none := by
            cases found : candidate with
            | none => rfl
            | some pair =>
                have member := RegexPikeVM.candidates_selected_sound (RegexPikeVM.terminal graph)
                  (fun thread => eligible thread.point) frontier pair.1 pair.2 found
                have accepted : SimpleAccept graph probe (fun thread => eligible thread.point) initial pair.1 pair.2 :=
                  (frontierHistories pair.1 member.1).1.accepted member.2.1 member.2.2
                exact False.elim (least_rejects_higher_accept graph probe (fun thread => eligible thread.point)
                  initial reference pair.1 pair.2 least accepted (frontierPreferred pair.1 member.1))
          have advancingHistories : ∀ thread ∈ advancing, History graph probe initial ∅ thread := by
            intro thread member
            obtain ⟨source, sourceMember, edge⟩ := List.mem_flatMap.mp member
            have activeSource := RegexPikeVM.candidates_active_mem (RegexPikeVM.terminal graph)
              (fun thread => eligible thread.point) frontier source sourceMember
            have sourceHistory := frontierHistories source activeSource.1
            have advances := (RegexPikeVM.active_consume_bounds graph probe source sourceHistory.2
              activeSource.2).2 thread edge
            exact sourceHistory.1.consume edge (by omega)
          have advancingPreferred : ∀ thread ∈ advancing,
              HigherPriority thread.choices reference.choices := by
            intro thread member
            obtain ⟨source, sourceMember, edge⟩ := List.mem_flatMap.mp member
            have activeSource := RegexPikeVM.candidates_active_mem (RegexPikeVM.terminal graph)
              (fun thread => eligible thread.point) frontier source sourceMember
            exact higher_after_edge graph probe source thread reference
              (frontierPreferred source activeSource.1) edge
          simp only [RegexPikeVM.execute, closed] at finished
          change (if advancing.isEmpty then RegexPikeVM.Result.finished (candidate.or (some (reference, tag)))
            else RegexPikeVM.execute (fun thread => thread.point.1) (epsilonChildren graph probe)
              (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
              (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
              closureFuel fuel advancing (candidate.or (some (reference, tag)))) =
              .finished selected at finished
          rw [candidateAbsent, Option.none_or] at finished
          cases empty : advancing.isEmpty with
          | true =>
              simp only [empty, ↓reduceIte, RegexPikeVM.Result.finished.injEq] at finished
              exact finished.symm
          | false =>
              simp only [empty, Bool.false_eq_true, ↓reduceIte] at finished
              exact ih advancing selected advancingHistories advancingPreferred finished

end Mettapedia.Computability.RegularLanguages.RegexPikeCandidate
