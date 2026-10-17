import Mettapedia.Computability.RegularLanguages.RegexEpsilonFirstArrival
import Mettapedia.Computability.RegularLanguages.RegexPikeSelection

/-!
# Actual phase owners precede independent reference arrivals

Ordered roots and the independently proved first-arrival theorem identify the
actual retained snapshot. If a simple reference arrival is not retained
literally, its retained competitor has strictly preferred branch history.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPhaseComparison

open RegexTaggedGraph RegexSelectionCorrespondence RegexPikeSelection RegexClosureComposition
open RegexEpsilonFirstArrival
open OrderedGraphSearch (Point Probe)
open RegexMatchObservations (HigherPriority)

universe u v w z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

/-- This comparison concerns the actual finite closure, not a hypothetical
preferred scheduler. Capture equality is literal when the reference wins. -/
theorem owner_precedes_reference [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (pending : List (Thread State length))
    (position : Fin (length + 1)) (output : List (Thread State length)) (final : Finset State)
    (owner referenceRoot reference : Thread State length)
    (closed : Closure (fun thread : Thread State length => thread.point.1)
      (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
      pending ∅ output final)
    (samePosition : ∀ thread ∈ pending, thread.point.2 = position)
    (selected : (RegexPikeVM.candidates (RegexPikeVM.terminal (phaseGraph graph))
      (fun thread => eligible thread.point) output).2 = some (owner, owner.point.1))
    (ordered : pending.Pairwise (fun first second => HigherPriority first.choices second.choices))
    (member : referenceRoot ∈ pending) (referenceCode : List Bool)
    (referencePoints : List (Point State length)) (referenceTag : State)
    (referenceTrace : Trace (phaseGraph graph) probe (fun thread => eligible thread.point)
      referenceRoot referenceCode referencePoints reference referenceTag)
    (referenceSimple : referencePoints.Nodup) :
    owner = reference ∨ HigherPriority owner.choices reference.choices := by
  obtain ⟨before, root, after, pendingSame, ownerLeast, earlierDead⟩ :=
    closed_roots_first_arrival graph probe eligible pending position output final owner
      closed samePosition selected
  obtain ⟨ownerCode, ownerPoints, ownerTag, ownerTrace, _, minimal⟩ := ownerLeast
  rw [pendingSame, List.mem_append, List.mem_cons] at member
  rcases member with earlier | same | later
  · exact False.elim (earlierDead referenceRoot earlier
      ⟨referenceCode, referencePoints, reference, referenceTag, referenceTrace⟩)
  · subst referenceRoot
    rcases minimal referenceCode referencePoints reference referenceTag referenceTrace referenceSimple with
      equal | priority
    · exact Or.inl (ownerTrace.prefix_free referenceTrace (Or.inl (by simp [equal]))).2.1
    · apply Or.inr
      rw [ownerTrace.choices, referenceTrace.choices]
      exact priority_common_prefix root.choices priority
  · have suffixOrdered := (List.pairwise_append.mp (pendingSame ▸ ordered)).2.1
    have rootBefore := (List.pairwise_cons.mp suffixOrdered).1 referenceRoot later
    apply Or.inr
    rw [ownerTrace.choices, referenceTrace.choices]
    exact priority_append rootBefore ownerCode referenceCode

end Mettapedia.Computability.RegularLanguages.RegexPhaseComparison
