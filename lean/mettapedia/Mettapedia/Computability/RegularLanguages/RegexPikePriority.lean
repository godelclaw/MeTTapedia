import Mettapedia.Computability.RegularLanguages.RegexPikeCoverage
import Mettapedia.Computability.RegularLanguages.RegexPikePrefix

/-!
# Independent evidence for preferred-root dominance

A finite accepting trace is enough to establish a successful preferred root.
The actual driver then retains that root's complete selected snapshot when
later roots or a provisional later candidate are present. This is a root-list
priority result, not the full graph-path minimality theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPikePriority

open RegexTaggedGraph RegexSelectionCorrespondence
open OrderedGraphSearch (Point Probe)

universe u v w z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

/-- Actual first-root dominance is justified by an independent accepting
trace, not by assuming that the combined execution chose the desired answer.
Completion of the combined call is kept explicit. -/
theorem accepting_first_root_dominates [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel)
    (preferred : Thread State length) (later : List (Thread State length))
    (previous selected : Option (Thread State length × Tag))
    {code : List Bool} {points : List (Point State length)} {last : Thread State length} {tag : Tag}
    (evidence : Trace graph probe (fun thread => eligible thread.point) preferred code points last tag)
    (completed : RegexPikeVM.execute (fun thread => thread.point.1) (epsilonChildren graph probe)
      (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
      (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
      closureFuel inputFuel (preferred :: later) previous = .finished selected) :
    ∃ winner,
      RegexPikeVM.run graph probe (fun thread => eligible thread.point)
        closureFuel inputFuel [preferred] = .finished (some winner) ∧ selected = some winner := by
  have sufficient := RegexPikeVM.run_ne_incomplete graph probe (fun thread => eligible thread.point)
    preferred closureFuel inputFuel closureEnough inputEnough
  cases result : RegexPikeVM.run graph probe (fun thread => eligible thread.point)
      closureFuel inputFuel [preferred] with
  | incomplete => exact False.elim (sufficient result)
  | finished candidate =>
      cases candidate with
      | none =>
          exact False.elim (RegexPikeCoverage.run_none_excludes_trace graph probe eligible
            closureFuel inputFuel preferred result code points last tag evidence)
      | some winner =>
          refine ⟨winner, rfl, ?_⟩
          exact RegexPikePrefix.execute_prefix_success (fun thread : Thread State length => thread.point.1)
            (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
            (edges graph probe) (RegexPikeVM.terminal graph) (fun thread => eligible thread.point)
            closureFuel inputFuel [preferred] later previous winner selected result completed

end Mettapedia.Computability.RegularLanguages.RegexPikePriority
