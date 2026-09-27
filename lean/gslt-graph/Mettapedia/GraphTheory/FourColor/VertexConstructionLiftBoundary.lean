import Mettapedia.GraphTheory.FourColor.VertexConstructionGSLT
import Mettapedia.GraphTheory.FourColor.FrontierVertexCode

/-!
# The boundary of unrestricted colouring-path lifting

The first two equal colours in an admissible word cannot enter one cubic
merge vertex. A legal structural step therefore need not extend every
admissible nonconstant boundary word. The obstruction concerns this universal
lifting requirement, not existence of a successful colouring construction.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexConstructionLiftBoundary

open VertexConstructionGSLT BoundaryWordFrontier

def repeatedPair : Fin 4 → Color := ![red, red, blue, blue]

theorem repeatedPair_required : Required repeatedPair := by
  unfold Required Admissible Nonconstant repeatedPair
  decide +kernel

theorem repeatedPair_no_merge (word : Fin 3 → Color) :
    ¬ colouring.Supports (single ⟨mergeCode 2, mergeCode_valid 2⟩) repeatedPair word := by
  intro supported
  have accepted := (supports_single_iff ⟨mergeCode 2, mergeCode_valid 2⟩
    repeatedPair word).mp supported
  have unequal := ((merge_accepts_iff 2 repeatedPair word repeatedPair_required.1.1).mp
    accepted).1
  exact unequal rfl

/-- Incidence-valid moves are not universally liftable even on the proposed
nonconstant, nonzero, zero-sum boundary invariant. -/
theorem not_every_required_word_lifts :
    ¬ (∀ source : Fin 4 → Color, Required source →
      ∃ target : Fin 3 → Color,
        colouring.Supports (single ⟨mergeCode 2, mergeCode_valid 2⟩) source target) := by
  intro lifting
  obtain ⟨target, supported⟩ := lifting repeatedPair repeatedPair_required
  exact repeatedPair_no_merge target supported

end Mettapedia.GraphTheory.FourColor.VertexConstructionLiftBoundary
