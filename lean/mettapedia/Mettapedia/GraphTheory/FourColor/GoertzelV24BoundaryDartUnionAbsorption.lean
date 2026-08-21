import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryDartOpposite
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSetRegionUnion

/-!
# Opposite boundary darts are absorbed by the joined vertex side

This file records one generic L1 portal-cancellation atom.  If two exposed
boundary darts lie on opposite orientations of the same ambient edge, then
the two dart bases are the two endpoints of that edge.  Consequently the
edge is internal after the two retained vertex sides are joined, and it is
absent from the joined side's true crossing frontier.

The result needs neither cubicity nor a source-corridor hypothesis.  It does
not construct opposite darts: a source realization must still prove the
`alpha` equation for each matched interface edge.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationCutDartDecomposition

open GoertzelV24RotationVertexCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The edge exposed by two alpha-opposite boundary darts has both endpoints
in the union of their retained vertex sides. -/
theorem edgeOf_endpoints_subset_union_of_alpha_eq_boundaryDart
    (RS : RotationSystem V E) (leftInside rightInside : Finset V)
    (left : BoundaryDart RS (fun vertex => vertex ∈ leftInside))
    (right : BoundaryDart RS (fun vertex => vertex ∈ rightInside))
    (halpha : RS.alpha left.1.1 = right.1.1) :
    RS.endpoints (RS.edgeOf left.1.1) ⊆ leftInside ∪ rightInside := by
  rw [RS.endpoints_eq_pair_of_mem (RS.mem_dartsOn.2 rfl)]
  intro vertex hvertex
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvertex
  rcases hvertex with hleft | hright
  · rw [hleft]
    exact Finset.mem_union_left _ left.1.2
  · rw [hright, halpha]
    exact Finset.mem_union_right _ right.1.2

/-- An alpha-opposite matched interface edge disappears from the true
crossing frontier after the two vertex sides are joined. -/
theorem edgeOf_not_mem_vertexSetCrossingEdges_union_of_alpha_eq_boundaryDart
    (RS : RotationSystem V E) (leftInside rightInside : Finset V)
    (left : BoundaryDart RS (fun vertex => vertex ∈ leftInside))
    (right : BoundaryDart RS (fun vertex => vertex ∈ rightInside))
    (halpha : RS.alpha left.1.1 = right.1.1) :
    RS.edgeOf left.1.1 ∉
      vertexSetCrossingEdges RS (leftInside ∪ rightInside) := by
  exact not_mem_vertexSetCrossingEdges_of_endpoints_subset
    RS (leftInside ∪ rightInside) (RS.edgeOf left.1.1)
    (edgeOf_endpoints_subset_union_of_alpha_eq_boundaryDart
      RS leftInside rightInside left right halpha)

end

end GoertzelV24RotationCutDartDecomposition

end Mettapedia.GraphTheory.FourColor
