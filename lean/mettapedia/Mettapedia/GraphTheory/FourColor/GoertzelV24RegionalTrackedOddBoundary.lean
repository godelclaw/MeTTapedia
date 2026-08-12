import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteOddDegreeReachability
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabConnectivityProfile

/-!
# Odd endpoints of regional tracked strands

Restricting an ambient two-colour edge graph to a finite edge region can make
an even-degree strand endpoint odd only by removing an adjacent edge.  This
module states that parity fact in the exact `regionalTrackedEdgeGraph`
vocabulary used by corridor profiles.

The theorem deliberately stops at an ambient edge outside the region.  Naming
that edge as a source crossing, rail terminal, or cap foot is the subsequent
portal-classification geometry; parity alone must not manufacture a portal.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexSlabConnectivityProfile

open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

noncomputable local instance regionalTrackedOddBoundaryRegionalNeighborFintype
    (RS : RotationSystem V E) (region : Finset E) (color : E → Color)
    (first second : Color) (edge : E) :
    Fintype ((regionalTrackedEdgeGraph RS region color first second).neighborSet
      edge) := by
  classical
  exact Subtype.fintype _

noncomputable local instance regionalTrackedOddBoundaryAmbientNeighborFintype
    (RS : RotationSystem V E) (color : E → Color)
    (first second : Color) (edge : E) :
    Fintype ((RS.trackedEdgeGraph color first second).neighborSet edge) := by
  classical
  exact Subtype.fintype _

/-- An odd endpoint in the regional tracked graph, whose ambient tracked
degree is even, has a tracked neighbor outside the region. -/
theorem exists_trackedNeighbor_not_mem_region_of_odd_regional_degree
    (RS : RotationSystem V E) (region : Finset E)
    (color : E → Color) (first second : Color) (start : E)
    (hstart : start ∈ region)
    (hregionalOdd : Odd
      ((regionalTrackedEdgeGraph RS region color first second).degree start))
    (hambientEven : Even
      ((RS.trackedEdgeGraph color first second).degree start)) :
    ∃ neighbor : E,
      (RS.trackedEdgeGraph color first second).Adj start neighbor ∧
        neighbor ∉ region := by
  classical
  apply exists_ambient_adj_not_mem_of_odd_regional_degree
    (regional := regionalTrackedEdgeGraph RS region color first second)
    (ambient := RS.trackedEdgeGraph color first second)
    (region := (region : Set E)) (start := start)
    (hregionalOdd := hregionalOdd) (hambientEven := hambientEven)
  intro neighbor
  simp only [regionalTrackedEdgeGraph]
  constructor
  · rintro ⟨hadj, _hstart, hneighbor⟩
    exact ⟨hadj, hneighbor⟩
  · rintro ⟨hadj, hneighbor⟩
    exact ⟨hadj, hstart, hneighbor⟩

end

end GoertzelV24HexSlabConnectivityProfile

end Mettapedia.GraphTheory.FourColor
