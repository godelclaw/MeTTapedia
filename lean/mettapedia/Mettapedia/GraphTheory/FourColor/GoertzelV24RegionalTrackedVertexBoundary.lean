import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalTrackedOddBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile

/-!
# Odd tracked endpoints reach a vertex-side boundary

For a region induced by a finite set of rotation-system vertices, parity has
a literal geometric consequence.  An edge of odd degree in the regional
two-colour graph but even degree in the ambient two-colour graph must cross
the vertex cut: the missing tracked neighbour supplies an outside endpoint,
while regional membership supplies an inside endpoint.

Combining this localization with componentwise handshaking gives a distinct
reachable crossing edge.  These are generic boundary theorems; identifying
the crossing edge with one of a source corridor's named portals remains the
source-specific portal-classification step.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexSlabConnectivityProfile

open GoertzelV24RotationVertexCutProfile
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

noncomputable local instance regionalTrackedVertexBoundaryRegionalNeighborFintype
    (RS : RotationSystem V E) (inside : Finset V) (color : E → Color)
    (first second : Color) (edge : E) :
    Fintype ((regionalTrackedEdgeGraph RS
      (vertexSetRegionEdges RS inside) color first second).neighborSet edge) := by
  classical
  exact Subtype.fintype _

noncomputable local instance regionalTrackedVertexBoundaryAmbientNeighborFintype
    (RS : RotationSystem V E) (color : E → Color)
    (first second : Color) (edge : E) :
    Fintype ((RS.trackedEdgeGraph color first second).neighborSet edge) := by
  classical
  exact Subtype.fintype _

/-- Odd regional tracked degree and even ambient tracked degree force an edge
to cross the underlying vertex side. -/
theorem mem_vertexSetCrossingEdges_of_odd_regional_degree
    (RS : RotationSystem V E) (inside : Finset V)
    (color : E → Color) (first second : Color) (edge : E)
    (hregionalOdd : Odd ((regionalTrackedEdgeGraph RS
      (vertexSetRegionEdges RS inside) color first second).degree edge))
    (hambientEven : Even
      ((RS.trackedEdgeGraph color first second).degree edge)) :
    edge ∈ vertexSetCrossingEdges RS inside := by
  classical
  let regional := regionalTrackedEdgeGraph RS
    (vertexSetRegionEdges RS inside) color first second
  have hregionalOdd' : Odd (regional.degree edge) := by
    simpa [regional] using hregionalOdd
  have hdegreePositive : 0 < regional.degree edge := by
    rcases hregionalOdd' with ⟨multiple, hmultiple⟩
    omega
  rcases (regional.degree_pos_iff_exists_adj edge).1 hdegreePositive with
    ⟨regionalNeighbor, hregionalAdj⟩
  have hedgeRegion : edge ∈ vertexSetRegionEdges RS inside :=
    hregionalAdj.2.1
  rcases exists_trackedNeighbor_not_mem_region_of_odd_regional_degree
      RS (vertexSetRegionEdges RS inside) color first second edge
      hedgeRegion hregionalOdd hambientEven with
    ⟨outsideNeighbor, hambientAdj, houtsideNeighbor⟩
  rw [mem_vertexSetRegionEdges_iff] at hedgeRegion
  rw [mem_vertexSetCrossingEdges_iff]
  rcases hedgeRegion with ⟨inner, hinnerEndpoint, hinnerInside⟩
  rcases (RS.edgeAdjacencyGraph_adj_iff).1 hambientAdj.1 with
    ⟨_hne, outer, houterEndpoint, houterNeighborEndpoint⟩
  have houterOutside : outer ∉ inside := by
    intro houterInside
    exact houtsideNeighbor ((mem_vertexSetRegionEdges_iff RS inside
      outsideNeighbor).2 ⟨outer, houterNeighborEndpoint, houterInside⟩)
  exact ⟨inner, hinnerEndpoint, hinnerInside,
    outer, houterEndpoint, houterOutside⟩

/-- A regional odd endpoint of ambient even degree reaches a distinct actual
crossing edge, provided every regional odd endpoint has ambient even degree.
The result exposes the true vertex boundary without naming source portals. -/
theorem exists_distinct_reachable_vertexSetCrossingEdge_of_odd_regional_degree
    (RS : RotationSystem V E) (inside : Finset V)
    (color : E → Color) (first second : Color) (start : E)
    (hstartOdd : Odd ((regionalTrackedEdgeGraph RS
      (vertexSetRegionEdges RS inside) color first second).degree start))
    (hambientEven : ∀ edge : E,
      Odd ((regionalTrackedEdgeGraph RS
        (vertexSetRegionEdges RS inside) color first second).degree edge) →
      Even ((RS.trackedEdgeGraph color first second).degree edge)) :
    ∃ finish : E, finish ≠ start ∧
      finish ∈ vertexSetCrossingEdges RS inside ∧
      (regionalTrackedEdgeGraph RS
        (vertexSetRegionEdges RS inside) color first second).Reachable
          start finish := by
  classical
  letI : DecidableRel (regionalTrackedEdgeGraph RS
      (vertexSetRegionEdges RS inside) color first second).Adj :=
    Classical.decRel _
  apply exists_distinct_reachable_mem_of_odd_of_odd_subset
    (H := regionalTrackedEdgeGraph RS
      (vertexSetRegionEdges RS inside) color first second)
    start hstartOdd (vertexSetCrossingEdges RS inside : Set E)
  intro edge hedgeOdd
  exact mem_vertexSetCrossingEdges_of_odd_regional_degree
    RS inside color first second edge hedgeOdd (hambientEven edge hedgeOdd)

end

end GoertzelV24HexSlabConnectivityProfile

end Mettapedia.GraphTheory.FourColor
