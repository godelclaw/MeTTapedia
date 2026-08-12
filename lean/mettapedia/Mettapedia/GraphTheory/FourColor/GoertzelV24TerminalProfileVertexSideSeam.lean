import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileSeamResidual

/-!
# Residual seams against a vertex-side region

When one factor of a regional update is induced by a vertex side, every
residual adjacency has a rigid geometric location.  The endpoint belonging
only to that factor must cross its vertex cut: its shared endpoint with the
other factor lies outside the side, while regional membership supplies an
endpoint inside.

This is a generic localization theorem.  It neither chooses a corridor
interface nor asserts that the residual seam is empty.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileVertexSideSeam

open GoertzelV24FaceDualConnectedness
open GoertzelV24HexFaceRungType
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileRegionalCoverage
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- If an edge in a vertex-side region is adjacent to an edge outside that
region, then it crosses the underlying vertex cut. -/
theorem mem_vertexSetCrossingEdges_of_adjacent_not_mem_region
    (RS : RotationSystem V E) (inside : Finset V) {outsideEdge regionEdge : E}
    (hadj : RS.edgeAdjacencyGraph.Adj outsideEdge regionEdge)
    (houtside : outsideEdge ∉ vertexSetRegionEdges RS inside)
    (hregion : regionEdge ∈ vertexSetRegionEdges RS inside) :
    regionEdge ∈ vertexSetCrossingEdges RS inside := by
  rw [mem_vertexSetRegionEdges_iff] at houtside hregion
  rw [mem_vertexSetCrossingEdges_iff]
  rcases hregion with ⟨inner, hinnerEndpoint, hinnerInside⟩
  rcases (RS.edgeAdjacencyGraph_adj_iff).1 hadj with
    ⟨_ne, shared, hsharedOutside, hsharedRegion⟩
  have hsharedNotInside : shared ∉ inside := by
    intro hsharedInside
    exact houtside ⟨shared, hsharedOutside, hsharedInside⟩
  exact ⟨inner, hinnerEndpoint, hinnerInside,
    shared, hsharedRegion, hsharedNotInside⟩

/-- In a tracked residual seam against a vertex-side region, the endpoint
exclusive to that region is an actual crossing edge of the vertex cut. -/
theorem regionalTrackedSeamGraph_adj_localizes_to_vertexCut
    (RS : RotationSystem V E) (leftRegion : Finset E) (inside : Finset V)
    (C : E → Color) (a b : Color) {x y : E}
    (hadj : (regionalTrackedSeamGraph RS leftRegion
      (vertexSetRegionEdges RS inside) C a b).Adj x y) :
    (x ∈ leftRegion ∧ x ∉ vertexSetRegionEdges RS inside ∧
        y ∈ vertexSetRegionEdges RS inside ∧ y ∉ leftRegion ∧
        y ∈ vertexSetCrossingEdges RS inside) ∨
      (x ∈ vertexSetRegionEdges RS inside ∧ x ∉ leftRegion ∧
        x ∈ vertexSetCrossingEdges RS inside ∧
        y ∈ leftRegion ∧ y ∉ vertexSetRegionEdges RS inside) := by
  rcases (regionalTrackedSeamGraph_adj_iff RS leftRegion
      (vertexSetRegionEdges RS inside) C a b x y).1 hadj with
    ⟨htracked, hforward | hbackward⟩
  · exact Or.inl ⟨hforward.1, hforward.2.1, hforward.2.2.1,
      hforward.2.2.2,
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS inside
        htracked.1 hforward.2.1 hforward.2.2.1⟩
  · exact Or.inr ⟨hbackward.1, hbackward.2.1,
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS inside
        htracked.1.symm hbackward.2.2.2 hbackward.1,
      hbackward.2.2.1, hbackward.2.2.2⟩

/-- The occurrence-sensitive facial residual has the same vertex-cut
localization after projecting its positions to ambient edges. -/
theorem faceRegionalSeamGraph_adj_localizes_to_vertexCut
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (leftRegion : Finset E) (inside : Finset V)
    {x y : Fin (RS.faceOrbit root).card}
    (hadj : (faceRegionalSeamGraph RS root leftRegion
      (vertexSetRegionEdges RS inside)).Adj x y) :
    (faceCycleEdge RS root x ∈ leftRegion ∧
        faceCycleEdge RS root x ∉ vertexSetRegionEdges RS inside ∧
        faceCycleEdge RS root y ∈ vertexSetRegionEdges RS inside ∧
        faceCycleEdge RS root y ∉ leftRegion ∧
        faceCycleEdge RS root y ∈ vertexSetCrossingEdges RS inside) ∨
      (faceCycleEdge RS root x ∈ vertexSetRegionEdges RS inside ∧
        faceCycleEdge RS root x ∉ leftRegion ∧
        faceCycleEdge RS root x ∈ vertexSetCrossingEdges RS inside ∧
        faceCycleEdge RS root y ∈ leftRegion ∧
        faceCycleEdge RS root y ∉ vertexSetRegionEdges RS inside) := by
  rcases (faceRegionalSeamGraph_adj_iff RS root leftRegion
      (vertexSetRegionEdges RS inside) x y).1 hadj with
    ⟨hface, hforward | hbackward⟩
  · have hedgeAdj := edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
      RS hcubic hrotation root hface
    exact Or.inl ⟨hforward.1, hforward.2.1, hforward.2.2.1,
      hforward.2.2.2,
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS inside
        hedgeAdj hforward.2.1 hforward.2.2.1⟩
  · have hedgeAdj := edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
      RS hcubic hrotation root hface
    exact Or.inr ⟨hbackward.1, hbackward.2.1,
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS inside
        hedgeAdj.symm hbackward.2.2.2 hbackward.1,
      hbackward.2.2.1, hbackward.2.2.2⟩

end

end GoertzelV24TerminalProfileVertexSideSeam

end Mettapedia.GraphTheory.FourColor
