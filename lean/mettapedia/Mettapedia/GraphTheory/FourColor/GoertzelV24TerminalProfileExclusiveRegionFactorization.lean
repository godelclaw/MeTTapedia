import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileVertexSideSeam

/-!
# Exact regional factorization after assigning overlaps to the old side

Two consecutive source regions can overlap.  Treating the overlap as if it
were absent changes the residual seam, while retaining it in both factors
leaves a later recurrence with duplicated ownership.  The exact alternative
is to assign every shared edge to the old factor and use `right \ left` as the
genuinely new factor.

This file proves that the resulting three-factor decomposition is exact.  It
also records the reason this presentation is useful for a finite recurrence:
when the old region is induced by a vertex side, every old endpoint of the new
exclusive seam is a true crossing edge of that side.  Thus overlap is not
silently discarded; its changed seam is forced onto the already classified
old frontier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileExclusiveRegionFactorization

open GoertzelV24FaceDualConnectedness
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileFaceUpdate
open GoertzelV24TerminalProfileRegionalCoverage
open GoertzelV24TerminalProfileSeamResidual
open GoertzelV24TerminalProfileVertexSideSeam
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The residual tracked seam after every shared regional edge has been
assigned to the old factor. -/
def regionalTrackedExclusiveSeamGraph
    (RS : RotationSystem V E) (oldRegion rightRegion : Finset E)
    (color : E → Color) (first second : Color) : SimpleGraph E :=
  regionalTrackedSeamGraph RS oldRegion (rightRegion \ oldRegion)
    color first second

/-- Old region, genuinely new right region, and their new seam recover the
same tracked graph as the original overlapping union. -/
theorem regionalTrackedEdgeGraph_union_eq_sup_sup_exclusiveSeam
    (RS : RotationSystem V E) (oldRegion rightRegion : Finset E)
    (color : E → Color) (first second : Color) :
    regionalTrackedEdgeGraph RS (oldRegion ∪ rightRegion) color first second =
      (regionalTrackedEdgeGraph RS oldRegion color first second ⊔
        regionalTrackedEdgeGraph RS (rightRegion \ oldRegion) color first
          second) ⊔
        regionalTrackedExclusiveSeamGraph RS oldRegion rightRegion color
          first second := by
  simpa [regionalTrackedExclusiveSeamGraph,
    Finset.union_sdiff_self_eq_union] using
    (regionalTrackedEdgeGraph_union_eq_sup_sup_seam RS oldRegion
      (rightRegion \ oldRegion) color first second)

/-- For a vertex-side old region, an exclusive tracked seam is oriented
between one true old-frontier edge and one genuinely new right edge. -/
theorem regionalTrackedExclusiveSeamGraph_adj_localizes_to_oldVertexCut
    (RS : RotationSystem V E) (inside : Finset V) (rightRegion : Finset E)
    (color : E → Color) (first second : Color) {x y : E}
    (hadj : (regionalTrackedExclusiveSeamGraph RS
      (vertexSetRegionEdges RS inside) rightRegion color first second).Adj
        x y) :
    (x ∈ vertexSetRegionEdges RS inside ∧
        x ∈ vertexSetCrossingEdges RS inside ∧
        y ∈ rightRegion ∧ y ∉ vertexSetRegionEdges RS inside) ∨
      (y ∈ vertexSetRegionEdges RS inside ∧
        y ∈ vertexSetCrossingEdges RS inside ∧
        x ∈ rightRegion ∧ x ∉ vertexSetRegionEdges RS inside) := by
  have hraw := (regionalTrackedSeamGraph_adj_iff RS
    (vertexSetRegionEdges RS inside)
    (rightRegion \ vertexSetRegionEdges RS inside)
    color first second x y).1 hadj
  rcases hraw.2 with hforward | hbackward
  · have hcrossing : x ∈ vertexSetCrossingEdges RS inside :=
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS inside
        hraw.1.1.symm hforward.2.2.2 hforward.1
    exact Or.inl ⟨hforward.1, hcrossing,
      (Finset.mem_sdiff.1 hforward.2.2.1).1,
      (Finset.mem_sdiff.1 hforward.2.2.1).2⟩
  · have hcrossing : y ∈ vertexSetCrossingEdges RS inside :=
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS inside
        hraw.1.1 hbackward.2.1 hbackward.2.2.1
    exact Or.inr ⟨hbackward.2.2.1, hcrossing,
      (Finset.mem_sdiff.1 hbackward.1).1,
      (Finset.mem_sdiff.1 hbackward.1).2⟩

/-- The occurrence-sensitive facial seam after assigning every shared edge
to the old factor. -/
def faceRegionalExclusiveSeamGraph
    (RS : RotationSystem V E) (root : RS.D)
    (oldRegion rightRegion : Finset E) :
    SimpleGraph (Fin (RS.faceOrbit root).card) :=
  faceRegionalSeamGraph RS root oldRegion (rightRegion \ oldRegion)

/-- The analogous occurrence-sensitive face factorization is exact. -/
theorem faceRegionalAmbientPositionGraph_union_eq_sup_sup_exclusiveSeam
    (RS : RotationSystem V E) (root : RS.D)
    (oldRegion rightRegion : Finset E) :
    faceRegionalAmbientPositionGraph RS root (oldRegion ∪ rightRegion) =
      (faceRegionalAmbientPositionGraph RS root oldRegion ⊔
        faceRegionalAmbientPositionGraph RS root
          (rightRegion \ oldRegion)) ⊔
        faceRegionalExclusiveSeamGraph RS root oldRegion rightRegion := by
  simpa [faceRegionalExclusiveSeamGraph,
    Finset.union_sdiff_self_eq_union] using
    (faceRegionalAmbientPositionGraph_union_eq_sup_sup_seam RS root oldRegion
      (rightRegion \ oldRegion))

/-- Facial occurrences in the exclusive seam project to the same true old
vertex-side frontier, while preserving which occurrence lies on which side. -/
theorem faceRegionalExclusiveSeamGraph_adj_localizes_to_oldVertexCut
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (inside : Finset V) (rightRegion : Finset E)
    {x y : Fin (RS.faceOrbit root).card}
    (hadj : (faceRegionalExclusiveSeamGraph RS root
      (vertexSetRegionEdges RS inside) rightRegion).Adj x y) :
    (faceCycleEdge RS root x ∈ vertexSetRegionEdges RS inside ∧
        faceCycleEdge RS root x ∈ vertexSetCrossingEdges RS inside ∧
        faceCycleEdge RS root y ∈ rightRegion ∧
        faceCycleEdge RS root y ∉ vertexSetRegionEdges RS inside) ∨
      (faceCycleEdge RS root y ∈ vertexSetRegionEdges RS inside ∧
        faceCycleEdge RS root y ∈ vertexSetCrossingEdges RS inside ∧
        faceCycleEdge RS root x ∈ rightRegion ∧
        faceCycleEdge RS root x ∉ vertexSetRegionEdges RS inside) := by
  have hraw := (faceRegionalSeamGraph_adj_iff RS root
    (vertexSetRegionEdges RS inside)
    (rightRegion \ vertexSetRegionEdges RS inside) x y).1 hadj
  have hedgeAdj := edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
    RS hcubic hrotation root hraw.1
  rcases hraw.2 with hforward | hbackward
  · have hcrossing : faceCycleEdge RS root x ∈
        vertexSetCrossingEdges RS inside :=
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS inside
        hedgeAdj.symm hforward.2.2.2 hforward.1
    exact Or.inl ⟨hforward.1, hcrossing,
      (Finset.mem_sdiff.1 hforward.2.2.1).1,
      (Finset.mem_sdiff.1 hforward.2.2.1).2⟩
  · have hcrossing : faceCycleEdge RS root y ∈
        vertexSetCrossingEdges RS inside :=
      mem_vertexSetCrossingEdges_of_adjacent_not_mem_region RS inside
        hedgeAdj hbackward.2.1 hbackward.2.2.1
    exact Or.inr ⟨hbackward.2.2.1, hcrossing,
      (Finset.mem_sdiff.1 hbackward.1).1,
      (Finset.mem_sdiff.1 hbackward.1).2⟩

end

end GoertzelV24TerminalProfileExclusiveRegionFactorization

end Mettapedia.GraphTheory.FourColor
