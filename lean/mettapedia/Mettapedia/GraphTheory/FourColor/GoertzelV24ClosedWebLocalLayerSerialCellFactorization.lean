import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialTerminalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileSeamResidual

/-!
# Exact actual-source prefix/Cell factorization

One literal source Cell enlarges the terminal-aware cumulative prefix by an
exact union of edge regions.  This file turns that geometric union into the
two semantic decompositions used by the full five-coordinate cut profile:
tracked two-color connectivity and occurrence-sensitive facial continuation.

Each enlarged graph is exactly the supremum of the predecessor factor, the
literal Cell factor, and the residual seam between them.  Consequently its
connectivity is exactly the reflexive-transitive closure of component moves
inside the first two factors and literal moves across the seam.  No global
cubicity, two-sidedness, deterministic update, or finite-state bound is
assumed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphSupResidual
open GoertzelV24TerminalProfileConnectivityUpdate
open GoertzelV24TerminalProfileFaceUpdate
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFactorizationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The tracked residual seam between the actual terminal-aware cumulative
prefix and one literal source Cell. -/
def sourceLocalLayerSerialTerminalTrackedSeamAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) :
    SimpleGraph G.edgeSet :=
  regionalTrackedSeamGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    (sourceLocalLayerCellRegionAt corridor hunique offset)
    color first second

/-- The tracked graph after adjoining one actual Cell is exactly the
predecessor graph, the literal Cell graph, and their residual seam. -/
theorem sourceLocalLayerSerialPreRebaseTrackedGraph_eq_three_factor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color) :
    regionalTrackedEdgeGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        color first second =
      (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
          color first second ⊔
        regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerCellRegionAt corridor hunique offset)
          color first second) ⊔
        sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
          color first second := by
  rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
    hunique offset]
  exact regionalTrackedEdgeGraph_union_eq_sup_sup_seam
    web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    (sourceLocalLayerCellRegionAt corridor hunique offset)
    color first second

/-- Tracked connectivity after adjoining one actual Cell is exactly the
three-factor closure of predecessor, Cell, and residual-seam moves. -/
theorem sourceLocalLayerSerialPreRebaseTrackedReachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color) (first second : Color)
    (left right : G.edgeSet) :
    (regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      color first second).Reachable left right ↔
      Relation.ReflTransGen
        (ThreeFactorComponentStep
          (regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
            color first second)
          (regionalTrackedEdgeGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset)
            color first second)
          (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
            color first second)) left right := by
  rw [sourceLocalLayerSerialPreRebaseTrackedGraph_eq_three_factor corridor
    hunique offset color first second]
  exact reachable_sup_sup_iff_threeFactorComponentClosure _ _ _ _ _

/-- The occurrence-sensitive facial residual seam between the actual
terminal-aware cumulative prefix and one literal source Cell. -/
def sourceLocalLayerSerialTerminalFaceSeamAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D) :=
  faceRegionalSeamGraph web.annular.RS root
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    (sourceLocalLayerCellRegionAt corridor hunique offset)

/-- The face-occurrence graph after adjoining one actual Cell has the same
exact predecessor/Cell/seam decomposition as tracked connectivity. -/
theorem sourceLocalLayerSerialPreRebaseFaceGraph_eq_three_factor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D) :
    faceRegionalAmbientPositionGraph web.annular.RS root
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset) =
      (faceRegionalAmbientPositionGraph web.annular.RS root
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) ⊔
        faceRegionalAmbientPositionGraph web.annular.RS root
          (sourceLocalLayerCellRegionAt corridor hunique offset)) ⊔
        sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset root := by
  rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
    hunique offset]
  exact faceRegionalAmbientPositionGraph_union_eq_sup_sup_seam _ _ _ _

/-- Facial continuation after adjoining one actual Cell is exactly the
three-factor closure of predecessor, Cell, and residual-seam moves. -/
theorem sourceLocalLayerSerialPreRebaseFaceReachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (root : web.annular.RS.D)
    (left right : Fin (web.annular.RS.faceOrbit root).card) :
    (faceRegionalAmbientPositionGraph web.annular.RS root
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)).Reachable
        left right ↔
      Relation.ReflTransGen
        (ThreeFactorComponentStep
          (faceRegionalAmbientPositionGraph web.annular.RS root
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset))
          (faceRegionalAmbientPositionGraph web.annular.RS root
            (sourceLocalLayerCellRegionAt corridor hunique offset))
          (sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset root))
        left right := by
  rw [sourceLocalLayerSerialPreRebaseFaceGraph_eq_three_factor corridor
    hunique offset root]
  exact reachable_sup_sup_iff_threeFactorComponentClosure _ _ _ _ _

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
