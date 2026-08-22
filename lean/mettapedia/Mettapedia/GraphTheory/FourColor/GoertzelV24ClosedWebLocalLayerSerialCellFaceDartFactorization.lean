import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceRegionalDartSeam

/-!
# Root-independent facial factorization for one opened-source Cell

The earlier source-Cell factorization is stated separately on the cyclic
position carrier of each selected face root.  This file records the same
exact update once on literal darts.  That carrier is the one needed by a
finite predecessor-attachment state: fragments and local occurrences may be
named from different roots, while their literal darts live in one fixed type.

The enlarged cumulative facial graph is exactly predecessor sup Cell sup the
explicit residual seam.  No two-sidedness, global cubicity, finite bound, or
deterministic successor is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24RotationFaceRegionalDartSeam
open GoertzelV24SimpleGraphSupResidual
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFaceDartFactorizationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The occurrence-sensitive residual seam between the terminal-aware
predecessor and the literal Cell, on the global literal-dart carrier. -/
def sourceLocalLayerSerialTerminalFaceDartSeamAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) : SimpleGraph web.annular.RS.D :=
  faceRegionalDartSeamGraph web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
    (sourceLocalLayerCellRegionAt corridor hunique offset)

/-- The literal-dart facial graph after adjoining one actual Cell is exactly
the predecessor graph, Cell graph, and their residual seam. -/
theorem sourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset) =
      (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset) ⊔
        faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerCellRegionAt corridor hunique offset)) ⊔
        sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique offset := by
  rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
    hunique offset]
  exact faceRegionalDartGraph_union_eq_sup_sup_seam _ _ _

/-- Complete occurrence-sensitive facial reachability after adjoining one
actual Cell is the three-factor closure on literal darts. -/
theorem sourceLocalLayerSerialPreRebaseFaceDartReachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (left right : web.annular.RS.D) :
    (faceRegionalDartGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      ).Reachable left right ↔
      Relation.ReflTransGen
        (ThreeFactorComponentStep
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
              offset))
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerCellRegionAt corridor hunique offset))
          (sourceLocalLayerSerialTerminalFaceDartSeamAt corridor hunique
            offset)) left right := by
  rw [sourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor corridor
    hunique offset]
  exact reachable_sup_sup_iff_threeFactorComponentClosure _ _ _ _ _

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
