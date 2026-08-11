import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSourceLocalLayerBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerHoleSafety

/-!
# The source-selected Cell-3 layer keeps both holes outside its cut

This is the direct source instance of the local-layer hole-safety theorem.
The Cell-3 corridor chooses the layer faces canonically; its dual loop stays
inside the annular interior, so it cannot cross either named hole boundary.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebSourceLocalLayerHoleSafetyEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The canonical Cell-3 layer crosses no edge of the designated inner-hole
boundary. -/
theorem sourceLocalLayerPair_dualLoopCrossingEdges_disjoint_innerHoleBoundary
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Disjoint
      (dualWalkCrossingEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
          hunique).dualLoop)
      (orbitFaceBoundary web.annular.RS web.annular.cellulation.innerHole) := by
  exact LocalLayerPair.dualLoopCrossingEdges_disjoint_innerHoleBoundary
    (sourceLocalLayerPair corridor hunique leftInterior hnext) hunique

/-- The same canonical layer crosses no edge of the outer-hole boundary. -/
theorem sourceLocalLayerPair_dualLoopCrossingEdges_disjoint_outerHoleBoundary
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Disjoint
      (dualWalkCrossingEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
          hunique).dualLoop)
      (orbitFaceBoundary web.annular.RS web.annular.cellulation.outerHole) := by
  exact LocalLayerPair.dualLoopCrossingEdges_disjoint_outerHoleBoundary
    (sourceLocalLayerPair corridor hunique leftInterior hnext) hunique

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
