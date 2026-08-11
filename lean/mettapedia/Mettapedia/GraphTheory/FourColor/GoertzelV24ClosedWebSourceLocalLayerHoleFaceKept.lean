import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebOpenTangle
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSourceLocalLayerHoleRetention

/-!
# Source-local outer-hole retention at the splice interface

The Cell-3 local layer has already selected the deletion component containing
the source outer root.  This adapter records the resulting whole-face
retention in the `HoleFaceKept` vocabulary consumed by the open-tangle splice.
It intentionally proves only the outer half: retaining the inner hole requires
the later global layer construction, not merely that this local wall avoids
the inner-hole boundary.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24SpliceUnification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebSourceLocalLayerHoleFaceKeptEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The source-selected local Cell-3 splice keeps the complete outer-hole
face.  This is the literal component-side result transported through the
concrete `sourceCrosscutLayerSpliceData` definition; no hole-side condition is
added to the splice as an assumption. -/
theorem sourceLocalLayerPair_outerHoleFaceKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (hseparated :
      ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique).MatchedCrossingsVertexDisjoint web.annular.cellulation.rotation) :
    HoleFaceKept
      ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique |>.sourceCrosscutLayerSpliceData web.annular.cellulation.rotation
          (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext)
          hseparated)
      web.annular.cellulation.outerHole := by
  intro dart hdart
  change web.annular.RS.vertOf dart ∈
    ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
      hunique).componentSide
      (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext).component
  exact sourceLocalLayerPair_outerHole_vertex_mem_componentSide
    corridor hunique leftInterior hnext dart hdart

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
