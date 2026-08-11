import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSourceLocalLayerBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutSerialOpenTangle

/-!
# Retained-side open tangle at a source Cell-3 layer cut

The source's local layer boundary has an exact outer retained deletion side
and an exact partition of its exposed darts into the two rail cuts.  This file
reads that retained side as an input/output tangle.  It is useful for the
eventual shortened-map splice, but it is deliberately *not* the local Cell-3
generator of the source's `Count` functor: that generator is the complementary
removed region bounded by the two layers.  Serially composing the retained
sides would duplicate the ambient exterior.
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
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OpenTangleComposition
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SpliceUnification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialOpenTangleEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The source-selected outer retained deletion side, viewed as a literal
two-sided open tangle.  Its left and right boundary carriers are exactly the
two disjoint source rail cuts.  This is a splice-side object, not a corridor
cell generator. -/
noncomputable def sourceLocalLayerPairRetainedTwoSidedOpenTangle
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :=
  (sourceLocalLayerPairOrderedCutSidesData
    corridor hunique leftInterior hnext).toTwoSidedOpenTangle

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
