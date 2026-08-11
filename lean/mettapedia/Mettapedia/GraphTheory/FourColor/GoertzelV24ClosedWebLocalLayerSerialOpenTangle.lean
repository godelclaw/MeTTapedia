import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSourceLocalLayerBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutSerialOpenTangle

/-!
# Two-sided open tangle of a source Cell-3 layer

The source's local layer boundary has an exact retained deletion side and an
exact partition of its exposed darts into the two rail cuts.  This file reads
that literal open region as an input/output tangle.  It does not close the
two interfaces or assert the false old-endpoint disjointness condition of the
closed-splice specialization.
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

/-- The source-selected Cell-3 retained deletion side, viewed as a literal
two-sided open tangle.  Its left and right boundary carriers are exactly the
two disjoint source rail cuts; only a later serial composition may join them.
-/
noncomputable def sourceLocalLayerPairTwoSidedOpenTangle
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
