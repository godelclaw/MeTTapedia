import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCorridorLayer
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCrosscutHoleBoundary

/-!
# Internal Cell-3 layers avoid the named hole boundaries

Addendum XXVII(iii) keeps hole data outside a pumped region.  Any local
Cell-3 layer whose facial-dual support lies in the annular interior therefore
has dual crossings disjoint from both named hole boundaries.  This is the
open-tangle incidence fact; it introduces neither a closed-cubic
specialization nor endpoint-disjointness of splice ports.
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
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerHoleSafetyEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerPair

/-- A source-local layer whose dual loop stays in the annular interior has
crossed primal edges disjoint from the inner-hole boundary. -/
theorem dualLoopCrossingEdges_disjoint_innerHoleBoundary
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    Disjoint
      (dualWalkCrossingEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        (layers.separatedLocalLayerPair hunique).dualLoop)
      (orbitFaceBoundary web.annular.RS web.annular.cellulation.innerHole) := by
  refine _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCrosscutHoleBoundary.ClosedWebAnnularEmbedding.dualWalkCrossingEdges_disjoint_innerHoleBoundary_of_support_internal web.annular (layers.separatedLocalLayerPair hunique).dualLoop ?_
  intro face hface
  exact layers.separatedLocalLayerPair_dualLoop_support_internal hunique face hface

/-- The same internal layer's crossed primal edges are disjoint from the
outer-hole boundary. -/
theorem dualLoopCrossingEdges_disjoint_outerHoleBoundary
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    Disjoint
      (dualWalkCrossingEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        (layers.separatedLocalLayerPair hunique).dualLoop)
      (orbitFaceBoundary web.annular.RS web.annular.cellulation.outerHole) := by
  refine _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCrosscutHoleBoundary.ClosedWebAnnularEmbedding.dualWalkCrossingEdges_disjoint_outerHoleBoundary_of_support_internal web.annular (layers.separatedLocalLayerPair hunique).dualLoop ?_
  intro face hface
  exact layers.separatedLocalLayerPair_dualLoop_support_internal hunique face hface

end LocalLayerPair

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
