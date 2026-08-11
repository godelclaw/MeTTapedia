import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAnnularHoleRetention
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSourceLocalLayerHoleSafety

/-!
# The source Cell-3 local layer retains its outer hole

The canonical local layer is internal to the annular source cell.  Its dual
loop therefore avoids the outer-hole boundary, while the source crosscut
chooses the component containing the designated outer dart.  Together these
facts retain the whole named outer facial boundary, including its open-tangle
degree-one stubs.
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
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebSourceLocalLayerHoleRetentionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Every outer-hole dart lies on the retained component side of the canonical
source local layer. -/
theorem sourceLocalLayerPair_outerHole_vertex_mem_componentSide
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (dart : G.Dart)
    (hdart : dartOrbitFace web.annular.RS dart =
      web.annular.cellulation.outerHole) :
    web.annular.RS.vertOf dart ∈
      ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique).componentSide
        (sourceLocalLayerPairCrosscutBoundaryData corridor hunique
          leftInterior hnext).component := by
  apply web.annular.outerHole_vertex_mem_componentSide_of_boundary_avoids_primalCut
    ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
      hunique)
    (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext)
  · intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      (((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique).primalCutEdges
          web.annular.cellulation.rotation) edge.1).1 hvalue with
      ⟨other, hother, hotherValue⟩
    have hotherCut : other ∈ dualWalkCrossingEdges
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
          hunique).dualLoop := by
      simpa [SeparatedAlignedSimpleDualCrosscuts.primalCutEdges] using hother
    have hedgeCut : edge ∈ dualWalkCrossingEdges
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
          hunique).dualLoop := by
      simpa [Subtype.ext hotherValue] using hotherCut
    exact (Finset.disjoint_left.mp
      (sourceLocalLayerPair_dualLoopCrossingEdges_disjoint_outerHoleBoundary
        corridor hunique leftInterior hnext) hedgeCut hedge)
  · exact hdart

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
