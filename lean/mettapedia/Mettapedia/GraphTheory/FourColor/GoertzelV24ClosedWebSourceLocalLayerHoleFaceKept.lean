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
open GoertzelV24FiniteDeletionCyclicCut
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

/-- A source-selected local layer retains the complete inner-hole face once a
concrete outer-to-inner comparison walk avoids its cut.  The premise is not a
replacement for the missing global layer construction: it is the exact
geometric witness which that construction must provide in order to certify,
as the source requires, that both holes lie outside the pumped region. -/
theorem sourceLocalLayerPair_innerHoleFaceKept_of_comparisonWalk
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
        hunique).MatchedCrossingsVertexDisjoint web.annular.cellulation.rotation)
    (innerRoot : G.Dart)
    (hinnerRoot : dartOrbitFace web.annular.RS innerRoot =
      web.annular.cellulation.innerHole)
    (bridge : G.Walk (web.annular.RS.vertOf web.annular.RS.outer)
      (web.annular.RS.vertOf innerRoot))
    (hbridgeAvoid : ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ bridge.edges →
      edge.1 ∉ edgeFinsetValueSet
        (((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
          hunique).primalCutEdges web.annular.cellulation.rotation)) :
    HoleFaceKept
      ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique |>.sourceCrosscutLayerSpliceData web.annular.cellulation.rotation
          (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext)
          hseparated)
      web.annular.cellulation.innerHole := by
  intro dart hdart
  change web.annular.RS.vertOf dart ∈
    ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
      hunique).componentSide
      (sourceLocalLayerPairCrosscutBoundaryData corridor hunique
        leftInterior hnext).component
  apply SourceCrosscutBoundaryData.face_vertex_mem_componentSide_of_bridge_and_boundary_avoids_primalCut
    web.annular.cellulation.rotation
    ((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair hunique)
    (sourceLocalLayerPairCrosscutBoundaryData corridor hunique leftInterior hnext)
    web.annular.RS.outer innerRoot dart bridge
  · exact
      (((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique).mem_componentSide_iff
          (sourceLocalLayerPairCrosscutBoundaryData corridor hunique
            leftInterior hnext).component
          (web.annular.RS.vertOf web.annular.RS.outer)).1
        (sourceLocalLayerPairCrosscutBoundaryData corridor hunique
          leftInterior hnext).outer_kept
  · exact hbridgeAvoid
  · intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      (((sourceLocalLayerPair corridor hunique leftInterior hnext).separatedLocalLayerPair
        hunique).primalCutEdges web.annular.cellulation.rotation) edge.1).1 hvalue with
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
    rw [hinnerRoot] at hedge
    exact (Finset.disjoint_left.mp
      (sourceLocalLayerPair_dualLoopCrossingEdges_disjoint_innerHoleBoundary
        corridor hunique leftInterior hnext) hedgeCut hedge)
  · exact hdart.trans hinnerRoot.symm

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
