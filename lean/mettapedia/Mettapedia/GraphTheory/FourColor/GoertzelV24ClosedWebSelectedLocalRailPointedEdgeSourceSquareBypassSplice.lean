import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeBypassSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeSourceSquareResidualRows

/-!
# L1: splice the source-square bypass into the selected rail

The source-square classification leaves one honest local alternative: either
one of the two literal selected chord triangles has a cyclic inner side, or a
two-hop bypass avoids the collision face.  This module feeds the latter branch
directly into the generic pointed splice, producing a repaired whole rail.

The result is still an alternative, not a construction of the final crosscut
pair.  It does not discharge the cyclic chord-triangle branch, prove that the
repaired rail avoids its companion, iterate repairs along the corridor, attach
the two end caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

private abbrev SelectedFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {secondPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext)}
    {thirdPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)}

/-- **L1 source-square whole-rail alternative.**  A literal non-flank
source-square collision either exhibits a selected chord triangle with a
cyclic inner side, or it produces a two-hop bypass already installed in the
entire selected rail.

This theorem connects the finite source classification to the generic splice;
the cyclic branch and the paired-rail preservation obligations remain
explicit. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.exists_sourceSquare_chordTriangleCycle_or_spliceRepair
    {start finish face : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    {occurrence : InteriorOccurrence (current := face) walk}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hpath : walk.IsPath)
    (hfirst : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hsecond : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (hneBefore : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftBefore)
    (hneAfter : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftAfter) :
    (let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
      (rungs := rungs) hfirst hthird hfaceSecond
    (∃ selected : square.SourceChordSelectedTriangles
        (secondPlacement := secondPlacement),
      (∃ component :
          (G.deleteEdges (edgeFinsetValueSet
            selected.firstShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
        web.annular.RS.outer.fst ∉ component.supp ∧
          HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) ∨
        ∃ component :
          (G.deleteEdges (edgeFinsetValueSet
            selected.secondShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
        web.annular.RS.outer.fst ∉ component.supp ∧
          HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) ∨
      ∃ bypass : InteriorOccurrence.TwoHopBypass occurrence,
        Nonempty (InteriorOccurrence.SpliceRepair occurrence bypass)) := by
  dsimp only
  rcases allocation.exists_sourceSquare_chordTriangleCycle_or_twoHopBypass
      hpath hfirst hsecond hthird hfaceSecond successor hneBefore hneAfter with
    hcycles | hbypass
  · exact .inl hcycles
  · rcases hbypass with ⟨bypass⟩
    exact .inr ⟨bypass,
      InteriorOccurrence.nonempty_spliceRepair occurrence hpath bypass⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
