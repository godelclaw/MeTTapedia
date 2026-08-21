import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeSourceSquareOriginReduction

/-!
# L1: retain the primal crossing of the source-square diagonal

The old-forward pointed-origin branch proves a facial-dual diagonal from the
second corridor centre to the collision face.  Its primal crossing is not the
old-forward receipt's third edge: it is the displayed centre-to-side edge at
the side slot occupied by the collision face.  This module retains that exact
slot and exact primal edge together with the chord proof.

This is source-local crossing provenance supporting L1.  It does not yet
split the square into selected triangles, consume the chord reduction, repair
or iterate the rails, attach end caps, construct separated crosscuts, or close
L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
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
    {left right :
      {position // position ∈ selectedPlacementSidePositions secondPlacement}}
    {edge : Sym2 (SelectedFace web)}

/-- **L1 old-forward chord-crossing receipt.**  The collision side slot
supplies the literal centre-to-side primal edge crossing the square diagonal.
The old-forward third edge is used only to locate the collision face; it is
not misidentified with this crossing. -/
theorem SelectedPlacementSideForwardEdgeReceipt.exists_sourceSquare_secondFace_chordCrossing
    (receipt : SelectedPlacementSideForwardEdgeReceipt
      secondPlacement left right edge)
    {face : SelectedFace web}
    (hfirst : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (hface : face = selectedPlacementSideFace secondPlacement left ∨
      face = selectedPlacementSideFace secondPlacement right) :
    ∃ position :
        {position // position ∈ selectedPlacementSidePositions secondPlacement},
      face = selectedPlacementSideFace secondPlacement position ∧
        let crossing := web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS secondPlacement.root position.1)
        crossing ∈ sharedInteriorEdges
            (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))
            (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
              (nextCorridorInterior firstInterior hfirstNext).center).1
            face.1 ∧
          let square := squareDualCycle_of_firstThirdSquare
            (rungs := rungs) hfirst hthird hfaceSecond
          square.cycle.walk.IsChord
            s(corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
                (nextCorridorInterior firstInterior hfirstNext).center,
              face) := by
  rcases hface with hface | hface
  · refine ⟨left, hface, ?_, ?_⟩
    · have hshared :=
        (selectedPlacementCenterSideEdgeReceipt secondPlacement left).sideEdge_mem_shared
      simpa [hface] using hshared
    · exact
        Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.sourceSquare_secondFace_isChord
          receipt hfirst hthird hfaceSecond (.inl hface)
  · refine ⟨right, hface, ?_, ?_⟩
    · have hshared :=
        (selectedPlacementCenterSideEdgeReceipt secondPlacement right).sideEdge_mem_shared
      simpa [hface] using hshared
    · exact
        Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.sourceSquare_secondFace_isChord
          receipt hfirst hthird hfaceSecond (.inr hface)

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
