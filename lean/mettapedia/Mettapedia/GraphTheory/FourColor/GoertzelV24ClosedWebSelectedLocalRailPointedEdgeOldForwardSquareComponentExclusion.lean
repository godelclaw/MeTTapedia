import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeOldForwardSquarePacketExclusion
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeComponentIncidence

/-!
# L1: exclude an old-forward corner from the source square component

The preceding coordinate theorem shows that neither boundary arm of an
old-forward receipt belongs to the source square's four-edge boundary.  If
the receipt's corner were one of the selected square component's two vertices,
the exact endpoint-triangle packet theorem would force both arms to be the
single internal bond.  Their proved distinctness rules this out.

Consequently the crossed third edge cannot be the internal bond either.  If a
later source theorem proves that this edge meets the square component, the
edge must be a selected square-boundary crossing.  This removes the older
named-corner orientation as a possible uniform discharge for this receipt; it
does not prove the remaining far-end incidence, construct a rolling repair,
attach end caps, construct separated crosscuts, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
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
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

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
    {left right :
      {position // position ∈ selectedPlacementSidePositions secondPlacement}}
    {edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS)))}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- **L1 old-forward component exclusion.**  The source corner of an
old-forward receipt at the second placement is not one of the two vertices of
the selected first--third square component. -/
theorem SelectedPlacementSideForwardEdgeReceipt.corner_not_mem_sourceSquare_component
    (receipt : SelectedPlacementSideForwardEdgeReceipt
      secondPlacement left right edge)
    {face : SelectedFace (web := web)}
    (hfirst : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          firstInterior.center) face)
    (hthird : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
          (rungs := rungs) hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : MiddleReplacementShortDualCycle.SquareBondRealization
      (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
        (rungs := rungs) hfirst hthird hfaceSecond).cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    selectedPlacementSideForwardCorner secondPlacement left ∉ component.supp := by
  classical
  let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
    (rungs := rungs) hfirst hthird hfaceSecond
  let firstArm := selectedPlacementSideForwardFirstArm secondPlacement left
  let secondArm := selectedPlacementSideForwardSecondArm secondPlacement left
  have harms :=
    Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.arms_not_mem_sourceSquare_crossingEdges
      receipt hfirst hthird hfaceSecond
  have hstar :=
    Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.cornerStar
      receipt
  intro hcorner
  have hfirstPacket : firstArm ∈
      insert bond.internalEdge square.cycle.selectedCycle.crossingEdges := by
    apply (bond.edge_mem_endpointTrianglePacket_iff_meets_component
      hroot firstArm).2
    exact ⟨selectedPlacementSideForwardCorner secondPlacement left,
      hstar.2.2.2.1, hcorner⟩
  have hsecondPacket : secondArm ∈
      insert bond.internalEdge square.cycle.selectedCycle.crossingEdges := by
    apply (bond.edge_mem_endpointTrianglePacket_iff_meets_component
      hroot secondArm).2
    exact ⟨selectedPlacementSideForwardCorner secondPlacement left,
      hstar.2.2.2.2.1, hcorner⟩
  have hfirstInternal : firstArm = bond.internalEdge := by
    simp only [Finset.mem_insert] at hfirstPacket
    rcases hfirstPacket with hfirst | hfirst
    · exact hfirst
    · exact False.elim (harms.1 hfirst)
  have hsecondInternal : secondArm = bond.internalEdge := by
    simp only [Finset.mem_insert] at hsecondPacket
    rcases hsecondPacket with hsecond | hsecond
    · exact hsecond
    · exact False.elim (harms.2 hsecond)
  exact hstar.1 (hfirstInternal.trans hsecondInternal.symm)

/-- The crossed third edge of the same receipt is not the internal bond.  Its
named corner is outside the component, whereas both endpoints of the internal
bond are the component vertices. -/
theorem SelectedPlacementSideForwardEdgeReceipt.thirdEdge_ne_sourceSquare_internalEdge
    (receipt : SelectedPlacementSideForwardEdgeReceipt
      secondPlacement left right edge)
    {face : SelectedFace (web := web)}
    (hfirst : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          firstInterior.center) face)
    (hthird : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
          (rungs := rungs) hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : MiddleReplacementShortDualCycle.SquareBondRealization
      (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
        (rungs := rungs) hfirst hthird hfaceSecond).cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    selectedPlacementSideForwardThirdEdge secondPlacement left ≠
      bond.internalEdge := by
  intro hedge
  have hcornerOutside :=
    Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.corner_not_mem_sourceSquare_component
      receipt hfirst hthird hfaceSecond bond hroot
  apply hcornerOutside
  rw [bond.component_supp]
  have hcornerThird :=
    (Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.cornerStar
      receipt).2.2.2.2.2
  rw [hedge] at hcornerThird
  simpa [MiddleReplacementShortDualCycle.SquareBondRealization.internalEdge,
    Sym2.mem_iff] using hcornerThird

/-- For an old-forward receipt, endpoint-triangle packet membership has no
internal-bond branch: it is exactly source-square boundary membership. -/
theorem SelectedPlacementSideForwardEdgeReceipt.thirdEdge_mem_endpointTrianglePacket_iff_mem_sourceSquare_crossingEdges
    (receipt : SelectedPlacementSideForwardEdgeReceipt
      secondPlacement left right edge)
    {face : SelectedFace (web := web)}
    (hfirst : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          firstInterior.center) face)
    (hthird : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
          (rungs := rungs) hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : MiddleReplacementShortDualCycle.SquareBondRealization
      (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
        (rungs := rungs) hfirst hthird hfaceSecond).cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    selectedPlacementSideForwardThirdEdge secondPlacement left ∈
        insert bond.internalEdge
          (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
            (rungs := rungs) hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges ↔
      selectedPlacementSideForwardThirdEdge secondPlacement left ∈
        (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
          (rungs := rungs) hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges := by
  rw [Finset.mem_insert]
  exact or_iff_right
    (Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.thirdEdge_ne_sourceSquare_internalEdge
      receipt hfirst hthird hfaceSecond bond hroot)

/-- The remaining old-forward source obligation in its intrinsic form: the
crossed third edge is a selected square-boundary edge exactly when one of its
endpoints lies in the selected two-vertex component.  The named source corner
is already proved to be the outside endpoint. -/
theorem SelectedPlacementSideForwardEdgeReceipt.thirdEdge_mem_sourceSquare_crossingEdges_iff_meets_component
    (receipt : SelectedPlacementSideForwardEdgeReceipt
      secondPlacement left right edge)
    {face : SelectedFace (web := web)}
    (hfirst : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          firstInterior.center) face)
    (hthird : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
          (rungs := rungs) hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : MiddleReplacementShortDualCycle.SquareBondRealization
      (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
        (rungs := rungs) hfirst hthird hfaceSecond).cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    selectedPlacementSideForwardThirdEdge secondPlacement left ∈
        (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
          (rungs := rungs) hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges ↔
      ∃ vertex,
        vertex ∈ (selectedPlacementSideForwardThirdEdge
          secondPlacement left).1 ∧ vertex ∈ component.supp := by
  calc
    selectedPlacementSideForwardThirdEdge secondPlacement left ∈
        (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
          (rungs := rungs) hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges ↔
      selectedPlacementSideForwardThirdEdge secondPlacement left ∈
        insert bond.internalEdge
          (MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
            (rungs := rungs) hfirst hthird hfaceSecond).cycle.selectedCycle.crossingEdges :=
      (Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.thirdEdge_mem_endpointTrianglePacket_iff_mem_sourceSquare_crossingEdges
        receipt hfirst hthird hfaceSecond bond hroot).symm
    _ ↔ ∃ vertex,
        vertex ∈ (selectedPlacementSideForwardThirdEdge
          secondPlacement left).1 ∧ vertex ∈ component.supp :=
      bond.edge_mem_endpointTrianglePacket_iff_meets_component hroot _

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
