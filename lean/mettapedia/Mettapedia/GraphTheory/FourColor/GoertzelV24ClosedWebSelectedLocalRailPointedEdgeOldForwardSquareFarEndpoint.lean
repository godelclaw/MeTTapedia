import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeOldForwardSquareComponentExclusion

/-!
# L1: name the far endpoint of an old-forward crossing

The crossed third edge of a pointed forward corner has one endpoint at the
named source corner and one literal opposite endpoint.  The source corner is
already proved to lie outside the selected first--third square component.
Therefore the third edge belongs to the source-square boundary exactly when
this one named far endpoint lies in the component.

This removes the last existential endpoint choice from the old-forward local
comparison.  It does not prove the far-end membership, construct a rolling
repair, attach end caps, construct separated crosscuts, or close Fable flag
L1.
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
open SimpleGraphDartRotation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

/-- The endpoint of the crossed third edge opposite the pointed source
corner. -/
def selectedPlacementSideForwardFarEndpoint
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left : {position // position ∈ selectedPlacementSidePositions placement}) :
    V :=
  (web.annular.RS.rho
    (web.annular.RS.phi
      (selectedPlacementSideForwardDart placement left))).snd

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

/-- The crossed third edge has exactly the named source corner and the literal
far endpoint as its unordered endpoints. -/
theorem selectedPlacementSideForwardThirdEdge_value
    (placement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext))
    (left : {position // position ∈ selectedPlacementSidePositions placement}) :
    (selectedPlacementSideForwardThirdEdge placement left).1 =
      s(selectedPlacementSideForwardCorner placement left,
        selectedPlacementSideForwardFarEndpoint placement left) := by
  let dart := selectedPlacementSideForwardDart placement left
  let thirdDart := web.annular.RS.rho (web.annular.RS.phi dart)
  have hfst : thirdDart.fst = selectedPlacementSideForwardCorner placement left := by
    change web.annular.RS.vertOf thirdDart =
      web.annular.RS.vertOf (web.annular.RS.alpha dart)
    exact (web.annular.RS.vert_rho (web.annular.RS.phi dart)).trans
      (web.annular.RS.vert_phi_eq_vert_alpha dart)
  change s(thirdDart.fst, thirdDart.snd) =
    s(selectedPlacementSideForwardCorner placement left, thirdDart.snd)
  rw [hfst]

/-- **L1 old-forward far-end criterion.**  The crossed third edge is a
selected source-square boundary edge exactly when its named far endpoint lies
in the selected two-vertex component. -/
theorem SelectedPlacementSideForwardEdgeReceipt.thirdEdge_mem_sourceSquare_crossingEdges_iff_farEndpoint_mem_component
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
      selectedPlacementSideForwardFarEndpoint secondPlacement left ∈
        component.supp := by
  rw [Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.thirdEdge_mem_sourceSquare_crossingEdges_iff_meets_component
    receipt hfirst hthird hfaceSecond bond hroot]
  have hcornerOutside :=
    Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.corner_not_mem_sourceSquare_component
      receipt hfirst hthird hfaceSecond bond hroot
  constructor
  · rintro ⟨vertex, hvertex, hcomponent⟩
    rw [selectedPlacementSideForwardThirdEdge_value] at hvertex
    simp only [Sym2.mem_iff] at hvertex
    rcases hvertex with rfl | rfl
    · exact False.elim (hcornerOutside hcomponent)
    · exact hcomponent
  · intro hfar
    refine ⟨selectedPlacementSideForwardFarEndpoint secondPlacement left, ?_, hfar⟩
    rw [selectedPlacementSideForwardThirdEdge_value]
    simp

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
