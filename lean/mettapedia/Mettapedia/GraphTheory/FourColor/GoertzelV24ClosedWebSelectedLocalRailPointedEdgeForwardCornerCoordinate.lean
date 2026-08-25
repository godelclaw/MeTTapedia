import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeCenterCoordinate

/-!
# L1: expose the three literal edges at a pointed forward corner

A forward source receipt already retains the third primal edge crossed by its
facial-dual step and a local degree-three certificate at the source corner.
This module names the other two edges at that corner: the consecutive boundary
arms of the displayed Cell--3 face.  The three named edges are pairwise
distinct and all meet the retained corner.

This is the exact local star needed by the finite source-square comparison.  It
does not identify either boundary arm with a particular square-packet edge,
discard the exterior-fan alternative, construct a rolling repair, attach end
caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open SimpleGraphDartRotation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

/-- The displayed Cell--3 boundary edge entering a selected forward corner. -/
def selectedPlacementSideForwardFirstArm
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left : {position // position ∈ selectedPlacementSidePositions placement}) :
    G.edgeSet :=
  web.annular.RS.edgeOf (selectedPlacementSideForwardDart placement left)

/-- The consecutive displayed Cell--3 boundary edge leaving that corner. -/
def selectedPlacementSideForwardSecondArm
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left : {position // position ∈ selectedPlacementSidePositions placement}) :
    G.edgeSet :=
  web.annular.RS.edgeOf
    (web.annular.RS.phi (selectedPlacementSideForwardDart placement left))

private theorem cornerDarts_pairwise_ne_of_card_eq_three
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    (dart : RS.D)
    (hcard : (RS.dartsAt (RS.vertOf (RS.phi dart))).card = 3) :
    RS.alpha dart ≠ RS.phi dart ∧
      RS.alpha dart ≠ RS.rho (RS.phi dart) ∧
      RS.phi dart ≠ RS.rho (RS.phi dart) := by
  let vertex := RS.vertOf (RS.phi dart)
  let first := RS.alpha dart
  have hfirstMem : first ∈ RS.dartsAt vertex := by
    simp [RotationSystem.dartsAt, first, vertex,
      RS.vert_phi_eq_vert_alpha dart]
  have hcardFirst : (RS.dartsAt (RS.vertOf first)).card = 3 := by
    rw [show RS.vertOf first = RS.vertOf (RS.phi dart) by
      exact (RS.vert_phi_eq_vert_alpha dart).symm]
    exact hcard
  have hvertexCard : (RS.dartsAt vertex).card = 3 := hcard
  have hnontrivialFinset : (RS.dartsAt vertex).Nontrivial := by
    apply Finset.one_lt_card_iff_nontrivial.mp
    rw [hvertexCard]
    omega
  have hnontrivial : (RS.dartsAt vertex : Set RS.D).Nontrivial :=
    hnontrivialFinset
  have hfirstStep : RS.rho first ≠ first :=
    (rho_isCycleOn_dartsAt RS hrotation vertex).apply_ne
      hnontrivial hfirstMem
  have hsecondStep : RS.rho (RS.rho first) ≠ RS.rho first := by
    exact fun heq => hfirstStep (RS.rho.injective heq)
  have hfirstThird : first ≠ RS.rho (RS.rho first) := by
    intro heq
    have hcube := rho_cube_apply_of_dartsAt_card_eq_three RS hrotation first
      hcardFirst
    have hrho := congrArg RS.rho heq
    rw [hcube] at hrho
    exact hfirstStep hrho
  simpa only [first, RotationSystem.phi_apply] using
    ⟨hfirstStep.symm, hfirstThird, hsecondStep.symm⟩

/-- The two literal boundary arms and the crossed third edge form the complete
three-edge star retained by a forward receipt.  Local degree three is read
from the receipt; no global cubicity is assumed on the opened carrier. -/
theorem SelectedPlacementSideForwardEdgeReceipt.cornerStar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    {placement : SelectedInternalHexRungPlacement corridor rungs interior}
    {left right :
      {position // position ∈ selectedPlacementSidePositions placement}}
    {edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS)))}
    (receipt : SelectedPlacementSideForwardEdgeReceipt
      placement left right edge) :
    let firstArm := selectedPlacementSideForwardFirstArm placement left
    let secondArm := selectedPlacementSideForwardSecondArm placement left
    let thirdEdge := selectedPlacementSideForwardThirdEdge placement left
    let corner := selectedPlacementSideForwardCorner placement left
    firstArm ≠ secondArm ∧ firstArm ≠ thirdEdge ∧ secondArm ≠ thirdEdge ∧
      corner ∈ firstArm.1 ∧ corner ∈ secondArm.1 ∧ corner ∈ thirdEdge.1 := by
  let RS := web.annular.RS
  let dart := selectedPlacementSideForwardDart placement left
  have hcardAlpha : (RS.dartsAt (RS.vertOf (RS.alpha dart))).card = 3 := by
    simpa [RS, dart, selectedPlacementSideForwardCorner] using
      receipt.corner_card_eq_three
  have hcard : (RS.dartsAt (RS.vertOf (RS.phi dart))).card = 3 := by
    rw [RS.vert_phi_eq_vert_alpha dart]
    exact hcardAlpha
  have hdarts := cornerDarts_pairwise_ne_of_card_eq_three RS
    (Instance.InteriorFace.vertexRotationCyclic web) dart hcard
  have halphaMem : RS.alpha dart ∈ RS.dartsAt (RS.vertOf (RS.phi dart)) := by
    simpa [RotationSystem.dartsAt] using
      (RS.vert_phi_eq_vert_alpha dart).symm
  have hphiMem : RS.phi dart ∈ RS.dartsAt (RS.vertOf (RS.phi dart)) := by
    simp [RotationSystem.dartsAt]
  have hrhoPhiMem : RS.rho (RS.phi dart) ∈
      RS.dartsAt (RS.vertOf (RS.phi dart)) := by
    simpa [RotationSystem.dartsAt] using RS.vert_rho (RS.phi dart)
  have hfirstSecond : RS.edgeOf dart ≠ RS.edgeOf (RS.phi dart) := by
    intro hedge
    apply hdarts.1
    apply RS.edgeOf_injOn_dartsAt (RS.vertOf (RS.phi dart))
      halphaMem hphiMem
    exact (RS.edge_alpha dart).trans hedge
  have hfirstThird :
      RS.edgeOf dart ≠ RS.edgeOf (RS.rho (RS.phi dart)) := by
    intro hedge
    apply hdarts.2.1
    apply RS.edgeOf_injOn_dartsAt (RS.vertOf (RS.phi dart))
      halphaMem hrhoPhiMem
    exact (RS.edge_alpha dart).trans hedge
  have hsecondThird :
      RS.edgeOf (RS.phi dart) ≠ RS.edgeOf (RS.rho (RS.phi dart)) := by
    intro hedge
    apply hdarts.2.2
    apply RS.edgeOf_injOn_dartsAt (RS.vertOf (RS.phi dart))
      hphiMem hrhoPhiMem hedge
  have hfirstEndpoint : RS.vertOf (RS.alpha dart) ∈ (RS.edgeOf dart).1 := by
    have hmem : RS.vertOf (RS.alpha dart) ∈
        (RS.edgeOf (RS.alpha dart)).1 := by
      change (RS.alpha dart).fst ∈
        s((RS.alpha dart).fst, (RS.alpha dart).snd)
      simp
    simpa only [RS.edge_alpha dart] using hmem
  have hsecondEndpoint : RS.vertOf (RS.alpha dart) ∈
      (RS.edgeOf (RS.phi dart)).1 := by
    have hmem : RS.vertOf (RS.phi dart) ∈
        (RS.edgeOf (RS.phi dart)).1 := by
      change (RS.phi dart).fst ∈
        s((RS.phi dart).fst, (RS.phi dart).snd)
      simp
    rw [RS.vert_phi_eq_vert_alpha dart] at hmem
    exact hmem
  have hthirdEndpoint : RS.vertOf (RS.alpha dart) ∈
      (RS.edgeOf (RS.rho (RS.phi dart))).1 := by
    have hmem : RS.vertOf (RS.rho (RS.phi dart)) ∈
        (RS.edgeOf (RS.rho (RS.phi dart))).1 := by
      change (RS.rho (RS.phi dart)).fst ∈
        s((RS.rho (RS.phi dart)).fst, (RS.rho (RS.phi dart)).snd)
      simp
    rw [RS.vert_rho (RS.phi dart), RS.vert_phi_eq_vert_alpha dart] at hmem
    exact hmem
  change selectedPlacementSideForwardFirstArm placement left ≠
      selectedPlacementSideForwardSecondArm placement left at hfirstSecond
  change selectedPlacementSideForwardFirstArm placement left ≠
      selectedPlacementSideForwardThirdEdge placement left at hfirstThird
  change selectedPlacementSideForwardSecondArm placement left ≠
      selectedPlacementSideForwardThirdEdge placement left at hsecondThird
  change selectedPlacementSideForwardCorner placement left ∈
      (selectedPlacementSideForwardFirstArm placement left).1 at hfirstEndpoint
  change selectedPlacementSideForwardCorner placement left ∈
      (selectedPlacementSideForwardSecondArm placement left).1 at hsecondEndpoint
  change selectedPlacementSideForwardCorner placement left ∈
      (selectedPlacementSideForwardThirdEdge placement left).1 at hthirdEndpoint
  exact ⟨hfirstSecond, hfirstThird, hsecondThird,
    hfirstEndpoint, hsecondEndpoint, hthirdEndpoint⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
