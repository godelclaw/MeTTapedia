import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorInterfaceMatching
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCorridorColorTransfer

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSlab
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

private theorem color_eq_add_of_three_distinct_nonzero {a b c : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c = a + b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    simp at hab hac hbc ⊢

/-- The three darts encountered at one facial corner are the three distinct
darts based at that cubic vertex. -/
theorem cornerDarts_pairwise_ne (RS : RotationSystem V E)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS) (dart : RS.D) :
    RS.alpha dart ≠ RS.phi dart ∧
      RS.alpha dart ≠ RS.rho (RS.phi dart) ∧
      RS.phi dart ≠ RS.rho (RS.phi dart) := by
  let vertex := RS.vertOf (RS.phi dart)
  let first := RS.alpha dart
  have hfirstMem : first ∈ RS.dartsAt vertex := by
    simpa [RotationSystem.dartsAt, first, vertex] using
      (RS.vert_phi_eq_vert_alpha dart).symm
  have hnontrivialFinset : (RS.dartsAt vertex).Nontrivial := by
    apply Finset.one_lt_card_iff_nontrivial.mp
    rw [hcubic vertex]
    omega
  have hnontrivial : (RS.dartsAt vertex : Set RS.D).Nontrivial := by
    simpa only [Finset.coe_sort_coe] using hnontrivialFinset
  have hfirstStep : RS.rho first ≠ first :=
    (rho_isCycleOn_dartsAt RS hrotation vertex).apply_ne
      hnontrivial hfirstMem
  have hsecondStep : RS.rho (RS.rho first) ≠ RS.rho first := by
    exact fun heq => hfirstStep (RS.rho.injective heq)
  have hfirstThird : first ≠ RS.rho (RS.rho first) := by
    intro heq
    have hcube := rho_cube_apply_of_isCubic RS hcubic hrotation first
    have hrho := congrArg RS.rho heq
    rw [hcube] at hrho
    exact hfirstStep hrho
  simpa only [first, RotationSystem.phi_apply] using
    ⟨hfirstStep.symm, hfirstThird, hsecondStep.symm⟩

/-- The third edge at a cubic facial corner is the actual shared interior
edge of the two faces across the consecutive boundary edges. -/
theorem thirdCornerEdge_mem_sharedInteriorEdges
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (dart : RS.D)
    (hfacesNe : dartOrbitFace RS (RS.alpha dart) ≠
      dartOrbitFace RS (RS.alpha (RS.phi dart))) :
    RS.edgeOf (RS.rho (RS.phi dart)) ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))
        (dartOrbitFace RS (RS.alpha dart))
        (dartOrbitFace RS (RS.alpha (RS.phi dart))) := by
  let third := RS.rho (RS.phi dart)
  have hthirdRho : RS.rho third = RS.alpha dart := by
    have hcube := rho_cube_apply_of_isCubic RS hcubic hrotation (RS.alpha dart)
    simpa only [third, RotationSystem.phi_apply] using hcube
  have hleftFace : dartOrbitFace RS (RS.alpha third) =
      dartOrbitFace RS (RS.alpha dart) := by
    calc
      dartOrbitFace RS (RS.alpha third) = dartOrbitFace RS (RS.rho third) :=
        dartOrbitFace_alpha_eq_dartOrbitFace_rho RS third
      _ = dartOrbitFace RS (RS.alpha dart) :=
        congrArg (dartOrbitFace RS) hthirdRho
  have hleft : RS.edgeOf third ∈
      orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha dart)) := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha third)
    rw [RS.edge_alpha third, hleftFace] at hraw
    exact hraw
  have hright : RS.edgeOf third ∈
      orbitFaceBoundary RS
        (dartOrbitFace RS (RS.alpha (RS.phi dart))) := by
    rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho RS (RS.phi dart)]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS third
  apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).2
  refine ⟨?_, hleft, hright⟩
  apply (mem_interiorEdgeSupport_iff (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).2
  refine ⟨Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hleft⟩, ?_⟩
  exact totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
    (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS) (Finset.mem_univ _) (Finset.mem_univ _)
        hfacesNe hleft hright

/-- The three rotation-system edges encountered at a cubic facial corner are
pairwise distinct and all incident to the corner vertex. -/
theorem cornerEdges_pairwise_ne_and_incident (RS : RotationSystem V E)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS) (dart : RS.D) :
    let side := RS.edgeOf dart
    let forward := RS.edgeOf (RS.phi dart)
    let third := RS.edgeOf (RS.rho (RS.phi dart))
    let vertex := RS.vertOf (RS.phi dart)
    side ≠ forward ∧ side ≠ third ∧ forward ≠ third ∧
      side ∈ RS.incidentEdges vertex ∧
      forward ∈ RS.incidentEdges vertex ∧
      third ∈ RS.incidentEdges vertex := by
  dsimp only
  have hdarts := cornerDarts_pairwise_ne RS hcubic hrotation dart
  have halphaMem : RS.alpha dart ∈ RS.dartsAt (RS.vertOf (RS.phi dart)) := by
    simpa [RotationSystem.dartsAt] using
      (RS.vert_phi_eq_vert_alpha dart).symm
  have hphiMem : RS.phi dart ∈ RS.dartsAt (RS.vertOf (RS.phi dart)) := by
    simp [RotationSystem.dartsAt]
  have hrhoPhiMem : RS.rho (RS.phi dart) ∈
      RS.dartsAt (RS.vertOf (RS.phi dart)) := by
    simpa [RotationSystem.dartsAt] using RS.vert_rho (RS.phi dart)
  have hsideForward : RS.edgeOf dart ≠ RS.edgeOf (RS.phi dart) := by
    intro hedge
    apply hdarts.1
    apply RS.edgeOf_injOn_dartsAt (RS.vertOf (RS.phi dart))
      halphaMem hphiMem
    exact (RS.edge_alpha dart).trans hedge
  have hsideThird : RS.edgeOf dart ≠ RS.edgeOf (RS.rho (RS.phi dart)) := by
    intro hedge
    apply hdarts.2.1
    apply RS.edgeOf_injOn_dartsAt (RS.vertOf (RS.phi dart))
      halphaMem hrhoPhiMem
    exact (RS.edge_alpha dart).trans hedge
  have hforwardThird : RS.edgeOf (RS.phi dart) ≠
      RS.edgeOf (RS.rho (RS.phi dart)) := by
    intro hedge
    apply hdarts.2.2
    apply RS.edgeOf_injOn_dartsAt (RS.vertOf (RS.phi dart))
      hphiMem hrhoPhiMem hedge
  refine ⟨hsideForward, hsideThird, hforwardThird, ?_, ?_, ?_⟩
  · apply (RS.mem_incidentEdges_iff).2
    exact ⟨RS.alpha dart, RS.edge_alpha dart,
      (RS.vert_phi_eq_vert_alpha dart).symm⟩
  · apply (RS.mem_incidentEdges_iff).2
    exact ⟨RS.phi dart, rfl, rfl⟩
  · apply (RS.mem_incidentEdges_iff).2
    exact ⟨RS.rho (RS.phi dart), rfl, RS.vert_rho (RS.phi dart)⟩

/-- Local graph-backed Tait transfer at a cubic facial corner. The color on
the third edge is uniquely forced by the boundary edge and its facial
successor. -/
theorem taitColor_thirdCornerEdge_eq_add (RS : RotationSystem V E)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) (dart : RS.D) :
    C (RS.edgeOf (RS.rho (RS.phi dart))) =
      C (RS.edgeOf dart) + C (RS.edgeOf (RS.phi dart)) := by
  obtain ⟨hsideForward, hsideThird, hforwardThird,
      hsideMem, hforwardMem, hthirdMem⟩ :=
    cornerEdges_pairwise_ne_and_incident RS hcubic hrotation dart
  have hcolorSideForward : C (RS.edgeOf dart) ≠ C (RS.edgeOf (RS.phi dart)) :=
    C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hsideForward hsideMem hforwardMem)
  have hcolorSideThird : C (RS.edgeOf dart) ≠
      C (RS.edgeOf (RS.rho (RS.phi dart))) :=
    C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hsideThird hsideMem hthirdMem)
  have hcolorForwardThird : C (RS.edgeOf (RS.phi dart)) ≠
      C (RS.edgeOf (RS.rho (RS.phi dart))) :=
    C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hforwardThird hforwardMem hthirdMem)
  exact color_eq_add_of_three_distinct_nonzero
    (hC _) (hC _) (hC _)
      hcolorSideForward hcolorSideThird hcolorForwardThird

/-- The third edge at the endpoint where the side slot immediately before the
outgoing rung meets that rung. -/
def beforeOutgoingCornerEdge
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) : E :=
  RS.edgeOf (RS.rho
    (faceCycleDart RS placement.root placement.outgoingPosition))

/-- The third edge at the other endpoint of the outgoing rung, where the
slot immediately after the rung begins. -/
def afterOutgoingCornerEdge
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) : E :=
  RS.edgeOf (RS.rho (RS.phi
    (faceCycleDart RS placement.root placement.outgoingPosition)))

/-- A real Tait coloring determines the first next-slab corner edge from the
preceding side edge and the outgoing rung color. -/
theorem taitColor_beforeOutgoingCornerEdge_eq_add
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : {position // position ∈ placementSidePositions placement})
    (hsuccessor : placement.outgoingPosition.val ≡ position.1.val + 1 [MOD 6])
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    C (beforeOutgoingCornerEdge placement) =
      C (placementSideEdge htwoSided placement position) +
        C (corridor.rungEdge hunique interior.outgoing) := by
  let sideDart := faceCycleDart RS placement.root position.1
  let outgoingDart :=
    faceCycleDart RS placement.root placement.outgoingPosition
  have hdarts : outgoingDart = RS.phi sideDart :=
    faceCycleDart_successor_of_modEq RS placement.root placement.orbit_card
      position.1 placement.outgoingPosition hsuccessor
  have htransfer := taitColor_thirdCornerEdge_eq_add RS hcubic hrotation C hC sideDart
  change C (RS.edgeOf (RS.rho outgoingDart)) =
    C (RS.edgeOf sideDart) +
      C (corridor.rungEdge hunique interior.outgoing)
  rw [← placement.outgoing_edge]
  change C (RS.edgeOf (RS.rho outgoingDart)) =
    C (RS.edgeOf sideDart) + C (RS.edgeOf outgoingDart)
  rw [hdarts]
  exact htransfer

/-- A real Tait coloring determines the second next-slab corner edge from
the outgoing rung and the following side edge color. -/
theorem taitColor_afterOutgoingCornerEdge_eq_add
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : {position // position ∈ placementSidePositions placement})
    (hsuccessor : position.1.val ≡ placement.outgoingPosition.val + 1 [MOD 6])
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    C (afterOutgoingCornerEdge placement) =
      C (corridor.rungEdge hunique interior.outgoing) +
        C (placementSideEdge htwoSided placement position) := by
  let outgoingDart :=
    faceCycleDart RS placement.root placement.outgoingPosition
  let sideDart := faceCycleDart RS placement.root position.1
  have hdarts : sideDart = RS.phi outgoingDart :=
    faceCycleDart_successor_of_modEq RS placement.root placement.orbit_card
      placement.outgoingPosition position.1 hsuccessor
  have htransfer :=
    taitColor_thirdCornerEdge_eq_add RS hcubic hrotation C hC outgoingDart
  change C (RS.edgeOf (RS.rho (RS.phi outgoingDart))) =
    C (corridor.rungEdge hunique interior.outgoing) +
      C (RS.edgeOf sideDart)
  rw [← placement.outgoing_edge]
  change C (RS.edgeOf (RS.rho (RS.phi outgoingDart))) =
    C (RS.edgeOf outgoingDart) + C (RS.edgeOf sideDart)
  rw [hdarts]
  exact htransfer

/-- The first corner edge is not merely adjacent to the next slab: pairwise
face-intersection uniqueness identifies it with an actual ordered side edge
of every placement of that slab. -/
theorem exists_nextPlacementSideEdge_eq_beforeOutgoingCornerEdge
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (leftInterior : CorridorInterior corridorLength)
    (hnext : leftInterior.center.val + 2 < corridorLength)
    (leftPlacement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique leftInterior)
    (leftPosition :
      {position // position ∈ placementSidePositions leftPlacement})
    (hsuccessor : leftPlacement.outgoingPosition.val ≡
      leftPosition.1.val + 1 [MOD 6])
    (rightPlacement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique
        (nextCorridorInterior leftInterior hnext)) :
    ∃ rightPosition :
        {position // position ∈ placementSidePositions rightPlacement},
      placementSideEdge htwoSided rightPlacement rightPosition =
        beforeOutgoingCornerEdge leftPlacement ∧
      placementSideNeighbor clean htwoSided hunique leftPlacement leftPosition =
        placementSideNeighbor clean htwoSided hunique rightPlacement rightPosition := by
  let corridor := clean.toOrbitHexCorridorSkeleton
  let rightInterior := nextCorridorInterior leftInterior hnext
  let leftFace :=
    placementSideNeighbor clean htwoSided hunique leftPlacement leftPosition
  let rightCenter := corridor.faceAt rightInterior.center
  have hadjRaw := placementSideNeighbor_adjacent_next_of_before_outgoing
    clean hcubic hrotation htwoSided hunique leftPlacement leftPosition hsuccessor
  have hadj : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj rightCenter leftFace := by
    simpa [rightCenter, rightInterior, leftFace, corridor,
      nextCorridorInterior] using hadjRaw.symm
  have hleftExternal : ∀ index : Fin corridorLength,
      leftFace ≠ corridor.faceAt index := by
    intro index
    exact placementSideNeighbor_ne_faceAt clean htwoSided hunique leftPlacement
      leftPosition index
  rcases exists_placementSideNeighbor_eq_of_adjacent_external clean htwoSided
    hunique rightPlacement leftFace hadj (by simpa [corridor] using hleftExternal) with
      ⟨rightPosition, hrightNeighbor⟩
  let rightSide := placementSideEdge htwoSided rightPlacement rightPosition
  have hrightBoundary : rightSide.1 ∈ orbitFaceBoundary RS rightCenter.1 := by
    exact ((mem_internalSideEdges_iff corridor hunique rightInterior rightSide.1).1
      rightSide.2).1
  let rightWitness := orbitFaceAcrossEdgeWitness RS htwoSided rightCenter
    rightSide.1 hrightBoundary
  have hrightWitnessEq : rightWitness.across = leftFace := by
    change placementSideNeighbor clean htwoSided hunique rightPlacement
      rightPosition = leftFace
    exact hrightNeighbor
  have hrightShared : rightSide.1 ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) leftFace.1 rightCenter.1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
    refine ⟨rightWitness.edge_interior, ?_, hrightBoundary⟩
    rw [← hrightWitnessEq]
    exact rightWitness.edge_mem_across
  let sideDart := faceCycleDart RS leftPlacement.root leftPosition.1
  let outgoingDart :=
    faceCycleDart RS leftPlacement.root leftPlacement.outgoingPosition
  have hdarts : outgoingDart = RS.phi sideDart :=
    faceCycleDart_successor_of_modEq RS leftPlacement.root
      leftPlacement.orbit_card leftPosition.1
        leftPlacement.outgoingPosition hsuccessor
  have hleftFaceEq : dartOrbitFace RS (RS.alpha sideDart) = leftFace.1 := by
    have hneighbor := placementSideNeighbor_eq_alphaFace clean htwoSided hunique
      leftPlacement leftPosition
    exact (congrArg Subtype.val hneighbor).symm
  have hrightFaceEq : dartOrbitFace RS (RS.alpha (RS.phi sideDart)) =
      rightCenter.1 := by
    rw [← hdarts]
    exact outgoing_alpha_face_eq_next htwoSided leftPlacement
  have hcornerFacesNe : dartOrbitFace RS (RS.alpha sideDart) ≠
      dartOrbitFace RS (RS.alpha (RS.phi sideDart)) := by
    rw [hleftFaceEq, hrightFaceEq]
    exact fun hfaces => hadj.ne.symm (Subtype.ext hfaces)
  have hcornerSharedRaw := thirdCornerEdge_mem_sharedInteriorEdges RS hcubic
    hrotation sideDart hcornerFacesNe
  have hcornerShared : beforeOutgoingCornerEdge leftPlacement ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) leftFace.1 rightCenter.1 := by
    rw [← hleftFaceEq, ← hrightFaceEq]
    change RS.edgeOf (RS.rho outgoingDart) ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))
          (dartOrbitFace RS (RS.alpha sideDart))
          (dartOrbitFace RS (RS.alpha (RS.phi sideDart)))
    rw [hdarts]
    exact hcornerSharedRaw
  have hfaceNe : leftFace.1 ≠ rightCenter.1 :=
    fun hfaces => hadj.ne.symm (Subtype.ext hfaces)
  have hedgeEq : rightSide.1 = beforeOutgoingCornerEdge leftPlacement :=
    (Finset.card_le_one_iff.1
      (hunique leftFace.1 leftFace.2 rightCenter.1 rightCenter.2 hfaceNe))
        hrightShared hcornerShared
  refine ⟨rightPosition, hedgeEq, ?_⟩
  exact hrightNeighbor.symm

/-- The second corner edge is likewise an actual ordered side edge of every
placement of the next slab. -/
theorem exists_nextPlacementSideEdge_eq_afterOutgoingCornerEdge
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (leftInterior : CorridorInterior corridorLength)
    (hnext : leftInterior.center.val + 2 < corridorLength)
    (leftPlacement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique leftInterior)
    (leftPosition :
      {position // position ∈ placementSidePositions leftPlacement})
    (hsuccessor : leftPosition.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6])
    (rightPlacement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique
        (nextCorridorInterior leftInterior hnext)) :
    ∃ rightPosition :
        {position // position ∈ placementSidePositions rightPlacement},
      placementSideEdge htwoSided rightPlacement rightPosition =
        afterOutgoingCornerEdge leftPlacement ∧
      placementSideNeighbor clean htwoSided hunique leftPlacement leftPosition =
        placementSideNeighbor clean htwoSided hunique rightPlacement rightPosition := by
  let corridor := clean.toOrbitHexCorridorSkeleton
  let rightInterior := nextCorridorInterior leftInterior hnext
  let leftFace :=
    placementSideNeighbor clean htwoSided hunique leftPlacement leftPosition
  let rightCenter := corridor.faceAt rightInterior.center
  have hadjRaw := placementSideNeighbor_adjacent_next_of_after_outgoing
    clean hcubic hrotation htwoSided hunique leftPlacement leftPosition hsuccessor
  have hadj : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj rightCenter leftFace := by
    simpa [rightCenter, rightInterior, leftFace, corridor,
      nextCorridorInterior] using hadjRaw.symm
  have hleftExternal : ∀ index : Fin corridorLength,
      leftFace ≠ corridor.faceAt index := by
    intro index
    exact placementSideNeighbor_ne_faceAt clean htwoSided hunique leftPlacement
      leftPosition index
  rcases exists_placementSideNeighbor_eq_of_adjacent_external clean htwoSided
    hunique rightPlacement leftFace hadj (by simpa [corridor] using hleftExternal) with
      ⟨rightPosition, hrightNeighbor⟩
  let rightSide := placementSideEdge htwoSided rightPlacement rightPosition
  have hrightBoundary : rightSide.1 ∈ orbitFaceBoundary RS rightCenter.1 := by
    exact ((mem_internalSideEdges_iff corridor hunique rightInterior rightSide.1).1
      rightSide.2).1
  let rightWitness := orbitFaceAcrossEdgeWitness RS htwoSided rightCenter
    rightSide.1 hrightBoundary
  have hrightWitnessEq : rightWitness.across = leftFace := by
    change placementSideNeighbor clean htwoSided hunique rightPlacement
      rightPosition = leftFace
    exact hrightNeighbor
  have hrightShared : rightSide.1 ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) rightCenter.1 leftFace.1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
    refine ⟨rightWitness.edge_interior, hrightBoundary, ?_⟩
    rw [← hrightWitnessEq]
    exact rightWitness.edge_mem_across
  let outgoingDart :=
    faceCycleDart RS leftPlacement.root leftPlacement.outgoingPosition
  let sideDart := faceCycleDart RS leftPlacement.root leftPosition.1
  have hdarts : sideDart = RS.phi outgoingDart :=
    faceCycleDart_successor_of_modEq RS leftPlacement.root
      leftPlacement.orbit_card leftPlacement.outgoingPosition
        leftPosition.1 hsuccessor
  have hrightFaceEq : dartOrbitFace RS (RS.alpha outgoingDart) =
      rightCenter.1 :=
    outgoing_alpha_face_eq_next htwoSided leftPlacement
  have hleftFaceEq : dartOrbitFace RS (RS.alpha (RS.phi outgoingDart)) =
      leftFace.1 := by
    rw [← hdarts]
    have hneighbor := placementSideNeighbor_eq_alphaFace clean htwoSided hunique
      leftPlacement leftPosition
    exact (congrArg Subtype.val hneighbor).symm
  have hcornerFacesNe : dartOrbitFace RS (RS.alpha outgoingDart) ≠
      dartOrbitFace RS (RS.alpha (RS.phi outgoingDart)) := by
    rw [hrightFaceEq, hleftFaceEq]
    exact fun hfaces => hadj.ne (Subtype.ext hfaces)
  have hcornerSharedRaw := thirdCornerEdge_mem_sharedInteriorEdges RS hcubic
    hrotation outgoingDart hcornerFacesNe
  have hcornerShared : afterOutgoingCornerEdge leftPlacement ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) rightCenter.1 leftFace.1 := by
    rw [← hrightFaceEq, ← hleftFaceEq]
    exact hcornerSharedRaw
  have hfaceNe : rightCenter.1 ≠ leftFace.1 :=
    fun hfaces => hadj.ne (Subtype.ext hfaces)
  have hedgeEq : rightSide.1 = afterOutgoingCornerEdge leftPlacement :=
    (Finset.card_le_one_iff.1
      (hunique rightCenter.1 rightCenter.2 leftFace.1 leftFace.2 hfaceNe))
        hrightShared hcornerShared
  refine ⟨rightPosition, hedgeEq, ?_⟩
  exact hrightNeighbor.symm

/-- Computed two-corner Tait transfer between consecutive clean hex slabs.
The witnesses are actual ordered side slots. Their edge identities, external
face matches, and colors are all derived from the rotation system and the
given Tait coloring. -/
def ConsecutiveSlabTaitColorTransfer
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (leftInterior : CorridorInterior corridorLength)
    (hnext : leftInterior.center.val + 2 < corridorLength)
    (leftPlacement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique leftInterior)
    (rightPlacement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique
        (nextCorridorInterior leftInterior hnext))
    (C : RS.EdgeColoring Color) : Prop :=
  ∃ leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement},
    ∃ rightBefore rightAfter :
      {position // position ∈ placementSidePositions rightPlacement},
      leftBefore ≠ leftAfter ∧ rightBefore ≠ rightAfter ∧
      placementSideEdge htwoSided rightPlacement rightBefore =
        beforeOutgoingCornerEdge leftPlacement ∧
      placementSideEdge htwoSided rightPlacement rightAfter =
        afterOutgoingCornerEdge leftPlacement ∧
      placementSideNeighbor clean htwoSided hunique leftPlacement leftBefore =
        placementSideNeighbor clean htwoSided hunique rightPlacement rightBefore ∧
      placementSideNeighbor clean htwoSided hunique leftPlacement leftAfter =
        placementSideNeighbor clean htwoSided hunique rightPlacement rightAfter ∧
      C (placementSideEdge htwoSided rightPlacement rightBefore) =
        C (placementSideEdge htwoSided leftPlacement leftBefore) +
          C (clean.toOrbitHexCorridorSkeleton.rungEdge hunique
            leftInterior.outgoing) ∧
      C (placementSideEdge htwoSided rightPlacement rightAfter) =
        C (clean.toOrbitHexCorridorSkeleton.rungEdge hunique
          leftInterior.outgoing) +
          C (placementSideEdge htwoSided leftPlacement leftAfter)

/-- A real Tait coloring transfers across both corners of every consecutive
pair of clean internal hex slabs. This is the first graph-backed color
transition theorem for the v24 corridor: no interface matching or color law
is supplied as data. -/
theorem consecutiveSlabTaitColorTransfer
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (leftInterior : CorridorInterior corridorLength)
    (hnext : leftInterior.center.val + 2 < corridorLength)
    (leftPlacement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique leftInterior)
    (rightPlacement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique
        (nextCorridorInterior leftInterior hnext))
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    ConsecutiveSlabTaitColorTransfer clean htwoSided hunique leftInterior hnext
      leftPlacement rightPlacement C := by
  have hnonadjacent : leftPlacement.rungType ≠ HexRungType.adjacent :=
    GoertzelV24InducedHexCorridorTypes.InternalHexRungPlacement.rungType_ne_adjacent
      leftPlacement hcubic hrotation htwoSided
  rcases exists_two_hexSidePositions_flanking_outgoing
    leftPlacement.incomingPosition6 leftPlacement.outgoingPosition6
      leftPlacement.positions6_ne hnonadjacent with
    ⟨before6, after6, hbeforeAfter, hbeforeMod, hafterMod⟩
  let leftBefore := placementSidePositionOfSix leftPlacement before6
  let leftAfter := placementSidePositionOfSix leftPlacement after6
  have hleftBeforeAfter : leftBefore ≠ leftAfter := by
    intro heq
    apply hbeforeAfter
    apply Subtype.ext
    have hvals := congrArg (fun position => position.1.val) heq
    exact Fin.ext hvals
  have hbeforeActual : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6] := by
    simpa [leftBefore, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.outgoingPosition6] using hbeforeMod
  have hafterActual : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6] := by
    simpa [leftAfter, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.outgoingPosition6] using hafterMod
  rcases exists_nextPlacementSideEdge_eq_beforeOutgoingCornerEdge
    clean hcubic hrotation htwoSided hunique leftInterior hnext leftPlacement
      leftBefore hbeforeActual rightPlacement with
    ⟨rightBefore, hrightBeforeEdge, hrightBeforeFace⟩
  rcases exists_nextPlacementSideEdge_eq_afterOutgoingCornerEdge
    clean hcubic hrotation htwoSided hunique leftInterior hnext leftPlacement
      leftAfter hafterActual rightPlacement with
    ⟨rightAfter, hrightAfterEdge, hrightAfterFace⟩
  have hrightBeforeAfter : rightBefore ≠ rightAfter := by
    intro heq
    apply hleftBeforeAfter
    apply placementSideNeighbor_injective clean htwoSided hunique leftPlacement
    calc
      placementSideNeighbor clean htwoSided hunique leftPlacement leftBefore =
          placementSideNeighbor clean htwoSided hunique rightPlacement rightBefore :=
        hrightBeforeFace
      _ = placementSideNeighbor clean htwoSided hunique rightPlacement rightAfter := by
        rw [heq]
      _ = placementSideNeighbor clean htwoSided hunique leftPlacement leftAfter :=
        hrightAfterFace.symm
  have hbeforeColor :
      C (placementSideEdge htwoSided rightPlacement rightBefore) =
        C (placementSideEdge htwoSided leftPlacement leftBefore) +
          C (clean.toOrbitHexCorridorSkeleton.rungEdge hunique
            leftInterior.outgoing) := by
    calc
      C (placementSideEdge htwoSided rightPlacement rightBefore) =
          C (beforeOutgoingCornerEdge leftPlacement) :=
        congrArg C hrightBeforeEdge
      _ = C (placementSideEdge htwoSided leftPlacement leftBefore) +
          C (clean.toOrbitHexCorridorSkeleton.rungEdge hunique
            leftInterior.outgoing) :=
        taitColor_beforeOutgoingCornerEdge_eq_add hcubic hrotation htwoSided
          leftPlacement leftBefore hbeforeActual C hC
  have hafterColor :
      C (placementSideEdge htwoSided rightPlacement rightAfter) =
        C (clean.toOrbitHexCorridorSkeleton.rungEdge hunique
          leftInterior.outgoing) +
          C (placementSideEdge htwoSided leftPlacement leftAfter) := by
    calc
      C (placementSideEdge htwoSided rightPlacement rightAfter) =
          C (afterOutgoingCornerEdge leftPlacement) :=
        congrArg C hrightAfterEdge
      _ = C (clean.toOrbitHexCorridorSkeleton.rungEdge hunique
          leftInterior.outgoing) +
          C (placementSideEdge htwoSided leftPlacement leftAfter) :=
        taitColor_afterOutgoingCornerEdge_eq_add hcubic hrotation htwoSided
          leftPlacement leftAfter hafterActual C hC
  exact ⟨leftBefore, leftAfter, rightBefore, rightAfter,
    hleftBeforeAfter, hrightBeforeAfter, hrightBeforeEdge, hrightAfterEdge,
    hrightBeforeFace, hrightAfterFace, hbeforeColor, hafterColor⟩

end

end GoertzelV24HexCorridorColorTransfer

end Mettapedia.GraphTheory.FourColor
