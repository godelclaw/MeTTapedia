import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabSideAdjacency

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCorridorInterfaceMatching

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The four side slots are complete for external dual neighbors of an
internal corridor face. Thus later slab matching can discover interface faces
from adjacency without assuming a separate coverage field. -/
theorem exists_internalSideNeighbor_eq_of_adjacent_external
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength)
    (neighbor : AmbientFace (Finset.univ : Finset (OrbitFace RS)))
    (hadj : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (clean.toOrbitHexCorridorSkeleton.faceAt interior.center) neighbor)
    (hexternal : ∀ index : Fin corridorLength,
      neighbor ≠ clean.toOrbitHexCorridorSkeleton.faceAt index) :
    ∃ side : {edge // edge ∈ internalSideEdges
        clean.toOrbitHexCorridorSkeleton hunique interior},
      internalSideNeighbor clean htwoSided hunique interior side = neighbor := by
  let corridor := clean.toOrbitHexCorridorSkeleton
  let center := corridor.faceAt interior.center
  rcases (interiorDualGraph_adj_iff (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).1 hadj with
      ⟨hcenterNeighbor, edge, hedgeInterior, hedgeCenter, hedgeNeighbor⟩
  have hedgeNeIncoming : edge ≠ corridor.rungEdge hunique interior.incoming := by
    intro hedge
    have hcenterPredecessor : center.1 ≠
        (corridor.faceAt interior.incoming.left).1 := by
      intro hfaces
      have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
      have hvalues := congrArg Fin.val hindices
      change interior.center.val = interior.center.val - 1 at hvalues
      have hcenterPositive := interior.center_pos
      omega
    have hedgePredecessor : edge ∈
        orbitFaceBoundary RS (corridor.faceAt interior.incoming.left).1 := by
      rw [hedge]
      exact corridor.rungEdge_mem_left hunique interior.incoming
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
        (orbitFace_incidence_le_two RS)
        center.2 (corridor.faceAt interior.incoming.left).2 neighbor.2
        hcenterPredecessor hedgeCenter hedgePredecessor hedgeNeighbor
    rcases hcases with hcenter | hpredecessor
    · exact hcenterNeighbor hcenter.symm
    · exact hexternal interior.incoming.left (Subtype.ext hpredecessor)
  have hedgeNeOutgoing : edge ≠ corridor.rungEdge hunique interior.outgoing := by
    intro hedge
    have hcenterSuccessor : center.1 ≠
        (corridor.faceAt interior.outgoing.right).1 := by
      intro hfaces
      have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
      have hvals := congrArg Fin.val hindices
      change interior.center.val = interior.center.val + 1 at hvals
      omega
    have hedgeSuccessor : edge ∈
        orbitFaceBoundary RS (corridor.faceAt interior.outgoing.right).1 := by
      rw [hedge]
      exact corridor.rungEdge_mem_right hunique interior.outgoing
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
        (orbitFace_incidence_le_two RS)
        center.2 (corridor.faceAt interior.outgoing.right).2 neighbor.2
        hcenterSuccessor hedgeCenter hedgeSuccessor hedgeNeighbor
    rcases hcases with hcenter | hsuccessor
    · exact hcenterNeighbor hcenter.symm
    · exact hexternal interior.outgoing.right (Subtype.ext hsuccessor)
  let side : {edge // edge ∈ internalSideEdges corridor hunique interior} :=
    ⟨edge, (mem_internalSideEdges_iff corridor hunique interior edge).2
      ⟨hedgeCenter, hedgeNeIncoming, hedgeNeOutgoing⟩⟩
  refine ⟨side, ?_⟩
  let witness := orbitFaceAcrossEdgeWitness RS htwoSided center edge hedgeCenter
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS)
      center.2 witness.across.2 neighbor.2
      (fun heq => witness.face_ne_across (Subtype.ext heq))
      hedgeCenter witness.edge_mem_across hedgeNeighbor
  change witness.across = neighbor
  rcases hcases with hcenter | hacross
  · exact (hcenterNeighbor hcenter.symm).elim
  · exact Subtype.ext hacross.symm

/-- The position of a standard six-cycle transported back to the actual
facial cycle of a placed corridor hexagon. -/
def placementPositionOfSix
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : Fin 6) : Fin (RS.faceOrbit placement.root).card :=
  Fin.cast placement.orbit_card.symm position

@[simp]
theorem placementPositionOfSix_val
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : Fin 6) :
    (placementPositionOfSix placement position).val = position.val :=
  rfl

@[simp]
theorem placementPositionOfSix_incomingPosition6
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    placementPositionOfSix placement placement.incomingPosition6 =
      placement.incomingPosition := by
  apply Fin.ext
  rfl

@[simp]
theorem placementPositionOfSix_outgoingPosition6
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    placementPositionOfSix placement placement.outgoingPosition6 =
      placement.outgoingPosition := by
  apply Fin.ext
  rfl

/-- A standard non-rung position transported to the actual four-slot side
interface of a placed corridor hexagon. -/
def placementSidePositionOfSix
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : {position // position ∈ hexSidePositions
      placement.incomingPosition6 placement.outgoingPosition6}) :
    {position // position ∈ placementSidePositions placement} :=
  ⟨placementPositionOfSix placement position.1, by
    apply (mem_placementSidePositions_iff placement _).2
    have hposition := position.2
    simp only [hexSidePositions, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hposition
    exact ⟨fun heq => hposition.1 (by
        apply Fin.ext
        simpa [placementPositionOfSix,
          InternalHexRungPlacement.incomingPosition6] using
            congrArg Fin.val heq),
      fun heq => hposition.2 (by
        apply Fin.ext
        simpa [placementPositionOfSix,
          InternalHexRungPlacement.outgoingPosition6] using
            congrArg Fin.val heq)⟩⟩

/-- The two retained side slots immediately before and after a non-adjacent
outgoing rung are distinct. -/
theorem exists_two_hexSidePositions_flanking_outgoing
    (incoming outgoing : Fin 6) (hne : incoming ≠ outgoing)
    (hnonadjacent : hexRungType incoming outgoing ≠ HexRungType.adjacent) :
    ∃ before after : {position // position ∈ hexSidePositions incoming outgoing},
      before ≠ after ∧
      outgoing.val ≡ before.1.val + 1 [MOD 6] ∧
      after.1.val ≡ outgoing.val + 1 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexSidePositions, hexRungType, hexCyclicDistance,
      hexForwardDistance, Nat.ModEq] at *
  all_goals decide

/-- Every external neighbor can also be recovered through the ordered
four-slot representation of any actual rung placement. -/
theorem exists_placementSideNeighbor_eq_of_adjacent_external
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique interior)
    (neighbor : AmbientFace (Finset.univ : Finset (OrbitFace RS)))
    (hadj : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (clean.toOrbitHexCorridorSkeleton.faceAt interior.center) neighbor)
    (hexternal : ∀ index : Fin corridorLength,
      neighbor ≠ clean.toOrbitHexCorridorSkeleton.faceAt index) :
    ∃ position : {position // position ∈ placementSidePositions placement},
      placementSideNeighbor clean htwoSided hunique placement position = neighbor := by
  rcases exists_internalSideNeighbor_eq_of_adjacent_external clean htwoSided
    hunique interior neighbor hadj hexternal with ⟨side, hsideNeighbor⟩
  have hsideImage : side.1 ∈
      (placementSidePositions placement).image
        (faceCycleEdge RS placement.root) := by
    rw [image_faceCycleEdge_placementSidePositions htwoSided placement]
    exact side.2
  rcases Finset.mem_image.1 hsideImage with
    ⟨position, hposition, hpositionEdge⟩
  let placedPosition : {position // position ∈ placementSidePositions placement} :=
    ⟨position, hposition⟩
  refine ⟨placedPosition, ?_⟩
  have hedge : placementSideEdge htwoSided placement placedPosition = side := by
    exact Subtype.ext hpositionEdge
  change internalSideNeighbor clean htwoSided hunique interior
      (placementSideEdge htwoSided placement placedPosition) = neighbor
  rw [hedge]
  exact hsideNeighbor

/-- The next internal corridor face, when one further successor exists. -/
def nextCorridorInterior {corridorLength : Nat}
    (interior : CorridorInterior corridorLength)
    (hnext : interior.center.val + 2 < corridorLength) :
    CorridorInterior corridorLength where
  center := interior.outgoing.right
  center_pos := by
    change 0 < interior.center.val + 1
    omega
  center_succ_lt := by
    change interior.center.val + 1 + 1 < corridorLength
    omega

@[simp]
theorem next_center {corridorLength : Nat}
    (interior : CorridorInterior corridorLength)
    (hnext : interior.center.val + 2 < corridorLength) :
    (nextCorridorInterior interior hnext).center = interior.outgoing.right :=
  rfl

/-- The face opposite the outgoing rung is the next corridor face. -/
theorem outgoing_alpha_face_eq_next
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    (htwoSided : OrbitFacesTwoSided RS)
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    dartOrbitFace RS (RS.alpha
      (faceCycleDart RS placement.root placement.outgoingPosition)) =
      (corridor.faceAt interior.outgoing.right).1 := by
  let outgoingDart :=
    faceCycleDart RS placement.root placement.outgoingPosition
  have houtgoingFace : dartOrbitFace RS outgoingDart =
      (corridor.faceAt interior.center).1 := by
    calc
      dartOrbitFace RS outgoingDart = dartOrbitFace RS placement.root :=
        dartOrbitFace_faceCycleDart RS placement.root placement.outgoingPosition
      _ = (corridor.faceAt interior.center).1 := placement.root_face
  have houtgoingEdge : RS.edgeOf outgoingDart =
      corridor.rungEdge hunique interior.outgoing := placement.outgoing_edge
  have hedgeNext : RS.edgeOf outgoingDart ∈
      orbitFaceBoundary RS (corridor.faceAt interior.outgoing.right).1 := by
    rw [houtgoingEdge]
    exact corridor.rungEdge_mem_right hunique interior.outgoing
  apply dartOrbitFace_alpha_eq_of_mem_other_face RS htwoSided outgoingDart
    (corridor.faceAt interior.outgoing.right).1 hedgeNext
  rw [houtgoingFace]
  intro hfaces
  have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
  have hvalues := congrArg Fin.val hindices
  change interior.center.val = interior.center.val + 1 at hvalues
  omega

/-- A retained side slot immediately before the outgoing rung reaches a face
adjacent to the next corridor hexagon. -/
theorem placementSideNeighbor_adjacent_next_of_before_outgoing
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique interior)
    (position : {position // position ∈ placementSidePositions placement})
    (hsuccessor : placement.outgoingPosition.val ≡ position.1.val + 1 [MOD 6]) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (placementSideNeighbor clean htwoSided hunique placement position)
        (clean.toOrbitHexCorridorSkeleton.faceAt interior.outgoing.right) := by
  let sideDart := faceCycleDart RS placement.root position.1
  let outgoingDart :=
    faceCycleDart RS placement.root placement.outgoingPosition
  have hdarts : outgoingDart = RS.phi sideDart :=
    faceCycleDart_successor_of_modEq RS placement.root placement.orbit_card
      position.1 placement.outgoingPosition hsuccessor
  have houtgoingOpposite : dartOrbitFace RS (RS.alpha outgoingDart) =
      (clean.toOrbitHexCorridorSkeleton.faceAt interior.outgoing.right).1 :=
    outgoing_alpha_face_eq_next htwoSided placement
  have hcornerNe : dartOrbitFace RS (RS.alpha sideDart) ≠
      dartOrbitFace RS (RS.alpha (RS.phi sideDart)) := by
    intro hfaces
    apply placementSideNeighbor_ne_faceAt clean htwoSided hunique placement
      position interior.outgoing.right
    apply Subtype.ext
    rw [placementSideNeighbor_eq_alphaFace clean htwoSided hunique placement
      position]
    exact hfaces.trans (by simpa only [← hdarts] using houtgoingOpposite)
  have hadj := oppositeFaces_adjacent_at_cubic_corner RS hcubic hrotation
    sideDart hcornerNe
  rw [placementSideNeighbor_eq_alphaFace clean htwoSided hunique placement
    position]
  convert hadj using 1
  apply Subtype.ext
  simpa only [← hdarts] using houtgoingOpposite.symm

/-- A retained side slot immediately after the outgoing rung also reaches a
face adjacent to the next corridor hexagon. -/
theorem placementSideNeighbor_adjacent_next_of_after_outgoing
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique interior)
    (position : {position // position ∈ placementSidePositions placement})
    (hsuccessor : position.1.val ≡ placement.outgoingPosition.val + 1 [MOD 6]) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (placementSideNeighbor clean htwoSided hunique placement position)
        (clean.toOrbitHexCorridorSkeleton.faceAt interior.outgoing.right) := by
  let outgoingDart :=
    faceCycleDart RS placement.root placement.outgoingPosition
  let sideDart := faceCycleDart RS placement.root position.1
  have hdarts : sideDart = RS.phi outgoingDart :=
    faceCycleDart_successor_of_modEq RS placement.root placement.orbit_card
      placement.outgoingPosition position.1 hsuccessor
  have houtgoingOpposite : dartOrbitFace RS (RS.alpha outgoingDart) =
      (clean.toOrbitHexCorridorSkeleton.faceAt interior.outgoing.right).1 :=
    outgoing_alpha_face_eq_next htwoSided placement
  have hcornerNe : dartOrbitFace RS (RS.alpha outgoingDart) ≠
      dartOrbitFace RS (RS.alpha (RS.phi outgoingDart)) := by
    intro hfaces
    apply placementSideNeighbor_ne_faceAt clean htwoSided hunique placement
      position interior.outgoing.right
    apply Subtype.ext
    rw [placementSideNeighbor_eq_alphaFace clean htwoSided hunique placement
      position]
    have hsideOpposite : dartOrbitFace RS (RS.alpha sideDart) =
        (clean.toOrbitHexCorridorSkeleton.faceAt interior.outgoing.right).1 := by
      rw [hdarts]
      exact hfaces.symm.trans houtgoingOpposite
    exact hsideOpposite
  have hadj := oppositeFaces_adjacent_at_cubic_corner RS hcubic hrotation
    outgoingDart hcornerNe
  rw [placementSideNeighbor_eq_alphaFace clean htwoSided hunique placement
    position]
  convert hadj.symm using 1
  · apply Subtype.ext
    exact congrArg (fun dart => dartOrbitFace RS (RS.alpha dart)) hdarts
  · apply Subtype.ext
    simpa only using houtgoingOpposite.symm

/-- Computed compatibility of the width-four interfaces of two consecutive
internal corridor hexagons: two distinct side faces of the left slab are
also two distinct side faces of the right slab. -/
def ConsecutiveSlabInterfacesMatch
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
        (nextCorridorInterior leftInterior hnext)) : Prop :=
  ∃ leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement},
    ∃ rightBefore rightAfter :
      {position // position ∈ placementSidePositions rightPlacement},
      leftBefore ≠ leftAfter ∧ rightBefore ≠ rightAfter ∧
      placementSideNeighbor clean htwoSided hunique leftPlacement leftBefore =
        placementSideNeighbor clean htwoSided hunique rightPlacement rightBefore ∧
      placementSideNeighbor clean htwoSided hunique leftPlacement leftAfter =
        placementSideNeighbor clean htwoSided hunique rightPlacement rightAfter

/-- Consecutive clean hex slabs really have a two-face overlap. The matching
is derived from the facial rotations, cubic corners, and exact two-sided
incidence; it is not supplied as corridor data. -/
theorem consecutiveSlabInterfacesMatch
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
        (nextCorridorInterior leftInterior hnext)) :
    ConsecutiveSlabInterfacesMatch clean htwoSided hunique leftInterior hnext
      leftPlacement rightPlacement := by
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
  let beforeFace :=
    placementSideNeighbor clean htwoSided hunique leftPlacement leftBefore
  let afterFace :=
    placementSideNeighbor clean htwoSided hunique leftPlacement leftAfter
  have hbeforeAdjacent : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (clean.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior leftInterior hnext).center) beforeFace := by
    have hraw := placementSideNeighbor_adjacent_next_of_before_outgoing
      clean hcubic hrotation htwoSided hunique leftPlacement leftBefore hbeforeActual
    simpa [beforeFace, nextCorridorInterior] using hraw.symm
  have hafterAdjacent : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (clean.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior leftInterior hnext).center) afterFace := by
    have hraw := placementSideNeighbor_adjacent_next_of_after_outgoing
      clean hcubic hrotation htwoSided hunique leftPlacement leftAfter hafterActual
    simpa [afterFace, nextCorridorInterior] using hraw.symm
  have hbeforeExternal : ∀ index : Fin corridorLength,
      beforeFace ≠ clean.toOrbitHexCorridorSkeleton.faceAt index := by
    intro index
    exact placementSideNeighbor_ne_faceAt clean htwoSided hunique leftPlacement
      leftBefore index
  have hafterExternal : ∀ index : Fin corridorLength,
      afterFace ≠ clean.toOrbitHexCorridorSkeleton.faceAt index := by
    intro index
    exact placementSideNeighbor_ne_faceAt clean htwoSided hunique leftPlacement
      leftAfter index
  rcases exists_placementSideNeighbor_eq_of_adjacent_external clean htwoSided
    hunique rightPlacement beforeFace hbeforeAdjacent hbeforeExternal with
      ⟨rightBefore, hbeforeMatch⟩
  rcases exists_placementSideNeighbor_eq_of_adjacent_external clean htwoSided
    hunique rightPlacement afterFace hafterAdjacent hafterExternal with
      ⟨rightAfter, hafterMatch⟩
  have hrightBeforeAfter : rightBefore ≠ rightAfter := by
    intro heq
    apply hleftBeforeAfter
    apply placementSideNeighbor_injective clean htwoSided hunique leftPlacement
    change beforeFace = afterFace
    rw [← hbeforeMatch, ← hafterMatch, heq]
  refine ⟨leftBefore, leftAfter, rightBefore, rightAfter,
    hleftBeforeAfter, hrightBeforeAfter, ?_, ?_⟩
  · exact hbeforeMatch.symm
  · exact hafterMatch.symm

end

end GoertzelV24HexCorridorInterfaceMatching

end Mettapedia.GraphTheory.FourColor
