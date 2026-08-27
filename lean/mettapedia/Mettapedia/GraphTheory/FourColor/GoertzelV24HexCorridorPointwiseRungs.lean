import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabSideAdjacency
import Mettapedia.GraphTheory.FourColor.GoertzelV24InteriorDualPointwiseLookup

/-!
# Corridor rungs from pointwise face intersections

The opened annular carrier need not have globally simple face intersections:
the two faces created by the opening can share many edges.  A corridor never
uses that global statement.  At one consecutive pair it needs only that the
two displayed corridor faces share at most one interior edge.

This module makes that actual dependency explicit.  It supplies a canonical
rung for each consecutive corridor pair from pointwise cardinality bounds and
records agreement with the historical globally-indexed rung whenever the
stronger hypothesis happens to be available.  The latter theorem lets the
existing source tower migrate without changing any computed edge.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCorridorPointwiseRungs

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InteriorDualPointwiseLookup
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Exactly the uniqueness consumed by corridor rung lookup: each consecutive
pair of corridor faces shares at most one interior edge.  Nothing is asserted
about the hole faces or about nonconsecutive ambient faces. -/
def ConsecutiveRungUnique {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength) : Prop :=
  ∀ step : CorridorStep corridorLength,
    (sharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (corridor.faceAt step.left).1
      (corridor.faceAt step.right).1).card ≤ 1

/-- The historical global hypothesis implies the local corridor receipt. -/
theorem consecutiveRungUnique_of_pairwiseUnique
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))) :
    ConsecutiveRungUnique corridor := by
  intro step
  exact card_le_one_of_pairwiseUnique
    (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS)) hunique
      (corridor.consecutive_adjacent step.left step.right rfl)

/-- The primal edge at one corridor step, selected from the pointwise receipt
rather than a false global invariant. -/
noncomputable def pointwiseRungEdge
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hlocal : ConsecutiveRungUnique corridor)
    (step : CorridorStep corridorLength) : E :=
  sharedInteriorEdgeOfAdj (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) (hlocal step)
      (corridor.consecutive_adjacent step.left step.right rfl)

theorem pointwiseRungEdge_mem_shared
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hlocal : ConsecutiveRungUnique corridor)
    (step : CorridorStep corridorLength) :
    pointwiseRungEdge corridor hlocal step ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))
        (corridor.faceAt step.left).1
        (corridor.faceAt step.right).1 :=
  sharedInteriorEdgeOfAdj_mem (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) (hlocal step)
      (corridor.consecutive_adjacent step.left step.right rfl)

theorem pointwiseRungEdge_mem_left
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hlocal : ConsecutiveRungUnique corridor)
    (step : CorridorStep corridorLength) :
    pointwiseRungEdge corridor hlocal step ∈
      orbitFaceBoundary RS (corridor.faceAt step.left).1 :=
  (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).1
      (pointwiseRungEdge_mem_shared corridor hlocal step) |>.2.1

theorem pointwiseRungEdge_mem_right
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hlocal : ConsecutiveRungUnique corridor)
    (step : CorridorStep corridorLength) :
    pointwiseRungEdge corridor hlocal step ∈
      orbitFaceBoundary RS (corridor.faceAt step.right).1 :=
  (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).1
      (pointwiseRungEdge_mem_shared corridor hlocal step) |>.2.2

/-- Any literal edge exhibited in the one shared set is the pointwise rung. -/
theorem pointwiseRungEdge_eq_of_mem
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hlocal : ConsecutiveRungUnique corridor)
    (step : CorridorStep corridorLength) {edge : E}
    (hedge : edge ∈ sharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (corridor.faceAt step.left).1
      (corridor.faceAt step.right).1) :
    pointwiseRungEdge corridor hlocal step = edge :=
  sharedInteriorEdgeOfAdj_eq_of_mem (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) (hlocal step)
      (corridor.consecutive_adjacent step.left step.right rfl) hedge

/-- Migration is extensionally exact: under the old global premise the new
pointwise lookup returns the old canonical rung. -/
theorem pointwiseRungEdge_eq_rungEdge
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : CorridorStep corridorLength) :
    pointwiseRungEdge corridor
        (consecutiveRungUnique_of_pairwiseUnique corridor hunique) step =
      corridor.rungEdge hunique step :=
  sharedInteriorEdgeOfAdj_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
    (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS)) hunique
      (corridor.consecutive_adjacent step.left step.right rfl)

/-- The two local rungs of one internal corridor face are different.  The
argument uses only the universal two-face incidence bound and the three
distinct corridor faces around the centre; no global intersection property is
involved. -/
theorem pointwiseRungEdge_incoming_ne_outgoing
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hlocal : ConsecutiveRungUnique corridor)
    (interior : CorridorInterior corridorLength) :
    pointwiseRungEdge corridor hlocal interior.incoming ≠
      pointwiseRungEdge corridor hlocal interior.outgoing := by
  intro hrungs
  have hpreviousCenter :
      (corridor.faceAt interior.incoming.left).1 ≠
        (corridor.faceAt interior.center).1 := by
    intro hfaces
    have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change interior.center.val - 1 = interior.center.val at hvalues
    have hpositive := interior.center_pos
    omega
  have hcenterNext :
      (corridor.faceAt interior.center).1 ≠
        (corridor.faceAt interior.outgoing.right).1 := by
    intro hfaces
    have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change interior.center.val = interior.center.val + 1 at hvalues
    omega
  have hpreviousNext :
      (corridor.faceAt interior.incoming.left).1 ≠
        (corridor.faceAt interior.outgoing.right).1 := by
    intro hfaces
    have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change interior.center.val - 1 = interior.center.val + 1 at hvalues
    have hpositive := interior.center_pos
    omega
  have hincomingPrevious :
      pointwiseRungEdge corridor hlocal interior.incoming ∈
        orbitFaceBoundary RS
          (corridor.faceAt interior.incoming.left).1 :=
    pointwiseRungEdge_mem_left corridor hlocal interior.incoming
  have hincomingCenter :
      pointwiseRungEdge corridor hlocal interior.incoming ∈
        orbitFaceBoundary RS (corridor.faceAt interior.center).1 := by
    simpa using pointwiseRungEdge_mem_right corridor hlocal interior.incoming
  have hnextOutgoing :
      pointwiseRungEdge corridor hlocal interior.incoming ∈
        orbitFaceBoundary RS
          (corridor.faceAt interior.outgoing.right).1 := by
    rw [hrungs]
    exact pointwiseRungEdge_mem_right corridor hlocal interior.outgoing
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS)
      (corridor.faceAt interior.center).2
      (corridor.faceAt interior.incoming.left).2
      (corridor.faceAt interior.outgoing.right).2
      hpreviousCenter.symm hincomingCenter hincomingPrevious hnextOutgoing
  rcases hcases with hcenterEqNext | hpreviousEqNext
  · exact hcenterNext hcenterEqNext.symm
  · exact hpreviousNext hpreviousEqNext.symm

/-- The local version of `InternalHexRungPlacement`.  Its data are identical,
but its two rung equations are indexed only by the consecutive-pair receipt. -/
structure PointwiseInternalHexRungPlacement
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hlocal : ConsecutiveRungUnique corridor)
    (interior : CorridorInterior corridorLength) where
  root : RS.D
  root_face : dartOrbitFace RS root = (corridor.faceAt interior.center).1
  orbit_card : (RS.faceOrbit root).card = 6
  incomingPosition : Fin (RS.faceOrbit root).card
  outgoingPosition : Fin (RS.faceOrbit root).card
  incoming_edge : faceCycleEdge RS root incomingPosition =
    pointwiseRungEdge corridor hlocal interior.incoming
  outgoing_edge : faceCycleEdge RS root outgoingPosition =
    pointwiseRungEdge corridor hlocal interior.outgoing
  positions_ne : incomingPosition ≠ outgoingPosition

/-- Every internal face of a two-sided hex corridor has a pointwise rung
placement.  Compared with the historical theorem, the only intersection
premise is `ConsecutiveRungUnique`. -/
theorem exists_pointwiseInternalHexRungPlacement
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : GoertzelV24OrbitFaceTwoSided.OrbitFacesTwoSided RS)
    (hlocal : ConsecutiveRungUnique corridor)
    (interior : CorridorInterior corridorLength) :
    Nonempty (PointwiseInternalHexRungPlacement corridor hlocal interior) := by
  rcases exists_dartOrbitFace_eq RS (corridor.faceAt interior.center).1 with
    ⟨root, hroot⟩
  have horbitCard : (RS.faceOrbit root).card = 6 := by
    calc
      (RS.faceOrbit root).card =
          (orbitFaceDarts RS (dartOrbitFace RS root)).card := by
        rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
      _ = (orbitFaceBoundary RS (dartOrbitFace RS root)).card := by
        exact (GoertzelV24OrbitFaceTwoSided.orbitFaceBoundarySimple_of_twoSided
          RS htwoSided (dartOrbitFace RS root)).symm
      _ = (orbitFaceBoundary RS
          (corridor.faceAt interior.center).1).card := by rw [hroot]
      _ = 6 := corridor.hexagonal interior.center
  have hincomingMem : pointwiseRungEdge corridor hlocal interior.incoming ∈
      orbitFaceBoundary RS (dartOrbitFace RS root) := by
    rw [hroot]
    simpa using pointwiseRungEdge_mem_right corridor hlocal interior.incoming
  have houtgoingMem : pointwiseRungEdge corridor hlocal interior.outgoing ∈
      orbitFaceBoundary RS (dartOrbitFace RS root) := by
    rw [hroot]
    exact pointwiseRungEdge_mem_left corridor hlocal interior.outgoing
  rcases existsUnique_faceCycleEdge_eq RS htwoSided root
      (pointwiseRungEdge corridor hlocal interior.incoming) hincomingMem with
    ⟨incomingPosition, hincomingEdge, _hincomingUnique⟩
  rcases existsUnique_faceCycleEdge_eq RS htwoSided root
      (pointwiseRungEdge corridor hlocal interior.outgoing) houtgoingMem with
    ⟨outgoingPosition, houtgoingEdge, _houtgoingUnique⟩
  have hpositionsNe : incomingPosition ≠ outgoingPosition := by
    intro hpositions
    apply pointwiseRungEdge_incoming_ne_outgoing corridor hlocal interior
    rw [← hincomingEdge, ← houtgoingEdge, hpositions]
  exact ⟨⟨root, hroot, horbitCard, incomingPosition, outgoingPosition,
    hincomingEdge, houtgoingEdge, hpositionsNe⟩⟩

/-- Canonical pointwise placement selected from the local receipt. -/
noncomputable def pointwiseInternalHexRungPlacement
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : GoertzelV24OrbitFaceTwoSided.OrbitFacesTwoSided RS)
    (hlocal : ConsecutiveRungUnique corridor)
    (interior : CorridorInterior corridorLength) :
    PointwiseInternalHexRungPlacement corridor hlocal interior :=
  Classical.choice
    (exists_pointwiseInternalHexRungPlacement corridor htwoSided hlocal interior)

namespace PointwiseInternalHexRungPlacement

def incomingPosition6
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior) :
    Fin 6 :=
  Fin.cast placement.orbit_card placement.incomingPosition

def outgoingPosition6
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior) :
    Fin 6 :=
  Fin.cast placement.orbit_card placement.outgoingPosition

theorem positions6_ne
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior) :
    placement.incomingPosition6 ≠ placement.outgoingPosition6 := by
  exact fun heq => placement.positions_ne
    (Fin.cast_injective placement.orbit_card heq)

/-- The four cyclic positions left after deleting the two pointwise rung
positions. -/
def sidePositions
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior) :
    Finset (Fin (RS.faceOrbit placement.root).card) :=
  Finset.univ \ {placement.incomingPosition, placement.outgoingPosition}

@[simp]
theorem mem_sidePositions_iff
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior)
    (position : Fin (RS.faceOrbit placement.root).card) :
    position ∈ placement.sidePositions ↔
      position ≠ placement.incomingPosition ∧
      position ≠ placement.outgoingPosition := by
  simp [sidePositions]

/-- Transport a standard six-cycle coordinate to the real facial orbit. -/
def positionOfSix
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior)
    (position : Fin 6) : Fin (RS.faceOrbit placement.root).card :=
  Fin.cast placement.orbit_card.symm position

@[simp]
theorem positionOfSix_val
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior)
    (position : Fin 6) :
    (placement.positionOfSix position).val = position.val :=
  rfl

@[simp]
theorem positionOfSix_incomingPosition6
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior) :
    placement.positionOfSix placement.incomingPosition6 =
      placement.incomingPosition := by
  apply Fin.ext
  rfl

@[simp]
theorem positionOfSix_outgoingPosition6
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior) :
    placement.positionOfSix placement.outgoingPosition6 =
      placement.outgoingPosition := by
  apply Fin.ext
  rfl

/-- Transport a standard non-rung coordinate to the four actual side slots. -/
def sidePositionOfSix
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior)
    (position : {position // position ∈ hexSidePositions
      placement.incomingPosition6 placement.outgoingPosition6}) :
    {position // position ∈ placement.sidePositions} :=
  ⟨placement.positionOfSix position.1, by
    apply (mem_sidePositions_iff placement _).2
    have hposition := position.2
    simp only [hexSidePositions, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hposition
    exact ⟨fun heq => hposition.1 (by
        apply Fin.ext
        simpa [positionOfSix, incomingPosition6] using congrArg Fin.val heq),
      fun heq => hposition.2 (by
        apply Fin.ext
        simpa [positionOfSix, outgoingPosition6] using congrArg Fin.val heq)⟩⟩

/-- Old placements embed without changing their root, positions, or literal
rung edges. -/
noncomputable def ofPairwiseUnique
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    PointwiseInternalHexRungPlacement corridor
      (consecutiveRungUnique_of_pairwiseUnique corridor hunique) interior where
  root := placement.root
  root_face := placement.root_face
  orbit_card := placement.orbit_card
  incomingPosition := placement.incomingPosition
  outgoingPosition := placement.outgoingPosition
  incoming_edge := placement.incoming_edge.trans
    (pointwiseRungEdge_eq_rungEdge corridor hunique interior.incoming).symm
  outgoing_edge := placement.outgoing_edge.trans
    (pointwiseRungEdge_eq_rungEdge corridor hunique interior.outgoing).symm
  positions_ne := placement.positions_ne

/-- The finite rung type is unchanged by the interface weakening. -/
def rungType
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior) :
    HexRungType :=
  hexRungType placement.incomingPosition6 placement.outgoingPosition6

theorem rungType_distance_eq
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hlocal : ConsecutiveRungUnique corridor}
    {interior : CorridorInterior corridorLength}
    (placement : PointwiseInternalHexRungPlacement corridor hlocal interior) :
    placement.rungType.distance =
      hexCyclicDistance placement.incomingPosition6
        placement.outgoingPosition6 :=
  hexRungType_distance_eq _ _ placement.positions6_ne

end PointwiseInternalHexRungPlacement

end

end GoertzelV24HexCorridorPointwiseRungs

end Mettapedia.GraphTheory.FourColor
