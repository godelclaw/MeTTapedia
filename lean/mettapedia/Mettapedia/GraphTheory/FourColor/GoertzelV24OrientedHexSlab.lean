import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorSlab

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrientedHexSlab

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The four cyclic positions left after deleting the incoming and outgoing
rungs from an internal hexagonal face. -/
def placementSidePositions {RS : RotationSystem V E}
    {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    Finset (Fin (RS.faceOrbit placement.root).card) :=
  Finset.univ \ {placement.incomingPosition, placement.outgoingPosition}

@[simp]
theorem mem_placementSidePositions_iff
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : Fin (RS.faceOrbit placement.root).card) :
    position ∈ placementSidePositions placement ↔
      position ≠ placement.incomingPosition ∧
      position ≠ placement.outgoingPosition := by
  simp [placementSidePositions]

/-- The cyclic side-position set has cardinality four. -/
theorem card_placementSidePositions_eq_four
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    (placementSidePositions placement).card = 4 := by
  have hsubset :
      ({placement.incomingPosition, placement.outgoingPosition} :
        Finset (Fin (RS.faceOrbit placement.root).card)) ⊆ Finset.univ := by
    simp
  rw [placementSidePositions,
    Finset.card_sdiff_of_subset hsubset]
  simp [placement.positions_ne, placement.orbit_card]

/-- The cyclic four-slot interface and the edge-set interface are exactly the
same data. This prevents the ordered slab representation from introducing
synthetic interface edges. -/
theorem image_faceCycleEdge_placementSidePositions
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    (htwoSided : OrbitFacesTwoSided RS)
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    (placementSidePositions placement).image (faceCycleEdge RS placement.root) =
      internalSideEdges corridor hunique interior := by
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_image.1 hedge with ⟨position, hposition, hpositionEdge⟩
    have hpositionNe := (mem_placementSidePositions_iff placement position).1 hposition
    apply (mem_internalSideEdges_iff corridor hunique interior edge).2
    refine ⟨?_, ?_, ?_⟩
    · rw [← hpositionEdge, ← placement.root_face]
      exact faceCycleEdge_mem RS placement.root position
    · intro hedgeIncoming
      apply hpositionNe.1
      apply faceCycleEdge_injective RS htwoSided placement.root
      calc
        faceCycleEdge RS placement.root position = edge := hpositionEdge
        _ = corridor.rungEdge hunique interior.incoming := hedgeIncoming
        _ = faceCycleEdge RS placement.root placement.incomingPosition :=
          placement.incoming_edge.symm
    · intro hedgeOutgoing
      apply hpositionNe.2
      apply faceCycleEdge_injective RS htwoSided placement.root
      calc
        faceCycleEdge RS placement.root position = edge := hpositionEdge
        _ = corridor.rungEdge hunique interior.outgoing := hedgeOutgoing
        _ = faceCycleEdge RS placement.root placement.outgoingPosition :=
          placement.outgoing_edge.symm
  · intro hedge
    have hside := (mem_internalSideEdges_iff corridor hunique interior edge).1 hedge
    have hedgeRoot : edge ∈ orbitFaceBoundary RS
        (dartOrbitFace RS placement.root) := by
      rw [placement.root_face]
      exact hside.1
    rcases existsUnique_faceCycleEdge_eq RS htwoSided placement.root edge
      hedgeRoot with ⟨position, hpositionEdge, _hpositionUnique⟩
    apply Finset.mem_image.2
    refine ⟨position, (mem_placementSidePositions_iff placement position).2 ⟨?_, ?_⟩,
      hpositionEdge⟩
    · intro hposition
      apply hside.2.1
      rw [← hpositionEdge, hposition, placement.incoming_edge]
    · intro hposition
      apply hside.2.2
      rw [← hpositionEdge, hposition, placement.outgoing_edge]

/-- A cyclic side position regarded as the corresponding member of the
width-four edge interface. -/
def placementSideEdge
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    (htwoSided : OrbitFacesTwoSided RS)
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    {edge // edge ∈ internalSideEdges corridor hunique interior} :=
  ⟨faceCycleEdge RS placement.root position.1, by
    rw [← image_faceCycleEdge_placementSidePositions htwoSided placement]
    exact Finset.mem_image.2 ⟨position.1, position.2, rfl⟩⟩

theorem placementSideEdge_injective
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    (htwoSided : OrbitFacesTwoSided RS)
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    Function.Injective (placementSideEdge htwoSided placement) := by
  intro left right hedge
  apply Subtype.ext
  exact faceCycleEdge_injective RS htwoSided placement.root
    (congrArg Subtype.val hedge)

/-- The external hexagonal face attached to one cyclic side slot. -/
noncomputable def placementSideNeighbor
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    AmbientFace (Finset.univ : Finset (OrbitFace RS)) :=
  internalSideNeighbor clean htwoSided hunique interior
    (placementSideEdge htwoSided placement position)

/-- The four cyclic side slots reach four distinct external faces. -/
theorem placementSideNeighbor_injective
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique interior) :
    Function.Injective
      (placementSideNeighbor clean htwoSided hunique placement) := by
  intro left right hfaces
  apply placementSideEdge_injective htwoSided placement
  apply internalSideNeighbor_injective clean htwoSided hunique interior
  exact hfaces

theorem placementSideNeighbor_hexagonal
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    (orbitFaceBoundary RS
      (placementSideNeighbor clean htwoSided hunique placement position).1).card = 6 :=
  internalSideNeighbor_hexagonal clean htwoSided hunique interior
    (placementSideEdge htwoSided placement position)

theorem placementSideNeighbor_ne_faceAt
    {RS : RotationSystem V E} {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement
      clean.toOrbitHexCorridorSkeleton hunique interior)
    (position : {position // position ∈ placementSidePositions placement})
    (index : Fin corridorLength) :
    placementSideNeighbor clean htwoSided hunique placement position ≠
      clean.toOrbitHexCorridorSkeleton.faceAt index :=
  internalSideNeighbor_ne_faceAt clean htwoSided hunique interior
    (placementSideEdge htwoSided placement position) index

/-- The ordered side-slot type itself has cardinality four. -/
theorem card_placementSideSlot_eq_four
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    Fintype.card {position // position ∈ placementSidePositions placement} = 4 := by
  change Fintype.card ↥(placementSidePositions placement) = 4
  rw [Fintype.card_coe, card_placementSidePositions_eq_four placement]

/-- Oriented local types retained by an induced hex corridor. The names are
the exact forward distances in the chosen face-permutation orientation. -/
inductive OrientedInducedHexSlabType where
  | forwardTwo
  | forwardThree
  | forwardFour
  deriving DecidableEq, Fintype

def OrientedInducedHexSlabType.forwardDistance :
    OrientedInducedHexSlabType → Nat
  | .forwardTwo => 2
  | .forwardThree => 3
  | .forwardFour => 4

@[simp]
theorem card_orientedInducedHexSlabType :
    Fintype.card OrientedInducedHexSlabType = 3 := by
  decide

/-- Removing the adjacent-rung case leaves exactly the directed distances
two, three, and four. -/
theorem hexForwardDistance_eq_two_or_three_or_four
    (incoming outgoing : Fin 6) (hne : incoming ≠ outgoing)
    (hnonadjacent : hexRungType incoming outgoing ≠ HexRungType.adjacent) :
    hexForwardDistance incoming outgoing = 2 ∨
      hexForwardDistance incoming outgoing = 3 ∨
      hexForwardDistance incoming outgoing = 4 := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexRungType, hexCyclicDistance, hexForwardDistance] at *

/-- Every induced oriented rung placement has a unique three-symbol slab
type matching its actual directed cyclic separation. -/
theorem existsUnique_orientedInducedHexSlabType
    (incoming outgoing : Fin 6) (hne : incoming ≠ outgoing)
    (hnonadjacent : hexRungType incoming outgoing ≠ HexRungType.adjacent) :
    ∃! slabType : OrientedInducedHexSlabType,
      slabType.forwardDistance = hexForwardDistance incoming outgoing := by
  rcases hexForwardDistance_eq_two_or_three_or_four incoming outgoing hne
    hnonadjacent with htwo | hthree | hfour
  · refine ⟨.forwardTwo, by
      simpa [OrientedInducedHexSlabType.forwardDistance] using htwo.symm, ?_⟩
    intro other hother
    cases other <;> simp [OrientedInducedHexSlabType.forwardDistance, htwo] at hother ⊢
  · refine ⟨.forwardThree, by
      simpa [OrientedInducedHexSlabType.forwardDistance] using hthree.symm, ?_⟩
    intro other hother
    cases other <;> simp [OrientedInducedHexSlabType.forwardDistance, hthree] at hother ⊢
  · refine ⟨.forwardFour, by
      simpa [OrientedInducedHexSlabType.forwardDistance] using hfour.symm, ?_⟩
    intro other hother
    cases other <;> simp [OrientedInducedHexSlabType.forwardDistance, hfour] at hother ⊢

/-- The oriented slab type selected from a proved non-adjacent placement. -/
noncomputable def orientedSlabTypeOfPlacement
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (hnonadjacent : placement.rungType ≠ HexRungType.adjacent) :
    OrientedInducedHexSlabType :=
  Classical.choose (existsUnique_orientedInducedHexSlabType
    placement.incomingPosition6 placement.outgoingPosition6
      placement.positions6_ne hnonadjacent)

theorem orientedSlabTypeOfPlacement_forwardDistance
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (hnonadjacent : placement.rungType ≠ HexRungType.adjacent) :
    (orientedSlabTypeOfPlacement placement hnonadjacent).forwardDistance =
      hexForwardDistance placement.incomingPosition6
        placement.outgoingPosition6 :=
  (Classical.choose_spec (existsUnique_orientedInducedHexSlabType
    placement.incomingPosition6 placement.outgoingPosition6
      placement.positions6_ne hnonadjacent)).1

/-- The actual oriented slab word of an induced cubic hex corridor. Unlike
the unoriented rung word, this retains the distinction between the two turn
directions needed by slab composition. -/
noncomputable def orientedHexSlabTypeWord {RS : RotationSystem V E}
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))) :
    Fin (corridorLength - 2) → OrientedInducedHexSlabType :=
  fun offset =>
    let placement := internalHexRungPlacement corridor htwoSided hunique offset
    orientedSlabTypeOfPlacement placement
      (GoertzelV24InducedHexCorridorTypes.InternalHexRungPlacement.rungType_ne_adjacent
        placement hcubic hrotation htwoSided)

/-- There are exactly `3^(L-2)` possible oriented local slab words before
compatibility between consecutive slabs is imposed. -/
theorem card_orientedHexSlabTypeWords (corridorLength : Nat) :
    Fintype.card (Fin (corridorLength - 2) → OrientedInducedHexSlabType) =
      3 ^ (corridorLength - 2) := by
  simp

end

end GoertzelV24OrientedHexSlab

end Mettapedia.GraphTheory.FourColor
