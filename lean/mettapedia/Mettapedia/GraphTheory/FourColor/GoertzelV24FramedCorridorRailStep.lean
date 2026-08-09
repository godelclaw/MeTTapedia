import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorCanonicalInterface
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLayerFormation

/-!
# One genuine rail-composition step in a source corridor

When the shared hexagon between two canonical source tiles has opposite
incoming and outgoing rungs, its four certified corner ports form two real
facial-dual rail steps.  This is the constructive middle case of the corridor
assembly: it derives the two rail adjacencies from the actual source positions
and their rotation-system corner equations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

private theorem left_rail_successor_of_opposite_rungs
    {incoming outgoing prior next : Nat}
    (hopposite : outgoing ≡ incoming + 3 [MOD 6])
    (hpriorPos : prior ≡ incoming + 1 [MOD 6])
    (hnextPos : outgoing ≡ next + 1 [MOD 6]) :
    next ≡ prior + 1 [MOD 6] := by
  rw [Nat.ModEq] at *
  omega

private theorem right_rail_successor_of_opposite_rungs
    {incoming outgoing prior next : Nat}
    (hopposite : outgoing ≡ incoming + 3 [MOD 6])
    (hpriorPos : incoming ≡ prior + 1 [MOD 6])
    (hnextPos : next ≡ outgoing + 1 [MOD 6]) :
    prior ≡ next + 1 [MOD 6] := by
  rw [Nat.ModEq] at *
  omega

/-- The finite `forwardThree` case is exactly the opposite-rung geometry
needed for a pair of straight exterior rail steps. -/
private theorem outgoing_modEq_of_hexForwardDistance_three
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 3) :
    outgoing.val ≡ incoming.val + 3 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexForwardDistance, Nat.ModEq] at *

/-- The other two source-word symbols are genuine bent-rung cases.  Keep
their cyclic coordinates explicit so neither case can be silently folded into
the straight `forwardThree` rail construction. -/
private theorem outgoing_modEq_of_hexForwardDistance_two
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 2) :
    outgoing.val ≡ incoming.val + 2 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexForwardDistance, Nat.ModEq] at *

private theorem outgoing_modEq_of_hexForwardDistance_four
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 4) :
    outgoing.val ≡ incoming.val + 4 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexForwardDistance, Nat.ModEq] at *

/-- In the `forwardTwo` case, the side slot four steps after the incoming
rung survives.  It is the bend between the two local source layers. -/
private theorem exists_forwardTwo_middleSidePosition
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 2) :
    ∃ middle : {position // position ∈ hexSidePositions incoming outgoing},
      middle.1.val ≡ incoming.val + 4 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexSidePositions, hexForwardDistance, Nat.ModEq] at * <;>
    decide

/-- In the `forwardFour` case, the side slot two steps after the incoming
rung survives.  It is the mirror-image bend of `forwardTwo`. -/
private theorem exists_forwardFour_middleSidePosition
    (incoming outgoing : Fin 6)
    (hdistance : hexForwardDistance incoming outgoing = 4) :
    ∃ middle : {position // position ∈ hexSidePositions incoming outgoing},
      middle.1.val ≡ incoming.val + 2 [MOD 6] := by
  fin_cases incoming <;> fin_cases outgoing <;>
    norm_num [hexSidePositions, hexForwardDistance, Nat.ModEq] at * <;>
    decide

/-- The four exterior slots used by a `forwardTwo` bend are all distinct.
The order is: shared first endpoint, first second endpoint, middle bend,
second second endpoint. -/
private theorem forwardTwo_cornerPositions_pairwise_ne
    {incoming outgoing firstBefore firstAfter middle secondAfter : Nat}
    (hforward : outgoing ≡ incoming + 2 [MOD 6])
    (hfirstBefore : firstBefore ≡ incoming + 1 [MOD 6])
    (hfirstAfter : incoming ≡ firstAfter + 1 [MOD 6])
    (hmiddle : middle ≡ incoming + 4 [MOD 6])
    (hsecondAfter : secondAfter ≡ outgoing + 1 [MOD 6]) :
    firstBefore ≠ firstAfter ∧ firstBefore ≠ middle ∧
      firstBefore ≠ secondAfter ∧ firstAfter ≠ middle ∧
      firstAfter ≠ secondAfter ∧ middle ≠ secondAfter := by
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  · intro heq
    rw [Nat.ModEq] at *
    omega

/-- The four exterior slots used by the mirrored `forwardFour` bend are
also all distinct. -/
private theorem forwardFour_cornerPositions_pairwise_ne
    {incoming outgoing firstBefore firstAfter middle secondBefore : Nat}
    (hforward : outgoing ≡ incoming + 4 [MOD 6])
    (hfirstBefore : firstBefore ≡ incoming + 1 [MOD 6])
    (hfirstAfter : incoming ≡ firstAfter + 1 [MOD 6])
    (hmiddle : middle ≡ incoming + 2 [MOD 6])
    (hsecondBefore : outgoing ≡ secondBefore + 1 [MOD 6]) :
    firstBefore ≠ firstAfter ∧ firstBefore ≠ middle ∧
      firstBefore ≠ secondBefore ∧ firstAfter ≠ middle ∧
      firstAfter ≠ secondBefore ∧ middle ≠ secondBefore := by
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  · intro heq
    rw [Nat.ModEq] at *
    omega

/-- Around an opposite-rung hexagon, the four corner ports used by two
successive source tiles occupy four different side positions. -/
private theorem oppositeRung_cornerPositions_pairwise_ne
    {incoming outgoing firstBefore firstAfter secondBefore secondAfter : Nat}
    (hopposite : outgoing ≡ incoming + 3 [MOD 6])
    (hfirstBefore : firstBefore ≡ incoming + 1 [MOD 6])
    (hfirstAfter : incoming ≡ firstAfter + 1 [MOD 6])
    (hsecondBefore : outgoing ≡ secondBefore + 1 [MOD 6])
    (hsecondAfter : secondAfter ≡ outgoing + 1 [MOD 6]) :
    firstBefore ≠ firstAfter ∧ firstBefore ≠ secondBefore ∧
      firstBefore ≠ secondAfter ∧ firstAfter ≠ secondBefore ∧
      firstAfter ≠ secondAfter ∧ secondBefore ≠ secondAfter := by
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  constructor
  · intro heq
    rw [Nat.ModEq] at *
    omega
  · intro heq
    rw [Nat.ModEq] at *
    omega

/-- The two canonical local interfaces on either side of an opposite-rung
hexagon have two actual adjacent pairs of exterior faces.  These are the
one-step continuations of the two source rails. -/
theorem sourceCornerAlignedRailStep_of_oppositeRungs
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hopposite :
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition.val ≡
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)).incomingPosition.val + 3 [MOD 6]) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        first.toInterface.firstLayerFace second.toInterface.firstLayerFace ∧
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        first.toInterface.secondLayerFace second.toInterface.secondLayerFace := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hleftStep : second.toInterface.leftBeforePos.1.val ≡
      first.toInterface.rightBeforePos.1.val + 1 [MOD 6] := by
    apply left_rail_successor_of_opposite_rungs
    · simpa [sharedPlacement] using hopposite
    · simpa [sharedPlacement] using first.rightBefore_followsIncoming
    · simpa [sharedPlacement] using second.leftBefore_precedesOutgoing
  have hrightStep : first.toInterface.rightAfterPos.1.val ≡
      second.toInterface.leftAfterPos.1.val + 1 [MOD 6] := by
    apply right_rail_successor_of_opposite_rungs
    · simpa [sharedPlacement] using hopposite
    · simpa [sharedPlacement] using first.rightAfter_precedesIncoming
    · simpa [sharedPlacement] using second.leftAfter_followsOutgoing
  have hleftRail := placementSideNeighbors_adjacent_of_forwardStep
    realization.toCleanOrbitHexCorridorSkeleton hcubic hrotation htwoSided hunique
      sharedPlacement first.toInterface.rightBeforePos second.toInterface.leftBeforePos
      hleftStep
  have hrightRail := placementSideNeighbors_adjacent_of_forwardStep
    realization.toCleanOrbitHexCorridorSkeleton hcubic hrotation htwoSided hunique
      sharedPlacement second.toInterface.leftAfterPos first.toInterface.rightAfterPos
      hrightStep
  constructor
  · rw [first.toInterface.firstLayerFace_eq_next_firstLayerFace]
    simpa [SourceConsecutiveSlabInterface.firstLayerFace, sharedPlacement] using hleftRail
  · rw [first.toInterface.secondLayerFace_eq_next_secondLayerFace]
    simpa [SourceConsecutiveSlabInterface.secondLayerFace, sharedPlacement] using hrightRail.symm

/-- Concrete rail data for the `forwardTwo` case.  The middle position is
retained, not existentially erased, because subsequent layer-boundary proofs
must know that its face is an actual side neighbor of the shared hexagon. -/
structure SourceCornerAlignedForwardTwoRailWitness
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext) where
  sharedFirst : first.toInterface.firstLayerFace = second.toInterface.firstLayerFace
  middlePosition : {position // position ∈ placementSidePositions
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior leftInterior hnext))}
  middlePosition_coordinate : middlePosition.1.val ≡
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior leftInterior hnext)).incomingPosition.val + 4 [MOD 6]
  secondToMiddle :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      second.toInterface.secondLayerFace
      (placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) middlePosition)
  middleToFirst :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      (placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) middlePosition)
      first.toInterface.secondLayerFace

/-- Concrete rail data for the `forwardFour` mirror case. -/
structure SourceCornerAlignedForwardFourRailWitness
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext) where
  sharedSecond : first.toInterface.secondLayerFace = second.toInterface.secondLayerFace
  middlePosition : {position // position ∈ placementSidePositions
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior leftInterior hnext))}
  middlePosition_coordinate : middlePosition.1.val ≡
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior leftInterior hnext)).incomingPosition.val + 2 [MOD 6]
  firstToMiddle :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      first.toInterface.firstLayerFace
      (placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) middlePosition)
  middleToSecond :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      (placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)) middlePosition)
      second.toInterface.firstLayerFace

/-- The retained middle side slot of a `forwardTwo` witness as its actual
external facial-dual vertex. -/
noncomputable def SourceCornerAlignedForwardTwoRailWitness.middleFace
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext}
    (rail : SourceCornerAlignedForwardTwoRailWitness first second) :
    AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) :=
  placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
    hunique
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior leftInterior hnext)) rail.middlePosition

/-- The retained middle side slot of a `forwardFour` witness as its actual
external facial-dual vertex. -/
noncomputable def SourceCornerAlignedForwardFourRailWitness.middleFace
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext}
    {second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext}
    (rail : SourceCornerAlignedForwardFourRailWitness first second) :
    AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) :=
  placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
    hunique
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior leftInterior hnext)) rail.middlePosition

/-- A `forwardTwo` source tile has one shared rail endpoint and one bent
two-edge rail through a third exterior hexagon.  This is constructed from the
actual four retained side slots of the shared corridor face; it is not a
surrogate chord wall. -/
theorem sourceCornerAlignedBentRailStep_of_forwardTwo
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hdistance : hexForwardDistance
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).incomingPosition6
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition6 = 2) :
    Nonempty (SourceCornerAlignedForwardTwoRailWitness first second) := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hforward6 : sharedPlacement.outgoingPosition6.val ≡
      sharedPlacement.incomingPosition6.val + 2 [MOD 6] :=
    outgoing_modEq_of_hexForwardDistance_two _ _ (by simpa [sharedPlacement] using hdistance)
  have hforward : sharedPlacement.outgoingPosition.val ≡
      sharedPlacement.incomingPosition.val + 2 [MOD 6] := by
    simpa [InternalHexRungPlacement.incomingPosition6,
      InternalHexRungPlacement.outgoingPosition6] using hforward6
  let middle6 := Classical.choose (exists_forwardTwo_middleSidePosition
    sharedPlacement.incomingPosition6 sharedPlacement.outgoingPosition6
      (by simpa [sharedPlacement] using hdistance))
  have hmiddle6 : middle6.1.val ≡ sharedPlacement.incomingPosition6.val + 4 [MOD 6] :=
    Classical.choose_spec (exists_forwardTwo_middleSidePosition
      sharedPlacement.incomingPosition6 sharedPlacement.outgoingPosition6
        (by simpa [sharedPlacement] using hdistance))
  let middlePos := placementSidePositionOfSix sharedPlacement middle6
  have hmiddle : middlePos.1.val ≡ sharedPlacement.incomingPosition.val + 4 [MOD 6] := by
    simpa [middlePos, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.incomingPosition6] using hmiddle6
  have hfirstBefore : first.toInterface.rightBeforePos.1.val ≡
      sharedPlacement.incomingPosition.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using first.rightBefore_followsIncoming
  have hfirstAfter : sharedPlacement.incomingPosition.val ≡
      first.toInterface.rightAfterPos.1.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using first.rightAfter_precedesIncoming
  have hsecondBefore : sharedPlacement.outgoingPosition.val ≡
      second.toInterface.leftBeforePos.1.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using second.leftBefore_precedesOutgoing
  have hsecondAfter : second.toInterface.leftAfterPos.1.val ≡
      sharedPlacement.outgoingPosition.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using second.leftAfter_followsOutgoing
  have hfirstBeforeEqSecondBeforeMod : first.toInterface.rightBeforePos.1.val ≡
      second.toInterface.leftBeforePos.1.val [MOD 6] := by
    rw [Nat.ModEq] at hfirstBefore hsecondBefore hforward ⊢
    omega
  have hfirstBeforeEqSecondBefore : first.toInterface.rightBeforePos =
      second.toInterface.leftBeforePos := by
    apply Subtype.ext
    apply Fin.ext
    rw [Nat.ModEq] at hfirstBeforeEqSecondBeforeMod
    have hfirstBound : first.toInterface.rightBeforePos.1.val < 6 := by
      have hbound := first.toInterface.rightBeforePos.1.isLt
      change first.toInterface.rightBeforePos.1.val <
        (embedded.cellulation.rotation.toRotationSystem.faceOrbit
          sharedPlacement.root).card at hbound
      simpa only [sharedPlacement.orbit_card] using hbound
    have hsecondBound : second.toInterface.leftBeforePos.1.val < 6 := by
      have hbound := second.toInterface.leftBeforePos.1.isLt
      change second.toInterface.leftBeforePos.1.val <
        (embedded.cellulation.rotation.toRotationSystem.faceOrbit
          sharedPlacement.root).card at hbound
      simpa only [sharedPlacement.orbit_card] using hbound
    simpa [Nat.mod_eq_of_lt hfirstBound, Nat.mod_eq_of_lt hsecondBound] using
      hfirstBeforeEqSecondBeforeMod
  have hsecondAfterToMiddle : middlePos.1.val ≡
      second.toInterface.leftAfterPos.1.val + 1 [MOD 6] := by
    rw [Nat.ModEq] at hsecondAfter hforward hmiddle ⊢
    omega
  have hmiddleToFirstAfter : first.toInterface.rightAfterPos.1.val ≡
      middlePos.1.val + 1 [MOD 6] := by
    rw [Nat.ModEq] at hfirstAfter hmiddle ⊢
    omega
  have hfirstBeforeFace : first.toInterface.firstLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement first.toInterface.rightBeforePos := by
    simpa [sharedPlacement] using first.toInterface.firstLayerFace_eq_next_firstLayerFace
  have hfirstAfterFace : first.toInterface.secondLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement first.toInterface.rightAfterPos := by
    simpa [sharedPlacement] using first.toInterface.secondLayerFace_eq_next_secondLayerFace
  have hsecondBeforeFace : second.toInterface.firstLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement second.toInterface.leftBeforePos := by
    rfl
  have hsecondAfterFace : second.toInterface.secondLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement second.toInterface.leftAfterPos := by
    rfl
  have hsharedFirst : first.toInterface.firstLayerFace = second.toInterface.firstLayerFace := by
    calc
      first.toInterface.firstLayerFace =
          placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
            hunique sharedPlacement first.toInterface.rightBeforePos := hfirstBeforeFace
      _ = placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
            hunique sharedPlacement second.toInterface.leftBeforePos := by
          rw [hfirstBeforeEqSecondBefore]
      _ = second.toInterface.firstLayerFace := hsecondBeforeFace.symm
  have hsecondToMiddleRaw := placementSideNeighbors_adjacent_of_forwardStep
    realization.toCleanOrbitHexCorridorSkeleton hcubic hrotation htwoSided hunique
      sharedPlacement second.toInterface.leftAfterPos middlePos hsecondAfterToMiddle
  have hmiddleToFirstRaw := placementSideNeighbors_adjacent_of_forwardStep
    realization.toCleanOrbitHexCorridorSkeleton hcubic hrotation htwoSided hunique
      sharedPlacement middlePos first.toInterface.rightAfterPos hmiddleToFirstAfter
  exact ⟨{
    sharedFirst := hsharedFirst
    middlePosition := middlePos
    middlePosition_coordinate := by simpa [sharedPlacement] using hmiddle
    secondToMiddle := by simpa [hsecondAfterFace] using hsecondToMiddleRaw
    middleToFirst := by simpa [hfirstAfterFace] using hmiddleToFirstRaw
  }⟩

/-- `forwardFour` is the mirror image of `forwardTwo`: the second rail
endpoint is shared, while the first one bends through a certified third
exterior face.  Keeping this construction separate makes the source word's
three cases exhaustive in the geometry, rather than merely in its encoding. -/
theorem sourceCornerAlignedBentRailStep_of_forwardFour
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hdistance : hexForwardDistance
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).incomingPosition6
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition6 = 4) :
    Nonempty (SourceCornerAlignedForwardFourRailWitness first second) := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hforward6 : sharedPlacement.outgoingPosition6.val ≡
      sharedPlacement.incomingPosition6.val + 4 [MOD 6] :=
    outgoing_modEq_of_hexForwardDistance_four _ _ (by simpa [sharedPlacement] using hdistance)
  have hforward : sharedPlacement.outgoingPosition.val ≡
      sharedPlacement.incomingPosition.val + 4 [MOD 6] := by
    simpa [InternalHexRungPlacement.incomingPosition6,
      InternalHexRungPlacement.outgoingPosition6] using hforward6
  let middle6 := Classical.choose (exists_forwardFour_middleSidePosition
    sharedPlacement.incomingPosition6 sharedPlacement.outgoingPosition6
      (by simpa [sharedPlacement] using hdistance))
  have hmiddle6 : middle6.1.val ≡ sharedPlacement.incomingPosition6.val + 2 [MOD 6] :=
    Classical.choose_spec (exists_forwardFour_middleSidePosition
      sharedPlacement.incomingPosition6 sharedPlacement.outgoingPosition6
        (by simpa [sharedPlacement] using hdistance))
  let middlePos := placementSidePositionOfSix sharedPlacement middle6
  have hmiddle : middlePos.1.val ≡ sharedPlacement.incomingPosition.val + 2 [MOD 6] := by
    simpa [middlePos, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.incomingPosition6] using hmiddle6
  have hfirstBefore : first.toInterface.rightBeforePos.1.val ≡
      sharedPlacement.incomingPosition.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using first.rightBefore_followsIncoming
  have hfirstAfter : sharedPlacement.incomingPosition.val ≡
      first.toInterface.rightAfterPos.1.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using first.rightAfter_precedesIncoming
  have hsecondBefore : sharedPlacement.outgoingPosition.val ≡
      second.toInterface.leftBeforePos.1.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using second.leftBefore_precedesOutgoing
  have hsecondAfter : second.toInterface.leftAfterPos.1.val ≡
      sharedPlacement.outgoingPosition.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using second.leftAfter_followsOutgoing
  have hfirstAfterEqSecondAfterMod : first.toInterface.rightAfterPos.1.val ≡
      second.toInterface.leftAfterPos.1.val [MOD 6] := by
    rw [Nat.ModEq] at hfirstAfter hsecondAfter hforward ⊢
    omega
  have hfirstAfterEqSecondAfter : first.toInterface.rightAfterPos =
      second.toInterface.leftAfterPos := by
    apply Subtype.ext
    apply Fin.ext
    rw [Nat.ModEq] at hfirstAfterEqSecondAfterMod
    have hfirstBound : first.toInterface.rightAfterPos.1.val < 6 := by
      have hbound := first.toInterface.rightAfterPos.1.isLt
      change first.toInterface.rightAfterPos.1.val <
        (embedded.cellulation.rotation.toRotationSystem.faceOrbit
          sharedPlacement.root).card at hbound
      simpa only [sharedPlacement.orbit_card] using hbound
    have hsecondBound : second.toInterface.leftAfterPos.1.val < 6 := by
      have hbound := second.toInterface.leftAfterPos.1.isLt
      change second.toInterface.leftAfterPos.1.val <
        (embedded.cellulation.rotation.toRotationSystem.faceOrbit
          sharedPlacement.root).card at hbound
      simpa only [sharedPlacement.orbit_card] using hbound
    simpa [Nat.mod_eq_of_lt hfirstBound, Nat.mod_eq_of_lt hsecondBound] using
      hfirstAfterEqSecondAfterMod
  have hfirstBeforeToMiddle : middlePos.1.val ≡
      first.toInterface.rightBeforePos.1.val + 1 [MOD 6] := by
    rw [Nat.ModEq] at hfirstBefore hmiddle ⊢
    omega
  have hmiddleToSecondBefore : second.toInterface.leftBeforePos.1.val ≡
      middlePos.1.val + 1 [MOD 6] := by
    rw [Nat.ModEq] at hsecondBefore hforward hmiddle ⊢
    omega
  have hfirstBeforeFace : first.toInterface.firstLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement first.toInterface.rightBeforePos := by
    simpa [sharedPlacement] using first.toInterface.firstLayerFace_eq_next_firstLayerFace
  have hfirstAfterFace : first.toInterface.secondLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement first.toInterface.rightAfterPos := by
    simpa [sharedPlacement] using first.toInterface.secondLayerFace_eq_next_secondLayerFace
  have hsecondBeforeFace : second.toInterface.firstLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement second.toInterface.leftBeforePos := by
    rfl
  have hsecondAfterFace : second.toInterface.secondLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement second.toInterface.leftAfterPos := by
    rfl
  have hsharedSecond : first.toInterface.secondLayerFace = second.toInterface.secondLayerFace := by
    calc
      first.toInterface.secondLayerFace =
          placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
            hunique sharedPlacement first.toInterface.rightAfterPos := hfirstAfterFace
      _ = placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
            hunique sharedPlacement second.toInterface.leftAfterPos := by
          rw [hfirstAfterEqSecondAfter]
      _ = second.toInterface.secondLayerFace := hsecondAfterFace.symm
  have hfirstToMiddleRaw := placementSideNeighbors_adjacent_of_forwardStep
    realization.toCleanOrbitHexCorridorSkeleton hcubic hrotation htwoSided hunique
      sharedPlacement first.toInterface.rightBeforePos middlePos hfirstBeforeToMiddle
  have hmiddleToSecondRaw := placementSideNeighbors_adjacent_of_forwardStep
    realization.toCleanOrbitHexCorridorSkeleton hcubic hrotation htwoSided hunique
      sharedPlacement middlePos second.toInterface.leftBeforePos hmiddleToSecondBefore
  exact ⟨{
    sharedSecond := hsharedSecond
    middlePosition := middlePos
    middlePosition_coordinate := by simpa [sharedPlacement] using hmiddle
    firstToMiddle := by simpa [hfirstBeforeFace] using hfirstToMiddleRaw
    middleToSecond := by simpa [hsecondBeforeFace] using hmiddleToSecondRaw
  }⟩

/-- The four exterior faces in a `forwardTwo` bend are distinct.  This is
the non-self-intersection calculation needed to close the two local layers
into a simple boundary cycle. -/
theorem sourceCornerAlignedExteriorFaces_pairwise_ne_of_forwardTwo
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (rail : SourceCornerAlignedForwardTwoRailWitness first second)
    (hdistance : hexForwardDistance
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).incomingPosition6
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition6 = 2) :
    first.toInterface.firstLayerFace ≠ first.toInterface.secondLayerFace ∧
      first.toInterface.firstLayerFace ≠ rail.middleFace ∧
      first.toInterface.firstLayerFace ≠ second.toInterface.secondLayerFace ∧
      first.toInterface.secondLayerFace ≠ rail.middleFace ∧
      first.toInterface.secondLayerFace ≠ second.toInterface.secondLayerFace ∧
      rail.middleFace ≠ second.toInterface.secondLayerFace := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hforward6 : sharedPlacement.outgoingPosition6.val ≡
      sharedPlacement.incomingPosition6.val + 2 [MOD 6] :=
    outgoing_modEq_of_hexForwardDistance_two _ _ (by simpa [sharedPlacement] using hdistance)
  have hforward : sharedPlacement.outgoingPosition.val ≡
      sharedPlacement.incomingPosition.val + 2 [MOD 6] := by
    simpa [InternalHexRungPlacement.incomingPosition6,
      InternalHexRungPlacement.outgoingPosition6] using hforward6
  have hfirstBefore : first.toInterface.rightBeforePos.1.val ≡
      sharedPlacement.incomingPosition.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using first.rightBefore_followsIncoming
  have hfirstAfter : sharedPlacement.incomingPosition.val ≡
      first.toInterface.rightAfterPos.1.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using first.rightAfter_precedesIncoming
  have hmiddle : rail.middlePosition.1.val ≡
      sharedPlacement.incomingPosition.val + 4 [MOD 6] := by
    simpa [sharedPlacement] using rail.middlePosition_coordinate
  have hsecondAfter : second.toInterface.leftAfterPos.1.val ≡
      sharedPlacement.outgoingPosition.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using second.leftAfter_followsOutgoing
  rcases forwardTwo_cornerPositions_pairwise_ne
      (incoming := sharedPlacement.incomingPosition.val)
      (outgoing := sharedPlacement.outgoingPosition.val)
      (firstBefore := first.toInterface.rightBeforePos.1.val)
      (firstAfter := first.toInterface.rightAfterPos.1.val)
      (middle := rail.middlePosition.1.val)
      (secondAfter := second.toInterface.leftAfterPos.1.val)
      hforward hfirstBefore hfirstAfter hmiddle hsecondAfter with
    ⟨hAB, hAM, hAD, hBM, hBD, hMD⟩
  have hfirstBeforeFace : first.toInterface.firstLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement first.toInterface.rightBeforePos := by
    simpa [sharedPlacement] using first.toInterface.firstLayerFace_eq_next_firstLayerFace
  have hfirstAfterFace : first.toInterface.secondLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement first.toInterface.rightAfterPos := by
    simpa [sharedPlacement] using first.toInterface.secondLayerFace_eq_next_secondLayerFace
  have hmiddleFace : rail.middleFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement rail.middlePosition := by
    rfl
  have hsecondAfterFace : second.toInterface.secondLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement second.toInterface.leftAfterPos := by
    rfl
  have face_ne_of_position_ne : ∀
      (left right : {position // position ∈ placementSidePositions sharedPlacement}),
      left ≠ right →
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
          hunique sharedPlacement left ≠
        placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
          hunique sharedPlacement right := by
    intro left right hpositions hfaces
    exact hpositions (placementSideNeighbor_injective
      realization.toCleanOrbitHexCorridorSkeleton htwoSided hunique sharedPlacement hfaces)
  have sidePosition_ne_of_value_ne : ∀
      (left right : {position // position ∈ placementSidePositions sharedPlacement}),
      left.1.val ≠ right.1.val → left ≠ right := by
    intro left right hvalues hpositions
    exact hvalues (congrArg (fun position => position.1.val) hpositions)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hfirstBeforeFace, hfirstAfterFace] using
      face_ne_of_position_ne first.toInterface.rightBeforePos
        first.toInterface.rightAfterPos
          (sidePosition_ne_of_value_ne _ _ hAB)
  · simpa [hfirstBeforeFace, hmiddleFace] using
      face_ne_of_position_ne first.toInterface.rightBeforePos rail.middlePosition
        (sidePosition_ne_of_value_ne _ _ hAM)
  · simpa [hfirstBeforeFace, hsecondAfterFace] using
      face_ne_of_position_ne first.toInterface.rightBeforePos
        second.toInterface.leftAfterPos
          (sidePosition_ne_of_value_ne _ _ hAD)
  · simpa [hfirstAfterFace, hmiddleFace] using
      face_ne_of_position_ne first.toInterface.rightAfterPos rail.middlePosition
        (sidePosition_ne_of_value_ne _ _ hBM)
  · simpa [hfirstAfterFace, hsecondAfterFace] using
      face_ne_of_position_ne first.toInterface.rightAfterPos
        second.toInterface.leftAfterPos
          (sidePosition_ne_of_value_ne _ _ hBD)
  · simpa [hmiddleFace, hsecondAfterFace] using
      face_ne_of_position_ne rail.middlePosition second.toInterface.leftAfterPos
        (sidePosition_ne_of_value_ne _ _ hMD)

/-- The actual `forwardTwo` bend closes the two local layers into a simple
six-edge facial-dual cycle.  The shared endpoint and the two-edge exterior
rail are both retained in the witness, so this is a genuine layer boundary
rather than a chord-cycle proxy. -/
theorem exists_sourceCornerAlignedTwoTileLayerBoundary_isCycle_of_forwardTwo
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hdistance : hexForwardDistance
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).incomingPosition6
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition6 = 2) :
    ∃ boundary : (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
        first.toInterface.firstLayerFace first.toInterface.firstLayerFace,
      boundary.IsCycle ∧ boundary.length = 6 := by
  rcases sourceCornerAlignedBentRailStep_of_forwardTwo hcubic hrotation
      first second hdistance with ⟨rail⟩
  rcases sourceCornerAlignedExteriorFaces_pairwise_ne_of_forwardTwo first second
      rail hdistance with ⟨hAB, hAM, hAD, hBM, hBD, hMD⟩
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hcenterIndex : leftInterior.center ≠
      (nextCorridorInterior leftInterior hnext).center := by
    intro h
    have hvalues := congrArg Fin.val h
    change leftInterior.center.val = leftInterior.center.val + 1 at hvalues
    omega
  have hXY : first.toInterface.centerLayerFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.centerLayerFace] using
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt_ne
        hcenterIndex
  have hAX : first.toInterface.firstLayerFace ≠ first.toInterface.centerLayerFace :=
    first.toInterface.firstLayerFace_ne_centerLayerFace
  have hBX : first.toInterface.secondLayerFace ≠ first.toInterface.centerLayerFace :=
    first.toInterface.secondLayerFace_ne_centerLayerFace
  have hDY : second.toInterface.secondLayerFace ≠ second.toInterface.centerLayerFace :=
    second.toInterface.secondLayerFace_ne_centerLayerFace
  have hAY : first.toInterface.firstLayerFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.firstLayerFace,
      SourceConsecutiveSlabInterface.centerLayerFace] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique (realization.slabPlacementAt htwoSided hunique leftInterior)
        first.toInterface.leftBeforePos
        (nextCorridorInterior leftInterior hnext).center
  have hBY : first.toInterface.secondLayerFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.secondLayerFace,
      SourceConsecutiveSlabInterface.centerLayerFace] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique (realization.slabPlacementAt htwoSided hunique leftInterior)
        first.toInterface.leftAfterPos
        (nextCorridorInterior leftInterior hnext).center
  have hMX : rail.middleFace ≠ first.toInterface.centerLayerFace := by
    simpa [SourceCornerAlignedForwardTwoRailWitness.middleFace,
      SourceConsecutiveSlabInterface.centerLayerFace, sharedPlacement] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique sharedPlacement rail.middlePosition leftInterior.center
  have hDX : second.toInterface.secondLayerFace ≠ first.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.secondLayerFace,
      SourceConsecutiveSlabInterface.centerLayerFace, sharedPlacement] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique sharedPlacement second.toInterface.leftAfterPos leftInterior.center
  have hMY : rail.middleFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceCornerAlignedForwardTwoRailWitness.middleFace,
      SourceConsecutiveSlabInterface.centerLayerFace, sharedPlacement] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique sharedPlacement rail.middlePosition
        (nextCorridorInterior leftInterior hnext).center
  let firstRail0 := first.toInterface.localLayer.walk.concat rail.middleToFirst.symm
  let firstRail := firstRail0.concat rail.secondToMiddle.symm
  let secondRail := second.toInterface.localLayer.walk.reverse.copy rfl rail.sharedFirst.symm
  have hfirstRail0 : firstRail0.IsPath := by
    apply SimpleGraph.Walk.IsPath.concat first.toInterface.localLayer.isPath
    simpa [SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      SourceCornerAlignedForwardTwoRailWitness.middleFace, sharedPlacement] using
      And.intro hAM.symm (And.intro hMX hBM.symm)
  have hfirstRail : firstRail.IsPath := by
    apply SimpleGraph.Walk.IsPath.concat hfirstRail0
    simpa [firstRail0, SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      SourceCornerAlignedForwardTwoRailWitness.middleFace, sharedPlacement] using
      And.intro hAD.symm (And.intro hDX (And.intro hBD.symm hMD.symm))
  have hsecondRail : secondRail.IsPath := by
    simpa [secondRail, SourceConsecutiveSlabInterface.localLayer] using
      second.toInterface.localLayer.isPath.reverse
  have hCX : second.toInterface.firstLayerFace ≠ first.toInterface.centerLayerFace := by
    intro h
    exact hAX (rail.sharedFirst.trans h)
  have hCB : second.toInterface.firstLayerFace ≠ first.toInterface.secondLayerFace := by
    intro h
    exact hAB (rail.sharedFirst.trans h)
  have hCM : second.toInterface.firstLayerFace ≠ rail.middleFace := by
    intro h
    exact hAM (rail.sharedFirst.trans h)
  have hCD : second.toInterface.firstLayerFace ≠ second.toInterface.secondLayerFace := by
    intro h
    exact hAD (rail.sharedFirst.trans h)
  have htails : firstRail.support.tail.Disjoint secondRail.support.tail := by
    simp [firstRail, firstRail0, secondRail,
      SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk]
    exact ⟨⟨hXY.symm, hBY.symm,
      (by simpa [SourceCornerAlignedForwardTwoRailWitness.middleFace,
        sharedPlacement] using hMY.symm), hDY.symm⟩,
      hCX, hCB,
      (by simpa [SourceCornerAlignedForwardTwoRailWitness.middleFace,
        sharedPlacement] using hCM), hCD⟩
  have hcycle : (firstRail.append secondRail).IsCycle :=
    SimpleGraph.Walk.IsPath.isCycle_append hfirstRail hsecondRail htails
      (Or.inl (by
        simp [firstRail, firstRail0, SourceConsecutiveSlabInterface.localLayer,
          SourceConsecutiveSlabInterface.localLayerWalk]))
  refine ⟨firstRail.append secondRail, hcycle, ?_⟩
  simp [firstRail, firstRail0, secondRail,
    SourceConsecutiveSlabInterface.localLayer,
    SourceConsecutiveSlabInterface.localLayerWalk]

/-- The four exterior faces in the mirror `forwardFour` bend are distinct. -/
theorem sourceCornerAlignedExteriorFaces_pairwise_ne_of_forwardFour
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (rail : SourceCornerAlignedForwardFourRailWitness first second)
    (hdistance : hexForwardDistance
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).incomingPosition6
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition6 = 4) :
    first.toInterface.firstLayerFace ≠ first.toInterface.secondLayerFace ∧
      first.toInterface.firstLayerFace ≠ rail.middleFace ∧
      first.toInterface.firstLayerFace ≠ second.toInterface.firstLayerFace ∧
      first.toInterface.secondLayerFace ≠ rail.middleFace ∧
      first.toInterface.secondLayerFace ≠ second.toInterface.firstLayerFace ∧
      rail.middleFace ≠ second.toInterface.firstLayerFace := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hforward6 : sharedPlacement.outgoingPosition6.val ≡
      sharedPlacement.incomingPosition6.val + 4 [MOD 6] :=
    outgoing_modEq_of_hexForwardDistance_four _ _ (by simpa [sharedPlacement] using hdistance)
  have hforward : sharedPlacement.outgoingPosition.val ≡
      sharedPlacement.incomingPosition.val + 4 [MOD 6] := by
    simpa [InternalHexRungPlacement.incomingPosition6,
      InternalHexRungPlacement.outgoingPosition6] using hforward6
  have hfirstBefore : first.toInterface.rightBeforePos.1.val ≡
      sharedPlacement.incomingPosition.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using first.rightBefore_followsIncoming
  have hfirstAfter : sharedPlacement.incomingPosition.val ≡
      first.toInterface.rightAfterPos.1.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using first.rightAfter_precedesIncoming
  have hmiddle : rail.middlePosition.1.val ≡
      sharedPlacement.incomingPosition.val + 2 [MOD 6] := by
    simpa [sharedPlacement] using rail.middlePosition_coordinate
  have hsecondBefore : sharedPlacement.outgoingPosition.val ≡
      second.toInterface.leftBeforePos.1.val + 1 [MOD 6] := by
    simpa [sharedPlacement] using second.leftBefore_precedesOutgoing
  rcases forwardFour_cornerPositions_pairwise_ne
      (incoming := sharedPlacement.incomingPosition.val)
      (outgoing := sharedPlacement.outgoingPosition.val)
      (firstBefore := first.toInterface.rightBeforePos.1.val)
      (firstAfter := first.toInterface.rightAfterPos.1.val)
      (middle := rail.middlePosition.1.val)
      (secondBefore := second.toInterface.leftBeforePos.1.val)
      hforward hfirstBefore hfirstAfter hmiddle hsecondBefore with
    ⟨hAB, hAM, hAC, hBM, hBC, hMC⟩
  have hfirstBeforeFace : first.toInterface.firstLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement first.toInterface.rightBeforePos := by
    simpa [sharedPlacement] using first.toInterface.firstLayerFace_eq_next_firstLayerFace
  have hfirstAfterFace : first.toInterface.secondLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement first.toInterface.rightAfterPos := by
    simpa [sharedPlacement] using first.toInterface.secondLayerFace_eq_next_secondLayerFace
  have hmiddleFace : rail.middleFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement rail.middlePosition := by
    rfl
  have hsecondBeforeFace : second.toInterface.firstLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement second.toInterface.leftBeforePos := by
    rfl
  have face_ne_of_position_ne : ∀
      (left right : {position // position ∈ placementSidePositions sharedPlacement}),
      left ≠ right →
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
          hunique sharedPlacement left ≠
        placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
          hunique sharedPlacement right := by
    intro left right hpositions hfaces
    exact hpositions (placementSideNeighbor_injective
      realization.toCleanOrbitHexCorridorSkeleton htwoSided hunique sharedPlacement hfaces)
  have sidePosition_ne_of_value_ne : ∀
      (left right : {position // position ∈ placementSidePositions sharedPlacement}),
      left.1.val ≠ right.1.val → left ≠ right := by
    intro left right hvalues hpositions
    exact hvalues (congrArg (fun position => position.1.val) hpositions)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hfirstBeforeFace, hfirstAfterFace] using
      face_ne_of_position_ne first.toInterface.rightBeforePos
        first.toInterface.rightAfterPos
          (sidePosition_ne_of_value_ne _ _ hAB)
  · simpa [hfirstBeforeFace, hmiddleFace] using
      face_ne_of_position_ne first.toInterface.rightBeforePos rail.middlePosition
        (sidePosition_ne_of_value_ne _ _ hAM)
  · simpa [hfirstBeforeFace, hsecondBeforeFace] using
      face_ne_of_position_ne first.toInterface.rightBeforePos
        second.toInterface.leftBeforePos
          (sidePosition_ne_of_value_ne _ _ hAC)
  · simpa [hfirstAfterFace, hmiddleFace] using
      face_ne_of_position_ne first.toInterface.rightAfterPos rail.middlePosition
        (sidePosition_ne_of_value_ne _ _ hBM)
  · simpa [hfirstAfterFace, hsecondBeforeFace] using
      face_ne_of_position_ne first.toInterface.rightAfterPos
        second.toInterface.leftBeforePos
          (sidePosition_ne_of_value_ne _ _ hBC)
  · simpa [hmiddleFace, hsecondBeforeFace] using
      face_ne_of_position_ne rail.middlePosition second.toInterface.leftBeforePos
        (sidePosition_ne_of_value_ne _ _ hMC)

/-- The mirror `forwardFour` bend also closes to a simple six-edge
facial-dual layer boundary. -/
theorem exists_sourceCornerAlignedTwoTileLayerBoundary_isCycle_of_forwardFour
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hdistance : hexForwardDistance
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).incomingPosition6
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition6 = 4) :
    ∃ boundary : (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
        first.toInterface.firstLayerFace first.toInterface.firstLayerFace,
      boundary.IsCycle ∧ boundary.length = 6 := by
  rcases sourceCornerAlignedBentRailStep_of_forwardFour hcubic hrotation
      first second hdistance with ⟨rail⟩
  rcases sourceCornerAlignedExteriorFaces_pairwise_ne_of_forwardFour first second
      rail hdistance with ⟨hAB, hAM, hAC, hBM, hBC, hMC⟩
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hcenterIndex : leftInterior.center ≠
      (nextCorridorInterior leftInterior hnext).center := by
    intro h
    have hvalues := congrArg Fin.val h
    change leftInterior.center.val = leftInterior.center.val + 1 at hvalues
    omega
  have hXY : first.toInterface.centerLayerFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.centerLayerFace] using
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt_ne
        hcenterIndex
  have hAX : first.toInterface.firstLayerFace ≠ first.toInterface.centerLayerFace :=
    first.toInterface.firstLayerFace_ne_centerLayerFace
  have hBX : first.toInterface.secondLayerFace ≠ first.toInterface.centerLayerFace :=
    first.toInterface.secondLayerFace_ne_centerLayerFace
  have hCY : second.toInterface.firstLayerFace ≠ second.toInterface.centerLayerFace :=
    second.toInterface.firstLayerFace_ne_centerLayerFace
  have hAY : first.toInterface.firstLayerFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.firstLayerFace,
      SourceConsecutiveSlabInterface.centerLayerFace] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique (realization.slabPlacementAt htwoSided hunique leftInterior)
        first.toInterface.leftBeforePos
        (nextCorridorInterior leftInterior hnext).center
  have hBY : first.toInterface.secondLayerFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.secondLayerFace,
      SourceConsecutiveSlabInterface.centerLayerFace] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique (realization.slabPlacementAt htwoSided hunique leftInterior)
        first.toInterface.leftAfterPos
        (nextCorridorInterior leftInterior hnext).center
  have hMX : rail.middleFace ≠ first.toInterface.centerLayerFace := by
    simpa [SourceCornerAlignedForwardFourRailWitness.middleFace,
      SourceConsecutiveSlabInterface.centerLayerFace, sharedPlacement] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique sharedPlacement rail.middlePosition leftInterior.center
  have hMY : rail.middleFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceCornerAlignedForwardFourRailWitness.middleFace,
      SourceConsecutiveSlabInterface.centerLayerFace, sharedPlacement] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique sharedPlacement rail.middlePosition
        (nextCorridorInterior leftInterior hnext).center
  have hCX : second.toInterface.firstLayerFace ≠ first.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.firstLayerFace,
      SourceConsecutiveSlabInterface.centerLayerFace, sharedPlacement] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique sharedPlacement second.toInterface.leftBeforePos leftInterior.center
  have hAD : first.toInterface.firstLayerFace ≠ second.toInterface.secondLayerFace := by
    intro h
    exact hAB (h.trans rail.sharedSecond.symm)
  have hDM : second.toInterface.secondLayerFace ≠ rail.middleFace := by
    intro h
    exact hBM (rail.sharedSecond.trans h)
  let firstRail := first.toInterface.localLayer.walk
  let secondRail0 := second.toInterface.localLayer.walk.reverse.copy rail.sharedSecond.symm rfl
  let secondRail1 := secondRail0.concat rail.middleToSecond.symm
  let secondRail := secondRail1.concat rail.firstToMiddle.symm
  have hfirstRail : firstRail.IsPath := by
    simpa [firstRail, SourceConsecutiveSlabInterface.localLayer] using
      first.toInterface.localLayer.isPath
  have hsecondRail0 : secondRail0.IsPath := by
    simpa [secondRail0, SourceConsecutiveSlabInterface.localLayer] using
      second.toInterface.localLayer.isPath.reverse
  have hsecondRail1 : secondRail1.IsPath := by
    apply SimpleGraph.Walk.IsPath.concat hsecondRail0
    simpa [secondRail0, SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      SourceCornerAlignedForwardFourRailWitness.middleFace, sharedPlacement] using
      And.intro hDM.symm (And.intro hMY hMC)
  have hsecondRail : secondRail.IsPath := by
    apply SimpleGraph.Walk.IsPath.concat hsecondRail1
    simpa [secondRail1, secondRail0,
      SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      SourceCornerAlignedForwardFourRailWitness.middleFace, sharedPlacement] using
      And.intro hAD (And.intro hAY (And.intro hAC hAM))
  have htails : firstRail.support.tail.Disjoint secondRail.support.tail := by
    simp [firstRail, secondRail, secondRail1, secondRail0,
      SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk]
    exact ⟨⟨hXY.symm, hBY.symm⟩,
      ⟨⟨hCX, hBC.symm⟩,
        ⟨⟨(by simpa [SourceCornerAlignedForwardFourRailWitness.middleFace,
          sharedPlacement] using hMX), hBM.symm⟩,
          ⟨hAX, hAB⟩⟩⟩⟩
  have hcycle : (firstRail.append secondRail).IsCycle :=
    SimpleGraph.Walk.IsPath.isCycle_append hfirstRail hsecondRail htails
      (Or.inl (by
        simp [firstRail, SourceConsecutiveSlabInterface.localLayer,
          SourceConsecutiveSlabInterface.localLayerWalk]))
  refine ⟨firstRail.append secondRail, hcycle, ?_⟩
  simp [firstRail, secondRail, secondRail1, secondRail0,
    SourceConsecutiveSlabInterface.localLayer,
    SourceConsecutiveSlabInterface.localLayerWalk]

/-- In the opposite-rung case, the two successive source tiles expose four
different exterior faces.  This is the local non-self-intersection fact needed
to close the two rail steps into a simple layer boundary. -/
theorem sourceCornerAlignedExteriorFaces_pairwise_ne_of_oppositeRungs
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hopposite :
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition.val ≡
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)).incomingPosition.val + 3 [MOD 6]) :
    first.toInterface.firstLayerFace ≠ first.toInterface.secondLayerFace ∧
      first.toInterface.firstLayerFace ≠ second.toInterface.firstLayerFace ∧
      first.toInterface.firstLayerFace ≠ second.toInterface.secondLayerFace ∧
      first.toInterface.secondLayerFace ≠ second.toInterface.firstLayerFace ∧
      first.toInterface.secondLayerFace ≠ second.toInterface.secondLayerFace ∧
      second.toInterface.firstLayerFace ≠ second.toInterface.secondLayerFace := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hpositions := oppositeRung_cornerPositions_pairwise_ne
    (incoming := sharedPlacement.incomingPosition.val)
    (outgoing := sharedPlacement.outgoingPosition.val)
    (firstBefore := first.toInterface.rightBeforePos.1.val)
    (firstAfter := first.toInterface.rightAfterPos.1.val)
    (secondBefore := second.toInterface.leftBeforePos.1.val)
    (secondAfter := second.toInterface.leftAfterPos.1.val)
    (by simpa [sharedPlacement] using hopposite)
    (by simpa [sharedPlacement] using first.rightBefore_followsIncoming)
    (by simpa [sharedPlacement] using first.rightAfter_precedesIncoming)
    (by simpa [sharedPlacement] using second.leftBefore_precedesOutgoing)
    (by simpa [sharedPlacement] using second.leftAfter_followsOutgoing)
  rcases hpositions with ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩
  have hfirstBefore : first.toInterface.firstLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement first.toInterface.rightBeforePos := by
    simpa [sharedPlacement] using first.toInterface.firstLayerFace_eq_next_firstLayerFace
  have hfirstAfter : first.toInterface.secondLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement first.toInterface.rightAfterPos := by
    simpa [sharedPlacement] using first.toInterface.secondLayerFace_eq_next_secondLayerFace
  have hsecondBefore : second.toInterface.firstLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement second.toInterface.leftBeforePos := by
    rfl
  have hsecondAfter : second.toInterface.secondLayerFace =
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique sharedPlacement second.toInterface.leftAfterPos := by
    rfl
  have face_ne_of_position_ne : ∀
      (left right : {position // position ∈ placementSidePositions sharedPlacement}),
      left ≠ right →
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
          hunique sharedPlacement left ≠
        placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
          hunique sharedPlacement right := by
    intro left right hpositions hfaces
    exact hpositions (placementSideNeighbor_injective
      realization.toCleanOrbitHexCorridorSkeleton htwoSided hunique sharedPlacement hfaces)
  have sidePosition_ne_of_value_ne : ∀
      (left right : {position // position ∈ placementSidePositions sharedPlacement}),
      left.1.val ≠ right.1.val → left ≠ right := by
    intro left right hvalues hpositions
    exact hvalues (congrArg (fun position => position.1.val) hpositions)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hfirstBefore, hfirstAfter] using
      face_ne_of_position_ne first.toInterface.rightBeforePos
        first.toInterface.rightAfterPos
          (sidePosition_ne_of_value_ne _ _ hAB)
  · simpa [hfirstBefore, hsecondBefore] using
      face_ne_of_position_ne first.toInterface.rightBeforePos
        second.toInterface.leftBeforePos
          (sidePosition_ne_of_value_ne _ _ hAC)
  · simpa [hfirstBefore, hsecondAfter] using
      face_ne_of_position_ne first.toInterface.rightBeforePos
        second.toInterface.leftAfterPos
          (sidePosition_ne_of_value_ne _ _ hAD)
  · simpa [hfirstAfter, hsecondBefore] using
      face_ne_of_position_ne first.toInterface.rightAfterPos
        second.toInterface.leftBeforePos
          (sidePosition_ne_of_value_ne _ _ hBC)
  · simpa [hfirstAfter, hsecondAfter] using
      face_ne_of_position_ne first.toInterface.rightAfterPos
        second.toInterface.leftAfterPos
          (sidePosition_ne_of_value_ne _ _ hBD)
  · simpa [hsecondBefore, hsecondAfter] using
      face_ne_of_position_ne second.toInterface.leftBeforePos
        second.toInterface.leftAfterPos
          (sidePosition_ne_of_value_ne _ _ hCD)

/-- The two local source layers and their two opposite-rung rail steps form
the literal six-edge facial-dual boundary of a two-tile layer. -/
noncomputable def sourceCornerAlignedTwoTileLayerBoundary_of_oppositeRungs
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hopposite :
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition.val ≡
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)).incomingPosition.val + 3 [MOD 6]) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      first.toInterface.firstLayerFace first.toInterface.firstLayerFace := by
  let rails := sourceCornerAlignedRailStep_of_oppositeRungs hcubic hrotation
    first second hopposite
  exact SimpleGraph.Walk.cons first.toInterface.firstLayerFace_adjacent_centerLayerFace
    (SimpleGraph.Walk.cons first.toInterface.centerLayerFace_adjacent_secondLayerFace
      (SimpleGraph.Walk.cons rails.2
        (SimpleGraph.Walk.cons second.toInterface.centerLayerFace_adjacent_secondLayerFace.symm
          (SimpleGraph.Walk.cons second.toInterface.firstLayerFace_adjacent_centerLayerFace.symm
            (SimpleGraph.Walk.cons rails.1.symm SimpleGraph.Walk.nil)))))

@[simp]
theorem sourceCornerAlignedTwoTileLayerBoundary_length_of_oppositeRungs
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hopposite :
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition.val ≡
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)).incomingPosition.val + 3 [MOD 6]) :
    (sourceCornerAlignedTwoTileLayerBoundary_of_oppositeRungs hcubic hrotation
      first second hopposite).length = 6 := by
  simp [sourceCornerAlignedTwoTileLayerBoundary_of_oppositeRungs]

/-- The literal two-tile layer boundary is simple.  This closes the local
source construction into an actual layer boundary: its six faces are checked
distinct from the corridor coordinates and the two certified rail steps, not
postulated as a Jordan premise. -/
theorem sourceCornerAlignedTwoTileLayerBoundary_isCycle_of_oppositeRungs
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hopposite :
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).outgoingPosition.val ≡
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)).incomingPosition.val + 3 [MOD 6]) :
    (sourceCornerAlignedTwoTileLayerBoundary_of_oppositeRungs hcubic hrotation
      first second hopposite).IsCycle := by
  let rails := sourceCornerAlignedRailStep_of_oppositeRungs hcubic hrotation
    first second hopposite
  rcases sourceCornerAlignedExteriorFaces_pairwise_ne_of_oppositeRungs
      first second hopposite with ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩
  have hcenterIndex : leftInterior.center ≠
      (nextCorridorInterior leftInterior hnext).center := by
    intro h
    have hvalues := congrArg Fin.val h
    change leftInterior.center.val = leftInterior.center.val + 1 at hvalues
    omega
  have hXY : first.toInterface.centerLayerFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.centerLayerFace] using
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt_ne
        hcenterIndex
  have hAX : first.toInterface.firstLayerFace ≠ first.toInterface.centerLayerFace :=
    first.toInterface.firstLayerFace_ne_centerLayerFace
  have hDY : second.toInterface.secondLayerFace ≠ second.toInterface.centerLayerFace :=
    second.toInterface.secondLayerFace_ne_centerLayerFace
  have hAY : first.toInterface.firstLayerFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.firstLayerFace,
      SourceConsecutiveSlabInterface.centerLayerFace] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique (realization.slabPlacementAt htwoSided hunique leftInterior)
        first.toInterface.leftBeforePos
        (nextCorridorInterior leftInterior hnext).center
  have hBY : first.toInterface.secondLayerFace ≠ second.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.secondLayerFace,
      SourceConsecutiveSlabInterface.centerLayerFace] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique (realization.slabPlacementAt htwoSided hunique leftInterior)
        first.toInterface.leftAfterPos
        (nextCorridorInterior leftInterior hnext).center
  have hCX : second.toInterface.firstLayerFace ≠ first.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.firstLayerFace,
      SourceConsecutiveSlabInterface.centerLayerFace] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext))
        second.toInterface.leftBeforePos leftInterior.center
  have hDX : second.toInterface.secondLayerFace ≠ first.toInterface.centerLayerFace := by
    simpa [SourceConsecutiveSlabInterface.secondLayerFace,
      SourceConsecutiveSlabInterface.centerLayerFace] using
      placementSideNeighbor_ne_faceAt realization.toCleanOrbitHexCorridorSkeleton
        htwoSided hunique
        (realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext))
        second.toInterface.leftAfterPos leftInterior.center
  let firstRail := first.toInterface.localLayer.walk.concat rails.2
  let secondRail := second.toInterface.localLayer.walk.reverse.concat rails.1.symm
  have hfirstRail : firstRail.IsPath := by
    apply SimpleGraph.Walk.IsPath.concat first.toInterface.localLayer.isPath
    simp [SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      hAD.symm, hBD.symm, hDX]
  have hsecondRail : secondRail.IsPath := by
    apply SimpleGraph.Walk.IsPath.concat second.toInterface.localLayer.isPath.reverse
    simp [SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      hAD, hAC, hAY]
  have htails : firstRail.support.tail.Disjoint secondRail.support.tail := by
    simp [firstRail, secondRail, SourceConsecutiveSlabInterface.localLayer,
      SourceConsecutiveSlabInterface.localLayerWalk,
      hAB, hAD, hBC.symm, hCD, hAX, hDY.symm, hBY.symm, hCX, hXY.symm]
  have hcycle : (firstRail.append secondRail).IsCycle :=
    SimpleGraph.Walk.IsPath.isCycle_append hfirstRail hsecondRail htails
      (Or.inl (by
        simp [firstRail, SourceConsecutiveSlabInterface.localLayer,
          SourceConsecutiveSlabInterface.localLayerWalk]))
  simpa [sourceCornerAlignedTwoTileLayerBoundary_of_oppositeRungs,
    firstRail, secondRail, SourceConsecutiveSlabInterface.localLayer,
    SourceConsecutiveSlabInterface.localLayerWalk, SimpleGraph.Walk.concat] using hcycle

/-- The source word's actual `forwardThree` symbol selects the opposite-rung
case above, so it yields both concrete one-step rail continuations without an
extra geometric premise. -/
theorem sourceCornerAlignedRailStep_of_forwardThree
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hthree : orientedSlabTypeOfPlacement
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext))
      (realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation
        htwoSided hunique (nextCorridorInterior leftInterior hnext)) = .forwardThree) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        first.toInterface.firstLayerFace second.toInterface.firstLayerFace ∧
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        first.toInterface.secondLayerFace second.toInterface.secondLayerFace := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hnonadjacent : sharedPlacement.rungType ≠ HexRungType.adjacent := by
    simpa [sharedPlacement] using
      realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation htwoSided
        hunique (nextCorridorInterior leftInterior hnext)
  have hdistance : hexForwardDistance sharedPlacement.incomingPosition6
      sharedPlacement.outgoingPosition6 = 3 := by
    simpa [sharedPlacement, hthree, OrientedInducedHexSlabType.forwardDistance] using
      (orientedSlabTypeOfPlacement_forwardDistance sharedPlacement hnonadjacent).symm
  have hopposite6 : sharedPlacement.outgoingPosition6.val ≡
      sharedPlacement.incomingPosition6.val + 3 [MOD 6] :=
    outgoing_modEq_of_hexForwardDistance_three _ _ hdistance
  have hopposite : sharedPlacement.outgoingPosition.val ≡
      sharedPlacement.incomingPosition.val + 3 [MOD 6] := by
    simpa [InternalHexRungPlacement.incomingPosition6,
      InternalHexRungPlacement.outgoingPosition6] using hopposite6
  exact sourceCornerAlignedRailStep_of_oppositeRungs hcubic hrotation first second
    (by simpa [sharedPlacement] using hopposite)

/-- At a source `forwardThree` tile, the constructed two-tile layer boundary
is a simple facial-dual cycle.  Thus the finite source word supplies a real
layer-boundary witness, rather than a chord-wall surrogate. -/
theorem sourceCornerAlignedTwoTileLayerBoundary_isCycle_of_forwardThree
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hthree : orientedSlabTypeOfPlacement
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext))
      (realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation
        htwoSided hunique (nextCorridorInterior leftInterior hnext)) = .forwardThree) :
    (sourceCornerAlignedTwoTileLayerBoundary_of_oppositeRungs hcubic hrotation
      first second (by
        let sharedPlacement := realization.slabPlacementAt htwoSided hunique
          (nextCorridorInterior leftInterior hnext)
        have hnonadjacent : sharedPlacement.rungType ≠ HexRungType.adjacent := by
          simpa [sharedPlacement] using
            realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation htwoSided
              hunique (nextCorridorInterior leftInterior hnext)
        have hdistance : hexForwardDistance sharedPlacement.incomingPosition6
            sharedPlacement.outgoingPosition6 = 3 := by
          simpa [sharedPlacement, hthree, OrientedInducedHexSlabType.forwardDistance] using
            (orientedSlabTypeOfPlacement_forwardDistance sharedPlacement hnonadjacent).symm
        have hopposite6 : sharedPlacement.outgoingPosition6.val ≡
            sharedPlacement.incomingPosition6.val + 3 [MOD 6] :=
          outgoing_modEq_of_hexForwardDistance_three _ _ hdistance
        simpa [sharedPlacement, InternalHexRungPlacement.incomingPosition6,
          InternalHexRungPlacement.outgoingPosition6] using hopposite6)).IsCycle := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hnonadjacent : sharedPlacement.rungType ≠ HexRungType.adjacent := by
    simpa [sharedPlacement] using
      realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation htwoSided
        hunique (nextCorridorInterior leftInterior hnext)
  have hdistance : hexForwardDistance sharedPlacement.incomingPosition6
      sharedPlacement.outgoingPosition6 = 3 := by
    simpa [sharedPlacement, hthree, OrientedInducedHexSlabType.forwardDistance] using
      (orientedSlabTypeOfPlacement_forwardDistance sharedPlacement hnonadjacent).symm
  have hopposite6 : sharedPlacement.outgoingPosition6.val ≡
      sharedPlacement.incomingPosition6.val + 3 [MOD 6] :=
    outgoing_modEq_of_hexForwardDistance_three _ _ hdistance
  have hopposite : sharedPlacement.outgoingPosition.val ≡
      sharedPlacement.incomingPosition.val + 3 [MOD 6] := by
    simpa [InternalHexRungPlacement.incomingPosition6,
      InternalHexRungPlacement.outgoingPosition6] using hopposite6
  simpa [sharedPlacement] using
    sourceCornerAlignedTwoTileLayerBoundary_isCycle_of_oppositeRungs
      hcubic hrotation first second hopposite

/-- Every non-adjacent source slab has one of the three finite oriented
forms, and each form supplies a literal simple six-edge layer boundary.  The
dispatcher follows the three concrete constructions it combines. -/
theorem exists_sourceCornerAlignedTwoTileLayerBoundary_isCycle
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext) :
    ∃ boundary : (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
        first.toInterface.firstLayerFace first.toInterface.firstLayerFace,
      boundary.IsCycle ∧ boundary.length = 6 := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hnonadjacent : sharedPlacement.rungType ≠ HexRungType.adjacent := by
    simpa [sharedPlacement] using
      realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation htwoSided
        hunique (nextCorridorInterior leftInterior hnext)
  rcases hexForwardDistance_eq_two_or_three_or_four
      sharedPlacement.incomingPosition6 sharedPlacement.outgoingPosition6
      sharedPlacement.positions6_ne hnonadjacent with htwo | hthree | hfour
  · exact exists_sourceCornerAlignedTwoTileLayerBoundary_isCycle_of_forwardTwo
      hcubic hrotation first second (by simpa [sharedPlacement] using htwo)
  · have hopposite6 : sharedPlacement.outgoingPosition6.val ≡
        sharedPlacement.incomingPosition6.val + 3 [MOD 6] :=
      outgoing_modEq_of_hexForwardDistance_three _ _ hthree
    have hopposite : sharedPlacement.outgoingPosition.val ≡
        sharedPlacement.incomingPosition.val + 3 [MOD 6] := by
      simpa [InternalHexRungPlacement.incomingPosition6,
        InternalHexRungPlacement.outgoingPosition6] using hopposite6
    let boundary := sourceCornerAlignedTwoTileLayerBoundary_of_oppositeRungs
      hcubic hrotation first second (by simpa [sharedPlacement] using hopposite)
    refine ⟨boundary, ?_, ?_⟩
    · simpa [boundary] using
        sourceCornerAlignedTwoTileLayerBoundary_isCycle_of_oppositeRungs
          hcubic hrotation first second (by simpa [sharedPlacement] using hopposite)
    · simp [boundary, sourceCornerAlignedTwoTileLayerBoundary_of_oppositeRungs]
  · exact exists_sourceCornerAlignedTwoTileLayerBoundary_isCycle_of_forwardFour
      hcubic hrotation first second (by simpa [sharedPlacement] using hfour)

/-- The source word's `forwardTwo` symbol supplies a concrete bent rail:
one endpoint is shared and the other travels through an explicitly realized
exterior hexagon. -/
theorem sourceCornerAlignedBentRailStep_of_sourceForwardTwo
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (htwo : orientedSlabTypeOfPlacement
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext))
      (realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation
        htwoSided hunique (nextCorridorInterior leftInterior hnext)) = .forwardTwo) :
    Nonempty (SourceCornerAlignedForwardTwoRailWitness first second) := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hnonadjacent : sharedPlacement.rungType ≠ HexRungType.adjacent := by
    simpa [sharedPlacement] using
      realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation htwoSided
        hunique (nextCorridorInterior leftInterior hnext)
  have hdistance : hexForwardDistance sharedPlacement.incomingPosition6
      sharedPlacement.outgoingPosition6 = 2 := by
    simpa [sharedPlacement, htwo, OrientedInducedHexSlabType.forwardDistance] using
      (orientedSlabTypeOfPlacement_forwardDistance sharedPlacement hnonadjacent).symm
  exact sourceCornerAlignedBentRailStep_of_forwardTwo hcubic hrotation first second
    (by simpa [sharedPlacement] using hdistance)

/-- The source word's `forwardFour` symbol supplies the mirror bent rail.
Together with `forwardTwo` and `forwardThree`, this discharges every finite
local slab type generated by an induced source corridor. -/
theorem sourceCornerAlignedBentRailStep_of_sourceForwardFour
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    {realization : BoundaryCleanCorridorRealization embedded blockLength}
    {htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {hnextNext : (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (first : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (second : SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior leftInterior hnext) hnextNext)
    (hfour : orientedSlabTypeOfPlacement
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext))
      (realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation
        htwoSided hunique (nextCorridorInterior leftInterior hnext)) = .forwardFour) :
    Nonempty (SourceCornerAlignedForwardFourRailWitness first second) := by
  let sharedPlacement := realization.slabPlacementAt htwoSided hunique
    (nextCorridorInterior leftInterior hnext)
  have hnonadjacent : sharedPlacement.rungType ≠ HexRungType.adjacent := by
    simpa [sharedPlacement] using
      realization.slabPlacementAt_rungType_ne_adjacent hcubic hrotation htwoSided
        hunique (nextCorridorInterior leftInterior hnext)
  have hdistance : hexForwardDistance sharedPlacement.incomingPosition6
      sharedPlacement.outgoingPosition6 = 4 := by
    simpa [sharedPlacement, hfour, OrientedInducedHexSlabType.forwardDistance] using
      (orientedSlabTypeOfPlacement_forwardDistance sharedPlacement hnonadjacent).symm
  exact sourceCornerAlignedBentRailStep_of_forwardFour hcubic hrotation first second
    (by simpa [sharedPlacement] using hdistance)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
