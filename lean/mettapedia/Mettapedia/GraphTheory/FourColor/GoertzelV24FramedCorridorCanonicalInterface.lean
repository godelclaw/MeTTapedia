import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorOpenSlab
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorColorTransfer

/-!
# Canonical corner-aligned interfaces in a source corridor

A source corridor interface has two matching exterior faces across each
consecutive pair of hexagons.  This file strengthens that local fact with the
rotation-system coordinates of those faces: on the left hexagon they flank
the outgoing rung, and on the right they flank the incoming rung.  Thus the
interface is a literal continuation datum for the two boundary rails, rather
than an independently chosen pair of matching faces at every position.

This is generic corridor geometry used by the reductive splice.  It introduces
no configuration catalogue or covering-style reduction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorColorTransfer
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

/-- A source interface together with the checked cyclic positions of all four
ports.  The edge identities are retained because they are what prevents a
later rail induction from silently switching to another local match. -/
structure SourceCornerAlignedSlabInterface
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) where
  toInterface : SourceConsecutiveSlabInterface realization htwoSided hunique
    leftInterior hnext
  leftBefore_precedesOutgoing :
    (realization.slabPlacementAt htwoSided hunique leftInterior).outgoingPosition.val ≡
      toInterface.leftBeforePos.1.val + 1 [MOD 6]
  leftAfter_followsOutgoing :
    toInterface.leftAfterPos.1.val ≡
      (realization.slabPlacementAt htwoSided hunique leftInterior).outgoingPosition.val + 1
        [MOD 6]
  rightBefore_followsIncoming :
    toInterface.rightBeforePos.1.val ≡
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)).incomingPosition.val + 1 [MOD 6]
  rightAfter_precedesIncoming :
    (realization.slabPlacementAt htwoSided hunique
      (nextCorridorInterior leftInterior hnext)).incomingPosition.val ≡
      toInterface.rightAfterPos.1.val + 1 [MOD 6]
  rightBefore_edge :
    placementSideEdge htwoSided
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)) toInterface.rightBeforePos =
      beforeOutgoingCornerEdge
        (realization.slabPlacementAt htwoSided hunique leftInterior)
  rightAfter_edge :
    placementSideEdge htwoSided
      (realization.slabPlacementAt htwoSided hunique
        (nextCorridorInterior leftInterior hnext)) toInterface.rightAfterPos =
      afterOutgoingCornerEdge
        (realization.slabPlacementAt htwoSided hunique leftInterior)

namespace BoundaryCleanCorridorRealization

/-- The facial rotations construct a corner-aligned interface for every
actual consecutive source pair.  In particular, the four positions are not
independent `Classical.choice` values. -/
theorem exists_sourceCornerAlignedSlabInterface
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Nonempty (SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) := by
  let clean := realization.toCleanOrbitHexCorridorSkeleton
  let leftPlacement := realization.slabPlacementAt htwoSided hunique leftInterior
  let rightInterior := nextCorridorInterior leftInterior hnext
  let rightPlacement := realization.slabPlacementAt htwoSided hunique rightInterior
  have hnonadjacent : leftPlacement.rungType ≠ HexRungType.adjacent :=
    InternalHexRungPlacement.rungType_ne_adjacent
      leftPlacement hcubic hrotation htwoSided
  rcases exists_two_hexSidePositions_flanking_outgoing
    leftPlacement.incomingPosition6 leftPlacement.outgoingPosition6
      leftPlacement.positions6_ne hnonadjacent with
    ⟨leftBefore6, leftAfter6, hleftBeforeAfter, hbeforeMod, hafterMod⟩
  let leftBefore := placementSidePositionOfSix leftPlacement leftBefore6
  let leftAfter := placementSidePositionOfSix leftPlacement leftAfter6
  have hleftBeforeAfter' : leftBefore ≠ leftAfter := by
    intro heq
    apply hleftBeforeAfter
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
    apply hleftBeforeAfter'
    apply placementSideNeighbor_injective clean htwoSided hunique leftPlacement
    calc
      placementSideNeighbor clean htwoSided hunique leftPlacement leftBefore =
          placementSideNeighbor clean htwoSided hunique rightPlacement rightBefore :=
        hrightBeforeFace
      _ = placementSideNeighbor clean htwoSided hunique rightPlacement rightAfter := by
        rw [heq]
      _ = placementSideNeighbor clean htwoSided hunique leftPlacement leftAfter :=
        hrightAfterFace.symm
  let interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext := {
    leftBeforePos := leftBefore
    leftAfterPos := leftAfter
    rightBeforePos := rightBefore
    rightAfterPos := rightAfter
    left_distinct := hleftBeforeAfter'
    right_distinct := hrightBeforeAfter
    before_match := hrightBeforeFace
    after_match := hrightAfterFace
  }
  have hrightBeforeActual : rightBefore.1.val ≡
      rightPlacement.incomingPosition.val + 1 [MOD 6] :=
    nextPlacement_beforeCornerPosition_after_incoming htwoSided hunique
      leftInterior hnext leftPlacement rightPlacement rightBefore hrightBeforeEdge
  have hrightAfterActual : rightPlacement.incomingPosition.val ≡
      rightAfter.1.val + 1 [MOD 6] :=
    nextPlacement_incoming_after_afterCornerPosition hcubic hrotation
      htwoSided hunique leftInterior hnext leftPlacement rightPlacement rightAfter
        hrightAfterEdge
  exact ⟨{
    toInterface := interface
    leftBefore_precedesOutgoing := by simpa [interface] using hbeforeActual
    leftAfter_followsOutgoing := by simpa [interface] using hafterActual
    rightBefore_followsIncoming := by
      simpa [interface, rightPlacement, rightInterior] using hrightBeforeActual
    rightAfter_precedesIncoming := by
      simpa [interface, rightPlacement, rightInterior] using hrightAfterActual
    rightBefore_edge := by
      simpa [interface, rightPlacement, rightInterior] using hrightBeforeEdge
    rightAfter_edge := by
      simpa [interface, rightPlacement, rightInterior] using hrightAfterEdge
  }⟩

/-- The canonical source interface used by subsequent rail formation.  The
choice resolves only a finite orientation after the corner identities above
have been constructed and retained. -/
noncomputable def sourceCornerAlignedSlabInterface
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext :=
  Classical.choice
    (realization.exists_sourceCornerAlignedSlabInterface hcubic hrotation
      htwoSided hunique leftInterior hnext)

end BoundaryCleanCorridorRealization

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
