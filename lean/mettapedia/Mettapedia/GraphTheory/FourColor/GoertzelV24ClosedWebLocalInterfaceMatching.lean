import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerFormation

/-!
# Consecutive source-local Cell-3 side interfaces

The two local paths around one Cell-3 tile are not themselves the completed
annular crosscuts used by the source splice.  Nevertheless, a lengthwise
assembly needs a concrete compatibility fact: the two side faces immediately
beside one cell's outgoing rung also occur as side faces of the next cell.

This file proves precisely that local overlap from actual face incidence.  It
does not assert that a chain of these windows is already a simple transversal,
that their primal regions are disjoint, or that the resulting paths reach the
two annular holes.  Those are the remaining source-local-to-global L9
construction obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace LocalLayerFormation

/-- The local width-four side interfaces of consecutive Cell-3 corridor
faces have two common external face slots.  This is only a facial-dual
interface match; it is deliberately weaker than a completed source
transversal or an open-tangle serial-composition theorem. -/
def LocalConsecutiveLayerSideSlotsMatch
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior)
    (rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)) : Prop :=
  ∃ leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement},
    ∃ rightBefore rightAfter :
      {position // position ∈ placementSidePositions rightPlacement},
      leftBefore ≠ leftAfter ∧ rightBefore ≠ rightAfter ∧
        localPlacementSideFace leftPlacement leftBefore =
          localPlacementSideFace rightPlacement rightBefore ∧
        localPlacementSideFace leftPlacement leftAfter =
          localPlacementSideFace rightPlacement rightAfter

/-- **L9 (local crosscut assembly).** Consecutive boundary-clean Cell-3
faces have two explicitly matched external side slots.  The match is derived
from the outgoing-rung corner, full-axis externality, and the next face's
complete four-slot lookup.  In particular no global cubicity or caller-made
two-sidedness assumption is used. -/
theorem localConsecutiveLayerSideSlotsMatch
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior)
    (rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)) :
    LocalConsecutiveLayerSideSlotsMatch corridor hunique leftInterior hnext
      leftPlacement rightPlacement := by
  have hnonadjacent : leftPlacement.rungType ≠ HexRungType.adjacent :=
    InternalHexRungPlacement.rungType_ne_adjacent_of_cell3
      corridor hunique leftInterior leftPlacement
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
    have hvalues := congrArg (fun position => position.1.val) heq
    exact Fin.ext hvalues
  have hbeforeActual : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6] := by
    simpa [leftBefore, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.outgoingPosition6] using hbeforeMod
  have hafterActual : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6] := by
    simpa [leftAfter, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.outgoingPosition6] using hafterMod
  let beforeFace := localPlacementSideFace leftPlacement leftBefore
  let afterFace := localPlacementSideFace leftPlacement leftAfter
  have hbeforeAdjacent : (interiorDualGraph
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior leftInterior hnext).center)
        beforeFace := by
    simpa [beforeFace] using
      (localPlacementSideFace_adjacent_next_of_before_outgoing
        (corridor := corridor) hnext leftPlacement leftBefore hbeforeActual).symm
  have hafterAdjacent : (interiorDualGraph
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior leftInterior hnext).center)
        afterFace := by
    simpa [afterFace] using
      (localPlacementSideFace_adjacent_next_of_after_outgoing
        (corridor := corridor) hnext leftPlacement leftAfter hafterActual).symm
  have hbeforeExternal : ∀ index : Fin blockLength,
      beforeFace ≠
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          index := by
    intro index
    simpa [beforeFace] using
      localPlacementSideFace_ne_faceAt (corridor := corridor)
        leftPlacement leftBefore index
  have hafterExternal : ∀ index : Fin blockLength,
      afterFace ≠
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          index := by
    intro index
    simpa [afterFace] using
      localPlacementSideFace_ne_faceAt (corridor := corridor)
        leftPlacement leftAfter index
  rcases exists_localPlacementSideFace_eq_of_adjacent_external
      (corridor := corridor) rightPlacement beforeFace hbeforeAdjacent
      hbeforeExternal with ⟨rightBefore, hbeforeMatch⟩
  rcases exists_localPlacementSideFace_eq_of_adjacent_external
      (corridor := corridor) rightPlacement afterFace hafterAdjacent
      hafterExternal with ⟨rightAfter, hafterMatch⟩
  have hrightBeforeAfter : rightBefore ≠ rightAfter := by
    intro heq
    apply hleftBeforeAfter
    apply localPlacementSideFace_injective (corridor := corridor)
      leftPlacement
    change beforeFace = afterFace
    rw [← hbeforeMatch, ← hafterMatch, heq]
  exact ⟨leftBefore, leftAfter, rightBefore, rightAfter,
    hleftBeforeAfter, hrightBeforeAfter, hbeforeMatch.symm, hafterMatch.symm⟩

/-- The canonical source-derived placements satisfy the same local matching
law.  This packages the finite Cell-3 construction for a later path assembly
without conflating it with the as-yet-unbuilt annular crosscuts. -/
theorem canonicalLocalConsecutiveLayerSideSlotsMatch
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    LocalConsecutiveLayerSideSlotsMatch corridor hunique leftInterior hnext
      (localInternalHexRungPlacement corridor hunique leftInterior)
      (localInternalHexRungPlacement corridor hunique
        (nextCorridorInterior leftInterior hnext)) :=
  localConsecutiveLayerSideSlotsMatch corridor hunique leftInterior hnext
    (localInternalHexRungPlacement corridor hunique leftInterior)
    (localInternalHexRungPlacement corridor hunique
      (nextCorridorInterior leftInterior hnext))

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
