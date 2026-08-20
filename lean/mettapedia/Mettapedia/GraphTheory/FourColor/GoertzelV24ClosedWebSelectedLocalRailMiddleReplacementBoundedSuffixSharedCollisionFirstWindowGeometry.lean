import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollisionBands

/-!
# L1: normalize the remaining shared collision to one ladder cell

Remote separation has already removed the shifted future's last terminal
window.  A retained shared-prefix collision is therefore supported by the
literal first live pair and by the exact terminal window on the following two
cells.  This module translates that finite support statement into the source
ladder's geometric vocabulary.

Only three shapes survive: the displayed second centre, a first--second dual
triangle, or a first--third distance-two square.  The third centre itself is
excluded by corridor separation.  The result retains the exact support packet
beside the geometric classification.  It does not apply the rotor or square
consumer, eliminate any of the three shapes, assemble an arbitrary corridor,
attach end caps, construct crosscuts, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
    {hfourthNext :
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center.val + 2 < blockLength}
    {firstPlacement : SelectedInternalHexRungPlacement corridor rungs firstInterior}
    {secondPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext)}
    {thirdPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)}
    {fourthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext)}
    {fifthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext)
        hfourthNext)}
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      firstPlacement secondPlacement}
    {bridge : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement}
    {lastSuccessor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement}
    {fourthSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfourthNext
      fourthPlacement fifthPlacement}
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions firstPlacement}}
    {firstLeft : SeparatedSelectedSourceLocalRailPaths firstPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev ShiftedFuture :=
  SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
    (firstInterior := nextCorridorInterior firstInterior hfirstNext)
    (hfirstNext := hbridgeNext) (hbridgeNext := hlastNext)
    (hlastNext := hfourthNext)
    (firstPlacement := secondPlacement) (secondPlacement := thirdPlacement)
    (thirdPlacement := fourthPlacement) (fourthPlacement := fifthPlacement)
    (firstSuccessor := bridge) (bridge := lastSuccessor)
    (lastSuccessor := fourthSuccessor)
    (firstLeft := firstSuccessor.rightRailsAsNextLeft bridge)

/-- The exact first-window packet together with its source-ladder geometry.
Keeping both fields prevents a later consumer from forgetting the literal
support evidence while pattern-matching on the three geometric cases. -/
structure RetainedSharedCollisionFirstWindowResolution
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (face : SelectedFace (web := web)) : Prop where
  sourceData : RetainedSharedCollisionFirstWindowData
    (corridor := corridor) (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext) (hfourthNext := hfourthNext)
    (firstLeft := firstLeft) future face
  ladderGeometry : ExactSelectedLocalRailMiddleReplacementLadderGeometry
    (corridor := corridor) (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext) face

/-- **L1 exact first-window geometry.**  A retained shared collision in the
only surviving terminal window is a second centre, an adjacent dual triangle,
or a distance-two square in the source ladder. -/
theorem RetainedSharedCollisionFirstWindowData.toResolution
    {future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)}
    {face : SelectedFace (web := web)}
    (sourceData : RetainedSharedCollisionFirstWindowData
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (firstLeft := firstLeft) future face) :
    RetainedSharedCollisionFirstWindowResolution
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (firstLeft := firstLeft) future face := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let second := (nextCorridorInterior firstInterior hfirstNext).center
  let third :=
    (nextCorridorInterior
      (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
  have hfirstAdjacent : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt firstInterior.center) face := by
    rcases sourceData.firstLive with hfirst | hsecond
    · exact firstLeft.paths.firstRail_support_adjacent_center face hfirst
    · exact firstLeft.paths.secondRail_support_adjacent_center face hsecond
  have hnear : FaceNearSelectedCenterPair (corridor := corridor)
      second third face := by
    rcases sourceData.futureSupport with hfirst | hsecond
    · exact faceNearSelectedCenterPair_of_mem_adjacentSelectedRailPieces
        (future.transition.firstTrace.toExactTerminalWindow
          |>.firstSupport_in_adjacentPieces face hfirst)
    · exact faceNearSelectedCenterPair_of_mem_adjacentSelectedRailPieces
        (future.transition.firstTrace.toExactTerminalWindow
          |>.secondSupport_in_adjacentPieces face hsecond)
  refine ⟨sourceData, ?_⟩
  rcases hnear with hsecond | hthird | hsecondAdjacent | hthirdAdjacent
  · exact .secondCenter hsecond
  · subst face
    exact False.elim ((skeleton.separated_not_adjacent
      firstInterior.center third (by dsimp [third]; omega)) hfirstAdjacent)
  · exact .firstSecondTriangle hfirstAdjacent hsecondAdjacent
  · by_cases hfaceSecond : face = skeleton.faceAt second
    · exact .secondCenter hfaceSecond
    · exact .firstThirdSquare hfirstAdjacent hthirdAdjacent hfaceSecond

/-- Every failure of the bounded shared-prefix append now carries source
geometry.  Future failures retain their exact four-cell band; retained-prefix
failures retain the exact three-cell packet together with its centre/triangle/
square classification.  Successful constructors remain successful. -/
def BoundedLiveSharedRailAppendOutcome.HasResolvedCollisionGeometry
    {firstStart secondStart : SelectedFace (web := web)}
    {prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)}
    (frozen : SourceTiedBoundedLiveSharedRailPrefix
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (firstSuccessor := firstSuccessor)
      (firstIncomingBefore := firstIncomingBefore)
      (firstIncomingAfter := firstIncomingAfter) (firstLeft := firstLeft)
      prefixAssembly)
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (outcome : BoundedLiveSharedRailAppendOutcome frozen.toBounded future) : Prop :=
  match outcome with
  | .straight _ | .swapped _ => True
  | .futureCollision _ =>
      ∃ face : SelectedFace (web := web),
        ExactSelectedLocalRailFourCellCollisionBandWithMiddleTrace
          future.transition face
  | .retainedStraightCollision _ _ collision
  | .retainedSwappedCollision _ _ collision =>
      RetainedSharedCollisionFirstWindowResolution
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
        (hlastNext := hlastNext) (hfourthNext := hfourthNext)
        (firstLeft := firstLeft) future collision.face

/-- **L1 resolved collision geometry.**  The constructed bounded transition
either succeeds or returns exact source geometry.  This theorem does not run a
triangle or square consumer, so it is not an append construction or L1
closure. -/
theorem BoundedLiveSharedRailAppendTransition.hasResolvedCollisionGeometry
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter))
    (state : BoundedLiveMiddleReplacementState
      (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (thirdPlacement := thirdPlacement) (fourthPlacement := fourthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
      prefixAssembly)
    (transition : BoundedLiveSharedRailAppendTransition
      (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
      (fourthSuccessor := fourthSuccessor) prefixAssembly state) :
    transition.outcome.HasResolvedCollisionGeometry transition.frozen
      transition.common.future := by
  have hlocalized := transition.hasLocalizedCollisionData
  cases houtcome : transition.outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | futureCollision collision =>
      rw [houtcome] at hlocalized
      exact hlocalized
  | retainedStraightCollision futureAssembly hfuture collision =>
      rw [houtcome] at hlocalized
      exact hlocalized.toResolution
  | retainedSwappedCollision futureAssembly hfuture collision =>
      rw [houtcome] at hlocalized
      exact hlocalized.toResolution

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
