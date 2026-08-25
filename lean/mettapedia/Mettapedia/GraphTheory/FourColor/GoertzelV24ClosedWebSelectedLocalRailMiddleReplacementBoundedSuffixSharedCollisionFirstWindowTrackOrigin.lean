import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollisionFirstWindowComponent

/-!
# L1: retain the exact rail origin of a first-window shared collision

The first-window geometry and separator packets deliberately localize a
retained collision to a bounded three-cell window.  That localization formerly
forgot one piece of data which a local bypass consumer needs: whether the face
came from the old first rail and the future second rail, or from the old second
rail and the future first rail.

This module retains that cross-track origin and combines it with the already
constructed cyclic/star/bond component resolution.  It adds no separation or
repair hypothesis.  In particular, it does not identify the two other faces of
an endpoint triangle with predecessor and successor faces on a rail, prove the
rerouted rail disjoint from its companion, iterate the rolling transition,
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

/-- Exact literal tracks on which a newly retained first-window collision
occurs.  The suffix occurrence remains in `support.tail`, retaining the fact
that it is not merely the future rail's starting endpoint. -/
inductive RetainedSharedCollisionFirstWindowTrackOrigin
    {firstFinish secondFinish : SelectedFace (web := web)}
    (futureAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish)
    (face : SelectedFace (web := web)) : Prop
  | firstSecond
      (firstLive : face ∈ firstLeft.toAssembly.firstRail.support)
      (futureSecond : face ∈ futureAssembly.secondRail.support.tail)
  | secondFirst
      (secondLive : face ∈ firstLeft.toAssembly.secondRail.support)
      (futureFirst : face ∈ futureAssembly.firstRail.support.tail)

/-- Source separation removes the frozen prefix alternative from the exact
cross origin, leaving the corresponding literal first-window rail. -/
theorem RetainedBypassCrossCollision.firstWindowTrackOrigin_of_sourceTied
    {firstStart secondStart firstFinish secondFinish : SelectedFace (web := web)}
    {prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)}
    (state : BoundedLiveMiddleReplacementState
      (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext)
      (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
      (thirdPlacement := thirdPlacement) (fourthPlacement := fourthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)
      prefixAssembly)
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
    {futureAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish}
    (collision : RetainedBypassCrossCollision
      frozen.toBounded.assembly futureAssembly)
    (hcontains : future.transition.outcome.SuccessfulRailContains collision.face) :
    RetainedSharedCollisionFirstWindowTrackOrigin
      (firstLeft := firstLeft) futureAssembly collision.face := by
  have hnotFirst := frozenSupport_not_mem_of_shiftedFuture_contains
    state.frozenPrefix.1 state.gapToLive future hcontains
  have hnotSecond := frozenSupport_not_mem_of_shiftedFuture_contains
    state.frozenPrefix.2 state.gapToLive future hcontains
  cases collision.origin with
  | firstSecond hold hnew =>
      rcases frozen.firstSupportProvenance collision.face hold with
        holdFirst | hliveFirst
      · exact False.elim (hnotFirst holdFirst)
      · exact .firstSecond hliveFirst hnew
  | secondFirst hold hnew =>
      rcases frozen.secondSupportProvenance collision.face hold with
        holdSecond | hliveSecond
      · exact False.elim (hnotSecond holdSecond)
      · exact .secondFirst hliveSecond hnew

/-- The consumer packet for a retained first-window collision: exact track
origin together with the already constructed component geometry. -/
structure RetainedSharedCollisionFirstWindowRepairPacket
    {firstFinish secondFinish : SelectedFace (web := web)}
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (futureAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish)
    (face : SelectedFace (web := web)) : Prop where
  trackOrigin : RetainedSharedCollisionFirstWindowTrackOrigin
    (firstLeft := firstLeft) futureAssembly face
  component : RetainedSharedCollisionFirstWindowComponentResolution
    (corridor := corridor) (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext) (hfourthNext := hfourthNext)
    (firstLeft := firstLeft) future face

/-- Outcome-level statement that retains the exact cross-track origin on both
newly retained collision branches. -/
def BoundedLiveSharedRailAppendOutcome.HasFirstWindowRepairPacket
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
  | .retainedStraightCollision futureAssembly _ collision
  | .retainedSwappedCollision futureAssembly _ collision =>
      RetainedSharedCollisionFirstWindowRepairPacket
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
        (hlastNext := hlastNext) (hfourthNext := hfourthNext)
        (firstLeft := firstLeft) future futureAssembly collision.face

/-- **L1 bounded repair input.** Every newly retained collision now preserves
its literal cross-track origin while retaining the exact centre/cyclic/star/
bond component resolution.  This is input for endpoint matching, not a repair
claim. -/
theorem BoundedLiveSharedRailAppendTransition.hasFirstWindowRepairPacket
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
    transition.outcome.HasFirstWindowRepairPacket transition.frozen
      transition.common.future := by
  have hcomponent := transition.hasFirstWindowComponentResolution
  cases houtcome : transition.outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | futureCollision collision =>
      rw [houtcome] at hcomponent
      exact hcomponent
  | retainedStraightCollision futureAssembly hfuture collision =>
      rw [houtcome] at hcomponent
      have hcontains :
          transition.common.future.transition.outcome.SuccessfulRailContains
            collision.face := by
        rw [hfuture]
        cases collision.origin with
        | firstSecond hold hnew => exact .inr (List.mem_of_mem_tail hnew)
        | secondFirst hold hnew => exact .inl (List.mem_of_mem_tail hnew)
      exact {
        trackOrigin := collision.firstWindowTrackOrigin_of_sourceTied
          state transition.frozen transition.common.future hcontains
        component := hcomponent
      }
  | retainedSwappedCollision futureAssembly hfuture collision =>
      rw [houtcome] at hcomponent
      have hcontains :
          transition.common.future.transition.outcome.SuccessfulRailContains
            collision.face := by
        rw [hfuture]
        cases collision.origin with
        | firstSecond hold hnew => exact .inr (List.mem_of_mem_tail hnew)
        | secondFirst hold hnew => exact .inl (List.mem_of_mem_tail hnew)
      exact {
        trackOrigin := collision.firstWindowTrackOrigin_of_sourceTied
          state transition.frozen transition.common.future hcontains
        component := hcomponent
      }

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
