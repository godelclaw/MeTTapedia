import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTracedFourCellTrackSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollisionFirstWindowTrackOrigin

/-!
# L1: exact first-terminal track of a retained shared collision

The first-window repair packet remembers which first-live rail and which
successful future rail contain a retained collision.  Track-sensitive
four-cell provenance now makes that information literal at the future's first
terminal window: old first collides with the future first-window second track,
or old second collides with the future first-window first track.  The remote
last-window alternatives are eliminated by the already proved source
separation theorem.

This is an exact support-origin theorem.  It does not identify predecessor or
successor faces, construct the endpoint-triangle bypass, prove companion-rail
separation after a bypass, iterate the transition, attach end caps, construct
separated crosscuts, or close Fable flag L1.
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

/-- Exact matching tracks on both sides of a newly retained collision.  The
future occurrence stays in the assembled rail's tail while also being placed
on one literal support of the shifted future's first terminal window. -/
inductive RetainedSharedCollisionFirstWindowExactTrackOrigin
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    {firstFinish secondFinish : SelectedFace (web := web)}
    (futureAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish)
    (face : SelectedFace (web := web)) : Prop
  | firstSecond
      (firstLive : face ∈ firstLeft.toAssembly.firstRail.support)
      (futureSecond : face ∈ futureAssembly.secondRail.support.tail)
      (futureFirstWindowSecond :
        face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.secondSupport)
  | secondFirst
      (secondLive : face ∈ firstLeft.toAssembly.secondRail.support)
      (futureFirst : face ∈ futureAssembly.firstRail.support.tail)
      (futureFirstWindowFirst :
        face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.firstSupport)

/-- Outcome-level receipt for the exact future first-window track of each
newly retained prefix/future collision. -/
def BoundedLiveSharedRailAppendOutcome.HasExactFirstWindowTrackOrigin
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
  | .straight _ | .swapped _ | .futureCollision _ => True
  | .retainedStraightCollision futureAssembly _ collision
  | .retainedSwappedCollision futureAssembly _ collision =>
      RetainedSharedCollisionFirstWindowExactTrackOrigin
        (firstLeft := firstLeft) future futureAssembly collision.face

/-- **L1 exact retained-track origin.** Track-sensitive four-cell provenance
and remote terminal-window separation identify the literal first-terminal
track of every newly retained collision. -/
theorem BoundedLiveSharedRailAppendTransition.hasExactFirstWindowTrackOrigin
    {firstStart secondStart : SelectedFace (web := web)}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
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
      (fourthSuccessor := fourthSuccessor) prefixAssembly state)
    (htrack : transition.common.future.transition.outcome
      |>.HasSuccessfulTrackSupportProvenance) :
    transition.outcome.HasExactFirstWindowTrackOrigin transition.frozen
      transition.common.future := by
  have hpacket := transition.hasFirstWindowRepairPacket
  cases houtcome : transition.outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | futureCollision collision => trivial
  | retainedStraightCollision futureAssembly hfuture collision =>
      rw [houtcome] at hpacket
      rw [hfuture] at htrack
      change
        SupportsContainedInOrderedExactTerminalTracks
              transition.common.future.transition.firstTrace.toExactTerminalWindow
              transition.common.future.transition.lastTrace.toExactTerminalWindow
              futureAssembly.firstRail.support futureAssembly.secondRail.support ∨
          SupportsContainedInCrossedExactTerminalTracks
              transition.common.future.transition.firstTrace.toExactTerminalWindow
              transition.common.future.transition.lastTrace.toExactTerminalWindow
              futureAssembly.firstRail.support futureAssembly.secondRail.support
        at htrack
      cases hpacket.trackOrigin with
      | firstSecond firstLive futureSecond =>
          have hfutureSecond := List.mem_of_mem_tail futureSecond
          rcases htrack with hordered | hcrossed
          · rcases hordered.2 collision.face hfutureSecond with hfirst | hlast
            · exact .firstSecond firstLive futureSecond hfirst
            · exact (firstLive_not_mem_shiftedLastWindow hsource
                transition.common.future hpacket.component.sourceData.firstLive
                (.inr hlast)).elim
          · rcases hcrossed.2 collision.face hfutureSecond with hfirst | hlast
            · exact .firstSecond firstLive futureSecond hfirst
            · exact (firstLive_not_mem_shiftedLastWindow hsource
                transition.common.future hpacket.component.sourceData.firstLive
                (.inl hlast)).elim
      | secondFirst secondLive futureFirst =>
          have hfutureFirst := List.mem_of_mem_tail futureFirst
          rcases htrack with hordered | hcrossed
          · rcases hordered.1 collision.face hfutureFirst with hfirst | hlast
            · exact .secondFirst secondLive futureFirst hfirst
            · exact (firstLive_not_mem_shiftedLastWindow hsource
                transition.common.future hpacket.component.sourceData.firstLive
                (.inl hlast)).elim
          · rcases hcrossed.1 collision.face hfutureFirst with hfirst | hlast
            · exact .secondFirst secondLive futureFirst hfirst
            · exact (firstLive_not_mem_shiftedLastWindow hsource
                transition.common.future hpacket.component.sourceData.firstLive
                (.inr hlast)).elim
  | retainedSwappedCollision futureAssembly hfuture collision =>
      rw [houtcome] at hpacket
      rw [hfuture] at htrack
      change
        SupportsContainedInOrderedExactTerminalTracks
              transition.common.future.transition.firstTrace.toExactTerminalWindow
              transition.common.future.transition.lastTrace.toExactTerminalWindow
              futureAssembly.firstRail.support futureAssembly.secondRail.support ∨
          SupportsContainedInCrossedExactTerminalTracks
              transition.common.future.transition.firstTrace.toExactTerminalWindow
              transition.common.future.transition.lastTrace.toExactTerminalWindow
              futureAssembly.firstRail.support futureAssembly.secondRail.support
        at htrack
      cases hpacket.trackOrigin with
      | firstSecond firstLive futureSecond =>
          have hfutureSecond := List.mem_of_mem_tail futureSecond
          rcases htrack with hordered | hcrossed
          · rcases hordered.2 collision.face hfutureSecond with hfirst | hlast
            · exact .firstSecond firstLive futureSecond hfirst
            · exact (firstLive_not_mem_shiftedLastWindow hsource
                transition.common.future hpacket.component.sourceData.firstLive
                (.inr hlast)).elim
          · rcases hcrossed.2 collision.face hfutureSecond with hfirst | hlast
            · exact .firstSecond firstLive futureSecond hfirst
            · exact (firstLive_not_mem_shiftedLastWindow hsource
                transition.common.future hpacket.component.sourceData.firstLive
                (.inl hlast)).elim
      | secondFirst secondLive futureFirst =>
          have hfutureFirst := List.mem_of_mem_tail futureFirst
          rcases htrack with hordered | hcrossed
          · rcases hordered.1 collision.face hfutureFirst with hfirst | hlast
            · exact .secondFirst secondLive futureFirst hfirst
            · exact (firstLive_not_mem_shiftedLastWindow hsource
                transition.common.future hpacket.component.sourceData.firstLive
                (.inl hlast)).elim
          · rcases hcrossed.1 collision.face hfutureFirst with hfirst | hlast
            · exact .secondFirst secondLive futureFirst hfirst
            · exact (firstLive_not_mem_shiftedLastWindow hsource
                transition.common.future hpacket.component.sourceData.firstLive
                (.inr hlast)).elim

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
