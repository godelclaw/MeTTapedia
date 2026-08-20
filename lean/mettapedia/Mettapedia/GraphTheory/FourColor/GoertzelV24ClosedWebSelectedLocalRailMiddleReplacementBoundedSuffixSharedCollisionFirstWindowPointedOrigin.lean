import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathPointedOccurrence
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollisionFirstWindowExactTrackOrigin

/-!
# L1: point the future occurrence of a retained shared collision

The exact first-window origin theorem identifies which literal future track
contains a retained collision, and it retains membership in the assembled
future rail's support tail.  This file converts that tail membership into the
position data needed by a later endpoint-triangle comparison: the collision is
either the future rail's terminal endpoint, or it has literal predecessor and
successor vertices on that simple rail.

The terminal alternative is intentionally preserved.  This file does not
identify either neighbour with a square-bond endpoint triangle, construct a
bypass, prove companion-rail separation, iterate the transition, attach end
caps, construct separated crosscuts, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
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

/-- Exact track provenance together with a pointed occurrence on the future
rail.  The terminal case is explicit because tail membership excludes only the
start of a simple path. -/
inductive RetainedSharedCollisionFirstWindowPointedOrigin
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
      (futurePosition : face = secondFinish ∨
        Nonempty (InteriorOccurrence (current := face) futureAssembly.secondRail))
  | secondFirst
      (secondLive : face ∈ firstLeft.toAssembly.secondRail.support)
      (futureFirst : face ∈ futureAssembly.firstRail.support.tail)
      (futureFirstWindowFirst :
        face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.firstSupport)
      (futurePosition : face = firstFinish ∨
        Nonempty (InteriorOccurrence (current := face) futureAssembly.firstRail))

/-- Exact first-window origin canonically yields a pointed occurrence on the
corresponding simple future rail. -/
theorem RetainedSharedCollisionFirstWindowExactTrackOrigin.pointed
    {firstFinish secondFinish : SelectedFace (web := web)}
    {futureAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish}
    {face : SelectedFace (web := web)}
    {future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)}
    (origin : RetainedSharedCollisionFirstWindowExactTrackOrigin
      (firstLeft := firstLeft) future futureAssembly face) :
    RetainedSharedCollisionFirstWindowPointedOrigin
      (firstLeft := firstLeft) future futureAssembly face := by
  cases origin with
  | firstSecond firstLive futureSecond futureFirstWindowSecond =>
      exact .firstSecond firstLive futureSecond futureFirstWindowSecond
        (eq_finish_or_nonempty_interiorOccurrence_of_mem_support_tail
          futureAssembly.secondRail futureAssembly.secondRail_isPath futureSecond)
  | secondFirst secondLive futureFirst futureFirstWindowFirst =>
      exact .secondFirst secondLive futureFirst futureFirstWindowFirst
        (eq_finish_or_nonempty_interiorOccurrence_of_mem_support_tail
          futureAssembly.firstRail futureAssembly.firstRail_isPath futureFirst)

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
