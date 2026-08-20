import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedAppend

/-!
# L1: localize collisions in the shared-prefix append

The shared-prefix append may still return a retained collision between the
accumulated prefix and a successful common future.  The source provenance
stored in the stronger prefix packet separates the two possible origins of
such a face.  If it came from the arbitrarily large old prefix, the rolling
state's frozen-support invariant contradicts the future transition's exact
terminal-window provenance.  Hence every surviving prefix/future collision
comes from the literal first live rail pair.

This turns an unbounded-prefix collision into bounded source geometry.  It
does not eliminate that local collision, consume a collision already returned
inside the four-cell future, iterate the rolling step, attach end caps, or
close Fable flag L1.
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

private abbrev FourthInterior :=
  nextCorridorInterior
    (nextCorridorInterior
      (nextCorridorInterior firstInterior hfirstNext) hbridgeNext) hlastNext

/-- A support frozen before the live suffix cannot contain a face on a
successful shifted future rail.  The singleton support exposes exactly which
of the two terminal windows supplies the contradiction. -/
theorem frozenSupport_not_mem_of_shiftedFuture_contains
    {cutoff : Nat} {support : List (SelectedFace (web := web))}
    (hfrozen : SupportSeparatedFromFutureSelectedWindows
      (corridor := corridor) cutoff support)
    (hgapToLive : cutoff + 3 < firstInterior.center.val)
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    {face : SelectedFace (web := web)}
    (hcontains : future.transition.outcome.SuccessfulRailContains face) :
    face ∉ support := by
  have hnear :=
    future.transition.outcome.faceNearTerminalCenterPairs_of_contains
      future.hasWindowSupportProvenance hcontains
  intro hsupport
  rcases hnear with hfirstWindow | hlastWindow
  · have hdisjoint := hfrozen (futureInterior :=
        nextCorridorInterior firstInterior hfirstNext)
      (hfutureNext := hbridgeNext) [face] (by
        intro other hother
        simp only [List.mem_singleton] at hother
        subst other
        exact hfirstWindow) (by
        have hgap := hgapToLive
        change cutoff + 3 < firstInterior.center.val + 1
        omega)
    exact (List.disjoint_left.mp hdisjoint hsupport) (by simp)
  · have hdisjoint := hfrozen
      (futureInterior := FourthInterior
        (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
      (hfutureNext := hfourthNext) [face] (by
        intro other hother
        simp only [List.mem_singleton] at hother
        subst other
        exact hlastWindow) (by
        have hgap := hgapToLive
        change cutoff + 3 < firstInterior.center.val + 3
        omega)
    exact (List.disjoint_left.mp hdisjoint hsupport) (by simp)

/-- A retained collision created by attaching the shared prefix is supported
on the literal first live pair, never solely in the unbounded old prefix. -/
theorem RetainedBypassCrossCollision.mem_firstLivePair_of_sourceTied
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
    collision.face ∈ firstLeft.toAssembly.firstRail.support ∨
      collision.face ∈ firstLeft.toAssembly.secondRail.support := by
  have hnotFirst := frozenSupport_not_mem_of_shiftedFuture_contains
    state.frozenPrefix.1 state.gapToLive future hcontains
  have hnotSecond := frozenSupport_not_mem_of_shiftedFuture_contains
    state.frozenPrefix.2 state.gapToLive future hcontains
  cases collision.origin with
  | firstSecond hold hnew =>
      rcases frozen.firstSupportProvenance collision.face hold with
        holdFirst | hliveFirst
      · exact False.elim (hnotFirst holdFirst)
      · exact .inl hliveFirst
  | secondFirst hold hnew =>
      rcases frozen.secondSupportProvenance collision.face hold with
        holdSecond | hliveSecond
      · exact False.elim (hnotSecond holdSecond)
      · exact .inr hliveSecond

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
