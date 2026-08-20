import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollision
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleCollisionRepair

/-!
# L1: attach bounded collision data to the shared-prefix step

The shared-prefix classifier has two collision sources.  A collision already
inside the canonical future belongs to the exact four-cell collision-band
table.  A collision created while attaching the older prefix was proved in
the preceding module to lie on the literal first live rail pair rather than
on the arbitrarily long frozen prefix.

This module combines those two facts in one proof-relevant predicate on the
constructed rolling transition.  Exact terminal-window provenance and source
boundary-cleanliness then eliminate the remote last-window alternative: a
new retained collision is confined to the literal three-cell window formed
by the first live pair and the shifted future's first terminal pair.  The
module does not eliminate that remaining first-window class or the internal
four-cell collision bands, iterate the rolling step, attach end caps,
construct dual crosscuts, or close Fable flag L1.
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

private abbrev CurrentState
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)) :=
  BoundedLiveMiddleReplacementState
    (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext)
    (firstPlacement := firstPlacement) (secondPlacement := secondPlacement)
    (thirdPlacement := thirdPlacement) (fourthPlacement := fourthPlacement)
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) prefixAssembly

/-- A collision returned by the shifted future carries one of the exact
four-cell bands, including the stored middle repair when that is the band. -/
theorem ShiftedFutureHasCollision.exists_bandWithMiddleTrace
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (hcollision : ShiftedFutureHasCollision future) :
    ∃ face : SelectedFace (web := web),
      ExactSelectedLocalRailFourCellCollisionBandWithMiddleTrace
        future.transition face := by
  have hband := future.transition.hasCollisionBandWithMiddleTrace hsource
  cases houtcome : future.transition.outcome with
  | straight assembly =>
      simp [ShiftedFutureHasCollision, houtcome] at hcollision
  | swapped assembly =>
      simp [ShiftedFutureHasCollision, houtcome] at hcollision
  | straightStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      unfold ExactSelectedLocalRailTracedFourCellTransition.HasCollisionBandWithMiddleTrace at hband
      rw [houtcome] at hband
      exact ⟨collision.face, hband⟩
  | straightSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      unfold ExactSelectedLocalRailTracedFourCellTransition.HasCollisionBandWithMiddleTrace at hband
      rw [houtcome] at hband
      exact ⟨collision.face, hband⟩
  | swappedStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      unfold ExactSelectedLocalRailTracedFourCellTransition.HasCollisionBandWithMiddleTrace at hband
      rw [houtcome] at hband
      exact ⟨collision.face, hband⟩
  | swappedSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      unfold ExactSelectedLocalRailTracedFourCellTransition.HasCollisionBandWithMiddleTrace at hband
      rw [houtcome] at hband
      exact ⟨collision.face, hband⟩

/-- The exact finite carrier of a collision created by attaching the shared
prefix.  Its old occurrence is on the first live pair; its new occurrence is
in one of the shifted future's two literal terminal windows. -/
inductive RetainedSharedCollisionWindowBand
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (face : SelectedFace (web := web)) : Prop
  | firstWindow
      (firstLive : face ∈ firstLeft.toAssembly.firstRail.support ∨
        face ∈ firstLeft.toAssembly.secondRail.support)
      (futureSupport :
        face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.firstSupport ∨
        face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.secondSupport)
  | lastWindow
      (firstLive : face ∈ firstLeft.toAssembly.firstRail.support ∨
        face ∈ firstLeft.toAssembly.secondRail.support)
      (futureSupport :
        face ∈ future.transition.lastTrace.toExactTerminalWindow.toCertified.firstSupport ∨
        face ∈ future.transition.lastTrace.toExactTerminalWindow.toCertified.secondSupport)

/-- The surviving bounded carrier after remote separation removes the last
terminal window.  Both occurrences now lie in the literal three-cell window
formed by the first live pair and the shifted future's first terminal pair. -/
structure RetainedSharedCollisionFirstWindowData
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    (face : SelectedFace (web := web)) : Prop where
  firstLive : face ∈ firstLeft.toAssembly.firstRail.support ∨
    face ∈ firstLeft.toAssembly.secondRail.support
  futureSupport :
    face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.firstSupport ∨
    face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.secondSupport

/-- A face on the first live pair cannot also occur in the remote last
terminal window of the shifted four-cell future.  The first occurrence is
adjacent to the first centre, while exact terminal-window provenance places
the second occurrence at or adjacent to the fourth or fifth centre.  Source
boundary-cleanliness excludes a common neighbour across that gap. -/
private theorem firstLive_not_mem_shiftedLastWindow
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    {face : SelectedFace (web := web)}
    (hfirst : face ∈ firstLeft.toAssembly.firstRail.support ∨
      face ∈ firstLeft.toAssembly.secondRail.support)
    (hlast :
      face ∈ future.transition.lastTrace.toExactTerminalWindow.toCertified.firstSupport ∨
      face ∈ future.transition.lastTrace.toExactTerminalWindow.toCertified.secondSupport) :
    False := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let fourth :=
    (nextCorridorInterior
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
      hlastNext).center
  let fifth :=
    (nextCorridorInterior
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext)
      hfourthNext).center
  have hfirstAdj : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt firstInterior.center) face := by
    rcases hfirst with hfirst | hfirst
    · exact firstLeft.paths.firstRail_support_adjacent_center face hfirst
    · exact firstLeft.paths.secondRail_support_adjacent_center face hfirst
  have hlastNear : FaceNearSelectedCenterPair (corridor := corridor)
      fourth fifth face := by
    rcases hlast with hlast | hlast
    · exact faceNearSelectedCenterPair_of_mem_adjacentSelectedRailPieces
        (future.transition.lastTrace.toExactTerminalWindow
          |>.firstSupport_in_adjacentPieces face hlast)
    · exact faceNearSelectedCenterPair_of_mem_adjacentSelectedRailPieces
        (future.transition.lastTrace.toExactTerminalWindow
          |>.secondSupport_in_adjacentPieces face hlast)
  rcases hlastNear with hfourth | hfifth | hfourthAdj | hfifthAdj
  · subst face
    exact (skeleton.separated_not_adjacent firstInterior.center fourth
      (by dsimp [fourth]; omega)) hfirstAdj
  · subst face
    exact (skeleton.separated_not_adjacent firstInterior.center fifth
      (by dsimp [fifth]; omega)) hfirstAdj
  · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
      firstInterior.center fourth (by dsimp [fourth]; omega)
      ⟨face, hfirstAdj, hfourthAdj⟩
  · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
      firstInterior.center fifth (by dsimp [fifth]; omega)
      ⟨face, hfirstAdj, hfifthAdj⟩

/-- **L1 remote-band elimination.**  Exact source provenance and the
gap-three boundary-cleanliness theorem remove the shifted future's last
terminal window.  A retained shared-prefix collision is therefore confined
to the first live pair and the shifted future's first terminal window. -/
theorem RetainedSharedCollisionWindowBand.toFirstWindowData
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)}
    {face : SelectedFace (web := web)}
    (band : RetainedSharedCollisionWindowBand
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (firstLeft := firstLeft) future face) :
    RetainedSharedCollisionFirstWindowData
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (firstLeft := firstLeft) future face := by
  cases band with
  | firstWindow firstLive futureSupport => exact ⟨firstLive, futureSupport⟩
  | lastWindow firstLive futureSupport =>
      exact (firstLive_not_mem_shiftedLastWindow hsource future
        firstLive futureSupport).elim

/-- A retained shared-prefix collision is contained in one of two explicit
bounded source windows. -/
theorem RetainedBypassCrossCollision.windowBand_of_sourceTied
    {firstStart secondStart firstFinish secondFinish : SelectedFace (web := web)}
    {prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter)}
    (state : CurrentState
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
    RetainedSharedCollisionWindowBand
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (firstLeft := firstLeft) future collision.face := by
  have hlive := collision.mem_firstLivePair_of_sourceTied state frozen future hcontains
  have hprovenance := future.hasWindowSupportProvenance
  cases houtcome : future.transition.outcome with
  | straight assembly | swapped assembly =>
      rw [houtcome] at hcontains hprovenance
      rcases hcontains with hfirstRail | hsecondRail
      · rcases hprovenance.1 collision.face hfirstRail with
          hfirstFirst | hfirstSecond | hlastFirst | hlastSecond
        · exact .firstWindow hlive (.inl hfirstFirst)
        · exact .firstWindow hlive (.inr hfirstSecond)
        · exact .lastWindow hlive (.inl hlastFirst)
        · exact .lastWindow hlive (.inr hlastSecond)
      · rcases hprovenance.2 collision.face hsecondRail with
          hfirstFirst | hfirstSecond | hlastFirst | hlastSecond
        · exact .firstWindow hlive (.inl hfirstFirst)
        · exact .firstWindow hlive (.inr hfirstSecond)
        · exact .lastWindow hlive (.inl hlastFirst)
        · exact .lastWindow hlive (.inr hlastSecond)
  | straightStraightCollision | straightSwappedCollision |
      swappedStraightCollision | swappedSwappedCollision =>
      rw [houtcome] at hcontains
      exact hcontains.elim

/-- Every collision branch of a shared-prefix append returns bounded source
data: an exact future collision band or the exact first three-cell window. -/
def BoundedLiveSharedRailAppendOutcome.HasLocalizedCollisionData
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
      RetainedSharedCollisionFirstWindowData
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
        (hlastNext := hlastNext) (hfourthNext := hfourthNext)
        (firstLeft := firstLeft) future collision.face

/-- **L1 bounded collision receipt.**  The constructed rolling transition
retains a successful assembly or reduces every failure to bounded source
geometry.  No collision constructor is discharged here. -/
theorem BoundedLiveSharedRailAppendTransition.hasLocalizedCollisionData
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace firstPlacement firstIncomingBefore)
      (selectedPlacementSideFace firstPlacement firstIncomingAfter))
    (state : CurrentState
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
    transition.outcome.HasLocalizedCollisionData transition.frozen
      transition.common.future := by
  cases houtcome : transition.outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | futureCollision hcollision =>
      exact hcollision.exists_bandWithMiddleTrace state.source
        transition.common.future
  | retainedStraightCollision futureAssembly hfuture collision =>
      have hcontains :
          transition.common.future.transition.outcome.SuccessfulRailContains
            collision.face := by
        rw [hfuture]
        cases collision.origin with
        | firstSecond hold hnew => exact .inr (List.mem_of_mem_tail hnew)
        | secondFirst hold hnew => exact .inl (List.mem_of_mem_tail hnew)
      exact (collision.windowBand_of_sourceTied state transition.frozen
        transition.common.future hcontains).toFirstWindowData state.source
  | retainedSwappedCollision futureAssembly hfuture collision =>
      have hcontains :
          transition.common.future.transition.outcome.SuccessfulRailContains
            collision.face := by
        rw [hfuture]
        cases collision.origin with
        | firstSecond hold hnew => exact .inr (List.mem_of_mem_tail hnew)
        | secondFirst hold hnew => exact .inl (List.mem_of_mem_tail hnew)
      exact (collision.windowBand_of_sourceTied state transition.frozen
        transition.common.future hcontains).toFirstWindowData state.source

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
