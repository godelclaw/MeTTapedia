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
constructed rolling transition.  Thus every unsuccessful shared step returns
bounded source data.  It does not eliminate either bounded collision class,
iterate the rolling step, attach end caps, construct dual crosscuts, or close
Fable flag L1.
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

/-- Every collision branch of a shared-prefix append returns bounded source
data: an exact future collision band or membership in the first live pair. -/
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
      collision.face ∈ firstLeft.toAssembly.firstRail.support ∨
        collision.face ∈ firstLeft.toAssembly.secondRail.support

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
      exact collision.mem_firstLivePair_of_sourceTied state transition.frozen
        transition.common.future hcontains
  | retainedSwappedCollision futureAssembly hfuture collision =>
      have hcontains :
          transition.common.future.transition.outcome.SuccessfulRailContains
            collision.face := by
        rw [hfuture]
        cases collision.origin with
        | firstSecond hold hnew => exact .inr (List.mem_of_mem_tail hnew)
        | secondFirst hold hnew => exact .inl (List.mem_of_mem_tail hnew)
      exact collision.mem_firstLivePair_of_sourceTied state transition.frozen
        transition.common.future hcontains

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
