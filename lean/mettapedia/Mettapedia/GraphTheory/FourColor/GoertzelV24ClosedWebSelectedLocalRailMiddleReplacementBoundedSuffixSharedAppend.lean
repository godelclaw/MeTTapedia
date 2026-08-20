import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedPrefix

/-!
# L1: append the frozen shared-cut prefix to the common future span

The bounded rolling construction now has two independently constructed
pieces with definitionally matching endpoints: a prefix frozen immediately
before the rail shared by consecutive local traces, and the canonical
four-cell transition beginning at that rail.  This module runs the retained
support classifier which joins those pieces.

Both successful endpoint orders remain explicit.  A collision inside the
four-cell transition remains the exact source-local collision already stored
by that transition; a collision created by attaching the older prefix retains
the corresponding retained-support witness.  Thus this is a fail-closed
prefix-to-future classifier, not an assumption that the append succeeds.

This is one bounded rolling append.  It does not eliminate either collision
class, iterate to arbitrary corridor length, attach the two end caps, construct
dual crosscuts, or close Fable flag L1.
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

/-- The canonical future returned one of its four exact retained-collision
branches.  The outcome itself still carries the complete witness. -/
def ShiftedFutureHasCollision (future : ShiftedFuture
    (firstInterior := firstInterior) (hfirstNext := hfirstNext)
    (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
    (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
    (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
    (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
    (firstSuccessor := firstSuccessor) (bridge := bridge)
    (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)) : Prop :=
  match future.transition.outcome with
  | .straight _ | .swapped _ => False
  | .straightStraightCollision _ _ _ _ _
  | .straightSwappedCollision _ _ _ _ _
  | .swappedStraightCollision _ _ _ _ _
  | .swappedSwappedCollision _ _ _ _ _ => True

/-- Result of attaching the prefix cut before the shared rail to the canonical
common future.  The last two constructors retain collisions created by this
new attachment; `futureCollision` leaves the exact collision in `future`.
-/
inductive BoundedLiveSharedRailAppendOutcome
    {firstStart secondStart : SelectedFace (web := web)}
    (frozen : BoundedLiveSharedRailPrefix
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (firstSuccessor := firstSuccessor)
      (firstStart := firstStart) (secondStart := secondStart))
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)) :
    Type (u + 1)
  | straight
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart
        (selectedPlacementSideFace fifthPlacement
          fourthSuccessor.rightOutgoingBefore)
        (selectedPlacementSideFace fifthPlacement
          fourthSuccessor.rightOutgoingAfter))
  | swapped
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart
        (selectedPlacementSideFace fifthPlacement
          fourthSuccessor.rightOutgoingAfter)
        (selectedPlacementSideFace fifthPlacement
          fourthSuccessor.rightOutgoingBefore))
  | futureCollision (collision : ShiftedFutureHasCollision future)
  | retainedStraightCollision
      (futureAssembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
        (selectedPlacementSideFace fifthPlacement
          fourthSuccessor.rightOutgoingBefore)
        (selectedPlacementSideFace fifthPlacement
          fourthSuccessor.rightOutgoingAfter))
      (hfuture : future.transition.outcome = .straight futureAssembly)
      (collision : RetainedBypassCrossCollision frozen.assembly futureAssembly)
  | retainedSwappedCollision
      (futureAssembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
        (selectedPlacementSideFace fifthPlacement
          fourthSuccessor.rightOutgoingAfter)
        (selectedPlacementSideFace fifthPlacement
          fourthSuccessor.rightOutgoingBefore))
      (hfuture : future.transition.outcome = .swapped futureAssembly)
      (collision : RetainedBypassCrossCollision frozen.assembly futureAssembly)

/-- **L1 fail-closed shared-prefix append.** Classify the supports which
survive loop erasure when the constructed frozen prefix is joined to the
constructed common future. -/
noncomputable def classifyBoundedLiveSharedRailAppend
    {firstStart secondStart : SelectedFace (web := web)}
    (frozen : BoundedLiveSharedRailPrefix
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (firstSuccessor := firstSuccessor)
      (firstStart := firstStart) (secondStart := secondStart))
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)) :
    BoundedLiveSharedRailAppendOutcome frozen future := by
  cases hfuture : future.transition.outcome with
  | straight futureAssembly =>
      cases happend : classifyRetainedBypassAppend frozen.assembly futureAssembly with
      | assembled assembly => exact .straight assembly
      | collision collision =>
          exact .retainedStraightCollision futureAssembly hfuture collision
  | swapped futureAssembly =>
      cases happend : classifyRetainedBypassAppend frozen.assembly futureAssembly with
      | assembled assembly => exact .swapped assembly
      | collision collision =>
          exact .retainedSwappedCollision futureAssembly hfuture collision
  | straightStraightCollision => exact .futureCollision (by simp [ShiftedFutureHasCollision, hfuture])
  | straightSwappedCollision => exact .futureCollision (by simp [ShiftedFutureHasCollision, hfuture])
  | swappedStraightCollision => exact .futureCollision (by simp [ShiftedFutureHasCollision, hfuture])
  | swappedSwappedCollision => exact .futureCollision (by simp [ShiftedFutureHasCollision, hfuture])

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

/-- The canonical shared-cut prefix selected from an actual bounded rolling
state.  Its existence theorem performs the source-gap append; this definition
only fixes that witness for the proof-relevant transition packet below. -/
noncomputable def boundedLiveSharedRailPrefixOfState
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
      prefixAssembly) :
    BoundedLiveSharedRailPrefix
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (firstSuccessor := firstSuccessor)
      (firstStart := firstStart) (secondStart := secondStart) :=
  Classical.choice (boundedLiveSharedRailPrefix_nonempty_ofState
    prefixAssembly state)

/-- A proof-relevant bounded rolling step assembled entirely from the stored
state and the actual source classifiers.  The equalities prevent later users
from replacing any of its three computations by an arbitrary inhabitant with
the same endpoint types. -/
structure BoundedLiveSharedRailAppendTransition
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
      prefixAssembly) where
  frozen : BoundedLiveSharedRailPrefix
    (corridor := corridor) (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (firstPlacement := firstPlacement)
    (secondPlacement := secondPlacement) (firstSuccessor := firstSuccessor)
    (firstStart := firstStart) (secondStart := secondStart)
  frozen_eq : frozen = boundedLiveSharedRailPrefixOfState prefixAssembly state
  common : BoundedLiveCommonSpanTransition
    (lastSuccessor := lastSuccessor)
    (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
    (fourthSuccessor := fourthSuccessor) state.source state.liveTraces
  common_eq : common = BoundedLiveCommonSpanTransition.ofClassifiers
    (lastSuccessor := lastSuccessor)
    (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
    (fourthSuccessor := fourthSuccessor) state.source state.liveTraces
  outcome : BoundedLiveSharedRailAppendOutcome frozen common.future
  outcome_eq : outcome = classifyBoundedLiveSharedRailAppend frozen common.future

/-- **L1 constructed bounded shared step.** Select the proved shared-cut
prefix, run the actual common-span future classifiers, and classify their
retained append.  Every collision branch remains in `outcome`. -/
noncomputable def BoundedLiveSharedRailAppendTransition.ofState
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
      prefixAssembly) :
    BoundedLiveSharedRailAppendTransition
      (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
      (fourthSuccessor := fourthSuccessor) prefixAssembly state := by
  let frozen := boundedLiveSharedRailPrefixOfState prefixAssembly state
  let common := BoundedLiveCommonSpanTransition.ofClassifiers
    (lastSuccessor := lastSuccessor)
    (hfourthNext := hfourthNext) (fifthPlacement := fifthPlacement)
    (fourthSuccessor := fourthSuccessor) state.source state.liveTraces
  let outcome := classifyBoundedLiveSharedRailAppend frozen common.future
  exact
    { frozen := frozen
      frozen_eq := rfl
      common := common
      common_eq := rfl
      outcome := outcome
      outcome_eq := rfl }

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
