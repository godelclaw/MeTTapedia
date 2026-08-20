import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailConstructionTrackProvenance
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTracedCollisionBands

/-!
# L1: exact track origins of canonical four-cell rail collisions

The four broad source-piece bands deliberately forget endpoint parity.  The
canonical construction traces retain more: each output rail has one named old
track and one endpoint-selected successor track, apart from the displayed
centre and two seam flanks.

This module intersects that invariant with the exact cross-origin stored by a
retained collision.  The result has eight constructors: two cross origins for
each of the straight/straight, straight/swapped, swapped/straight, and
swapped/swapped endpoint parities.  Thus the next geometric consumer receives
the actual pair of source tracks which can contain the retained face.

This is a proof-relevant refinement of the collision alternative.  It does
not claim that one of the eight origins is impossible, eliminate a four-cell
collision, construct the rolling transition or end caps, or close Fable flag
L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
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
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      firstPlacement secondPlacement}
    {bridge : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement}
    {lastSuccessor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement}
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions firstPlacement}}
    {firstLeft : SeparatedSelectedSourceLocalRailPaths firstPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

/-- Expected source track in the first canonical two-cell window. -/
def FaceInFirstWindowExpectedTrack
    (oldSupport newSupport : List (SelectedFace (web := web)))
    (face : SelectedFace (web := web)) : Prop :=
  FaceInExpectedSelectedRailTrack (corridor := corridor)
    (leftInterior := firstInterior) (leftPlacement := firstPlacement)
    (successor := firstSuccessor) oldSupport newSupport face

/-- Expected source track in the last canonical two-cell window. -/
def FaceInLastWindowExpectedTrack
    (oldSupport newSupport : List (SelectedFace (web := web)))
    (face : SelectedFace (web := web)) : Prop :=
  FaceInExpectedSelectedRailTrack (corridor := corridor)
    (leftInterior :=
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext))
    (leftPlacement := thirdPlacement) (successor := lastSuccessor)
    oldSupport newSupport face

/-- The eight parity-sensitive source-track origins of a retained collision. -/
inductive ExactSelectedLocalRailFourCellCollisionTrackOrigin
    (face : SelectedFace (web := web)) : Prop
  | straightStraightFirstSecond
      (firstTrack : FaceInFirstWindowExpectedTrack
        (firstSuccessor := firstSuccessor) firstLeft.paths.firstRail.support
        firstSuccessor.firstContinuation.support face)
      (lastTrack : FaceInLastWindowExpectedTrack
        (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (lastSuccessor := lastSuccessor)
        (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.secondRail.support
        lastSuccessor.secondContinuation.support face)
  | straightStraightSecondFirst
      (firstTrack : FaceInFirstWindowExpectedTrack
        (firstSuccessor := firstSuccessor) firstLeft.paths.secondRail.support
        firstSuccessor.secondContinuation.support face)
      (lastTrack : FaceInLastWindowExpectedTrack
        (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (lastSuccessor := lastSuccessor)
        (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.firstRail.support
        lastSuccessor.firstContinuation.support face)
  | straightSwappedFirstSecond
      (firstTrack : FaceInFirstWindowExpectedTrack
        (firstSuccessor := firstSuccessor) firstLeft.paths.firstRail.support
        firstSuccessor.firstContinuation.support face)
      (lastTrack : FaceInLastWindowExpectedTrack
        (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (lastSuccessor := lastSuccessor)
        (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.secondRail.support
        lastSuccessor.firstContinuation.support face)
  | straightSwappedSecondFirst
      (firstTrack : FaceInFirstWindowExpectedTrack
        (firstSuccessor := firstSuccessor) firstLeft.paths.secondRail.support
        firstSuccessor.secondContinuation.support face)
      (lastTrack : FaceInLastWindowExpectedTrack
        (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (lastSuccessor := lastSuccessor)
        (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.firstRail.support
        lastSuccessor.secondContinuation.support face)
  | swappedStraightFirstFirst
      (firstTrack : FaceInFirstWindowExpectedTrack
        (firstSuccessor := firstSuccessor) firstLeft.paths.firstRail.support
        firstSuccessor.secondContinuation.support face)
      (lastTrack : FaceInLastWindowExpectedTrack
        (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (lastSuccessor := lastSuccessor)
        (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.firstRail.support
        lastSuccessor.firstContinuation.support face)
  | swappedStraightSecondSecond
      (firstTrack : FaceInFirstWindowExpectedTrack
        (firstSuccessor := firstSuccessor) firstLeft.paths.secondRail.support
        firstSuccessor.firstContinuation.support face)
      (lastTrack : FaceInLastWindowExpectedTrack
        (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (lastSuccessor := lastSuccessor)
        (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.secondRail.support
        lastSuccessor.secondContinuation.support face)
  | swappedSwappedFirstFirst
      (firstTrack : FaceInFirstWindowExpectedTrack
        (firstSuccessor := firstSuccessor) firstLeft.paths.firstRail.support
        firstSuccessor.secondContinuation.support face)
      (lastTrack : FaceInLastWindowExpectedTrack
        (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (lastSuccessor := lastSuccessor)
        (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.firstRail.support
        lastSuccessor.secondContinuation.support face)
  | swappedSwappedSecondSecond
      (firstTrack : FaceInFirstWindowExpectedTrack
        (firstSuccessor := firstSuccessor) firstLeft.paths.secondRail.support
        firstSuccessor.firstContinuation.support face)
      (lastTrack : FaceInLastWindowExpectedTrack
        (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (lastSuccessor := lastSuccessor)
        (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.secondRail.support
        lastSuccessor.firstContinuation.support face)

/-- Track-origin predicate on the canonical four-cell outcome. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.HasCollisionTrackOrigin
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow) : Prop :=
  match outcome with
  | .straight _ | .swapped _ => True
  | .straightStraightCollision _ _ _ _ collision
  | .straightSwappedCollision _ _ _ _ collision
  | .swappedStraightCollision _ _ _ _ collision
  | .swappedSwappedCollision _ _ _ _ collision =>
      ExactSelectedLocalRailFourCellCollisionTrackOrigin
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) collision.face

/-- **L1 canonical track-origin refinement.** Every bad branch of a traced
four-cell transition exposes one of the eight exact track pairs selected by
its endpoint parity and retained cross origin. -/
theorem ExactSelectedLocalRailTracedFourCellTransition.hasCollisionTrackOrigin
    (transition : ExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)) :
    transition.outcome.HasCollisionTrackOrigin := by
  have hfirst := transition.firstTrace.hasTrackProvenance
  have hlast := transition.lastTrace.hasTrackProvenance
  generalize hout : transition.outcome = outcome at ⊢
  cases outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | straightStraightCollision firstAssembly lastAssembly hfirstEq hlastEq collision =>
      rw [ExactSelectedLocalRailConstructionTrace.HasTrackProvenance] at hfirst hlast
      change transition.firstTrace.toOutcome = .straight firstAssembly at hfirstEq
      change transition.lastTrace.toOutcome = .straight lastAssembly at hlastEq
      rw [hfirstEq] at hfirst
      rw [hlastEq] at hlast
      simp only [SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] at hfirst hlast
      cases collision.origin with
      | firstSecond hold hnew =>
          have hnew' : collision.face ∈ lastAssembly.secondRail.support.tail := by
            simpa using hnew
          exact .straightStraightFirstSecond (hfirst.1 _ hold)
            (hlast.2 _ (List.mem_of_mem_tail hnew'))
      | secondFirst hold hnew =>
          have hnew' : collision.face ∈ lastAssembly.firstRail.support.tail := by
            simpa using hnew
          exact .straightStraightSecondFirst (hfirst.2 _ hold)
            (hlast.1 _ (List.mem_of_mem_tail hnew'))
  | straightSwappedCollision firstAssembly lastAssembly hfirstEq hlastEq collision =>
      rw [ExactSelectedLocalRailConstructionTrace.HasTrackProvenance] at hfirst hlast
      change transition.firstTrace.toOutcome = .straight firstAssembly at hfirstEq
      change transition.lastTrace.toOutcome = .swapped lastAssembly at hlastEq
      rw [hfirstEq] at hfirst
      rw [hlastEq] at hlast
      simp only [SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] at hfirst hlast
      cases collision.origin with
      | firstSecond hold hnew =>
          have hnew' : collision.face ∈ lastAssembly.secondRail.support.tail := by
            simpa using hnew
          exact .straightSwappedFirstSecond (hfirst.1 _ hold)
            (hlast.2 _ (List.mem_of_mem_tail hnew'))
      | secondFirst hold hnew =>
          have hnew' : collision.face ∈ lastAssembly.firstRail.support.tail := by
            simpa using hnew
          exact .straightSwappedSecondFirst (hfirst.2 _ hold)
            (hlast.1 _ (List.mem_of_mem_tail hnew'))
  | swappedStraightCollision firstAssembly lastAssembly hfirstEq hlastEq collision =>
      rw [ExactSelectedLocalRailConstructionTrace.HasTrackProvenance] at hfirst hlast
      change transition.firstTrace.toOutcome = .swapped firstAssembly at hfirstEq
      change transition.lastTrace.toOutcome = .straight lastAssembly at hlastEq
      rw [hfirstEq] at hfirst
      rw [hlastEq] at hlast
      simp only [SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] at hfirst hlast
      cases collision.origin with
      | firstFirst hold hnew =>
          have hnew' : collision.face ∈ lastAssembly.firstRail.support.tail := by
            simpa using hnew
          exact .swappedStraightFirstFirst (hfirst.1 _ hold)
            (hlast.1 _ (List.mem_of_mem_tail hnew'))
      | secondSecond hold hnew =>
          have hnew' : collision.face ∈ lastAssembly.secondRail.support.tail := by
            simpa using hnew
          exact .swappedStraightSecondSecond (hfirst.2 _ hold)
            (hlast.2 _ (List.mem_of_mem_tail hnew'))
  | swappedSwappedCollision firstAssembly lastAssembly hfirstEq hlastEq collision =>
      rw [ExactSelectedLocalRailConstructionTrace.HasTrackProvenance] at hfirst hlast
      change transition.firstTrace.toOutcome = .swapped firstAssembly at hfirstEq
      change transition.lastTrace.toOutcome = .swapped lastAssembly at hlastEq
      rw [hfirstEq] at hfirst
      rw [hlastEq] at hlast
      simp only [SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance] at hfirst hlast
      cases collision.origin with
      | firstFirst hold hnew =>
          have hnew' : collision.face ∈ lastAssembly.firstRail.support.tail := by
            simpa using hnew
          exact .swappedSwappedFirstFirst (hfirst.1 _ hold)
            (hlast.1 _ (List.mem_of_mem_tail hnew'))
      | secondSecond hold hnew =>
          have hnew' : collision.face ∈ lastAssembly.secondRail.support.tail := by
            simpa using hnew
          exact .swappedSwappedSecondSecond (hfirst.2 _ hold)
            (hlast.2 _ (List.mem_of_mem_tail hnew'))

/-- The same packet retains the canonical finite repair at the middle seam
where the four-cell collision is detected. -/
theorem ExactSelectedLocalRailTracedFourCellTransition.bridgeHasTrackProvenance
    (transition : ExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)) :
    transition.bridgeTrace.HasTrackProvenance :=
  transition.bridgeTrace.hasTrackProvenance

/-- The first successor track of the first window is definitionally the first
old track presented to the middle-seam classifier, modulo the endpoint casts
stored by successor compatibility. -/
theorem firstContinuation_support_eq_bridgeLeft_firstRail_support :
    firstSuccessor.firstContinuation.support =
      (firstSuccessor.rightRailsAsNextLeft bridge).paths.firstRail.support := by
  rw [firstSuccessor.firstContinuation_support]
  exact (firstSuccessor.rightRailsAsNextLeft_firstRail_support bridge).symm

/-- The same identification for the second track. -/
theorem secondContinuation_support_eq_bridgeLeft_secondRail_support :
    firstSuccessor.secondContinuation.support =
      (firstSuccessor.rightRailsAsNextLeft bridge).paths.secondRail.support := by
  rw [firstSuccessor.secondContinuation_support]
  exact (firstSuccessor.rightRailsAsNextLeft_secondRail_support bridge).symm

/-- The first successor track produced at the middle seam is the first old
track of the last window. -/
theorem bridge_firstContinuation_support_eq_lastLeft_firstRail_support :
    bridge.firstContinuation.support =
      (bridge.rightRailsAsNextLeft lastSuccessor).paths.firstRail.support := by
  rw [bridge.firstContinuation_support]
  exact (bridge.rightRailsAsNextLeft_firstRail_support lastSuccessor).symm

/-- The corresponding middle/last identification on the second track. -/
theorem bridge_secondContinuation_support_eq_lastLeft_secondRail_support :
    bridge.secondContinuation.support =
      (bridge.rightRailsAsNextLeft lastSuccessor).paths.secondRail.support := by
  rw [bridge.secondContinuation_support]
  exact (bridge.rightRailsAsNextLeft_secondRail_support lastSuccessor).symm

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
