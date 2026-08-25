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

private theorem mem_support_eq_start_or_mem_tail
    {F : Type*} {H : SimpleGraph F} {start finish face : F}
    (walk : H.Walk start finish) (hface : face ∈ walk.support) :
    face = start ∨ face ∈ walk.support.tail := by
  rw [← walk.cons_tail_support] at hface
  exact List.mem_cons.mp hface

/-- A full-support contact across the middle seam is either an actual append
collision (strictly after the shared endpoint) or one of the two legal shared
seam faces. -/
inductive MiddleSeamTrackContact (face : SelectedFace (web := web)) : Prop
  | collision
      (value : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision bridge
        (firstSuccessor.rightRailsAsNextLeft bridge))
      (face_eq : value.face = face)
  | firstEndpoint
      (face_eq : face = selectedPlacementSideFace secondPlacement
        bridge.frame.leftBefore)
  | secondEndpoint
      (face_eq : face = selectedPlacementSideFace secondPlacement
        bridge.frame.leftAfter)

/-- The `successor/old` broad collision band is precisely middle-seam contact.
The only part not consumed by the append classifier is its two shared
endpoints. -/
theorem middleSeamTrackContact_of_successorOld
    {face : SelectedFace (web := web)}
    (firstSuccessorPiece : face ∈ firstSuccessor.firstContinuation.support ∨
      face ∈ firstSuccessor.secondContinuation.support)
    (lastOld : face ∈
        (bridge.rightRailsAsNextLeft lastSuccessor).paths.firstRail.support ∨
      face ∈
        (bridge.rightRailsAsNextLeft lastSuccessor).paths.secondRail.support) :
    MiddleSeamTrackContact (firstSuccessor := firstSuccessor)
      (bridge := bridge) face := by
  have hleft : face ∈
        (firstSuccessor.rightRailsAsNextLeft bridge).paths.firstRail.support ∨
      face ∈
        (firstSuccessor.rightRailsAsNextLeft bridge).paths.secondRail.support := by
    rcases firstSuccessorPiece with hfirst | hsecond
    · exact Or.inl (by
        rw [← firstContinuation_support_eq_bridgeLeft_firstRail_support]
        exact hfirst)
    · exact Or.inr (by
        rw [← secondContinuation_support_eq_bridgeLeft_secondRail_support]
        exact hsecond)
  have hright : face ∈ bridge.firstContinuation.support ∨
      face ∈ bridge.secondContinuation.support := by
    rcases lastOld with hfirst | hsecond
    · exact Or.inl (by
        rw [bridge_firstContinuation_support_eq_lastLeft_firstRail_support]
        exact hfirst)
    · exact Or.inr (by
        rw [bridge_secondContinuation_support_eq_lastLeft_secondRail_support]
        exact hsecond)
  rcases hleft with hleftFirst | hleftSecond
  · rcases hright with hrightFirst | hrightSecond
    · rcases mem_support_eq_start_or_mem_tail bridge.firstContinuation
          hrightFirst with hstart | htail
      · exact .firstEndpoint hstart
      · exact .collision
          ⟨face, Or.inl ⟨hleftFirst, htail⟩⟩ rfl
    · rcases mem_support_eq_start_or_mem_tail bridge.secondContinuation
          hrightSecond with hstart | htail
      · exact .secondEndpoint hstart
      · exact .collision
          ⟨face, Or.inr (Or.inr (Or.inl ⟨hleftFirst, htail⟩))⟩ rfl
  · rcases hright with hrightFirst | hrightSecond
    · rcases mem_support_eq_start_or_mem_tail bridge.firstContinuation
          hrightFirst with hstart | htail
      · exact .firstEndpoint hstart
      · exact .collision
          ⟨face, Or.inr (Or.inr (Or.inr ⟨hleftSecond, htail⟩))⟩ rfl
    · rcases mem_support_eq_start_or_mem_tail bridge.secondContinuation
          hrightSecond with hstart | htail
      · exact .secondEndpoint hstart
      · exact .collision
          ⟨face, Or.inr (Or.inl ⟨hleftSecond, htail⟩)⟩ rfl

private theorem ne_middleBefore_of_ne_firstOutgoingBefore
    {face : SelectedFace (web := web)}
    (hne : face ≠ selectedPlacementSideFace secondPlacement
      firstSuccessor.rightOutgoingBefore) :
    face ≠ selectedPlacementSideFace secondPlacement bridge.frame.leftBefore := by
  intro hface
  apply hne
  exact hface.trans (congrArg
    (fun position => selectedPlacementSideFace secondPlacement position)
    (firstSuccessor.rightOutgoingBefore_eq_nextLeftBefore bridge).symm)

private theorem ne_middleAfter_of_ne_firstOutgoingAfter
    {face : SelectedFace (web := web)}
    (hne : face ≠ selectedPlacementSideFace secondPlacement
      firstSuccessor.rightOutgoingAfter) :
    face ≠ selectedPlacementSideFace secondPlacement bridge.frame.leftAfter := by
  intro hface
  apply hne
  exact hface.trans (congrArg
    (fun position => selectedPlacementSideFace secondPlacement position)
    (firstSuccessor.rightOutgoingAfter_eq_nextLeftAfter bridge).symm)

/-- Collision branches returned by the retained four-cell classifier cannot
occur at either legal shared endpoint of the middle seam.  This is a path and
mutual-support fact, independent of the corridor geometry. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.CollisionFaceAvoidsMiddleSeamEndpoints
    {firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft}
    {lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))}
    (outcome : ExactSelectedLocalRailFourCellRetainedOutcome
      firstWindow lastWindow) : Prop :=
  match outcome with
  | .straight _ | .swapped _ => True
  | .straightStraightCollision _ _ _ _ collision
  | .straightSwappedCollision _ _ _ _ collision =>
      collision.face ≠ selectedPlacementSideFace secondPlacement
          bridge.frame.leftBefore ∧
        collision.face ≠ selectedPlacementSideFace secondPlacement
          bridge.frame.leftAfter
  | .swappedStraightCollision _ _ _ _ collision
  | .swappedSwappedCollision _ _ _ _ collision =>
      collision.face ≠ selectedPlacementSideFace secondPlacement
          bridge.frame.leftBefore ∧
        collision.face ≠ selectedPlacementSideFace secondPlacement
          bridge.frame.leftAfter

/-- Every bad retained outcome avoids the two middle-seam endpoints. -/
theorem ExactSelectedLocalRailTracedFourCellTransition.collisionFaceAvoidsMiddleSeamEndpoints
    (transition : ExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)) :
    transition.outcome.CollisionFaceAvoidsMiddleSeamEndpoints := by
  generalize hout : transition.outcome = outcome at ⊢
  cases outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | straightStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact ⟨ne_middleBefore_of_ne_firstOutgoingBefore
          collision.face_ne_newFirstStart,
        ne_middleAfter_of_ne_firstOutgoingAfter
          collision.face_ne_newSecondStart⟩
  | straightSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact ⟨ne_middleBefore_of_ne_firstOutgoingBefore
          collision.face_ne_newFirstStart,
        ne_middleAfter_of_ne_firstOutgoingAfter
          collision.face_ne_newSecondStart⟩
  | swappedStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact ⟨ne_middleBefore_of_ne_firstOutgoingBefore
          collision.face_ne_newFirstStart,
        ne_middleAfter_of_ne_firstOutgoingAfter
          collision.face_ne_newSecondStart⟩
  | swappedSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact ⟨ne_middleBefore_of_ne_firstOutgoingBefore
          collision.face_ne_newFirstStart,
        ne_middleAfter_of_ne_firstOutgoingAfter
          collision.face_ne_newSecondStart⟩

/-- The collision bands after consuming the middle `successor/old` overlap.
That band is replaced by an actual collision in the canonical middle-seam
append classifier; the other three bands are retained verbatim. -/
inductive ExactSelectedLocalRailFourCellCollisionBandAfterMiddleSeam
    (face : SelectedFace (web := web)) : Prop
  | oldOld
      (firstOld : face ∈ firstLeft.paths.firstRail.support ∨
        face ∈ firstLeft.paths.secondRail.support)
      (lastOld : face ∈
          (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.firstRail.support ∨
        face ∈
          (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.secondRail.support)
  | successorThirdCenter
      (firstSuccessorPiece : face ∈ firstSuccessor.firstContinuation.support ∨
        face ∈ firstSuccessor.secondContinuation.support)
      (atThirdCenter : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
  | middleCollision
      (value : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision bridge
        (firstSuccessor.rightRailsAsNextLeft bridge))
      (face_eq : value.face = face)
  | successorSuccessor
      (firstSuccessorPiece : face ∈ firstSuccessor.firstContinuation.support ∨
        face ∈ firstSuccessor.secondContinuation.support)
      (lastSuccessorPiece : face ∈ lastSuccessor.firstContinuation.support ∨
        face ∈ lastSuccessor.secondContinuation.support)

/-- Endpoint exclusion turns the broad middle `successor/old` band into a
literal append collision. -/
theorem collisionBandAfterMiddleSeam_of_collisionBand
    {face : SelectedFace (web := web)}
    (hband : ExactSelectedLocalRailFourCellCollisionBand
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face)
    (hneBefore : face ≠ selectedPlacementSideFace secondPlacement
      bridge.frame.leftBefore)
    (hneAfter : face ≠ selectedPlacementSideFace secondPlacement
      bridge.frame.leftAfter) :
    ExactSelectedLocalRailFourCellCollisionBandAfterMiddleSeam
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face := by
  cases hband with
  | oldOld firstOld lastOld => exact .oldOld firstOld lastOld
  | successorThirdCenter firstSuccessorPiece atThirdCenter =>
      exact .successorThirdCenter firstSuccessorPiece atThirdCenter
  | successorSuccessor firstSuccessorPiece lastSuccessorPiece =>
      exact .successorSuccessor firstSuccessorPiece lastSuccessorPiece
  | successorOld firstSuccessorPiece lastOld =>
      cases middleSeamTrackContact_of_successorOld firstSuccessorPiece lastOld with
      | collision value face_eq => exact .middleCollision value face_eq
      | firstEndpoint face_eq => exact False.elim (hneBefore face_eq)
      | secondEndpoint face_eq => exact False.elim (hneAfter face_eq)

/-- Reduced collision-band predicate on a canonical outcome. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.HasCollisionBandAfterMiddleSeam
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
      ExactSelectedLocalRailFourCellCollisionBandAfterMiddleSeam
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) collision.face

/-- **L1 middle-seam band reduction.** The canonical four-cell transition has
only three untouched remote bands or an actual collision already classified
by the stored middle repair. -/
theorem ExactSelectedLocalRailTracedFourCellTransition.hasCollisionBandAfterMiddleSeam
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (transition : ExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)) :
    transition.outcome.HasCollisionBandAfterMiddleSeam := by
  have hband := transition.hasCollisionBandData hsource
  have haway := transition.collisionFaceAvoidsMiddleSeamEndpoints
  generalize hout : transition.outcome = outcome at hband haway ⊢
  cases outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | straightStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact collisionBandAfterMiddleSeam_of_collisionBand hband haway.1 haway.2
  | straightSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact collisionBandAfterMiddleSeam_of_collisionBand hband haway.1 haway.2
  | swappedStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact collisionBandAfterMiddleSeam_of_collisionBand hband haway.1 haway.2
  | swappedSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact collisionBandAfterMiddleSeam_of_collisionBand hband haway.1 haway.2

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
