import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTracedCollisionTrackOrigins

/-!
# L1: relate the middle-seam collision to its canonical repair

The reduced four-cell collision table contains one branch which is already an
actual append collision for the middle two-cell window.  The collision witness
was selected by the outer four-cell classifier, whereas the stored middle
construction trace was selected independently by the canonical adjacent
classifier.  Equality of those two choices is neither available nor needed.

The canonical middle trace returns a concrete separated assembly.  Hence, for
the particular face named by the outer collision, at least one of its two
output rails avoids that face.  Moreover, the triangle inequalities exclude
all connector alternatives in the general track-provenance predicate, so any
remaining occurrence of that face lies on one of the two literal source
tracks.  This module records both facts in the four-cell collision table.

This is a constructed refinement of the middle band.  It does not yet reroute
the outer four-cell collision, eliminate the other three bounded bands, perform
the arbitrary-length fold, attach either end cap, or close Fable flag L1.
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
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- A concrete complete adjacent repair avoids a specified face on at least
one of its two mutually disjoint output rails. -/
def SelectedLocalRailAppendCompleteOutcome.AvoidsFaceOnOneRail
    (outcome : SelectedLocalRailAppendCompleteOutcome successor left)
    (face : SelectedFace (web := web)) : Prop :=
  match outcome with
  | .straight assembly | .swapped assembly =>
      face ∉ assembly.firstRail.support ∨
        face ∉ assembly.secondRail.support

/-- Mutual rail separation turns every concrete adjacent result into a
face-by-face avoidance certificate. -/
theorem SelectedLocalRailAppendCompleteOutcome.avoidsFaceOnOneRail
    (outcome : SelectedLocalRailAppendCompleteOutcome successor left)
    (face : SelectedFace (web := web)) :
    outcome.AvoidsFaceOnOneRail face := by
  cases outcome with
  | straight assembly | swapped assembly =>
      by_cases hfirst : face ∈ assembly.firstRail.support
      · exact Or.inr (fun hsecond =>
          (List.disjoint_left.mp
            assembly.firstRail_support_disjoint_secondRail hfirst) hsecond)
      · exact Or.inl hfirst

/-- The actual canonical trace resolves any independently selected collision
face in the only sense needed here: its concrete output has a clear rail at
that face.  No equality between collision-choice functions is assumed. -/
theorem ExactSelectedLocalRailConstructionTrace.avoidsActualCollisionFaceOnOneRail
    (trace : ExactSelectedLocalRailConstructionTrace successor left)
    (collision :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left) :
    trace.toOutcome.AvoidsFaceOnOneRail collision.face :=
  trace.toOutcome.avoidsFaceOnOneRail collision.face

/-- An actual collision face is not the displayed centre of its left Cell--3
piece. -/
theorem actualAppendCollision_face_ne_leftCenter
    (collision :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left) :
    collision.face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center :=
  collision.toAdjacentDualTriangle.leftCenter_adj_third.ne.symm

/-- At an actual collision face the three connector alternatives in the
track-provenance predicate are impossible. -/
theorem actualAppendCollision_faceInExpectedTrack_iff
    (collision :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left)
    (oldSupport newSupport : List (SelectedFace (web := web))) :
    FaceInExpectedSelectedRailTrack (corridor := corridor)
        (leftInterior := leftInterior) (leftPlacement := leftPlacement)
        (successor := successor) oldSupport newSupport collision.face ↔
      collision.face ∈ oldSupport ∨ collision.face ∈ newSupport := by
  simp only [FaceInExpectedSelectedRailTrack]
  constructor
  · intro hface
    rcases hface with hold | hnew | hcenter | hbefore | hafter
    · exact Or.inl hold
    · exact Or.inr hnew
    · exact False.elim
        (actualAppendCollision_face_ne_leftCenter collision hcenter)
    · exact False.elim
        (collision.toAdjacentDualTriangle.third_ne_before hbefore)
    · exact False.elim
        (collision.toAdjacentDualTriangle.third_ne_after hafter)
  · exact fun hface => hface.elim Or.inl (fun hnew => Or.inr (Or.inl hnew))

/-- Track membership of one specified actual collision face in a concrete
canonical repair.  Unlike the general provenance predicate, this statement
contains no connector-face alternatives. -/
def SelectedLocalRailAppendCompleteOutcome.CollisionFaceFollowsExpectedTracks
    (outcome : SelectedLocalRailAppendCompleteOutcome successor left)
    (collision :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left) : Prop :=
  match outcome with
  | .straight assembly =>
      (∀ _hface : collision.face ∈ assembly.firstRail.support,
          collision.face ∈ left.paths.firstRail.support ∨
            collision.face ∈ successor.firstContinuation.support) ∧
        ∀ _hface : collision.face ∈ assembly.secondRail.support,
          collision.face ∈ left.paths.secondRail.support ∨
            collision.face ∈ successor.secondContinuation.support
  | .swapped assembly =>
      (∀ _hface : collision.face ∈ assembly.firstRail.support,
          collision.face ∈ left.paths.firstRail.support ∨
            collision.face ∈ successor.secondContinuation.support) ∧
        ∀ _hface : collision.face ∈ assembly.secondRail.support,
          collision.face ∈ left.paths.secondRail.support ∨
            collision.face ∈ successor.firstContinuation.support

/-- The stored canonical construction branch gives exact, connector-free
track membership for any independently selected actual collision face. -/
theorem ExactSelectedLocalRailConstructionTrace.collisionFaceFollowsExpectedTracks
    (trace : ExactSelectedLocalRailConstructionTrace successor left)
    (collision :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left) :
    trace.toOutcome.CollisionFaceFollowsExpectedTracks collision := by
  have htrack := trace.hasTrackProvenance
  cases hresult : trace.toOutcome with
  | straight assembly =>
      rw [ExactSelectedLocalRailConstructionTrace.HasTrackProvenance,
        hresult, SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance]
        at htrack
      change
        (∀ hface : collision.face ∈ assembly.firstRail.support,
            collision.face ∈ left.paths.firstRail.support ∨
              collision.face ∈ successor.firstContinuation.support) ∧
          ∀ hface : collision.face ∈ assembly.secondRail.support,
            collision.face ∈ left.paths.secondRail.support ∨
              collision.face ∈ successor.secondContinuation.support
      constructor
      · intro hface
        exact (actualAppendCollision_faceInExpectedTrack_iff collision
          left.paths.firstRail.support
          successor.firstContinuation.support).mp
            (htrack.1 collision.face hface)
      · intro hface
        exact (actualAppendCollision_faceInExpectedTrack_iff collision
          left.paths.secondRail.support
          successor.secondContinuation.support).mp
            (htrack.2 collision.face hface)
  | swapped assembly =>
      rw [ExactSelectedLocalRailConstructionTrace.HasTrackProvenance,
        hresult, SelectedLocalRailAppendCompleteOutcome.HasTrackProvenance]
        at htrack
      change
        (∀ hface : collision.face ∈ assembly.firstRail.support,
            collision.face ∈ left.paths.firstRail.support ∨
              collision.face ∈ successor.secondContinuation.support) ∧
          ∀ hface : collision.face ∈ assembly.secondRail.support,
            collision.face ∈ left.paths.secondRail.support ∨
              collision.face ∈ successor.firstContinuation.support
      constructor
      · intro hface
        exact (actualAppendCollision_faceInExpectedTrack_iff collision
          left.paths.firstRail.support
          successor.secondContinuation.support).mp
            (htrack.1 collision.face hface)
      · intro hface
        exact (actualAppendCollision_faceInExpectedTrack_iff collision
          left.paths.secondRail.support
          successor.firstContinuation.support).mp
            (htrack.2 collision.face hface)

variable
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

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

/-- The reduced four-cell collision bands with the middle case tied to the
actual stored repair.  The other three bounded bands are left unchanged. -/
inductive ExactSelectedLocalRailFourCellCollisionBandWithMiddleTrace
    (transition : ExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft))
    (face : SelectedFace (web := web)) : Prop
  | oldOld
      (firstOld : face ∈ firstLeft.paths.firstRail.support ∨
        face ∈ firstLeft.paths.secondRail.support)
      (lastOld : face ∈
          (LastLeft (bridge := bridge)
            (lastSuccessor := lastSuccessor)).paths.firstRail.support ∨
        face ∈
          (LastLeft (bridge := bridge)
            (lastSuccessor := lastSuccessor)).paths.secondRail.support)
  | successorThirdCenter
      (firstSuccessorPiece :
        face ∈ firstSuccessor.firstContinuation.support ∨
          face ∈ firstSuccessor.secondContinuation.support)
      (atThirdCenter : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
  | middleTrace
      (value : SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        bridge (firstSuccessor.rightRailsAsNextLeft bridge))
      (face_eq : value.face = face)
      (avoidsFace : transition.bridgeTrace.toOutcome.AvoidsFaceOnOneRail
        value.face)
      (trackProvenance : transition.bridgeTrace.HasTrackProvenance)
      (collisionTrackMembership :
        transition.bridgeTrace.toOutcome.CollisionFaceFollowsExpectedTracks
          value)
  | successorSuccessor
      (firstSuccessorPiece :
        face ∈ firstSuccessor.firstContinuation.support ∨
          face ∈ firstSuccessor.secondContinuation.support)
      (lastSuccessorPiece :
        face ∈ lastSuccessor.firstContinuation.support ∨
          face ∈ lastSuccessor.secondContinuation.support)

/-- Upgrade the old middle-seam table without matching collision-choice
witnesses: the stored trace resolves the face named by whichever witness the
outer classifier returned. -/
def ExactSelectedLocalRailFourCellCollisionBandAfterMiddleSeam.withMiddleTrace
    (transition : ExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft))
    {face : SelectedFace (web := web)}
    (band : ExactSelectedLocalRailFourCellCollisionBandAfterMiddleSeam
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face) :
    ExactSelectedLocalRailFourCellCollisionBandWithMiddleTrace transition face :=
  match band with
  | .oldOld firstOld lastOld => .oldOld firstOld lastOld
  | .successorThirdCenter firstSuccessorPiece atThirdCenter =>
      .successorThirdCenter firstSuccessorPiece atThirdCenter
  | .middleCollision value face_eq =>
      .middleTrace value face_eq
        (transition.bridgeTrace.avoidsActualCollisionFaceOnOneRail value)
        transition.bridgeTrace.hasTrackProvenance
        (transition.bridgeTrace.collisionFaceFollowsExpectedTracks value)
  | .successorSuccessor firstSuccessorPiece lastSuccessorPiece =>
      .successorSuccessor firstSuccessorPiece lastSuccessorPiece

/-- Collision-band predicate on the canonical transition after the middle
trace has been connected to the outer witness. -/
def ExactSelectedLocalRailTracedFourCellTransition.HasCollisionBandWithMiddleTrace
    (transition : ExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)) : Prop :=
  match transition.outcome with
  | .straight _ | .swapped _ => True
  | .straightStraightCollision _ _ _ _ collision
  | .straightSwappedCollision _ _ _ _ collision
  | .swappedStraightCollision _ _ _ _ collision
  | .swappedSwappedCollision _ _ _ _ collision =>
      ExactSelectedLocalRailFourCellCollisionBandWithMiddleTrace
        transition collision.face

/-- **L1 witness-specific middle repair.** Every canonical traced four-cell
transition either succeeds or returns one of three untouched bounded bands or
an actual middle collision together with the concrete canonical repair which
avoids its face on one rail and retains exact source-track provenance. -/
theorem ExactSelectedLocalRailTracedFourCellTransition.hasCollisionBandWithMiddleTrace
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (transition : ExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)) :
    transition.HasCollisionBandWithMiddleTrace := by
  have hband := transition.hasCollisionBandAfterMiddleSeam hsource
  unfold ExactSelectedLocalRailTracedFourCellTransition.HasCollisionBandWithMiddleTrace
  cases hout : transition.outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | straightStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      rw [hout] at hband
      exact hband.withMiddleTrace transition
  | straightSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      rw [hout] at hband
      exact hband.withMiddleTrace transition
  | swappedStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      rw [hout] at hband
      exact hband.withMiddleTrace transition
  | swappedSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      rw [hout] at hband
      exact hband.withMiddleTrace transition

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
