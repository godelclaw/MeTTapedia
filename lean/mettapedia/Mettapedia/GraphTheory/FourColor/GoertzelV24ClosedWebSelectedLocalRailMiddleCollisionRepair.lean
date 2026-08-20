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
output rails avoids that face.  This module records that witness-specific fact
together with the trace's already-proved source-track provenance and inserts
both into the four-cell collision table.

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
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
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
