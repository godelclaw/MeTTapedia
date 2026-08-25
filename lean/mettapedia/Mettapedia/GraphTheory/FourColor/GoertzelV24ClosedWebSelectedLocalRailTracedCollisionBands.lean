import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTracedFourCellTransition

/-!
# L1: source bands of a traced four-cell rail collision

The traced four-cell packet localizes a retained collision in five geometric
positions and in five literal source pieces on either side.  Not every pair of
pieces can meet.  Corridor distance excludes the first centre entirely,
excludes an old first-window rail from the third centre, and excludes an old
first-window rail from either fourth-centre rail.

Consequently every retained collision produced by the canonical classifiers
lies in one of four source bands: old/old, successor/third-centre,
successor/old, or successor/successor.  This removes impossible branches from
the finite repair table without assuming that any surviving band is empty.

This does not eliminate the four surviving bands, construct the rolling
transition, attach either end cap, or close Fable flag L1.
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

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

/-- The four source bands which remain after the corridor-distance exclusions.
The disjunctions retain the exact rail track inside each band. -/
inductive ExactSelectedLocalRailFourCellCollisionBand
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
  | successorOld
      (firstSuccessorPiece : face ∈ firstSuccessor.firstContinuation.support ∨
        face ∈ firstSuccessor.secondContinuation.support)
      (lastOld : face ∈
          (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.firstRail.support ∨
        face ∈
          (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)).paths.secondRail.support)
  | successorSuccessor
      (firstSuccessorPiece : face ∈ firstSuccessor.firstContinuation.support ∨
        face ∈ firstSuccessor.secondContinuation.support)
      (lastSuccessorPiece : face ∈ lastSuccessor.firstContinuation.support ∨
        face ∈ lastSuccessor.secondContinuation.support)

/-- **L1 four-band pruning.** Exact literal-piece membership and corridor
distance reduce the raw five-by-five origin product to four live bands. -/
theorem collisionBand_of_retainedCollisionData
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    {face : SelectedFace (web := web)}
    (hdata : ExactSelectedLocalRailFourCellRetainedCollisionData
      firstWindow lastWindow face) :
    ExactSelectedLocalRailFourCellCollisionBand
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let third :=
    (nextCorridorInterior
      (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
  let fourth :=
    (nextCorridorInterior
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
      hlastNext).center
  have hfirstThirdNe : skeleton.faceAt firstInterior.center ≠
      skeleton.faceAt third :=
    skeleton.faceAt_ne (by
      intro h
      have hvalues := congrArg Fin.val h
      dsimp [third] at hvalues
      omega)
  have hfirstThirdNotAdj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt firstInterior.center) (skeleton.faceAt third) :=
    skeleton.separated_not_adjacent firstInterior.center third (by
      dsimp [third]
      omega)
  have hfirstFourthNotAdj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt firstInterior.center) (skeleton.faceAt fourth) :=
    skeleton.separated_not_adjacent firstInterior.center fourth (by
      dsimp [fourth]
      omega)
  rcases hdata with ⟨_, hfirst, hlast⟩
  rcases hfirst with hfirstCenter | hfirstOldFirst | hfirstOldSecond |
      hfirstSuccessorFirst | hfirstSuccessorSecond
  · rcases hlast with hlastCenter | hlastOldFirst | hlastOldSecond |
        hlastSuccessorFirst | hlastSuccessorSecond
    · exact (hfirstThirdNe (hfirstCenter.symm.trans hlastCenter)).elim
    · subst face
      exact (hfirstThirdNotAdj
        ((LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))
          |>.paths.firstRail_support_adjacent_center _ hlastOldFirst).symm).elim
    · subst face
      exact (hfirstThirdNotAdj
        ((LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))
          |>.paths.secondRail_support_adjacent_center _ hlastOldSecond).symm).elim
    · have hlast' : skeleton.faceAt firstInterior.center ∈
          lastSuccessor.rightRails.paths.firstRail.support := by
        rw [← lastSuccessor.firstContinuation_support]
        simpa [hfirstCenter] using hlastSuccessorFirst
      exact (hfirstFourthNotAdj
        (lastSuccessor.rightRails.paths.firstRail_support_adjacent_center
          _ hlast').symm).elim
    · have hlast' : skeleton.faceAt firstInterior.center ∈
          lastSuccessor.rightRails.paths.secondRail.support := by
        rw [← lastSuccessor.secondContinuation_support]
        simpa [hfirstCenter] using hlastSuccessorSecond
      exact (hfirstFourthNotAdj
        (lastSuccessor.rightRails.paths.secondRail_support_adjacent_center
          _ hlast').symm).elim
  · have hfirstAdj :=
      firstLeft.paths.firstRail_support_adjacent_center face hfirstOldFirst
    rcases hlast with hlastCenter | hlastOldFirst | hlastOldSecond |
        hlastSuccessorFirst | hlastSuccessorSecond
    · subst face
      exact (hfirstThirdNotAdj hfirstAdj).elim
    · exact .oldOld (Or.inl hfirstOldFirst) (Or.inl hlastOldFirst)
    · exact .oldOld (Or.inl hfirstOldFirst) (Or.inr hlastOldSecond)
    · have hlast' : face ∈ lastSuccessor.rightRails.paths.firstRail.support := by
        rw [← lastSuccessor.firstContinuation_support]
        exact hlastSuccessorFirst
      exact False.elim (corridor.no_common_fullNeighbor_of_add_two_lt hsource
        firstInterior.center fourth (by dsimp [fourth]; omega)
        ⟨face, hfirstAdj,
          lastSuccessor.rightRails.paths.firstRail_support_adjacent_center
            face hlast'⟩)
    · have hlast' : face ∈ lastSuccessor.rightRails.paths.secondRail.support := by
        rw [← lastSuccessor.secondContinuation_support]
        exact hlastSuccessorSecond
      exact False.elim (corridor.no_common_fullNeighbor_of_add_two_lt hsource
        firstInterior.center fourth (by dsimp [fourth]; omega)
        ⟨face, hfirstAdj,
          lastSuccessor.rightRails.paths.secondRail_support_adjacent_center
            face hlast'⟩)
  · have hfirstAdj :=
      firstLeft.paths.secondRail_support_adjacent_center face hfirstOldSecond
    rcases hlast with hlastCenter | hlastOldFirst | hlastOldSecond |
        hlastSuccessorFirst | hlastSuccessorSecond
    · subst face
      exact (hfirstThirdNotAdj hfirstAdj).elim
    · exact .oldOld (Or.inr hfirstOldSecond) (Or.inl hlastOldFirst)
    · exact .oldOld (Or.inr hfirstOldSecond) (Or.inr hlastOldSecond)
    · have hlast' : face ∈ lastSuccessor.rightRails.paths.firstRail.support := by
        rw [← lastSuccessor.firstContinuation_support]
        exact hlastSuccessorFirst
      exact False.elim (corridor.no_common_fullNeighbor_of_add_two_lt hsource
        firstInterior.center fourth (by dsimp [fourth]; omega)
        ⟨face, hfirstAdj,
          lastSuccessor.rightRails.paths.firstRail_support_adjacent_center
            face hlast'⟩)
    · have hlast' : face ∈ lastSuccessor.rightRails.paths.secondRail.support := by
        rw [← lastSuccessor.secondContinuation_support]
        exact hlastSuccessorSecond
      exact False.elim (corridor.no_common_fullNeighbor_of_add_two_lt hsource
        firstInterior.center fourth (by dsimp [fourth]; omega)
        ⟨face, hfirstAdj,
          lastSuccessor.rightRails.paths.secondRail_support_adjacent_center
            face hlast'⟩)
  · rcases hlast with hlastCenter | hlastOldFirst | hlastOldSecond |
        hlastSuccessorFirst | hlastSuccessorSecond
    · exact .successorThirdCenter (Or.inl hfirstSuccessorFirst) hlastCenter
    · exact .successorOld (Or.inl hfirstSuccessorFirst) (Or.inl hlastOldFirst)
    · exact .successorOld (Or.inl hfirstSuccessorFirst) (Or.inr hlastOldSecond)
    · exact .successorSuccessor (Or.inl hfirstSuccessorFirst)
        (Or.inl hlastSuccessorFirst)
    · exact .successorSuccessor (Or.inl hfirstSuccessorFirst)
        (Or.inr hlastSuccessorSecond)
  · rcases hlast with hlastCenter | hlastOldFirst | hlastOldSecond |
        hlastSuccessorFirst | hlastSuccessorSecond
    · exact .successorThirdCenter (Or.inr hfirstSuccessorSecond) hlastCenter
    · exact .successorOld (Or.inr hfirstSuccessorSecond) (Or.inl hlastOldFirst)
    · exact .successorOld (Or.inr hfirstSuccessorSecond) (Or.inr hlastOldSecond)
    · exact .successorSuccessor (Or.inr hfirstSuccessorSecond)
        (Or.inl hlastSuccessorFirst)
    · exact .successorSuccessor (Or.inr hfirstSuccessorSecond)
        (Or.inr hlastSuccessorSecond)

/-- Collision-band predicate on a canonical traced transition outcome. -/
def ExactSelectedLocalRailFourCellRetainedOutcome.HasCollisionBandData
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
      ExactSelectedLocalRailFourCellCollisionBand
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) collision.face

/-- Every canonical traced four-cell transition has only one of the four live
collision bands in a bad branch. -/
theorem ExactSelectedLocalRailTracedFourCellTransition.hasCollisionBandData
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (transition : ExactSelectedLocalRailTracedFourCellTransition
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft)) :
    transition.outcome.HasCollisionBandData := by
  have hlocalized := transition.hasLocalizedCollisionData
  generalize hout : transition.outcome = outcome at hlocalized ⊢
  cases outcome with
  | straight assembly => trivial
  | swapped assembly => trivial
  | straightStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact collisionBand_of_retainedCollisionData hsource
        transition.firstTrace.toExactTerminalWindow
        transition.lastTrace.toExactTerminalWindow hlocalized
  | straightSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact collisionBand_of_retainedCollisionData hsource
        transition.firstTrace.toExactTerminalWindow
        transition.lastTrace.toExactTerminalWindow hlocalized
  | swappedStraightCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact collisionBand_of_retainedCollisionData hsource
        transition.firstTrace.toExactTerminalWindow
        transition.lastTrace.toExactTerminalWindow hlocalized
  | swappedSwappedCollision firstAssembly lastAssembly hfirst hlast collision =>
      exact collisionBand_of_retainedCollisionData hsource
        transition.firstTrace.toExactTerminalWindow
        transition.lastTrace.toExactTerminalWindow hlocalized

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
