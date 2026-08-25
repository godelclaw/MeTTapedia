import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFourCellAppend

/-!
# L1: bounded geometry of a four-cell selected-rail collision

The four-cell append classifier localizes every failed interaction to the
closed dual neighbourhoods of two consecutive centre pairs.  Boundary-clean
corridor geometry reduces that intersection to five positive cases: either
one of the two middle centres, or a common neighbour across one of the three
two-step/adjacent spans meeting the middle seam.

This is the finite geometric case split consumed by the next repair.  It does
not yet reroute either rail, eliminate either two-step case using closed-map
minimality, iterate the transition, attach an end cap, or close Fable flag L1.
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- The five possible positions of a face lying near both consecutive
two-centre windows. -/
inductive FourCenterCollisionGeometry
    (first second third fourth : Fin blockLength)
    (face : SelectedFace (web := web)) : Prop
  | secondCenter
      (hface : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          second)
  | thirdCenter
      (hface : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          third)
  | firstThirdCommon
      (hfirst : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          first) face)
      (hthird : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          third) face)
  | secondThirdCommon
      (hsecond : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          second) face)
      (hthird : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          third) face)
  | secondFourthCommon
      (hsecond : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          second) face)
      (hfourth : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          fourth) face)

/-- **L1 bounded four-centre intersection.** Boundary cleanliness removes all
but five cases from the product of the two closed-neighbourhood predicates. -/
theorem fourCenterCollisionGeometry_of_near_pairs
    {first second third fourth : Fin blockLength}
    (hsecond : second.val = first.val + 1)
    (hthird : third.val = second.val + 1)
    (hfourth : fourth.val = third.val + 1)
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (face : SelectedFace (web := web))
    (hleft : FaceNearSelectedCenterPair (corridor := corridor)
      first second face)
    (hright : FaceNearSelectedCenterPair (corridor := corridor)
      third fourth face) :
    FourCenterCollisionGeometry (corridor := corridor)
      first second third fourth face := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  have hfirstThirdNe : skeleton.faceAt first ≠ skeleton.faceAt third :=
    skeleton.faceAt_ne (by
      intro h
      have hval := congrArg Fin.val h
      omega)
  have hfirstFourthNe : skeleton.faceAt first ≠ skeleton.faceAt fourth :=
    skeleton.faceAt_ne (by
      intro h
      have hval := congrArg Fin.val h
      omega)
  have hsecondThirdNe : skeleton.faceAt second ≠ skeleton.faceAt third :=
    skeleton.faceAt_ne (by
      intro h
      have hval := congrArg Fin.val h
      omega)
  have hsecondFourthNe : skeleton.faceAt second ≠ skeleton.faceAt fourth :=
    skeleton.faceAt_ne (by
      intro h
      have hval := congrArg Fin.val h
      omega)
  have hfirstThirdNotAdj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt first) (skeleton.faceAt third) :=
    skeleton.separated_not_adjacent first third (by omega)
  have hfirstFourthNotAdj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt first) (skeleton.faceAt fourth) :=
    skeleton.separated_not_adjacent first fourth (by omega)
  have hsecondFourthNotAdj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt second) (skeleton.faceAt fourth) :=
    skeleton.separated_not_adjacent second fourth (by omega)
  rcases hleft with hfirstEq | hsecondEq | hfirstAdj | hsecondAdj
  · rcases hright with hthirdEq | hfourthEq | hthirdAdj | hfourthAdj
    · exact (hfirstThirdNe (hfirstEq.symm.trans hthirdEq)).elim
    · exact (hfirstFourthNe (hfirstEq.symm.trans hfourthEq)).elim
    · subst face
      exact (hfirstThirdNotAdj hthirdAdj.symm).elim
    · subst face
      exact (hfirstFourthNotAdj hfourthAdj.symm).elim
  · rcases hright with hthirdEq | hfourthEq | hthirdAdj | hfourthAdj
    · exact (hsecondThirdNe (hsecondEq.symm.trans hthirdEq)).elim
    · exact (hsecondFourthNe (hsecondEq.symm.trans hfourthEq)).elim
    · exact .secondCenter hsecondEq
    · subst face
      exact (hsecondFourthNotAdj hfourthAdj.symm).elim
  · rcases hright with hthirdEq | hfourthEq | hthirdAdj | hfourthAdj
    · subst face
      exact (hfirstThirdNotAdj hfirstAdj).elim
    · subst face
      exact (hfirstFourthNotAdj hfirstAdj).elim
    · exact .firstThirdCommon hfirstAdj hthirdAdj
    · exact (corridor.no_common_fullNeighbor_of_add_two_lt hsource
        first fourth (by omega) ⟨face, hfirstAdj, hfourthAdj⟩).elim
  · rcases hright with hthirdEq | hfourthEq | hthirdAdj | hfourthAdj
    · exact .thirdCenter hthirdEq
    · subst face
      exact (hsecondFourthNotAdj hsecondAdj).elim
    · exact .secondThirdCommon hsecondAdj hthirdAdj
    · exact .secondFourthCommon hsecondAdj hfourthAdj

variable
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

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

/-- Every ordered collision returned by the literal four-cell append belongs
to one of the five bounded geometric cases. -/
theorem orderedFourCellCollision_geometry
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (firstWindow : CertifiedSelectedLocalRailTerminalWindow firstSuccessor firstLeft)
    (lastWindow : CertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (collision : SelectedRailPairAppendCollision (web := web)
      firstWindow.firstSupport firstWindow.secondSupport
      lastWindow.firstSupport lastWindow.secondSupport) :
    FourCenterCollisionGeometry (corridor := corridor)
      firstInterior.center
      (nextCorridorInterior firstInterior hfirstNext).center
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center collision.face := by
  have hnear := orderedFourCellCollision_face_near_both_windows
    firstWindow lastWindow collision
  exact fourCenterCollisionGeometry_of_near_pairs rfl rfl rfl hsource
    collision.face hnear.1 hnear.2

/-- Crossed endpoint order has the same five geometric possibilities. -/
theorem crossedFourCellCollision_geometry
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (firstWindow : CertifiedSelectedLocalRailTerminalWindow firstSuccessor firstLeft)
    (lastWindow : CertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (collision : SelectedRailPairAppendCollision (web := web)
      firstWindow.firstSupport firstWindow.secondSupport
      lastWindow.secondSupport lastWindow.firstSupport) :
    FourCenterCollisionGeometry (corridor := corridor)
      firstInterior.center
      (nextCorridorInterior firstInterior hfirstNext).center
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center collision.face := by
  have hnear := crossedFourCellCollision_face_near_both_windows
    firstWindow lastWindow collision
  exact fourCenterCollisionGeometry_of_near_pairs rfl rfl rfl hsource
    collision.face hnear.1 hnear.2

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
