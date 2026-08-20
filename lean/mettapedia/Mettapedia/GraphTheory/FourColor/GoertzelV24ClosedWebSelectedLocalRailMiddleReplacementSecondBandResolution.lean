import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementFirstBandResolution

/-!
# L1: resolve the non-endpoint part of the second replacement band

The first-band resolution is not literally symmetric.  On the middle--last
band, a collision may be the far endpoint of the fourth-cell continuation;
the three-centre splice cannot remove its own requested endpoint.  This file
records that asymmetry rather than hiding it.

Every middle--last collision is reduced to one of three positive outcomes:
the displayed third centre, a third--fourth dual triangle, or a literal
second--fourth square splice.  The only remaining alternative is one of the
two exact fourth-cell far endpoints.  That residue is the reason the next
rolling window must advance once more before the second band can be consumed.

This is an exhaustive bounded classification with an actual route in the
square case.  It is not elimination of the far-end residue, companion-rail
separation, an arbitrary-length assembly, or closure of Fable flag L1.
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
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
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

private abbrev BridgeLeft :=
  firstSuccessor.rightRailsAsNextLeft bridge

/-- Exact source ingredients used by a second--fourth square splice. -/
def FaceInSecondFourthSquareSourceSpliceSupport
    (oldSupport newSupport : List (SelectedFace (web := web)))
    (current : SelectedFace (web := web)) : Prop :=
  current ∈ oldSupport ∨
    current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior firstInterior hfirstNext).center ∨
    current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center ∨
    current = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center ∨
    current ∈ newSupport

/-- A support receipt for the shifted source splice reduces companion
separation to the two source pieces and the three displayed centres. -/
theorem support_disjoint_of_faceInSecondFourthSquareSourceSpliceSupport
    {oldSupport newSupport routeSupport companionSupport :
      List (SelectedFace (web := web))}
    (hroute : ∀ current ∈ routeSupport,
      FaceInSecondFourthSquareSourceSpliceSupport
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
        (hlastNext := hlastNext) oldSupport newSupport current)
    (hold : oldSupport.Disjoint companionSupport)
    (hsecondCenter :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center ∉ companionSupport)
    (hthirdCenter :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center ∉
        companionSupport)
    (hfourthCenter :
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center ∉ companionSupport)
    (hnew : newSupport.Disjoint companionSupport) :
    routeSupport.Disjoint companionSupport := by
  rw [List.disjoint_left]
  intro current hcurrent hcompanion
  rcases hroute current hcurrent with
    holdCurrent | hsecond | hthird | hfourth | hnewCurrent
  · exact (List.disjoint_left.mp hold holdCurrent) hcompanion
  · exact hsecondCenter (hsecond ▸ hcompanion)
  · exact hthirdCenter (hthird ▸ hcompanion)
  · exact hfourthCenter (hfourth ▸ hcompanion)
  · exact (List.disjoint_left.mp hnew hnewCurrent) hcompanion

/-- One of the four literal second-cell/fourth-cell track splices, retaining
the exact endpoint parity and support receipt. -/
inductive SecondFourthSquareSourceSplice
    (face : SelectedFace (web := web)) : Type (u + 1)
  | firstFirst
      (route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingBefore))
      (isPath : route.IsPath) (avoids : face ∉ route.support)
      (support_receipt : ∀ current ∈ route.support,
        FaceInSecondFourthSquareSourceSpliceSupport
          (corridor := corridor) (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
          (hlastNext := hlastNext)
          (BridgeLeft (firstSuccessor := firstSuccessor)
            (bridge := bridge)).paths.firstRail.support
          lastSuccessor.firstContinuation.support current)
  | firstSecond
      (route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingAfter))
      (isPath : route.IsPath) (avoids : face ∉ route.support)
      (support_receipt : ∀ current ∈ route.support,
        FaceInSecondFourthSquareSourceSpliceSupport
          (corridor := corridor) (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
          (hlastNext := hlastNext)
          (BridgeLeft (firstSuccessor := firstSuccessor)
            (bridge := bridge)).paths.firstRail.support
          lastSuccessor.secondContinuation.support current)
  | secondFirst
      (route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingBefore))
      (isPath : route.IsPath) (avoids : face ∉ route.support)
      (support_receipt : ∀ current ∈ route.support,
        FaceInSecondFourthSquareSourceSpliceSupport
          (corridor := corridor) (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
          (hlastNext := hlastNext)
          (BridgeLeft (firstSuccessor := firstSuccessor)
            (bridge := bridge)).paths.secondRail.support
          lastSuccessor.firstContinuation.support current)
  | secondSecond
      (route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingAfter))
      (isPath : route.IsPath) (avoids : face ∉ route.support)
      (support_receipt : ∀ current ∈ route.support,
        FaceInSecondFourthSquareSourceSpliceSupport
          (corridor := corridor) (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
          (hlastNext := hlastNext)
          (BridgeLeft (firstSuccessor := firstSuccessor)
            (bridge := bridge)).paths.secondRail.support
          lastSuccessor.secondContinuation.support current)

/-- The honest residue of the shifted square repair: the collision is the
requested far endpoint, so no path avoiding it can retain that endpoint. -/
inductive SecondFourthFarEndpoint (face : SelectedFace (web := web)) : Prop
  | first
      (face_eq : face = selectedPlacementSideFace fourthPlacement
        lastSuccessor.rightOutgoingBefore)
  | second
      (face_eq : face = selectedPlacementSideFace fourthPlacement
        lastSuccessor.rightOutgoingAfter)

private theorem oldFirst_start_ne
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter ≠
      face := by
  intro hface
  apply (collision.face_ne_firstFlanks hsource).1
  exact (firstSuccessor.frame.leftBeforeFace_eq_rightAfterFace.trans hface).symm

private theorem oldSecond_start_ne
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore ≠
      face := by
  intro hface
  apply (collision.face_ne_firstFlanks hsource).2
  exact (firstSuccessor.frame.leftAfterFace_eq_rightBeforeFace.trans hface).symm

private theorem exists_secondFourthSquare_firstFirstSourceSplice
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (hold : face ∈ (BridgeLeft (firstSuccessor := firstSuccessor)
      (bridge := bridge)).paths.firstRail.support)
    (hnew : face ∈ lastSuccessor.firstContinuation.support)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hfourth : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center) face)
    (hthird : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
    (hfinish : face ≠ selectedPlacementSideFace fourthPlacement
      lastSuccessor.rightOutgoingBefore) :
    Nonempty (SecondFourthSquareSourceSplice
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) face) := by
  have holdAdjacent : ∀ current ∈ (BridgeLeft
      (firstSuccessor := firstSuccessor) (bridge := bridge)).paths.firstRail.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center) current :=
    (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)).paths
      |>.firstRail_support_adjacent_center
  have hnewAdjacent : ∀ current ∈ lastSuccessor.firstContinuation.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
            hlastNext).center) current := by
    intro current hcurrent
    apply lastSuccessor.rightRails.paths.firstRail_support_adjacent_center
    simpa only [lastSuccessor.firstContinuation_support] using hcurrent
  rcases exists_secondFourthSquare_crossSplice
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail
      lastSuccessor.firstContinuation
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail_isPath
      lastSuccessor.firstContinuation_isPath hold hnew
      (oldFirst_start_ne hsource collision) hfinish holdAdjacent hnewAdjacent
      hsecond hfourth hthird with ⟨route, hpath, havoids, hsupport⟩
  exact ⟨SecondFourthSquareSourceSplice.firstFirst route hpath havoids hsupport⟩

private theorem exists_secondFourthSquare_firstSecondSourceSplice
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (hold : face ∈ (BridgeLeft (firstSuccessor := firstSuccessor)
      (bridge := bridge)).paths.firstRail.support)
    (hnew : face ∈ lastSuccessor.secondContinuation.support)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hfourth : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center) face)
    (hthird : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
    (hfinish : face ≠ selectedPlacementSideFace fourthPlacement
      lastSuccessor.rightOutgoingAfter) :
    Nonempty (SecondFourthSquareSourceSplice
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) face) := by
  have holdAdjacent : ∀ current ∈ (BridgeLeft
      (firstSuccessor := firstSuccessor) (bridge := bridge)).paths.firstRail.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center) current :=
    (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)).paths
      |>.firstRail_support_adjacent_center
  have hnewAdjacent : ∀ current ∈ lastSuccessor.secondContinuation.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
            hlastNext).center) current := by
    intro current hcurrent
    apply lastSuccessor.rightRails.paths.secondRail_support_adjacent_center
    simpa only [lastSuccessor.secondContinuation_support] using hcurrent
  rcases exists_secondFourthSquare_crossSplice
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail
      lastSuccessor.secondContinuation
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail_isPath
      lastSuccessor.secondContinuation_isPath hold hnew
      (oldFirst_start_ne hsource collision) hfinish holdAdjacent hnewAdjacent
      hsecond hfourth hthird with ⟨route, hpath, havoids, hsupport⟩
  exact ⟨SecondFourthSquareSourceSplice.firstSecond route hpath havoids hsupport⟩

private theorem exists_secondFourthSquare_secondFirstSourceSplice
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (hold : face ∈ (BridgeLeft (firstSuccessor := firstSuccessor)
      (bridge := bridge)).paths.secondRail.support)
    (hnew : face ∈ lastSuccessor.firstContinuation.support)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hfourth : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center) face)
    (hthird : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
    (hfinish : face ≠ selectedPlacementSideFace fourthPlacement
      lastSuccessor.rightOutgoingBefore) :
    Nonempty (SecondFourthSquareSourceSplice
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) face) := by
  have holdAdjacent : ∀ current ∈ (BridgeLeft
      (firstSuccessor := firstSuccessor) (bridge := bridge)).paths.secondRail.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center) current :=
    (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)).paths
      |>.secondRail_support_adjacent_center
  have hnewAdjacent : ∀ current ∈ lastSuccessor.firstContinuation.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
            hlastNext).center) current := by
    intro current hcurrent
    apply lastSuccessor.rightRails.paths.firstRail_support_adjacent_center
    simpa only [lastSuccessor.firstContinuation_support] using hcurrent
  rcases exists_secondFourthSquare_crossSplice
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail
      lastSuccessor.firstContinuation
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail_isPath
      lastSuccessor.firstContinuation_isPath hold hnew
      (oldSecond_start_ne hsource collision) hfinish holdAdjacent hnewAdjacent
      hsecond hfourth hthird with ⟨route, hpath, havoids, hsupport⟩
  exact ⟨SecondFourthSquareSourceSplice.secondFirst route hpath havoids hsupport⟩

private theorem exists_secondFourthSquare_secondSecondSourceSplice
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (hold : face ∈ (BridgeLeft (firstSuccessor := firstSuccessor)
      (bridge := bridge)).paths.secondRail.support)
    (hnew : face ∈ lastSuccessor.secondContinuation.support)
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hfourth : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center) face)
    (hthird : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
    (hfinish : face ≠ selectedPlacementSideFace fourthPlacement
      lastSuccessor.rightOutgoingAfter) :
    Nonempty (SecondFourthSquareSourceSplice
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) face) := by
  have holdAdjacent : ∀ current ∈ (BridgeLeft
      (firstSuccessor := firstSuccessor) (bridge := bridge)).paths.secondRail.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center) current :=
    (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)).paths
      |>.secondRail_support_adjacent_center
  have hnewAdjacent : ∀ current ∈ lastSuccessor.secondContinuation.support,
      SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
            hlastNext).center) current := by
    intro current hcurrent
    apply lastSuccessor.rightRails.paths.secondRail_support_adjacent_center
    simpa only [lastSuccessor.secondContinuation_support] using hcurrent
  rcases exists_secondFourthSquare_crossSplice
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail
      lastSuccessor.secondContinuation
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail_isPath
      lastSuccessor.secondContinuation_isPath hold hnew
      (oldSecond_start_ne hsource collision) hfinish holdAdjacent hnewAdjacent
      hsecond hfourth hthird with ⟨route, hpath, havoids, hsupport⟩
  exact ⟨SecondFourthSquareSourceSplice.secondSecond route hpath havoids hsupport⟩

/-- Exhaustive resolution of the literal middle--last band.  The far endpoint
constructor is retained because deleting the requested endpoint would change
the interface rather than repair the path. -/
inductive ExactSelectedLocalRailMiddleReplacementSecondBandResolution
    (face : SelectedFace (web := web)) : Type (u + 1)
  | thirdCenter
      (face_eq : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
  | thirdFourthTriangle
      (third_adjacent : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        face)
      (fourth_adjacent : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
            hlastNext).center) face)
  | secondFourthSplice
      (splice : SecondFourthSquareSourceSplice
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) face)
  | farEndpoint
      (endpoint : SecondFourthFarEndpoint
        (fourthPlacement := fourthPlacement) (lastSuccessor := lastSuccessor) face)

/-- Every literal middle--last source band is consumed except for the two
named far endpoints. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.resolveSecondBand
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (middle : FaceInCanonicalMiddleSourcePieces
      (firstSuccessor := firstSuccessor) (bridge := bridge) face)
    (last : face ∈ lastSuccessor.firstContinuation.support ∨
      face ∈ lastSuccessor.secondContinuation.support) :
    Nonempty (ExactSelectedLocalRailMiddleReplacementSecondBandResolution
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (firstSuccessor := firstSuccessor)
      (bridge := bridge) (lastSuccessor := lastSuccessor) face) := by
  have hfourth : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center) face := by
    rcases last with hfirst | hsecond
    · apply lastSuccessor.rightRails.paths.firstRail_support_adjacent_center
      simpa only [lastSuccessor.firstContinuation_support] using hfirst
    · apply lastSuccessor.rightRails.paths.secondRail_support_adjacent_center
      simpa only [lastSuccessor.secondContinuation_support] using hsecond
  have resolveOld (old : face ∈ (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail.support ∨
      face ∈ (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail.support) :
      Nonempty (ExactSelectedLocalRailMiddleReplacementSecondBandResolution
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
        (hlastNext := hlastNext) (firstSuccessor := firstSuccessor)
        (bridge := bridge) (lastSuccessor := lastSuccessor) face) := by
    rcases old with holdFirst | holdSecond
    · have hsecond := (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail_support_adjacent_center face holdFirst
      by_cases hthird : face =
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
      · exact ⟨.thirdCenter hthird⟩
      · rcases last with hnew | hnew
        · by_cases hfinish : face = selectedPlacementSideFace fourthPlacement
              lastSuccessor.rightOutgoingBefore
          · exact ⟨.farEndpoint (.first hfinish)⟩
          · rcases exists_secondFourthSquare_firstFirstSourceSplice hsource collision
                holdFirst hnew hsecond hfourth hthird hfinish with ⟨splice⟩
            exact ⟨.secondFourthSplice splice⟩
        · by_cases hfinish : face = selectedPlacementSideFace fourthPlacement
              lastSuccessor.rightOutgoingAfter
          · exact ⟨.farEndpoint (.second hfinish)⟩
          · rcases exists_secondFourthSquare_firstSecondSourceSplice hsource collision
                holdFirst hnew hsecond hfourth hthird hfinish with ⟨splice⟩
            exact ⟨.secondFourthSplice splice⟩
    · have hsecond := (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail_support_adjacent_center face holdSecond
      by_cases hthird : face =
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
      · exact ⟨.thirdCenter hthird⟩
      · rcases last with hnew | hnew
        · by_cases hfinish : face = selectedPlacementSideFace fourthPlacement
              lastSuccessor.rightOutgoingBefore
          · exact ⟨.farEndpoint (.first hfinish)⟩
          · rcases exists_secondFourthSquare_secondFirstSourceSplice hsource collision
                holdSecond hnew hsecond hfourth hthird hfinish with ⟨splice⟩
            exact ⟨.secondFourthSplice splice⟩
        · by_cases hfinish : face = selectedPlacementSideFace fourthPlacement
              lastSuccessor.rightOutgoingAfter
          · exact ⟨.farEndpoint (.second hfinish)⟩
          · rcases exists_secondFourthSquare_secondSecondSourceSplice hsource collision
                holdSecond hnew hsecond hfourth hthird hfinish with ⟨splice⟩
            exact ⟨.secondFourthSplice splice⟩
  rcases middle with holdFirst | holdSecond | hthirdFirst | hthirdSecond |
      hsecondCenter | hbefore | hafter
  · exact resolveOld (.inl holdFirst)
  · exact resolveOld (.inr holdSecond)
  · have hthird : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        face := by
      apply bridge.rightRails.paths.firstRail_support_adjacent_center
      simpa only [← bridge.firstContinuation_support] using hthirdFirst
    exact ⟨.thirdFourthTriangle hthird hfourth⟩
  · have hthird : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
        face := by
      apply bridge.rightRails.paths.secondRail_support_adjacent_center
      simpa only [← bridge.secondContinuation_support] using hthirdSecond
    exact ⟨.thirdFourthTriangle hthird hfourth⟩
  · subst face
    let skeleton :=
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    have hnotadj : ¬ SelectedDualGraph (web := web).Adj
        (skeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center)
        (skeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior
              (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
            hlastNext).center) :=
      skeleton.separated_not_adjacent
        (nextCorridorInterior firstInterior hfirstNext).center
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center (by
            change firstInterior.center.val + 1 + 1 < firstInterior.center.val + 3
            omega)
    exact False.elim (hnotadj hfourth.symm)
  · subst face
    have holdFirst : selectedPlacementSideFace secondPlacement bridge.frame.leftBefore ∈
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.firstRail.support :=
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.firstRail.end_mem_support
    exact resolveOld (.inl holdFirst)
  · subst face
    have holdSecond : selectedPlacementSideFace secondPlacement bridge.frame.leftAfter ∈
        (BridgeLeft (firstSuccessor := firstSuccessor)
          (bridge := bridge)).paths.secondRail.support :=
      (BridgeLeft (firstSuccessor := firstSuccessor)
        (bridge := bridge)).paths.secondRail.end_mem_support
    exact resolveOld (.inr holdSecond)

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
