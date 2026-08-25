import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSquareCenterBridge

/-!
# L1: resolve the first band of a middle-replacement collision

The source-local band theorem places every surviving replacement collision
either between the first packet and the repaired middle, or between the
repaired middle and the last packet.  This module completely consumes the
first alternative.  Its seven middle-source atoms reduce to the displayed
second centre, a first--second dual triangle, or one of the four literal
first--third square splices.

The middle--last alternative is retained verbatim.  This is therefore an
exhaustive first-band resolution, not a complete collision resolution,
companion-rail separation, arbitrary-length assembly, or Fable flag L1.
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

/-- One of the four literal first-cell/third-cell track splices, retaining
the exact endpoint parity and support receipt. -/
inductive FirstThirdSquareSourceSplice
    (face : SelectedFace (web := web)) : Type (u + 1)
  | firstFirst
      (route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore))
      (isPath : route.IsPath) (avoids : face ∉ route.support)
      (support_receipt : ∀ current ∈ route.support,
        FaceInFirstThirdSquareSourceSpliceSupport
          (corridor := corridor) (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
          firstLeft.paths.firstRail.support bridge.firstContinuation.support
          current)
  | firstSecond
      (route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftBefore)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter))
      (isPath : route.IsPath) (avoids : face ∉ route.support)
      (support_receipt : ∀ current ∈ route.support,
        FaceInFirstThirdSquareSourceSpliceSupport
          (corridor := corridor) (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
          firstLeft.paths.firstRail.support bridge.secondContinuation.support
          current)
  | secondFirst
      (route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingBefore))
      (isPath : route.IsPath) (avoids : face ∉ route.support)
      (support_receipt : ∀ current ∈ route.support,
        FaceInFirstThirdSquareSourceSpliceSupport
          (corridor := corridor) (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
          firstLeft.paths.secondRail.support bridge.firstContinuation.support
          current)
  | secondSecond
      (route : SelectedDualGraph (web := web).Walk
        (selectedPlacementSideFace firstPlacement firstSuccessor.frame.leftAfter)
        (selectedPlacementSideFace thirdPlacement bridge.rightOutgoingAfter))
      (isPath : route.IsPath) (avoids : face ∉ route.support)
      (support_receipt : ∀ current ∈ route.support,
        FaceInFirstThirdSquareSourceSpliceSupport
          (corridor := corridor) (firstInterior := firstInterior)
          (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
          firstLeft.paths.secondRail.support bridge.secondContinuation.support
          current)

/-- Package the complete two-by-two literal track table. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.exists_firstThirdSquareSourceSplice
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge (BridgeLeft
      (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face)
    (hfirst : face ∈ firstLeft.paths.firstRail.support ∨
      face ∈ firstLeft.paths.secondRail.support)
    (hnew : face ∈ bridge.firstContinuation.support ∨
      face ∈ bridge.secondContinuation.support)
    (hfirstAdjacent : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthirdAdjacent : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    Nonempty (FirstThirdSquareSourceSplice
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (firstLeft := firstLeft) face) := by
  rcases hfirst with hfirst | hsecond <;> rcases hnew with hnew | hnew
  · rcases collision.exists_firstThirdSquare_firstFirstSourceSplice hsource
      hfirst hnew hfirstAdjacent hthirdAdjacent hfaceSecond with
      ⟨route, hpath, havoids, hsupport⟩
    exact ⟨.firstFirst route hpath havoids hsupport⟩
  · rcases collision.exists_firstThirdSquare_firstSecondSourceSplice hsource
      hfirst hnew hfirstAdjacent hthirdAdjacent hfaceSecond with
      ⟨route, hpath, havoids, hsupport⟩
    exact ⟨.firstSecond route hpath havoids hsupport⟩
  · rcases collision.exists_firstThirdSquare_secondFirstSourceSplice hsource
      hsecond hnew hfirstAdjacent hthirdAdjacent hfaceSecond with
      ⟨route, hpath, havoids, hsupport⟩
    exact ⟨.secondFirst route hpath havoids hsupport⟩
  · rcases collision.exists_firstThirdSquare_secondSecondSourceSplice hsource
      hsecond hnew hfirstAdjacent hthirdAdjacent hfaceSecond with
      ⟨route, hpath, havoids, hsupport⟩
    exact ⟨.secondSecond route hpath havoids hsupport⟩

/-- Exhaustive resolution of the first adjacent collision band.  The only
unconsumed constructor is the explicitly retained middle--last band. -/
inductive ExactSelectedLocalRailMiddleReplacementFirstBandResolution
    (face : SelectedFace (web := web)) : Type (u + 1)
  | secondCenter
      (face_eq : face =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center)
  | firstSecondTriangle
      (first_adjacent : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          firstInterior.center) face)
      (second_adjacent : SelectedDualGraph (web := web).Adj
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center) face)
  | firstThirdSplice
      (splice : FirstThirdSquareSourceSplice
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (firstLeft := firstLeft) face)
  | middleLast
      (band : ExactSelectedLocalRailMiddleReplacementSourceLocalBand
        (firstSuccessor := firstSuccessor) (bridge := bridge)
        (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) face)

/-- Every surviving collision is either resolved in the first band or is
returned as the exact middle--last source packet for the next rung. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.resolveFirstBand
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge (BridgeLeft
      (firstSuccessor := firstSuccessor) (bridge := bridge))}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    Nonempty (@ExactSelectedLocalRailMiddleReplacementFirstBandResolution
      V _ _ G _ data coloring web blockLength corridor firstInterior hfirstNext
      hbridgeNext hlastNext rungs firstPlacement secondPlacement thirdPlacement
      fourthPlacement firstSuccessor bridge lastSuccessor firstIncomingBefore
      firstIncomingAfter firstLeft face) := by
  let band := (collision.hasLocalBand hsource).toSourceLocalBand
  cases band with
  | middleLast middle last => exact ⟨.middleLast (.middleLast middle last)⟩
  | firstMiddle first middle =>
      have hfirstAdjacent : SelectedDualGraph (web := web).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            firstInterior.center) face := by
        rcases first with hfirst | hsecond
        · exact firstLeft.paths.firstRail_support_adjacent_center face hfirst
        · exact firstLeft.paths.secondRail_support_adjacent_center face hsecond
      rcases middle with holdFirst | holdSecond | hnewFirst | hnewSecond |
          hcenter | hbefore | hafter
      · exact ⟨.firstSecondTriangle hfirstAdjacent
          ((BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)).paths
            |>.firstRail_support_adjacent_center face holdFirst)⟩
      · exact ⟨.firstSecondTriangle hfirstAdjacent
          ((BridgeLeft (firstSuccessor := firstSuccessor) (bridge := bridge)).paths
            |>.secondRail_support_adjacent_center face holdSecond)⟩
      · by_cases hfaceSecond : face =
            corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
              (nextCorridorInterior firstInterior hfirstNext).center
        · exact ⟨.secondCenter hfaceSecond⟩
        · have hthirdAdjacent : SelectedDualGraph (web := web).Adj
              (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
                (nextCorridorInterior
                  (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
              face := by
              apply bridge.rightRails.paths.firstRail_support_adjacent_center
              simpa only [← bridge.firstContinuation_support] using hnewFirst
          rcases collision.exists_firstThirdSquareSourceSplice hsource first
              (.inl hnewFirst) hfirstAdjacent hthirdAdjacent hfaceSecond with
            ⟨splice⟩
          exact ⟨.firstThirdSplice splice⟩
      · by_cases hfaceSecond : face =
            corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
              (nextCorridorInterior firstInterior hfirstNext).center
        · exact ⟨.secondCenter hfaceSecond⟩
        · have hthirdAdjacent : SelectedDualGraph (web := web).Adj
              (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
                (nextCorridorInterior
                  (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
              face := by
              apply bridge.rightRails.paths.secondRail_support_adjacent_center
              simpa only [← bridge.secondContinuation_support] using hnewSecond
          rcases collision.exists_firstThirdSquareSourceSplice hsource first
              (.inr hnewSecond) hfirstAdjacent hthirdAdjacent hfaceSecond with
            ⟨splice⟩
          exact ⟨.firstThirdSplice splice⟩
      · exact ⟨.secondCenter hcenter⟩
      · subst face
        exact ⟨.firstSecondTriangle hfirstAdjacent
          (selectedPlacementSideFace_adjacent_center
            (corridor := corridor) secondPlacement bridge.frame.leftBefore)⟩
      · subst face
        exact ⟨.firstSecondTriangle hfirstAdjacent
          (selectedPlacementSideFace_adjacent_center
            (corridor := corridor) secondPlacement bridge.frame.leftAfter)⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
