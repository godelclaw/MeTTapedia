import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalRailStep

/-!
# Remote separation of literal Cell-3 rail steps

Every face on a literal local rail remembers that it is adjacent to the
Cell-3 centre that generated it.  The source's boundary-clean geodesic
condition forbids one face from being adjacent to corridor centres more than
two positions apart.  Consequently all four pairs of rail tracks have
disjoint support once their centres have a gap of at least three.

This is the remote part of lengthwise rail assembly.  It deliberately leaves
the two bounded neighbouring gaps and the end-cap attachments open.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace LocalLayerFormation

private theorem supports_disjoint_of_add_two_lt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (leftInterior rightInterior : CorridorInterior blockLength)
    (hseparated : leftInterior.center.val + 2 < rightInterior.center.val)
    (leftSupport rightSupport :
      List (AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))))
    (hleft : ∀ face ∈ leftSupport,
      (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          ((corridor.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) face)
    (hright : ∀ face ∈ rightSupport,
      (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          ((corridor.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton).faceAt rightInterior.center) face) :
    leftSupport.Disjoint rightSupport := by
  rw [List.disjoint_left]
  intro face hfaceLeft hfaceRight
  exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
    leftInterior.center rightInterior.center hseparated
    ⟨face, hleft face hfaceLeft, hright face hfaceRight⟩

namespace SourceLocalRailWalkPair

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior rightInterior : CorridorInterior blockLength}
    {leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior}
    {rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique rightInterior}
    {leftIncomingBefore leftIncomingAfter leftOutgoingBefore leftOutgoingAfter :
      {position // position ∈ placementSidePositions leftPlacement}}
    {rightIncomingBefore rightIncomingAfter rightOutgoingBefore rightOutgoingAfter :
      {position // position ∈ placementSidePositions rightPlacement}}

/-- **Remote literal rail separation, first/first (not Fable flag L1).** First-track rail
steps generated at Cell-3 centres at least three positions apart cannot share
a facial-dual vertex. -/
theorem firstRail_support_disjoint_firstRail_of_add_two_lt
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftOutgoingBefore leftOutgoingAfter)
    (right : SourceLocalRailWalkPair rightPlacement rightIncomingBefore
      rightIncomingAfter rightOutgoingBefore rightOutgoingAfter)
    (hseparated : leftInterior.center.val + 2 < rightInterior.center.val) :
    left.firstRail.support.Disjoint right.firstRail.support :=
  supports_disjoint_of_add_two_lt hsource leftInterior rightInterior hseparated
    left.firstRail.support right.firstRail.support
    left.firstRail_support_adjacent_center
    right.firstRail_support_adjacent_center

/-- **Remote literal rail separation, first/second (not Fable flag L1).** The first track of
the left cell and second track of a remote right cell have disjoint support. -/
theorem firstRail_support_disjoint_secondRail_of_add_two_lt
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftOutgoingBefore leftOutgoingAfter)
    (right : SourceLocalRailWalkPair rightPlacement rightIncomingBefore
      rightIncomingAfter rightOutgoingBefore rightOutgoingAfter)
    (hseparated : leftInterior.center.val + 2 < rightInterior.center.val) :
    left.firstRail.support.Disjoint right.secondRail.support :=
  supports_disjoint_of_add_two_lt hsource leftInterior rightInterior hseparated
    left.firstRail.support right.secondRail.support
    left.firstRail_support_adjacent_center
    right.secondRail_support_adjacent_center

/-- **Remote literal rail separation, second/first (not Fable flag L1).** The second track of
the left cell and first track of a remote right cell have disjoint support. -/
theorem secondRail_support_disjoint_firstRail_of_add_two_lt
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftOutgoingBefore leftOutgoingAfter)
    (right : SourceLocalRailWalkPair rightPlacement rightIncomingBefore
      rightIncomingAfter rightOutgoingBefore rightOutgoingAfter)
    (hseparated : leftInterior.center.val + 2 < rightInterior.center.val) :
    left.secondRail.support.Disjoint right.firstRail.support :=
  supports_disjoint_of_add_two_lt hsource leftInterior rightInterior hseparated
    left.secondRail.support right.firstRail.support
    left.secondRail_support_adjacent_center
    right.firstRail_support_adjacent_center

/-- **Remote literal rail separation, second/second (not Fable flag L1).** Second-track rail
steps generated at Cell-3 centres at least three positions apart cannot share
a facial-dual vertex. -/
theorem secondRail_support_disjoint_secondRail_of_add_two_lt
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (left : SourceLocalRailWalkPair leftPlacement leftIncomingBefore
      leftIncomingAfter leftOutgoingBefore leftOutgoingAfter)
    (right : SourceLocalRailWalkPair rightPlacement rightIncomingBefore
      rightIncomingAfter rightOutgoingBefore rightOutgoingAfter)
    (hseparated : leftInterior.center.val + 2 < rightInterior.center.val) :
    left.secondRail.support.Disjoint right.secondRail.support :=
  supports_disjoint_of_add_two_lt hsource leftInterior rightInterior hseparated
    left.secondRail.support right.secondRail.support
    left.secondRail_support_adjacent_center
    right.secondRail_support_adjacent_center

end SourceLocalRailWalkPair

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
