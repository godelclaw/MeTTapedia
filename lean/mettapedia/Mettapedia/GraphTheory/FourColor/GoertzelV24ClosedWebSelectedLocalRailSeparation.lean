import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailShape

/-!
# Remote separation of selected literal Cell-3 rail paths

Every face retained by a selected bounded rail path is adjacent to the
Cell-3 centre that generated it.  The source boundary-clean geodesic condition
forbids one face from being adjacent to corridor centres more than two
positions apart.  Hence all four pairs of selected rail tracks are disjoint
for centre gap at least three.

This is the remote part of L1 rail assembly in the choice-based selected-rung
representation.  It leaves only the bounded neighbouring interactions and
the two end-cap attachments; it does not construct the final crosscuts.
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

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailPaths

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior rightInterior : CorridorInterior blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs rightInterior}
    {leftIncomingBefore leftIncomingAfter leftOutgoingBefore leftOutgoingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {rightIncomingBefore rightIncomingAfter rightOutgoingBefore rightOutgoingAfter :
      {position // position ∈ selectedPlacementSidePositions rightPlacement}}

private theorem supports_disjoint_of_add_two_lt
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (hseparated : leftInterior.center.val + 2 < rightInterior.center.val)
    (leftSupport rightSupport :
      List (AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))))
    (hleft : ∀ face ∈ leftSupport,
      (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
            |>.faceAt leftInterior.center) face)
    (hright : ∀ face ∈ rightSupport,
      (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
            |>.faceAt rightInterior.center) face) :
    leftSupport.Disjoint rightSupport := by
  rw [List.disjoint_left]
  intro face hfaceLeft hfaceRight
  exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
    leftInterior.center rightInterior.center hseparated
    ⟨face, hleft face hfaceLeft, hright face hfaceRight⟩

/-- **L1 remote selected rail separation, first/first.** First-track pieces
generated at Cell-3 centres at least three positions apart have disjoint
facial support. -/
theorem firstRail_support_disjoint_firstRail_of_add_two_lt
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (left : SelectedSourceLocalRailPaths leftPlacement leftIncomingBefore
      leftIncomingAfter leftOutgoingBefore leftOutgoingAfter)
    (right : SelectedSourceLocalRailPaths rightPlacement rightIncomingBefore
      rightIncomingAfter rightOutgoingBefore rightOutgoingAfter)
    (hseparated : leftInterior.center.val + 2 < rightInterior.center.val) :
    left.firstRail.support.Disjoint right.firstRail.support :=
  supports_disjoint_of_add_two_lt hsource hseparated
    left.firstRail.support right.firstRail.support
    left.firstRail_support_adjacent_center
    right.firstRail_support_adjacent_center

/-- **L1 remote selected rail separation, first/second.** -/
theorem firstRail_support_disjoint_secondRail_of_add_two_lt
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (left : SelectedSourceLocalRailPaths leftPlacement leftIncomingBefore
      leftIncomingAfter leftOutgoingBefore leftOutgoingAfter)
    (right : SelectedSourceLocalRailPaths rightPlacement rightIncomingBefore
      rightIncomingAfter rightOutgoingBefore rightOutgoingAfter)
    (hseparated : leftInterior.center.val + 2 < rightInterior.center.val) :
    left.firstRail.support.Disjoint right.secondRail.support :=
  supports_disjoint_of_add_two_lt hsource hseparated
    left.firstRail.support right.secondRail.support
    left.firstRail_support_adjacent_center
    right.secondRail_support_adjacent_center

/-- **L1 remote selected rail separation, second/first.** -/
theorem secondRail_support_disjoint_firstRail_of_add_two_lt
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (left : SelectedSourceLocalRailPaths leftPlacement leftIncomingBefore
      leftIncomingAfter leftOutgoingBefore leftOutgoingAfter)
    (right : SelectedSourceLocalRailPaths rightPlacement rightIncomingBefore
      rightIncomingAfter rightOutgoingBefore rightOutgoingAfter)
    (hseparated : leftInterior.center.val + 2 < rightInterior.center.val) :
    left.secondRail.support.Disjoint right.firstRail.support :=
  supports_disjoint_of_add_two_lt hsource hseparated
    left.secondRail.support right.firstRail.support
    left.secondRail_support_adjacent_center
    right.firstRail_support_adjacent_center

/-- **L1 remote selected rail separation, second/second.** -/
theorem secondRail_support_disjoint_secondRail_of_add_two_lt
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (left : SelectedSourceLocalRailPaths leftPlacement leftIncomingBefore
      leftIncomingAfter leftOutgoingBefore leftOutgoingAfter)
    (right : SelectedSourceLocalRailPaths rightPlacement rightIncomingBefore
      rightIncomingAfter rightOutgoingBefore rightOutgoingAfter)
    (hseparated : leftInterior.center.val + 2 < rightInterior.center.val) :
    left.secondRail.support.Disjoint right.secondRail.support :=
  supports_disjoint_of_add_two_lt hsource hseparated
    left.secondRail.support right.secondRail.support
    left.secondRail_support_adjacent_center
    right.secondRail_support_adjacent_center

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailPaths

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
