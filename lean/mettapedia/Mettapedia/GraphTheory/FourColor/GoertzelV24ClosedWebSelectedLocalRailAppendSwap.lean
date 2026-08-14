import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendReroute

/-!
# L1: repair two cross-track collisions by swapping the outgoing rails

A single cross-track collision constructs one crossed route, but it does not
connect the other two unmatched seam faces.  If both cross-track tests fail,
the two exhibited collision faces supply both switches.  Provided the two
same-track old/new separation tests hold, the two crossed reroutes are simple,
mutually support-disjoint, and form an assembly with swapped outgoing
endpoints.

This is a constructive local repair and an exact classification of what the
endpoint swap consumes.  It does not handle the one-collision pattern,
iterate an arbitrary corridor, or attach the two annular end caps.
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

variable {V : Type*} [Fintype V] [DecidableEq V]
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

/-- **L1 double-collision swap.** Two opposite cross-track collisions and
the two surviving same-track separation tests construct a separated rail
assembly with the two outgoing endpoints exchanged. -/
noncomputable def appendSuccessorSwapBothCrossCollisions
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter)
    (firstSecondFace secondFirstFace :
      AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hfirstSecondOld : firstSecondFace ∈ left.paths.firstRail.support)
    (hfirstSecondNew :
      firstSecondFace ∈ successor.secondContinuation.support.tail)
    (hsecondFirstOld : secondFirstFace ∈ left.paths.secondRail.support)
    (hsecondFirstNew :
      secondFirstFace ∈ successor.firstContinuation.support.tail)
    (hfirstFirst : left.paths.firstRail.support.Disjoint
      successor.firstContinuation.support.tail)
    (hsecondSecond : left.paths.secondRail.support.Disjoint
      successor.secondContinuation.support.tail) :
    SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore) := by
  let firstReroute :=
    SeparatedSelectedSourceLocalRailSuccessor.firstToSecondReroute
      (successor := successor) (left := left) firstSecondFace
        hfirstSecondOld hfirstSecondNew
  let secondReroute :=
    SeparatedSelectedSourceLocalRailSuccessor.secondToFirstReroute
      (successor := successor) (left := left) secondFirstFace
        hsecondFirstOld hsecondFirstNew
  refine {
    firstRail := firstReroute.route
    secondRail := secondReroute.route
    firstRail_isPath := firstReroute.route_isPath
    secondRail_isPath := secondReroute.route_isPath
    firstRail_support_disjoint_secondRail := ?_
  }
  rw [List.disjoint_left]
  intro face hfirst hsecond
  have hfirstParts := firstReroute.route_support_subset face hfirst
  have hsecondParts := secondReroute.route_support_subset face hsecond
  rcases hfirstParts with hfirstOld | hsecondNew
  · rcases hsecondParts with hsecondOld | hfirstNew
    · exact (List.disjoint_left.mp
        left.firstRail_support_disjoint_secondRail hfirstOld) hsecondOld
    · exact (List.disjoint_left.mp hfirstFirst hfirstOld) hfirstNew
  · rcases hsecondParts with hsecondOld | hfirstNew
    · exact (List.disjoint_left.mp hsecondSecond hsecondOld) hsecondNew
    · exact (List.disjoint_left.mp
        successor.firstContinuation_support_disjoint_secondContinuation
          (List.mem_of_mem_tail hfirstNew))
        (List.mem_of_mem_tail hsecondNew)

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
