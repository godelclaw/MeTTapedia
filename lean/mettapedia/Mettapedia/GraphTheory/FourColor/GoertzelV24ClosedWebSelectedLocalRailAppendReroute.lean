import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendBypass

/-!
# L1: a literal reroute supplied by every cross-track collision

The loop-erased selected append can fail only when an old rail meets the
opposite continuation.  Such a collision is not merely negative data: cut
the old rail at the exhibited face, follow the opposite continuation from
that face, and erase loops.  This constructs a simple path to the opposite
outgoing endpoint whose support stays inside the two displayed pieces.

The result below deliberately constructs one crossed path, not a separated
pair.  Simultaneous uncrossing of both rails and preservation of their two
end caps remain the source-facing L1 obligation.
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

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

namespace SeparatedSelectedSourceLocalRailSuccessor

variable
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

/-- A collision of the old first rail with the new second continuation
constructs a simple crossed route from the first incoming endpoint to the
second outgoing endpoint. -/
structure FirstToSecondReroute
    (collisionFace : SelectedFace (web := web)) where
  route : SelectedDualGraph (web := web).Walk
    (selectedPlacementSideFace leftPlacement leftIncomingBefore)
    (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
  route_isPath : route.IsPath
  route_support_subset : ∀ face ∈ route.support,
    face ∈ left.paths.firstRail.support ∨
      face ∈ successor.secondContinuation.support

/-- Symmetrically, a collision of the old second rail with the new first
continuation constructs a simple crossed route to the first outgoing
endpoint. -/
structure SecondToFirstReroute
    (collisionFace : SelectedFace (web := web)) where
  route : SelectedDualGraph (web := web).Walk
    (selectedPlacementSideFace leftPlacement leftIncomingAfter)
    (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
  route_isPath : route.IsPath
  route_support_subset : ∀ face ∈ route.support,
    face ∈ left.paths.secondRail.support ∨
      face ∈ successor.firstContinuation.support

/-- Construct the first-to-second reroute at one exhibited collision. -/
noncomputable def firstToSecondReroute
    (collisionFace : SelectedFace (web := web))
    (hold : collisionFace ∈ left.paths.firstRail.support)
    (hnew : collisionFace ∈ successor.secondContinuation.support.tail) :
    FirstToSecondReroute (successor := successor) (left := left)
      collisionFace := by
  let hnewFull : collisionFace ∈ successor.secondContinuation.support :=
    List.mem_of_mem_tail hnew
  let raw :=
    (left.paths.firstRail.takeUntil collisionFace hold).append
      (successor.secondContinuation.dropUntil collisionFace hnewFull)
  refine {
    route := raw.bypass
    route_isPath := raw.bypass_isPath
    route_support_subset := ?_
  }
  intro face hface
  have hraw := raw.support_bypass_subset_support hface
  rw [SimpleGraph.Walk.support_append] at hraw
  rcases List.mem_append.mp hraw with hprefix | hsuffix
  · exact Or.inl
      (left.paths.firstRail.support_takeUntil_subset_support hold hprefix)
  · exact Or.inr
      (successor.secondContinuation.support_dropUntil_subset_support hnewFull
        (List.mem_of_mem_tail hsuffix))

/-- Construct the second-to-first reroute at one exhibited collision. -/
noncomputable def secondToFirstReroute
    (collisionFace : SelectedFace (web := web))
    (hold : collisionFace ∈ left.paths.secondRail.support)
    (hnew : collisionFace ∈ successor.firstContinuation.support.tail) :
    SecondToFirstReroute (successor := successor) (left := left)
      collisionFace := by
  let hnewFull : collisionFace ∈ successor.firstContinuation.support :=
    List.mem_of_mem_tail hnew
  let raw :=
    (left.paths.secondRail.takeUntil collisionFace hold).append
      (successor.firstContinuation.dropUntil collisionFace hnewFull)
  refine {
    route := raw.bypass
    route_isPath := raw.bypass_isPath
    route_support_subset := ?_
  }
  intro face hface
  have hraw := raw.support_bypass_subset_support hface
  rw [SimpleGraph.Walk.support_append] at hraw
  rcases List.mem_append.mp hraw with hprefix | hsuffix
  · exact Or.inl
      (left.paths.secondRail.support_takeUntil_subset_support hold hprefix)
  · exact Or.inr
      (successor.firstContinuation.support_dropUntil_subset_support hnewFull
        (List.mem_of_mem_tail hsuffix))

/-- **L1 constructive collision alternative.** Every actual cross-track
collision supplies one of the two literal crossed simple routes. -/
noncomputable def toReroute
    (collision : ActualCrossAppendCollision successor left) :
    Nonempty (FirstToSecondReroute (successor := successor) (left := left)
      collision.face) ∨
    Nonempty (SecondToFirstReroute (successor := successor) (left := left)
      collision.face) := by
  rcases collision.collision with hfirstSecond | hsecondFirst
  · exact Or.inl ⟨firstToSecondReroute collision.face
      hfirstSecond.1 hfirstSecond.2⟩
  · exact Or.inr ⟨secondToFirstReroute collision.face
      hsecondFirst.1 hsecondFirst.2⟩

end SeparatedSelectedSourceLocalRailSuccessor

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
