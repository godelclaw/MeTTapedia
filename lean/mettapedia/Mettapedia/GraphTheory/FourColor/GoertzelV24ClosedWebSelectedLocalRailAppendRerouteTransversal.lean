import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendReroute
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversal

/-!
# L1: selected primal crossings on a collision reroute

Every literal collision reroute is already a simple facial-dual path.  The
selected-transversal API therefore chooses one actual shared primal edge at
each of its dual steps, without any global unique-shared-edge premise.

These are local corridor fragments: their endpoints are selected side faces,
not the two named annular hole faces.  This adapter does not construct the
second disjoint fragment, attach either end cap, or claim the C-5 crosscut
pair.
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
open GoertzelV24SelectedDualPathTransversal

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

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

namespace SeparatedSelectedSourceLocalRailSuccessor.FirstToSecondReroute

/-- Equip the simple first-to-second reroute with one literal primal crossing
edge at every dual step. -/
noncomputable def toSelectedTransversal
    {collisionFace :
      AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (reroute : FirstToSecondReroute (successor := successor) (left := left)
      collisionFace) :
    SelectedDualPathTransversal (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingAfter) :=
  SelectedDualPathTransversal.ofCrosscut {
    walk := reroute.route
    isPath := reroute.route_isPath
  }

end SeparatedSelectedSourceLocalRailSuccessor.FirstToSecondReroute

namespace SeparatedSelectedSourceLocalRailSuccessor.SecondToFirstReroute

/-- Equip the simple second-to-first reroute with one literal primal crossing
edge at every dual step. -/
noncomputable def toSelectedTransversal
    {collisionFace :
      AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (reroute : SecondToFirstReroute (successor := successor) (left := left)
      collisionFace) :
    SelectedDualPathTransversal (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement
        successor.rightOutgoingBefore) :=
  SelectedDualPathTransversal.ofCrosscut {
    walk := reroute.route
    isPath := reroute.route_isPath
  }

end SeparatedSelectedSourceLocalRailSuccessor.SecondToFirstReroute

namespace SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision

/-- **L1 selected-reroute alternative.** An actual cross-track collision
constructs a selected simple transversal fragment to one of the two opposite
outgoing endpoints. -/
noncomputable def toSelectedReroute
    (collision : ActualCrossAppendCollision successor left) :
    Nonempty
        (SelectedDualPathTransversal (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))
          (selectedPlacementSideFace leftPlacement leftIncomingBefore)
          (selectedPlacementSideFace rightPlacement
            successor.rightOutgoingAfter)) ∨
      Nonempty
        (SelectedDualPathTransversal (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))
          (selectedPlacementSideFace leftPlacement leftIncomingAfter)
          (selectedPlacementSideFace rightPlacement
            successor.rightOutgoingBefore)) := by
  rcases SeparatedSelectedSourceLocalRailSuccessor.toReroute collision with
    reroute | reroute
  · rcases reroute with ⟨reroute⟩
    exact Or.inl ⟨reroute.toSelectedTransversal⟩
  · rcases reroute with ⟨reroute⟩
    exact Or.inr ⟨reroute.toSelectedTransversal⟩

end SeparatedSelectedSourceLocalRailSuccessor.ActualCrossAppendCollision

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
