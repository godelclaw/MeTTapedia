import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleCollisionRepair

/-!
# L1: deterministic clearance in the parity-matched middle repairs

The canonical middle repair already supplies a rail avoiding any actual
collision face.  The exact source-track receipt sharpens half of the finite
table: when the repair's endpoint parity matches the collision pairing, the
opposite repaired rail is forced to avoid the face.  The proof uses only the
two input rail separations and the connector-free track membership established
for an actual collision face.

The four parity-mismatched cases still carry only the existing disjunctive
clear-rail certificate.  This module does not construct the outer four-cell
reroute, eliminate the other collision bands, iterate a corridor, attach end
caps, construct separated crosscuts, or close Fable flag L1.
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

/-- In a straight repair, a first/first collision forces the repaired second
rail to avoid the collision face. -/
theorem ExactSelectedLocalRailConstructionTrace.straight_secondRail_avoids_firstFirst
    (trace : ExactSelectedLocalRailConstructionTrace successor left)
    (collision :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left)
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
    (hresult : trace.toOutcome = .straight assembly)
    (hcollision : collision.face ∈ left.paths.firstRail.support ∧
      collision.face ∈ successor.firstContinuation.support.tail) :
    collision.face ∉ assembly.secondRail.support := by
  have htracks := trace.collisionFaceFollowsExpectedTracks collision
  rw [hresult] at htracks
  intro hface
  rcases htracks.2 hface with hold | hnew
  · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      hcollision.1) hold
  · exact (List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
      (List.mem_of_mem_tail hcollision.2)) hnew

/-- In a straight repair, a second/second collision forces the repaired first
rail to avoid the collision face. -/
theorem ExactSelectedLocalRailConstructionTrace.straight_firstRail_avoids_secondSecond
    (trace : ExactSelectedLocalRailConstructionTrace successor left)
    (collision :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left)
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
    (hresult : trace.toOutcome = .straight assembly)
    (hcollision : collision.face ∈ left.paths.secondRail.support ∧
      collision.face ∈ successor.secondContinuation.support.tail) :
    collision.face ∉ assembly.firstRail.support := by
  have htracks := trace.collisionFaceFollowsExpectedTracks collision
  rw [hresult] at htracks
  intro hface
  rcases htracks.1 hface with hold | hnew
  · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      hold) hcollision.1
  · exact (List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
      hnew) (List.mem_of_mem_tail hcollision.2)

/-- In a swapped repair, a first/second collision forces the repaired second
rail to avoid the collision face. -/
theorem ExactSelectedLocalRailConstructionTrace.swapped_secondRail_avoids_firstSecond
    (trace : ExactSelectedLocalRailConstructionTrace successor left)
    (collision :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left)
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))
    (hresult : trace.toOutcome = .swapped assembly)
    (hcollision : collision.face ∈ left.paths.firstRail.support ∧
      collision.face ∈ successor.secondContinuation.support.tail) :
    collision.face ∉ assembly.secondRail.support := by
  have htracks := trace.collisionFaceFollowsExpectedTracks collision
  rw [hresult] at htracks
  intro hface
  rcases htracks.2 hface with hold | hnew
  · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      hcollision.1) hold
  · exact (List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
      hnew) (List.mem_of_mem_tail hcollision.2)

/-- In a swapped repair, a second/first collision forces the repaired first
rail to avoid the collision face. -/
theorem ExactSelectedLocalRailConstructionTrace.swapped_firstRail_avoids_secondFirst
    (trace : ExactSelectedLocalRailConstructionTrace successor left)
    (collision :
      SeparatedSelectedSourceLocalRailSuccessor.ActualAppendCollision
        successor left)
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
      (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))
    (hresult : trace.toOutcome = .swapped assembly)
    (hcollision : collision.face ∈ left.paths.secondRail.support ∧
      collision.face ∈ successor.firstContinuation.support.tail) :
    collision.face ∉ assembly.firstRail.support := by
  have htracks := trace.collisionFaceFollowsExpectedTracks collision
  rw [hresult] at htracks
  intro hface
  rcases htracks.1 hface with hold | hnew
  · exact (List.disjoint_left.mp left.firstRail_support_disjoint_secondRail
      hold) hcollision.1
  · exact (List.disjoint_left.mp
      successor.firstContinuation_support_disjoint_secondContinuation
      (List.mem_of_mem_tail hcollision.2)) hnew

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
