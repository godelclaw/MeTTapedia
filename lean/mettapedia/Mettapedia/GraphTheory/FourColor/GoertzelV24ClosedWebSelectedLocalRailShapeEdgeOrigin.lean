import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailStepEdgeReceipt
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailShape

/-!
# L1: source origins of canonical selected local rail edges

The canonical `0+2`, `1+1`, and `2+0` local rail constructors are assembled
from selected forward walks, reversal, append, and loop erasure.  Every edge
surviving those operations therefore retains an exact selected forward-step
receipt: two source slots, their cyclic successor relation, the locally cubic
corner, and the literal crossed primal edge.

This is bounded source provenance.  The subsequent separated-rail layer
retains it as a proof-relevant invariant; terminal-window replacement and the
arbitrary-length crosscuts required by L1 remain later obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation

/-- An edge has a literal selected forward-step origin in this placement. -/
def SelectedPlacementForwardEdgeOrigin
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS)))) : Prop :=
  ∃ (left right :
      {position // position ∈ selectedPlacementSidePositions placement}),
    right.1.val ≡ left.1.val + 1 [MOD 6] ∧
      SelectedPlacementSideForwardEdgeReceipt placement left right edge

private theorem selectedPlacementForwardEdgeOrigin_of_walk_edge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left right :
      {position // position ∈ selectedPlacementSidePositions placement})
    (hsuccessor : right.1.val ≡ left.1.val + 1 [MOD 6])
    (walk : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace placement left)
        (selectedPlacementSideFace placement right))
    (hlength : walk.length ≤ 1)
    (edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))))
    (hedge : edge ∈ walk.edges) :
    SelectedPlacementForwardEdgeOrigin placement edge := by
  exact ⟨left, right, hsuccessor,
    selectedPlacementSideForwardEdgeReceipt_of_walk_edge placement left right
      hsuccessor walk hlength edge hedge⟩

/-- Every edge on either rail of a canonical selected local shape retains a
literal selected forward-step origin. -/
theorem selectedSourceLocalRailPathsOfShape_edge_has_forward_origin
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (incomingBefore incomingAfter outgoingBefore outgoingAfter :
      {position // position ∈ selectedPlacementSidePositions placement})
    (shape : SelectedSourceLocalRailShape placement incomingBefore
      incomingAfter outgoingBefore outgoingAfter)
    (edge : Sym2 (AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))))
    (hedge : edge ∈
        (selectedSourceLocalRailPathsOfShape placement incomingBefore
          incomingAfter outgoingBefore outgoingAfter shape).firstRail.edges ∨
      edge ∈
        (selectedSourceLocalRailPathsOfShape placement incomingBefore
          incomingAfter outgoingBefore outgoingAfter shape).secondRail.edges) :
    SelectedPlacementForwardEdgeOrigin placement edge := by
  cases shape with
  | forwardTwo first_eq middle houtMiddle hmiddleIn =>
      let rawFirst :
          (interiorDualGraph (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
              (selectedPlacementSideFace placement incomingBefore)
              (selectedPlacementSideFace placement outgoingBefore) :=
        SimpleGraph.Walk.nil.copy rfl
          (congrArg (selectedPlacementSideFace placement) first_eq)
      let houtWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement outgoingAfter middle houtMiddle
      let outMiddle := Classical.choose houtWitness
      have houtMiddleLength : outMiddle.length ≤ 1 := by
        simpa [outMiddle] using (Classical.choose_spec houtWitness).2
      let hinWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement middle incomingAfter hmiddleIn
      let middleIn := Classical.choose hinWitness
      have hmiddleInLength : middleIn.length ≤ 1 := by
        simpa [middleIn] using (Classical.choose_spec hinWitness).2
      rcases hedge with hfirst | hsecond
      · have hraw : edge ∈ rawFirst.edges := by
          apply rawFirst.edges_bypass_subset_edges
          simpa [selectedSourceLocalRailPathsOfShape, rawFirst, middleIn,
            outMiddle, hinWitness, houtWitness] using hfirst
        simp [rawFirst] at hraw
      · have hraw : edge ∈ (middleIn.reverse.append outMiddle.reverse).edges := by
          apply (middleIn.reverse.append outMiddle.reverse).edges_bypass_subset_edges
          simpa [selectedSourceLocalRailPathsOfShape, middleIn, outMiddle,
            hinWitness, houtWitness] using hsecond
        simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
          List.mem_append, List.mem_reverse] at hraw
        rcases hraw with hin | hout
        · exact selectedPlacementForwardEdgeOrigin_of_walk_edge placement middle
            incomingAfter hmiddleIn middleIn hmiddleInLength edge hin
        · exact selectedPlacementForwardEdgeOrigin_of_walk_edge placement
            outgoingAfter middle houtMiddle outMiddle houtMiddleLength edge hout
  | forwardThree hfirst hsecond =>
      let hfirstWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement incomingBefore outgoingBefore hfirst
      let firstStep := Classical.choose hfirstWitness
      have hfirstLength : firstStep.length ≤ 1 := by
        simpa [firstStep] using (Classical.choose_spec hfirstWitness).2
      let hsecondWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement outgoingAfter incomingAfter hsecond
      let secondStep := Classical.choose hsecondWitness
      have hsecondLength : secondStep.length ≤ 1 := by
        simpa [secondStep] using (Classical.choose_spec hsecondWitness).2
      rcases hedge with hleft | hright
      · have hraw : edge ∈ firstStep.edges := by
          apply firstStep.edges_bypass_subset_edges
          simpa [selectedSourceLocalRailPathsOfShape, firstStep, hfirstWitness]
            using hleft
        exact selectedPlacementForwardEdgeOrigin_of_walk_edge placement
          incomingBefore outgoingBefore hfirst firstStep hfirstLength edge hraw
      · have hraw : edge ∈ secondStep.reverse.edges := by
          apply secondStep.reverse.edges_bypass_subset_edges
          simpa [selectedSourceLocalRailPathsOfShape, secondStep, hsecondWitness]
            using hright
        have hraw' : edge ∈ secondStep.edges := by
          simpa [SimpleGraph.Walk.edges_reverse] using hraw
        exact selectedPlacementForwardEdgeOrigin_of_walk_edge placement
          outgoingAfter incomingAfter hsecond secondStep hsecondLength edge hraw'
  | forwardFour middle hinMiddle hmiddleOut second_eq =>
      let hinWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement incomingBefore middle hinMiddle
      let inMiddle := Classical.choose hinWitness
      have hinMiddleLength : inMiddle.length ≤ 1 := by
        simpa [inMiddle] using (Classical.choose_spec hinWitness).2
      let houtWitness := exists_selectedPlacementSideWalk_of_forwardStep
        (corridor := corridor) placement middle outgoingBefore hmiddleOut
      let middleOut := Classical.choose houtWitness
      have hmiddleOutLength : middleOut.length ≤ 1 := by
        simpa [middleOut] using (Classical.choose_spec houtWitness).2
      let rawSecond :
          (interiorDualGraph (orbitFaceBoundary web.annular.RS)
            (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
              (selectedPlacementSideFace placement incomingAfter)
              (selectedPlacementSideFace placement outgoingAfter) :=
        SimpleGraph.Walk.nil.copy rfl
          (congrArg (selectedPlacementSideFace placement) second_eq)
      rcases hedge with hfirst | hsecond
      · have hraw : edge ∈ (inMiddle.append middleOut).edges := by
          apply (inMiddle.append middleOut).edges_bypass_subset_edges
          simpa [selectedSourceLocalRailPathsOfShape, inMiddle, middleOut,
            hinWitness, houtWitness] using hfirst
        simp only [SimpleGraph.Walk.edges_append, List.mem_append] at hraw
        rcases hraw with hin | hout
        · exact selectedPlacementForwardEdgeOrigin_of_walk_edge placement
            incomingBefore middle hinMiddle inMiddle hinMiddleLength edge hin
        · exact selectedPlacementForwardEdgeOrigin_of_walk_edge placement middle
            outgoingBefore hmiddleOut middleOut hmiddleOutLength edge hout
      · have hraw : edge ∈ rawSecond.edges := by
          apply rawSecond.edges_bypass_subset_edges
          simpa [selectedSourceLocalRailPathsOfShape, rawSecond, inMiddle,
            middleOut, hinWitness, houtWitness] using hsecond
        simp [rawSecond] at hraw

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
