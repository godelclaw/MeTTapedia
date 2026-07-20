import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingPrimalReturnRoute

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

namespace ScalarCompanionTurnState.ImmediateReturnBoundary

variable (boundary : ScalarCompanionTurnState.ImmediateReturnBoundary
  (collar := collar) (sourceEscape := sourceEscape))

/-- Forgetting the transported support predicate turns the forward prefix
back into the literal common-core edge word of the arrival arc. -/
theorem arrivalForwardPrefix_map_eq_arrivalEdgeWord :
    boundary.arrivalForwardPrefix.map
        boundary.returnCorner.supportEdgeAmbientEdge =
      boundary.arrival.path.edgeSubtypeSupport := by
  unfold arrivalForwardPrefix
  rw [boundary.arrivalCycleInReturnGraph_takeUntil_edgeSubtypeSupport,
    List.map_map]
  calc
    boundary.arrival.witness.interior.straightEdgeWord.map
          (fun edge => boundary.returnCorner.supportEdgeAmbientEdge
            (boundary.arrivalSupportEdgeInReturnGraph edge)) =
        boundary.arrival.witness.interior.straightEdgeWord.map
          boundary.arrival.witness.corner.supportEdgeAmbientEdge := by
      apply List.map_congr_left
      intro edge _hedge
      exact boundary.returnCorner_supportEdgeAmbientEdge_transport edge
    _ = boundary.arrival.witness.interior.primalArc.edgeSubtypeSupport := by
      rw [boundary.arrival.witness.interior.primalArc_edgeSubtypeSupport,
        boundary.arrival.witness.interior.supportArc_edgeSubtypeSupport]
    _ = boundary.arrival.path.edgeSubtypeSupport :=
      boundary.arrival.path_edgeSubtypeSupport_eq_witness.symm

/-- Any certified reverse first turn traverses exactly the reversed common-core
edge word of the forward arrival arc. -/
theorem reversedFirstTurn_primalArc_edgeWord
    (firstTurn : boundary.reversedArrivalRoute.FirstInteriorTransverseTurn)
    (hstraight : firstTurn.straightEdgeWord =
      boundary.arrivalForwardPrefix.reverse) :
    firstTurn.primalArc.edgeSubtypeSupport =
      boundary.arrival.path.edgeSubtypeSupport.reverse := by
  rw [firstTurn.primalArc_edgeSubtypeSupport,
    firstTurn.supportArc_edgeSubtypeSupport, hstraight,
    List.map_reverse,
    boundary.arrivalForwardPrefix_map_eq_arrivalEdgeWord]

/-- The complete two-sided datum at an immediate return: an exact finite
transition whose geometric representative is the literal reverse arrival
arc. -/
structure ExactReverseArrivalLens where
  firstTurn : boundary.reversedArrivalRoute.FirstInteriorTransverseTurn
  exactNext : boundary.returnState.IsExactNext
    (boundary.reverseTargetState firstTurn)
  finishJunction_eq_before :
    firstTurn.finishJunction = boundary.before.junction
  turnPosition_eq_arrival :
    firstTurn.turnPosition =
      boundary.arrival.witness.interior.turnPosition
  straightEdgeWord_eq_reverse :
    firstTurn.straightEdgeWord = boundary.arrivalForwardPrefix.reverse
  primalArc_edgeWord_eq_reverse :
    firstTurn.primalArc.edgeSubtypeSupport =
      boundary.arrival.path.edgeSubtypeSupport.reverse
  primalArc_length_eq_arrival :
    firstTurn.primalArc.length = boundary.arrival.path.length

/-- Every immediate-return boundary carries an exact reverse arrival lens. -/
theorem nonempty_exactReverseArrivalLens :
    Nonempty boundary.ExactReverseArrivalLens := by
  rcases boundary.exists_reversedArrivalFirstTurn_finish_eq_before with
    ⟨firstTurn, hfinish, hposition, hstraight⟩
  have hedgeWord := boundary.reversedFirstTurn_primalArc_edgeWord
    firstTurn hstraight
  have hlength : firstTurn.primalArc.length =
      boundary.arrival.path.length := by
    calc
      firstTurn.primalArc.length =
          firstTurn.primalArc.edgeSubtypeSupport.length :=
        firstTurn.primalArc.edgeSubtypeSupport_length.symm
      _ = boundary.arrival.path.edgeSubtypeSupport.reverse.length :=
        congrArg List.length hedgeWord
      _ = boundary.arrival.path.edgeSubtypeSupport.length :=
        List.length_reverse
      _ = boundary.arrival.path.length :=
        boundary.arrival.path.edgeSubtypeSupport_length
  exact ⟨{
    firstTurn := firstTurn
    exactNext :=
      boundary.returnState_isExactNext_reverseTargetState firstTurn
    finishJunction_eq_before := hfinish
    turnPosition_eq_arrival := hposition
    straightEdgeWord_eq_reverse := hstraight
    primalArc_edgeWord_eq_reverse := hedgeWord
    primalArc_length_eq_arrival := hlength }⟩

namespace ExactReverseArrivalLens

variable (lens : boundary.ExactReverseArrivalLens)

/-- The reverse geometric arc with endpoints normalized to the middle and
predecessor finite-state junctions. -/
noncomputable def reversePath :
    collar.commonCore.Walk boundary.middle.junction
      boundary.before.junction :=
  lens.firstTurn.primalArc.copy (by
    calc
      boundary.returnTurn.junction = boundary.returnState.junction := by
        rw [returnState, ScalarCompanionTurnState.ofTurn_junction]
      _ = boundary.middle.junction := boundary.returnState_junction)
    (lens.firstTurn.toScalarCompanionTurn_junction_eq_finishJunction.trans
      lens.finishJunction_eq_before)

/-- Endpoint normalization preserves the exact reversed edge word. -/
theorem reversePath_edgeWord :
    lens.reversePath.edgeSubtypeSupport =
      boundary.arrival.path.edgeSubtypeSupport.reverse := by
  rw [reversePath,
    GoertzelV24AlternatingPrimalReturn.edgeSubtypeSupport_copy]
  exact lens.primalArc_edgeWord_eq_reverse

/-- The normalized reverse path is the reverse of the arrival walk itself,
not merely a walk with the same unoriented support. -/
theorem reversePath_eq_arrival_reverse :
    lens.reversePath = boundary.arrival.path.reverse := by
  apply SimpleGraph.Walk.edges_injective
  rw [← lens.reversePath.edgeSubtypeSupport_map_val,
    lens.reversePath_edgeWord, List.map_reverse,
    boundary.arrival.path.edgeSubtypeSupport_map_val,
    SimpleGraph.Walk.edges_reverse]

/-- Closed palindromic common-core walk underlying the immediate-return
lens. -/
noncomputable def closedWalk :
    collar.commonCore.Walk boundary.before.junction
      boundary.before.junction :=
  boundary.arrival.path.append lens.reversePath

theorem closedWalk_eq_arrival_append_reverse :
    lens.closedWalk =
      boundary.arrival.path.append boundary.arrival.path.reverse := by
  rw [closedWalk, lens.reversePath_eq_arrival_reverse]

theorem closedWalk_edgeWord :
    lens.closedWalk.edgeSubtypeSupport =
      boundary.arrival.path.edgeSubtypeSupport ++
        boundary.arrival.path.edgeSubtypeSupport.reverse := by
  rw [lens.closedWalk_eq_arrival_append_reverse,
    GoertzelV24AlternatingPrimalReturn.edgeSubtypeSupport_append,
    GoertzelV24AlternatingPrimalReturn.edgeSubtypeSupport_reverse]

@[simp]
theorem reversePath_length :
    lens.reversePath.length = boundary.arrival.path.length := by
  rw [lens.reversePath_eq_arrival_reverse,
    SimpleGraph.Walk.length_reverse]

@[simp]
theorem closedWalk_length :
    lens.closedWalk.length = 2 * boundary.arrival.path.length := by
  rw [lens.closedWalk_eq_arrival_append_reverse,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

theorem closedWalk_not_nil : ¬ lens.closedWalk.Nil := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
  rw [lens.closedWalk_length]
  exact Nat.mul_pos (by omega) boundary.arrival.path_positive

end ExactReverseArrivalLens

end ScalarCompanionTurnState.ImmediateReturnBoundary
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
