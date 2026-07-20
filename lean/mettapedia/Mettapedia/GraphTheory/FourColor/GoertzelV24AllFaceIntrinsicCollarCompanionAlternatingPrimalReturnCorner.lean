import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingPrimalSupportReduction

/-! Exact involutive data at an immediate returning turn boundary. -/

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
  {coordinate : Bool}
  {turn : collar.ScalarCompanionTurn sourceEscape coordinate}

namespace ScalarCompanionTurn.ComplementarySupportCorner

variable (corner : turn.ComplementarySupportCorner)

/-- Toggling a complementary corner changes the coordinate but not its
canonical primal junction. -/
theorem toggleTurn_junction_eq :
    corner.toggleTurn.junction = turn.junction := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
    corner.toggleTurn.firstSecond
  · change turn.junction ∈
      (corner.incoming.1 : Sym2 collar.commonCoreVertex)
    rcases corner.orientation with horientation | horientation
    · rw [horientation.1]
      exact turn.junction_mem_first
    · rw [horientation.1]
      exact turn.junction_mem_second
  · change turn.junction ∈
      (turn.third.1 : Sym2 collar.commonCoreVertex)
    exact turn.junction_mem_third

end ScalarCompanionTurn.ComplementarySupportCorner

namespace ScalarCompanionTurnState.ImmediateReturnBoundary

variable (boundary : ScalarCompanionTurnState.ImmediateReturnBoundary
  (collar := collar) (sourceEscape := sourceEscape))

/-- Same-coordinate turn obtained by toggling at the returning middle
junction. -/
noncomputable def returnTurn :
    collar.ScalarCompanionTurn sourceEscape
      (!boundary.middle.1.coordinate) :=
  boundary.departure.witness.corner.toggleTurn

/-- Finite state of the returning turn. -/
noncomputable def returnState :
    collar.ScalarCompanionTurnState sourceEscape :=
  ScalarCompanionTurnState.ofTurn boundary.returnTurn

/-- Toggling through the canonical return corner once more. -/
noncomputable def doubleReturnTurn :
    collar.ScalarCompanionTurn sourceEscape
      (!(!boundary.middle.1.coordinate)) :=
  boundary.departure.witness.corner.returnCorner.toggleTurn

/-- Finite state after toggling the returning corner twice. -/
noncomputable def doubleReturnState :
    collar.ScalarCompanionTurnState sourceEscape :=
  ScalarCompanionTurnState.ofTurn boundary.doubleReturnTurn

theorem middle_coordinate_eq_not_before :
    boundary.middle.1.coordinate = !boundary.before.1.coordinate := by
  have hcoordinate := congrArg
    (fun state : collar.ScalarCompanionTurnState sourceEscape =>
      state.1.coordinate)
    boundary.arrival.target_eq_ofTurn
  simpa only [ScalarCompanionTurnState.ofTurn_coordinate] using hcoordinate

@[simp]
theorem returnState_coordinate :
    boundary.returnState.1.coordinate = boundary.before.1.coordinate := by
  rw [returnState, ScalarCompanionTurnState.ofTurn_coordinate]
  rw [boundary.middle_coordinate_eq_not_before]
  cases boundary.before.1.coordinate <;> rfl

@[simp]
theorem returnState_junction :
    boundary.returnState.junction = boundary.middle.junction := by
  rw [returnState, ScalarCompanionTurnState.ofTurn_junction]
  exact boundary.departure.witness.corner.toggleTurn_junction_eq

theorem returnState_ne_before :
    boundary.returnState ≠ boundary.before := by
  intro heq
  have hjunction := congrArg ScalarCompanionTurnState.junction heq
  rw [boundary.returnState_junction] at hjunction
  exact boundary.arrival.junction_ne hjunction

@[simp]
theorem returnState_first :
    boundary.returnState.1.first = boundary.middle.1.first := by
  rw [returnState, ScalarCompanionTurnState.ofTurn_first]
  change boundary.departure.witness.corner.incoming =
    boundary.middle.1.first
  exact boundary.departure_corner_orientation.1.trans
    boundary.middle.realizedTurn_first

@[simp]
theorem returnState_second :
    boundary.returnState.1.second = boundary.middle.1.third := by
  rw [returnState, ScalarCompanionTurnState.ofTurn_second]
  change boundary.middle.realizedTurn.third = boundary.middle.1.third
  exact boundary.middle.realizedTurn_third

@[simp]
theorem returnState_third :
    boundary.returnState.1.third = boundary.middle.1.second := by
  rw [returnState, ScalarCompanionTurnState.ofTurn_third]
  change boundary.departure.witness.corner.bypassed =
    boundary.middle.1.second
  exact boundary.departure_corner_orientation.2.trans
    boundary.middle.realizedTurn_second

@[simp]
theorem doubleReturnState_coordinate :
    boundary.doubleReturnState.1.coordinate =
      boundary.middle.1.coordinate := by
  rw [doubleReturnState, ScalarCompanionTurnState.ofTurn_coordinate]
  cases boundary.middle.1.coordinate <;> rfl

@[simp]
theorem doubleReturnState_first :
    boundary.doubleReturnState.1.first = boundary.middle.1.first := by
  rw [doubleReturnState, ScalarCompanionTurnState.ofTurn_first]
  change boundary.departure.witness.corner.incoming =
    boundary.middle.1.first
  exact boundary.departure_corner_orientation.1.trans
    boundary.middle.realizedTurn_first

@[simp]
theorem doubleReturnState_second :
    boundary.doubleReturnState.1.second = boundary.middle.1.second := by
  rw [doubleReturnState, ScalarCompanionTurnState.ofTurn_second]
  change boundary.departure.witness.corner.bypassed =
    boundary.middle.1.second
  exact boundary.departure_corner_orientation.2.trans
    boundary.middle.realizedTurn_second

@[simp]
theorem doubleReturnState_third :
    boundary.doubleReturnState.1.third = boundary.middle.1.third := by
  rw [doubleReturnState, ScalarCompanionTurnState.ofTurn_third]
  change boundary.middle.realizedTurn.third = boundary.middle.1.third
  exact boundary.middle.realizedTurn_third

/-- At finite-state level the local returning-corner toggle is exactly an
involution, with ordered turn data restored rather than merely an unordered
edge pair. -/
theorem doubleReturnState_eq_middle :
    boundary.doubleReturnState = boundary.middle := by
  apply Subtype.ext
  apply Prod.ext
  · exact boundary.doubleReturnState_coordinate
  · apply Prod.ext
    · exact boundary.doubleReturnState_first
    · apply Prod.ext
      · exact boundary.doubleReturnState_second
      · exact boundary.doubleReturnState_third

end ScalarCompanionTurnState.ImmediateReturnBoundary
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
