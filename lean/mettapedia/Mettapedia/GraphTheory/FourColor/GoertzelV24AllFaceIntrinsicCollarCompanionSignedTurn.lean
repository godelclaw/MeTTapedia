import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionTransferMonoid

/-! The signed companion change retained by a complementary-coordinate turn. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

namespace ScalarDiscrepancyColorState

variable {coordinate : Bool}

/-- The same ordered pair of actual colors, regarded in the complementary
scalar coordinate whenever it has nonzero complementary discrepancy. -/
def complementCoordinateState
    (state : ScalarDiscrepancyColorState coordinate)
    (hsupport : crossFaceCoordinate (!coordinate)
      (state.sourceColor + state.targetColor) ≠ 0) :
    ScalarDiscrepancyColorState (!coordinate) :=
  ⟨(state.sourceColor, state.targetColor),
    state.sourceColor_ne_zero, state.targetColor_ne_zero,
    (crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor
      (!coordinate) state.sourceColor state.targetColor
      state.sourceColor_ne_zero state.targetColor_ne_zero).1 hsupport⟩

@[simp]
theorem complementCoordinateState_sourceColor
    (state : ScalarDiscrepancyColorState coordinate)
    (hsupport : crossFaceCoordinate (!coordinate)
      (state.sourceColor + state.targetColor) ≠ 0) :
    (state.complementCoordinateState hsupport).sourceColor =
      state.sourceColor := rfl

@[simp]
theorem complementCoordinateState_targetColor
    (state : ScalarDiscrepancyColorState coordinate)
    (hsupport : crossFaceCoordinate (!coordinate)
      (state.sourceColor + state.targetColor) ≠ 0) :
    (state.complementCoordinateState hsupport).targetColor =
      state.targetColor := rfl

/-- If a state also lies in the complementary scalar support, changing
coordinates makes its old distinguished color the new companion. -/
theorem complementCoordinateState_companionColor_eq_zeroColor
    (state : ScalarDiscrepancyColorState coordinate)
    (hsupport : crossFaceCoordinate (!coordinate)
      (state.sourceColor + state.targetColor) ≠ 0) :
    (state.complementCoordinateState hsupport).companionColor =
      crossFaceZeroColor coordinate := by
  have hcompanion : state.companionColor =
      crossFaceZeroColor (!coordinate) :=
    state.complement_support_iff_companion_eq.mp hsupport
  rcases state.source_target_zero_companion_cases with
    hsource | htarget
  · have hsourceNe :
        (state.complementCoordinateState hsupport).sourceColor ≠
          crossFaceZeroColor (!coordinate) := by
      rw [complementCoordinateState_sourceColor, hsource.1]
      exact crossFaceZeroColor_ne_complement coordinate
    calc
      (state.complementCoordinateState hsupport).companionColor =
          (state.complementCoordinateState hsupport).sourceColor :=
        (state.complementCoordinateState hsupport
          |>.companionColor_of_sourceColor_ne hsourceNe)
      _ = state.sourceColor := rfl
      _ = crossFaceZeroColor coordinate := hsource.1
  · have hsourceEq :
        (state.complementCoordinateState hsupport).sourceColor =
          crossFaceZeroColor (!coordinate) := by
      rw [complementCoordinateState_sourceColor, htarget.1,
        hcompanion]
    calc
      (state.complementCoordinateState hsupport).companionColor =
          (state.complementCoordinateState hsupport).targetColor :=
        state.complementCoordinateState hsupport
          |>.companionColor_of_sourceColor_eq hsourceEq
      _ = state.targetColor := rfl
      _ = crossFaceZeroColor coordinate := htarget.2

/-- If the two colors sum to the other coordinate's distinguished color,
then the present companion is not that other distinguished color. -/
theorem companionColor_ne_otherZero_of_source_add_target_eq
    (state : ScalarDiscrepancyColorState (!coordinate))
    (hsum : state.sourceColor + state.targetColor =
      crossFaceZeroColor coordinate) :
    state.companionColor ≠ crossFaceZeroColor coordinate := by
  intro hcompanion
  rcases state.source_target_zero_companion_cases with
    hsource | htarget
  · rw [hsource.1, hsource.2, hcompanion] at hsum
    have hzero : crossFaceZeroColor (!coordinate) = 0 := by
      apply add_right_cancel (b := crossFaceZeroColor coordinate)
      simpa only [zero_add] using hsum
    exact crossFaceZeroColor_ne_zero (!coordinate) hzero
  · rw [htarget.1, htarget.2, hcompanion] at hsum
    have hzero : crossFaceZeroColor (!coordinate) = 0 := by
      apply add_left_cancel (a := crossFaceZeroColor coordinate)
      simpa only [add_zero] using hsum
    exact crossFaceZeroColor_ne_zero (!coordinate) hzero

end ScalarDiscrepancyColorState

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

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

namespace FirstHitSingletonCompanionTransferPath

variable {firstHit : FirstHitSingletonCompanionTransferPath
  (collar := collar) (sourceEscape := sourceEscape)}

namespace TransverseCompanionChange

variable {change : firstHit.TransverseCompanionChange}

namespace ComplementarySupportCorner

variable (corner : change.ComplementarySupportCorner)

/-- The selected incoming edge still carries a state in the original scalar
coordinate. -/
theorem incoming_originalSupport :
    crossFaceCoordinate firstHit.transfer.coordinate
      (collar.sourceCommonColoring sourceEscape corner.incoming +
        collar.targetCommonColoring corner.incoming) ≠ 0 := by
  rcases corner.orientation with ⟨hincoming, _hbypassed⟩ |
      ⟨hincoming, _hbypassed⟩
  · rw [hincoming]
    exact firstHit.transfer.support change.resolved.first.1
      change.resolved.first.2
  · rw [hincoming]
    exact firstHit.transfer.support change.resolved.second.1
      change.resolved.second.2

/-- Original-coordinate state on the selected old support edge. -/
noncomputable def incomingOriginalState :
    ScalarDiscrepancyColorState firstHit.transfer.coordinate :=
  scalarDiscrepancyColorStateOf
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    firstHit.transfer.coordinate corner.incoming
    corner.incoming_originalSupport

/-- Complementary-coordinate state on the same selected incoming edge. -/
noncomputable def incomingComplementState :
    ScalarDiscrepancyColorState (!firstHit.transfer.coordinate) :=
  corner.incomingOriginalState.complementCoordinateState (by
    simpa only [incomingOriginalState,
      scalarDiscrepancyColorStateOf_sourceColor,
      scalarDiscrepancyColorStateOf_targetColor,
      commonDiscrepancy_apply] using corner.incoming_support)

/-- Complementary-coordinate state on the transverse edge emitted by the
original companion change. -/
noncomputable def transverseComplementState :
    ScalarDiscrepancyColorState (!firstHit.transfer.coordinate) :=
  scalarDiscrepancyColorStateOf
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    (!firstHit.transfer.coordinate) change.thirdEdge (by
      simpa only [commonDiscrepancy_apply] using
        change.third_complementSupport)

@[simp]
theorem incomingComplementState_sourceColor :
    corner.incomingComplementState.sourceColor =
      collar.sourceCommonColoring sourceEscape corner.incoming := rfl

@[simp]
theorem incomingComplementState_targetColor :
    corner.incomingComplementState.targetColor =
      collar.targetCommonColoring corner.incoming := rfl

@[simp]
theorem transverseComplementState_sourceColor :
    (transverseComplementState (change := change)).sourceColor =
      collar.sourceCommonColoring sourceEscape change.thirdEdge := rfl

@[simp]
theorem transverseComplementState_targetColor :
    (transverseComplementState (change := change)).targetColor =
      collar.targetCommonColoring change.thirdEdge := rfl

/-- Recoordinating the selected old edge makes the original distinguished
color its companion. -/
theorem incomingComplementState_companionColor_eq :
    corner.incomingComplementState.companionColor =
      crossFaceZeroColor firstHit.transfer.coordinate := by
  exact corner.incomingOriginalState
    |>.complementCoordinateState_companionColor_eq_zeroColor _

/-- The transverse edge has the opposite signed companion behavior. -/
theorem transverseComplementState_companionColor_ne :
    (transverseComplementState (change := change)).companionColor ≠
      crossFaceZeroColor firstHit.transfer.coordinate := by
  apply (transverseComplementState (change := change)
    ).companionColor_ne_otherZero_of_source_add_target_eq
  simpa only [transverseComplementState_sourceColor,
    transverseComplementState_targetColor] using change.discrepancy

/-- The complementary launch is a genuine companion-changing transition,
not merely an ownership flip in the unsigned four-state quotient. -/
theorem incoming_transverse_companionColor_ne :
    corner.incomingComplementState.companionColor ≠
      (transverseComplementState (change := change)).companionColor := by
  rw [corner.incomingComplementState_companionColor_eq]
  exact (transverseComplementState_companionColor_ne
    (change := change)).symm

/-- The two signed launch states are connected by the actual adjacent
common-core edges. -/
theorem incoming_transverse_stateTransition :
    ScalarDiscrepancyColorTransition corner.incomingComplementState
      (transverseComplementState (change := change)) := by
  apply scalarDiscrepancyColorTransition_of_adjacent
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait
    (!firstHit.transfer.coordinate) corner.incoming_third
  · simpa only [commonDiscrepancy_apply] using corner.incoming_support

/-- Exact local signed-turn package at the complementary launch. -/
structure SignedCompanionTurn where
  incomingState : ScalarDiscrepancyColorState
    (!firstHit.transfer.coordinate)
  transverseState : ScalarDiscrepancyColorState
    (!firstHit.transfer.coordinate)
  incomingState_eq : incomingState = corner.incomingComplementState
  transverseState_eq : transverseState =
    transverseComplementState (change := change)
  transition : ScalarDiscrepancyColorTransition
    incomingState transverseState
  companion_ne : incomingState.companionColor ≠
    transverseState.companionColor

/-- Every complementary corner carries its exact nontrivial signed turn. -/
def signedCompanionTurn : corner.SignedCompanionTurn := {
  incomingState := corner.incomingComplementState
  transverseState := transverseComplementState (change := change)
  incomingState_eq := rfl
  transverseState_eq := rfl
  transition := corner.incoming_transverse_stateTransition
  companion_ne := corner.incoming_transverse_companionColor_ne }

end ComplementarySupportCorner
end TransverseCompanionChange
end FirstHitSingletonCompanionTransferPath
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
