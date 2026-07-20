import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarFirstHitCompanionTransfer

/-! Complementary-coordinate turns at singleton companion changes. -/

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

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- The two scalar coordinates have different distinguished nonzero
zero-coordinate colors. -/
theorem crossFaceZeroColor_ne_complement (coordinate : Bool) :
    crossFaceZeroColor coordinate ≠ crossFaceZeroColor (!coordinate) := by
  cases coordinate <;>
    simp [crossFaceZeroColor, red, blue]

/-- A distinguished zero-coordinate color is nonzero in the complementary
coordinate. -/
theorem crossFaceCoordinate_complement_zeroColor_ne_zero
    (coordinate : Bool) :
    crossFaceCoordinate (!coordinate) (crossFaceZeroColor coordinate) ≠ 0 := by
  cases coordinate <;>
    simp [crossFaceZeroColor, crossFaceCoordinate, red, blue]

namespace ScalarDiscrepancyColorState

/-- A scalar-support state lies in the complementary scalar support exactly
when its companion is the complementary distinguished color. -/
theorem complement_support_iff_companion_eq
    {coordinate : Bool} (state : ScalarDiscrepancyColorState coordinate) :
    crossFaceCoordinate (!coordinate)
          (state.sourceColor + state.targetColor) ≠ 0 ↔
      state.companionColor = crossFaceZeroColor (!coordinate) := by
  have hzeroNe : crossFaceZeroColor coordinate ≠
      crossFaceZeroColor (!coordinate) :=
    crossFaceZeroColor_ne_complement coordinate
  rw [crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor
    (!coordinate) state.sourceColor state.targetColor
    state.sourceColor_ne_zero state.targetColor_ne_zero]
  rcases state.source_target_zero_companion_cases with
    ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · rw [hsource, htarget]
    simp [hzeroNe]
  · rw [hsource, htarget]
    simp [hzeroNe]

end ScalarDiscrepancyColorState

/-- Two distinct nonzero colors, both different from one distinguished
color, contain the complementary distinguished color exactly once. -/
theorem exactlyOne_eq_complementZeroColor
    (coordinate : Bool) {first second : Color}
    (hfirstZero : first ≠ 0) (hsecondZero : second ≠ 0)
    (hfirstDistinguished : first ≠ crossFaceZeroColor coordinate)
    (hsecondDistinguished : second ≠ crossFaceZeroColor coordinate)
    (hfirstSecond : first ≠ second) :
    (first = crossFaceZeroColor (!coordinate) ∧
        second ≠ crossFaceZeroColor (!coordinate)) ∨
      (first ≠ crossFaceZeroColor (!coordinate) ∧
        second = crossFaceZeroColor (!coordinate)) := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero first hfirstZero with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero second hsecondZero with
      rfl | rfl | rfl <;>
      cases coordinate <;>
        simp [crossFaceZeroColor, red, blue, purple] at *

/-- At a companion change, exactly one of the two old scalar-support edges
belongs to the complementary coordinate. -/
theorem exactlyOne_complementSupport_of_companion_ne
    {coordinate : Bool}
    (first second : ScalarDiscrepancyColorState coordinate)
    (hcompanion : first.companionColor ≠ second.companionColor) :
    (crossFaceCoordinate (!coordinate)
          (first.sourceColor + first.targetColor) ≠ 0 ∧
        crossFaceCoordinate (!coordinate)
          (second.sourceColor + second.targetColor) = 0) ∨
      (crossFaceCoordinate (!coordinate)
          (first.sourceColor + first.targetColor) = 0 ∧
        crossFaceCoordinate (!coordinate)
          (second.sourceColor + second.targetColor) ≠ 0) := by
  have hcompanions := exactlyOne_eq_complementZeroColor coordinate
    first.companionColor_ne_zero second.companionColor_ne_zero
    first.companionColor_ne_zeroColor second.companionColor_ne_zeroColor
    hcompanion
  rcases hcompanions with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · apply Or.inl
    refine ⟨first.complement_support_iff_companion_eq.mpr hfirst, ?_⟩
    by_contra hsupport
    exact hsecond
      (second.complement_support_iff_companion_eq.mp hsupport)
  · apply Or.inr
    refine ⟨?_, second.complement_support_iff_companion_eq.mpr hsecond⟩
    by_contra hsupport
    exact hfirst
      (first.complement_support_iff_companion_eq.mp hsupport)

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
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

/-- A common-core edge with nonzero selected discrepancy, regarded as an
edge of the corresponding scalar support graph. -/
def coordinateDiscrepancySupportEdge
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) (edge : collar.commonCore.edgeSet)
    (hsupport : crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape edge) ≠ 0) :
    (collar.coordinateDiscrepancySupportGraph
      sourceEscape coordinate).edgeSet :=
  ⟨edge.1,
    (ambientEdge_mem_scalarSupportGraph_edgeSet_iff
      (fun current => crossFaceCoordinate coordinate
        (collar.commonDiscrepancy sourceEscape current)) edge).2 hsupport⟩

@[simp]
theorem coordinateDiscrepancySupportEdge_val
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) (edge : collar.commonCore.edgeSet)
    (hsupport : crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape edge) ≠ 0) :
    (collar.coordinateDiscrepancySupportEdge sourceEscape coordinate edge
      hsupport).1 = edge.1 := rfl

/-- Adjacency of selected common-core edges is preserved when both are
viewed inside the scalar support graph. -/
theorem coordinateDiscrepancySupportEdge_lineGraph_adj
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) {first second : collar.commonCore.edgeSet}
    (hfirst : crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape first) ≠ 0)
    (hsecond : crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape second) ≠ 0)
    (hadjacent : collar.commonCore.lineGraph.Adj first second) :
    (collar.coordinateDiscrepancySupportGraph sourceEscape coordinate).lineGraph.Adj
      (collar.coordinateDiscrepancySupportEdge
        sourceEscape coordinate first hfirst)
      (collar.coordinateDiscrepancySupportEdge
        sourceEscape coordinate second hsecond) := by
  rcases SimpleGraph.lineGraph_adj_iff_exists.mp hadjacent with
    ⟨hne, vertex, hfirstVertex, hsecondVertex⟩
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨?_, vertex, ?_, ?_⟩
  · intro heq
    apply hne
    apply Subtype.ext
    have hvalues := congrArg
      (fun supportEdge :
        (collar.coordinateDiscrepancySupportGraph
          sourceEscape coordinate).edgeSet => supportEdge.1) heq
    simpa only [coordinateDiscrepancySupportEdge_val] using hvalues
  · simpa only [coordinateDiscrepancySupportEdge_val] using hfirstVertex
  · simpa only [coordinateDiscrepancySupportEdge_val] using hsecondVertex

namespace FirstHitSingletonCompanionTransferPath

variable {firstHit : FirstHitSingletonCompanionTransferPath
  (collar := collar) (sourceEscape := sourceEscape)}

namespace TransverseCompanionChange

variable (change : firstHit.TransverseCompanionChange)

/-- The transverse edge is a genuine support edge for the complementary
scalar coordinate. -/
theorem third_complementSupport :
    crossFaceCoordinate (!firstHit.transfer.coordinate)
        (collar.sourceCommonColoring sourceEscape change.thirdEdge +
          collar.targetCommonColoring change.thirdEdge) ≠ 0 := by
  rw [change.discrepancy]
  exact crossFaceCoordinate_complement_zeroColor_ne_zero
    firstHit.transfer.coordinate

/-- Exactly one incoming edge at a transverse change continues in the
complementary scalar support. -/
theorem exactlyOne_first_second_complementSupport :
    (crossFaceCoordinate (!firstHit.transfer.coordinate)
          (collar.sourceCommonColoring sourceEscape
              change.resolved.first.1 +
            collar.targetCommonColoring change.resolved.first.1) ≠ 0 ∧
        crossFaceCoordinate (!firstHit.transfer.coordinate)
          (collar.sourceCommonColoring sourceEscape
              change.resolved.second.1 +
            collar.targetCommonColoring change.resolved.second.1) = 0) ∨
      (crossFaceCoordinate (!firstHit.transfer.coordinate)
          (collar.sourceCommonColoring sourceEscape
              change.resolved.first.1 +
            collar.targetCommonColoring change.resolved.first.1) = 0 ∧
        crossFaceCoordinate (!firstHit.transfer.coordinate)
          (collar.sourceCommonColoring sourceEscape
              change.resolved.second.1 +
            collar.targetCommonColoring change.resolved.second.1) ≠ 0) := by
  simpa only [SingletonCompanionTransferPath.supportEdgeState_sourceColor,
    SingletonCompanionTransferPath.supportEdgeState_targetColor] using
      exactlyOne_complementSupport_of_companion_ne
        (firstHit.transfer.supportEdgeState change.resolved.first)
        (firstHit.transfer.supportEdgeState change.resolved.second)
        change.resolved.companion_ne

/-- At a transverse change the source and target colorings differ by one
of the two exact cyclic rotations of the three colors at the cubic junction.
The transverse edge carries the old companion on one side and the new
companion on the other. -/
theorem localColorRotation :
    (collar.sourceCommonColoring sourceEscape change.resolved.first.1 =
          crossFaceZeroColor firstHit.transfer.coordinate ∧
        collar.targetCommonColoring change.resolved.first.1 =
          (firstHit.transfer.supportEdgeState
            change.resolved.first).companionColor ∧
        collar.sourceCommonColoring sourceEscape change.resolved.second.1 =
          (firstHit.transfer.supportEdgeState
            change.resolved.second).companionColor ∧
        collar.targetCommonColoring change.resolved.second.1 =
          crossFaceZeroColor firstHit.transfer.coordinate ∧
        collar.sourceCommonColoring sourceEscape change.thirdEdge =
          (firstHit.transfer.supportEdgeState
            change.resolved.first).companionColor ∧
        collar.targetCommonColoring change.thirdEdge =
          (firstHit.transfer.supportEdgeState
            change.resolved.second).companionColor) ∨
      (collar.sourceCommonColoring sourceEscape change.resolved.first.1 =
          (firstHit.transfer.supportEdgeState
            change.resolved.first).companionColor ∧
        collar.targetCommonColoring change.resolved.first.1 =
          crossFaceZeroColor firstHit.transfer.coordinate ∧
        collar.sourceCommonColoring sourceEscape change.resolved.second.1 =
          crossFaceZeroColor firstHit.transfer.coordinate ∧
        collar.targetCommonColoring change.resolved.second.1 =
          (firstHit.transfer.supportEdgeState
            change.resolved.second).companionColor ∧
        collar.sourceCommonColoring sourceEscape change.thirdEdge =
          (firstHit.transfer.supportEdgeState
            change.resolved.second).companionColor ∧
        collar.targetCommonColoring change.thirdEdge =
          (firstHit.transfer.supportEdgeState
            change.resolved.first).companionColor) := by
  let firstState :=
    firstHit.transfer.supportEdgeState change.resolved.first
  let secondState :=
    firstHit.transfer.supportEdgeState change.resolved.second
  have htransition :
      ScalarDiscrepancyColorTransition firstState secondState := by
    simpa only [firstState, secondState,
      SingletonCompanionTransferPath.supportEdgeState,
      SingletonCompanionTransferPath.stateOfEdge] using
        scalarDiscrepancyColorTransition_of_adjacent
          (collar.sourceCommonColoring sourceEscape)
          collar.targetCommonColoring
          (collar.sourceCommonColoring_isTait sourceEscape)
          collar.targetCommonColoring_isTait
          firstHit.transfer.coordinate change.resolved.firstSecond
          (firstHit.transfer.support change.resolved.first.1
            change.resolved.first.2)
          (firstHit.transfer.support change.resolved.second.1
            change.resolved.second.2)
  have hcompanion : firstState.companionColor ≠
      secondState.companionColor := by
    simpa only [firstState, secondState] using change.resolved.companion_ne
  have hcompanionSum : firstState.companionColor +
      secondState.companionColor =
        crossFaceZeroColor firstHit.transfer.coordinate := by
    have hemitted :=
      scalarDiscrepancyTransverseEmission_eq_zeroColor_of_companion_ne
        htransition hcompanion
    rw [scalarDiscrepancyTransverseEmission_eq_companion_add
      htransition] at hemitted
    exact hemitted
  have hsourceThird :
      collar.sourceCommonColoring sourceEscape change.thirdEdge =
        collar.sourceCommonColoring sourceEscape change.resolved.first.1 +
          collar.sourceCommonColoring sourceEscape
            change.resolved.second.1 :=
    color_eq_add_of_three_distinct_nonzero
      (collar.sourceCommonColoring_isTait sourceEscape change.thirdEdge)
      (collar.sourceCommonColoring_isTait sourceEscape
        change.resolved.first.1)
      (collar.sourceCommonColoring_isTait sourceEscape
        change.resolved.second.1)
      ((collar.sourceCommonColoring sourceEscape).valid
        change.firstThird).symm
      ((collar.sourceCommonColoring sourceEscape).valid
        change.secondThird).symm
      ((collar.sourceCommonColoring sourceEscape).valid
        change.resolved.firstSecond)
  have htargetThird :
      collar.targetCommonColoring change.thirdEdge =
        collar.targetCommonColoring change.resolved.first.1 +
          collar.targetCommonColoring change.resolved.second.1 :=
    color_eq_add_of_three_distinct_nonzero
      (collar.targetCommonColoring_isTait change.thirdEdge)
      (collar.targetCommonColoring_isTait change.resolved.first.1)
      (collar.targetCommonColoring_isTait change.resolved.second.1)
      (collar.targetCommonColoring.valid change.firstThird).symm
      (collar.targetCommonColoring.valid change.secondThird).symm
      (collar.targetCommonColoring.valid change.resolved.firstSecond)
  rcases htransition with hsourceTarget | htargetSource
  · have hfirstTarget : firstState.targetColor =
        firstState.companionColor :=
      (firstState.companionColor_of_sourceColor_eq
        hsourceTarget.1).symm
    have hsecondSource : secondState.sourceColor =
        secondState.companionColor :=
      (secondState.companionColor_of_sourceColor_ne
        (secondState.sourceColor_ne_zeroColor_of_targetColor_eq
          hsourceTarget.2)).symm
    apply Or.inl
    refine ⟨by simpa only [firstState,
          SingletonCompanionTransferPath.supportEdgeState_sourceColor] using
        hsourceTarget.1,
      by simpa only [firstState,
          SingletonCompanionTransferPath.supportEdgeState_targetColor] using
        hfirstTarget,
      by simpa only [secondState,
          SingletonCompanionTransferPath.supportEdgeState_sourceColor] using
        hsecondSource,
      by simpa only [secondState,
          SingletonCompanionTransferPath.supportEdgeState_targetColor] using
        hsourceTarget.2, ?_, ?_⟩
    · calc
        collar.sourceCommonColoring sourceEscape change.thirdEdge =
            collar.sourceCommonColoring sourceEscape
                change.resolved.first.1 +
              collar.sourceCommonColoring sourceEscape
                change.resolved.second.1 := hsourceThird
        _ = firstState.sourceColor + secondState.sourceColor := rfl
        _ = crossFaceZeroColor firstHit.transfer.coordinate +
              secondState.companionColor := by
            rw [hsourceTarget.1, hsecondSource]
        _ = firstState.companionColor := by
            rw [← hcompanionSum, add_assoc, color_add_self, add_zero]
    · calc
        collar.targetCommonColoring change.thirdEdge =
            collar.targetCommonColoring change.resolved.first.1 +
              collar.targetCommonColoring change.resolved.second.1 :=
          htargetThird
        _ = firstState.targetColor + secondState.targetColor := rfl
        _ = firstState.companionColor +
              crossFaceZeroColor firstHit.transfer.coordinate := by
            rw [hfirstTarget, hsourceTarget.2]
        _ = secondState.companionColor := by
            rw [← hcompanionSum, ← add_assoc, color_add_self, zero_add]
  · have hfirstSource : firstState.sourceColor =
        firstState.companionColor :=
      (firstState.companionColor_of_sourceColor_ne
        (firstState.sourceColor_ne_zeroColor_of_targetColor_eq
          htargetSource.1)).symm
    have hsecondTarget : secondState.targetColor =
        secondState.companionColor :=
      (secondState.companionColor_of_sourceColor_eq
        htargetSource.2).symm
    apply Or.inr
    refine ⟨by simpa only [firstState,
          SingletonCompanionTransferPath.supportEdgeState_sourceColor] using
        hfirstSource,
      by simpa only [firstState,
          SingletonCompanionTransferPath.supportEdgeState_targetColor] using
        htargetSource.1,
      by simpa only [secondState,
          SingletonCompanionTransferPath.supportEdgeState_sourceColor] using
        htargetSource.2,
      by simpa only [secondState,
          SingletonCompanionTransferPath.supportEdgeState_targetColor] using
        hsecondTarget, ?_, ?_⟩
    · calc
        collar.sourceCommonColoring sourceEscape change.thirdEdge =
            collar.sourceCommonColoring sourceEscape
                change.resolved.first.1 +
              collar.sourceCommonColoring sourceEscape
                change.resolved.second.1 := hsourceThird
        _ = firstState.sourceColor + secondState.sourceColor := rfl
        _ = firstState.companionColor +
              crossFaceZeroColor firstHit.transfer.coordinate := by
            rw [hfirstSource, htargetSource.2]
        _ = secondState.companionColor := by
            rw [← hcompanionSum, ← add_assoc, color_add_self, zero_add]
    · calc
        collar.targetCommonColoring change.thirdEdge =
            collar.targetCommonColoring change.resolved.first.1 +
              collar.targetCommonColoring change.resolved.second.1 :=
          htargetThird
        _ = firstState.targetColor + secondState.targetColor := rfl
        _ = crossFaceZeroColor firstHit.transfer.coordinate +
              secondState.companionColor := by
            rw [htargetSource.1, hsecondTarget]
        _ = firstState.companionColor := by
            rw [← hcompanionSum, add_assoc, color_add_self, add_zero]

/-- A companion change is therefore a degree-two turn in the complementary
coordinate: one old edge and the transverse edge carry that coordinate,
while the other old edge does not. -/
structure ComplementaryCoordinateTurn where
  first_second :
    (crossFaceCoordinate (!firstHit.transfer.coordinate)
          (collar.sourceCommonColoring sourceEscape
              change.resolved.first.1 +
            collar.targetCommonColoring change.resolved.first.1) ≠ 0 ∧
        crossFaceCoordinate (!firstHit.transfer.coordinate)
          (collar.sourceCommonColoring sourceEscape
              change.resolved.second.1 +
            collar.targetCommonColoring change.resolved.second.1) = 0) ∨
      (crossFaceCoordinate (!firstHit.transfer.coordinate)
          (collar.sourceCommonColoring sourceEscape
              change.resolved.first.1 +
            collar.targetCommonColoring change.resolved.first.1) = 0 ∧
        crossFaceCoordinate (!firstHit.transfer.coordinate)
          (collar.sourceCommonColoring sourceEscape
              change.resolved.second.1 +
            collar.targetCommonColoring change.resolved.second.1) ≠ 0)
  third_support :
    crossFaceCoordinate (!firstHit.transfer.coordinate)
        (collar.sourceCommonColoring sourceEscape change.thirdEdge +
          collar.targetCommonColoring change.thirdEdge) ≠ 0

/-- Every transverse companion change constructs its complementary-coordinate
turn without an additional choice or hypothesis. -/
def complementaryCoordinateTurn : change.ComplementaryCoordinateTurn := {
  first_second := change.exactlyOne_first_second_complementSupport
  third_support := change.third_complementSupport }

/-- The graph-level complementary corner selects the unique old edge that
continues through the transverse edge and records the bypassed old edge. -/
structure ComplementarySupportCorner where
  incoming : collar.commonCore.edgeSet
  bypassed : collar.commonCore.edgeSet
  orientation :
    (incoming = change.resolved.first.1 ∧
        bypassed = change.resolved.second.1) ∨
      (incoming = change.resolved.second.1 ∧
        bypassed = change.resolved.first.1)
  incoming_support :
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape incoming) ≠ 0
  bypassed_zero :
    crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape bypassed) = 0
  incoming_third :
    collar.commonCore.lineGraph.Adj incoming change.thirdEdge

/-- Every transverse change has a uniquely supported complementary corner;
the disjunction records which old edge supplies it. -/
theorem nonempty_complementarySupportCorner :
    Nonempty change.ComplementarySupportCorner := by
  rcases change.exactlyOne_first_second_complementSupport with
    ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · exact ⟨{
      incoming := change.resolved.first.1
      bypassed := change.resolved.second.1
      orientation := Or.inl ⟨rfl, rfl⟩
      incoming_support := by
        simpa only [commonDiscrepancy_apply] using hfirst
      bypassed_zero := by
        simpa only [commonDiscrepancy_apply] using hsecond
      incoming_third := change.firstThird }⟩
  · exact ⟨{
      incoming := change.resolved.second.1
      bypassed := change.resolved.first.1
      orientation := Or.inr ⟨rfl, rfl⟩
      incoming_support := by
        simpa only [commonDiscrepancy_apply] using hsecond
      bypassed_zero := by
        simpa only [commonDiscrepancy_apply] using hfirst
      incoming_third := change.secondThird }⟩

namespace ComplementarySupportCorner

variable (corner : change.ComplementarySupportCorner)

/-- The selected incoming edge inside the complementary support graph. -/
def incomingSupportEdge :
    (collar.coordinateDiscrepancySupportGraph sourceEscape
      (!firstHit.transfer.coordinate)).edgeSet :=
  collar.coordinateDiscrepancySupportEdge sourceEscape
    (!firstHit.transfer.coordinate) corner.incoming corner.incoming_support

/-- The transverse edge inside the same complementary support graph. -/
def transverseSupportEdge :
    (collar.coordinateDiscrepancySupportGraph sourceEscape
      (!firstHit.transfer.coordinate)).edgeSet :=
  collar.coordinateDiscrepancySupportEdge sourceEscape
    (!firstHit.transfer.coordinate) change.thirdEdge (by
      simpa only [commonDiscrepancy_apply] using
        change.third_complementSupport)

/-- The selected incoming and transverse support edges remain adjacent in
the complementary support graph. -/
theorem incoming_transverse_adj :
    (collar.coordinateDiscrepancySupportGraph sourceEscape
      (!firstHit.transfer.coordinate)).lineGraph.Adj
        corner.incomingSupportEdge (transverseSupportEdge change) := by
  apply collar.coordinateDiscrepancySupportEdge_lineGraph_adj
    sourceEscape (!firstHit.transfer.coordinate)
  exact corner.incoming_third

/-- The junction selected by the complementary corner has support degree
exactly two.  Thus the transverse edge is the unique continuation from the
selected old edge in that scalar support graph. -/
theorem supportJunction_degree_eq_two :
    let supportGraph := collar.coordinateDiscrepancySupportGraph
      sourceEscape (!firstHit.transfer.coordinate)
    let junction := SimpleGraph.lineGraphCommonVertex
      corner.incoming_transverse_adj
    (incidentEdgeFinset supportGraph junction).card = 2 := by
  let supportGraph := collar.coordinateDiscrepancySupportGraph
    sourceEscape (!firstHit.transfer.coordinate)
  let incomingEdge := corner.incomingSupportEdge
  let transverseEdge := transverseSupportEdge change
  let junction := SimpleGraph.lineGraphCommonVertex
    corner.incoming_transverse_adj
  change (incidentEdgeFinset supportGraph junction).card = 2
  have hincoming : incomingEdge ∈
      incidentEdgeFinset supportGraph junction := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact SimpleGraph.lineGraphCommonVertex_mem_left
      corner.incoming_transverse_adj
  have htransverse : transverseEdge ∈
      incidentEdgeFinset supportGraph junction := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact SimpleGraph.lineGraphCommonVertex_mem_right
      corner.incoming_transverse_adj
  have hpairSubset : ({incomingEdge, transverseEdge} :
      Finset supportGraph.edgeSet) ⊆
        incidentEdgeFinset supportGraph junction := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact hincoming
    · exact htransverse
  have hlower : 2 ≤
      (incidentEdgeFinset supportGraph junction).card := by
    have hpairCard : ({incomingEdge, transverseEdge} :
        Finset supportGraph.edgeSet).card = 2 :=
      Finset.card_pair corner.incoming_transverse_adj.ne
    rw [← hpairCard]
    exact Finset.card_le_card hpairSubset
  have hupper :
      (incidentEdgeFinset supportGraph junction).card ≤ 2 := by
    exact taitDiscrepancySupport_incidentCard_le_two
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate) junction
      (collar.commonCore_incidentEdgeFinset_card_le_three junction)
  exact Nat.le_antisymm hupper hlower

end ComplementarySupportCorner

end TransverseCompanionChange

end FirstHitSingletonCompanionTransferPath

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
