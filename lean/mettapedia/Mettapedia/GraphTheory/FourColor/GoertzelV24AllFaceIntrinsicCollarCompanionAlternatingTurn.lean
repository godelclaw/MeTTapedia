import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionClosedKempeReentry

/-! Coordinate-generic companion turns and their involutive local switch. -/

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

/-- The actual two-color state of one common-core edge in a selected scalar
discrepancy support. -/
noncomputable def discrepancyColorState
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) (edge : collar.commonCore.edgeSet)
    (hsupport : crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape edge) ≠ 0) :
    ScalarDiscrepancyColorState coordinate :=
  scalarDiscrepancyColorStateOf
    (collar.sourceCommonColoring sourceEscape)
    collar.targetCommonColoring
    (collar.sourceCommonColoring_isTait sourceEscape)
    collar.targetCommonColoring_isTait coordinate edge (by
      simpa only [commonDiscrepancy_apply] using hsupport)

@[simp]
theorem discrepancyColorState_sourceColor
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) (edge : collar.commonCore.edgeSet)
    (hsupport : crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape edge) ≠ 0) :
    (collar.discrepancyColorState sourceEscape coordinate edge
      hsupport).sourceColor =
        collar.sourceCommonColoring sourceEscape edge := rfl

@[simp]
theorem discrepancyColorState_targetColor
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) (edge : collar.commonCore.edgeSet)
    (hsupport : crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape edge) ≠ 0) :
    (collar.discrepancyColorState sourceEscape coordinate edge
      hsupport).targetColor = collar.targetCommonColoring edge := rfl

/-- A coordinate-generic signed turn at one cubic common-core junction. -/
structure ScalarCompanionTurn
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) where
  first : collar.commonCore.edgeSet
  second : collar.commonCore.edgeSet
  third : collar.commonCore.edgeSet
  firstSecond : collar.commonCore.lineGraph.Adj first second
  firstThird : collar.commonCore.lineGraph.Adj first third
  secondThird : collar.commonCore.lineGraph.Adj second third
  firstSupport : crossFaceCoordinate coordinate
    (collar.commonDiscrepancy sourceEscape first) ≠ 0
  secondSupport : crossFaceCoordinate coordinate
    (collar.commonDiscrepancy sourceEscape second) ≠ 0
  companion_ne :
    (collar.discrepancyColorState sourceEscape coordinate first
        firstSupport).companionColor ≠
      (collar.discrepancyColorState sourceEscape coordinate second
        secondSupport).companionColor
  thirdDiscrepancy : collar.commonDiscrepancy sourceEscape third =
    crossFaceZeroColor coordinate

namespace ScalarCompanionTurn

variable {coordinate : Bool}
  (turn : collar.ScalarCompanionTurn sourceEscape coordinate)

/-- The transverse edge of a signed turn lies in the complementary scalar
support. -/
theorem third_complementSupport :
    crossFaceCoordinate (!coordinate)
      (collar.commonDiscrepancy sourceEscape turn.third) ≠ 0 := by
  rw [turn.thirdDiscrepancy]
  exact crossFaceCoordinate_complement_zeroColor_ne_zero coordinate

/-- In its original coordinate, the transverse distinguished color has
zero scalar value. -/
theorem third_originalCoordinate_zero :
    crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape turn.third) = 0 := by
  rw [turn.thirdDiscrepancy]
  cases coordinate <;>
    simp [crossFaceZeroColor, crossFaceCoordinate, red, blue]

/-- Exactly one old support edge also lies in the complementary scalar
support. -/
theorem exactlyOne_first_second_complementSupport :
    (crossFaceCoordinate (!coordinate)
          (collar.commonDiscrepancy sourceEscape turn.first) ≠ 0 ∧
        crossFaceCoordinate (!coordinate)
          (collar.commonDiscrepancy sourceEscape turn.second) = 0) ∨
      (crossFaceCoordinate (!coordinate)
          (collar.commonDiscrepancy sourceEscape turn.first) = 0 ∧
        crossFaceCoordinate (!coordinate)
          (collar.commonDiscrepancy sourceEscape turn.second) ≠ 0) := by
  simpa only [discrepancyColorState_sourceColor,
    discrepancyColorState_targetColor, commonDiscrepancy_apply] using
    exactlyOne_complementSupport_of_companion_ne
      (collar.discrepancyColorState sourceEscape coordinate turn.first
        turn.firstSupport)
      (collar.discrepancyColorState sourceEscape coordinate turn.second
        turn.secondSupport)
      turn.companion_ne

/-- The unique old edge continuing in the complementary support, together
with the old edge bypassed by the turn. -/
structure ComplementarySupportCorner where
  incoming : collar.commonCore.edgeSet
  bypassed : collar.commonCore.edgeSet
  orientation :
    (incoming = turn.first ∧ bypassed = turn.second) ∨
      (incoming = turn.second ∧ bypassed = turn.first)
  incoming_support : crossFaceCoordinate (!coordinate)
    (collar.commonDiscrepancy sourceEscape incoming) ≠ 0
  bypassed_zero : crossFaceCoordinate (!coordinate)
    (collar.commonDiscrepancy sourceEscape bypassed) = 0
  incoming_third : collar.commonCore.lineGraph.Adj incoming turn.third

/-- Every coordinate-generic signed turn has its complementary corner. -/
theorem nonempty_complementarySupportCorner :
    Nonempty turn.ComplementarySupportCorner := by
  rcases turn.exactlyOne_first_second_complementSupport with
    ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · exact ⟨{
      incoming := turn.first
      bypassed := turn.second
      orientation := Or.inl ⟨rfl, rfl⟩
      incoming_support := hfirst
      bypassed_zero := hsecond
      incoming_third := turn.firstThird }⟩
  · exact ⟨{
      incoming := turn.second
      bypassed := turn.first
      orientation := Or.inr ⟨rfl, rfl⟩
      incoming_support := hsecond
      bypassed_zero := hfirst
      incoming_third := turn.secondThird }⟩

namespace ComplementarySupportCorner

variable (corner : turn.ComplementarySupportCorner)

/-- The selected incoming edge retains its original-coordinate support. -/
theorem incoming_originalSupport :
    crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape corner.incoming) ≠ 0 := by
  rcases corner.orientation with ⟨hincoming, _hbypassed⟩ |
      ⟨hincoming, _hbypassed⟩
  · simpa only [hincoming] using turn.firstSupport
  · simpa only [hincoming] using turn.secondSupport

/-- The bypassed edge likewise retains its original-coordinate support. -/
theorem bypassed_originalSupport :
    crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape corner.bypassed) ≠ 0 := by
  rcases corner.orientation with ⟨_hincoming, hbypassed⟩ |
      ⟨_hincoming, hbypassed⟩
  · simpa only [hbypassed] using turn.secondSupport
  · simpa only [hbypassed] using turn.firstSupport

/-- The bypassed old edge carries exactly the distinguished color of the
new coordinate. -/
theorem bypassedDiscrepancy_eq_zeroColor :
    collar.commonDiscrepancy sourceEscape corner.bypassed =
      crossFaceZeroColor (!coordinate) := by
  have hnonzero : collar.commonDiscrepancy sourceEscape
      corner.bypassed ≠ 0 := by
    intro hzero
    apply corner.bypassed_originalSupport
    rw [hzero]
    simp [crossFaceCoordinate]
  exact (crossFaceCoordinate_eq_zero_iff_eq_crossFaceZeroColor
    (!coordinate) (collar.commonDiscrepancy sourceEscape corner.bypassed)
    hnonzero).1 corner.bypassed_zero

/-- Original-coordinate state on the selected old edge. -/
noncomputable def incomingOriginalState :
    ScalarDiscrepancyColorState coordinate :=
  collar.discrepancyColorState sourceEscape coordinate corner.incoming
    corner.incoming_originalSupport

/-- The same actual color pair recoordinated into the complementary
support. -/
noncomputable def incomingComplementState :
    ScalarDiscrepancyColorState (!coordinate) :=
  corner.incomingOriginalState.complementCoordinateState (by
    simpa only [incomingOriginalState, discrepancyColorState_sourceColor,
      discrepancyColorState_targetColor, commonDiscrepancy_apply] using
      corner.incoming_support)

/-- Complementary-coordinate state on the transverse edge. -/
noncomputable def thirdComplementState :
    ScalarDiscrepancyColorState (!coordinate) :=
  collar.discrepancyColorState sourceEscape (!coordinate) turn.third
    turn.third_complementSupport

/-- Recoordinating the selected old edge makes the original distinguished
color its new companion. -/
theorem incomingComplementState_companionColor_eq :
    corner.incomingComplementState.companionColor =
      crossFaceZeroColor coordinate := by
  exact corner.incomingOriginalState
    |>.complementCoordinateState_companionColor_eq_zeroColor _

/-- The transverse edge has the opposite signed companion behavior. -/
theorem thirdComplementState_companionColor_ne :
    (thirdComplementState (turn := turn)).companionColor ≠
      crossFaceZeroColor coordinate := by
  apply (thirdComplementState (turn := turn))
    |>.companionColor_ne_otherZero_of_source_add_target_eq
  simpa only [thirdComplementState, discrepancyColorState_sourceColor,
    discrepancyColorState_targetColor, commonDiscrepancy_apply] using
    turn.thirdDiscrepancy

/-- Hence the complementary launch is again a genuine signed companion
turn. -/
theorem incoming_third_companionColor_ne :
    corner.incomingComplementState.companionColor ≠
      (thirdComplementState (turn := turn)).companionColor := by
  rw [corner.incomingComplementState_companionColor_eq]
  exact (thirdComplementState_companionColor_ne (turn := turn)).symm

/-- Complementary scalar-support graph entered by the turn. -/
abbrev complementarySupportGraph
    (_corner : turn.ComplementarySupportCorner) :=
  collar.coordinateDiscrepancySupportGraph sourceEscape (!coordinate)

/-- Selected old edge inside the complementary support graph. -/
def incomingSupportEdge : corner.complementarySupportGraph.edgeSet :=
  collar.coordinateDiscrepancySupportEdge sourceEscape (!coordinate)
    corner.incoming corner.incoming_support

/-- Transverse edge inside the complementary support graph. -/
def transverseSupportEdge : corner.complementarySupportGraph.edgeSet :=
  collar.coordinateDiscrepancySupportEdge sourceEscape (!coordinate)
    turn.third turn.third_complementSupport

/-- The selected old and transverse support edges are adjacent. -/
theorem incoming_transverse_adj :
    corner.complementarySupportGraph.lineGraph.Adj
      corner.incomingSupportEdge corner.transverseSupportEdge := by
  apply collar.coordinateDiscrepancySupportEdge_lineGraph_adj
    sourceEscape (!coordinate)
  exact corner.incoming_third

/-- The complementary-support launch junction has degree exactly two. -/
theorem supportJunction_degree_eq_two :
    (incidentEdgeFinset corner.complementarySupportGraph
      (SimpleGraph.lineGraphCommonVertex
        corner.incoming_transverse_adj)).card = 2 := by
  let junction := SimpleGraph.lineGraphCommonVertex
    corner.incoming_transverse_adj
  have hincoming : corner.incomingSupportEdge ∈
      incidentEdgeFinset corner.complementarySupportGraph junction := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact SimpleGraph.lineGraphCommonVertex_mem_left
      corner.incoming_transverse_adj
  have htransverse : corner.transverseSupportEdge ∈
      incidentEdgeFinset corner.complementarySupportGraph junction := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact SimpleGraph.lineGraphCommonVertex_mem_right
      corner.incoming_transverse_adj
  have hpairSubset :
      ({corner.incomingSupportEdge, corner.transverseSupportEdge} :
        Finset corner.complementarySupportGraph.edgeSet) ⊆
        incidentEdgeFinset corner.complementarySupportGraph junction := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact hincoming
    · exact htransverse
  have hlower : 2 ≤
      (incidentEdgeFinset corner.complementarySupportGraph junction).card := by
    have hpairCard :
        ({corner.incomingSupportEdge, corner.transverseSupportEdge} :
          Finset corner.complementarySupportGraph.edgeSet).card = 2 :=
      Finset.card_pair corner.incoming_transverse_adj.ne
    rw [← hpairCard]
    exact Finset.card_le_card hpairSubset
  have hupper :
      (incidentEdgeFinset corner.complementarySupportGraph junction).card ≤
        2 := by
    exact taitDiscrepancySupport_incidentCard_le_two
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!coordinate) junction
      (collar.commonCore_incidentEdgeFinset_card_le_three junction)
  exact Nat.le_antisymm hupper hlower

/-- Recoordinating the selected incoming state agrees with direct
extraction in the new coordinate. -/
theorem incomingComplementState_eq_discrepancyColorState :
    corner.incomingComplementState =
      collar.discrepancyColorState sourceEscape (!coordinate)
        corner.incoming corner.incoming_support := by
  apply Subtype.ext
  rfl

/-- The selected and bypassed old edges remain adjacent. -/
theorem incoming_bypassed_adj :
    collar.commonCore.lineGraph.Adj corner.incoming corner.bypassed := by
  rcases corner.orientation with ⟨hincoming, hbypassed⟩ |
      ⟨hincoming, hbypassed⟩
  · simpa only [hincoming, hbypassed] using turn.firstSecond
  · simpa only [hincoming, hbypassed] using turn.firstSecond.symm

/-- The transverse and bypassed edges remain adjacent. -/
theorem third_bypassed_adj :
    collar.commonCore.lineGraph.Adj turn.third corner.bypassed := by
  rcases corner.orientation with ⟨_hincoming, hbypassed⟩ |
      ⟨_hincoming, hbypassed⟩
  · simpa only [hbypassed] using turn.secondThird.symm
  · simpa only [hbypassed] using turn.firstThird.symm

/-- Switching coordinates at the junction constructs another full signed
turn. Its transverse edge is the old bypassed edge, so the local operation
is involutive up to ordering of the two old edges. -/
noncomputable def toggleTurn :
    collar.ScalarCompanionTurn sourceEscape (!coordinate) where
  first := corner.incoming
  second := turn.third
  third := corner.bypassed
  firstSecond := corner.incoming_third
  firstThird := corner.incoming_bypassed_adj
  secondThird := corner.third_bypassed_adj
  firstSupport := corner.incoming_support
  secondSupport := turn.third_complementSupport
  companion_ne := by
    rw [← corner.incomingComplementState_eq_discrepancyColorState]
    exact corner.incoming_third_companionColor_ne
  thirdDiscrepancy := corner.bypassedDiscrepancy_eq_zeroColor

/-- The canonical corner for switching the toggled turn back: the same
incoming edge continues, while the old transverse edge is bypassed. -/
noncomputable def returnCorner :
    corner.toggleTurn.ComplementarySupportCorner where
  incoming := corner.incoming
  bypassed := turn.third
  orientation := Or.inl ⟨rfl, rfl⟩
  incoming_support := by
    simpa using corner.incoming_originalSupport
  bypassed_zero := by
    simpa using turn.third_originalCoordinate_zero
  incoming_third := corner.incoming_bypassed_adj

/-- Toggling twice restores the original unordered pair of old edges. -/
theorem toggleTwice_edgePair_eq :
    ({corner.returnCorner.toggleTurn.first,
        corner.returnCorner.toggleTurn.second} :
      Finset collar.commonCore.edgeSet) =
      {turn.first, turn.second} := by
  rcases corner.orientation with ⟨hincoming, hbypassed⟩ |
      ⟨hincoming, hbypassed⟩
  · simp only [toggleTurn, returnCorner]
    rw [hincoming, hbypassed]
  · simp only [toggleTurn, returnCorner]
    rw [hincoming, hbypassed, Finset.pair_comm]

/-- Toggling twice also restores the original transverse edge literally. -/
theorem toggleTwice_third_eq :
    corner.returnCorner.toggleTurn.third = turn.third := by
  rfl

end ComplementarySupportCorner
end ScalarCompanionTurn

variable {firstHit : FirstHitSingletonCompanionTransferPath
    (collar := collar) (sourceEscape := sourceEscape)}
  {change : firstHit.TransverseCompanionChange}

namespace FirstHitSingletonCompanionTransferPath.TransverseCompanionChange.ComplementarySupportCorner.ClosedSupportRoute.InteriorTransverseTurn

variable {corner : change.ComplementarySupportCorner}
  {route : corner.ClosedSupportRoute}

/-- The residual interior event is an instance of the coordinate-generic
signed turn in the complementary coordinate. -/
noncomputable def toScalarCompanionTurn
    (interior : route.InteriorTransverseTurn) :
    collar.ScalarCompanionTurn sourceEscape
      (!firstHit.transfer.coordinate) where
  first := corner.supportEdgeAmbientEdge interior.first
  second := corner.supportEdgeAmbientEdge interior.second
  third := interior.thirdEdge
  firstSecond := corner.supportEdgeAmbientEdge_lineGraph_adj
    interior.firstSecond
  firstThird := interior.firstThird
  secondThird := interior.secondThird
  firstSupport := corner.supportEdgeAmbientEdge_support interior.first
  secondSupport := corner.supportEdgeAmbientEdge_support interior.second
  companion_ne := by
    simpa only [discrepancyColorState, supportEdgeColorState] using
      interior.companion_ne
  thirdDiscrepancy := interior.discrepancy

/-- Toggling the residual interior turn constructs a full signed turn back
in the original scalar coordinate. -/
theorem nonempty_originalCoordinateTurn
    (interior : route.InteriorTransverseTurn) :
    Nonempty (collar.ScalarCompanionTurn sourceEscape
      firstHit.transfer.coordinate) := by
  let turn := interior.toScalarCompanionTurn
  rcases turn.nonempty_complementarySupportCorner with ⟨switchCorner⟩
  simpa using (show Nonempty
      (collar.ScalarCompanionTurn sourceEscape
        (!(!firstHit.transfer.coordinate))) from
    ⟨switchCorner.toggleTurn⟩)

end FirstHitSingletonCompanionTransferPath.TransverseCompanionChange.ComplementarySupportCorner.ClosedSupportRoute.InteriorTransverseTurn
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
