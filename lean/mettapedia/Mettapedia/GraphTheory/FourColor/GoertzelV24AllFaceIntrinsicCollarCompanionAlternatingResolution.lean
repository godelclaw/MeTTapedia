import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingClosedTurn

/-! Kempe-or-next-turn resolution for coordinate-generic signed turns. -/

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
  {coordinate : Bool}
  {turn : collar.ScalarCompanionTurn sourceEscape coordinate}

namespace ScalarCompanionTurn.ComplementarySupportCorner

variable (corner : turn.ComplementarySupportCorner)

/-- Adjacent support edges are two distinct common-core edges incident to
their common junction. -/
theorem supportEdgePair_subset_incidentEdgeFinset
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second) :
    ({corner.supportEdgeAmbientEdge first,
        corner.supportEdgeAmbientEdge second} :
      Finset collar.commonCore.edgeSet) ⊆
      incidentEdgeFinset collar.commonCore
        (SimpleGraph.lineGraphCommonVertex
          (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent)) := by
  intro edge hedge
  simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
  rcases hedge with rfl | rfl
  · simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact SimpleGraph.lineGraphCommonVertex_mem_left
      (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent)
  · simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact SimpleGraph.lineGraphCommonVertex_mem_right
      (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent)

/-- The junction of adjacent support edges has common-core degree at least
two. -/
theorem two_le_card_incidentEdgeFinset_of_supportEdge_adjacent
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second) :
    2 ≤ (incidentEdgeFinset collar.commonCore
      (SimpleGraph.lineGraphCommonVertex
        (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent))).card := by
  have hle := Finset.card_le_card
    (corner.supportEdgePair_subset_incidentEdgeFinset first second hadjacent)
  have hpair :
      ({corner.supportEdgeAmbientEdge first,
          corner.supportEdgeAmbientEdge second} :
        Finset collar.commonCore.edgeSet).card = 2 :=
    Finset.card_pair
      (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent).ne
  rw [hpair] at hle
  exact hle

/-- A source-port support adjacency cannot be a literal source--target
overlap, whose common-core degree is one. -/
theorem no_portOverlap_of_supportEdge_adjacent_at_sourcePort
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second)
    (sourcePort : Fin 4)
    (hvertex : SimpleGraph.lineGraphCommonVertex
        (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
      collar.sourcePortInCommonCore sourcePort) :
    ∀ targetPort : Fin 4, ¬ collar.PortOverlap sourcePort targetPort := by
  intro targetPort hoverlap
  have hcard :=
    collar.card_incidentEdgeFinset_sourcePortInCommonCore sourcePort
  rw [if_pos ⟨targetPort, hoverlap⟩] at hcard
  have htwo : 2 ≤ (incidentEdgeFinset collar.commonCore
      (collar.sourcePortInCommonCore sourcePort)).card := by
    rw [← hvertex]
    exact corner.two_le_card_incidentEdgeFinset_of_supportEdge_adjacent
      first second hadjacent
  omega

/-- The analogous no-overlap theorem at a target port. -/
theorem no_portOverlap_of_supportEdge_adjacent_at_targetPort
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second)
    (targetPort : Fin 4)
    (hvertex : SimpleGraph.lineGraphCommonVertex
        (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
      collar.targetPortInCommonCore targetPort) :
    ∀ sourcePort : Fin 4, ¬ collar.PortOverlap sourcePort targetPort := by
  intro sourcePort hoverlap
  have hcard :=
    collar.card_incidentEdgeFinset_targetPortInCommonCore targetPort
  rw [if_pos ⟨sourcePort, hoverlap⟩] at hcard
  have htwo : 2 ≤ (incidentEdgeFinset collar.commonCore
      (collar.targetPortInCommonCore targetPort)).card := by
    rw [← hvertex]
    exact corner.two_le_card_incidentEdgeFinset_of_supportEdge_adjacent
      first second hadjacent
  omega

/-- At a nonoverlapping source port, the support pair exhausts the two
common-core edges. -/
theorem incidentEdgeFinset_sourcePort_eq_supportEdgePair
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second)
    (sourcePort : Fin 4)
    (hvertex : SimpleGraph.lineGraphCommonVertex
        (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
      collar.sourcePortInCommonCore sourcePort) :
    incidentEdgeFinset collar.commonCore
        (collar.sourcePortInCommonCore sourcePort) =
      {corner.supportEdgeAmbientEdge first,
        corner.supportEdgeAmbientEdge second} := by
  have hnone : ¬ ∃ targetPort : Fin 4,
      collar.PortOverlap sourcePort targetPort := by
    rintro ⟨targetPort, hoverlap⟩
    exact corner.no_portOverlap_of_supportEdge_adjacent_at_sourcePort
      first second hadjacent sourcePort hvertex targetPort hoverlap
  have hcard :=
    collar.card_incidentEdgeFinset_sourcePortInCommonCore sourcePort
  rw [if_neg hnone] at hcard
  have hsubset :
      ({corner.supportEdgeAmbientEdge first,
          corner.supportEdgeAmbientEdge second} :
        Finset collar.commonCore.edgeSet) ⊆
        incidentEdgeFinset collar.commonCore
          (collar.sourcePortInCommonCore sourcePort) := by
    rw [← hvertex]
    exact corner.supportEdgePair_subset_incidentEdgeFinset
      first second hadjacent
  have hpair :
      ({corner.supportEdgeAmbientEdge first,
          corner.supportEdgeAmbientEdge second} :
        Finset collar.commonCore.edgeSet).card = 2 :=
    Finset.card_pair
      (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent).ne
  symm
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hpair, hcard]

/-- At a nonoverlapping target port, the support pair likewise exhausts
the two common-core edges. -/
theorem incidentEdgeFinset_targetPort_eq_supportEdgePair
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second)
    (targetPort : Fin 4)
    (hvertex : SimpleGraph.lineGraphCommonVertex
        (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
      collar.targetPortInCommonCore targetPort) :
    incidentEdgeFinset collar.commonCore
        (collar.targetPortInCommonCore targetPort) =
      {corner.supportEdgeAmbientEdge first,
        corner.supportEdgeAmbientEdge second} := by
  have hnone : ¬ ∃ sourcePort : Fin 4,
      collar.PortOverlap sourcePort targetPort := by
    rintro ⟨sourcePort, hoverlap⟩
    exact corner.no_portOverlap_of_supportEdge_adjacent_at_targetPort
      first second hadjacent targetPort hvertex sourcePort hoverlap
  have hcard :=
    collar.card_incidentEdgeFinset_targetPortInCommonCore targetPort
  rw [if_neg hnone] at hcard
  have hsubset :
      ({corner.supportEdgeAmbientEdge first,
          corner.supportEdgeAmbientEdge second} :
        Finset collar.commonCore.edgeSet) ⊆
        incidentEdgeFinset collar.commonCore
          (collar.targetPortInCommonCore targetPort) := by
    rw [← hvertex]
    exact corner.supportEdgePair_subset_incidentEdgeFinset
      first second hadjacent
  have hpair :
      ({corner.supportEdgeAmbientEdge first,
          corner.supportEdgeAmbientEdge second} :
        Finset collar.commonCore.edgeSet).card = 2 :=
    Finset.card_pair
      (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent).ne
  symm
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hpair, hcard]

/-- A companion-changing support pair sums to the distinguished color of
its active coordinate. -/
theorem changedSupportEdgePair_discrepancy_eq_zeroColor
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second)
    (hcompanion :
      (corner.supportEdgeColorState first).companionColor ≠
        (corner.supportEdgeColorState second).companionColor) :
    collar.commonDiscrepancy sourceEscape
          (corner.supportEdgeAmbientEdge first) +
        collar.commonDiscrepancy sourceEscape
          (corner.supportEdgeAmbientEdge second) =
      crossFaceZeroColor (!coordinate) := by
  let ambientAdj :=
    corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent
  have htransition : ScalarDiscrepancyColorTransition
      (corner.supportEdgeColorState first)
      (corner.supportEdgeColorState second) := by
    apply scalarDiscrepancyColorTransition_of_adjacent
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!coordinate) ambientAdj
    · simpa only [commonDiscrepancy_apply] using
        corner.supportEdgeAmbientEdge_support first
    · simpa only [commonDiscrepancy_apply] using
        corner.supportEdgeAmbientEdge_support second
  have hemitted :=
    scalarDiscrepancyTransverseEmission_eq_zeroColor_of_companion_ne
      htransition hcompanion
  rw [scalarDiscrepancyTransverseEmission] at hemitted
  simpa only [supportEdgeColorState_sourceColor,
    supportEdgeColorState_targetColor, commonDiscrepancy_apply] using
    (show
      (collar.sourceCommonColoring sourceEscape
            (corner.supportEdgeAmbientEdge first) +
          collar.targetCommonColoring
            (corner.supportEdgeAmbientEdge first)) +
        (collar.sourceCommonColoring sourceEscape
            (corner.supportEdgeAmbientEdge second) +
          collar.targetCommonColoring
            (corner.supportEdgeAmbientEdge second)) =
        crossFaceZeroColor (!coordinate) by
      calc
        _ = (collar.sourceCommonColoring sourceEscape
                (corner.supportEdgeAmbientEdge first) +
              collar.sourceCommonColoring sourceEscape
                (corner.supportEdgeAmbientEdge second)) +
            (collar.targetCommonColoring
                (corner.supportEdgeAmbientEdge first) +
              collar.targetCommonColoring
                (corner.supportEdgeAmbientEdge second)) := by abel
        _ = crossFaceZeroColor (!coordinate) := by
          simpa only [supportEdgeColorState_sourceColor,
            supportEdgeColorState_targetColor] using hemitted)

/-- A source-port second turn has this exact collar boundary value. -/
theorem changedSupportEdges_sourcePort_boundaryValue_eq_zeroColor
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second)
    (hcompanion :
      (corner.supportEdgeColorState first).companionColor ≠
        (corner.supportEdgeColorState second).companionColor)
    (sourcePort : Fin 4)
    (hvertex : SimpleGraph.lineGraphCommonVertex
        (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
      collar.sourcePortInCommonCore sourcePort) :
    vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape)
        (collar.sourcePortInCommonCore sourcePort) =
      crossFaceZeroColor (!coordinate) := by
  classical
  rw [vertexKirchhoffSum,
    corner.incidentEdgeFinset_sourcePort_eq_supportEdgePair
      first second hadjacent sourcePort hvertex]
  have hne : corner.supportEdgeAmbientEdge first ≠
      corner.supportEdgeAmbientEdge second :=
    (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent).ne
  have hnotmem : corner.supportEdgeAmbientEdge first ∉
      ({corner.supportEdgeAmbientEdge second} :
        Finset collar.commonCore.edgeSet) := by
    intro hmem
    exact hne (Finset.mem_singleton.mp hmem)
  rw [Finset.sum_insert hnotmem, Finset.sum_singleton]
  exact corner.changedSupportEdgePair_discrepancy_eq_zeroColor
    first second hadjacent hcompanion

/-- A target-port second turn has the same exact boundary value. -/
theorem changedSupportEdges_targetPort_boundaryValue_eq_zeroColor
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second)
    (hcompanion :
      (corner.supportEdgeColorState first).companionColor ≠
        (corner.supportEdgeColorState second).companionColor)
    (targetPort : Fin 4)
    (hvertex : SimpleGraph.lineGraphCommonVertex
        (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
      collar.targetPortInCommonCore targetPort) :
    vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape)
        (collar.targetPortInCommonCore targetPort) =
      crossFaceZeroColor (!coordinate) := by
  classical
  rw [vertexKirchhoffSum,
    corner.incidentEdgeFinset_targetPort_eq_supportEdgePair
      first second hadjacent targetPort hvertex]
  have hne : corner.supportEdgeAmbientEdge first ≠
      corner.supportEdgeAmbientEdge second :=
    (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent).ne
  have hnotmem : corner.supportEdgeAmbientEdge first ∉
      ({corner.supportEdgeAmbientEdge second} :
        Finset collar.commonCore.edgeSet) := by
    intro hmem
    exact hne (Finset.mem_singleton.mp hmem)
  rw [Finset.sum_insert hnotmem, Finset.sum_singleton]
  exact corner.changedSupportEdgePair_discrepancy_eq_zeroColor
    first second hadjacent hcompanion

/-- A nonoverlapping target port as its canonical terminal representative. -/
def unmatchedTargetPortOfNoOverlap
    (_corner : turn.ComplementarySupportCorner)
    (targetPort : Fin 4)
    (hnoOverlap : ∀ sourcePort : Fin 4,
      ¬ collar.PortOverlap sourcePort targetPort) :
    ↑(intrinsicCollarUnmatchedTargetPorts
      collar.intrinsicCollarPortOverlapProfile) :=
  ⟨targetPort, by
    rw [intrinsicCollarUnmatchedTargetPorts, Finset.mem_filter]
    refine ⟨Finset.mem_univ targetPort, ?_⟩
    intro sourcePort hprofile
    exact hnoOverlap sourcePort
      ((collar.mem_intrinsicCollarPortOverlapProfile_iff _).1 hprofile)⟩

@[simp]
theorem unmatchedTargetPortOfNoOverlap_val
    (targetPort : Fin 4)
    (hnoOverlap : ∀ sourcePort : Fin 4,
      ¬ collar.PortOverlap sourcePort targetPort) :
    (corner.unmatchedTargetPortOfNoOverlap targetPort hnoOverlap).1 =
      targetPort := rfl

/-- A source-port boundary turn supplies an actual Kempe action and
canonical same-base reentry. -/
theorem changedSupportEdges_sourcePort_kempeAction_and_sameBaseReentry
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second)
    (hcompanion :
      (corner.supportEdgeColorState first).companionColor ≠
        (corner.supportEdgeColorState second).companionColor)
    (sourcePort : Fin 4)
    (hvertex : SimpleGraph.lineGraphCommonVertex
        (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
      collar.sourcePortInCommonCore sourcePort) :
    ChargedTerminalKempeAction collar sourceEscape coordinate
        (Sum.inl sourcePort) ∧
      (sourceNormal.SameBaseKempeReentry sourceEscape ∨
        collar.targetNormal.SameBaseKempeReentry collar.targetEscape) := by
  have hboundary :=
    corner.changedSupportEdges_sourcePort_boundaryValue_eq_zeroColor
      first second hadjacent hcompanion sourcePort hvertex
  have hword :
      intrinsicCollarTerminalBoundaryWord
          collar.intrinsicCollarPortOverlapProfile
          (collar.intrinsicCollarCorrectionWord sourceEscape)
          (Sum.inl sourcePort) =
        crossFaceZeroColor (!coordinate) := by
    rw [collar.intrinsicCollarTerminalBoundaryWord_source_eq_boundaryState,
      commonDiscrepancyBoundaryState_apply]
    simpa only [sourcePortCommonTerminal] using hboundary
  have hcharged : crossFaceCoordinate coordinate
      (intrinsicCollarTerminalBoundaryWord
          collar.intrinsicCollarPortOverlapProfile
          (collar.intrinsicCollarCorrectionWord sourceEscape)
          (intrinsicCollarTerminalCoordinateOfRepresentative
          ((Sum.inl sourcePort) :
            IntrinsicCollarTerminalRepresentative
              collar.intrinsicCollarPortOverlapProfile))) ≠ 0 := by
    change crossFaceCoordinate coordinate
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (Sum.inl sourcePort)) ≠ 0
    rw [hword]
    simpa using
      crossFaceCoordinate_complement_zeroColor_ne_zero (!coordinate)
  let witness :=
    collar.chargedTerminalColorWitness_of_coordinate_ne_zero
      sourceEscape coordinate
      ((Sum.inl sourcePort) :
        IntrinsicCollarTerminalRepresentative
          collar.intrinsicCollarPortOverlapProfile)
      hcharged
  let action := witness.nonempty_kempeAction
  exact ⟨action, action.sameBaseReentry⟩

/-- A target-port boundary turn supplies the same action through its
unmatched terminal representative. -/
theorem changedSupportEdges_targetPort_kempeAction_and_sameBaseReentry
    (first second : corner.complementarySupportGraph.edgeSet)
    (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
      first second)
    (hcompanion :
      (corner.supportEdgeColorState first).companionColor ≠
        (corner.supportEdgeColorState second).companionColor)
    (targetPort : Fin 4)
    (hvertex : SimpleGraph.lineGraphCommonVertex
        (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
      collar.targetPortInCommonCore targetPort) :
    let unmatched := corner.unmatchedTargetPortOfNoOverlap targetPort
      (corner.no_portOverlap_of_supportEdge_adjacent_at_targetPort
        first second hadjacent targetPort hvertex)
    ChargedTerminalKempeAction collar sourceEscape coordinate
        (Sum.inr unmatched) ∧
      (sourceNormal.SameBaseKempeReentry sourceEscape ∨
        collar.targetNormal.SameBaseKempeReentry collar.targetEscape) := by
  let hnoOverlap :=
    corner.no_portOverlap_of_supportEdge_adjacent_at_targetPort
      first second hadjacent targetPort hvertex
  let unmatched :=
    corner.unmatchedTargetPortOfNoOverlap targetPort hnoOverlap
  have hboundary :=
    corner.changedSupportEdges_targetPort_boundaryValue_eq_zeroColor
      first second hadjacent hcompanion targetPort hvertex
  have hword :
      intrinsicCollarTerminalBoundaryWord
          collar.intrinsicCollarPortOverlapProfile
          (collar.intrinsicCollarCorrectionWord sourceEscape)
          (Sum.inr targetPort) =
        crossFaceZeroColor (!coordinate) := by
    rw [collar.intrinsicCollarTerminalBoundaryWord_target_eq_boundaryState,
      commonDiscrepancyBoundaryState_apply]
    simpa only [targetPortCommonTerminal] using hboundary
  have hcharged : crossFaceCoordinate coordinate
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative
          (Sum.inr unmatched))) ≠ 0 := by
    change crossFaceCoordinate coordinate
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (Sum.inr targetPort)) ≠ 0
    rw [hword]
    simpa using
      crossFaceCoordinate_complement_zeroColor_ne_zero (!coordinate)
  let witness :=
    collar.chargedTerminalColorWitness_of_coordinate_ne_zero
      sourceEscape coordinate (Sum.inr unmatched) hcharged
  let action := witness.nonempty_kempeAction
  exact ⟨action, action.sameBaseReentry⟩

namespace ClosedSupportRoute

variable {corner : turn.ComplementarySupportCorner}

/-- The structured interior event emitted by the second turn of a closed
route. -/
structure InteriorTransverseTurn (route : corner.ClosedSupportRoute) where
  before : List corner.complementarySupportGraph.edgeSet
  first : corner.complementarySupportGraph.edgeSet
  second : corner.complementarySupportGraph.edgeSet
  after : List corner.complementarySupportGraph.edgeSet
  firstSecond : corner.complementarySupportGraph.lineGraph.Adj first second
  thirdEdge : collar.commonCore.edgeSet
  word_eq : route.rootedAtLaunch.cycle.edgeSubtypeSupport =
    before ++ first :: second :: after
  companion_ne :
    (corner.supportEdgeColorState first).companionColor ≠
      (corner.supportEdgeColorState second).companionColor
  firstThird : collar.commonCore.lineGraph.Adj
    (corner.supportEdgeAmbientEdge first) thirdEdge
  secondThird : collar.commonCore.lineGraph.Adj
    (corner.supportEdgeAmbientEdge second) thirdEdge
  discrepancy : collar.commonDiscrepancy sourceEscape thirdEdge =
    crossFaceZeroColor (!coordinate)

namespace InteriorTransverseTurn

variable {route : corner.ClosedSupportRoute}
  (interior : route.InteriorTransverseTurn)

/-- The interior event is the next full signed turn in the toggled
coordinate. -/
noncomputable def toScalarCompanionTurn :
    collar.ScalarCompanionTurn sourceEscape (!coordinate) where
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
    simpa only [supportEdgeColorState, discrepancyColorState] using
      interior.companion_ne
  thirdDiscrepancy := interior.discrepancy

end InteriorTransverseTurn

/-- A generic closed route is consumed by a Kempe action or emits the next
signed turn. -/
theorem kempeAction_and_sameBaseReentry_or_interiorTransverseTurn
    (route : corner.ClosedSupportRoute) :
    (∃ representative : IntrinsicCollarTerminalRepresentative
        collar.intrinsicCollarPortOverlapProfile,
      ChargedTerminalKempeAction collar sourceEscape coordinate
          representative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
      Nonempty route.InteriorTransverseTurn := by
  rcases route.exists_internal_boundaryPort_or_transverseEmission with
    ⟨before, first, second, after, hadjacent, hword, hcompanion,
      hsource | htarget | hinterior⟩
  · rcases hsource with ⟨sourcePort, hvertex⟩
    rcases corner.changedSupportEdges_sourcePort_kempeAction_and_sameBaseReentry
        first second hadjacent hcompanion sourcePort hvertex with
      ⟨action, hreentry⟩
    exact Or.inl ⟨Sum.inl sourcePort, action, hreentry⟩
  · rcases htarget with ⟨targetPort, hvertex⟩
    let hnoOverlap :=
      corner.no_portOverlap_of_supportEdge_adjacent_at_targetPort
        first second hadjacent targetPort hvertex
    let unmatched :=
      corner.unmatchedTargetPortOfNoOverlap targetPort hnoOverlap
    have haction :=
      corner.changedSupportEdges_targetPort_kempeAction_and_sameBaseReentry
        first second hadjacent hcompanion targetPort hvertex
    exact Or.inl ⟨Sum.inr unmatched, haction⟩
  · rcases hinterior with
      ⟨thirdEdge, hfirstThird, hsecondThird, hdiscrepancy, _hsupport⟩
    exact Or.inr ⟨{
      before := before
      first := first
      second := second
      after := after
      firstSecond := hadjacent
      thirdEdge := thirdEdge
      word_eq := hword
      companion_ne := hcompanion
      firstThird := hfirstThird
      secondThird := hsecondThird
      discrepancy := hdiscrepancy }⟩

/-- Closed-route resolution stated directly with its next turn. -/
theorem kempeAction_and_sameBaseReentry_or_nextTurn
    (route : corner.ClosedSupportRoute) :
    (∃ representative : IntrinsicCollarTerminalRepresentative
        collar.intrinsicCollarPortOverlapProfile,
      ChargedTerminalKempeAction collar sourceEscape coordinate
          representative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
      Nonempty (collar.ScalarCompanionTurn sourceEscape (!coordinate)) := by
  rcases route.kempeAction_and_sameBaseReentry_or_interiorTransverseTurn with
    haction | hturn
  · exact Or.inl haction
  · rcases hturn with ⟨interior⟩
    exact Or.inr ⟨interior.toScalarCompanionTurn⟩

end ClosedSupportRoute

/-- Complete resolution of one complementary-support corner. -/
theorem exists_kempeAction_and_sameBaseReentry_or_nextTurn
    (corner : turn.ComplementarySupportCorner) :
    (∃ (actionCoordinate : Bool)
        (representative : IntrinsicCollarTerminalRepresentative
          collar.intrinsicCollarPortOverlapProfile),
      ChargedTerminalKempeAction collar sourceEscape actionCoordinate
          representative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
      Nonempty (collar.ScalarCompanionTurn sourceEscape (!coordinate)) := by
  rcases corner.exists_kempeAction_and_sameBaseReentry_or_closedSupportRoute with
    haction | hclosed
  · rcases haction with ⟨representative, action, hreentry⟩
    exact Or.inl ⟨!coordinate, representative, action, hreentry⟩
  · rcases hclosed with ⟨route⟩
    rcases route.kempeAction_and_sameBaseReentry_or_nextTurn with
      haction | hnext
    · rcases haction with ⟨representative, action, hreentry⟩
      exact Or.inl ⟨coordinate, representative, action, hreentry⟩
    · exact Or.inr hnext

end ScalarCompanionTurn.ComplementarySupportCorner

namespace ScalarCompanionTurn

/-- One-step alternating dynamics: every signed turn yields a verified
Kempe action with reentry or a full signed turn in the toggled coordinate. -/
theorem exists_kempeAction_and_sameBaseReentry_or_nextTurn
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    (∃ (actionCoordinate : Bool)
        (representative : IntrinsicCollarTerminalRepresentative
          collar.intrinsicCollarPortOverlapProfile),
      ChargedTerminalKempeAction collar sourceEscape actionCoordinate
          representative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
      Nonempty (collar.ScalarCompanionTurn sourceEscape (!coordinate)) := by
  rcases turn.nonempty_complementarySupportCorner with ⟨corner⟩
  exact corner.exists_kempeAction_and_sameBaseReentry_or_nextTurn

end ScalarCompanionTurn
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
