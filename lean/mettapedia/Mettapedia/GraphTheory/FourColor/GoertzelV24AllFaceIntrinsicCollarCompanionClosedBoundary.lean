import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionClosedRouteTurn

/-! Boundary values forced by the second turn on a closed support route. -/

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
  {firstHit : FirstHitSingletonCompanionTransferPath
    (collar := collar) (sourceEscape := sourceEscape)}
  {change : firstHit.TransverseCompanionChange}

namespace FirstHitSingletonCompanionTransferPath.TransverseCompanionChange.ComplementarySupportCorner

variable (corner : change.ComplementarySupportCorner)

/-- Two adjacent complementary-support edges give two distinct common-core
edges incident to their common junction. -/
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

/-- Consequently, the common-core junction of adjacent support edges has
degree at least two. -/
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

/-- A support adjacency meeting a source port cannot meet a literal
source--target port overlap, since such an overlap has common-core degree one. -/
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

/-- The analogous no-overlap fact at a target port. -/
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

/-- At a source port, the adjacent support pair exhausts the two remaining
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

/-- At a target port, the adjacent support pair likewise exhausts the
remaining common-core edges. -/
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

/-- A companion-changing adjacent support pair has total discrepancy equal
to the distinguished color of its current coordinate. -/
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
      crossFaceZeroColor (!firstHit.transfer.coordinate) := by
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
      (!firstHit.transfer.coordinate) ambientAdj
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
        crossFaceZeroColor (!firstHit.transfer.coordinate) by
      calc
        _ = (collar.sourceCommonColoring sourceEscape
                (corner.supportEdgeAmbientEdge first) +
              collar.sourceCommonColoring sourceEscape
                (corner.supportEdgeAmbientEdge second)) +
            (collar.targetCommonColoring
                (corner.supportEdgeAmbientEdge first) +
              collar.targetCommonColoring
                (corner.supportEdgeAmbientEdge second)) := by abel
        _ = crossFaceZeroColor (!firstHit.transfer.coordinate) := by
          simpa only [supportEdgeColorState_sourceColor,
            supportEdgeColorState_targetColor] using hemitted)

/-- A companion change at a source port is an exact nonzero collar-boundary
value, not an unresolved overlap case. -/
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
      crossFaceZeroColor (!firstHit.transfer.coordinate) := by
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

/-- The target-port boundary value obeys the same exact equation. -/
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
      crossFaceZeroColor (!firstHit.transfer.coordinate) := by
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

namespace ClosedSupportRoute

variable {corner : change.ComplementarySupportCorner}

/-- Every closed support route has a second turn whose emitted discrepancy
is realized exactly: as a nonoverlapping source boundary value, a
nonoverlapping target boundary value, or an interior transverse edge. -/
theorem exists_internal_exactBoundaryPort_or_transverseEmission
    (route : corner.ClosedSupportRoute) :
    ∃ (before : List corner.complementarySupportGraph.edgeSet)
        (first second : corner.complementarySupportGraph.edgeSet)
        (after : List corner.complementarySupportGraph.edgeSet)
        (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
          first second),
      route.rootedAtLaunch.cycle.edgeSubtypeSupport =
          before ++ first :: second :: after ∧
        (corner.supportEdgeColorState first).companionColor ≠
          (corner.supportEdgeColorState second).companionColor ∧
        ((∃ sourcePort : Fin 4,
            SimpleGraph.lineGraphCommonVertex
                (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
              collar.sourcePortInCommonCore sourcePort ∧
            (∀ targetPort : Fin 4,
              ¬ collar.PortOverlap sourcePort targetPort) ∧
            vertexKirchhoffSum collar.commonCore
                (collar.commonDiscrepancy sourceEscape)
                (collar.sourcePortInCommonCore sourcePort) =
              crossFaceZeroColor (!firstHit.transfer.coordinate)) ∨
          (∃ targetPort : Fin 4,
            SimpleGraph.lineGraphCommonVertex
                (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
              collar.targetPortInCommonCore targetPort ∧
            (∀ sourcePort : Fin 4,
              ¬ collar.PortOverlap sourcePort targetPort) ∧
            vertexKirchhoffSum collar.commonCore
                (collar.commonDiscrepancy sourceEscape)
                (collar.targetPortInCommonCore targetPort) =
              crossFaceZeroColor (!firstHit.transfer.coordinate)) ∨
          ∃ thirdEdge : collar.commonCore.edgeSet,
            collar.commonCore.lineGraph.Adj
                (corner.supportEdgeAmbientEdge first) thirdEdge ∧
              collar.commonCore.lineGraph.Adj
                (corner.supportEdgeAmbientEdge second) thirdEdge ∧
              collar.commonDiscrepancy sourceEscape thirdEdge =
                crossFaceZeroColor (!firstHit.transfer.coordinate)) := by
  rcases route.exists_internal_boundaryPort_or_transverseEmission with
    ⟨before, first, second, after, hadjacent, hword, hcompanion,
      hsource | htarget | hinterior⟩
  · rcases hsource with ⟨sourcePort, hvertex⟩
    exact ⟨before, first, second, after, hadjacent, hword, hcompanion,
      Or.inl ⟨sourcePort, hvertex,
        corner.no_portOverlap_of_supportEdge_adjacent_at_sourcePort
          first second hadjacent sourcePort hvertex,
        corner.changedSupportEdges_sourcePort_boundaryValue_eq_zeroColor
          first second hadjacent hcompanion sourcePort hvertex⟩⟩
  · rcases htarget with ⟨targetPort, hvertex⟩
    exact ⟨before, first, second, after, hadjacent, hword, hcompanion,
      Or.inr (Or.inl ⟨targetPort, hvertex,
        corner.no_portOverlap_of_supportEdge_adjacent_at_targetPort
          first second hadjacent targetPort hvertex,
        corner.changedSupportEdges_targetPort_boundaryValue_eq_zeroColor
          first second hadjacent hcompanion targetPort hvertex⟩)⟩
  · rcases hinterior with
      ⟨thirdEdge, hfirstThird, hsecondThird, hdiscrepancy, _hsupport⟩
    exact ⟨before, first, second, after, hadjacent, hword, hcompanion,
      Or.inr (Or.inr ⟨thirdEdge, hfirstThird, hsecondThird, by
        simpa only [commonDiscrepancy_apply] using hdiscrepancy⟩)⟩

end ClosedSupportRoute
end FirstHitSingletonCompanionTransferPath.TransverseCompanionChange.ComplementarySupportCorner
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
