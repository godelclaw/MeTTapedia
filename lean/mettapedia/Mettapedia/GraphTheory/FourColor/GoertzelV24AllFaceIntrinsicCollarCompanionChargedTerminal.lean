import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionSupportContinuation

/-! Exact collar-color witnesses at charged complementary-support terminals. -/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open GoertzelV24CorridorPumping
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
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
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

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

/-- Every source missing-color request is a genuine Tait color. -/
theorem sourceOwnBoundaryColor_ne_zero
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (sourcePort : Fin 4) :
    collar.sourceData.degreeTwoBoundaryData.colorWord
        sourceEscape.coloring sourcePort ≠ 0 := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  exact collar.sourceData.degreeTwoBoundaryData.colorWord_ne_zero
    (collar.sourceData.degreeTwoBoundaryData_wellFormed hcubic)
      sourceEscape.coloring sourcePort

/-- Every color read on a source boundary edge in the target deletion is
nonzero. -/
theorem sourceBoundaryWord_apply_ne_zero
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort : Fin 4) :
    collar.sourceBoundaryWord sourcePort ≠ 0 := by
  exact collar.targetEscape.isTait (collar.sourceBoundaryInTarget sourcePort)

/-- Every target missing-color request is a genuine Tait color. -/
theorem targetOwnBoundaryColor_ne_zero
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) :
    collar.targetData.degreeTwoBoundaryData.colorWord
        collar.targetEscape.coloring targetPort ≠ 0 := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  exact collar.targetData.degreeTwoBoundaryData.colorWord_ne_zero
    (collar.targetData.degreeTwoBoundaryData_wellFormed hcubic)
      collar.targetEscape.coloring targetPort

/-- Every color read on a target boundary edge in the source deletion is
nonzero. -/
theorem targetBoundaryWordInSource_apply_ne_zero
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (targetPort : Fin 4) :
    collar.targetBoundaryWordInSource sourceEscape targetPort ≠ 0 := by
  exact sourceEscape.isTait (collar.targetBoundaryInSource targetPort)

/-- At an unmatched source port, the exact terminal word consists of the
source missing-color request and the target coloring's source-boundary
color, with no additional overlap summand. -/
theorem intrinsicCollarTerminalBoundaryWord_source_eq_boundaryColors_of_noOverlap
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (sourcePort : Fin 4)
    (hnoOverlap : ∀ targetPort : Fin 4,
      ¬ collar.PortOverlap sourcePort targetPort) :
    intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (Sum.inl sourcePort) =
      collar.sourceData.degreeTwoBoundaryData.colorWord
          sourceEscape.coloring sourcePort +
        collar.sourceBoundaryWord sourcePort := by
  classical
  have hsum :
      (∑ targetPort : Fin 4,
        if (sourcePort, targetPort) ∈
            collar.intrinsicCollarPortOverlapProfile then
          collar.intrinsicCollarCorrectionWord sourceEscape
            (Sum.inr (some targetPort))
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro targetPort _htarget
    rw [if_neg]
    intro hoverlap
    exact hnoOverlap targetPort
      ((collar.mem_intrinsicCollarPortOverlapProfile_iff _).1 hoverlap)
  rw [intrinsicCollarTerminalBoundaryWord, hsum, add_zero]
  exact collar.intrinsicCollarCorrectionWord_sourceBoundary
    sourceEscape sourcePort

/-- At an unmatched target port, the exact terminal word consists of the
target missing-color request and the source coloring's target-boundary
color, with no additional overlap summand. -/
theorem intrinsicCollarTerminalBoundaryWord_target_eq_boundaryColors_of_noOverlap
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (targetPort : Fin 4)
    (hnoOverlap : ∀ sourcePort : Fin 4,
      ¬ collar.PortOverlap sourcePort targetPort) :
    intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (Sum.inr targetPort) =
      collar.targetData.degreeTwoBoundaryData.colorWord
          collar.targetEscape.coloring targetPort +
        collar.targetBoundaryWordInSource sourceEscape targetPort := by
  classical
  have hsum :
      (∑ sourcePort : Fin 4,
        if (sourcePort, targetPort) ∈
            collar.intrinsicCollarPortOverlapProfile then
          collar.intrinsicCollarCorrectionWord sourceEscape
            (Sum.inl (some sourcePort))
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro sourcePort _hsource
    rw [if_neg]
    intro hoverlap
    exact hnoOverlap sourcePort
      ((collar.mem_intrinsicCollarPortOverlapProfile_iff _).1 hoverlap)
  rw [intrinsicCollarTerminalBoundaryWord, hsum, add_zero]
  exact collar.intrinsicCollarCorrectionWord_targetBoundary
    sourceEscape targetPort

/-- At a literal source-target port overlap, the common core has one stem
and the fixed terminal word is exactly the discrepancy on that stem. -/
theorem exists_matchedStem_terminalBoundaryWord_eq_commonDiscrepancy
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (sourcePort targetPort : Fin 4)
    (hoverlap : collar.PortOverlap sourcePort targetPort) :
    ∃ stem : collar.commonCore.edgeSet,
      incidentEdgeFinset collar.commonCore
          (collar.sourcePortInCommonCore sourcePort) = {stem} ∧
        intrinsicCollarTerminalBoundaryWord
            collar.intrinsicCollarPortOverlapProfile
            (collar.intrinsicCollarCorrectionWord sourceEscape)
            (Sum.inl sourcePort) =
          collar.commonDiscrepancy sourceEscape stem := by
  classical
  rcases collar.exists_commonEdge_incident_eq_singleton_of_portOverlap
      sourcePort targetPort hoverlap with ⟨stem, hstem⟩
  refine ⟨stem, hstem, ?_⟩
  have hstem' : incidentEdgeFinset collar.commonCore
      (collar.sourcePortCommonTerminal sourcePort).1 = {stem} := by
    simpa only [sourcePortCommonTerminal] using hstem
  rw [collar.intrinsicCollarTerminalBoundaryWord_source_eq_boundaryState,
    commonDiscrepancyBoundaryState_apply, vertexKirchhoffSum, hstem',
    Finset.sum_singleton]

/-- A charged canonical terminal carries one of three exact local color
witnesses: an unmatched source boundary mismatch, a unique matched stem
mismatch, or an unmatched target boundary mismatch. -/
inductive ChargedTerminalColorWitness
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool) :
    IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile → Prop
  | unmatchedSource
      (sourcePort : Fin 4)
      (noOverlap : ∀ targetPort : Fin 4,
        ¬ collar.PortOverlap sourcePort targetPort)
      (mismatch :
        (collar.sourceData.degreeTwoBoundaryData.colorWord
              sourceEscape.coloring sourcePort =
                crossFaceZeroColor coordinate ∧
            collar.sourceBoundaryWord sourcePort ≠
                crossFaceZeroColor coordinate) ∨
          (collar.sourceData.degreeTwoBoundaryData.colorWord
              sourceEscape.coloring sourcePort ≠
                crossFaceZeroColor coordinate ∧
            collar.sourceBoundaryWord sourcePort =
                crossFaceZeroColor coordinate)) :
      ChargedTerminalColorWitness collar sourceEscape coordinate
        (Sum.inl sourcePort)
  | matchedStem
      (sourcePort targetPort : Fin 4)
      (overlap : collar.PortOverlap sourcePort targetPort)
      (stem : collar.commonCore.edgeSet)
      (incident_eq : incidentEdgeFinset collar.commonCore
          (collar.sourcePortInCommonCore sourcePort) = {stem})
      (mismatch :
        (collar.sourceCommonColoring sourceEscape stem =
              crossFaceZeroColor coordinate ∧
            collar.targetCommonColoring stem ≠
              crossFaceZeroColor coordinate) ∨
          (collar.sourceCommonColoring sourceEscape stem ≠
              crossFaceZeroColor coordinate ∧
            collar.targetCommonColoring stem =
              crossFaceZeroColor coordinate)) :
      ChargedTerminalColorWitness collar sourceEscape coordinate
        (Sum.inl sourcePort)
  | unmatchedTarget
      (targetPort : ↑(intrinsicCollarUnmatchedTargetPorts
        collar.intrinsicCollarPortOverlapProfile))
      (noOverlap : ∀ sourcePort : Fin 4,
        ¬ collar.PortOverlap sourcePort targetPort.1)
      (mismatch :
        (collar.targetData.degreeTwoBoundaryData.colorWord
              collar.targetEscape.coloring targetPort.1 =
                crossFaceZeroColor coordinate ∧
            collar.targetBoundaryWordInSource sourceEscape targetPort.1 ≠
                crossFaceZeroColor coordinate) ∨
          (collar.targetData.degreeTwoBoundaryData.colorWord
              collar.targetEscape.coloring targetPort.1 ≠
                crossFaceZeroColor coordinate ∧
            collar.targetBoundaryWordInSource sourceEscape targetPort.1 =
                crossFaceZeroColor coordinate)) :
      ChargedTerminalColorWitness collar sourceEscape coordinate
        (Sum.inr targetPort)

/-- Every nonzero scalar coordinate of a canonical terminal word is
resolved into one of the three concrete collar-color witnesses. -/
theorem chargedTerminalColorWitness_of_coordinate_ne_zero
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (coordinate : Bool)
    (representative : IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile)
    (hcharged : crossFaceCoordinate coordinate
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative
          representative)) ≠ 0) :
    ChargedTerminalColorWitness collar sourceEscape coordinate
      representative := by
  classical
  rcases representative with sourcePort | targetPort
  · by_cases hoverlap : ∃ targetPort : Fin 4,
        collar.PortOverlap sourcePort targetPort
    · rcases hoverlap with ⟨targetPort, hoverlap⟩
      rcases collar.exists_matchedStem_terminalBoundaryWord_eq_commonDiscrepancy
          sourceEscape sourcePort targetPort hoverlap with
        ⟨stem, hstem, hboundary⟩
      apply ChargedTerminalColorWitness.matchedStem
        sourcePort targetPort hoverlap stem hstem
      apply (crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor
        coordinate
        (collar.sourceCommonColoring sourceEscape stem)
        (collar.targetCommonColoring stem)
        (collar.sourceCommonColoring_isTait sourceEscape stem)
        (collar.targetCommonColoring_isTait stem)).1
      have hcharged' := hcharged
      change crossFaceCoordinate coordinate
        (intrinsicCollarTerminalBoundaryWord
          collar.intrinsicCollarPortOverlapProfile
          (collar.intrinsicCollarCorrectionWord sourceEscape)
          (Sum.inl sourcePort)) ≠ 0 at hcharged'
      rw [hboundary] at hcharged'
      simpa only [commonDiscrepancy_apply] using hcharged'
    · have hnoOverlap : ∀ targetPort : Fin 4,
          ¬ collar.PortOverlap sourcePort targetPort := by
        simpa only [not_exists] using hoverlap
      apply ChargedTerminalColorWitness.unmatchedSource
        sourcePort hnoOverlap
      apply (crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor
        coordinate
        (collar.sourceData.degreeTwoBoundaryData.colorWord
          sourceEscape.coloring sourcePort)
        (collar.sourceBoundaryWord sourcePort)
        (collar.sourceOwnBoundaryColor_ne_zero sourceEscape sourcePort)
        (collar.sourceBoundaryWord_apply_ne_zero sourcePort)).1
      rw [← collar.intrinsicCollarTerminalBoundaryWord_source_eq_boundaryColors_of_noOverlap
        sourceEscape sourcePort hnoOverlap]
      exact hcharged
  · have hnoProfile : ∀ sourcePort : Fin 4,
        (sourcePort, targetPort.1) ∉
          collar.intrinsicCollarPortOverlapProfile := by
      simpa [intrinsicCollarUnmatchedTargetPorts] using targetPort.2
    have hnoOverlap : ∀ sourcePort : Fin 4,
        ¬ collar.PortOverlap sourcePort targetPort.1 := by
      intro sourcePort hoverlap
      exact hnoProfile sourcePort
        ((collar.mem_intrinsicCollarPortOverlapProfile_iff _).2 hoverlap)
    apply ChargedTerminalColorWitness.unmatchedTarget
      targetPort hnoOverlap
    apply (crossFaceCoordinate_add_ne_zero_iff_exactlyOne_zeroColor
      coordinate
      (collar.targetData.degreeTwoBoundaryData.colorWord
        collar.targetEscape.coloring targetPort.1)
      (collar.targetBoundaryWordInSource sourceEscape targetPort.1)
      (collar.targetOwnBoundaryColor_ne_zero targetPort.1)
      (collar.targetBoundaryWordInSource_apply_ne_zero
        sourceEscape targetPort.1)).1
    rw [← collar.intrinsicCollarTerminalBoundaryWord_target_eq_boundaryColors_of_noOverlap
      sourceEscape targetPort.1 hnoOverlap]
    exact hcharged

namespace FirstHitSingletonCompanionTransferPath

variable {firstHit : FirstHitSingletonCompanionTransferPath
  (collar := collar) (sourceEscape := sourceEscape)}

namespace TransverseCompanionChange

variable {change : firstHit.TransverseCompanionChange}

namespace ComplementarySupportCorner

namespace ChargedSupportRoute

variable {corner : change.ComplementarySupportCorner}

/-- The canonical endpoint representative of either charged-route
constructor. -/
noncomputable def finishRepresentative
    (route : corner.ChargedSupportRoute) :
    IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile :=
  match route with
  | .direct strand _ => strand.terminalRepresentative
  | .continued _strand _continuation routeData =>
      routeData.finishRepresentative

/-- Every charged complementary-support route terminates at an explicit
unmatched-boundary or matched-stem color mismatch. -/
theorem finishColorWitness
    (route : corner.ChargedSupportRoute) :
    ChargedTerminalColorWitness collar sourceEscape
      (!firstHit.transfer.coordinate) route.finishRepresentative := by
  cases route with
  | direct strand hcharged =>
      change ChargedTerminalColorWitness collar sourceEscape
        (!firstHit.transfer.coordinate) strand.terminalRepresentative
      apply collar.chargedTerminalColorWitness_of_coordinate_ne_zero
        sourceEscape (!firstHit.transfer.coordinate)
          strand.terminalRepresentative
      rw [← strand.terminalBoundaryCoordinate_eq_word]
      exact hcharged
  | continued strand continuation routeData =>
      change ChargedTerminalColorWitness collar sourceEscape
        (!firstHit.transfer.coordinate) routeData.finishRepresentative
      apply collar.chargedTerminalColorWitness_of_coordinate_ne_zero
        sourceEscape (!firstHit.transfer.coordinate)
          routeData.finishRepresentative
      exact routeData.finishBoundaryWord_coordinate_ne_zero

end ChargedSupportRoute
end ComplementarySupportCorner
end TransverseCompanionChange
end FirstHitSingletonCompanionTransferPath
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
