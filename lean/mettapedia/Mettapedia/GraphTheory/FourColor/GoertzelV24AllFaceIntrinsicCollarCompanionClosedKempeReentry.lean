import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionClosedBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionChargedKempeReentry

/-! Kempe reentry forced by a boundary turn on a closed support route. -/

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

/-- A target port with no source overlap, regarded as a canonical terminal
representative. -/
def unmatchedTargetPortOfNoOverlap
    (_corner : change.ComplementarySupportCorner)
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

/-- A second companion turn at a source port supplies an actual one-step
Kempe action and canonical same-base reentry. -/
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
    ChargedTerminalKempeAction collar sourceEscape
        firstHit.transfer.coordinate (Sum.inl sourcePort) ∧
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
        crossFaceZeroColor (!firstHit.transfer.coordinate) := by
    rw [collar.intrinsicCollarTerminalBoundaryWord_source_eq_boundaryState,
      commonDiscrepancyBoundaryState_apply]
    simpa only [sourcePortCommonTerminal] using hboundary
  have hcharged : crossFaceCoordinate firstHit.transfer.coordinate
      (intrinsicCollarTerminalBoundaryWord
          collar.intrinsicCollarPortOverlapProfile
          (collar.intrinsicCollarCorrectionWord sourceEscape)
          (intrinsicCollarTerminalCoordinateOfRepresentative
          ((Sum.inl sourcePort) :
            IntrinsicCollarTerminalRepresentative
              collar.intrinsicCollarPortOverlapProfile))) ≠ 0 := by
    change crossFaceCoordinate firstHit.transfer.coordinate
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (Sum.inl sourcePort)) ≠ 0
    rw [hword]
    simpa using
      crossFaceCoordinate_complement_zeroColor_ne_zero
        (!firstHit.transfer.coordinate)
  let witness :=
    collar.chargedTerminalColorWitness_of_coordinate_ne_zero
      sourceEscape firstHit.transfer.coordinate
      ((Sum.inl sourcePort) :
        IntrinsicCollarTerminalRepresentative
          collar.intrinsicCollarPortOverlapProfile)
      hcharged
  let action := witness.nonempty_kempeAction
  exact ⟨action, action.sameBaseReentry⟩

/-- The same construction at a target port, using its certified unmatched
terminal representative. -/
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
    ChargedTerminalKempeAction collar sourceEscape
        firstHit.transfer.coordinate (Sum.inr unmatched) ∧
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
        crossFaceZeroColor (!firstHit.transfer.coordinate) := by
    rw [collar.intrinsicCollarTerminalBoundaryWord_target_eq_boundaryState,
      commonDiscrepancyBoundaryState_apply]
    simpa only [targetPortCommonTerminal] using hboundary
  have hcharged : crossFaceCoordinate firstHit.transfer.coordinate
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative
          (Sum.inr unmatched))) ≠ 0 := by
    change crossFaceCoordinate firstHit.transfer.coordinate
      (intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (Sum.inr targetPort)) ≠ 0
    rw [hword]
    simpa using
      crossFaceCoordinate_complement_zeroColor_ne_zero
        (!firstHit.transfer.coordinate)
  let witness :=
    collar.chargedTerminalColorWitness_of_coordinate_ne_zero
      sourceEscape firstHit.transfer.coordinate (Sum.inr unmatched)
      hcharged
  let action := witness.nonempty_kempeAction
  exact ⟨action, action.sameBaseReentry⟩

namespace ClosedSupportRoute

variable {corner : change.ComplementarySupportCorner}

/-- The exact residual event when the second turn of a closed route is
interior: two consecutive complementary-support edges change companion and
emit the distinguished complementary color on a third edge, which lies in
the original scalar support. -/
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
    crossFaceZeroColor (!firstHit.transfer.coordinate)

/-- Closed routes no longer end at a bare boundary turn.  Such a turn is
consumed by a real Kempe action and canonical same-base reentry; the sole
remaining alternative is an interior turn back to the original scalar
coordinate. -/
theorem kempeReentry_or_internal_transverseEmission
    (route : corner.ClosedSupportRoute) :
    (∃ representative : IntrinsicCollarTerminalRepresentative
        collar.intrinsicCollarPortOverlapProfile,
      ChargedTerminalKempeAction collar sourceEscape
          firstHit.transfer.coordinate representative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
      ∃ (before : List corner.complementarySupportGraph.edgeSet)
          (first second : corner.complementarySupportGraph.edgeSet)
          (after : List corner.complementarySupportGraph.edgeSet)
          (_hadjacent : corner.complementarySupportGraph.lineGraph.Adj
            first second)
          (thirdEdge : collar.commonCore.edgeSet),
        route.rootedAtLaunch.cycle.edgeSubtypeSupport =
            before ++ first :: second :: after ∧
          (corner.supportEdgeColorState first).companionColor ≠
            (corner.supportEdgeColorState second).companionColor ∧
          collar.commonCore.lineGraph.Adj
              (corner.supportEdgeAmbientEdge first) thirdEdge ∧
          collar.commonCore.lineGraph.Adj
              (corner.supportEdgeAmbientEdge second) thirdEdge ∧
          collar.commonDiscrepancy sourceEscape thirdEdge =
            crossFaceZeroColor (!firstHit.transfer.coordinate) := by
  rcases route.exists_internal_exactBoundaryPort_or_transverseEmission with
    ⟨before, first, second, after, hadjacent, hword, hcompanion,
      hsource | htarget | hinterior⟩
  · rcases hsource with
      ⟨sourcePort, hvertex, _hnoOverlap, _hboundary⟩
    rcases corner.changedSupportEdges_sourcePort_kempeAction_and_sameBaseReentry
        first second hadjacent hcompanion sourcePort hvertex with
      ⟨action, hreentry⟩
    exact Or.inl ⟨Sum.inl sourcePort, action, hreentry⟩
  · rcases htarget with
      ⟨targetPort, hvertex, hnoOverlap, _hboundary⟩
    let unmatched :=
      corner.unmatchedTargetPortOfNoOverlap targetPort hnoOverlap
    have haction :=
      corner.changedSupportEdges_targetPort_kempeAction_and_sameBaseReentry
        first second hadjacent hcompanion targetPort hvertex
    exact Or.inl ⟨Sum.inr unmatched, haction⟩
  · rcases hinterior with
      ⟨thirdEdge, hfirstThird, hsecondThird, hdiscrepancy⟩
    exact Or.inr ⟨before, first, second, after, hadjacent, thirdEdge,
      hword, hcompanion, hfirstThird, hsecondThird, hdiscrepancy⟩

/-- Structured form of the same closed-route dichotomy. -/
theorem kempeReentry_or_internalTransverseTurn
    (route : corner.ClosedSupportRoute) :
    (∃ representative : IntrinsicCollarTerminalRepresentative
        collar.intrinsicCollarPortOverlapProfile,
      ChargedTerminalKempeAction collar sourceEscape
          firstHit.transfer.coordinate representative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
      Nonempty route.InteriorTransverseTurn := by
  rcases route.kempeReentry_or_internal_transverseEmission with
    haction |
      ⟨before, first, second, after, firstSecond, thirdEdge,
        hword, hcompanion, hfirstThird, hsecondThird, hdiscrepancy⟩
  · exact Or.inl haction
  · exact Or.inr ⟨{
      before := before
      first := first
      second := second
      after := after
      firstSecond := firstSecond
      thirdEdge := thirdEdge
      word_eq := hword
      companion_ne := hcompanion
      firstThird := hfirstThird
      secondThird := hsecondThird
      discrepancy := hdiscrepancy }⟩

end ClosedSupportRoute

/-- Complete complementary-support resolution with coloring content. Every
charged endpoint and every boundary turn of a closed route is consumed by
an actual Kempe action and canonical same-base reentry. The only residual
case is an interior transverse turn switching back to the original scalar
coordinate. -/
theorem kempeReentry_or_exists_closedSupportInteriorTransverseTurn
    (corner : change.ComplementarySupportCorner) :
    (∃ (coordinate : Bool)
        (representative : IntrinsicCollarTerminalRepresentative
          collar.intrinsicCollarPortOverlapProfile),
      ChargedTerminalKempeAction collar sourceEscape coordinate
          representative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
      ∃ route : corner.ClosedSupportRoute,
        Nonempty route.InteriorTransverseTurn := by
  rcases corner.chargedSupportRoute_or_closedSupportRoute with
    hcharged | hclosed
  · rcases hcharged with ⟨route⟩
    rcases route.finishKempeAction_and_sameBaseReentry with
      ⟨action, hreentry⟩
    exact Or.inl ⟨!firstHit.transfer.coordinate,
      route.finishRepresentative, action, hreentry⟩
  · rcases hclosed with ⟨route⟩
    rcases route.kempeReentry_or_internalTransverseTurn with
      ⟨representative, action, hreentry⟩ | hturn
    · exact Or.inl ⟨firstHit.transfer.coordinate,
        representative, action, hreentry⟩
    · exact Or.inr ⟨route, hturn⟩

end FirstHitSingletonCompanionTransferPath.TransverseCompanionChange.ComplementarySupportCorner
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
