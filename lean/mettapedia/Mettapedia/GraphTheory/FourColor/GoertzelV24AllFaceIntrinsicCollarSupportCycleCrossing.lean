import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarTerminalAlternation
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceEscapeStateOneZeroFlow
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalSeparator

/-! Ambient support cycles coupling an intrinsic collar discrepancy to its
remote facial-dual separator. -/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedChainExtension
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

private theorem exists_other_ne_zero_of_sum_eq_zero
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (value : Index → F2) (pivot : Index)
    (hpivot : value pivot ≠ 0)
    (hsum : ∑ index, value index = 0) :
    ∃ other : Index, other ≠ pivot ∧ value other ≠ 0 := by
  by_contra hother
  push Not at hother
  have hsingle : (∑ index, value index) = value pivot := by
    rw [Finset.sum_eq_single pivot]
    · intro other _hother hne
      exact hother other hne
    · exact fun hnot => False.elim (hnot (Finset.mem_univ pivot))
  exact hpivot (hsingle.symm.trans hsum)

private theorem f2_eq_one_of_ne_zero (value : F2) (hvalue : value ≠ 0) :
    value = 1 := by
  fin_cases value
  · exact False.elim (hvalue rfl)
  · rfl

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open RotationOrderedFusionEscapeColorState

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

/-- One scalar coordinate of the completed source--target discrepancy has
a simple ambient support cycle through the target central edge.  Primal--dual
intersection parity forces the same cycle to cross the remote dual cycle at
a second, distinct primal edge. -/
theorem exists_scalarSupportCycle_with_other_remoteCrossing
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    ∃ (coordinate : Bool) (root : V) (supportCycle : G.Walk root root)
        (otherCrossing : G.edgeSet),
      supportCycle.IsCycle ∧
        (targetEdge : Sym2 V) ∈ supportCycle.edges ∧
        otherCrossing ∈ cycle.crossingEdges ∧
        otherCrossing ≠ targetEdge ∧
        (otherCrossing : Sym2 V) ∈ supportCycle.edges ∧
        ∀ edge : G.edgeSet,
          (edge : Sym2 V) ∈ supportCycle.edges →
            crossFaceCoordinate coordinate
              (alignedOneZeroDiscrepancy collar sourceEscape edge) ≠ 0 := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hsourceTargetNonzero :
      oneZeroAmbientChain collar.sourceData sourceEscape.coloring
          targetEdge ≠ 0 := by
    apply oneZeroAmbientChain_ne_zero_of_ne_central
      collar.sourceData hcubic sourceEscape.coloring sourceEscape.isTait
    exact (cycle.crossingEdge_ne_central collar.targetCrossing).symm
  have htargetTargetZero :
      oneZeroAmbientChain collar.targetData collar.targetEscape.coloring
          targetEdge = 0 := by
    calc
      oneZeroAmbientChain collar.targetData collar.targetEscape.coloring
          targetEdge =
          oneZeroAmbientChain collar.targetData collar.targetEscape.coloring
            (centralEdge collar.targetData) :=
        congrArg
          (oneZeroAmbientChain collar.targetData
            collar.targetEscape.coloring)
          collar.targetCentral_eq.symm
      _ = 0 := oneZeroAmbientChain_central collar.targetData
        collar.targetEscape.coloring
  have htargetDiscrepancy :
      alignedOneZeroDiscrepancy collar sourceEscape targetEdge ≠ 0 := by
    unfold alignedOneZeroDiscrepancy
    change
      oneZeroAmbientChain collar.sourceData sourceEscape.coloring targetEdge +
          oneZeroAmbientChain collar.targetData
            collar.targetEscape.coloring targetEdge ≠ 0
    rw [htargetTargetZero, add_zero]
    exact hsourceTargetNonzero
  rcases exists_crossFaceCoordinate_ne_zero
      (alignedOneZeroDiscrepancy collar sourceEscape targetEdge)
      htargetDiscrepancy with
    ⟨coordinate, htargetCoordinate⟩
  let scalar : G.edgeSet → F2 := fun edge =>
    crossFaceCoordinate coordinate
      (alignedOneZeroDiscrepancy collar sourceEscape edge)
  have hscalarFlow : ∀ vertex : V,
      scalarVertexKirchhoffSum G scalar vertex = 0 := by
    intro vertex
    change scalarVertexKirchhoffSum G
      (fun edge => crossFaceCoordinate coordinate
        (alignedOneZeroDiscrepancy collar sourceEscape edge)) vertex = 0
    rw [scalarVertexKirchhoffSum_crossFaceCoordinate,
      alignedOneZeroDiscrepancy_isGraphFlow collar sourceEscape vertex]
    cases coordinate <;> rfl
  have htargetScalar : scalar targetEdge ≠ 0 := htargetCoordinate
  rcases exists_isCycle_through_of_scalar_ne_zero scalar hscalarFlow hcubic
      targetEdge htargetScalar with
    ⟨root, supportCycle, hsupportCycle, htargetMem, hcycleSupport⟩
  rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk targetEdge).1 collar.targetCrossing with
    ⟨targetStep, htargetStep⟩
  have htargetCrossingAt : cycle.crossingAt targetStep = targetEdge := by
    simpa [crossingAt] using htargetStep
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Connected :=
    orbitFaceInteriorDual_connected graphData.toRotationSystem
      minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic
  have hintersectionParity :=
    GoertzelV24DualCycleSeparator.f2CycleSpace_sum_crossings_eq_zero_of_dualCycle
      graphData minimal.facesTwoSided hdual hconnected minimal.spherical
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk cycle.isCycle
      (walkEdgeParity_mem_f2CycleSpace_of_closed supportCycle)
  have hintersectionParity' :
      (∑ step : Fin cycle.walk.length,
        walkEdgeParity supportCycle (cycle.crossingAt step)) = 0 := by
    simpa [crossingAt] using hintersectionParity
  have htargetParity :
      walkEdgeParity supportCycle (cycle.crossingAt targetStep) ≠ 0 := by
    rw [walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
      hsupportCycle.isTrail (cycle.crossingAt targetStep)]
    · exact one_ne_zero
    · simpa [htargetCrossingAt] using htargetMem
  rcases exists_other_ne_zero_of_sum_eq_zero
      (fun step : Fin cycle.walk.length =>
        walkEdgeParity supportCycle (cycle.crossingAt step))
      targetStep htargetParity hintersectionParity' with
    ⟨otherStep, hotherStep, hotherParity⟩
  let otherCrossing := cycle.crossingAt otherStep
  have hotherCrossingMem : otherCrossing ∈ cycle.crossingEdges := by
    apply (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk otherCrossing).2
    exact ⟨otherStep, rfl⟩
  have hotherCrossingNe : otherCrossing ≠ targetEdge := by
    intro hotherTarget
    apply hotherStep
    apply dualWalkCrossingEdge_injective_of_isCycle
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (orbitFace_incidence_le_two graphData.toRotationSystem)
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk cycle.isCycle
    exact hotherTarget.trans htargetCrossingAt.symm
  have hotherParityOne :
      walkEdgeParity supportCycle otherCrossing = 1 :=
    f2_eq_one_of_ne_zero _ hotherParity
  have hotherMem : (otherCrossing : Sym2 V) ∈ supportCycle.edges :=
    (walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
      hsupportCycle.isTrail otherCrossing).1 hotherParityOne
  refine ⟨coordinate, root, supportCycle, otherCrossing,
    hsupportCycle, htargetMem, hotherCrossingMem, hotherCrossingNe,
    hotherMem, ?_⟩
  intro edge hedge
  exact hcycleSupport edge hedge

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
