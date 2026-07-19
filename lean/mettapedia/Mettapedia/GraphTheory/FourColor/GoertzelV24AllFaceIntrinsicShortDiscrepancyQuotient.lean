import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortBoundaryState
import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedChainExtension

/-! Equal intrinsic-short terminal states differ by an ambient facial
circulation. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedChainExtension
open GoertzelV24MinimalFaceIntersections
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

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

/-- The ambient vertex predicate defining the common four-vertex deletion. -/
abbrev commonCorePredicate
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (vertex : V) : Prop :=
  vertex ≠ collar.sourceData.firstVertex ∧
    vertex ≠ collar.sourceData.secondVertex ∧
      vertex ≠ collar.targetData.firstVertex ∧
        vertex ≠ collar.targetData.secondVertex

/-- Extend a chain on the common four-vertex deletion by zero to the original
ambient graph. -/
def commonCoreChainExtendZero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (chain : collar.commonCore.edgeSet → Color) :
    G.edgeSet → Color :=
  inducedEdgeChainExtendZero G collar.commonCorePredicate chain

@[simp]
theorem commonCoreChainExtendZero_apply_inducedEdgeEmbedding
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (chain : collar.commonCore.edgeSet → Color)
    (edge : collar.commonCore.edgeSet) :
    collar.commonCoreChainExtendZero chain
        (inducedEdgeEmbedding G collar.commonCorePredicate edge) =
      chain edge :=
  inducedEdgeChainExtendZero_apply_inducedEdgeEmbedding
    G collar.commonCorePredicate chain edge

/-- A common-core circulation remains a circulation after zero extension to
the original graph. -/
theorem isGraphFlow_commonCoreChainExtendZero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    {chain : collar.commonCore.edgeSet → Color}
    (hflow : IsGraphFlow collar.commonCore chain) :
    IsGraphFlow G (collar.commonCoreChainExtendZero chain) :=
  isGraphFlow_inducedEdgeChainExtendZero
    G collar.commonCorePredicate hflow

/-- For chains supported on the common terminal interface, equality of the
terminal state is exactly equality modulo ambient circulations. -/
theorem commonPortBoundaryLinearMap_eq_iff_isGraphFlow_commonCoreChainExtendZero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    {left right : collar.commonCore.edgeSet → Color}
    (hleft : collar.HasCommonPortBoundary left)
    (hright : collar.HasCommonPortBoundary right) :
    collar.commonPortBoundaryLinearMap left =
        collar.commonPortBoundaryLinearMap right ↔
      IsGraphFlow G
        (collar.commonCoreChainExtendZero (left + right)) := by
  rw [collar.commonPortBoundaryLinearMap_eq_iff_add_mem_kirchhoffSubmodule
    hleft hright]
  constructor
  · intro hmember
    exact collar.isGraphFlow_commonCoreChainExtendZero
      (isGraphFlow_of_mem_kirchhoffSubmodule_univ hmember)
  · intro hflow
    apply mem_kirchhoffSubmodule_univ_of_isGraphFlow
    exact (isGraphFlow_inducedEdgeChainExtendZero_iff
      G collar.commonCorePredicate).1 hflow

/-- Specializing the exact quotient to the forced cross-base discrepancy: a
supported chain has the forced terminal state exactly when their zero-extended
difference is an ambient circulation. -/
theorem commonPortBoundaryLinearMap_eq_commonDiscrepancy_iff_isGraphFlow
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    {chain : collar.commonCore.edgeSet → Color}
    (hchain : collar.HasCommonPortBoundary chain) :
    collar.commonPortBoundaryLinearMap chain =
        collar.commonPortBoundaryLinearMap
          (collar.commonDiscrepancy sourceEscape) ↔
      IsGraphFlow G (collar.commonCoreChainExtendZero
        (chain + collar.commonDiscrepancy sourceEscape)) :=
  collar.commonPortBoundaryLinearMap_eq_iff_isGraphFlow_commonCoreChainExtendZero
    hchain (collar.commonDiscrepancy_hasCommonPortBoundary sourceEscape)

/-- Two chains with the same terminal state differ, after zero extension, by
two explicit binary combinations of ambient facial boundaries. Thus the
terminal state is a complete quotient of supported common-core chains modulo
ambient facial circulations. -/
theorem exists_orbitFaceBoundary_coefficients_of_commonPortBoundary_eq
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    {left right : collar.commonCore.edgeSet → Color}
    (hleft : collar.HasCommonPortBoundary left)
    (hright : collar.HasCommonPortBoundary right)
    (hboundary : collar.commonPortBoundaryLinearMap left =
      collar.commonPortBoundaryLinearMap right) :
    ∃ first second : OrbitFace graphData.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap graphData.toRotationSystem first =
          (fun edge =>
            (collar.commonCoreChainExtendZero (left + right) edge).1) ∧
      orbitFaceBoundaryLinearMap graphData.toRotationSystem second =
          (fun edge =>
            (collar.commonCoreChainExtendZero (left + right) edge).2) := by
  have hambientFlow : IsGraphFlow G
      (collar.commonCoreChainExtendZero (left + right)) :=
    (collar.commonPortBoundaryLinearMap_eq_iff_isGraphFlow_commonCoreChainExtendZero
      hleft hright).1 hboundary
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
  exact exists_orbitFaceBoundary_coefficients_of_isGraphFlow
    graphData minimal.facesTwoSided hdual hconnected minimal.spherical
      hambientFlow

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
