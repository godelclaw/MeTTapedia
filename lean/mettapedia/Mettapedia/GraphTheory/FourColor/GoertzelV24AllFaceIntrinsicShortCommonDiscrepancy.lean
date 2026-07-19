import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortSingletonColorObstruction

/-! The bounded-terminal color discrepancy between the two intrinsic-short
escape states. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
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

/-- The pointwise `F₂²` discrepancy between the source and target escape
colorings on their exact common core. -/
def commonDiscrepancy
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.commonCore.edgeSet → Color :=
  fun edge => collar.sourceCommonColoring sourceEscape edge +
    collar.targetCommonColoring edge

@[simp]
theorem commonDiscrepancy_apply
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) :
    collar.commonDiscrepancy sourceEscape edge =
      collar.sourceCommonColoring sourceEscape edge +
        collar.targetCommonColoring edge :=
  rfl

/-- Vanishing of the common discrepancy is exactly literal equality of the
two common-core restrictions. -/
theorem commonDiscrepancy_eq_zeroChain_iff
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.commonDiscrepancy sourceEscape = zeroChain ↔
      collar.sourceCommonColoring sourceEscape =
        collar.targetCommonColoring := by
  constructor
  · intro hzero
    apply DFunLike.ext _ _
    intro edge
    apply (add_eq_zero_iff_eq _ _).mp
    have hvalue := congrFun hzero edge
    simpa only [commonDiscrepancy_apply, zeroChain_apply] using hvalue
  · intro hcoloring
    funext edge
    have hvalue := congrArg (fun coloring => coloring edge) hcoloring
    simp only [commonDiscrepancy_apply, zeroChain_apply, hvalue,
      color_add_self]

/-- The singleton collar forces a genuinely nonzero discrepancy on the
exact common core. -/
theorem commonDiscrepancy_ne_zeroChain
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.commonDiscrepancy sourceEscape ≠ zeroChain := by
  rw [ne_eq, collar.commonDiscrepancy_eq_zeroChain_iff sourceEscape]
  exact collar.sourceCommonColoring_ne_targetCommonColoring sourceEscape

/-- Hence some exact common-core edge carries a nonzero discrepancy. -/
theorem commonDiscrepancy_support_nonempty
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    (support (collar.commonDiscrepancy sourceEscape)).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  apply collar.commonDiscrepancy_ne_zeroChain sourceEscape
  funext edge
  exact eq_zero_of_support_eq_empty hempty edge

/-- Kirchhoff boundary is additive under the common discrepancy. -/
theorem vertexKirchhoffSum_commonDiscrepancy
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (vertex : collar.commonCoreVertex) :
    vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape) vertex =
      vertexKirchhoffSum collar.commonCore
          (collar.sourceCommonColoring sourceEscape) vertex +
        vertexKirchhoffSum collar.commonCore
          collar.targetCommonColoring vertex := by
  unfold vertexKirchhoffSum commonDiscrepancy
  exact Finset.sum_add_distrib

/-- At a target port with no literal source-port overlap, the discrepancy
boundary is exactly the sum of the cross-collar source color and the target
escape's own missing-color request. -/
theorem vertexKirchhoffSum_commonDiscrepancy_targetPort_eq
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (targetPort : Fin 4)
    (hnoOverlap : ∀ sourcePort : Fin 4,
      ¬ collar.PortOverlap sourcePort targetPort) :
    vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape)
        (collar.targetPortInCommonCore targetPort) =
      collar.targetBoundaryWordInSource sourceEscape targetPort +
        collar.targetData.degreeTwoBoundaryData.colorWord
          collar.targetEscape.coloring targetPort := by
  classical
  have hnone : ¬ ∃ sourcePort : Fin 4,
      collar.PortOverlap sourcePort targetPort := by
    rintro ⟨sourcePort, hoverlap⟩
    exact hnoOverlap sourcePort hoverlap
  have hcard :=
    collar.card_incidentEdgeFinset_targetPortInCommonCore targetPort
  rw [if_neg hnone] at hcard
  rcases Finset.card_eq_two.mp hcard with
    ⟨firstEdge, secondEdge, hedgesNe, hedgesEq⟩
  have hfirstCommon : firstEdge ∈ incidentEdgeFinset collar.commonCore
      (collar.targetPortInCommonCore targetPort) := by
    rw [hedgesEq]
    exact Finset.mem_insert_self firstEdge {secondEdge}
  have hsecondCommon : secondEdge ∈ incidentEdgeFinset collar.commonCore
      (collar.targetPortInCommonCore targetPort) := by
    rw [hedgesEq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self secondEdge)
  have hfirstSource :=
    collar.commonEdgeInSource_mem_incidentEdgeFinset_targetPort
      targetPort firstEdge hfirstCommon
  have hsecondSource :=
    collar.commonEdgeInSource_mem_incidentEdgeFinset_targetPort
      targetPort secondEdge hsecondCommon
  have hboundarySource :=
    collar.targetBoundaryInSource_mem_incidentEdgeFinset_targetPort
      targetPort
  have hfirstTarget :=
    collar.commonEdgeInTarget_mem_incidentEdgeFinset
      targetPort firstEdge hfirstCommon
  have hsecondTarget :=
    collar.commonEdgeInTarget_mem_incidentEdgeFinset
      targetPort secondEdge hsecondCommon
  have hfirstCommonVertex : collar.targetPortInCommonCore targetPort ∈
      firstEdge.1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hfirstCommon
  have hsecondCommonVertex : collar.targetPortInCommonCore targetPort ∈
      secondEdge.1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hsecondCommon
  have hcommonAdjacent : collar.commonCore.lineGraph.Adj
      firstEdge secondEdge :=
    collar.commonCore.lineGraph_adj_of_edgeSet_common_vertex
      hedgesNe hfirstCommonVertex hsecondCommonVertex
  have hsourceColorsNe :
      collar.sourceCommonColoring sourceEscape firstEdge ≠
        collar.sourceCommonColoring sourceEscape secondEdge :=
    (collar.sourceCommonColoring sourceEscape).valid hcommonAdjacent
  have htargetColorsNe :
      collar.targetCommonColoring firstEdge ≠
        collar.targetCommonColoring secondEdge :=
    collar.targetCommonColoring.valid hcommonAdjacent
  have hfirstSourceVertex : collar.targetPortInSourceDeletion targetPort ∈
      (collar.commonEdgeInSource firstEdge).1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hfirstSource
  have hsecondSourceVertex : collar.targetPortInSourceDeletion targetPort ∈
      (collar.commonEdgeInSource secondEdge).1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hsecondSource
  have hboundarySourceVertex :
      collar.targetPortInSourceDeletion targetPort ∈
        (collar.targetBoundaryInSource targetPort).1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hboundarySource
  have hboundaryFirst :
      collar.targetBoundaryWordInSource sourceEscape targetPort ≠
        collar.sourceCommonColoring sourceEscape firstEdge := by
    exact sourceEscape.coloring.valid
      ((DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex).lineGraph_adj_of_edgeSet_common_vertex
          (collar.commonEdgeInSource_ne_targetBoundaryInSource
            firstEdge targetPort).symm
          hboundarySourceVertex hfirstSourceVertex)
  have hboundarySecond :
      collar.targetBoundaryWordInSource sourceEscape targetPort ≠
        collar.sourceCommonColoring sourceEscape secondEdge := by
    exact sourceEscape.coloring.valid
      ((DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex).lineGraph_adj_of_edgeSet_common_vertex
          (collar.commonEdgeInSource_ne_targetBoundaryInSource
            secondEdge targetPort).symm
          hboundarySourceVertex hsecondSourceVertex)
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have htargetWell :=
    collar.targetData.degreeTwoBoundaryData_wellFormed hcubic
  have htargetWordFirst :
      collar.targetData.degreeTwoBoundaryData.colorWord
          collar.targetEscape.coloring targetPort ≠
        collar.targetCommonColoring firstEdge := by
    exact collar.targetData.degreeTwoBoundaryData.colorWord_ne_incidentColor
      htargetWell collar.targetEscape.coloring collar.targetEscape.isTait
        targetPort (collar.commonEdgeInTarget firstEdge) hfirstTarget
  have htargetWordSecond :
      collar.targetData.degreeTwoBoundaryData.colorWord
          collar.targetEscape.coloring targetPort ≠
        collar.targetCommonColoring secondEdge := by
    exact collar.targetData.degreeTwoBoundaryData.colorWord_ne_incidentColor
      htargetWell collar.targetEscape.coloring collar.targetEscape.isTait
        targetPort (collar.commonEdgeInTarget secondEdge) hsecondTarget
  have hsourceBoundaryEq :
      collar.targetBoundaryWordInSource sourceEscape targetPort =
        collar.sourceCommonColoring sourceEscape firstEdge +
          collar.sourceCommonColoring sourceEscape secondEdge := by
    exact color_eq_add_of_three_distinct_nonzero
      (sourceEscape.isTait _)
      (collar.sourceCommonColoring_isTait sourceEscape firstEdge)
      (collar.sourceCommonColoring_isTait sourceEscape secondEdge)
      hboundaryFirst hboundarySecond hsourceColorsNe
  have htargetWordEq :
      collar.targetData.degreeTwoBoundaryData.colorWord
          collar.targetEscape.coloring targetPort =
        collar.targetCommonColoring firstEdge +
          collar.targetCommonColoring secondEdge := by
    exact color_eq_add_of_three_distinct_nonzero
      (collar.targetData.degreeTwoBoundaryData.colorWord_ne_zero
        htargetWell collar.targetEscape.coloring targetPort)
      (collar.targetCommonColoring_isTait firstEdge)
      (collar.targetCommonColoring_isTait secondEdge)
      htargetWordFirst htargetWordSecond htargetColorsNe
  unfold vertexKirchhoffSum
  rw [hedgesEq]
  have hfirstNotMem : firstEdge ∉ ({secondEdge} :
      Finset collar.commonCore.edgeSet) := by
    intro hmem
    exact hedgesNe (Finset.mem_singleton.mp hmem)
  rw [Finset.sum_insert hfirstNotMem, Finset.sum_singleton]
  simp only [commonDiscrepancy_apply]
  calc
    (collar.sourceCommonColoring sourceEscape firstEdge +
          collar.targetCommonColoring firstEdge) +
        (collar.sourceCommonColoring sourceEscape secondEdge +
          collar.targetCommonColoring secondEdge) =
        (collar.sourceCommonColoring sourceEscape firstEdge +
          collar.sourceCommonColoring sourceEscape secondEdge) +
        (collar.targetCommonColoring firstEdge +
          collar.targetCommonColoring secondEdge) := by abel
    _ = collar.targetBoundaryWordInSource sourceEscape targetPort +
        collar.targetData.degreeTwoBoundaryData.colorWord
          collar.targetEscape.coloring targetPort := by
      rw [← hsourceBoundaryEq, ← htargetWordEq]

/-- The two discrepancy-boundary values at the singleton target endpoint
have nonzero sum.  Thus the forced discrepancy has a genuine terminal
boundary and cannot be only an internal cycle. -/
theorem singletonTargetPort_boundarySum_ne_zero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    (collar.targetData.firstVertex ∈
          collar.singletonCutProfile.component.supp ∧
        vertexKirchhoffSum collar.commonCore
            (collar.commonDiscrepancy sourceEscape)
            (collar.targetPortInCommonCore 0) +
          vertexKirchhoffSum collar.commonCore
            (collar.commonDiscrepancy sourceEscape)
            (collar.targetPortInCommonCore 1) ≠ 0) ∨
      (collar.targetData.secondVertex ∈
          collar.singletonCutProfile.component.supp ∧
        vertexKirchhoffSum collar.commonCore
            (collar.commonDiscrepancy sourceEscape)
            (collar.targetPortInCommonCore 2) +
          vertexKirchhoffSum collar.commonCore
            (collar.commonDiscrepancy sourceEscape)
            (collar.targetPortInCommonCore 3) ≠ 0) := by
  rcases collar.targetEndpoint_singletonSide_xor with
      ⟨hfirstSingleton, _hsecondOutside⟩ |
      ⟨_hfirstOutside, hsecondSingleton⟩
  · left
    refine ⟨hfirstSingleton, ?_⟩
    have hinsideZero : boundaryDeletedVertex collar.targetData 0 ∈
        collar.singletonCutProfile.component.supp := by
      simpa [boundaryDeletedVertex] using hfirstSingleton
    have hinsideOne : boundaryDeletedVertex collar.targetData 1 ∈
        collar.singletonCutProfile.component.supp := by
      simpa [boundaryDeletedVertex] using hfirstSingleton
    have hnoZero : ∀ sourcePort : Fin 4,
        ¬ collar.PortOverlap sourcePort 0 := fun sourcePort =>
      collar.not_portOverlap_of_targetDeletedVertex_mem_singleton
        sourcePort 0 hinsideZero
    have hnoOne : ∀ sourcePort : Fin 4,
        ¬ collar.PortOverlap sourcePort 1 := fun sourcePort =>
      collar.not_portOverlap_of_targetDeletedVertex_mem_singleton
        sourcePort 1 hinsideOne
    rw [collar.vertexKirchhoffSum_commonDiscrepancy_targetPort_eq
        sourceEscape 0 hnoZero,
      collar.vertexKirchhoffSum_commonDiscrepancy_targetPort_eq
        sourceEscape 1 hnoOne]
    intro hsum
    have hsourceDistinct :
        collar.targetBoundaryWordInSource sourceEscape 0 ≠
          collar.targetBoundaryWordInSource sourceEscape 1 :=
      sourceEscape.coloring.valid
        collar.targetBoundaryInSource_zero_adj_one
    apply hsourceDistinct
    apply (add_eq_zero_iff_eq _ _).mp
    let targetZero :=
      collar.targetData.degreeTwoBoundaryData.colorWord
        collar.targetEscape.coloring 0
    let targetOne :=
      collar.targetData.degreeTwoBoundaryData.colorWord
        collar.targetEscape.coloring 1
    have htarget : targetZero = targetOne :=
      collar.targetEscape.boundary_adjacent01_23.1
    calc
      collar.targetBoundaryWordInSource sourceEscape 0 +
          collar.targetBoundaryWordInSource sourceEscape 1 =
          (collar.targetBoundaryWordInSource sourceEscape 0 +
            targetZero) +
          (collar.targetBoundaryWordInSource sourceEscape 1 +
            targetZero) := by
        symm
        calc
          (collar.targetBoundaryWordInSource sourceEscape 0 +
                targetZero) +
              (collar.targetBoundaryWordInSource sourceEscape 1 +
                targetZero) =
              (collar.targetBoundaryWordInSource sourceEscape 0 +
                collar.targetBoundaryWordInSource sourceEscape 1) +
                (targetZero + targetZero) := by abel
          _ = collar.targetBoundaryWordInSource sourceEscape 0 +
              collar.targetBoundaryWordInSource sourceEscape 1 := by
            rw [color_add_self, add_zero]
      _ = (collar.targetBoundaryWordInSource sourceEscape 0 +
            targetZero) +
          (collar.targetBoundaryWordInSource sourceEscape 1 +
            targetOne) := by rw [htarget]
      _ = 0 := hsum
  · right
    refine ⟨hsecondSingleton, ?_⟩
    have hinsideTwo : boundaryDeletedVertex collar.targetData 2 ∈
        collar.singletonCutProfile.component.supp := by
      simpa [boundaryDeletedVertex] using hsecondSingleton
    have hinsideThree : boundaryDeletedVertex collar.targetData 3 ∈
        collar.singletonCutProfile.component.supp := by
      simpa [boundaryDeletedVertex] using hsecondSingleton
    have hnoTwo : ∀ sourcePort : Fin 4,
        ¬ collar.PortOverlap sourcePort 2 := fun sourcePort =>
      collar.not_portOverlap_of_targetDeletedVertex_mem_singleton
        sourcePort 2 hinsideTwo
    have hnoThree : ∀ sourcePort : Fin 4,
        ¬ collar.PortOverlap sourcePort 3 := fun sourcePort =>
      collar.not_portOverlap_of_targetDeletedVertex_mem_singleton
        sourcePort 3 hinsideThree
    rw [collar.vertexKirchhoffSum_commonDiscrepancy_targetPort_eq
        sourceEscape 2 hnoTwo,
      collar.vertexKirchhoffSum_commonDiscrepancy_targetPort_eq
        sourceEscape 3 hnoThree]
    intro hsum
    have hsourceDistinct :
        collar.targetBoundaryWordInSource sourceEscape 2 ≠
          collar.targetBoundaryWordInSource sourceEscape 3 :=
      sourceEscape.coloring.valid
        collar.targetBoundaryInSource_two_adj_three
    apply hsourceDistinct
    apply (add_eq_zero_iff_eq _ _).mp
    let targetTwo :=
      collar.targetData.degreeTwoBoundaryData.colorWord
        collar.targetEscape.coloring 2
    let targetThree :=
      collar.targetData.degreeTwoBoundaryData.colorWord
        collar.targetEscape.coloring 3
    have htarget : targetTwo = targetThree :=
      collar.targetEscape.boundary_adjacent01_23.2.1
    calc
      collar.targetBoundaryWordInSource sourceEscape 2 +
          collar.targetBoundaryWordInSource sourceEscape 3 =
          (collar.targetBoundaryWordInSource sourceEscape 2 +
            targetTwo) +
          (collar.targetBoundaryWordInSource sourceEscape 3 +
            targetTwo) := by
        symm
        calc
          (collar.targetBoundaryWordInSource sourceEscape 2 +
                targetTwo) +
              (collar.targetBoundaryWordInSource sourceEscape 3 +
                targetTwo) =
              (collar.targetBoundaryWordInSource sourceEscape 2 +
                collar.targetBoundaryWordInSource sourceEscape 3) +
                (targetTwo + targetTwo) := by abel
          _ = collar.targetBoundaryWordInSource sourceEscape 2 +
              collar.targetBoundaryWordInSource sourceEscape 3 := by
            rw [color_add_self, add_zero]
      _ = (collar.targetBoundaryWordInSource sourceEscape 2 +
            targetTwo) +
          (collar.targetBoundaryWordInSource sourceEscape 3 +
            targetThree) := by rw [htarget]
      _ = 0 := hsum

/-- Away from the source and target port images, the discrepancy obeys
Kirchhoff's law. -/
theorem vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_ports
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (vertex : collar.commonCoreVertex)
    (hsource : ∀ port : Fin 4,
      vertex ≠ collar.sourcePortInCommonCore port)
    (htarget : ∀ port : Fin 4,
      vertex ≠ collar.targetPortInCommonCore port) :
    vertexKirchhoffSum collar.commonCore
      (collar.commonDiscrepancy sourceEscape) vertex = 0 := by
  rw [collar.vertexKirchhoffSum_commonDiscrepancy sourceEscape vertex,
    collar.vertexKirchhoffSum_sourceCommonColoring_eq_zero_of_not_ports
      sourceEscape vertex hsource htarget,
    collar.vertexKirchhoffSum_targetCommonColoring_eq_zero_of_not_ports
      vertex hsource htarget]
  exact add_zero 0

/-- The four source port images in the exact common core. -/
def sourcePortVertexFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Finset collar.commonCoreVertex :=
  Finset.univ.image collar.sourcePortInCommonCore

/-- The four target port images in the exact common core. -/
def targetPortVertexFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Finset collar.commonCoreVertex :=
  Finset.univ.image collar.targetPortInCommonCore

/-- The variable-width terminal set of the common-core discrepancy. -/
def commonPortVertexFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Finset collar.commonCoreVertex :=
  collar.sourcePortVertexFinset ∪ collar.targetPortVertexFinset

@[simp]
theorem card_sourcePortVertexFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.sourcePortVertexFinset.card = 4 := by
  rw [sourcePortVertexFinset,
    Finset.card_image_of_injective _
      collar.sourcePortInCommonCore_injective]
  rfl

@[simp]
theorem card_targetPortVertexFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.targetPortVertexFinset.card = 4 := by
  rw [targetPortVertexFinset,
    Finset.card_image_of_injective _
      collar.targetPortInCommonCore_injective]
  rfl

/-- Before accounting for literal overlaps, the common discrepancy has at
most eight named terminal vertices. -/
theorem card_commonPortVertexFinset_le_eight
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.commonPortVertexFinset.card ≤ 8 := by
  calc
    collar.commonPortVertexFinset.card ≤
        collar.sourcePortVertexFinset.card +
          collar.targetPortVertexFinset.card := by
      exact Finset.card_union_le _ _
    _ = 8 := by
      rw [collar.card_sourcePortVertexFinset,
        collar.card_targetPortVertexFinset]

/-- The singleton geometry permits at most two collisions between the four
source and four target port images. -/
theorem card_sourcePortVertexFinset_inter_targetPortVertexFinset_le_two
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    (collar.sourcePortVertexFinset ∩
      collar.targetPortVertexFinset).card ≤ 2 := by
  rcases collar.portOverlap_targetPort_pair with
      ⟨_hfirstSingleton, hoverlapPorts⟩ |
      ⟨_hsecondSingleton, hoverlapPorts⟩
  · calc
      (collar.sourcePortVertexFinset ∩
          collar.targetPortVertexFinset).card ≤
          ({collar.targetPortInCommonCore 2,
            collar.targetPortInCommonCore 3} :
              Finset collar.commonCoreVertex).card := by
        apply Finset.card_le_card
        intro vertex hvertex
        rcases Finset.mem_inter.mp hvertex with
          ⟨hsourceImage, htargetImage⟩
        rcases Finset.mem_image.mp hsourceImage with
          ⟨sourcePort, _hsourcePort, hsourceEq⟩
        rcases Finset.mem_image.mp htargetImage with
          ⟨targetPort, _htargetPort, htargetEq⟩
        have hoverlap : collar.PortOverlap sourcePort targetPort :=
          (collar.sourcePortInCommonCore_eq_targetPortInCommonCore_iff
            sourcePort targetPort).1 (hsourceEq.trans htargetEq.symm)
        rcases hoverlapPorts hoverlap with rfl | rfl
        · rw [← htargetEq]
          exact Finset.mem_insert_self _ _
        · rw [← htargetEq]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      _ ≤ 2 := Finset.card_le_two
  · calc
      (collar.sourcePortVertexFinset ∩
          collar.targetPortVertexFinset).card ≤
          ({collar.targetPortInCommonCore 0,
            collar.targetPortInCommonCore 1} :
              Finset collar.commonCoreVertex).card := by
        apply Finset.card_le_card
        intro vertex hvertex
        rcases Finset.mem_inter.mp hvertex with
          ⟨hsourceImage, htargetImage⟩
        rcases Finset.mem_image.mp hsourceImage with
          ⟨sourcePort, _hsourcePort, hsourceEq⟩
        rcases Finset.mem_image.mp htargetImage with
          ⟨targetPort, _htargetPort, htargetEq⟩
        have hoverlap : collar.PortOverlap sourcePort targetPort :=
          (collar.sourcePortInCommonCore_eq_targetPortInCommonCore_iff
            sourcePort targetPort).1 (hsourceEq.trans htargetEq.symm)
        rcases hoverlapPorts hoverlap with rfl | rfl
        · rw [← htargetEq]
          exact Finset.mem_insert_self _ _
        · rw [← htargetEq]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      _ ≤ 2 := Finset.card_le_two

/-- The variable common-core terminal interface has width six, seven, or
eight, according to whether there are two, one, or no literal overlaps. -/
theorem commonPortVertexFinset_card_bounds
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    6 ≤ collar.commonPortVertexFinset.card ∧
      collar.commonPortVertexFinset.card ≤ 8 := by
  have hcard := Finset.card_union_add_card_inter
    collar.sourcePortVertexFinset collar.targetPortVertexFinset
  have hinter :=
    collar.card_sourcePortVertexFinset_inter_targetPortVertexFinset_le_two
  have hsource := collar.card_sourcePortVertexFinset
  have htarget := collar.card_targetPortVertexFinset
  constructor
  · rw [← commonPortVertexFinset] at hcard
    omega
  · exact collar.card_commonPortVertexFinset_le_eight

/-- Finset form of the bounded-terminal Kirchhoff property. -/
theorem vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (vertex : collar.commonCoreVertex)
    (hvertex : vertex ∉ collar.commonPortVertexFinset) :
    vertexKirchhoffSum collar.commonCore
      (collar.commonDiscrepancy sourceEscape) vertex = 0 := by
  apply collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_ports
    sourceEscape vertex
  · intro port heq
    apply hvertex
    rw [heq]
    rw [commonPortVertexFinset]
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨port, Finset.mem_univ port, rfl⟩
  · intro port heq
    apply hvertex
    rw [heq]
    rw [commonPortVertexFinset]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨port, Finset.mem_univ port, rfl⟩

/-- The exact terminal boundary values satisfy the global parity law. -/
theorem sum_vertexKirchhoffSum_commonDiscrepancy_on_commonPortVertexFinset_eq_zero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    ∑ vertex ∈ collar.commonPortVertexFinset,
        vertexKirchhoffSum collar.commonCore
          (collar.commonDiscrepancy sourceEscape) vertex = 0 := by
  apply GoertzelV24TwoDefectParity.sum_vertexKirchhoffSum_on_boundary_eq_zero
  intro vertex hvertex
  exact
    collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
      sourceEscape vertex hvertex

/-- The actual Kirchhoff-boundary support of the discrepancy. -/
def commonDiscrepancyBoundarySupport
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    Finset collar.commonCoreVertex :=
  Finset.univ.filter fun vertex =>
    vertexKirchhoffSum collar.commonCore
      (collar.commonDiscrepancy sourceEscape) vertex ≠ 0

/-- At least one singleton-side target port carries nonzero discrepancy
boundary. -/
theorem commonDiscrepancyBoundarySupport_nonempty
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    (collar.commonDiscrepancyBoundarySupport sourceEscape).Nonempty := by
  rcases collar.singletonTargetPort_boundarySum_ne_zero sourceEscape with
      ⟨_hfirstSingleton, hsum⟩ |
      ⟨_hsecondSingleton, hsum⟩
  · by_cases hzero : vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape)
        (collar.targetPortInCommonCore 0) = 0
    · have hone : vertexKirchhoffSum collar.commonCore
          (collar.commonDiscrepancy sourceEscape)
          (collar.targetPortInCommonCore 1) ≠ 0 := by
        intro hone
        exact hsum (by rw [hzero, hone, add_zero])
      refine ⟨collar.targetPortInCommonCore 1, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hone⟩
    · refine ⟨collar.targetPortInCommonCore 0, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩
  · by_cases htwo : vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape)
        (collar.targetPortInCommonCore 2) = 0
    · have hthree : vertexKirchhoffSum collar.commonCore
          (collar.commonDiscrepancy sourceEscape)
          (collar.targetPortInCommonCore 3) ≠ 0 := by
        intro hthree
        exact hsum (by rw [htwo, hthree, add_zero])
      refine ⟨collar.targetPortInCommonCore 3, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hthree⟩
    · refine ⟨collar.targetPortInCommonCore 2, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htwo⟩

/-- Every nonzero Kirchhoff boundary value lies at one of the named source
or target ports. -/
theorem commonDiscrepancyBoundarySupport_subset_commonPortVertexFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.commonDiscrepancyBoundarySupport sourceEscape ⊆
      collar.commonPortVertexFinset := by
  intro vertex hboundary
  simp only [commonDiscrepancyBoundarySupport, Finset.mem_filter,
    Finset.mem_univ, true_and] at hboundary
  by_contra hport
  exact hboundary
    (collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
      sourceEscape vertex hport)

/-- The discrepancy boundary has interface width at most eight. -/
theorem card_commonDiscrepancyBoundarySupport_le_eight
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    (collar.commonDiscrepancyBoundarySupport sourceEscape).card ≤ 8 :=
  le_trans
    (Finset.card_le_card
      (collar.commonDiscrepancyBoundarySupport_subset_commonPortVertexFinset
        sourceEscape))
    collar.card_commonPortVertexFinset_le_eight

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
