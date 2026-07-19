import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortSingletonOverlap

/-! Exact common-core agreement is incompatible with the singleton-side
target collar. -/

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

private theorem color_eq_of_two_distinct_nonzero_exclusions
    {first second a b : Color}
    (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hfirstA : first ≠ a) (hfirstB : first ≠ b)
    (hsecondA : second ≠ a) (hsecondB : second ≠ b) :
    first = second := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero first hfirst with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero second hsecond with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with
      rfl | rfl | rfl <;>
    simp at hab hfirstA hfirstB hsecondA hsecondB ⊢

/-- A target port, regarded as a vertex of the source adjacent-pair
deletion graph. -/
def targetPortInSourceDeletion
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) :
    retainedVertexSet collar.sourceData.firstVertex
      collar.sourceData.secondVertex :=
  ⟨collar.targetData.portVertex targetPort,
    collar.targetPort_mem_sourceRetainedVertexSet targetPort⟩

/-- Incidence of a common edge at a target port is preserved in the source
deletion embedding. -/
theorem commonEdgeInSource_mem_incidentEdgeFinset_targetPort
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) (edge : collar.commonCore.edgeSet)
    (hmem : edge ∈ incidentEdgeFinset collar.commonCore
      (collar.targetPortInCommonCore targetPort)) :
    collar.commonEdgeInSource edge ∈ incidentEdgeFinset
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex)
      (collar.targetPortInSourceDeletion targetPort) := by
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem ⊢
  simp only [commonEdgeInSource, SimpleGraph.Embedding.mapEdgeSet]
  apply Sym2.mem_map.mpr
  exact ⟨collar.targetPortInCommonCore targetPort, hmem, Subtype.ext rfl⟩

/-- The target boundary edge is incident to its target port after embedding
the whole target collar in the source deletion. -/
theorem targetBoundaryInSource_mem_incidentEdgeFinset_targetPort
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) :
    collar.targetBoundaryInSource targetPort ∈ incidentEdgeFinset
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex)
      (collar.targetPortInSourceDeletion targetPort) := by
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact (mem_ambientEdgeToRetainedEdge_iff collar.sourceData
    (boundaryEdge collar.targetData targetPort)
      (collar.targetBoundaryRetainedBySource targetPort)
      (collar.targetData.portVertex targetPort)
      (collar.targetPort_mem_sourceRetainedVertexSet targetPort)).2
        (by
          rw [boundaryEdge_val]
          exact collar.targetData.portVertex_mem_boundaryEdgeValue
            targetPort)

/-- At a target port not shared with a source port, equality of the two
common-core colorings forces the retained target boundary color in the
source escape to equal the target escape's missing-color request. -/
theorem targetBoundaryWordInSource_eq_targetColorWord_of_commonColoring_eq_of_noPortOverlap
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (hcommon : collar.sourceCommonColoring sourceEscape =
      collar.targetCommonColoring)
    (targetPort : Fin 4)
    (hnoOverlap : ∀ sourcePort : Fin 4,
      ¬ collar.PortOverlap sourcePort targetPort) :
    collar.targetBoundaryWordInSource sourceEscape targetPort =
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
  let boundaryColor :=
    sourceEscape.coloring (collar.targetBoundaryInSource targetPort)
  let targetWord :=
    collar.targetData.degreeTwoBoundaryData.colorWord
      collar.targetEscape.coloring targetPort
  let firstColor :=
    sourceEscape.coloring (collar.commonEdgeInSource firstEdge)
  let secondColor :=
    sourceEscape.coloring (collar.commonEdgeInSource secondEdge)
  have hboundaryNonzero : boundaryColor ≠ 0 := sourceEscape.isTait _
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have htargetWell :=
    collar.targetData.degreeTwoBoundaryData_wellFormed hcubic
  have htargetWordNonzero : targetWord ≠ 0 :=
    collar.targetData.degreeTwoBoundaryData.colorWord_ne_zero
      htargetWell collar.targetEscape.coloring targetPort
  have hfirstNonzero : firstColor ≠ 0 := sourceEscape.isTait _
  have hsecondNonzero : secondColor ≠ 0 := sourceEscape.isTait _
  have hfirstCommonVertex : collar.targetPortInCommonCore targetPort ∈
      firstEdge.1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hfirstCommon
  have hsecondCommonVertex : collar.targetPortInCommonCore targetPort ∈
      secondEdge.1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hsecondCommon
  have hcolorsNe : firstColor ≠ secondColor := by
    have hvalid := (collar.sourceCommonColoring sourceEscape).valid
      (collar.commonCore.lineGraph_adj_of_edgeSet_common_vertex
        hedgesNe hfirstCommonVertex hsecondCommonVertex)
    exact hvalid
  have hfirstVertex : collar.targetPortInSourceDeletion targetPort ∈
      (collar.commonEdgeInSource firstEdge).1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hfirstSource
  have hsecondVertex : collar.targetPortInSourceDeletion targetPort ∈
      (collar.commonEdgeInSource secondEdge).1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hsecondSource
  have hboundaryVertex : collar.targetPortInSourceDeletion targetPort ∈
      (collar.targetBoundaryInSource targetPort).1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hboundarySource
  have hboundaryFirst : boundaryColor ≠ firstColor :=
    sourceEscape.coloring.valid
      ((DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex).lineGraph_adj_of_edgeSet_common_vertex
          (collar.commonEdgeInSource_ne_targetBoundaryInSource
            firstEdge targetPort).symm
          hboundaryVertex hfirstVertex)
  have hboundarySecond : boundaryColor ≠ secondColor :=
    sourceEscape.coloring.valid
      ((DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex).lineGraph_adj_of_edgeSet_common_vertex
          (collar.commonEdgeInSource_ne_targetBoundaryInSource
            secondEdge targetPort).symm
          hboundaryVertex hsecondVertex)
  have hfirstAgreement :=
    collar.commonEdge_color_eq_of_commonColoring_eq
      sourceEscape hcommon firstEdge
  have hsecondAgreement :=
    collar.commonEdge_color_eq_of_commonColoring_eq
      sourceEscape hcommon secondEdge
  have htargetWordFirst : targetWord ≠ firstColor := by
    intro heq
    apply collar.targetData.degreeTwoBoundaryData.colorWord_ne_incidentColor
      htargetWell collar.targetEscape.coloring collar.targetEscape.isTait
        targetPort (collar.commonEdgeInTarget firstEdge) hfirstTarget
    exact heq.trans hfirstAgreement
  have htargetWordSecond : targetWord ≠ secondColor := by
    intro heq
    apply collar.targetData.degreeTwoBoundaryData.colorWord_ne_incidentColor
      htargetWell collar.targetEscape.coloring collar.targetEscape.isTait
        targetPort (collar.commonEdgeInTarget secondEdge) hsecondTarget
    exact heq.trans hsecondAgreement
  exact color_eq_of_two_distinct_nonzero_exclusions
    hboundaryNonzero htargetWordNonzero hfirstNonzero hsecondNonzero
      hcolorsNe hboundaryFirst hboundarySecond
      htargetWordFirst htargetWordSecond

/-- The source and target escape colorings cannot agree exactly on their
common core.  At the two ports based at the singleton target endpoint there
is no literal source-port overlap.  Exact common-core agreement would make
the two retained source colors equal to the target's adjacent equal pair,
contradicting Tait distinctness at that endpoint. -/
theorem sourceCommonColoring_ne_targetCommonColoring
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    collar.sourceCommonColoring sourceEscape ≠
      collar.targetCommonColoring := by
  intro hcommon
  rcases collar.portOverlap_targetPort_pair with
      ⟨hfirstSingleton, _hoverlaps⟩ |
      ⟨hsecondSingleton, _hoverlaps⟩
  · have hinsideZero : boundaryDeletedVertex collar.targetData 0 ∈
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
    have hzero :=
      collar.targetBoundaryWordInSource_eq_targetColorWord_of_commonColoring_eq_of_noPortOverlap
        sourceEscape hcommon 0 hnoZero
    have hone :=
      collar.targetBoundaryWordInSource_eq_targetColorWord_of_commonColoring_eq_of_noPortOverlap
        sourceEscape hcommon 1 hnoOne
    have htargetEqual := collar.targetEscape.boundary_adjacent01_23.1
    have hsourceDistinct := sourceEscape.coloring.valid
      collar.targetBoundaryInSource_zero_adj_one
    exact hsourceDistinct (hzero.trans (htargetEqual.trans hone.symm))
  · have hinsideTwo : boundaryDeletedVertex collar.targetData 2 ∈
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
    have htwo :=
      collar.targetBoundaryWordInSource_eq_targetColorWord_of_commonColoring_eq_of_noPortOverlap
        sourceEscape hcommon 2 hnoTwo
    have hthree :=
      collar.targetBoundaryWordInSource_eq_targetColorWord_of_commonColoring_eq_of_noPortOverlap
        sourceEscape hcommon 3 hnoThree
    have htargetEqual := collar.targetEscape.boundary_adjacent01_23.2.1
    have hsourceDistinct := sourceEscape.coloring.valid
      collar.targetBoundaryInSource_two_adj_three
    exact hsourceDistinct (htwo.trans (htargetEqual.trans hthree.symm))

/-- Consequently, a source and target escape cannot agree pointwise on
every ambient edge retained by both adjacent-pair deletions. -/
theorem not_commonAgreement_of_singletonProfile
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    ¬ ∀ (edge : G.edgeSet)
        (hsource : IsRetainedAmbientEdge collar.sourceData edge)
        (htarget : IsRetainedAmbientEdge collar.targetData edge),
      sourceEscape.coloring
          (ambientEdgeToRetainedEdge collar.sourceData edge hsource) =
        collar.targetEscape.coloring
          (ambientEdgeToRetainedEdge collar.targetData edge htarget) := by
  intro hcommon
  exact collar.sourceCommonColoring_ne_targetCommonColoring sourceEscape
    (collar.sourceCommonColoring_eq_targetCommonColoring_of_commonAgreement
      sourceEscape hcommon)

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
