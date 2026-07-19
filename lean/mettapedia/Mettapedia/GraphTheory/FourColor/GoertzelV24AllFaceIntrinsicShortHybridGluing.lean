import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortColorMatrix

/-! Hybrid gluing of the two intrinsic-short adjacent-pair escape colorings. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
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

/-- Every edge omitted by the source adjacent-pair deletion survives the
target adjacent-pair deletion. -/
theorem retainedByTarget_of_not_retainedBySource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : G.edgeSet) (hnot : ¬ IsRetainedAmbientEdge collar.sourceData edge) :
    IsRetainedAmbientEdge collar.targetData edge := by
  rcases (not_isRetainedAmbientEdge_iff collar.sourceData edge).1 hnot with
    hcentral | ⟨port, hboundary⟩
  · have hedge : edge = centralEdge collar.sourceData := by
      apply Subtype.ext
      exact hcentral
    rw [hedge]
    exact collar.sourceCentralRetainedByTarget
  · have hedge : edge = boundaryEdge collar.sourceData port := by
      apply Subtype.ext
      exact hboundary
    rw [hedge]
    exact collar.sourceBoundaryRetainedByTarget port

/-- Use the source escape on every source-retained edge and the target escape
on the five omitted source-collar edges. -/
def hybridColor
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : G.edgeSet) : Color := by
  classical
  exact if hsource : IsRetainedAmbientEdge collar.sourceData edge then
      sourceEscape.coloring
        (ambientEdgeToRetainedEdge collar.sourceData edge hsource)
    else
      collar.targetEscape.coloring
        (ambientEdgeToRetainedEdge collar.targetData edge
          (collar.retainedByTarget_of_not_retainedBySource edge hsource))

@[simp]
theorem hybridColor_of_retainedBySource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : G.edgeSet) (hsource : IsRetainedAmbientEdge collar.sourceData edge) :
    collar.hybridColor sourceEscape edge =
      sourceEscape.coloring
        (ambientEdgeToRetainedEdge collar.sourceData edge hsource) := by
  simp [hybridColor, hsource]

@[simp]
theorem hybridColor_of_not_retainedBySource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : G.edgeSet)
    (hsource : ¬ IsRetainedAmbientEdge collar.sourceData edge) :
    collar.hybridColor sourceEscape edge =
      collar.targetEscape.coloring
        (ambientEdgeToRetainedEdge collar.targetData edge
          (collar.retainedByTarget_of_not_retainedBySource edge hsource)) := by
  simp [hybridColor, hsource]

/-- The only mixed-color validity check is at a literal overlap of a source
and target port. -/
theorem hybridColor_ne_of_retainedBySource_of_not_retainedBySource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (hcommon : ∀ (edge : G.edgeSet)
        (hsource : IsRetainedAmbientEdge collar.sourceData edge)
        (htarget : IsRetainedAmbientEdge collar.targetData edge),
      sourceEscape.coloring
          (ambientEdgeToRetainedEdge collar.sourceData edge hsource) =
        collar.targetEscape.coloring
          (ambientEdgeToRetainedEdge collar.targetData edge htarget))
    (hoverlap : ∀ sourcePort targetPort : Fin 4,
      collar.PortOverlap sourcePort targetPort →
        collar.targetEscape.coloring
            (collar.sourceBoundaryInTarget sourcePort) ≠
          sourceEscape.coloring
            (collar.targetBoundaryInSource targetPort))
    (sourceEdge targetEdge' : G.edgeSet)
    (hsourceRetained :
      IsRetainedAmbientEdge collar.sourceData sourceEdge)
    (htargetNotRetained :
      ¬ IsRetainedAmbientEdge collar.sourceData targetEdge')
    (hadj : G.lineGraph.Adj sourceEdge targetEdge') :
    collar.hybridColor sourceEscape sourceEdge ≠
      collar.hybridColor sourceEscape targetEdge' := by
  rw [collar.hybridColor_of_retainedBySource sourceEscape sourceEdge
      hsourceRetained,
    collar.hybridColor_of_not_retainedBySource sourceEscape targetEdge'
      htargetNotRetained]
  rcases (not_isRetainedAmbientEdge_iff collar.sourceData targetEdge').1
      htargetNotRetained with hcentral | ⟨sourcePort, hboundary⟩
  · have htargetEdge : targetEdge' = centralEdge collar.sourceData := by
      apply Subtype.ext
      exact hcentral
    subst targetEdge'
    rcases (SimpleGraph.lineGraph_adj_iff_exists.mp hadj) with
      ⟨_hne, vertex, hsourceVertex, hcentralVertex⟩
    have hsourceSurvives := endpoints_mem_retainedVertexSet
      collar.sourceData sourceEdge hsourceRetained vertex hsourceVertex
    rw [centralEdge_val, centralEdgeValue] at hcentralVertex
    rcases (Sym2.mem_iff.mp hcentralVertex) with hfirst | hsecond
    · exact (hsourceSurvives.1 hfirst).elim
    · exact (hsourceSurvives.2 hsecond).elim
  · have htargetEdge : targetEdge' =
        boundaryEdge collar.sourceData sourcePort := by
      apply Subtype.ext
      exact hboundary
    subst targetEdge'
    rcases (SimpleGraph.lineGraph_adj_iff_exists.mp hadj) with
      ⟨_hne, vertex, hsourceVertex, hboundaryVertex⟩
    have hsourceSurvives := endpoints_mem_retainedVertexSet
      collar.sourceData sourceEdge hsourceRetained vertex hsourceVertex
    rw [boundaryEdge_val, boundaryEdgeValue_eq] at hboundaryVertex
    rcases (Sym2.mem_iff.mp hboundaryVertex) with
      hdeleted | hsourcePort
    · fin_cases sourcePort <;>
        simp [boundaryDeletedVertex] at hdeleted
      · exact (hsourceSurvives.1 hdeleted).elim
      · exact (hsourceSurvives.1 hdeleted).elim
      · exact (hsourceSurvives.2 hdeleted).elim
      · exact (hsourceSurvives.2 hdeleted).elim
    · have hvertex : vertex = collar.sourceData.portVertex sourcePort :=
        hsourcePort
      subst vertex
      by_cases htargetRetained :
          IsRetainedAmbientEdge collar.targetData sourceEdge
      · have hadjTarget :
          (DeletedAdjacentPairGraph G collar.targetData.firstVertex
            collar.targetData.secondVertex).lineGraph.Adj
              (ambientEdgeToRetainedEdge collar.targetData sourceEdge
                htargetRetained)
              (collar.sourceBoundaryInTarget sourcePort) := by
          exact ambientEdgeToRetainedEdge_adj collar.targetData
            sourceEdge (boundaryEdge collar.sourceData sourcePort)
              htargetRetained
                (collar.sourceBoundaryRetainedByTarget sourcePort) hadj
        have hneTarget := collar.targetEscape.coloring.valid hadjTarget
        simpa [sourceBoundaryInTarget] using
          (hcommon sourceEdge hsourceRetained htargetRetained).trans_ne
            hneTarget
      · rcases (not_isRetainedAmbientEdge_iff collar.targetData sourceEdge).1
          htargetRetained with htargetCentral | ⟨targetPort, htargetBoundary⟩
        · have hsourceValue : sourceEdge.1 =
              centralEdgeValue collar.targetData := htargetCentral
          have hsourcePortMem : collar.sourceData.portVertex sourcePort ∈
              (sourceEdge.1 : Sym2 V) := hsourceVertex
          rw [hsourceValue, centralEdgeValue] at hsourcePortMem
          rcases (Sym2.mem_iff.mp hsourcePortMem) with
            hfirst | hsecond
          · exact False.elim
              ((collar.sourcePort_mem_targetRetainedVertexSet
                sourcePort).1 hfirst)
          · exact False.elim
              ((collar.sourcePort_mem_targetRetainedVertexSet
                sourcePort).2 hsecond)
        · have hsourceEdge : sourceEdge =
              boundaryEdge collar.targetData targetPort := by
            apply Subtype.ext
            exact htargetBoundary
          subst sourceEdge
          have htargetPortValue :
              collar.sourceData.portVertex sourcePort =
                collar.targetData.portVertex targetPort := by
            rw [boundaryEdge_val, boundaryEdgeValue_eq] at hsourceVertex
            rcases (Sym2.mem_iff.mp hsourceVertex) with
              hdeleted | hport
            · fin_cases targetPort <;>
                simp [boundaryDeletedVertex] at hdeleted
              · exact False.elim
                  ((collar.sourcePort_mem_targetRetainedVertexSet
                    sourcePort).1 hdeleted)
              · exact False.elim
                  ((collar.sourcePort_mem_targetRetainedVertexSet
                    sourcePort).1 hdeleted)
              · exact False.elim
                  ((collar.sourcePort_mem_targetRetainedVertexSet
                    sourcePort).2 hdeleted)
              · exact False.elim
                  ((collar.sourcePort_mem_targetRetainedVertexSet
                    sourcePort).2 hdeleted)
            · exact hport
          have hoverlap' : collar.PortOverlap sourcePort targetPort :=
            htargetPortValue
          simpa [sourceBoundaryInTarget, targetBoundaryInSource] using
            (hoverlap sourcePort targetPort hoverlap').symm

/-- Common-edge agreement and the at-most-four overlap inequalities splice
the two escape states into a full ambient Tait coloring. -/
theorem exists_ambientTaitColoring_of_commonAgreement_of_overlapCompatibility
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (hcommon : ∀ (edge : G.edgeSet)
        (hsource : IsRetainedAmbientEdge collar.sourceData edge)
        (htarget : IsRetainedAmbientEdge collar.targetData edge),
      sourceEscape.coloring
          (ambientEdgeToRetainedEdge collar.sourceData edge hsource) =
        collar.targetEscape.coloring
          (ambientEdgeToRetainedEdge collar.targetData edge htarget))
    (hoverlap : ∀ sourcePort targetPort : Fin 4,
      collar.PortOverlap sourcePort targetPort →
        collar.targetEscape.coloring
            (collar.sourceBoundaryInTarget sourcePort) ≠
          sourceEscape.coloring
            (collar.targetBoundaryInSource targetPort)) :
    ∃ coloring : G.EdgeColoring Color,
      IsTaitEdgeColoring G coloring := by
  let coloring : G.EdgeColoring Color :=
    SimpleGraph.Coloring.mk (collar.hybridColor sourceEscape) (by
      intro first second hadj
      by_cases hfirst : IsRetainedAmbientEdge collar.sourceData first
      · by_cases hsecond : IsRetainedAmbientEdge collar.sourceData second
        · rw [collar.hybridColor_of_retainedBySource sourceEscape first hfirst,
            collar.hybridColor_of_retainedBySource sourceEscape second hsecond]
          exact sourceEscape.coloring.valid
            (ambientEdgeToRetainedEdge_adj collar.sourceData first second
              hfirst hsecond hadj)
        · exact collar.hybridColor_ne_of_retainedBySource_of_not_retainedBySource
            sourceEscape hcommon hoverlap first second hfirst hsecond hadj
      · by_cases hsecond : IsRetainedAmbientEdge collar.sourceData second
        · exact (collar.hybridColor_ne_of_retainedBySource_of_not_retainedBySource
            sourceEscape hcommon hoverlap second first hsecond hfirst hadj.symm).symm
        · rw [collar.hybridColor_of_not_retainedBySource sourceEscape first hfirst,
            collar.hybridColor_of_not_retainedBySource sourceEscape second hsecond]
          exact collar.targetEscape.coloring.valid
            (ambientEdgeToRetainedEdge_adj collar.targetData first second
              (collar.retainedByTarget_of_not_retainedBySource first hfirst)
              (collar.retainedByTarget_of_not_retainedBySource second hsecond)
              hadj))
  refine ⟨coloring, ?_⟩
  intro edge
  by_cases hsource : IsRetainedAmbientEdge collar.sourceData edge
  · change collar.hybridColor sourceEscape edge ≠ 0
    rw [collar.hybridColor_of_retainedBySource sourceEscape edge hsource]
    exact sourceEscape.isTait _
  · change collar.hybridColor sourceEscape edge ≠ 0
    rw [collar.hybridColor_of_not_retainedBySource sourceEscape edge hsource]
    exact collar.targetEscape.isTait _

/-- In a pinned minimal counterexample, common-edge agreement and overlap
compatibility cannot hold simultaneously. -/
theorem not_commonAgreement_and_overlapCompatibility
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    ¬ ((∀ (edge : G.edgeSet)
          (hsource : IsRetainedAmbientEdge collar.sourceData edge)
          (htarget : IsRetainedAmbientEdge collar.targetData edge),
        sourceEscape.coloring
            (ambientEdgeToRetainedEdge collar.sourceData edge hsource) =
          collar.targetEscape.coloring
            (ambientEdgeToRetainedEdge collar.targetData edge htarget)) ∧
      (∀ sourcePort targetPort : Fin 4,
        collar.PortOverlap sourcePort targetPort →
          collar.targetEscape.coloring
              (collar.sourceBoundaryInTarget sourcePort) ≠
            sourceEscape.coloring
              (collar.targetBoundaryInSource targetPort))) := by
  rintro ⟨hcommon, hoverlap⟩
  exact (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
    graphData minimal)
      (collar.exists_ambientTaitColoring_of_commonAgreement_of_overlapCompatibility
        sourceEscape hcommon hoverlap)

/-- If the two escape colorings agree on their exact common core, minimality
forces a literal port overlap at which the two collar colors coincide. -/
theorem exists_conflictingPortOverlap_of_commonAgreement
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (hcommon : ∀ (edge : G.edgeSet)
        (hsource : IsRetainedAmbientEdge collar.sourceData edge)
        (htarget : IsRetainedAmbientEdge collar.targetData edge),
      sourceEscape.coloring
          (ambientEdgeToRetainedEdge collar.sourceData edge hsource) =
        collar.targetEscape.coloring
          (ambientEdgeToRetainedEdge collar.targetData edge htarget)) :
    ∃ sourcePort targetPort : Fin 4,
      collar.PortOverlap sourcePort targetPort ∧
        collar.targetEscape.coloring
            (collar.sourceBoundaryInTarget sourcePort) =
          sourceEscape.coloring
            (collar.targetBoundaryInSource targetPort) := by
  by_contra hnone
  exact (collar.not_commonAgreement_and_overlapCompatibility sourceEscape)
    ⟨hcommon, by
      intro sourcePort targetPort hoverlap heq
      exact hnone ⟨sourcePort, targetPort, hoverlap, heq⟩⟩

/-- With no literal port overlap, the two escape colorings cannot agree on
their exact common core. -/
theorem not_commonAgreement_of_noPortOverlap
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (hnoOverlap : ∀ sourcePort targetPort : Fin 4,
      ¬ collar.PortOverlap sourcePort targetPort) :
    ¬ (∀ (edge : G.edgeSet)
        (hsource : IsRetainedAmbientEdge collar.sourceData edge)
        (htarget : IsRetainedAmbientEdge collar.targetData edge),
      sourceEscape.coloring
          (ambientEdgeToRetainedEdge collar.sourceData edge hsource) =
        collar.targetEscape.coloring
          (ambientEdgeToRetainedEdge collar.targetData edge htarget)) := by
  intro hcommon
  rcases collar.exists_conflictingPortOverlap_of_commonAgreement
      sourceEscape hcommon with ⟨sourcePort, targetPort, hoverlap, _⟩
  exact hnoOverlap sourcePort targetPort hoverlap

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
