import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitConstantFaceCellBoundaryArc
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionSignature
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphTaitBridge

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
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

namespace CrossCentralExactFaceCertifiedRebaseInvolutionCell

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- At either orientation of the source cross, its terminal endpoint cannot
also lie on the target cross.  Otherwise the two source closure cycles would
each require a distinct third incident edge there, contradicting cubicity and
their exact common-support profile. -/
private theorem sourceDart_snd_not_mem_targetCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (root : G.Dart)
    (hroot : root.edge = cell.sourceAmbientCross.1)
    (hretained : root.snd ∉ centralEdgeValue
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) :
    root.snd ∉ cell.targetAmbientCross.1 := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  intro htargetIncident
  have hsourceTarget :
      cell.sourceAmbientCross ≠ cell.targetAmbientCross := by
    intro heq
    apply cell.cross_ne
    exact data.retainedEdgeToAmbientEdge_injective heq |>.symm
  have hsourceBoth :
      cell.sourceAmbientCross.1 ∈ cell.sourcePrefixClosure.edges ∧
        cell.sourceAmbientCross.1 ∈ cell.sourceSuffixClosure.edges :=
    (cell.sourceClosures_both_iff_eq_sourceCross
      cell.sourceAmbientCross cell.crosses_mem_face.1).2 rfl
  have hrootPrefix : root.edge ∈ cell.sourcePrefixClosure.edges := by
    rw [hroot]
    exact hsourceBoth.1
  have hrootSuffix : root.edge ∈ cell.sourceSuffixClosure.edges := by
    rw [hroot]
    exact hsourceBoth.2
  have hcycles := cell.closure_cycles
  dsimp only at hcycles
  rcases hcycles.1.exists_nextEdge_ne_at_dart root hrootPrefix with
    ⟨prefixEdge, hprefixIncident, hprefixMem, hprefixNeRoot⟩
  rcases hcycles.2.1.exists_nextEdge_ne_at_dart root hrootSuffix with
    ⟨suffixEdge, hsuffixIncident, hsuffixMem, hsuffixNeRoot⟩
  have htargetNeither :
      cell.targetAmbientCross.1 ∉ cell.sourcePrefixClosure.edges ∧
        cell.targetAmbientCross.1 ∉ cell.sourceSuffixClosure.edges :=
    (cell.sourceClosures_neither_iff_eq_targetCross
      cell.targetAmbientCross cell.crosses_mem_face.2).2 rfl
  have hprefixNeSource : prefixEdge ≠ cell.sourceAmbientCross := by
    intro heq
    apply hprefixNeRoot
    exact (congrArg Subtype.val heq).trans hroot.symm
  have hsuffixNeSource : suffixEdge ≠ cell.sourceAmbientCross := by
    intro heq
    apply hsuffixNeRoot
    exact (congrArg Subtype.val heq).trans hroot.symm
  have hprefixNeTarget : prefixEdge ≠ cell.targetAmbientCross := by
    intro heq
    apply htargetNeither.1
    exact congrArg Subtype.val heq ▸ hprefixMem
  have hsuffixNeTarget : suffixEdge ≠ cell.targetAmbientCross := by
    intro heq
    apply htargetNeither.2
    exact congrArg Subtype.val heq ▸ hsuffixMem
  have hsourceIncident :
      cell.sourceAmbientCross ∈ incidentEdgeFinset G root.snd := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [← hroot]
    simp [SimpleGraph.Dart.edge]
  have htargetIncident' :
      cell.targetAmbientCross ∈ incidentEdgeFinset G root.snd := by
    simpa [incidentEdgeFinset] using htargetIncident
  have hprefixIncident' :
      prefixEdge ∈ incidentEdgeFinset G root.snd := by
    simpa [incidentEdgeFinset] using hprefixIncident
  have hsuffixIncident' :
      suffixEdge ∈ incidentEdgeFinset G root.snd := by
    simpa [incidentEdgeFinset] using hsuffixIncident
  have hprefixSuffix : prefixEdge = suffixEdge := by
    by_contra hne
    have hsubset :
        ({cell.sourceAmbientCross, cell.targetAmbientCross,
            prefixEdge, suffixEdge} : Finset G.edgeSet) ⊆
          incidentEdgeFinset G root.snd := by
      intro edge hedge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
      rcases hedge with rfl | rfl | rfl | rfl
      · exact hsourceIncident
      · exact htargetIncident'
      · exact hprefixIncident'
      · exact hsuffixIncident'
    have hcardFour :
        ({cell.sourceAmbientCross, cell.targetAmbientCross,
            prefixEdge, suffixEdge} : Finset G.edgeSet).card = 4 := by
      simp [hsourceTarget, hprefixNeSource, hsuffixNeSource,
        hprefixNeTarget, hsuffixNeTarget, hne, ne_comm]
    have hcardLe := Finset.card_le_card hsubset
    rw [hcardFour,
      incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
        graphData minimal.spherical.cubic root.snd] at hcardLe
    omega
  have hcommon :
      prefixEdge.1 = cell.sourceAmbientCross.1 ∨
        prefixEdge.1 = centralEdgeValue data := by
    apply (data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
      cell.source.2.prefixTrail cell.source.2.suffixTrail cell.source.1
        cell.source.2.retainedIntersectionExact prefixEdge.1).1
    exact ⟨hprefixMem, by simpa [hprefixSuffix] using hsuffixMem⟩
  rcases hcommon with hsource | hcentral
  · exact hprefixNeSource (Subtype.ext hsource)
  · apply hretained
    rw [← hcentral]
    exact hprefixIncident

/-- The target cross does not meet the terminal endpoint of the rooted source
cross. -/
theorem targetCross_not_incident_root_snd
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (split : BoundaryArcSplit cell) :
    split.root.snd ∉ cell.targetAmbientCross.1 := by
  apply sourceDart_snd_not_mem_targetCross cell split.root
    split.root_edge_value
  exact cell.faceDart_snd_not_mem_centralEdgeValue split.root
    split.root_face

/-- The target cross does not meet the initial endpoint of the rooted source
cross either. -/
theorem targetCross_not_incident_root_fst
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (split : BoundaryArcSplit cell) :
    split.root.fst ∉ cell.targetAmbientCross.1 := by
  let RS := graphData.toRotationSystem
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have hsourceRetained : IsRetainedAmbientEdge data
      cell.sourceAmbientCross :=
    cell.faceEdge_isRetained cell.sourceAmbientCross cell.crosses_mem_face.1
  have hrootFstSource : split.root.fst ∈ cell.sourceAmbientCross.1 := by
    rw [← split.root_edge_value]
    simp [SimpleGraph.Dart.edge]
  have hrootFstRetained :
      split.root.fst ∈ retainedVertexSet data.firstVertex data.secondVertex :=
    endpoints_mem_retainedVertexSet data cell.sourceAmbientCross
      hsourceRetained split.root.fst hrootFstSource
  have hrootFstNotCentral :
      split.root.fst ∉ centralEdgeValue data := by
    intro hcentral
    have hdeleted : split.root.fst = data.firstVertex ∨
        split.root.fst = data.secondVertex := by
      simpa [centralEdgeValue] using hcentral
    rcases hdeleted with hfirst | hsecond
    · exact hrootFstRetained.1 hfirst
    · exact hrootFstRetained.2 hsecond
  apply sourceDart_snd_not_mem_targetCross cell (RS.alpha split.root)
  · calc
      (RS.alpha split.root).edge = split.root.edge := by
        change (RS.edgeOf (RS.alpha split.root)).1 =
          (RS.edgeOf split.root).1
        rw [RS.edge_alpha]
      _ = cell.sourceAmbientCross.1 := split.root_edge_value
  · simpa [RS] using hrootFstNotCentral

/-- The first source-to-target facial arc contains an edge. -/
theorem before_not_nil
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (split : BoundaryArcSplit cell) :
    ¬split.before.Nil := by
  intro hnil
  apply targetCross_not_incident_root_snd cell split
  rw [split.target_edge, hnil.eq]
  simp

/-- The second source-to-target facial arc also contains an edge. -/
theorem after_not_nil
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (split : BoundaryArcSplit cell) :
    ¬split.after.Nil := by
  intro hnil
  apply targetCross_not_incident_root_fst cell split
  rw [split.target_edge, hnil.eq]
  simp

end CrossCentralExactFaceCertifiedRebaseInvolutionCell

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
