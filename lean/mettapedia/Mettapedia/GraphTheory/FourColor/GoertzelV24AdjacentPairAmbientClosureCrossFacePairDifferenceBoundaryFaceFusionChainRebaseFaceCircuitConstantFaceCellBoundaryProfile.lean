import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitConstantFaceCell
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureCycleIntersection
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24OrbitFaceWalk
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

/-- First ambient closure at the source of an involution cell. -/
abbrev sourcePrefixClosure
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :=
  (baseData.rotationOrderedData graphData minimal.spherical.cubic
    minimal.vertexRotationCyclic).oppositePortClosure
      cell.source.2.prefixTrail

/-- Second ambient closure at the source of an involution cell. -/
abbrev sourceSuffixClosure
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :=
  (baseData.rotationOrderedData graphData minimal.spherical.cubic
    minimal.vertexRotationCyclic).alternateOppositePortClosure
      cell.source.2.suffixTrail

/-- First ambient closure at the target of an involution cell. -/
abbrev targetPrefixClosure
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :=
  (baseData.rotationOrderedData graphData minimal.spherical.cubic
    minimal.vertexRotationCyclic).oppositePortClosure
      cell.target.2.prefixTrail

/-- Second ambient closure at the target of an involution cell. -/
abbrev targetSuffixClosure
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :=
  (baseData.rotationOrderedData graphData minimal.spherical.cubic
    minimal.vertexRotationCyclic).alternateOppositePortClosure
      cell.target.2.suffixTrail

/-- On the selected facial boundary, the two source closures meet together
exactly at the source cross. -/
theorem sourceClosures_both_iff_eq_sourceCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face) :
    (edge.1 ∈ cell.sourcePrefixClosure.edges ∧
        edge.1 ∈ cell.sourceSuffixClosure.edges) ↔
      edge = retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) cell.source.1 := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rw [data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
    cell.source.2.prefixTrail cell.source.2.suffixTrail cell.source.1
      cell.source.2.retainedIntersectionExact edge.1]
  constructor
  · rintro (hsource | hcentral)
    · exact Subtype.ext hsource
    · have hedge : edge = centralEdge data := Subtype.ext hcentral
      subst edge
      exact (cell.forward.central_not_mem_face hface).elim
  · intro hsource
    left
    exact congrArg Subtype.val hsource

/-- The two target closures likewise meet together on the selected face
exactly at the target cross. -/
theorem targetClosures_both_iff_eq_targetCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face) :
    (edge.1 ∈ cell.targetPrefixClosure.edges ∧
        edge.1 ∈ cell.targetSuffixClosure.edges) ↔
      edge = retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) cell.target.1 := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rw [data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
    cell.target.2.prefixTrail cell.target.2.suffixTrail cell.target.1
      cell.target.2.retainedIntersectionExact edge.1]
  constructor
  · rintro (htarget | hcentral)
    · exact Subtype.ext htarget
    · have hedge : edge = centralEdge data := Subtype.ext hcentral
      subst edge
      exact (cell.forward.central_not_mem_face hface).elim
  · intro htarget
    left
    exact congrArg Subtype.val htarget

/-- Toggling the selected facial boundary complements first-closure
membership edge by edge. -/
theorem targetPrefixClosure_mem_iff_not_sourcePrefixClosure_mem
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face) :
    edge.1 ∈ cell.targetPrefixClosure.edges ↔
      edge.1 ∉ cell.sourcePrefixClosure.edges := by
  have htoggle :=
    (cell.prefixClosure_support_symmDiff_iff_mem_face edge).2 hface
  constructor
  · intro htarget hsource
    rcases htoggle with hforward | hbackward
    · exact hforward.2 htarget
    · exact hbackward.1 hsource
  · intro hsource
    rcases htoggle with hforward | hbackward
    · exact False.elim (hsource hforward.1)
    · exact hbackward.2

/-- The same pointwise complement law holds for second-closure
membership. -/
theorem targetSuffixClosure_mem_iff_not_sourceSuffixClosure_mem
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face) :
    edge.1 ∈ cell.targetSuffixClosure.edges ↔
      edge.1 ∉ cell.sourceSuffixClosure.edges := by
  have htoggle :=
    (cell.suffixClosure_support_symmDiff_iff_mem_face edge).2 hface
  constructor
  · intro htarget hsource
    rcases htoggle with hforward | hbackward
    · exact hforward.2 htarget
    · exact hbackward.1 hsource
  · intro hsource
    rcases htoggle with hforward | hbackward
    · exact False.elim (hsource hforward.1)
    · exact hbackward.2

/-- On the selected facial boundary, absence from both source closures
occurs exactly at the target cross. -/
theorem sourceClosures_neither_iff_eq_targetCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face) :
    (edge.1 ∉ cell.sourcePrefixClosure.edges ∧
        edge.1 ∉ cell.sourceSuffixClosure.edges) ↔
      edge = retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) cell.target.1 := by
  calc
    (edge.1 ∉ cell.sourcePrefixClosure.edges ∧
          edge.1 ∉ cell.sourceSuffixClosure.edges) ↔
        (edge.1 ∈ cell.targetPrefixClosure.edges ∧
          edge.1 ∈ cell.targetSuffixClosure.edges) := by
            rw [cell.targetPrefixClosure_mem_iff_not_sourcePrefixClosure_mem
                edge hface,
              cell.targetSuffixClosure_mem_iff_not_sourceSuffixClosure_mem
                edge hface]
    _ ↔ edge = retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cell.target.1 :=
      cell.targetClosures_both_iff_eq_targetCross edge hface

/-- Dually, absence from both target closures occurs exactly at the source
cross. -/
theorem targetClosures_neither_iff_eq_sourceCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face) :
    (edge.1 ∉ cell.targetPrefixClosure.edges ∧
        edge.1 ∉ cell.targetSuffixClosure.edges) ↔
      edge = retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) cell.source.1 := by
  simpa [sourcePrefixClosure, sourceSuffixClosure, targetPrefixClosure,
    targetSuffixClosure] using
      (cell.symm.sourceClosures_neither_iff_eq_targetCross edge hface)

/-- Every other selected-face boundary edge belongs to exactly one of the
two source closures. -/
theorem sourceClosures_xor_iff_ne_crosses
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face) :
    Xor (edge.1 ∈ cell.sourcePrefixClosure.edges)
        (edge.1 ∈ cell.sourceSuffixClosure.edges) ↔
      edge ≠ retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cell.source.1 ∧
        edge ≠ retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cell.target.1 := by
  have hboth := cell.sourceClosures_both_iff_eq_sourceCross edge hface
  have hneither := cell.sourceClosures_neither_iff_eq_targetCross edge hface
  rw [xor_def]
  tauto

/-- The target closures have the symmetric exclusive-ownership profile. -/
theorem targetClosures_xor_iff_ne_crosses
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face) :
    Xor (edge.1 ∈ cell.targetPrefixClosure.edges)
        (edge.1 ∈ cell.targetSuffixClosure.edges) ↔
      edge ≠ retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cell.target.1 ∧
        edge ≠ retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cell.source.1 := by
  simpa [sourcePrefixClosure, sourceSuffixClosure, targetPrefixClosure,
    targetSuffixClosure, and_comm] using
      (cell.symm.sourceClosures_xor_iff_ne_crosses edge hface)

/-- Every ambient edge on the selected cell face belongs to the retained
deletion: the face avoids the central edge and all four boundary edges. -/
theorem faceEdge_isRetained
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face) :
    IsRetainedAmbientEdge
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) edge := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  apply isRetainedAmbientEdge_of_ne data edge
  · intro hedge
    have hedge' : edge = centralEdge data := Subtype.ext hedge
    exact cell.forward.central_not_mem_face (hedge' ▸ hface)
  · intro hedge
    have hedge' : edge = boundaryEdge data 0 := Subtype.ext hedge
    exact cell.forward.boundary_not_mem_face 0 (hedge' ▸ hface)
  · intro hedge
    have hedge' : edge = boundaryEdge data 1 := Subtype.ext hedge
    exact cell.forward.boundary_not_mem_face 1 (hedge' ▸ hface)
  · intro hedge
    have hedge' : edge = boundaryEdge data 2 := Subtype.ext hedge
    exact cell.forward.boundary_not_mem_face 2 (hedge' ▸ hface)
  · intro hedge
    have hedge' : edge = boundaryEdge data 3 := Subtype.ext hedge
    exact cell.forward.boundary_not_mem_face 3 (hedge' ▸ hface)

/-- A vertex reached while traversing the selected cell face cannot be one
of the two endpoints of the restored central edge. -/
theorem faceDart_snd_not_mem_centralEdgeValue
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (dart : graphData.toRotationSystem.D)
    (hface : dartOrbitFace graphData.toRotationSystem dart = cell.face) :
    dart.snd ∉ centralEdgeValue
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) := by
  let RS := graphData.toRotationSystem
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have hedgeFace : RS.edgeOf dart ∈
      orbitFaceBoundary RS cell.face := by
    rw [← hface]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS dart
  have hedgeRetained : IsRetainedAmbientEdge data (RS.edgeOf dart) :=
    cell.faceEdge_isRetained (RS.edgeOf dart) hedgeFace
  have hsndEdge : dart.snd ∈ (RS.edgeOf dart).1 := by
    simp [RS, SimpleGraph.Dart.edge]
  have hsndRetained : dart.snd ∈
      retainedVertexSet data.firstVertex data.secondVertex :=
    endpoints_mem_retainedVertexSet data (RS.edgeOf dart) hedgeRetained
      dart.snd hsndEdge
  intro hsndCentral
  have hsndDeleted : dart.snd = data.firstVertex ∨
      dart.snd = data.secondVertex := by
    simpa [centralEdgeValue] using hsndCentral
  rcases hsndDeleted with hfirst | hsecond
  · exact hsndRetained.1 hfirst
  · exact hsndRetained.2 hsecond

/-- Along the oriented selected-face boundary, a change from the prefix
closure to the suffix closure can occur only at an endpoint of the source
cross. -/
theorem sourcePrefix_then_suffix_vertex_mem_sourceCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (dart : graphData.toRotationSystem.D)
    (hface : dartOrbitFace graphData.toRotationSystem dart = cell.face)
    (hprefix : (graphData.toRotationSystem.edgeOf dart).1 ∈
      cell.sourcePrefixClosure.edges)
    (hsuffix :
      (graphData.toRotationSystem.edgeOf
        (graphData.toRotationSystem.phi dart)).1 ∈
          cell.sourceSuffixClosure.edges) :
    dart.snd ∈
      (retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) cell.source.1).1 := by
  let RS := graphData.toRotationSystem
  have hcycles := cell.closure_cycles
  have hprefixVertex : dart.snd ∈ cell.sourcePrefixClosure.support := by
    apply cell.sourcePrefixClosure.mem_support_of_mem_edges hprefix
    simp [SimpleGraph.Dart.edge]
  have hphiFst : dart.snd = (RS.phi dart).fst := by
    exact dartAdj_phi graphData dart
  have hsuffixVertex : dart.snd ∈ cell.sourceSuffixClosure.support := by
    apply cell.sourceSuffixClosure.mem_support_of_mem_edges hsuffix
    rw [hphiFst]
    simp [RS, SimpleGraph.Dart.edge]
  have hcommon :=
    (cell.source.2.mem_both_closure_support_iff minimal hcycles.1
      hcycles.2.1 dart.snd).1 ⟨hprefixVertex, hsuffixVertex⟩
  rcases hcommon with hsource | hcentral
  · exact hsource
  · exact False.elim
      (cell.faceDart_snd_not_mem_centralEdgeValue dart hface hcentral)

/-- The opposite directed ownership change has the same unique location:
an endpoint of the source cross. -/
theorem sourceSuffix_then_prefix_vertex_mem_sourceCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (dart : graphData.toRotationSystem.D)
    (hface : dartOrbitFace graphData.toRotationSystem dart = cell.face)
    (hsuffix : (graphData.toRotationSystem.edgeOf dart).1 ∈
      cell.sourceSuffixClosure.edges)
    (hprefix :
      (graphData.toRotationSystem.edgeOf
        (graphData.toRotationSystem.phi dart)).1 ∈
          cell.sourcePrefixClosure.edges) :
    dart.snd ∈
      (retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) cell.source.1).1 := by
  let RS := graphData.toRotationSystem
  have hcycles := cell.closure_cycles
  have hsuffixVertex : dart.snd ∈ cell.sourceSuffixClosure.support := by
    apply cell.sourceSuffixClosure.mem_support_of_mem_edges hsuffix
    simp [SimpleGraph.Dart.edge]
  have hphiFst : dart.snd = (RS.phi dart).fst := by
    exact dartAdj_phi graphData dart
  have hprefixVertex : dart.snd ∈ cell.sourcePrefixClosure.support := by
    apply cell.sourcePrefixClosure.mem_support_of_mem_edges hprefix
    rw [hphiFst]
    simp [RS, SimpleGraph.Dart.edge]
  have hcommon :=
    (cell.source.2.mem_both_closure_support_iff minimal hcycles.1
      hcycles.2.1 dart.snd).1 ⟨hprefixVertex, hsuffixVertex⟩
  rcases hcommon with hsource | hcentral
  · exact hsource
  · exact False.elim
      (cell.faceDart_snd_not_mem_centralEdgeValue dart hface hcentral)

/-- For the target closure pair, ownership changes only at an endpoint of
the target cross. -/
theorem targetPrefix_then_suffix_vertex_mem_targetCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (dart : graphData.toRotationSystem.D)
    (hface : dartOrbitFace graphData.toRotationSystem dart = cell.face)
    (hprefix : (graphData.toRotationSystem.edgeOf dart).1 ∈
      cell.targetPrefixClosure.edges)
    (hsuffix :
      (graphData.toRotationSystem.edgeOf
        (graphData.toRotationSystem.phi dart)).1 ∈
          cell.targetSuffixClosure.edges) :
    dart.snd ∈
      (retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) cell.target.1).1 := by
  simpa [sourcePrefixClosure, sourceSuffixClosure, targetPrefixClosure,
    targetSuffixClosure] using
      (cell.symm.sourcePrefix_then_suffix_vertex_mem_sourceCross dart hface
        hprefix hsuffix)

/-- The reverse target ownership change is likewise confined to a target
cross endpoint. -/
theorem targetSuffix_then_prefix_vertex_mem_targetCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (dart : graphData.toRotationSystem.D)
    (hface : dartOrbitFace graphData.toRotationSystem dart = cell.face)
    (hsuffix : (graphData.toRotationSystem.edgeOf dart).1 ∈
      cell.targetSuffixClosure.edges)
    (hprefix :
      (graphData.toRotationSystem.edgeOf
        (graphData.toRotationSystem.phi dart)).1 ∈
          cell.targetPrefixClosure.edges) :
    dart.snd ∈
      (retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) cell.target.1).1 := by
  simpa [sourcePrefixClosure, sourceSuffixClosure, targetPrefixClosure,
    targetSuffixClosure] using
      (cell.symm.sourceSuffix_then_prefix_vertex_mem_sourceCross dart hface
        hsuffix hprefix)

end CrossCentralExactFaceCertifiedRebaseInvolutionCell

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
