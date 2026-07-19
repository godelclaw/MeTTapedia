import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitConstantFace

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
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

omit [Fintype V] [DecidableRel G.Adj] in
private theorem trail_support_symmDiff_iff_of_parity_add_eq_indicator
    {firstStart firstFinish secondStart secondFinish : V}
    (first : G.Walk firstStart firstFinish)
    (second : G.Walk secondStart secondFinish)
    (hfirstTrail : first.IsTrail) (hsecondTrail : second.IsTrail)
    (edge : G.edgeSet) (support : Prop) [Decidable support]
    (hparity : walkEdgeParity first edge + walkEdgeParity second edge =
      if support then 1 else 0) :
    ((edge.1 ∈ first.edges ∧ edge.1 ∉ second.edges) ∨
        (edge.1 ∉ first.edges ∧ edge.1 ∈ second.edges)) ↔
      support := by
  by_cases hfirstMem : edge.1 ∈ first.edges
  · have hfirstParity : walkEdgeParity first edge = 1 :=
      walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
        hfirstTrail edge hfirstMem
    by_cases hsecondMem : edge.1 ∈ second.edges
    · have hsecondParity : walkEdgeParity second edge = 1 :=
        walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
          hsecondTrail edge hsecondMem
      have hnotSupport : ¬support := by
        intro hsupport
        rw [hfirstParity, hsecondParity, zmod2_add_self,
          if_pos hsupport] at hparity
        exact zero_ne_one hparity
      simp [hfirstMem, hsecondMem, hnotSupport]
    · have hsecondParity : walkEdgeParity second edge = 0 :=
        walkEdgeParity_apply_eq_zero_of_not_mem_edges second edge hsecondMem
      have hsupport : support := by
        by_contra hnotSupport
        rw [hfirstParity, hsecondParity, if_neg hnotSupport] at hparity
        norm_num at hparity
      simp [hfirstMem, hsecondMem, hsupport]
  · have hfirstParity : walkEdgeParity first edge = 0 :=
      walkEdgeParity_apply_eq_zero_of_not_mem_edges first edge hfirstMem
    by_cases hsecondMem : edge.1 ∈ second.edges
    · have hsecondParity : walkEdgeParity second edge = 1 :=
        walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
          hsecondTrail edge hsecondMem
      have hsupport : support := by
        by_contra hnotSupport
        rw [hfirstParity, hsecondParity, if_neg hnotSupport] at hparity
        norm_num at hparity
      simp [hfirstMem, hsecondMem, hsupport]
    · have hsecondParity : walkEdgeParity second edge = 0 :=
        walkEdgeParity_apply_eq_zero_of_not_mem_edges second edge hsecondMem
      have hnotSupport : ¬support := by
        intro hsupport
        rw [hfirstParity, hsecondParity, if_pos hsupport] at hparity
        norm_num at hparity
      simp [hfirstMem, hsecondMem, hnotSupport]

private theorem orbitFaceBoundaryLinearMap_single_eq_indicator
    (graphData : Data G)
    (face : OrbitFace graphData.toRotationSystem) :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem
        (Pi.single face 1) =
      orbitFaceBoundaryIndicator graphData face := by
  classical
  funext edge
  rw [orbitFaceBoundaryLinearMap_apply, Fintype.sum_eq_single face]
  · simp [orbitFaceBoundaryIndicator]
  · intro other hne
    simp [hne]

/-- The exact local normal form left by a two-arc certified rebase circuit:
two distinct cut states rebase to one another on one geometric face. -/
structure CrossCentralExactFaceCertifiedRebaseInvolutionCell
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G) where
  face : OrbitFace graphData.toRotationSystem
  source : CrossCentralExactFaceCutState graphData
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic)
  target : CrossCentralExactFaceCutState graphData
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic)
  forward : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
    graphData minimal baseData face source target
  backward : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
    graphData minimal baseData face target source

/-- Every provenance-certified fixed-face target prefix closure is a
genuine simple cycle. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.target_prefixClosure_isCycle
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    ((baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic).oppositePortClosure
        target.2.prefixTrail).IsCycle := by
  rcases transition with ⟨step, rfl, _⟩
  change ((baseData.rotationOrderedData graphData minimal.spherical.cubic
    minimal.vertexRotationCyclic).oppositePortClosure
      step.rebase.targetPair.prefixTrail).IsCycle
  rw [step.rebase.target_prefixTrail]
  exact step.successors.prefix_closure_isCycle

/-- Every provenance-certified fixed-face target suffix closure is likewise
a genuine simple cycle. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.target_suffixClosure_isCycle
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    ((baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic).alternateOppositePortClosure
        target.2.suffixTrail).IsCycle := by
  rcases transition with ⟨step, rfl, _⟩
  change ((baseData.rotationOrderedData graphData minimal.spherical.cubic
    minimal.vertexRotationCyclic).alternateOppositePortClosure
      step.rebase.targetPair.suffixTrail).IsCycle
  rw [step.rebase.target_suffixTrail]
  exact step.successors.suffix_closure_isCycle

namespace CrossCentralExactFaceCertifiedRebaseInvolutionCell

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- The two retained crosses of an involution cell are different. -/
theorem cross_ne
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    cell.target.1 ≠ cell.source.1 :=
  cell.forward.cross_ne

/-- Both retained crosses lie on the cell's selected face. -/
theorem crosses_mem_face
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cell.source.1 ∈
        orbitFaceBoundary graphData.toRotationSystem cell.face ∧
      retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) cell.target.1 ∈
        orbitFaceBoundary graphData.toRotationSystem cell.face :=
  ⟨cell.forward.source_cross_mem_face,
    cell.forward.target_cross_mem_face⟩

/-- Both closure pairs in an involution cell are provenance-certified
simple cycles. -/
theorem closure_cycles
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    (data.oppositePortClosure cell.source.2.prefixTrail).IsCycle ∧
      (data.alternateOppositePortClosure
        cell.source.2.suffixTrail).IsCycle ∧
      (data.oppositePortClosure cell.target.2.prefixTrail).IsCycle ∧
      (data.alternateOppositePortClosure
        cell.target.2.suffixTrail).IsCycle := by
  exact ⟨cell.backward.target_prefixClosure_isCycle,
    cell.backward.target_suffixClosure_isCycle,
    cell.forward.target_prefixClosure_isCycle,
    cell.forward.target_suffixClosure_isCycle⟩

/-- Away from the selected face, the two prefix closures have exactly the
same support. -/
theorem prefixClosure_offFace_iff
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hoff : edge ∉ orbitFaceBoundary graphData.toRotationSystem cell.face) :
    edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              cell.source.2.prefixTrail).edges ↔
      edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              cell.target.2.prefixTrail).edges := by
  constructor
  · exact cell.backward.target_prefixClosure_offFace_subset_source edge hoff
  · exact cell.forward.target_prefixClosure_offFace_subset_source edge hoff

/-- Away from the selected face, the two suffix closures likewise have
exactly the same support. -/
theorem suffixClosure_offFace_iff
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet)
    (hoff : edge ∉ orbitFaceBoundary graphData.toRotationSystem cell.face) :
    edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).alternateOppositePortClosure
              cell.source.2.suffixTrail).edges ↔
      edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).alternateOppositePortClosure
              cell.target.2.suffixTrail).edges := by
  constructor
  · exact cell.backward.target_suffixClosure_offFace_subset_source edge hoff
  · exact cell.forward.target_suffixClosure_offFace_subset_source edge hoff

/-- The binary symmetric difference of the two prefix closures is exactly
the selected facial boundary. -/
theorem prefixParity_add_eq_faceBoundaryIndicator
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    walkEdgeParity (data.oppositePortClosure cell.source.2.prefixTrail) +
        walkEdgeParity (data.oppositePortClosure cell.target.2.prefixTrail) =
      orbitFaceBoundaryIndicator graphData cell.face := by
  exact
    cell.forward.prefixParity_add_eq_faceBoundaryIndicator_of_offFace_support_eq
      cell.prefixClosure_offFace_iff

/-- The suffix closures have the same exact facial symmetric difference. -/
theorem suffixParity_add_eq_faceBoundaryIndicator
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    walkEdgeParity
          (data.alternateOppositePortClosure cell.source.2.suffixTrail) +
        walkEdgeParity
          (data.alternateOppositePortClosure cell.target.2.suffixTrail) =
      orbitFaceBoundaryIndicator graphData cell.face := by
  exact
    cell.forward.suffixParity_add_eq_faceBoundaryIndicator_of_offFace_support_eq
      cell.suffixClosure_offFace_iff

/-- After the selected face is toggled, the two exact label pairs differ
only by one unique pair of global binary complements.  This is the finite
label-transfer letter carried by an involution cell. -/
theorem existsUnique_labelToggleProfile
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    ∃! profile : F2 × F2,
      (∀ selectedFace,
        cell.target.2.prefixLabels selectedFace =
          cell.source.2.prefixLabels selectedFace +
            (Pi.single cell.face 1 :
              OrbitFace graphData.toRotationSystem → F2) selectedFace +
                profile.1) ∧
      (∀ selectedFace,
        cell.target.2.suffixLabels selectedFace =
          cell.source.2.suffixLabels selectedFace +
            (Pi.single cell.face 1 :
              OrbitFace graphData.toRotationSystem → F2) selectedFace +
                profile.2) := by
  let RS := graphData.toRotationSystem
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let prefixToggled :=
    cell.source.2.prefixLabels + Pi.single cell.face 1
  let suffixToggled :=
    cell.source.2.suffixLabels + Pi.single cell.face 1
  have hprefixBoundary : orbitFaceBoundaryLinearMap RS prefixToggled =
      orbitFaceBoundaryLinearMap RS cell.target.2.prefixLabels := by
    calc
      orbitFaceBoundaryLinearMap RS prefixToggled =
          orbitFaceBoundaryLinearMap RS cell.source.2.prefixLabels +
            orbitFaceBoundaryLinearMap RS (Pi.single cell.face 1) := by
              rw [map_add]
      _ = walkEdgeParity
              (data.oppositePortClosure cell.source.2.prefixTrail) +
            orbitFaceBoundaryIndicator graphData cell.face := by
              rw [cell.source.2.prefixBoundary,
                orbitFaceBoundaryLinearMap_single_eq_indicator]
      _ = walkEdgeParity
              (data.oppositePortClosure cell.target.2.prefixTrail) := by
            rw [← cell.prefixParity_add_eq_faceBoundaryIndicator]
            funext edge
            simp only [Pi.add_apply]
            rw [← add_assoc, zmod2_add_self, zero_add]
      _ = orbitFaceBoundaryLinearMap RS
          cell.target.2.prefixLabels := cell.target.2.prefixBoundary.symm
  have hsuffixBoundary : orbitFaceBoundaryLinearMap RS suffixToggled =
      orbitFaceBoundaryLinearMap RS cell.target.2.suffixLabels := by
    calc
      orbitFaceBoundaryLinearMap RS suffixToggled =
          orbitFaceBoundaryLinearMap RS cell.source.2.suffixLabels +
            orbitFaceBoundaryLinearMap RS (Pi.single cell.face 1) := by
              rw [map_add]
      _ = walkEdgeParity
              (data.alternateOppositePortClosure
                cell.source.2.suffixTrail) +
            orbitFaceBoundaryIndicator graphData cell.face := by
              rw [cell.source.2.suffixBoundary,
                orbitFaceBoundaryLinearMap_single_eq_indicator]
      _ = walkEdgeParity
              (data.alternateOppositePortClosure
                cell.target.2.suffixTrail) := by
            rw [← cell.suffixParity_add_eq_faceBoundaryIndicator]
            funext edge
            simp only [Pi.add_apply]
            rw [← add_assoc, zmod2_add_self, zero_add]
      _ = orbitFaceBoundaryLinearMap RS
          cell.target.2.suffixLabels := cell.target.2.suffixBoundary.symm
  rcases orbitFaceLabels_eq_add_constant_of_boundary_eq minimal
      prefixToggled cell.target.2.prefixLabels hprefixBoundary with
    ⟨prefixShift, hprefixShift⟩
  rcases orbitFaceLabels_eq_add_constant_of_boundary_eq minimal
      suffixToggled cell.target.2.suffixLabels hsuffixBoundary with
    ⟨suffixShift, hsuffixShift⟩
  refine ⟨(prefixShift, suffixShift), ?_, ?_⟩
  · constructor
    · intro selectedFace
      simpa [prefixToggled, Pi.add_apply] using
        hprefixShift selectedFace
    · intro selectedFace
      simpa [suffixToggled, Pi.add_apply] using
        hsuffixShift selectedFace
  · intro other hother
    apply Prod.ext
    · have hactual := hprefixShift cell.face
      have hclaimed := hother.1 cell.face
      change cell.target.2.prefixLabels cell.face =
          (cell.source.2.prefixLabels cell.face +
            (Pi.single cell.face 1 :
              OrbitFace graphData.toRotationSystem → F2) cell.face) +
                prefixShift at hactual
      exact (add_left_cancel (hactual.symm.trans hclaimed)).symm
    · have hactual := hsuffixShift cell.face
      have hclaimed := hother.2 cell.face
      change cell.target.2.suffixLabels cell.face =
          (cell.source.2.suffixLabels cell.face +
            (Pi.single cell.face 1 :
              OrbitFace graphData.toRotationSystem → F2) cell.face) +
                suffixShift at hactual
      exact (add_left_cancel (hactual.symm.trans hclaimed)).symm

/-- The four-state finite label-transfer letter of an involution cell. -/
noncomputable def labelToggleProfile
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) : F2 × F2 :=
  Classical.choose cell.existsUnique_labelToggleProfile

/-- The selected profile realizes the exact face toggle on both label
channels. -/
theorem labelToggleProfile_spec
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    (∀ selectedFace,
      cell.target.2.prefixLabels selectedFace =
        cell.source.2.prefixLabels selectedFace +
          (Pi.single cell.face 1 :
            OrbitFace graphData.toRotationSystem → F2) selectedFace +
              cell.labelToggleProfile.1) ∧
    (∀ selectedFace,
      cell.target.2.suffixLabels selectedFace =
        cell.source.2.suffixLabels selectedFace +
          (Pi.single cell.face 1 :
            OrbitFace graphData.toRotationSystem → F2) selectedFace +
              cell.labelToggleProfile.2) :=
  (Classical.choose_spec cell.existsUnique_labelToggleProfile).1

/-- An ambient edge belongs to exactly one of the two prefix closures if
and only if it belongs to the selected facial boundary. -/
theorem prefixClosure_support_symmDiff_iff_mem_face
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    ((edge.1 ∈
          (data.oppositePortClosure cell.source.2.prefixTrail).edges ∧
        edge.1 ∉
          (data.oppositePortClosure cell.target.2.prefixTrail).edges) ∨
      (edge.1 ∉
          (data.oppositePortClosure cell.source.2.prefixTrail).edges ∧
        edge.1 ∈
          (data.oppositePortClosure cell.target.2.prefixTrail).edges)) ↔
      edge ∈ orbitFaceBoundary graphData.toRotationSystem cell.face := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  apply trail_support_symmDiff_iff_of_parity_add_eq_indicator
    (data.oppositePortClosure cell.source.2.prefixTrail)
    (data.oppositePortClosure cell.target.2.prefixTrail)
    cell.source.2.prefixTrail_isTrail cell.target.2.prefixTrail_isTrail edge
      (edge ∈ orbitFaceBoundary graphData.toRotationSystem cell.face)
  have hparity := congrFun cell.prefixParity_add_eq_faceBoundaryIndicator edge
  simpa [orbitFaceBoundaryIndicator] using hparity

/-- The same selected facial boundary is exactly the symmetric difference
of the two suffix closures. -/
theorem suffixClosure_support_symmDiff_iff_mem_face
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (edge : G.edgeSet) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    ((edge.1 ∈
          (data.alternateOppositePortClosure
            cell.source.2.suffixTrail).edges ∧
        edge.1 ∉
          (data.alternateOppositePortClosure
            cell.target.2.suffixTrail).edges) ∨
      (edge.1 ∉
          (data.alternateOppositePortClosure
            cell.source.2.suffixTrail).edges ∧
        edge.1 ∈
          (data.alternateOppositePortClosure
            cell.target.2.suffixTrail).edges)) ↔
      edge ∈ orbitFaceBoundary graphData.toRotationSystem cell.face := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  apply trail_support_symmDiff_iff_of_parity_add_eq_indicator
    (data.alternateOppositePortClosure cell.source.2.suffixTrail)
    (data.alternateOppositePortClosure cell.target.2.suffixTrail)
    cell.source.2.suffixTrail_isTrail cell.target.2.suffixTrail_isTrail edge
      (edge ∈ orbitFaceBoundary graphData.toRotationSystem cell.face)
  have hparity := congrFun cell.suffixParity_add_eq_faceBoundaryIndicator edge
  simpa [orbitFaceBoundaryIndicator] using hparity

/-- The old retained cross belongs to both old closures and to neither new
closure. -/
theorem sourceCross_support_polarity
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    let edge := retainedEdgeToAmbientEdge data cell.source.1
    edge.1 ∈ (data.oppositePortClosure
          cell.source.2.prefixTrail).edges ∧
      edge.1 ∈ (data.alternateOppositePortClosure
          cell.source.2.suffixTrail).edges ∧
      edge.1 ∉ (data.oppositePortClosure
          cell.target.2.prefixTrail).edges ∧
      edge.1 ∉ (data.alternateOppositePortClosure
          cell.target.2.suffixTrail).edges := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let edge := retainedEdgeToAmbientEdge data cell.source.1
  have hprefixSource : edge.1 ∈
      (data.oppositePortClosure cell.source.2.prefixTrail).edges :=
    cell.source.2.cross_mem_oppositePortClosure
  have hsuffixSource : edge.1 ∈
      (data.alternateOppositePortClosure cell.source.2.suffixTrail).edges :=
    (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
      (data := data) cell.source.2.suffixTrail cell.source.1).2
        ((cell.source.2.retainedIntersectionExact cell.source.1.1).2 rfl).2
  have hprefixXor :=
    (cell.prefixClosure_support_symmDiff_iff_mem_face edge).2
      cell.crosses_mem_face.1
  have hsuffixXor :=
    (cell.suffixClosure_support_symmDiff_iff_mem_face edge).2
      cell.crosses_mem_face.1
  have hprefixTarget : edge.1 ∉
      (data.oppositePortClosure cell.target.2.prefixTrail).edges := by
    rcases hprefixXor with hforward | hbackward
    · exact hforward.2
    · exact False.elim (hbackward.1 hprefixSource)
  have hsuffixTarget : edge.1 ∉
      (data.alternateOppositePortClosure cell.target.2.suffixTrail).edges := by
    rcases hsuffixXor with hforward | hbackward
    · exact hforward.2
    · exact False.elim (hbackward.1 hsuffixSource)
  exact ⟨hprefixSource, hsuffixSource, hprefixTarget, hsuffixTarget⟩

/-- The new retained cross has the opposite exact polarity: it belongs to
both new closures and to neither old closure. -/
theorem targetCross_support_polarity
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    let edge := retainedEdgeToAmbientEdge data cell.target.1
    edge.1 ∉ (data.oppositePortClosure
          cell.source.2.prefixTrail).edges ∧
      edge.1 ∉ (data.alternateOppositePortClosure
          cell.source.2.suffixTrail).edges ∧
      edge.1 ∈ (data.oppositePortClosure
          cell.target.2.prefixTrail).edges ∧
      edge.1 ∈ (data.alternateOppositePortClosure
          cell.target.2.suffixTrail).edges := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let edge := retainedEdgeToAmbientEdge data cell.target.1
  have hprefixTarget : edge.1 ∈
      (data.oppositePortClosure cell.target.2.prefixTrail).edges :=
    cell.target.2.cross_mem_oppositePortClosure
  have hsuffixTarget : edge.1 ∈
      (data.alternateOppositePortClosure cell.target.2.suffixTrail).edges :=
    (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
      (data := data) cell.target.2.suffixTrail cell.target.1).2
        ((cell.target.2.retainedIntersectionExact cell.target.1.1).2 rfl).2
  have hprefixXor :=
    (cell.prefixClosure_support_symmDiff_iff_mem_face edge).2
      cell.crosses_mem_face.2
  have hsuffixXor :=
    (cell.suffixClosure_support_symmDiff_iff_mem_face edge).2
      cell.crosses_mem_face.2
  have hprefixSource : edge.1 ∉
      (data.oppositePortClosure cell.source.2.prefixTrail).edges := by
    rcases hprefixXor with hforward | hbackward
    · exact False.elim (hforward.2 hprefixTarget)
    · exact hbackward.1
  have hsuffixSource : edge.1 ∉
      (data.alternateOppositePortClosure cell.source.2.suffixTrail).edges := by
    rcases hsuffixXor with hforward | hbackward
    · exact False.elim (hforward.2 hsuffixTarget)
    · exact hbackward.1
  exact ⟨hprefixSource, hsuffixSource, hprefixTarget, hsuffixTarget⟩

end CrossCentralExactFaceCertifiedRebaseInvolutionCell

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- Every certified rebase circuit of length two is one exact involution
cell, retaining both provenance-certified directions. -/
theorem exists_involutionCell_of_arcLength_eq_two
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (hlength : circuit.arcLength = 2) :
    Nonempty (CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) := by
  cases hrest : circuit.rest with
  | nil =>
      have hone : circuit.arcLength = 1 := by simp [arcLength, hrest]
      omega
  | cons second tail =>
      cases htail : tail with
      | nil =>
          have hfirstSecond :
              CrossCentralExactFaceCertifiedRebaseArc.Follows
                circuit.first second := by
            simpa [hrest, htail] using circuit.consecutive
          have hsecondFirst :
              CrossCentralExactFaceCertifiedRebaseArc.Follows
                second circuit.first := by
            simpa [hrest, htail] using circuit.closing
          have hforward :
              CrossCentralExactFaceCertifiedRebaseTransitionOnFace
                graphData minimal baseData circuit.first.selectedFace
                  circuit.first.source second.source := by
            rw [← hfirstSecond]
            exact circuit.first.transition
          have hbackwardOnSecond :
              CrossCentralExactFaceCertifiedRebaseTransitionOnFace
                graphData minimal baseData second.selectedFace
                  second.source circuit.first.source := by
            rw [← hsecondFirst]
            exact second.transition
          have hfaces : circuit.first.selectedFace = second.selectedFace :=
            hforward.faces_eq_of_twoStep_cycle hbackwardOnSecond
          exact ⟨{
            face := circuit.first.selectedFace
            source := circuit.first.source
            target := second.source
            forward := hforward
            backward := by simpa [← hfaces] using hbackwardOnSecond }⟩
      | cons third more =>
          have hthree : 3 ≤ circuit.arcLength := by
            simp [arcLength, hrest, htail]
          omega

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
