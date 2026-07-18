import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebasePumping

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
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

/-- The ambient face selected by a provenance-certified exact rebase. -/
abbrev CrossCentralExactFaceCertifiedRebaseStep.selectedFace
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) : OrbitFace graphData.toRotationSystem :=
  edgeCrossFaceCoordinateOrbitFace graphData
    (retainedEdgeToAmbientEdge
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) source.1) step.witness.coordinate

/-- A certified target prefix can introduce retained edges only on the
selected face. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.target_prefix_edge_mem_source_or_selectedFace
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source)
    (edge : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet)
    (hmem : edge.1 ∈ step.target.2.prefixTrail.edges) :
    edge.1 ∈ source.2.prefixTrail.edges ∨
      retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) edge ∈
        orbitFaceBoundary graphData.toRotationSystem step.selectedFace := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have hsuccessor : edge.1 ∈ step.successors.prefixSuccessor.edges := by
    change edge.1 ∈ step.rebase.targetPair.prefixTrail.edges at hmem
    rw [step.rebase.target_prefixTrail] at hmem
    exact hmem
  have hambient : (retainedEdgeToAmbientEdge data edge).1 ∈
      (data.retainedWalkToAmbient step.successors.prefixSuccessor).edges :=
    (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
      data step.successors.prefixSuccessor edge).2 hsuccessor
  have hfusion : (retainedEdgeToAmbientEdge data edge).1 ∈
      step.resolution.firstFusion.edges :=
    step.successors.prefix_ambient_edges_subset hambient
  rcases step.resolution.firstFusion_support
      (retainedEdgeToAmbientEdge data edge) hfusion with hsource | hface
  · exact Or.inl
      ((retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data source.2.prefixTrail edge).1 hsource)
  · exact Or.inr hface

/-- A certified target suffix can introduce retained edges only on the
selected face. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.target_suffix_edge_mem_source_or_selectedFace
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source)
    (edge : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet)
    (hmem : edge.1 ∈ step.target.2.suffixTrail.edges) :
    edge.1 ∈ source.2.suffixTrail.edges ∨
      retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) edge ∈
        orbitFaceBoundary graphData.toRotationSystem step.selectedFace := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have hsuccessor : edge.1 ∈ step.successors.suffixSuccessor.edges := by
    change edge.1 ∈ step.rebase.targetPair.suffixTrail.edges at hmem
    rw [step.rebase.target_suffixTrail] at hmem
    exact hmem
  have hambient : (retainedEdgeToAmbientEdge data edge).1 ∈
      (data.retainedWalkToAmbient step.successors.suffixSuccessor).edges :=
    (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
      data step.successors.suffixSuccessor edge).2 hsuccessor
  have hfusion : (retainedEdgeToAmbientEdge data edge).1 ∈
      step.resolution.secondFusion.edges :=
    step.successors.suffix_ambient_edges_subset hambient
  rcases step.resolution.secondFusion_support
      (retainedEdgeToAmbientEdge data edge) hfusion with hsource | hface
  · exact Or.inl
      ((retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
        source.2.suffixTrail edge).1 hsource)
  · exact Or.inr hface

/-- The source cross is supported by the selected face. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.source_cross_mem_selectedFace
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) source.1 ∈
      orbitFaceBoundary graphData.toRotationSystem step.selectedFace :=
  step.witness.cross_mem_coordinate_face

/-- The target cross remains supported by the selected face. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.target_cross_mem_selectedFace
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) step.target.1 ∈
      orbitFaceBoundary graphData.toRotationSystem step.selectedFace :=
  step.rebase.targetCross_mem_face

/-- The selected remote face avoids the restored central edge. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.central_not_mem_selectedFace
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    centralEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) ∉
      orbitFaceBoundary graphData.toRotationSystem step.selectedFace :=
  step.witness.central_not_mem_coordinate_face

/-- The selected remote face avoids all four restored boundary edges. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.boundary_not_mem_selectedFace
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) (port : Fin 4) :
    boundaryEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) port ∉
      orbitFaceBoundary graphData.toRotationSystem step.selectedFace :=
  step.resolution.boundary_avoids_coordinate_face port

/-- Faithful certified rebases whose selected geometric face is fixed. -/
def CrossCentralExactFaceCertifiedRebaseTransitionOnFace
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (face : OrbitFace graphData.toRotationSystem)
    (source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) : Prop :=
  ∃ step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source,
    step.target = target ∧ step.selectedFace = face

/-- Forgetting the fixed-face certificate gives the faithful transition. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.to_transition
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    CrossCentralExactFaceCertifiedRebaseTransition graphData minimal
      baseData source target := by
  rcases transition with ⟨step, htarget, _⟩
  exact ⟨step, htarget⟩

/-- A fixed-face transition changes its retained cross. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.cross_ne
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    target.1 ≠ source.1 :=
  transition.to_transition.cross_ne

/-- Off the fixed face, a transition's target prefix is contained in its
source prefix. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.target_prefix_offFace_subset_source
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target)
    (edge : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet)
    (hoff : retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) edge ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    (hmem : edge.1 ∈ target.2.prefixTrail.edges) :
    edge.1 ∈ source.2.prefixTrail.edges := by
  rcases transition with ⟨step, rfl, hface⟩
  rcases step.target_prefix_edge_mem_source_or_selectedFace edge hmem with
    hsource | hselected
  · exact hsource
  · exact False.elim (hoff (hface ▸ hselected))

/-- Off the fixed face, a transition's target suffix is contained in its
source suffix. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.target_suffix_offFace_subset_source
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target)
    (edge : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet)
    (hoff : retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) edge ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    (hmem : edge.1 ∈ target.2.suffixTrail.edges) :
    edge.1 ∈ source.2.suffixTrail.edges := by
  rcases transition with ⟨step, rfl, hface⟩
  rcases step.target_suffix_edge_mem_source_or_selectedFace edge hmem with
    hsource | hselected
  · exact hsource
  · exact False.elim (hoff (hface ▸ hselected))

/-- Off one fixed face, prefix support is antitone along every finite
certified rebase run. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_prefix_offFace_subset
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (run : Relation.ReflTransGen
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData face) source target)
    (edge : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet)
    (hoff : retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) edge ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    (hmem : edge.1 ∈ target.2.prefixTrail.edges) :
    edge.1 ∈ source.2.prefixTrail.edges := by
  induction run with
  | refl => exact hmem
  | tail run transition ih =>
      exact ih (transition.target_prefix_offFace_subset_source edge hoff hmem)

/-- Off one fixed face, suffix support is antitone along every finite
certified rebase run. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_suffix_offFace_subset
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (run : Relation.ReflTransGen
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData face) source target)
    (edge : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet)
    (hoff : retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) edge ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    (hmem : edge.1 ∈ target.2.suffixTrail.edges) :
    edge.1 ∈ source.2.suffixTrail.edges := by
  induction run with
  | refl => exact hmem
  | tail run transition ih =>
      exact ih (transition.target_suffix_offFace_subset_source edge hoff hmem)

/-- Expose the first transition of a nonempty transitive run. -/
theorem transGen_exists_head_reflTransGen
    {State : Type*} {transition : State → State → Prop}
    {source target : State}
    (run : Relation.TransGen transition source target) :
    ∃ next, transition source next ∧
      Relation.ReflTransGen transition next target := by
  induction run using Relation.TransGen.head_induction_on with
  | single step => exact ⟨target, step, Relation.ReflTransGen.refl⟩
  | head step run _ => exact ⟨_, step, run.to_reflTransGen⟩

/-- In a nonempty closed certified run on one face, the first step changes
the cross but preserves both trail supports exactly away from that face. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exists_firstStep_offFace_support_eq_of_cycle
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (cycle : Relation.TransGen
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData face) state state) :
    ∃ next,
      CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
          minimal baseData face state next ∧
        next.1 ≠ state.1 ∧
        Relation.ReflTransGen
          (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
            minimal baseData face) next state ∧
        (∀ edge : (DeletedAdjacentPairGraph G
            (baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).firstVertex
            (baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).secondVertex).edgeSet,
          retainedEdgeToAmbientEdge
              (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic) edge ∉
              orbitFaceBoundary graphData.toRotationSystem face →
            (edge.1 ∈ next.2.prefixTrail.edges ↔
                edge.1 ∈ state.2.prefixTrail.edges) ∧
              (edge.1 ∈ next.2.suffixTrail.edges ↔
                edge.1 ∈ state.2.suffixTrail.edges)) := by
  rcases transGen_exists_head_reflTransGen cycle with
    ⟨next, first, rest⟩
  refine ⟨next, first, first.cross_ne, rest, ?_⟩
  intro edge hoff
  constructor
  · constructor
    · exact first.target_prefix_offFace_subset_source edge hoff
    · exact
        CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_prefix_offFace_subset
          rest edge hoff
  · constructor
    · exact first.target_suffix_offFace_subset_source edge hoff
    · exact
        CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_suffix_offFace_subset
          rest edge hoff

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
