import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseTransition

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

/-- Forget only the selected face of a complete channel state. -/
abbrev CrossCentralExactFaceCutChannelState.exactState
    {graphData : Data G} {data : AdjacentPairData G}
    (state : CrossCentralExactFaceCutChannelState graphData data) :
    CrossCentralExactFaceCutState graphData data :=
  state.2.1

/-- The terminal branches of a localized successor resolution.  The exact
rebase branch is deliberately omitted. -/
def LocalizedFusionSuccessorResolution.CertifiedTerminalOutcome
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion)
    (firstIndex secondIndex : Fin 2) : Prop :=
  successors.prefixSuccessor.edges.Disjoint
      successors.suffixSuccessor.edges ∨
    ∃ successor : LocalizedSuccessorFusionChainProfile cross face
        successors.prefixSuccessor successors.suffixSuccessor,
      ∃ signed : LocalizedFusionChainSignedTransferResolution
          successor.pair cross face,
        signed.CleanTransferIsDiagonal ∧
          signed.CleanClosedTransferIsRouteOnly firstIndex secondIndex

/-- Terminal normal forms of one support-certified remote witness.  This
keeps all retained-cycle and transfer certificates while excluding only
the geometric rebase constructor. -/
def CrossSideRemoteFusionChainTransferWitness.CertifiedTerminalOutcome
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    (witness : CrossSideRemoteFusionChainTransferWitness graphData data
      cross pair) : Prop :=
  (witness.firstIndex ≠ witness.secondIndex ∧
      rejectedCrossCentralReturnClosedTransfer witness.firstIndex
          witness.secondIndex = Equiv.refl (Bool × Bool)) ∨
    ∃ (_active : CrossSideRemoteFusionChainActiveState witness)
        (resolution : CrossSideRemoteFusionChainResolution graphData data
          cross pair witness.coordinate),
      (∃ (hroot : resolution.firstRoot ∈
            retainedVertexSet data.firstVertex data.secondVertex)
          (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).Walk ⟨resolution.firstRoot, hroot⟩
              ⟨resolution.firstRoot, hroot⟩),
        retainedFusion.IsCycle ∧
          data.retainedWalkToAmbient retainedFusion =
            resolution.firstFusion) ∨
      (∃ (hroot : resolution.secondRoot ∈
            retainedVertexSet data.firstVertex data.secondVertex)
          (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).Walk ⟨resolution.secondRoot, hroot⟩
              ⟨resolution.secondRoot, hroot⟩),
        retainedFusion.IsCycle ∧
          data.retainedWalkToAmbient retainedFusion =
            resolution.secondFusion) ∨
      ∃ successors : LocalizedFusionSuccessorResolution pair
          (edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data cross) witness.coordinate)
          resolution.firstFusion resolution.secondFusion,
        successors.CertifiedTerminalOutcome witness.firstIndex
          witness.secondIndex

/-- One rebase step with the complete minimal-counterexample provenance:
the remote witness, its active state, the support-certified fusion cycles,
and the localized successor pair are all retained. -/
structure CrossCentralExactFaceCertifiedRebaseStep
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) where
  witness : CrossSideRemoteFusionChainTransferWitness graphData
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic) source.1 source.2
  active : CrossSideRemoteFusionChainActiveState witness
  resolution : CrossSideRemoteFusionChainResolution graphData
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic) source.1 source.2 witness.coordinate
  firstFusion_mem_central : centralEdgeValue
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) ∈ resolution.firstFusion.edges
  secondFusion_mem_central : centralEdgeValue
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) ∈ resolution.secondFusion.edges
  successors : LocalizedFusionSuccessorResolution source.2
    (edgeCrossFaceCoordinateOrbitFace graphData
      (retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) source.1) witness.coordinate)
    resolution.firstFusion resolution.secondFusion
  rebase : CrossCentralExactFaceRebaseStep graphData
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic) witness.channelState successors

/-- Exact-pair target of a provenance-certified rebase step. -/
def CrossCentralExactFaceCertifiedRebaseStep.target
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) :=
  step.rebase.target.exactState

/-- The faithful exact-state dynamics generated by provenance-certified
minimal-counterexample rebases. -/
def CrossCentralExactFaceCertifiedRebaseTransition
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) : Prop :=
  ∃ step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source,
    step.target = target

/-- A certified rebase changes the retained cross. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.target_cross_ne
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    step.target.1 ≠ source.1 :=
  step.rebase.targetCross_ne

/-- Both target trails avoid the source cross edge. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.target_trails_avoid_source_cross
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    source.1.1 ∉ step.target.2.prefixTrail.edges ∧
      source.1.1 ∉ step.target.2.suffixTrail.edges := by
  constructor
  · change source.1.1 ∉ step.rebase.targetPair.prefixTrail.edges
    rw [step.rebase.target_prefixTrail]
    exact step.successors.prefix_avoids_cross
  · change source.1.1 ∉ step.rebase.targetPair.suffixTrail.edges
    rw [step.rebase.target_suffixTrail]
    exact step.successors.suffix_avoids_cross

/-- Every certified transition changes its retained cross. -/
theorem CrossCentralExactFaceCertifiedRebaseTransition.cross_ne
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransition graphData
      minimal baseData source target) :
    target.1 ≠ source.1 := by
  rcases transition with ⟨step, rfl⟩
  exact step.target_cross_ne

/-- Every certified transition removes the source cross from both target
trails. -/
theorem CrossCentralExactFaceCertifiedRebaseTransition.target_trails_avoid_source_cross
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransition graphData
      minimal baseData source target) :
    source.1.1 ∉ target.2.prefixTrail.edges ∧
      source.1.1 ∉ target.2.suffixTrail.edges := by
  rcases transition with ⟨step, rfl⟩
  exact step.target_trails_avoid_source_cross

/-- The provenance-certified transition relation is irreflexive. -/
theorem CrossCentralExactFaceCertifiedRebaseTransition.irrefl
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    (state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) :
    ¬CrossCentralExactFaceCertifiedRebaseTransition graphData minimal
      baseData state state := by
  intro transition
  exact transition.cross_ne rfl

/-- A minimal remote witness is terminal, or it supplies one faithful
provenance-certified rebase step. -/
theorem CrossSideRemoteFusionChainTransferWitness.certifiedTerminal_or_exists_rebaseStep_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross}
    (witness : CrossSideRemoteFusionChainTransferWitness graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross pair) :
    witness.CertifiedTerminalOutcome ∨
      Nonempty (CrossCentralExactFaceCertifiedRebaseStep graphData minimal
        baseData ⟨cross, pair⟩) := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases witness.mixedIndices_or_activeState with hmixed | hactive
  · exact Or.inl (Or.inl hmixed)
  · rcases hactive with ⟨active⟩
    rcases active.exists_resolution with ⟨resolution⟩
    let face := edgeCrossFaceCoordinateOrbitFace graphData
      (retainedEdgeToAmbientEdge data cross) witness.coordinate
    by_cases hfirstCentral : centralEdgeValue data ∈
        resolution.firstFusion.edges
    · by_cases hsecondCentral : centralEdgeValue data ∈
          resolution.secondFusion.edges
      · rcases oppositePortFusion_exists_successor_of_central data
          pair.prefixTrail face
          resolution.boundary_avoids_coordinate_face
          resolution.firstFusion resolution.firstFusion_isCycle
          resolution.firstFusion_support hfirstCentral cross
          resolution.firstFusion_avoids_cross with
          ⟨prefixSuccessor, hprefixPath, hprefixAvoids,
            hprefixClosure, hprefixSubset⟩
        rcases alternateOppositePortFusion_exists_successor_of_central data
          pair.suffixTrail face
          resolution.boundary_avoids_coordinate_face
          resolution.secondFusion resolution.secondFusion_isCycle
          resolution.secondFusion_support hsecondCentral cross
          resolution.secondFusion_avoids_cross with
          ⟨suffixSuccessor, hsuffixPath, hsuffixAvoids,
            hsuffixClosure, hsuffixSubset⟩
        have hfinite := pair.exists_localizedSuccessorFusionChainTrichotomy
          minimal face resolution.firstFusion
          resolution.firstFusion_support resolution.secondFusion
          resolution.secondFusion_support prefixSuccessor hprefixAvoids
          hprefixClosure hprefixSubset suffixSuccessor hsuffixClosure
          hsuffixSubset
        let successors : LocalizedFusionSuccessorResolution pair face
            resolution.firstFusion resolution.secondFusion := {
          prefixSuccessor := prefixSuccessor
          suffixSuccessor := suffixSuccessor
          prefix_isPath := hprefixPath
          prefix_avoids_cross := hprefixAvoids
          prefix_closure_isCycle := hprefixClosure
          prefix_ambient_edges_subset := hprefixSubset
          suffix_isPath := hsuffixPath
          suffix_avoids_cross := hsuffixAvoids
          suffix_closure_isCycle := hsuffixClosure
          suffix_ambient_edges_subset := hsuffixSubset
          finite_outcome := hfinite }
        have houtcome :=
          successors.finite_routeOnlyComposition_outcome_of_indices_eq
            graphData minimal baseData witness.firstIndex
              witness.secondIndex active.indices_eq
        have hterminal :=
          LocalizedFusionSuccessorResolution.terminalOrRebase_of_routeOnlyComposition
            (source := witness.channelState) successors
            witness.firstIndex witness.secondIndex houtcome
        cases hterminal with
        | disjoint hdisjoint =>
            exact Or.inl (Or.inr ⟨active, resolution,
              Or.inr (Or.inr ⟨successors, Or.inl hdisjoint⟩)⟩)
        | rebase rebase =>
            exact Or.inr ⟨{
              witness := witness
              active := active
              resolution := resolution
              firstFusion_mem_central := hfirstCentral
              secondFusion_mem_central := hsecondCentral
              successors := successors
              rebase := rebase }⟩
        | cleanRouteOnly successor signed hdiagonal hrouteOnly =>
            exact Or.inl (Or.inr ⟨active, resolution,
              Or.inr (Or.inr ⟨successors,
                Or.inr ⟨successor, signed, hdiagonal, hrouteOnly⟩⟩)⟩)
      · have hretained :=
          alternateOppositePortFusion_exists_retainedCycle_of_not_central
            data pair.suffixTrail face
              resolution.boundary_avoids_coordinate_face
              resolution.secondFusion resolution.secondFusion_isCycle
              resolution.secondFusion_support hsecondCentral
        exact Or.inl (Or.inr ⟨active, resolution,
          Or.inr (Or.inl hretained)⟩)
    · have hretained :=
        oppositePortFusion_exists_retainedCycle_of_not_central data
          pair.prefixTrail face resolution.boundary_avoids_coordinate_face
            resolution.firstFusion resolution.firstFusion_isCycle
            resolution.firstFusion_support hfirstCentral
      exact Or.inl (Or.inr ⟨active, resolution, Or.inl hretained⟩)

/-- Terminal outcome of an exact state, with a complete remote witness. -/
def CrossCentralExactFaceCutState.CertifiedTerminalOutcome
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) : Prop :=
  ∃ witness : CrossSideRemoteFusionChainTransferWitness graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) state.1 state.2,
    witness.CertifiedTerminalOutcome

/-- Every exact state in a minimal counterexample has a strict source-cycle
descent, a fully certified terminal normal form, or one faithful rebase
transition. -/
theorem CrossCentralExactFaceCutState.descent_or_certifiedTerminal_or_transition
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) :
    CrossCentralSourceClosureCycleDescent state.2 ∨
      state.CertifiedTerminalOutcome graphData minimal baseData ∨
      ∃ target, CrossCentralExactFaceCertifiedRebaseTransition graphData
        minimal baseData state target := by
  rcases state with ⟨cross, pair⟩
  rcases pair.sourceClosureCycleDescent_or_exists_finiteRebaseTransition
      minimal baseData with hdescent | ⟨witness, _houtcome⟩
  · exact Or.inl hdescent
  · rcases witness.certifiedTerminal_or_exists_rebaseStep_of_minimal
        graphData minimal baseData with hterminal | hstep
    · exact Or.inr (Or.inl ⟨witness, hterminal⟩)
    · rcases hstep with ⟨step⟩
      exact Or.inr (Or.inr ⟨step.target, step, rfl⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
