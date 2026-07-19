import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitConstantFaceCellBoundaryIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileReversedDartSplice

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

/-- Forget the distinguished singleton cross while retaining the complete
finite shared-edge profile of an exact cross-central face-cut pair. -/
def CrossCentralExactFaceCutPair.toRetainedIntersectionProfile
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    RetainedIntersectionExactFaceCutPair graphData data where
  prefixTrail := pair.prefixTrail
  suffixTrail := pair.suffixTrail
  prefixLabels := pair.prefixLabels
  suffixLabels := pair.suffixLabels
  prefixTrail_isTrail := pair.prefixTrail_isTrail
  suffixTrail_isTrail := pair.suffixTrail_isTrail
  prefixBoundary := pair.prefixBoundary
  suffixBoundary := pair.suffixBoundary
  prefixExact := pair.prefixExact
  suffixExact := pair.suffixExact

@[simp] theorem CrossCentralExactFaceCutPair.toRetainedIntersectionProfile_prefixTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.toRetainedIntersectionProfile.prefixTrail = pair.prefixTrail :=
  rfl

@[simp] theorem CrossCentralExactFaceCutPair.toRetainedIntersectionProfile_suffixTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.toRetainedIntersectionProfile.suffixTrail = pair.suffixTrail :=
  rfl

/-- The forgotten retained profile is exactly the singleton distinguished
cross. -/
theorem CrossCentralExactFaceCutPair.toRetainedIntersectionProfile_sharedEdges
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.toRetainedIntersectionProfile.sharedEdges = {cross} := by
  ext edge
  rw [pair.toRetainedIntersectionProfile.mem_sharedEdges_iff,
    Finset.mem_singleton]
  constructor
  · intro hboth
    apply Subtype.ext
    exact (pair.retainedIntersectionExact edge.1).1 hboth
  · intro hedge
    subst edge
    exact (pair.retainedIntersectionExact cross.1).2 rfl

/-- The shared-edge word of an exact cross-central pair has length one. -/
theorem CrossCentralExactFaceCutPair.toRetainedIntersectionProfile_orderLength
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.toRetainedIntersectionProfile.prefixSharedEdgeOrder.length = 1 := by
  rw [RetainedIntersectionExactFaceCutPair.prefixSharedEdgeOrder_length_eq_sharedEdges_card,
    pair.toRetainedIntersectionProfile_sharedEdges, Finset.card_singleton]

/-- The canonical position of the unique retained shared edge. -/
def CrossCentralExactFaceCutPair.singletonSharedPosition
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    Fin pair.toRetainedIntersectionProfile.prefixSharedEdgeOrder.length :=
  ⟨0, by rw [pair.toRetainedIntersectionProfile_orderLength]; omega⟩

/-- The canonical singleton position names the distinguished cross itself. -/
theorem CrossCentralExactFaceCutPair.sharedEdgeAt_singletonSharedPosition
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.toRetainedIntersectionProfile.sharedEdgeAt
        pair.singletonSharedPosition = cross := by
  have hmem :=
    pair.toRetainedIntersectionProfile.sharedEdgeAt_mem_sharedEdges
      pair.singletonSharedPosition
  rw [pair.toRetainedIntersectionProfile_sharedEdges,
    Finset.mem_singleton] at hmem
  exact hmem

/-- Identity signed monodromy on the singleton is precisely agreement of the
two retained traversal darts at the distinguished cross. -/
theorem CrossCentralExactFaceCutPair.singletonSharedDarts_eq_of_signedMonodromy_eq_refl
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hidentity : pair.toRetainedIntersectionProfile.sharedEdgeSignedMonodromy =
      Equiv.refl
        (Fin pair.toRetainedIntersectionProfile.prefixSharedEdgeOrder.length ×
          Bool)) :
    pair.toRetainedIntersectionProfile.suffixSharedEdgeDart
        pair.singletonSharedPosition =
      pair.toRetainedIntersectionProfile.prefixSharedEdgeDart
        pair.singletonSharedPosition :=
  pair.toRetainedIntersectionProfile.suffixSharedEdgeDart_eq_prefixSharedEdgeDart_of_sharedEdgeSignedMonodromy_eq_refl
    hidentity pair.singletonSharedPosition

/-- The finite retained profile underlying one complete exact cut state. -/
abbrev CrossCentralExactFaceCutState.retainedIntersectionProfile
    {graphData : Data G} {data : AdjacentPairData G}
    (state : CrossCentralExactFaceCutState graphData data) :
    RetainedIntersectionExactFaceCutPair graphData data :=
  state.2.toRetainedIntersectionProfile

/-- The complete singleton profile carried by the target of an exact rebase. -/
abbrev CrossCentralExactFaceRebaseStep.targetRetainedIntersectionProfile
    {graphData : Data G} {data : AdjacentPairData G}
    {source : CrossCentralExactFaceCutChannelState graphData data}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    {successors : LocalizedFusionSuccessorResolution source.pair source.face
      firstFusion secondFusion}
    (step : CrossCentralExactFaceRebaseStep graphData data source successors) :
    RetainedIntersectionExactFaceCutPair graphData data :=
  step.targetPair.toRetainedIntersectionProfile

theorem CrossCentralExactFaceRebaseStep.targetRetainedIntersectionProfile_sharedEdges
    {graphData : Data G} {data : AdjacentPairData G}
    {source : CrossCentralExactFaceCutChannelState graphData data}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    {successors : LocalizedFusionSuccessorResolution source.pair source.face
      firstFusion secondFusion}
    (step : CrossCentralExactFaceRebaseStep graphData data source successors) :
    step.targetRetainedIntersectionProfile.sharedEdges = {step.targetCross} :=
  step.targetPair.toRetainedIntersectionProfile_sharedEdges

theorem CrossCentralExactFaceRebaseStep.targetRetainedIntersectionProfile_prefix_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    {source : CrossCentralExactFaceCutChannelState graphData data}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    {successors : LocalizedFusionSuccessorResolution source.pair source.face
      firstFusion secondFusion}
    (step : CrossCentralExactFaceRebaseStep graphData data source successors) :
    step.targetRetainedIntersectionProfile.prefixTrail.IsPath := by
  change step.targetPair.prefixTrail.IsPath
  rw [step.target_prefixTrail]
  exact successors.prefix_isPath

theorem CrossCentralExactFaceRebaseStep.targetRetainedIntersectionProfile_suffix_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    {source : CrossCentralExactFaceCutChannelState graphData data}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    {successors : LocalizedFusionSuccessorResolution source.pair source.face
      firstFusion secondFusion}
    (step : CrossCentralExactFaceRebaseStep graphData data source successors) :
    step.targetRetainedIntersectionProfile.suffixTrail.IsPath := by
  change step.targetPair.suffixTrail.IsPath
  rw [step.target_suffixTrail]
  exact successors.suffix_isPath

/-- Every shared edge of the target singleton profile is a genuinely new
edge on the selected rebase face. -/
theorem CrossCentralExactFaceRebaseStep.targetRetainedIntersectionProfile_localized
    {graphData : Data G} {data : AdjacentPairData G}
    {source : CrossCentralExactFaceCutChannelState graphData data}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    {successors : LocalizedFusionSuccessorResolution source.pair source.face
      firstFusion secondFusion}
    (step : CrossCentralExactFaceRebaseStep graphData data source successors) :
    ∀ edge ∈ step.targetRetainedIntersectionProfile.sharedEdges,
      edge ≠ source.cross ∧
        retainedEdgeToAmbientEdge data edge ∈
          orbitFaceBoundary graphData.toRotationSystem source.face := by
  intro edge hedge
  have hedgeTarget : edge = step.targetCross := by
    rw [step.targetRetainedIntersectionProfile_sharedEdges,
      Finset.mem_singleton] at hedge
    exact hedge
  subst edge
  exact ⟨step.targetCross_ne, step.targetCross_mem_face⟩

/-- A singleton exact rebase has only two signed outcomes.  Its unique shared
edge is aligned in the two route orientations, or reversing it splices the
two routes into a strictly shorter pair of mixed-port cycles.  An order
inversion is impossible on a singleton profile. -/
theorem CrossCentralExactFaceRebaseStep.target_signedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles
    {graphData : Data G} {data : AdjacentPairData G}
    {source : CrossCentralExactFaceCutChannelState graphData data}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    {successors : LocalizedFusionSuccessorResolution source.pair source.face
      firstFusion secondFusion}
    (step : CrossCentralExactFaceRebaseStep graphData data source successors) :
    let pair := step.targetRetainedIntersectionProfile
    pair.sharedEdgeSignedMonodromy =
        Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair source.cross
        source.face) := by
  let pair := step.targetRetainedIntersectionProfile
  have hsingleton : pair.sharedEdges = {step.targetCross} := by
    simpa only [pair] using
      step.targetRetainedIntersectionProfile_sharedEdges
  rcases pair.sharedEdgeSignedMonodromy_eq_refl_or_exists_localizedPathIntervalInversion_or_strictlyShorterMixedPortCycles
      step.targetRetainedIntersectionProfile_prefix_isPath
      step.targetRetainedIntersectionProfile_suffix_isPath source.cross
      source.face step.targetRetainedIntersectionProfile_localized with
    hidentity | hinversion | hshorter
  · exact Or.inl hidentity
  · rcases hinversion with ⟨inversion⟩
    have hfirst : pair.sharedEdgeAt inversion.first = step.targetCross := by
      have hmem := pair.sharedEdgeAt_mem_sharedEdges inversion.first
      rw [hsingleton, Finset.mem_singleton] at hmem
      exact hmem
    have hsecond : pair.sharedEdgeAt inversion.second = step.targetCross := by
      have hmem := pair.sharedEdgeAt_mem_sharedEdges inversion.second
      rw [hsingleton, Finset.mem_singleton] at hmem
      exact hmem
    exact False.elim
      (inversion.first_edge_ne_second_edge (hfirst.trans hsecond.symm))
  · exact Or.inr hshorter

/-- The signed singleton dichotomy with the complete
minimal-counterexample provenance restored. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.target_signedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    let pair := step.target.retainedIntersectionProfile
    pair.sharedEdgeSignedMonodromy =
        Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair source.1
        step.selectedFace) := by
  exact step.rebase.target_signedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles

namespace CrossCentralExactFaceCertifiedRebaseInvolutionCell

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- In the forward direction of an involution cell, the target singleton is
signed-aligned or already supplies strict mixed-port descent. -/
theorem target_signedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    let pair := cell.target.retainedIntersectionProfile
    pair.sharedEdgeSignedMonodromy =
        Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair cell.source.1
        cell.face) := by
  rcases cell.forward with ⟨step, htarget, hface⟩
  rw [← htarget, ← hface]
  exact
    step.target_signedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles

/-- The reverse certified direction gives the symmetric dichotomy at the
source singleton. -/
theorem source_signedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    let pair := cell.source.retainedIntersectionProfile
    pair.sharedEdgeSignedMonodromy =
        Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair cell.target.1
        cell.face) := by
  rcases cell.backward with ⟨step, htarget, hface⟩
  rw [← htarget, ← hface]
  exact
    step.target_signedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles

/-- Both singleton signs in an involution cell are therefore aligned unless
one of its two certified directions already contains strict descent. -/
theorem endpoint_signedMonodromy_normalForm
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    (let pair := cell.source.retainedIntersectionProfile;
      pair.sharedEdgeSignedMonodromy =
          Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ∨
        Nonempty (LocalizedStrictlyShorterMixedPortCycles pair cell.target.1
          cell.face)) ∧
      (let pair := cell.target.retainedIntersectionProfile;
        pair.sharedEdgeSignedMonodromy =
            Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ∨
          Nonempty (LocalizedStrictlyShorterMixedPortCycles pair cell.source.1
            cell.face)) :=
  ⟨cell.source_signedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles,
    cell.target_signedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles⟩

end CrossCentralExactFaceCertifiedRebaseInvolutionCell

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
