import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionPrimalTrail

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

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

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {start : sourceNormal.KempeOrbitAdjacentEscape}

namespace CompanionCrossPairFusionPrimalTrail

variable (fusion : CompanionCrossPairFusionPrimalTrail collar start)

/-- Every edge of the ambient fusion trail survives deletion of the target
adjacent pair. -/
def TargetCollarAvoiding : Prop :=
  ∀ edge : G.edgeSet, edge.1 ∈ fusion.ambientTrail.edges →
    IsRetainedAmbientEdge collar.targetData edge

end CompanionCrossPairFusionPrimalTrail

/-- A cross-pair fusion trail transported verbatim into the target
adjacent-pair deletion. -/
structure CompanionCrossPairFusionTargetTransport
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  fusion : CompanionCrossPairFusionPrimalTrail collar start
  start_mem : fusion.startVertex.1 ∈
    retainedVertexSet collar.targetData.firstVertex
      collar.targetData.secondVertex
  end_mem : fusion.endVertex.1 ∈
    retainedVertexSet collar.targetData.firstVertex
      collar.targetData.secondVertex
  targetTrail :
    (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).Walk
        ⟨fusion.startVertex.1, start_mem⟩
        ⟨fusion.endVertex.1, end_mem⟩
  targetTrail_isTrail : targetTrail.IsTrail
  ambient_eq : collar.targetData.retainedWalkToAmbient targetTrail =
    fusion.ambientTrail

/-- The exact finite obstruction to target transport: the fusion trail
uses the target central edge or one of its four boundary edges. -/
structure CompanionCrossPairFusionTargetCollarContact
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (start : sourceNormal.KempeOrbitAdjacentEscape) where
  fusion : CompanionCrossPairFusionPrimalTrail collar start
  contactEdge : G.edgeSet
  contactEdge_mem : contactEdge.1 ∈ fusion.ambientTrail.edges
  central_or_boundary : contactEdge = centralEdge collar.targetData ∨
    ∃ port : Fin 4, contactEdge = boundaryEdge collar.targetData port

namespace CompanionCrossPairFusionPrimalTrail

variable (fusion : CompanionCrossPairFusionPrimalTrail collar start)

/-- A target-collar-avoiding fusion trail induces an exact edge-simple
trail in the target deletion. -/
theorem nonempty_targetTransport_of_targetCollarAvoiding
    (avoiding : fusion.TargetCollarAvoiding) :
    Nonempty (CompanionCrossPairFusionTargetTransport collar start) := by
  have supportRetained : ∀ vertex ∈ fusion.ambientTrail.support,
      vertex ∈ retainedVertexSet collar.targetData.firstVertex
        collar.targetData.secondVertex := by
    intro vertex vertex_mem
    rcases (fusion.ambientTrail.mem_support_iff_exists_mem_edges_of_not_nil
        fusion.ambientTrail_not_nil).1 vertex_mem with
      ⟨edgeValue, edge_mem, vertex_mem_edge⟩
    let edge : G.edgeSet :=
      ⟨edgeValue, fusion.ambientTrail.edges_subset_edgeSet edge_mem⟩
    exact endpoints_mem_retainedVertexSet collar.targetData edge
      (avoiding edge edge_mem) vertex vertex_mem_edge
  let targetTrail := fusion.ambientTrail.induce
    (retainedVertexSet collar.targetData.firstVertex
      collar.targetData.secondVertex) supportRetained
  have targetTrail_isTrail : targetTrail.IsTrail := by
    let embedding := SimpleGraph.Embedding.induce
      (G := G) (retainedVertexSet collar.targetData.firstVertex
        collar.targetData.secondVertex)
    have mapped : (targetTrail.map embedding.toHom).IsTrail := by
      rw [SimpleGraph.Walk.map_induce]
      exact fusion.ambientTrail_isTrail
    exact (SimpleGraph.Walk.map_isTrail_iff_of_injective
      (p := targetTrail) (f := embedding.toHom) embedding.injective).1 mapped
  refine ⟨{
    fusion := fusion
    start_mem := supportRetained fusion.startVertex.1
      fusion.ambientTrail.start_mem_support
    end_mem := supportRetained fusion.endVertex.1
      fusion.ambientTrail.end_mem_support
    targetTrail := targetTrail
    targetTrail_isTrail := targetTrail_isTrail
    ambient_eq := ?_ }⟩
  change targetTrail.map
    (SimpleGraph.Embedding.induce
      (retainedVertexSet collar.targetData.firstVertex
        collar.targetData.secondVertex)).toHom = fusion.ambientTrail
  exact SimpleGraph.Walk.map_induce fusion.ambientTrail supportRetained

include fusion in
/-- Every fusion trail either transports exactly to the target deletion or
meets one of the five explicit target-collar edges. -/
theorem nonempty_targetTransport_or_targetCollarContact :
    Nonempty (CompanionCrossPairFusionTargetTransport collar start) ∨
      Nonempty (CompanionCrossPairFusionTargetCollarContact collar start) := by
  classical
  by_cases avoiding :
      CompanionCrossPairFusionPrimalTrail.TargetCollarAvoiding fusion
  · exact Or.inl
      (CompanionCrossPairFusionPrimalTrail.nonempty_targetTransport_of_targetCollarAvoiding
        fusion avoiding)
  · rw [CompanionCrossPairFusionPrimalTrail.TargetCollarAvoiding] at avoiding
    push Not at avoiding
    rcases avoiding with ⟨contactEdge, contactEdge_mem, notRetained⟩
    apply Or.inr
    refine ⟨{
      fusion := fusion
      contactEdge := contactEdge
      contactEdge_mem := contactEdge_mem
      central_or_boundary := ?_ }⟩
    rcases (not_isRetainedAmbientEdge_iff collar.targetData contactEdge).1
        notRetained with central | ⟨port, boundary⟩
    · exact Or.inl (Subtype.ext central)
    · exact Or.inr ⟨port, Subtype.ext boundary⟩

end CompanionCrossPairFusionPrimalTrail

/-- The cross-pair branch of a closed circuit separates into exact target
transport and an explicit five-edge collar contact. -/
theorem closedCircuit_exists_localCancellation_or_fusionTargetTransport_or_fusionTargetCollarContact_or_edgePivot_or_threePairMonodromy
    (closed : Relation.TransGen
      (CompanionAdjacentEscapeTransition collar) start start) :
    Nonempty (CompanionCanonicalComponentDisjointClosure collar start) ∨
      Nonempty (CompanionCrossPairFusionTargetTransport collar start) ∨
        Nonempty (CompanionCrossPairFusionTargetCollarContact collar start) ∨
          Nonempty (CompanionSameOuterTargetAvoidingEdgePivot collar start) ∨
            Nonempty (CompanionThreePairMonodromy collar start) := by
  rcases
      closedCircuit_exists_localCancellation_or_fusionPrimalTrail_or_edgePivot_or_threePairMonodromy
        closed with cancellation | fusion | pivot | monodromy
  · exact Or.inl cancellation
  · rcases fusion with ⟨fusion⟩
    rcases
        CompanionCrossPairFusionPrimalTrail.nonempty_targetTransport_or_targetCollarContact
          fusion with transport | contact
    · exact Or.inr (Or.inl transport)
    · exact Or.inr (Or.inr (Or.inl contact))
  · exact Or.inr (Or.inr (Or.inr (Or.inl pivot)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr monodromy)))

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
