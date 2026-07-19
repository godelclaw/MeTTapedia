import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortHybridGluing

/-! The exact one-edge stem and color algebra at an intrinsic-reentry port
overlap. -/

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

/-- A common-core edge regarded as an edge of the source-pair deletion. -/
def commonEdgeInSource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) :
    (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
      collar.sourceData.secondVertex).edgeSet :=
  (deletedTwoPairsToFirstDeletionEmbedding G
    collar.sourceData.firstVertex collar.sourceData.secondVertex
    collar.targetData.firstVertex collar.targetData.secondVertex).mapEdgeSet edge

/-- A common-core edge regarded as an edge of the target-pair deletion. -/
def commonEdgeInTarget
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) :
    (DeletedAdjacentPairGraph G collar.targetData.firstVertex
      collar.targetData.secondVertex).edgeSet :=
  (deletedTwoPairsToSecondDeletionEmbedding G
    collar.sourceData.firstVertex collar.sourceData.secondVertex
    collar.targetData.firstVertex collar.targetData.secondVertex).mapEdgeSet edge

/-- The two deletion embeddings of a common-core edge have the same ambient
edge. -/
theorem retainedEdgeToAmbientEdge_commonEdgeInSource_eq_target
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) :
    retainedEdgeToAmbientEdge collar.sourceData
        (collar.commonEdgeInSource edge) =
      retainedEdgeToAmbientEdge collar.targetData
        (collar.commonEdgeInTarget edge) := by
  apply Subtype.ext
  apply Sym2.ext
  intro vertex
  constructor
  · intro hvertex
    rw [retainedEdgeToAmbientEdge_val] at hvertex
    rcases Sym2.mem_map.mp hvertex with
      ⟨sourceVertex, hsourceVertex, hsourceValue⟩
    change sourceVertex ∈ Sym2.map
      (deletedTwoPairsToFirstDeletionEmbedding G
        collar.sourceData.firstVertex collar.sourceData.secondVertex
        collar.targetData.firstVertex collar.targetData.secondVertex)
      edge.1 at hsourceVertex
    rcases Sym2.mem_map.mp hsourceVertex with
      ⟨commonVertex, hcommonVertex, hcommonSource⟩
    rw [retainedEdgeToAmbientEdge_val]
    apply Sym2.mem_map.mpr
    let targetVertex :=
      (deletedTwoPairsToSecondDeletionEmbedding G
        collar.sourceData.firstVertex collar.sourceData.secondVertex
        collar.targetData.firstVertex collar.targetData.secondVertex)
          commonVertex
    refine ⟨targetVertex, ?_, ?_⟩
    · change targetVertex ∈ Sym2.map
        (deletedTwoPairsToSecondDeletionEmbedding G
          collar.sourceData.firstVertex collar.sourceData.secondVertex
          collar.targetData.firstVertex collar.targetData.secondVertex)
        edge.1
      exact Sym2.mem_map.mpr ⟨commonVertex, hcommonVertex, rfl⟩
    · change commonVertex.1 = vertex
      exact (congrArg Subtype.val hcommonSource).trans hsourceValue
  · intro hvertex
    rw [retainedEdgeToAmbientEdge_val] at hvertex
    rcases Sym2.mem_map.mp hvertex with
      ⟨targetVertex, htargetVertex, htargetValue⟩
    change targetVertex ∈ Sym2.map
      (deletedTwoPairsToSecondDeletionEmbedding G
        collar.sourceData.firstVertex collar.sourceData.secondVertex
        collar.targetData.firstVertex collar.targetData.secondVertex)
      edge.1 at htargetVertex
    rcases Sym2.mem_map.mp htargetVertex with
      ⟨commonVertex, hcommonVertex, hcommonTarget⟩
    rw [retainedEdgeToAmbientEdge_val]
    apply Sym2.mem_map.mpr
    let sourceVertex :=
      (deletedTwoPairsToFirstDeletionEmbedding G
        collar.sourceData.firstVertex collar.sourceData.secondVertex
        collar.targetData.firstVertex collar.targetData.secondVertex)
          commonVertex
    refine ⟨sourceVertex, ?_, ?_⟩
    · change sourceVertex ∈ Sym2.map
        (deletedTwoPairsToFirstDeletionEmbedding G
          collar.sourceData.firstVertex collar.sourceData.secondVertex
          collar.targetData.firstVertex collar.targetData.secondVertex)
        edge.1
      exact Sym2.mem_map.mpr ⟨commonVertex, hcommonVertex, rfl⟩
    · change commonVertex.1 = vertex
      exact (congrArg Subtype.val hcommonTarget).trans htargetValue

/-- The ambient image of a common-core edge is retained by the source
deletion. -/
theorem retainedEdgeToAmbientEdge_commonEdgeInSource_retainedBySource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) :
    IsRetainedAmbientEdge collar.sourceData
      (retainedEdgeToAmbientEdge collar.sourceData
        (collar.commonEdgeInSource edge)) :=
  retainedEdgeToAmbientEdge_isRetainedAmbientEdge collar.sourceData
    (collar.commonEdgeInSource edge)

/-- The same ambient common-core edge is retained by the target deletion. -/
theorem retainedEdgeToAmbientEdge_commonEdgeInSource_retainedByTarget
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) :
    IsRetainedAmbientEdge collar.targetData
      (retainedEdgeToAmbientEdge collar.sourceData
        (collar.commonEdgeInSource edge)) := by
  rw [collar.retainedEdgeToAmbientEdge_commonEdgeInSource_eq_target edge]
  exact retainedEdgeToAmbientEdge_isRetainedAmbientEdge collar.targetData
    (collar.commonEdgeInTarget edge)

/-- A common-core edge incident to a source port remains incident to that
port in the source-pair deletion. -/
theorem commonEdgeInSource_mem_incidentEdgeFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort : Fin 4) (edge : collar.commonCore.edgeSet)
    (hmem : edge ∈ incidentEdgeFinset collar.commonCore
      (collar.sourcePortInCommonCore sourcePort)) :
    collar.commonEdgeInSource edge ∈ incidentEdgeFinset
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex)
      (collar.sourceData.retainedPort sourcePort) := by
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem ⊢
  simp only [commonEdgeInSource, SimpleGraph.Embedding.mapEdgeSet]
  apply Sym2.mem_map.mpr
  exact ⟨collar.sourcePortInCommonCore sourcePort, hmem, Subtype.ext rfl⟩

/-- A common-core edge incident to a target port remains incident to that
port in the target-pair deletion. -/
theorem commonEdgeInTarget_mem_incidentEdgeFinset
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) (edge : collar.commonCore.edgeSet)
    (hmem : edge ∈ incidentEdgeFinset collar.commonCore
      (collar.targetPortInCommonCore targetPort)) :
    collar.commonEdgeInTarget edge ∈ incidentEdgeFinset
      (DeletedAdjacentPairGraph G collar.targetData.firstVertex
        collar.targetData.secondVertex)
      (collar.targetData.retainedPort targetPort) := by
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem ⊢
  simp only [commonEdgeInTarget, SimpleGraph.Embedding.mapEdgeSet]
  apply Sym2.mem_map.mpr
  exact ⟨collar.targetPortInCommonCore targetPort, hmem, Subtype.ext rfl⟩

/-- At a literal overlap, the target and source boundary edges meet at the
common port vertex. -/
theorem targetBoundaryEdge_adj_sourceBoundaryEdge_of_portOverlap
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort targetPort : Fin 4)
    (hoverlap : collar.PortOverlap sourcePort targetPort) :
    G.lineGraph.Adj
      (boundaryEdge collar.targetData targetPort)
      (boundaryEdge collar.sourceData sourcePort) := by
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨?_, collar.sourceData.portVertex sourcePort, ?_, ?_⟩
  · intro heq
    have hnotRetained :
        ¬ IsRetainedAmbientEdge collar.sourceData
          (boundaryEdge collar.sourceData sourcePort) :=
      (not_isRetainedAmbientEdge_iff collar.sourceData
        (boundaryEdge collar.sourceData sourcePort)).2
          (Or.inr ⟨sourcePort, boundaryEdge_val _ _⟩)
    have hretained := collar.targetBoundaryRetainedBySource targetPort
    rw [heq] at hretained
    exact hnotRetained hretained
  · rw [boundaryEdge_val, boundaryEdgeValue_eq, hoverlap]
    exact Sym2.mem_mk_right _ _
  · rw [boundaryEdge_val, boundaryEdgeValue_eq]
    exact Sym2.mem_mk_right _ _

/-- At an overlap, the target boundary edge is one of the two edges incident
to the source defect vertex in the source deletion. -/
theorem targetBoundaryInSource_mem_incidentEdgeFinset_of_portOverlap
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort targetPort : Fin 4)
    (hoverlap : collar.PortOverlap sourcePort targetPort) :
    collar.targetBoundaryInSource targetPort ∈ incidentEdgeFinset
      (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex)
      (collar.sourceData.retainedPort sourcePort) := by
  exact ambientEdgeToRetainedEdge_mem_incident_of_adj_boundaryEdge
    collar.sourceData (boundaryEdge collar.targetData targetPort)
      (collar.targetBoundaryRetainedBySource targetPort) sourcePort
        (collar.targetBoundaryEdge_adj_sourceBoundaryEdge_of_portOverlap
          sourcePort targetPort hoverlap)

/-- Symmetrically, the source boundary edge is incident to the target defect
vertex in the target deletion. -/
theorem sourceBoundaryInTarget_mem_incidentEdgeFinset_of_portOverlap
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort targetPort : Fin 4)
    (hoverlap : collar.PortOverlap sourcePort targetPort) :
    collar.sourceBoundaryInTarget sourcePort ∈ incidentEdgeFinset
      (DeletedAdjacentPairGraph G collar.targetData.firstVertex
        collar.targetData.secondVertex)
      (collar.targetData.retainedPort targetPort) := by
  exact ambientEdgeToRetainedEdge_mem_incident_of_adj_boundaryEdge
    collar.targetData (boundaryEdge collar.sourceData sourcePort)
      (collar.sourceBoundaryRetainedByTarget sourcePort) targetPort
        (collar.targetBoundaryEdge_adj_sourceBoundaryEdge_of_portOverlap
          sourcePort targetPort hoverlap).symm

/-- A common-core edge cannot be the target boundary edge removed by the
target deletion. -/
theorem commonEdgeInSource_ne_targetBoundaryInSource
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) (targetPort : Fin 4) :
    collar.commonEdgeInSource edge ≠
      collar.targetBoundaryInSource targetPort := by
  intro heq
  have hambient :
      retainedEdgeToAmbientEdge collar.sourceData
          (collar.commonEdgeInSource edge) =
        boundaryEdge collar.targetData targetPort := by
    calc
      retainedEdgeToAmbientEdge collar.sourceData
          (collar.commonEdgeInSource edge) =
          retainedEdgeToAmbientEdge collar.sourceData
            (collar.targetBoundaryInSource targetPort) := by rw [heq]
      _ = boundaryEdge collar.targetData targetPort := by
        exact retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge
          collar.sourceData (boundaryEdge collar.targetData targetPort)
            (collar.targetBoundaryRetainedBySource targetPort)
  have hretained :=
    collar.retainedEdgeToAmbientEdge_commonEdgeInSource_retainedByTarget edge
  rw [hambient] at hretained
  exact (not_isRetainedAmbientEdge_iff collar.targetData
    (boundaryEdge collar.targetData targetPort)).2
      (Or.inr ⟨targetPort, boundaryEdge_val _ _⟩) hretained

/-- Symmetrically, a common-core edge cannot be the source boundary edge
removed by the source deletion. -/
theorem commonEdgeInTarget_ne_sourceBoundaryInTarget
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) (sourcePort : Fin 4) :
    collar.commonEdgeInTarget edge ≠
      collar.sourceBoundaryInTarget sourcePort := by
  intro heq
  have hambient :
      retainedEdgeToAmbientEdge collar.targetData
          (collar.commonEdgeInTarget edge) =
        boundaryEdge collar.sourceData sourcePort := by
    calc
      retainedEdgeToAmbientEdge collar.targetData
          (collar.commonEdgeInTarget edge) =
          retainedEdgeToAmbientEdge collar.targetData
            (collar.sourceBoundaryInTarget sourcePort) := by rw [heq]
      _ = boundaryEdge collar.sourceData sourcePort := by
        exact retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge
          collar.targetData (boundaryEdge collar.sourceData sourcePort)
            (collar.sourceBoundaryRetainedByTarget sourcePort)
  have hretained :=
    collar.retainedEdgeToAmbientEdge_commonEdgeInSource_retainedBySource edge
  rw [collar.retainedEdgeToAmbientEdge_commonEdgeInSource_eq_target edge,
    hambient] at hretained
  exact (not_isRetainedAmbientEdge_iff collar.sourceData
    (boundaryEdge collar.sourceData sourcePort)).2
      (Or.inr ⟨sourcePort, boundaryEdge_val _ _⟩) hretained

/-- A literal port overlap has one exact common-core stem edge. -/
theorem exists_commonEdge_incident_eq_singleton_of_portOverlap
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort targetPort : Fin 4)
    (hoverlap : collar.PortOverlap sourcePort targetPort) :
    ∃ edge : collar.commonCore.edgeSet,
      incidentEdgeFinset collar.commonCore
        (collar.sourcePortInCommonCore sourcePort) = {edge} := by
  apply Finset.card_eq_one.mp
  rw [collar.card_incidentEdgeFinset_sourcePortInCommonCore sourcePort,
    if_pos ⟨targetPort, hoverlap⟩]

/-- Pointwise agreement on every ambient edge retained by both deletions
implies equality of the two exact common-core restrictions. -/
theorem sourceCommonColoring_eq_targetCommonColoring_of_commonAgreement
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
    collar.sourceCommonColoring sourceEscape =
      collar.targetCommonColoring := by
  apply DFunLike.ext _ _
  intro edge
  let ambientEdge := retainedEdgeToAmbientEdge collar.sourceData
    (collar.commonEdgeInSource edge)
  have hsource : IsRetainedAmbientEdge collar.sourceData ambientEdge :=
    collar.retainedEdgeToAmbientEdge_commonEdgeInSource_retainedBySource edge
  have htarget : IsRetainedAmbientEdge collar.targetData ambientEdge :=
    collar.retainedEdgeToAmbientEdge_commonEdgeInSource_retainedByTarget edge
  have htargetEdge :
      ambientEdgeToRetainedEdge collar.targetData ambientEdge htarget =
        collar.commonEdgeInTarget edge := by
    apply collar.targetData.retainedEdgeToAmbientEdge_injective
    calc
      retainedEdgeToAmbientEdge collar.targetData
          (ambientEdgeToRetainedEdge collar.targetData ambientEdge htarget) =
          ambientEdge := by
            exact retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge
              collar.targetData ambientEdge htarget
      _ = retainedEdgeToAmbientEdge collar.targetData
          (collar.commonEdgeInTarget edge) :=
        collar.retainedEdgeToAmbientEdge_commonEdgeInSource_eq_target edge
  have hvalue := hcommon ambientEdge hsource htarget
  change sourceEscape.coloring (collar.commonEdgeInSource edge) =
    collar.targetEscape.coloring (collar.commonEdgeInTarget edge)
  rw [htargetEdge] at hvalue
  simpa only [ambientEdge,
    ambientEdgeToRetainedEdge_retainedEdgeToAmbientEdge] using hvalue

/-- Equality of the two exact common-core restrictions is pointwise equality
on the two deletion images of every common edge. -/
theorem commonEdge_color_eq_of_commonColoring_eq
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
    (edge : collar.commonCore.edgeSet) :
    sourceEscape.coloring (collar.commonEdgeInSource edge) =
      collar.targetEscape.coloring (collar.commonEdgeInTarget edge) := by
  have hvalue := congrArg (fun coloring => coloring edge) hcommon
  exact hvalue

/-- At a conflicting overlap over equal common-core colorings, the source
and target own boundary requests are the same third color. -/
theorem ownBoundaryWord_eq_of_commonColoring_eq_of_conflictingPortOverlap
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
    (sourcePort targetPort : Fin 4)
    (hoverlap : collar.PortOverlap sourcePort targetPort)
    (hconflict : collar.targetEscape.coloring
          (collar.sourceBoundaryInTarget sourcePort) =
        sourceEscape.coloring
          (collar.targetBoundaryInSource targetPort)) :
    collar.sourceData.degreeTwoBoundaryData.colorWord
        sourceEscape.coloring sourcePort =
      collar.targetData.degreeTwoBoundaryData.colorWord
        collar.targetEscape.coloring targetPort := by
  classical
  rcases collar.exists_commonEdge_incident_eq_singleton_of_portOverlap
      sourcePort targetPort hoverlap with ⟨commonEdge, hcommonIncident⟩
  have hcommonSource : collar.commonEdgeInSource commonEdge ∈
      incidentEdgeFinset
        (DeletedAdjacentPairGraph G collar.sourceData.firstVertex
          collar.sourceData.secondVertex)
        (collar.sourceData.retainedPort sourcePort) :=
    collar.commonEdgeInSource_mem_incidentEdgeFinset sourcePort commonEdge
      (by
        rw [hcommonIncident]
        exact Finset.mem_singleton_self commonEdge)
  have hportCommon :
      collar.sourcePortInCommonCore sourcePort =
        collar.targetPortInCommonCore targetPort :=
    (collar.sourcePortInCommonCore_eq_targetPortInCommonCore_iff
      sourcePort targetPort).2 hoverlap
  have hcommonTarget : collar.commonEdgeInTarget commonEdge ∈
      incidentEdgeFinset
        (DeletedAdjacentPairGraph G collar.targetData.firstVertex
          collar.targetData.secondVertex)
        (collar.targetData.retainedPort targetPort) :=
    collar.commonEdgeInTarget_mem_incidentEdgeFinset targetPort commonEdge
      (by
        rw [← hportCommon, hcommonIncident]
        exact Finset.mem_singleton_self commonEdge)
  have htargetBoundary :=
    collar.targetBoundaryInSource_mem_incidentEdgeFinset_of_portOverlap
      sourcePort targetPort hoverlap
  have hsourceBoundary :=
    collar.sourceBoundaryInTarget_mem_incidentEdgeFinset_of_portOverlap
      sourcePort targetPort hoverlap
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hsourceWell :=
    collar.sourceData.degreeTwoBoundaryData_wellFormed hcubic
  have htargetWell :=
    collar.targetData.degreeTwoBoundaryData_wellFormed hcubic
  let sourceWord :=
    collar.sourceData.degreeTwoBoundaryData.colorWord
      sourceEscape.coloring sourcePort
  let targetWord :=
    collar.targetData.degreeTwoBoundaryData.colorWord
      collar.targetEscape.coloring targetPort
  let commonSourceColor :=
    sourceEscape.coloring (collar.commonEdgeInSource commonEdge)
  let boundarySourceColor :=
    sourceEscape.coloring (collar.targetBoundaryInSource targetPort)
  have hcommonColor :=
    collar.commonEdge_color_eq_of_commonColoring_eq
      sourceEscape hcommon commonEdge
  have hsourceWordNonzero : sourceWord ≠ 0 :=
    collar.sourceData.degreeTwoBoundaryData.colorWord_ne_zero
      hsourceWell sourceEscape.coloring sourcePort
  have htargetWordNonzero : targetWord ≠ 0 :=
    collar.targetData.degreeTwoBoundaryData.colorWord_ne_zero
      htargetWell collar.targetEscape.coloring targetPort
  have hcommonSourceNonzero : commonSourceColor ≠ 0 :=
    sourceEscape.isTait _
  have hboundarySourceNonzero : boundarySourceColor ≠ 0 :=
    sourceEscape.isTait _
  have hcommonSourceVertex : collar.sourceData.retainedPort sourcePort ∈
      (collar.commonEdgeInSource commonEdge).1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hcommonSource
  have htargetBoundaryVertex : collar.sourceData.retainedPort sourcePort ∈
      (collar.targetBoundaryInSource targetPort).1 := by
    simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using htargetBoundary
  have hcommonBoundarySource : commonSourceColor ≠ boundarySourceColor := by
    exact sourceEscape.coloring.valid
      ((DeletedAdjacentPairGraph G collar.sourceData.firstVertex
        collar.sourceData.secondVertex).lineGraph_adj_of_edgeSet_common_vertex
          (collar.commonEdgeInSource_ne_targetBoundaryInSource
            commonEdge targetPort)
          hcommonSourceVertex htargetBoundaryVertex)
  have hsourceWordCommon : sourceWord ≠ commonSourceColor :=
    collar.sourceData.degreeTwoBoundaryData.colorWord_ne_incidentColor
      hsourceWell sourceEscape.coloring sourceEscape.isTait sourcePort
        (collar.commonEdgeInSource commonEdge) hcommonSource
  have hsourceWordBoundary : sourceWord ≠ boundarySourceColor :=
    collar.sourceData.degreeTwoBoundaryData.colorWord_ne_incidentColor
      hsourceWell sourceEscape.coloring sourceEscape.isTait sourcePort
        (collar.targetBoundaryInSource targetPort) htargetBoundary
  have htargetWordCommon : targetWord ≠ commonSourceColor := by
    intro heq
    apply collar.targetData.degreeTwoBoundaryData.colorWord_ne_incidentColor
      htargetWell collar.targetEscape.coloring collar.targetEscape.isTait
        targetPort (collar.commonEdgeInTarget commonEdge) hcommonTarget
    exact heq.trans hcommonColor
  have htargetWordBoundary : targetWord ≠ boundarySourceColor := by
    intro heq
    apply collar.targetData.degreeTwoBoundaryData.colorWord_ne_incidentColor
      htargetWell collar.targetEscape.coloring collar.targetEscape.isTait
        targetPort (collar.sourceBoundaryInTarget sourcePort) hsourceBoundary
    exact heq.trans hconflict.symm
  exact color_eq_of_two_distinct_nonzero_exclusions
    hsourceWordNonzero htargetWordNonzero hcommonSourceNonzero
      hboundarySourceNonzero hcommonBoundarySource
      hsourceWordCommon hsourceWordBoundary
      htargetWordCommon htargetWordBoundary

/-- Under common-edge agreement, minimality supplies one exact overlap at
which both cross-collar colors and both own missing-color requests agree. -/
theorem exists_conflictingPortOverlap_with_equal_ownBoundaryWord_of_commonAgreement
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
            (collar.targetBoundaryInSource targetPort) ∧
        collar.sourceData.degreeTwoBoundaryData.colorWord
            sourceEscape.coloring sourcePort =
          collar.targetData.degreeTwoBoundaryData.colorWord
            collar.targetEscape.coloring targetPort := by
  have hcommonCore :=
    collar.sourceCommonColoring_eq_targetCommonColoring_of_commonAgreement
      sourceEscape hcommon
  rcases collar.exists_conflictingPortOverlap_of_commonAgreement
      sourceEscape hcommon with
    ⟨sourcePort, targetPort, hoverlap, hconflict⟩
  exact ⟨sourcePort, targetPort, hoverlap, hconflict,
    collar.ownBoundaryWord_eq_of_commonColoring_eq_of_conflictingPortOverlap
      sourceEscape hcommonCore sourcePort targetPort hoverlap hconflict⟩

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
