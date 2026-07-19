import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortEscapeCollar

/-! The exact eight-port boundary shared by the source and intrinsic target
adjacent-pair deletions. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualCycleCollar
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

/-- An endpoint of a remote crossing edge is not adjacent to the first
deleted source vertex. -/
theorem crossingEdge_endpoint_not_adjacent_firstVertex
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {edge : G.edgeSet} (hcrossing : edge ∈ cycle.crossingEdges)
    {vertex : V} (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    ¬ G.Adj vertex
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex := by
  intro hadjacent
  let data := RecoveredRotationOrderedData graphData minimal baseData
  let incident : G.edgeSet :=
    ⟨s(vertex, data.firstVertex), hadjacent⟩
  have hedgeRetained : IsRetainedAmbientEdge data edge := by
    apply isRetainedAmbientEdge_of_ne_central_boundary data edge
    · exact cycle.crossingEdge_ne_central hcrossing
    · intro port
      simpa [data, RecoveredRotationOrderedData] using
        cycle.crossingEdge_ne_boundary hcrossing port
  have hfirstNotEndpoint : data.firstVertex ∉ (edge.1 : Sym2 V) := by
    intro hfirst
    exact (endpoints_mem_retainedVertexSet data edge hedgeRetained
      data.firstVertex hfirst).1 rfl
  have hne : edge ≠ incident := by
    intro heq
    apply hfirstNotEndpoint
    rw [heq]
    exact Sym2.mem_mk_right _ _
  have hincidentVertex : vertex ∈
      graphData.toRotationSystem.endpoints incident :=
    (mem_simpleGraphRotationSystem_endpoints_iff graphData incident vertex).2
      (Sym2.mem_mk_left _ _)
  have hedgeVertex : vertex ∈
      graphData.toRotationSystem.endpoints edge :=
    (mem_simpleGraphRotationSystem_endpoints_iff graphData edge vertex).2
      hvertex
  rcases graphData.toRotationSystem.exists_common_orbitFace_of_distinct_incident_edges
      minimal.spherical.cubic minimal.vertexRotationCyclic hne
        hedgeVertex hincidentVertex with
    ⟨face, hedgeFace, hincidentFace⟩
  have hsupport :
      (⟨face, Finset.mem_univ face⟩ : AmbientFace
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))) ∈ cycle.walk.support :=
    face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
        cycle.walk hcrossing hedgeFace
  have hfirstMem : data.firstVertex ∈ (incident.1 : Sym2 V) := by
    exact Sym2.mem_mk_right _ _
  rcases edge_eq_central_or_firstPort_of_mem data incident hfirstMem with
    hcentral | hzero | hone
  · apply cycle.central_not_mem
      ⟨face, Finset.mem_univ face⟩ hsupport
    have heq : centralEdge data = incident := by
      apply Subtype.ext
      rw [centralEdge_val, centralEdgeValue]
      exact hcentral.symm
    exact heq ▸ hincidentFace
  · apply cycle.boundary_not_mem
      ⟨face, Finset.mem_univ face⟩ hsupport 0
    have heq : boundaryEdge data 0 = incident := by
      apply Subtype.ext
      rw [boundaryEdge_val, boundaryEdgeValue_eq]
      exact hzero.symm
    exact heq ▸ hincidentFace
  · apply cycle.boundary_not_mem
      ⟨face, Finset.mem_univ face⟩ hsupport 1
    have heq : boundaryEdge data 1 = incident := by
      apply Subtype.ext
      rw [boundaryEdge_val, boundaryEdgeValue_eq]
      exact hone.symm
    exact heq ▸ hincidentFace

/-- An endpoint of a remote crossing edge is not adjacent to the second
deleted source vertex. -/
theorem crossingEdge_endpoint_not_adjacent_secondVertex
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {edge : G.edgeSet} (hcrossing : edge ∈ cycle.crossingEdges)
    {vertex : V} (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    ¬ G.Adj vertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex := by
  intro hadjacent
  let data := RecoveredRotationOrderedData graphData minimal baseData
  let incident : G.edgeSet :=
    ⟨s(vertex, data.secondVertex), hadjacent⟩
  have hedgeRetained : IsRetainedAmbientEdge data edge := by
    apply isRetainedAmbientEdge_of_ne_central_boundary data edge
    · exact cycle.crossingEdge_ne_central hcrossing
    · intro port
      simpa [data, RecoveredRotationOrderedData] using
        cycle.crossingEdge_ne_boundary hcrossing port
  have hsecondNotEndpoint : data.secondVertex ∉ (edge.1 : Sym2 V) := by
    intro hsecond
    exact (endpoints_mem_retainedVertexSet data edge hedgeRetained
      data.secondVertex hsecond).2 rfl
  have hne : edge ≠ incident := by
    intro heq
    apply hsecondNotEndpoint
    rw [heq]
    exact Sym2.mem_mk_right _ _
  have hincidentVertex : vertex ∈
      graphData.toRotationSystem.endpoints incident :=
    (mem_simpleGraphRotationSystem_endpoints_iff graphData incident vertex).2
      (Sym2.mem_mk_left _ _)
  have hedgeVertex : vertex ∈
      graphData.toRotationSystem.endpoints edge :=
    (mem_simpleGraphRotationSystem_endpoints_iff graphData edge vertex).2
      hvertex
  rcases graphData.toRotationSystem.exists_common_orbitFace_of_distinct_incident_edges
      minimal.spherical.cubic minimal.vertexRotationCyclic hne
        hedgeVertex hincidentVertex with
    ⟨face, hedgeFace, hincidentFace⟩
  have hsupport :
      (⟨face, Finset.mem_univ face⟩ : AmbientFace
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))) ∈ cycle.walk.support :=
    face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
        cycle.walk hcrossing hedgeFace
  have hsecondMem : data.secondVertex ∈ (incident.1 : Sym2 V) := by
    exact Sym2.mem_mk_right _ _
  rcases edge_eq_central_or_secondPort_of_mem data incident hsecondMem with
    hcentral | htwo | hthree
  · apply cycle.central_not_mem
      ⟨face, Finset.mem_univ face⟩ hsupport
    have heq : centralEdge data = incident := by
      apply Subtype.ext
      rw [centralEdge_val, centralEdgeValue]
      exact hcentral.symm
    exact heq ▸ hincidentFace
  · apply cycle.boundary_not_mem
      ⟨face, Finset.mem_univ face⟩ hsupport 2
    have heq : boundaryEdge data 2 = incident := by
      apply Subtype.ext
      rw [boundaryEdge_val, boundaryEdgeValue_eq]
      exact htwo.symm
    exact heq ▸ hincidentFace
  · apply cycle.boundary_not_mem
      ⟨face, Finset.mem_univ face⟩ hsupport 3
    have heq : boundaryEdge data 3 = incident := by
      apply Subtype.ext
      rw [boundaryEdge_val, boundaryEdgeValue_eq]
      exact hthree.symm
    exact heq ▸ hincidentFace

namespace IntrinsicShortTargetEscapeCollar

/-- The first target vertex is an endpoint of the retained crossing edge. -/
theorem targetFirst_mem_targetEdge
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.targetData.firstVertex ∈ (targetEdge.1 : Sym2 V) := by
  have hvalue := congrArg Subtype.val collar.targetCentral_eq
  rw [centralEdge_val, centralEdgeValue] at hvalue
  rw [← hvalue]
  exact Sym2.mem_mk_left _ _

/-- The second target vertex is an endpoint of the retained crossing edge. -/
theorem targetSecond_mem_targetEdge
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.targetData.secondVertex ∈ (targetEdge.1 : Sym2 V) := by
  have hvalue := congrArg Subtype.val collar.targetCentral_eq
  rw [centralEdge_val, centralEdgeValue] at hvalue
  rw [← hvalue]
  exact Sym2.mem_mk_right _ _

/-- The first target vertex survives the source deletion. -/
theorem targetFirst_mem_sourceRetainedVertexSet
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.targetData.firstVertex ∈
      retainedVertexSet collar.sourceData.firstVertex
        collar.sourceData.secondVertex :=
  endpoints_mem_retainedVertexSet collar.sourceData targetEdge
    collar.targetRetainedBySource collar.targetData.firstVertex
      collar.targetFirst_mem_targetEdge

/-- The second target vertex survives the source deletion. -/
theorem targetSecond_mem_sourceRetainedVertexSet
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.targetData.secondVertex ∈
      retainedVertexSet collar.sourceData.firstVertex
        collar.sourceData.secondVertex :=
  endpoints_mem_retainedVertexSet collar.sourceData targetEdge
    collar.targetRetainedBySource collar.targetData.secondVertex
      collar.targetSecond_mem_targetEdge

/-- The intrinsic target pair is anticomplete to the deleted source pair.
This is stronger than mere vertex-disjointness. -/
theorem targetPair_anticomplete_sourcePair
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    (¬ G.Adj collar.targetData.firstVertex
        collar.sourceData.firstVertex) ∧
      (¬ G.Adj collar.targetData.firstVertex
        collar.sourceData.secondVertex) ∧
      (¬ G.Adj collar.targetData.secondVertex
        collar.sourceData.firstVertex) ∧
      (¬ G.Adj collar.targetData.secondVertex
        collar.sourceData.secondVertex) := by
  exact ⟨
    cycle.crossingEdge_endpoint_not_adjacent_firstVertex
      collar.targetCrossing collar.targetFirst_mem_targetEdge,
    cycle.crossingEdge_endpoint_not_adjacent_secondVertex
      collar.targetCrossing collar.targetFirst_mem_targetEdge,
    cycle.crossingEdge_endpoint_not_adjacent_firstVertex
      collar.targetCrossing collar.targetSecond_mem_targetEdge,
    cycle.crossingEdge_endpoint_not_adjacent_secondVertex
      collar.targetCrossing collar.targetSecond_mem_targetEdge⟩

/-- Every target port survives deletion of the source pair. -/
theorem targetPort_mem_sourceRetainedVertexSet
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (port : Fin 4) :
    collar.targetData.portVertex port ∈
      retainedVertexSet collar.sourceData.firstVertex
        collar.sourceData.secondVertex := by
  have hseparated := collar.targetPair_anticomplete_sourcePair
  constructor
  · intro heq
    fin_cases port
    · exact hseparated.1
        (heq ▸ collar.targetData.first_adj_port_zero)
    · exact hseparated.1
        (heq ▸ collar.targetData.first_adj_port_one)
    · exact hseparated.2.2.1
        (heq ▸ collar.targetData.second_adj_port_two)
    · exact hseparated.2.2.1
        (heq ▸ collar.targetData.second_adj_port_three)
  · intro heq
    fin_cases port
    · exact hseparated.2.1
        (heq ▸ collar.targetData.first_adj_port_zero)
    · exact hseparated.2.1
        (heq ▸ collar.targetData.first_adj_port_one)
    · exact hseparated.2.2.2
        (heq ▸ collar.targetData.second_adj_port_two)
    · exact hseparated.2.2.2
        (heq ▸ collar.targetData.second_adj_port_three)

/-- Every source port survives deletion of the target pair. -/
theorem sourcePort_mem_targetRetainedVertexSet
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (port : Fin 4) :
    collar.sourceData.portVertex port ∈
      retainedVertexSet collar.targetData.firstVertex
        collar.targetData.secondVertex := by
  apply endpoints_mem_retainedVertexSet collar.targetData
    (boundaryEdge collar.sourceData port)
      (collar.sourceBoundaryRetainedByTarget port)
        (collar.sourceData.portVertex port)
  rw [boundaryEdge_val, boundaryEdgeValue_eq]
  exact Sym2.mem_mk_right _ _

/-- The first source vertex survives the target deletion. -/
theorem sourceFirst_mem_targetRetainedVertexSet
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.sourceData.firstVertex ∈
      retainedVertexSet collar.targetData.firstVertex
        collar.targetData.secondVertex := by
  apply endpoints_mem_retainedVertexSet collar.targetData
    (centralEdge collar.sourceData) collar.sourceCentralRetainedByTarget
      collar.sourceData.firstVertex
  rw [centralEdge_val, centralEdgeValue]
  exact Sym2.mem_mk_left _ _

/-- The second source vertex survives the target deletion. -/
theorem sourceSecond_mem_targetRetainedVertexSet
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.sourceData.secondVertex ∈
      retainedVertexSet collar.targetData.firstVertex
        collar.targetData.secondVertex := by
  apply endpoints_mem_retainedVertexSet collar.targetData
    (centralEdge collar.sourceData) collar.sourceCentralRetainedByTarget
      collar.sourceData.secondVertex
  rw [centralEdge_val, centralEdgeValue]
  exact Sym2.mem_mk_right _ _

/-- The vertex carrier common to the two adjacent-pair deletions. -/
abbrev commonCoreVertex
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :=
  {vertex : V |
    vertex ≠ collar.sourceData.firstVertex ∧
      vertex ≠ collar.sourceData.secondVertex ∧
        vertex ≠ collar.targetData.firstVertex ∧
          vertex ≠ collar.targetData.secondVertex}

/-- The common induced graph obtained by deleting both adjacent pairs. -/
abbrev commonCore
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    SimpleGraph collar.commonCoreVertex :=
  DeletedTwoPairsGraph G
    collar.sourceData.firstVertex collar.sourceData.secondVertex
    collar.targetData.firstVertex collar.targetData.secondVertex

/-- Inclusion of the common-core carrier into the ambient vertex type. -/
def commonCoreVertexEmbedding
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.commonCoreVertex ↪ V :=
  Function.Embedding.subtype fun vertex : V =>
    vertex ∈ collar.commonCoreVertex

/-- Common-core neighbors are exactly ambient neighbors with all four
deleted vertices erased. -/
theorem map_neighborFinset_commonCore
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (vertex : collar.commonCoreVertex) :
    (SimpleGraph.neighborFinset (G := collar.commonCore) vertex).map
        collar.commonCoreVertexEmbedding =
      ((((G.neighborFinset vertex.1).erase
          collar.sourceData.firstVertex).erase
          collar.sourceData.secondVertex).erase
          collar.targetData.firstVertex).erase
          collar.targetData.secondVertex := by
  ext other
  rw [Finset.mem_map]
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  constructor
  · rintro ⟨neighbor, hadjacent, heq⟩
    subst other
    exact ⟨neighbor.2.2.2.2, neighbor.2.2.2.1,
      neighbor.2.2.1, neighbor.2.1, hadjacent⟩
  · rintro ⟨htargetSecond, htargetFirst, hsourceSecond,
      hsourceFirst, hadjacent⟩
    let neighbor : collar.commonCoreVertex :=
      ⟨other, hsourceFirst, hsourceSecond, htargetFirst, htargetSecond⟩
    exact ⟨neighbor, hadjacent, rfl⟩

/-- A source port as a vertex of the common four-vertex deletion. -/
def sourcePortInCommonCore
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (port : Fin 4) : collar.commonCoreVertex :=
  ⟨collar.sourceData.portVertex port,
    collar.sourceData.portNeFirst port,
    collar.sourceData.portNeSecond port,
    (collar.sourcePort_mem_targetRetainedVertexSet port).1,
    (collar.sourcePort_mem_targetRetainedVertexSet port).2⟩

/-- The first target vertex, regarded as a vertex of the source deletion. -/
def targetFirstInSourceDeletion
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    retainedVertexSet collar.sourceData.firstVertex
      collar.sourceData.secondVertex :=
  ⟨collar.targetData.firstVertex,
    collar.targetFirst_mem_sourceRetainedVertexSet⟩

/-- The second target vertex, regarded as a vertex of the source deletion. -/
def targetSecondInSourceDeletion
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    retainedVertexSet collar.sourceData.firstVertex
      collar.sourceData.secondVertex :=
  ⟨collar.targetData.secondVertex,
    collar.targetSecond_mem_sourceRetainedVertexSet⟩

/-- At a source port, mapping common-core neighbors into the source deletion
amounts exactly to erasing the two target vertices. -/
theorem map_neighborFinset_commonCore_to_sourceDeletion
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort : Fin 4) :
    (SimpleGraph.neighborFinset (G := collar.commonCore)
        (collar.sourcePortInCommonCore sourcePort)).map
          (deletedTwoPairsToFirstDeletionEmbedding G
            collar.sourceData.firstVertex collar.sourceData.secondVertex
            collar.targetData.firstVertex
            collar.targetData.secondVertex).toCopy.toEmbedding =
      ((SimpleGraph.neighborFinset
        (G := DeletedAdjacentPairGraph G
          collar.sourceData.firstVertex collar.sourceData.secondVertex)
        (collar.sourceData.retainedPort sourcePort)).erase
          collar.targetFirstInSourceDeletion).erase
            collar.targetSecondInSourceDeletion := by
  ext other
  rw [Finset.mem_map]
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  constructor
  · rintro ⟨neighbor, hadjacent, heq⟩
    subst other
    refine ⟨?_, ?_, hadjacent⟩
    · intro htargetSecond
      exact neighbor.2.2.2.2 (congrArg Subtype.val htargetSecond)
    · intro htargetFirst
      exact neighbor.2.2.2.1 (congrArg Subtype.val htargetFirst)
  · rintro ⟨htargetSecond, htargetFirst, hadjacent⟩
    have htargetFirstValue : other.1 ≠ collar.targetData.firstVertex := by
      intro heq
      apply htargetFirst
      exact Subtype.ext heq
    have htargetSecondValue : other.1 ≠ collar.targetData.secondVertex := by
      intro heq
      apply htargetSecond
      exact Subtype.ext heq
    let neighbor : collar.commonCoreVertex :=
      ⟨other.1, other.2.1, other.2.2,
        htargetFirstValue, htargetSecondValue⟩
    refine ⟨neighbor, hadjacent, ?_⟩
    exact Subtype.ext rfl

/-- A target port as a vertex of the same common deletion. -/
def targetPortInCommonCore
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (port : Fin 4) : collar.commonCoreVertex :=
  ⟨collar.targetData.portVertex port,
    (collar.targetPort_mem_sourceRetainedVertexSet port).1,
    (collar.targetPort_mem_sourceRetainedVertexSet port).2,
    collar.targetData.portNeFirst port,
    collar.targetData.portNeSecond port⟩

/-- The first source vertex, regarded as a vertex of the target deletion. -/
def sourceFirstInTargetDeletion
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    retainedVertexSet collar.targetData.firstVertex
      collar.targetData.secondVertex :=
  ⟨collar.sourceData.firstVertex,
    collar.sourceFirst_mem_targetRetainedVertexSet⟩

/-- The second source vertex, regarded as a vertex of the target deletion. -/
def sourceSecondInTargetDeletion
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    retainedVertexSet collar.targetData.firstVertex
      collar.targetData.secondVertex :=
  ⟨collar.sourceData.secondVertex,
    collar.sourceSecond_mem_targetRetainedVertexSet⟩

/-- At a target port, mapping common-core neighbors into the target deletion
amounts exactly to erasing the two source vertices. -/
theorem map_neighborFinset_commonCore_to_targetDeletion
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) :
    (SimpleGraph.neighborFinset (G := collar.commonCore)
        (collar.targetPortInCommonCore targetPort)).map
          (deletedTwoPairsToSecondDeletionEmbedding G
            collar.sourceData.firstVertex collar.sourceData.secondVertex
            collar.targetData.firstVertex
            collar.targetData.secondVertex).toCopy.toEmbedding =
      ((SimpleGraph.neighborFinset
        (G := DeletedAdjacentPairGraph G
          collar.targetData.firstVertex collar.targetData.secondVertex)
        (collar.targetData.retainedPort targetPort)).erase
          collar.sourceFirstInTargetDeletion).erase
            collar.sourceSecondInTargetDeletion := by
  ext other
  rw [Finset.mem_map]
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  constructor
  · rintro ⟨neighbor, hadjacent, heq⟩
    subst other
    refine ⟨?_, ?_, hadjacent⟩
    · intro hsourceSecond
      exact neighbor.2.2.1 (congrArg Subtype.val hsourceSecond)
    · intro hsourceFirst
      exact neighbor.2.1 (congrArg Subtype.val hsourceFirst)
  · rintro ⟨hsourceSecond, hsourceFirst, hadjacent⟩
    have hsourceFirstValue : other.1 ≠ collar.sourceData.firstVertex := by
      intro heq
      apply hsourceFirst
      exact Subtype.ext heq
    have hsourceSecondValue : other.1 ≠ collar.sourceData.secondVertex := by
      intro heq
      apply hsourceSecond
      exact Subtype.ext heq
    let neighbor : collar.commonCoreVertex :=
      ⟨other.1, hsourceFirstValue, hsourceSecondValue,
        other.2.1, other.2.2⟩
    refine ⟨neighbor, hadjacent, ?_⟩
    exact Subtype.ext rfl

theorem sourcePortInCommonCore_injective
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Function.Injective collar.sourcePortInCommonCore := by
  intro first second heq
  apply collar.sourceData.portInjective
  exact congrArg Subtype.val heq

theorem targetPortInCommonCore_injective
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Function.Injective collar.targetPortInCommonCore := by
  intro first second heq
  apply collar.targetData.portInjective
  exact congrArg Subtype.val heq

/-- The only possible collision in the eight named common-core ports is a
literal equality between one source port and one target port. -/
abbrev PortOverlap
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort targetPort : Fin 4) : Prop :=
  collar.sourceData.portVertex sourcePort =
    collar.targetData.portVertex targetPort

theorem sourcePortInCommonCore_eq_targetPortInCommonCore_iff
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort targetPort : Fin 4) :
    collar.sourcePortInCommonCore sourcePort =
        collar.targetPortInCommonCore targetPort ↔
      collar.PortOverlap sourcePort targetPort := by
  constructor
  · intro heq
    exact congrArg Subtype.val heq
  · intro heq
    exact Subtype.ext heq

/-- Port overlap is functional from source ports to target ports. -/
theorem portOverlap_target_unique
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    {sourcePort firstTarget secondTarget : Fin 4}
    (hfirst : collar.PortOverlap sourcePort firstTarget)
    (hsecond : collar.PortOverlap sourcePort secondTarget) :
    firstTarget = secondTarget := by
  apply collar.targetData.portInjective
  exact hfirst.symm.trans hsecond

/-- Port overlap is functional from target ports to source ports. -/
theorem portOverlap_source_unique
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    {firstSource secondSource targetPort : Fin 4}
    (hfirst : collar.PortOverlap firstSource targetPort)
    (hsecond : collar.PortOverlap secondSource targetPort) :
    firstSource = secondSource := by
  apply collar.sourceData.portInjective
  exact hfirst.trans hsecond.symm

/-- A source port overlaps the target boundary exactly when it is adjacent
to one endpoint of the target pair. -/
theorem exists_portOverlap_iff_adj_targetPair
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort : Fin 4) :
    (∃ targetPort : Fin 4, collar.PortOverlap sourcePort targetPort) ↔
      G.Adj (collar.sourceData.portVertex sourcePort)
          collar.targetData.firstVertex ∨
        G.Adj (collar.sourceData.portVertex sourcePort)
          collar.targetData.secondVertex := by
  constructor
  · rintro ⟨targetPort, hoverlap⟩
    fin_cases targetPort
    · exact Or.inl (by
        rw [hoverlap]
        exact collar.targetData.first_adj_port_zero.symm)
    · exact Or.inl (by
        rw [hoverlap]
        exact collar.targetData.first_adj_port_one.symm)
    · exact Or.inr (by
        rw [hoverlap]
        exact collar.targetData.second_adj_port_two.symm)
    · exact Or.inr (by
        rw [hoverlap]
        exact collar.targetData.second_adj_port_three.symm)
  · rintro (hfirst | hsecond)
    · have hmem : collar.sourceData.portVertex sourcePort ∈
          G.neighborSet collar.targetData.firstVertex := hfirst.symm
      rw [collar.targetData.firstNeighbors] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with htargetSecond | hzero | hone
      · exact False.elim
          ((collar.sourcePort_mem_targetRetainedVertexSet sourcePort).2
            htargetSecond)
      · exact ⟨0, hzero⟩
      · exact ⟨1, hone⟩
    · have hmem : collar.sourceData.portVertex sourcePort ∈
          G.neighborSet collar.targetData.secondVertex := hsecond.symm
      rw [collar.targetData.secondNeighbors] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with htargetFirst | htwo | hthree
      · exact False.elim
          ((collar.sourcePort_mem_targetRetainedVertexSet sourcePort).1
            htargetFirst)
      · exact ⟨2, htwo⟩
      · exact ⟨3, hthree⟩

/-- A common-core source port cannot be adjacent to both target vertices. -/
theorem not_adj_sourcePort_targetFirst_and_targetSecond
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort : Fin 4) :
    ¬ (G.Adj (collar.sourceData.portVertex sourcePort)
          collar.targetData.firstVertex ∧
        G.Adj (collar.sourceData.portVertex sourcePort)
          collar.targetData.secondVertex) := by
  rintro ⟨hfirst, hsecond⟩
  exact GoertzelV24MinimalTriangleFree.no_common_neighbor_of_vertexMinimalTaitCounterexample
    graphData minimal collar.targetData.centralAdjacent
      (collar.sourceData.portVertex sourcePort) hfirst.symm hsecond.symm

/-- A target port overlaps the source boundary exactly when it is adjacent
to one endpoint of the source pair. -/
theorem exists_portOverlap_iff_adj_sourcePair
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) :
    (∃ sourcePort : Fin 4, collar.PortOverlap sourcePort targetPort) ↔
      G.Adj (collar.targetData.portVertex targetPort)
          collar.sourceData.firstVertex ∨
        G.Adj (collar.targetData.portVertex targetPort)
          collar.sourceData.secondVertex := by
  constructor
  · rintro ⟨sourcePort, hoverlap⟩
    fin_cases sourcePort
    · exact Or.inl (by
        rw [← hoverlap]
        exact collar.sourceData.first_adj_port_zero.symm)
    · exact Or.inl (by
        rw [← hoverlap]
        exact collar.sourceData.first_adj_port_one.symm)
    · exact Or.inr (by
        rw [← hoverlap]
        exact collar.sourceData.second_adj_port_two.symm)
    · exact Or.inr (by
        rw [← hoverlap]
        exact collar.sourceData.second_adj_port_three.symm)
  · rintro (hfirst | hsecond)
    · have hmem : collar.targetData.portVertex targetPort ∈
          G.neighborSet collar.sourceData.firstVertex := hfirst.symm
      rw [collar.sourceData.firstNeighbors] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hsourceSecond | hzero | hone
      · exact False.elim
          ((collar.targetPort_mem_sourceRetainedVertexSet targetPort).2
            hsourceSecond)
      · exact ⟨0, hzero.symm⟩
      · exact ⟨1, hone.symm⟩
    · have hmem : collar.targetData.portVertex targetPort ∈
          G.neighborSet collar.sourceData.secondVertex := hsecond.symm
      rw [collar.sourceData.secondNeighbors] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hsourceFirst | htwo | hthree
      · exact False.elim
          ((collar.targetPort_mem_sourceRetainedVertexSet targetPort).1
            hsourceFirst)
      · exact ⟨2, htwo.symm⟩
      · exact ⟨3, hthree.symm⟩

/-- A common-core target port cannot be adjacent to both source vertices. -/
theorem not_adj_targetPort_sourceFirst_and_sourceSecond
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) :
    ¬ (G.Adj (collar.targetData.portVertex targetPort)
          collar.sourceData.firstVertex ∧
        G.Adj (collar.targetData.portVertex targetPort)
          collar.sourceData.secondVertex) := by
  rintro ⟨hfirst, hsecond⟩
  exact GoertzelV24MinimalTriangleFree.no_common_neighbor_of_vertexMinimalTaitCounterexample
    graphData minimal collar.sourceData.centralAdjacent
      (collar.targetData.portVertex targetPort) hfirst.symm hsecond.symm

/-- A source port has degree two in the common core unless it overlaps one
target port, in which case the second deletion lowers its degree to one. -/
theorem card_incidentEdgeFinset_sourcePortInCommonCore
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort : Fin 4) :
    (incidentEdgeFinset collar.commonCore
      (collar.sourcePortInCommonCore sourcePort)).card =
        if ∃ targetPort : Fin 4,
            collar.PortOverlap sourcePort targetPort then 1 else 2 := by
  classical
  let sourceGraph := DeletedAdjacentPairGraph G
    collar.sourceData.firstVertex collar.sourceData.secondVertex
  let sourcePortVertex := collar.sourceData.retainedPort sourcePort
  let targetFirst := collar.targetFirstInSourceDeletion
  let targetSecond := collar.targetSecondInSourceDeletion
  let sourceNeighborhood := SimpleGraph.neighborFinset
    (G := sourceGraph) sourcePortVertex
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hsourceNeighborhoodCard : sourceNeighborhood.card = 2 := by
    calc
      sourceNeighborhood.card = sourceGraph.degree sourcePortVertex := by
        exact SimpleGraph.card_neighborFinset_eq_degree _ _
      _ = (incidentEdgeFinset sourceGraph sourcePortVertex).card := by
        exact (incidentEdgeFinset_card_eq_degree sourcePortVertex).symm
      _ = 2 := by
        simpa [sourceGraph, sourcePortVertex,
          GoertzelV24AdjacentPairBoundary.AdjacentPairData.degreeTwoBoundaryData]
          using
          (collar.sourceData.degreeTwoBoundaryData_wellFormed hcubic).2.1
            sourcePort
  have hfirstMem : targetFirst ∈ sourceNeighborhood ↔
      G.Adj (collar.sourceData.portVertex sourcePort)
        collar.targetData.firstVertex := by
    simp only [sourceNeighborhood, SimpleGraph.mem_neighborFinset]
    rfl
  have hsecondMem : targetSecond ∈ sourceNeighborhood ↔
      G.Adj (collar.sourceData.portVertex sourcePort)
        collar.targetData.secondVertex := by
    simp only [sourceNeighborhood, SimpleGraph.mem_neighborFinset]
    rfl
  calc
    (incidentEdgeFinset collar.commonCore
        (collar.sourcePortInCommonCore sourcePort)).card =
        collar.commonCore.degree
          (collar.sourcePortInCommonCore sourcePort) :=
      incidentEdgeFinset_card_eq_degree _
    _ = (SimpleGraph.neighborFinset
          (G := collar.commonCore)
          (collar.sourcePortInCommonCore sourcePort)).card :=
      (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ = ((SimpleGraph.neighborFinset
          (G := collar.commonCore)
          (collar.sourcePortInCommonCore sourcePort)).map
            (deletedTwoPairsToFirstDeletionEmbedding G
              collar.sourceData.firstVertex collar.sourceData.secondVertex
              collar.targetData.firstVertex
              collar.targetData.secondVertex).toCopy.toEmbedding).card := by
      simp
    _ = ((sourceNeighborhood.erase targetFirst).erase
          targetSecond).card := by
      exact congrArg Finset.card
        (collar.map_neighborFinset_commonCore_to_sourceDeletion sourcePort)
    _ = if ∃ targetPort : Fin 4,
          collar.PortOverlap sourcePort targetPort then 1 else 2 := by
      by_cases hoverlap : ∃ targetPort : Fin 4,
          collar.PortOverlap sourcePort targetPort
      · rw [if_pos hoverlap]
        rcases (collar.exists_portOverlap_iff_adj_targetPair sourcePort).1
          hoverlap with hfirst | hsecond
        · have hfirstIn := hfirstMem.2 hfirst
          have hsecondNot : targetSecond ∉ sourceNeighborhood := by
            intro hsecondIn
            exact collar.not_adj_sourcePort_targetFirst_and_targetSecond
              sourcePort ⟨hfirst, hsecondMem.1 hsecondIn⟩
          have hsecondNotAfter : targetSecond ∉
              sourceNeighborhood.erase targetFirst := by
            exact fun hmem => hsecondNot (Finset.mem_of_mem_erase hmem)
          rw [Finset.erase_eq_self.mpr hsecondNotAfter,
            Finset.card_erase_of_mem hfirstIn, hsourceNeighborhoodCard]
        · have hsecondIn := hsecondMem.2 hsecond
          have hfirstNot : targetFirst ∉ sourceNeighborhood := by
            intro hfirstIn
            exact collar.not_adj_sourcePort_targetFirst_and_targetSecond
              sourcePort ⟨hfirstMem.1 hfirstIn, hsecond⟩
          rw [Finset.erase_eq_self.mpr hfirstNot,
            Finset.card_erase_of_mem hsecondIn, hsourceNeighborhoodCard]
      · rw [if_neg hoverlap]
        have hnotAdjacent :=
          not_or.mp (not_congr
            (collar.exists_portOverlap_iff_adj_targetPair sourcePort) |>.mp
              hoverlap)
        have hfirstNot : targetFirst ∉ sourceNeighborhood := fun hmem =>
          hnotAdjacent.1 (hfirstMem.1 hmem)
        have hsecondNot : targetSecond ∉ sourceNeighborhood := fun hmem =>
          hnotAdjacent.2 (hsecondMem.1 hmem)
        rw [Finset.erase_eq_self.mpr hfirstNot,
          Finset.erase_eq_self.mpr hsecondNot, hsourceNeighborhoodCard]

/-- Symmetrically, a target port has degree two in the common core unless
it overlaps one source port, in which case its degree is one. -/
theorem card_incidentEdgeFinset_targetPortInCommonCore
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) :
    (incidentEdgeFinset collar.commonCore
      (collar.targetPortInCommonCore targetPort)).card =
        if ∃ sourcePort : Fin 4,
            collar.PortOverlap sourcePort targetPort then 1 else 2 := by
  classical
  let targetGraph := DeletedAdjacentPairGraph G
    collar.targetData.firstVertex collar.targetData.secondVertex
  let targetPortVertex := collar.targetData.retainedPort targetPort
  let sourceFirst := collar.sourceFirstInTargetDeletion
  let sourceSecond := collar.sourceSecondInTargetDeletion
  let targetNeighborhood := SimpleGraph.neighborFinset
    (G := targetGraph) targetPortVertex
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have htargetNeighborhoodCard : targetNeighborhood.card = 2 := by
    calc
      targetNeighborhood.card = targetGraph.degree targetPortVertex := by
        exact SimpleGraph.card_neighborFinset_eq_degree _ _
      _ = (incidentEdgeFinset targetGraph targetPortVertex).card := by
        exact (incidentEdgeFinset_card_eq_degree targetPortVertex).symm
      _ = 2 := by
        simpa [targetGraph, targetPortVertex,
          GoertzelV24AdjacentPairBoundary.AdjacentPairData.degreeTwoBoundaryData]
          using
          (collar.targetData.degreeTwoBoundaryData_wellFormed hcubic).2.1
            targetPort
  have hfirstMem : sourceFirst ∈ targetNeighborhood ↔
      G.Adj (collar.targetData.portVertex targetPort)
        collar.sourceData.firstVertex := by
    simp only [targetNeighborhood, SimpleGraph.mem_neighborFinset]
    rfl
  have hsecondMem : sourceSecond ∈ targetNeighborhood ↔
      G.Adj (collar.targetData.portVertex targetPort)
        collar.sourceData.secondVertex := by
    simp only [targetNeighborhood, SimpleGraph.mem_neighborFinset]
    rfl
  calc
    (incidentEdgeFinset collar.commonCore
        (collar.targetPortInCommonCore targetPort)).card =
        collar.commonCore.degree
          (collar.targetPortInCommonCore targetPort) :=
      incidentEdgeFinset_card_eq_degree _
    _ = (SimpleGraph.neighborFinset
          (G := collar.commonCore)
          (collar.targetPortInCommonCore targetPort)).card :=
      (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ = ((SimpleGraph.neighborFinset
          (G := collar.commonCore)
          (collar.targetPortInCommonCore targetPort)).map
            (deletedTwoPairsToSecondDeletionEmbedding G
              collar.sourceData.firstVertex collar.sourceData.secondVertex
              collar.targetData.firstVertex
              collar.targetData.secondVertex).toCopy.toEmbedding).card := by
      simp
    _ = ((targetNeighborhood.erase sourceFirst).erase
          sourceSecond).card := by
      exact congrArg Finset.card
        (collar.map_neighborFinset_commonCore_to_targetDeletion targetPort)
    _ = if ∃ sourcePort : Fin 4,
          collar.PortOverlap sourcePort targetPort then 1 else 2 := by
      by_cases hoverlap : ∃ sourcePort : Fin 4,
          collar.PortOverlap sourcePort targetPort
      · rw [if_pos hoverlap]
        rcases (collar.exists_portOverlap_iff_adj_sourcePair targetPort).1
          hoverlap with hfirst | hsecond
        · have hfirstIn := hfirstMem.2 hfirst
          have hsecondNot : sourceSecond ∉ targetNeighborhood := by
            intro hsecondIn
            exact collar.not_adj_targetPort_sourceFirst_and_sourceSecond
              targetPort ⟨hfirst, hsecondMem.1 hsecondIn⟩
          have hsecondNotAfter : sourceSecond ∉
              targetNeighborhood.erase sourceFirst := by
            exact fun hmem => hsecondNot (Finset.mem_of_mem_erase hmem)
          rw [Finset.erase_eq_self.mpr hsecondNotAfter,
            Finset.card_erase_of_mem hfirstIn, htargetNeighborhoodCard]
        · have hsecondIn := hsecondMem.2 hsecond
          have hfirstNot : sourceFirst ∉ targetNeighborhood := by
            intro hfirstIn
            exact collar.not_adj_targetPort_sourceFirst_and_sourceSecond
              targetPort ⟨hfirstMem.1 hfirstIn, hsecond⟩
          rw [Finset.erase_eq_self.mpr hfirstNot,
            Finset.card_erase_of_mem hsecondIn, htargetNeighborhoodCard]
      · rw [if_neg hoverlap]
        have hnotAdjacent :=
          not_or.mp (not_congr
            (collar.exists_portOverlap_iff_adj_sourcePair targetPort) |>.mp
              hoverlap)
        have hfirstNot : sourceFirst ∉ targetNeighborhood := fun hmem =>
          hnotAdjacent.1 (hfirstMem.1 hmem)
        have hsecondNot : sourceSecond ∉ targetNeighborhood := fun hmem =>
          hnotAdjacent.2 (hsecondMem.1 hmem)
        rw [Finset.erase_eq_self.mpr hfirstNot,
          Finset.erase_eq_self.mpr hsecondNot, htargetNeighborhoodCard]

/-- Every common-core vertex outside the two four-port images keeps its
ambient cubic degree. Thus the partial port matching accounts for all
degree-one and degree-two defects of the common core. -/
theorem card_incidentEdgeFinset_commonCore_eq_three_of_not_ports
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (vertex : collar.commonCoreVertex)
    (hsource : ∀ port : Fin 4,
      vertex ≠ collar.sourcePortInCommonCore port)
    (htarget : ∀ port : Fin 4,
      vertex ≠ collar.targetPortInCommonCore port) :
    (incidentEdgeFinset collar.commonCore vertex).card = 3 := by
  have hnotSourceFirst :
      ¬ G.Adj vertex.1 collar.sourceData.firstVertex := by
    intro hadjacent
    have hmem : vertex.1 ∈
        G.neighborSet collar.sourceData.firstVertex := hadjacent.symm
    rw [collar.sourceData.firstNeighbors] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hsourceSecond | hzero | hone
    · exact vertex.2.2.1 hsourceSecond
    · exact hsource 0 (Subtype.ext hzero)
    · exact hsource 1 (Subtype.ext hone)
  have hnotSourceSecond :
      ¬ G.Adj vertex.1 collar.sourceData.secondVertex := by
    intro hadjacent
    have hmem : vertex.1 ∈
        G.neighborSet collar.sourceData.secondVertex := hadjacent.symm
    rw [collar.sourceData.secondNeighbors] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hsourceFirst | htwo | hthree
    · exact vertex.2.1 hsourceFirst
    · exact hsource 2 (Subtype.ext htwo)
    · exact hsource 3 (Subtype.ext hthree)
  have hnotTargetFirst :
      ¬ G.Adj vertex.1 collar.targetData.firstVertex := by
    intro hadjacent
    have hmem : vertex.1 ∈
        G.neighborSet collar.targetData.firstVertex := hadjacent.symm
    rw [collar.targetData.firstNeighbors] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with htargetSecond | hzero | hone
    · exact vertex.2.2.2.2 htargetSecond
    · exact htarget 0 (Subtype.ext hzero)
    · exact htarget 1 (Subtype.ext hone)
  have hnotTargetSecond :
      ¬ G.Adj vertex.1 collar.targetData.secondVertex := by
    intro hadjacent
    have hmem : vertex.1 ∈
        G.neighborSet collar.targetData.secondVertex := hadjacent.symm
    rw [collar.targetData.secondNeighbors] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with htargetFirst | htwo | hthree
    · exact vertex.2.2.2.1 htargetFirst
    · exact htarget 2 (Subtype.ext htwo)
    · exact htarget 3 (Subtype.ext hthree)
  have hsourceFirstNotMem : collar.sourceData.firstVertex ∉
      G.neighborFinset vertex.1 := by
    simpa only [SimpleGraph.mem_neighborFinset] using hnotSourceFirst
  have hsourceSecondNotMem : collar.sourceData.secondVertex ∉
      G.neighborFinset vertex.1 := by
    simpa only [SimpleGraph.mem_neighborFinset] using hnotSourceSecond
  have htargetFirstNotMem : collar.targetData.firstVertex ∉
      G.neighborFinset vertex.1 := by
    simpa only [SimpleGraph.mem_neighborFinset] using hnotTargetFirst
  have htargetSecondNotMem : collar.targetData.secondVertex ∉
      G.neighborFinset vertex.1 := by
    simpa only [SimpleGraph.mem_neighborFinset] using hnotTargetSecond
  have hcubic : ∀ ambientVertex : V,
      (incidentEdgeFinset G ambientVertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  calc
    (incidentEdgeFinset collar.commonCore vertex).card =
        collar.commonCore.degree vertex :=
      incidentEdgeFinset_card_eq_degree _
    _ = (SimpleGraph.neighborFinset
          (G := collar.commonCore) vertex).card :=
      (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ = ((SimpleGraph.neighborFinset
          (G := collar.commonCore) vertex).map
            collar.commonCoreVertexEmbedding).card := by simp
    _ = (((((G.neighborFinset vertex.1).erase
          collar.sourceData.firstVertex).erase
          collar.sourceData.secondVertex).erase
          collar.targetData.firstVertex).erase
          collar.targetData.secondVertex).card := by
      exact congrArg Finset.card
        (collar.map_neighborFinset_commonCore vertex)
    _ = (G.neighborFinset vertex.1).card := by
      simp [hsourceFirstNotMem, hsourceSecondNotMem,
        htargetFirstNotMem, htargetSecondNotMem]
    _ = G.degree vertex.1 :=
      SimpleGraph.card_neighborFinset_eq_degree _ _
    _ = (incidentEdgeFinset G vertex.1).card :=
      (incidentEdgeFinset_card_eq_degree vertex.1).symm
    _ = 3 := hcubic vertex.1

/-- The finite graph of the partial matching between the two port maps. -/
abbrev PortOverlapPair
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :=
  { ports : Fin 4 × Fin 4 // collar.PortOverlap ports.1 ports.2 }

/-- At most four common-core boundary vertices have degree lowered by both
deletions: the overlap relation is a partial matching. -/
theorem card_portOverlapPair_le_four
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    Fintype.card collar.PortOverlapPair ≤ 4 := by
  let sourceProjection : collar.PortOverlapPair → Fin 4 :=
    fun overlap => overlap.1.1
  have hinjective : Function.Injective sourceProjection := by
    rintro ⟨⟨firstSource, firstTarget⟩, hfirst⟩
      ⟨⟨secondSource, secondTarget⟩, hsecond⟩ heq
    dsimp only [sourceProjection] at heq
    subst secondSource
    apply Subtype.ext
    change (firstSource, firstTarget) = (firstSource, secondTarget)
    exact Prod.ext rfl
      (collar.portOverlap_target_unique hfirst hsecond)
  simpa using Fintype.card_le_of_injective sourceProjection hinjective

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
