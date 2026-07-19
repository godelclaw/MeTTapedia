import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitPortPairingReductionBridgePortSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutGluing

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FourDefectBoundary
open GoertzelV24FourEdgeCutRetainedBridge
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

local instance reductionBridgeCyclicCutGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance reductionBridgeCyclicCutRetainedVertexSetFintype
    (first second : V) :
    Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance reductionBridgeCyclicCutRetainedVertexSetDecidableEq
    (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- Lift one component obtained by deleting a retained edge back to an
ambient vertex-side predicate. -/
def retainedEdgeDeleteComponentSide
    (data : AdjacentPairData G)
    (removed : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (component : ((DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).deleteEdges {removed.1}).ConnectedComponent)
    (vertex : V) : Prop :=
  ∃ retained : retainedVertexSet data.firstVertex data.secondVertex,
    retained ∈ component.supp ∧ retained.1 = vertex

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A retained-edge deletion component stays connected when lifted into
the ambient graph. -/
theorem retainedEdgeDeleteComponentSide_connected
    (data : AdjacentPairData G)
    (removed : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (component : ((DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).deleteEdges {removed.1}).ConnectedComponent) :
    (G.induce {vertex |
      retainedEdgeDeleteComponentSide data removed component vertex}).Connected := by
  let source := component.toSimpleGraph
  let target := G.induce {vertex |
    retainedEdgeDeleteComponentSide data removed component vertex}
  let mapVertex : component →
      {vertex : V |
        retainedEdgeDeleteComponentSide data removed component vertex} :=
    fun vertex => ⟨vertex.1.1, ⟨vertex.1, vertex.2, rfl⟩⟩
  let hom : source →g target :=
    { toFun := mapVertex
      map_rel' := by
        intro left right hadj
        exact hadj.1 }
  let rootSource : component := ⟨component.out, component.out_eq⟩
  letI : Nonempty
      {vertex : V |
        retainedEdgeDeleteComponentSide data removed component vertex} :=
    ⟨mapVertex rootSource⟩
  refine ⟨?_⟩
  intro left right
  rcases left.2 with ⟨leftRetained, hleftComponent, hleftValue⟩
  rcases right.2 with ⟨rightRetained, hrightComponent, hrightValue⟩
  let leftSource : component := ⟨leftRetained, hleftComponent⟩
  let rightSource : component := ⟨rightRetained, hrightComponent⟩
  have hreach := component.connected_toSimpleGraph leftSource rightSource
  have hmapped := hreach.map hom
  change target.Reachable left right
  convert hmapped using 1 <;> apply Subtype.ext
  · exact hleftValue.symm
  · exact hrightValue.symm

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every ambient edge leaving a retained-edge deletion component is the
deleted retained edge itself or an exposed boundary edge whose port lies in
that component. -/
theorem retainedEdgeDeleteComponentSide_crossingEdge
    (data : AdjacentPairData G)
    (removed : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (component : ((DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).deleteEdges {removed.1}).ConnectedComponent)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (retainedEdgeDeleteComponentSide data removed component) edge) :
    edge = data.retainedEdgeToAmbientEdge removed ∨
      ∃ port : Fin 4,
        edge = data.boundaryEdge port ∧
          data.retainedPort port ∈ component.supp := by
  rcases hcross with
    ⟨inside, outside, hinsideEdge, houtsideEdge,
      hinsideSide, houtsideSide⟩
  rcases hinsideSide with
    ⟨insideRetained, hinsideComponent, hinsideValue⟩
  have hvertices : inside ≠ outside := by
    intro heq
    apply houtsideSide
    exact ⟨insideRetained, hinsideComponent, hinsideValue.trans heq⟩
  have hedgeValue : edge.1 = s(inside, outside) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hinsideEdge houtsideEdge hvertices
  have hadj : G.Adj inside outside :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [hedgeValue] using edge.2)
  by_cases houtsideRetained :
      outside ∈ retainedVertexSet data.firstVertex data.secondVertex
  · let outsideVertex : retainedVertexSet data.firstVertex
        data.secondVertex := ⟨outside, houtsideRetained⟩
    have hinduced :
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Adj
          insideRetained outsideVertex := by
      change G.Adj insideRetained.1 outsideVertex.1
      simpa [hinsideValue] using hadj
    by_cases hremoved : s(insideRetained, outsideVertex) = removed.1
    · left
      apply Subtype.ext
      rw [retainedEdgeToAmbientEdge_val]
      rw [← hremoved, Sym2.map_mk]
      simpa [hinsideValue]
    · have hdeletedAdj :
          ((DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).deleteEdges {removed.1}).Adj
            insideRetained outsideVertex := by
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hinduced, ?_⟩
        intro hmem
        exact hremoved (Set.mem_singleton_iff.mp hmem)
      have houtsideComponent : outsideVertex ∈ component.supp :=
        (component.mem_supp_congr_adj hdeletedAdj).mp hinsideComponent
      exact False.elim (houtsideSide
        ⟨outsideVertex, houtsideComponent, rfl⟩)
  · right
    have hinsideRetained : inside ∉ data.deletedVertices := by
      simpa [deletedVertices, hinsideValue] using insideRetained.2
    have houtsideMem : outside ∈ data.deletedVertices := by
      have houtsideCases :
          outside = data.firstVertex ∨ outside = data.secondVertex := by
        by_cases hfirst : outside = data.firstVertex
        · exact Or.inl hfirst
        · right
          by_contra hsecond
          exact houtsideRetained ⟨hfirst, hsecond⟩
      rcases houtsideCases with rfl | rfl <;> simp [deletedVertices]
    have hcrossDeleted : EdgeCrossesVertexSide G
        (fun vertex => vertex ∈ data.deletedVertices) edge :=
      ⟨outside, inside, houtsideEdge, hinsideEdge,
        houtsideMem, hinsideRetained⟩
    rcases (data.edgeCrosses_deletedVertices_iff_exists_boundaryEdge edge).1
        hcrossDeleted with ⟨port, hedge⟩
    refine ⟨port, hedge, ?_⟩
    subst edge
    change inside ∈ (data.boundaryEdgeValue port : Sym2 V) at hinsideEdge
    rw [data.boundaryEdgeValue_eq] at hinsideEdge
    simp only [Sym2.mem_iff] at hinsideEdge
    have hinsidePort : inside = data.portVertex port := by
      rcases hinsideEdge with hdeleted | hport
      · exfalso
        apply hinsideRetained
        fin_cases port <;>
          simp [deletedVertices,
            GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryDeletedVertex,
            hdeleted]
      · exact hport
    have hretainedEq : data.retainedPort port = insideRetained := by
      apply Subtype.ext
      exact hinsidePort.symm.trans hinsideValue.symm
    rw [hretainedEq]
    exact hinsideComponent

/-- If two vertices have the same membership status in the first endpoint
component after deleting one edge of a connected graph, then they lie in
the same deletion component. -/
theorem reachable_deleteEdge_of_fst_reachable_iff
    {W : Type*} {H : SimpleGraph W}
    (hconnected : H.Connected) (removed : H.Dart) {left right : W}
    (hiff :
      (H.deleteEdges {removed.edge}).Reachable removed.fst left ↔
        (H.deleteEdges {removed.edge}).Reachable removed.fst right) :
    (H.deleteEdges {removed.edge}).Reachable left right := by
  by_cases hleft :
      (H.deleteEdges {removed.edge}).Reachable removed.fst left
  · exact hleft.symm.trans (hiff.mp hleft)
  · have hright :
        ¬ (H.deleteEdges {removed.edge}).Reachable removed.fst right :=
      fun hreach => hleft (hiff.mpr hreach)
    have hleftCover := reachable_deleteEdge_endpoint_or_endpoint
      hconnected removed left
    have hrightCover := reachable_deleteEdge_endpoint_or_endpoint
      hconnected removed right
    rcases hleftCover with hleftFirst | hleftSecond
    · exact False.elim (hleft hleftFirst)
    · rcases hrightCover with hrightFirst | hrightSecond
      · exact False.elim (hright hrightFirst)
      · exact hleftSecond.symm.trans hrightSecond

/-- A connected side of a cubic graph containing two distinct vertices and
supported by at most three outgoing edges contains a cycle. -/
theorem hasCycleOnSide_of_cubic_of_connected_of_two_vertices_of_crossing_le_three
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop)
    (first second : V) (hfirst : side first) (hsecond : side second)
    (hne : first ≠ second)
    (hconnected : (G.induce {vertex | side vertex}).Connected)
    (support : Finset G.edgeSet) (hsupportCard : support.card ≤ 3)
    (hcrossing : ∀ dart : CrossingSideDart G side,
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ support) :
    HasCycleOnSide G side := by
  by_contra hnoCycle
  have hcount :=
    card_crossingSideDart_eq_card_add_two_of_cubic_of_noCycle
      hregular side hconnected hnoCycle
  have hcrossingCard := card_crossingSideDart_le_card_removed
    side support hcrossing
  let pairEmbedding : Fin 2 → {vertex : V // side vertex} := fun index =>
    if index = 0 then ⟨first, hfirst⟩ else ⟨second, hsecond⟩
  have hpairEmbedding : Function.Injective pairEmbedding := by
    intro left right heq
    fin_cases left <;> fin_cases right
    · rfl
    · exfalso
      exact hne (congrArg Subtype.val heq)
    · exfalso
      exact hne (congrArg Subtype.val heq).symm
    · rfl
  have htwo : 2 ≤ Nat.card {vertex : V // side vertex} := by
    simpa using Nat.card_le_card_of_injective pairEmbedding hpairEmbedding
  omega

/-- Incidence-card cubicity gives regularity independently of the chosen
finite-neighbor instance. -/
theorem isRegularOfDegree_three_of_incidentEdgeFinset_card_eq_three
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    G.IsRegularOfDegree 3 := fun vertex => by
  have hmap :
      (incidentEdgeFinset G vertex).map
          (Function.Embedding.subtype
            (fun edge : Sym2 V => edge ∈ G.edgeSet)) =
        G.incidenceFinset vertex := by
    rw [SimpleGraph.incidenceFinset_eq_filter]
    ext edge
    simp [incidentEdgeFinset, and_comm]
  calc
    G.degree vertex = (G.incidenceFinset vertex).card := by simp
    _ = ((incidentEdgeFinset G vertex).map
        (Function.Embedding.subtype
          (fun edge : Sym2 V => edge ∈ G.edgeSet))).card := by rw [hmap]
    _ = (incidentEdgeFinset G vertex).card := by simp
    _ = 3 := hcubic vertex

/-- The deletion graph carried by an alternate reduction bridge witness. -/
abbrev Join12_30InternalBridgeWitness.deletedGraph
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :=
  (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).deleteEdges
    {(deletedEdgeOfInternal graphData data witness.internal).1}

/-- The deletion component containing alternate ports `0` and `3`. -/
def Join12_30InternalBridgeWitness.component03
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    witness.deletedGraph graphData data |>.ConnectedComponent :=
  (witness.deletedGraph graphData data).connectedComponentMk
    (data.retainedPort 0)

/-- The deletion component containing alternate ports `1` and `2`. -/
def Join12_30InternalBridgeWitness.component12
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    witness.deletedGraph graphData data |>.ConnectedComponent :=
  (witness.deletedGraph graphData data).connectedComponentMk
    (data.retainedPort 1)

/-- Ports `0` and `3` genuinely lie in one component of the retained-edge
deletion. -/
theorem Join12_30InternalBridgeWitness.port03_reachable
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    witness.deletedGraph graphData data |>.Reachable
      (data.retainedPort 0) (data.retainedPort 3) := by
  let retained := DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex
  let removed := deletedDartOfInternal graphData data witness.internal
  have hconnected : retained.Connected :=
    retainedRegion_connected_of_vertexMinimalTaitCounterexample
      graphData minimal data
  apply reachable_deleteEdge_of_fst_reachable_iff hconnected removed
  simpa [retained, removed, Join12_30InternalBridgeWitness.deletedGraph,
    deletedEdgeOfInternal] using witness.pair03_sameComponent

/-- Ports `1` and `2` genuinely lie in one component of the retained-edge
deletion. -/
theorem Join12_30InternalBridgeWitness.port12_reachable
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    witness.deletedGraph graphData data |>.Reachable
      (data.retainedPort 1) (data.retainedPort 2) := by
  let retained := DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex
  let removed := deletedDartOfInternal graphData data witness.internal
  have hconnected : retained.Connected :=
    retainedRegion_connected_of_vertexMinimalTaitCounterexample
      graphData minimal data
  apply reachable_deleteEdge_of_fst_reachable_iff hconnected removed
  simpa [retained, removed, Join12_30InternalBridgeWitness.deletedGraph,
    deletedEdgeOfInternal] using witness.pair12_sameComponent

/-- The two alternate port-pair components are distinct. -/
theorem Join12_30InternalBridgeWitness.component03_ne_component12
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    witness.component03 graphData data ≠
      witness.component12 graphData data := by
  intro hcomponents
  have hzeroOne : witness.deletedGraph graphData data |>.Reachable
      (data.retainedPort 0) (data.retainedPort 1) := by
    exact SimpleGraph.ConnectedComponent.exact hcomponents
  apply witness.port03_opposite_port12 graphData minimal data
  constructor
  · intro hzero
    exact hzero.trans hzeroOne
  · intro hone
    exact hone.trans hzeroOne.symm

/-- The first alternate component contains exactly boundary ports `0` and
`3`. -/
theorem Join12_30InternalBridgeWitness.retainedPort_mem_component03_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data)
    (port : Fin 4) :
    data.retainedPort port ∈
        (witness.component03 graphData data).supp ↔
      port = 0 ∨ port = 3 := by
  constructor
  · intro hmem
    fin_cases port
    · exact Or.inl rfl
    · exfalso
      exact witness.component03_ne_component12 graphData minimal data
        (SimpleGraph.ConnectedComponent.eq_of_common_vertex hmem
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem)
    · exfalso
      have htwo : data.retainedPort 2 ∈
          (witness.component12 graphData data).supp := by
        apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        exact SimpleGraph.ConnectedComponent.sound
          (witness.port12_reachable graphData minimal data).symm
      exact witness.component03_ne_component12 graphData minimal data
        (SimpleGraph.ConnectedComponent.eq_of_common_vertex hmem htwo)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    · apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
      exact SimpleGraph.ConnectedComponent.sound
        (witness.port03_reachable graphData minimal data).symm

/-- The second alternate component contains exactly boundary ports `1` and
`2`. -/
theorem Join12_30InternalBridgeWitness.retainedPort_mem_component12_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data)
    (port : Fin 4) :
    data.retainedPort port ∈
        (witness.component12 graphData data).supp ↔
      port = 1 ∨ port = 2 := by
  constructor
  · intro hmem
    fin_cases port
    · exfalso
      exact witness.component03_ne_component12 graphData minimal data
        (SimpleGraph.ConnectedComponent.eq_of_common_vertex
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem hmem)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have hthree : data.retainedPort 3 ∈
          (witness.component03 graphData data).supp := by
        apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        exact SimpleGraph.ConnectedComponent.sound
          (witness.port03_reachable graphData minimal data).symm
      exact witness.component03_ne_component12 graphData minimal data
        (SimpleGraph.ConnectedComponent.eq_of_common_vertex hthree hmem)
  · rintro (rfl | rfl)
    · exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    · apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
      exact SimpleGraph.ConnectedComponent.sound
        (witness.port12_reachable graphData minimal data).symm

/-- Ambient side carried by the alternate component containing ports `0`
and `3`. -/
def Join12_30InternalBridgeWitness.component03Side
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) (vertex : V) :
    Prop :=
  retainedEdgeDeleteComponentSide data
    (deletedEdgeOfInternal graphData data witness.internal)
    (witness.component03 graphData data) vertex

/-- Ambient side carried by the alternate component containing ports `1`
and `2`. -/
def Join12_30InternalBridgeWitness.component12Side
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) (vertex : V) :
    Prop :=
  retainedEdgeDeleteComponentSide data
    (deletedEdgeOfInternal graphData data witness.internal)
    (witness.component12 graphData data) vertex

/-- Three-edge support of the first alternate component: the deleted
retained edge and boundary edges `0` and `3`. -/
def Join12_30InternalBridgeWitness.component03Support
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    Finset G.edgeSet :=
  {data.retainedEdgeToAmbientEdge
      (deletedEdgeOfInternal graphData data witness.internal),
    data.boundaryEdge 0, data.boundaryEdge 3}

/-- Three-edge support of the second alternate component: the deleted
retained edge and boundary edges `1` and `2`. -/
def Join12_30InternalBridgeWitness.component12Support
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    Finset G.edgeSet :=
  {data.retainedEdgeToAmbientEdge
      (deletedEdgeOfInternal graphData data witness.internal),
    data.boundaryEdge 1, data.boundaryEdge 2}

theorem Join12_30InternalBridgeWitness.component03Support_card_le_three
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    (witness.component03Support graphData data).card ≤ 3 := by
  exact Finset.card_le_three

theorem Join12_30InternalBridgeWitness.component12Support_card_le_three
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    (witness.component12Support graphData data).card ≤ 3 := by
  exact Finset.card_le_three

/-- Every edge leaving the first alternate component belongs to its
three-edge support. -/
theorem Join12_30InternalBridgeWitness.crossingEdge_mem_component03Support
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (witness.component03Side graphData data) edge) :
    edge ∈ witness.component03Support graphData data := by
  rcases retainedEdgeDeleteComponentSide_crossingEdge data
      (deletedEdgeOfInternal graphData data witness.internal)
      (witness.component03 graphData data) edge hcross with
    hbridge | ⟨port, hboundary, hport⟩
  · simp [Join12_30InternalBridgeWitness.component03Support, hbridge]
  · have hportClass :=
      (witness.retainedPort_mem_component03_iff
        graphData minimal data port).1 hport
    rcases hportClass with rfl | rfl <;>
      simp [Join12_30InternalBridgeWitness.component03Support, hboundary]

/-- Every edge leaving the second alternate component belongs to its
three-edge support. -/
theorem Join12_30InternalBridgeWitness.crossingEdge_mem_component12Support
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (witness.component12Side graphData data) edge) :
    edge ∈ witness.component12Support graphData data := by
  rcases retainedEdgeDeleteComponentSide_crossingEdge data
      (deletedEdgeOfInternal graphData data witness.internal)
      (witness.component12 graphData data) edge hcross with
    hbridge | ⟨port, hboundary, hport⟩
  · simp [Join12_30InternalBridgeWitness.component12Support, hbridge]
  · have hportClass :=
      (witness.retainedPort_mem_component12_iff
        graphData minimal data port).1 hport
    rcases hportClass with rfl | rfl <;>
      simp [Join12_30InternalBridgeWitness.component12Support, hboundary]

/-- The first alternate component contains an ambient cycle. -/
theorem Join12_30InternalBridgeWitness.component03Side_hasCycle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    HasCycleOnSide G (witness.component03Side graphData data) := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    GoertzelV24SimpleGraphTaitBridge.incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hregular : G.IsRegularOfDegree 3 :=
    isRegularOfDegree_three_of_incidentEdgeFinset_card_eq_three hcubic
  have hzero : witness.component03Side graphData data
      (data.portVertex 0) :=
    ⟨data.retainedPort 0,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩
  have hthree : witness.component03Side graphData data
      (data.portVertex 3) :=
    ⟨data.retainedPort 3,
      (witness.retainedPort_mem_component03_iff
        graphData minimal data 3).2 (Or.inr rfl), rfl⟩
  refine
    hasCycleOnSide_of_cubic_of_connected_of_two_vertices_of_crossing_le_three
      hregular (witness.component03Side graphData data)
      (data.portVertex 0) (data.portVertex 3) hzero hthree
      (data.portVertex_ne (by decide : (0 : Fin 4) ≠ 3))
      (retainedEdgeDeleteComponentSide_connected data
        (deletedEdgeOfInternal graphData data witness.internal)
        (witness.component03 graphData data))
      (witness.component03Support graphData data)
      (witness.component03Support_card_le_three graphData data) ?_
  intro dart
  apply witness.crossingEdge_mem_component03Support
    graphData minimal data
  refine ⟨dart.1.fst, dart.1.snd, ?_, ?_, dart.2.1, dart.2.2⟩
  · change dart.1.fst ∈ s(dart.1.fst, dart.1.snd)
    simp
  · change dart.1.snd ∈ s(dart.1.fst, dart.1.snd)
    simp

/-- The second alternate component contains an ambient cycle. -/
theorem Join12_30InternalBridgeWitness.component12Side_hasCycle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    HasCycleOnSide G (witness.component12Side graphData data) := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    GoertzelV24SimpleGraphTaitBridge.incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hregular : G.IsRegularOfDegree 3 :=
    isRegularOfDegree_three_of_incidentEdgeFinset_card_eq_three hcubic
  have hone : witness.component12Side graphData data
      (data.portVertex 1) :=
    ⟨data.retainedPort 1,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩
  have htwo : witness.component12Side graphData data
      (data.portVertex 2) :=
    ⟨data.retainedPort 2,
      (witness.retainedPort_mem_component12_iff
        graphData minimal data 2).2 (Or.inr rfl), rfl⟩
  refine
    hasCycleOnSide_of_cubic_of_connected_of_two_vertices_of_crossing_le_three
      hregular (witness.component12Side graphData data)
      (data.portVertex 1) (data.portVertex 2) hone htwo
      (data.portVertex_ne (by decide : (1 : Fin 4) ≠ 2))
      (retainedEdgeDeleteComponentSide_connected data
        (deletedEdgeOfInternal graphData data witness.internal)
        (witness.component12 graphData data))
      (witness.component12Support graphData data)
      (witness.component12Support_card_le_three graphData data) ?_
  intro dart
  apply witness.crossingEdge_mem_component12Support
    graphData minimal data
  refine ⟨dart.1.fst, dart.1.snd, ?_, ?_, dart.2.1, dart.2.2⟩
  · change dart.1.fst ∈ s(dart.1.fst, dart.1.snd)
    simp
  · change dart.1.snd ∈ s(dart.1.fst, dart.1.snd)
    simp

/-- The two ambient component sides are disjoint. -/
theorem Join12_30InternalBridgeWitness.component12Side_not_component03Side
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data)
    (vertex : V)
    (htwelve : witness.component12Side graphData data vertex) :
    ¬ witness.component03Side graphData data vertex := by
  intro hzeroThree
  rcases htwelve with
    ⟨twelveRetained, htwelveComponent, htwelveValue⟩
  rcases hzeroThree with
    ⟨zeroThreeRetained, hzeroThreeComponent, hzeroThreeValue⟩
  have hretained : zeroThreeRetained = twelveRetained := by
    apply Subtype.ext
    exact hzeroThreeValue.trans htwelveValue.symm
  subst twelveRetained
  exact witness.component03_ne_component12 graphData minimal data
    (SimpleGraph.ConnectedComponent.eq_of_common_vertex
      hzeroThreeComponent htwelveComponent)

/-- The exact ambient crossing-edge set of the first alternate component. -/
def Join12_30InternalBridgeWitness.component03EdgeCut
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun edge => EdgeCrossesVertexSide G
    (witness.component03Side graphData data) edge

@[simp]
theorem Join12_30InternalBridgeWitness.mem_component03EdgeCut_iff
    (graphData : Data G) (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data)
    (edge : G.edgeSet) :
    edge ∈ witness.component03EdgeCut graphData data ↔
      EdgeCrossesVertexSide G
        (witness.component03Side graphData data) edge := by
  simp [Join12_30InternalBridgeWitness.component03EdgeCut]

/-- The exact crossing-edge set is contained in the explicit three-edge
support. -/
theorem Join12_30InternalBridgeWitness.component03EdgeCut_subset_support
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    witness.component03EdgeCut graphData data ⊆
      witness.component03Support graphData data := by
  intro edge hedge
  exact witness.crossingEdge_mem_component03Support graphData minimal data
    edge ((witness.mem_component03EdgeCut_iff graphData data edge).1 hedge)

theorem Join12_30InternalBridgeWitness.component03EdgeCut_card_le_three
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    (witness.component03EdgeCut graphData data).card ≤ 3 := by
  exact le_trans
    (Finset.card_le_card
      (witness.component03EdgeCut_subset_support graphData minimal data))
    (witness.component03Support_card_le_three graphData data)

/-- An alternate reduction bridge witness would realize a cyclic edge cut
of size at most three in the ambient graph. -/
def Join12_30InternalBridgeWitness.smallCyclicEdgeCut
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    SmallCyclicEdgeCut G where
  edgeCut := witness.component03EdgeCut graphData data
  side := witness.component03Side graphData data
  hcut_eq := witness.mem_component03EdgeCut_iff graphData data
  hcard_le_four := le_trans
    (witness.component03EdgeCut_card_le_three graphData minimal data)
    (by omega)
  hinside_cycle := witness.component03Side_hasCycle graphData minimal data
  houtside_cycle := HasCycleOnSide.mono
    (fun vertex htwelve =>
      witness.component12Side_not_component03Side
        graphData minimal data vertex htwelve)
    (witness.component12Side_hasCycle graphData minimal data)

/-- Cyclic five-edge-connectivity excludes every alternate reduction bridge
witness. -/
theorem Join12_30InternalBridgeWitness.false
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) : False := by
  have hcyclic :=
    GoertzelV24FourEdgeCutGluing.cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      graphData minimal
  exact hcyclic.not_smallCyclicEdgeCut_card_le_four
    (witness.smallCyclicEdgeCut graphData minimal data)
    (witness.smallCyclicEdgeCut graphData minimal data).hcard_le_four

/-- The alternate `12|30` square reduction is bridge-free in every
vertex-minimal Tait counterexample. -/
theorem reductionJoin12_30_edgeBridgeFree
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    EdgeBridgeFree
      (data.reductionRotationSystem graphData
        SquareReductionSide.join12_30) := by
  by_contra hnot
  rcases nonempty_join12_30InternalBridgeWitness_of_not_edgeBridgeFree
      graphData minimal data hnot with ⟨witness⟩
  exact witness.false graphData minimal data

/-- Consequently the alternate reduction always supplies an honest
all-equal coloring of the deleted four-pole. -/
theorem exists_deletedColoring_allEqual_of_order
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData) :
    ∃ deletedColoring :
        (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).EdgeColoring Color,
      IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          deletedColoring ∧
        SquareBoundaryWord.AllEqual
          (data.degreeTwoBoundaryData.colorWord deletedColoring) := by
  exact
    exists_deletedColoring_allEqual_of_reductionJoin12_30_edgeBridgeFree_of_order
      graphData minimal data horder
      (reductionJoin12_30_edgeBridgeFree graphData minimal data)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
