import Mathlib.Combinatorics.SimpleGraph.Matching
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionCoordinateSwitch

/-! Finite support components entered by complementary-coordinate turns. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]

/-- In a finite graph of maximum degree two, a degree-two root either shares
its component with an odd vertex or lies on a simple cycle. -/
theorem exists_reachable_odd_or_cycle_of_degree_eq_two_of_degree_le_two
    (start : W) (hstartDegree : H.degree start = 2)
    (hdegree : ∀ vertex : W, H.degree vertex ≤ 2) :
    (∃ finish : W, finish ≠ start ∧ Odd (H.degree finish) ∧
      H.Reachable start finish) ∨
    ∃ cycle : H.Walk start start, cycle.IsCycle := by
  classical
  let component : H.ConnectedComponent := H.connectedComponentMk start
  have hstartComponent : start ∈ component.supp := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  by_cases hodd : ∃ finish : W,
      finish ∈ component.supp ∧ Odd (H.degree finish)
  · left
    rcases hodd with ⟨finish, hfinishComponent, hfinishOdd⟩
    have hfinishNe : finish ≠ start := by
      intro heq
      subst finish
      rcases hfinishOdd with ⟨multiple, hmultiple⟩
      omega
    exact ⟨finish, hfinishNe, hfinishOdd,
      component.reachable_of_mem_supp
        hstartComponent hfinishComponent⟩
  · right
    let componentGraph : SimpleGraph component.supp :=
      H.induce component.supp
    letI componentVertexFintype : Fintype component.supp :=
      Subtype.fintype _
    letI componentNeighborFintype
        (vertex : component.supp) :
        Fintype (componentGraph.neighborSet vertex) :=
      Subtype.fintype _
    let startInComponent : component.supp :=
      ⟨start, hstartComponent⟩
    have hcomponentCycles : componentGraph.IsCycles := by
      intro vertex hneighbor
      have hneighbors : H.neighborSet vertex.1 ⊆ component.supp := by
        intro neighbor hadjacent
        exact component.mem_supp_of_adj_mem_supp
          vertex.2 hadjacent
      have hdegreeEq : componentGraph.degree vertex =
          H.degree vertex.1 := by
        have hinduced := SimpleGraph.degree_induce_of_neighborSet_subset
          (G := H) (s := component.supp) (v := vertex) hneighbors
        exact hinduced.trans
          (degree_eq_of_neighborFintypes H vertex.1
            (Subtype.fintype _) inferInstance)
      have hpositive : 0 < componentGraph.degree vertex :=
        SimpleGraph.degree_pos_iff_nonempty.mpr hneighbor
      have hnotOdd : ¬ Odd (H.degree vertex.1) := by
        intro hvertexOdd
        exact hodd ⟨vertex.1, vertex.2, hvertexOdd⟩
      have hnotOne : H.degree vertex.1 ≠ 1 := by
        intro hdegreeOne
        apply hnotOdd
        simp [hdegreeOne]
      have hdegreeTwo : H.degree vertex.1 = 2 := by
        have hpositiveAmbient : 0 < H.degree vertex.1 := by
          simpa [hdegreeEq] using hpositive
        exact Nat.le_antisymm (hdegree vertex.1) (by omega)
      rw [Set.ncard_eq_toFinset_card']
      exact hdegreeEq.trans hdegreeTwo
    have hstartNeighbor :
        (componentGraph.neighborSet startInComponent).Nonempty := by
      have hpositive : 0 < H.degree start := by
        simp [hstartDegree]
      rcases SimpleGraph.degree_pos_iff_nonempty.mp hpositive with
        ⟨neighbor, hadjacent⟩
      have hneighborComponent : neighbor ∈ component.supp :=
        component.mem_supp_of_adj_mem_supp
          hstartComponent hadjacent
      exact ⟨⟨neighbor, hneighborComponent⟩, hadjacent⟩
    let cycleComponent : componentGraph.ConnectedComponent :=
      componentGraph.connectedComponentMk startInComponent
    have hstartCycleComponent :
        startInComponent ∈ cycleComponent.supp := by
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    rcases
        hcomponentCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
          hstartCycleComponent hstartNeighbor with
      ⟨componentCycle, hcomponentCycle, _hcomponentCycleSupport⟩
    let cycle : H.Walk start start :=
      componentCycle.map
        (SimpleGraph.Embedding.induce (G := H) component.supp).toHom
    exact ⟨cycle,
      hcomponentCycle.map
        (SimpleGraph.Embedding.induce (G := H) component.supp).injective⟩

/-- Every odd vertex in a finite graph shares its component with a distinct
odd vertex. -/
theorem exists_distinct_reachable_odd_of_odd
    (start : W) (hstartOdd : Odd (H.degree start)) :
    ∃ finish : W, finish ≠ start ∧ Odd (H.degree finish) ∧
      H.Reachable start finish := by
  classical
  let component : H.ConnectedComponent := H.connectedComponentMk start
  letI componentVertexFintype : Fintype component.supp :=
    Subtype.fintype _
  let componentGraph : SimpleGraph component.supp :=
    H.induce component.supp
  letI componentNeighborFintype
      (vertex : component.supp) :
      Fintype (componentGraph.neighborSet vertex) :=
    Subtype.fintype _
  have hstartComponent : start ∈ component.supp := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  let startInComponent : component.supp :=
    ⟨start, hstartComponent⟩
  have hstartNeighbors : H.neighborSet start ⊆ component.supp := by
    intro neighbor hadjacent
    exact component.mem_supp_of_adj_mem_supp
      hstartComponent hadjacent
  have hstartDegree : componentGraph.degree startInComponent =
      H.degree start := by
    have hinduced := SimpleGraph.degree_induce_of_neighborSet_subset
      (G := H) (s := component.supp) (v := startInComponent)
        hstartNeighbors
    exact hinduced.trans
      (degree_eq_of_neighborFintypes H start
        (Subtype.fintype _) inferInstance)
  have hstartComponentOdd :
      Odd (componentGraph.degree startInComponent) := by
    simpa [hstartDegree] using hstartOdd
  obtain ⟨finishInComponent, hfinishNe, hfinishComponentOdd⟩ :=
    componentGraph.exists_ne_odd_degree_of_exists_odd_degree
      startInComponent hstartComponentOdd
  have hfinishNeighbors : H.neighborSet finishInComponent.1 ⊆
      component.supp := by
    intro neighbor hadjacent
    exact component.mem_supp_of_adj_mem_supp
      finishInComponent.2 hadjacent
  have hfinishDegree : componentGraph.degree finishInComponent =
      H.degree finishInComponent.1 := by
    have hinduced := SimpleGraph.degree_induce_of_neighborSet_subset
      (G := H) (s := component.supp) (v := finishInComponent)
        hfinishNeighbors
    exact hinduced.trans
      (degree_eq_of_neighborFintypes H finishInComponent.1
        (Subtype.fintype _) inferInstance)
  have hfinishOdd : Odd (H.degree finishInComponent.1) := by
    simpa [hfinishDegree] using hfinishComponentOdd
  have hfinishDistinct : finishInComponent.1 ≠ start := by
    intro heq
    exact hfinishNe (Subtype.ext heq)
  exact ⟨finishInComponent.1, hfinishDistinct, hfinishOdd,
    component.reachable_of_mem_supp
      hstartComponent finishInComponent.2⟩

omit [Fintype W] [DecidableRel H.Adj] in
/-- Deleting an edge removes exactly its opposite endpoint from the neighbor
set at either incident vertex. -/
theorem neighborSet_deleteEdges_singleton_eq_sdiff_of_mem
    (edge : H.edgeSet) {vertex : W} (hincident : vertex ∈ edge.1) :
    (H.deleteEdges {edge.1}).neighborSet vertex =
      H.neighborSet vertex \ {Sym2.Mem.other' hincident} := by
  classical
  let other := Sym2.Mem.other' hincident
  ext neighbor
  constructor
  · intro hdeleted
    have hadjacent : H.Adj vertex neighbor :=
      (SimpleGraph.deleteEdges_adj.mp hdeleted).1
    have hvalueNe : s(vertex, neighbor) ≠ edge.1 := by
      simpa only [Set.mem_singleton_iff] using
        (SimpleGraph.deleteEdges_adj.mp hdeleted).2
    refine ⟨hadjacent, ?_⟩
    simpa only [Set.mem_singleton_iff] using fun hneighbor : neighbor = other =>
      hvalueNe (by simpa only [other, hneighbor] using
        Sym2.other_spec' hincident)
  · intro horiginal
    rcases horiginal with ⟨hadjacent, hneighbor⟩
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hadjacent, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hvalue
    have hneighborEq : neighbor = other := by
      apply (Sym2.mkEmbedding vertex).injective
      exact hvalue.trans (Sym2.other_spec' hincident).symm
    apply hneighbor
    simpa only [Set.mem_singleton_iff, other] using hneighborEq

omit [DecidableEq W] in
/-- Neighbor-set cardinality agrees with graph degree independently of the
chosen finite enumeration of that neighbor set. -/
theorem neighborSet_ncard_eq_degree
    (graph : SimpleGraph W) (vertex : W) :
    (graph.neighborSet vertex).ncard = graph.degree vertex := by
  calc
    (graph.neighborSet vertex).ncard =
        Fintype.card (graph.neighborSet vertex) :=
      (Set.fintypeCard_eq_ncard (graph.neighborSet vertex)).symm
    _ = graph.degree vertex := graph.card_neighborSet_eq_degree vertex

omit [DecidableRel H.Adj] in
/-- Deleting an incident edge lowers the degree by exactly one. -/
theorem degree_deleteEdges_singleton_add_one_of_mem
    (edge : H.edgeSet) {vertex : W} (hincident : vertex ∈ edge.1) :
    (H.deleteEdges {edge.1}).degree vertex + 1 = H.degree vertex := by
  classical
  let other := Sym2.Mem.other' hincident
  have hotherNeighbor : other ∈ H.neighborSet vertex := by
    change H.Adj vertex other
    rw [← SimpleGraph.mem_edgeSet, Sym2.other_spec' hincident]
    exact edge.2
  have hcard := Set.ncard_sdiff_singleton_add_one hotherNeighbor
  rw [← neighborSet_deleteEdges_singleton_eq_sdiff_of_mem
    edge hincident] at hcard
  calc
    (H.deleteEdges {edge.1}).degree vertex + 1 =
        ((H.deleteEdges {edge.1}).neighborSet vertex).ncard + 1 := by
      rw [neighborSet_ncard_eq_degree]
    _ = (H.neighborSet vertex).ncard := hcard
    _ = H.degree vertex := neighborSet_ncard_eq_degree H vertex

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
/-- Deleting an edge does not change the neighbor set at a vertex outside
that edge. -/
theorem neighborSet_deleteEdges_singleton_eq_of_not_mem
    (edge : H.edgeSet) {vertex : W} (hincident : vertex ∉ edge.1) :
    (H.deleteEdges {edge.1}).neighborSet vertex =
      H.neighborSet vertex := by
  classical
  ext neighbor
  constructor
  · intro hdeleted
    exact (SimpleGraph.deleteEdges_adj.mp hdeleted).1
  · intro hadjacent
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hadjacent, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hvalue
    apply hincident
    rw [← hvalue]
    simp

omit [DecidableEq W] [DecidableRel H.Adj] in
/-- Deleting an edge leaves the degree unchanged away from its endpoints. -/
theorem degree_deleteEdges_singleton_eq_of_not_mem
    (edge : H.edgeSet) {vertex : W} (hincident : vertex ∉ edge.1) :
    (H.deleteEdges {edge.1}).degree vertex = H.degree vertex := by
  classical
  have hneighbors :=
    neighborSet_deleteEdges_singleton_eq_of_not_mem edge hincident
  calc
    (H.deleteEdges {edge.1}).degree vertex =
        ((H.deleteEdges {edge.1}).neighborSet vertex).ncard := by
      rw [neighborSet_ncard_eq_degree]
    _ = (H.neighborSet vertex).ncard := congrArg Set.ncard hneighbors
    _ = H.degree vertex := neighborSet_ncard_eq_degree H vertex

omit [DecidableRel H.Adj] in
/-- A simple cycle rooted at a degree-two vertex uses every ambient edge
incident to that root. -/
theorem edge_mem_rooted_isCycle_of_degree_eq_two
    {start : W} {cycle : H.Walk start start}
    (hcycle : cycle.IsCycle) (hdegree : H.degree start = 2)
    (edge : H.edgeSet) (hincident : start ∈ edge.1) :
    edge.1 ∈ cycle.edges := by
  classical
  let other := Sym2.Mem.other' hincident
  have hedgeAdjacent : H.Adj start other := by
    rw [← SimpleGraph.mem_edgeSet, Sym2.other_spec' hincident]
    exact edge.2
  have hcycleNeighborCard :
      (cycle.toSubgraph.neighborSet start).ncard = 2 := by
    exact hcycle.ncard_neighborSet_toSubgraph_eq_two
      cycle.start_mem_support
  have hambientNeighborCard : (H.neighborSet start).ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card']
    exact hdegree
  have hneighborSubset : cycle.toSubgraph.neighborSet start ⊆
      H.neighborSet start := by
    intro neighbor hadjacent
    exact hadjacent.adj_sub
  have hneighborEq : cycle.toSubgraph.neighborSet start =
      H.neighborSet start := by
    apply Set.eq_of_subset_of_ncard_le hneighborSubset
    omega
  have hcycleAdjacent : cycle.toSubgraph.Adj start other := by
    have hotherNeighbor : other ∈
        cycle.toSubgraph.neighborSet start := by
      rw [hneighborEq]
      exact hedgeAdjacent
    exact hotherNeighbor
  have hedgeCycle : s(start, other) ∈ cycle.edges :=
    cycle.adj_toSubgraph_iff_mem_edges.1 hcycleAdjacent
  simpa only [other, Sym2.other_spec' hincident] using hedgeCycle

omit [DecidableRel H.Adj] in
/-- A nontrivial simple path rooted at a degree-one vertex uses its unique
ambient incident edge. -/
theorem edge_mem_rooted_isPath_of_degree_eq_one
    {start finish : W} {path : H.Walk start finish}
    (hpath : path.IsPath) (hfinish : finish ≠ start)
    (hdegree : H.degree start = 1)
    (edge : H.edgeSet) (hincident : start ∈ edge.1) :
    edge.1 ∈ path.edges := by
  classical
  let other := Sym2.Mem.other' hincident
  have hedgeAdjacent : H.Adj start other := by
    rw [← SimpleGraph.mem_edgeSet, Sym2.other_spec' hincident]
    exact edge.2
  have hnotNil : ¬ path.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hfinish.symm
  have hpathNeighborCard :
      (path.toSubgraph.neighborSet start).ncard = 1 := by
    rw [hpath.neighborSet_toSubgraph_startpoint hnotNil]
    simp
  have hambientNeighborCard : (H.neighborSet start).ncard = 1 := by
    rw [neighborSet_ncard_eq_degree, hdegree]
  have hneighborSubset : path.toSubgraph.neighborSet start ⊆
      H.neighborSet start := by
    intro neighbor hadjacent
    exact hadjacent.adj_sub
  have hneighborEq : path.toSubgraph.neighborSet start =
      H.neighborSet start := by
    apply Set.eq_of_subset_of_ncard_le hneighborSubset
    omega
  have hpathAdjacent : path.toSubgraph.Adj start other := by
    have hotherNeighbor : other ∈ path.toSubgraph.neighborSet start := by
      rw [hneighborEq]
      exact hedgeAdjacent
    exact hotherNeighbor
  have hedgePath : s(start, other) ∈ path.edges :=
    path.adj_toSubgraph_iff_mem_edges.1 hpathAdjacent
  simpa only [other, Sym2.other_spec' hincident] using hedgePath

omit [DecidableRel H.Adj] in
/-- A nontrivial simple path from a degree-two root that avoids one of two
named incident edges must use the other. -/
theorem second_mem_edges_of_isPath_of_degree_eq_two_of_first_not_mem
    {start finish : W} {path : H.Walk start finish}
    (hpath : path.IsPath) (hfinish : finish ≠ start)
    (first second : H.edgeSet) (hfirstSecond : first ≠ second)
    (hfirstIncident : start ∈ first.1)
    (hsecondIncident : start ∈ second.1)
    (hdegree : H.degree start = 2)
    (hfirstPath : first.1 ∉ path.edges) :
    second.1 ∈ path.edges := by
  classical
  let deletedGraph : SimpleGraph W := H.deleteEdges {first.1}
  have hdeletedDegreeAddOne : deletedGraph.degree start + 1 =
      H.degree start :=
    degree_deleteEdges_singleton_add_one_of_mem first hfirstIncident
  have hdeletedDegree : deletedGraph.degree start = 1 := by
    omega
  have hpathEdgesDeleted : ∀ edgeValue : Sym2 W,
      edgeValue ∈ path.edges → edgeValue ∈ deletedGraph.edgeSet := by
    intro edgeValue hedge
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨path.edges_subset_edgeSet hedge, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hvalue
    exact hfirstPath (hvalue ▸ hedge)
  let deletedPath : deletedGraph.Walk start finish :=
    path.transfer deletedGraph hpathEdgesDeleted
  have hdeletedPath : deletedPath.IsPath :=
    hpath.transfer hpathEdgesDeleted
  have hsecondValueNe : second.1 ≠ first.1 := by
    intro hvalue
    exact hfirstSecond (Subtype.ext hvalue.symm)
  let secondDeleted : deletedGraph.edgeSet :=
    ⟨second.1, by
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨second.2, by simpa only [Set.mem_singleton_iff]⟩⟩
  have hsecondDeletedIncident : start ∈ secondDeleted.1 :=
    hsecondIncident
  have hsecondDeletedPath : secondDeleted.1 ∈ deletedPath.edges :=
    edge_mem_rooted_isPath_of_degree_eq_one
      hdeletedPath hfinish hdeletedDegree
        secondDeleted hsecondDeletedIncident
  simpa only [deletedPath, SimpleGraph.Walk.edges_transfer] using
    hsecondDeletedPath

/-- At a degree-two vertex with two named incident edges, deleting the first
and following the second reaches an odd endpoint or closes through the first
edge into a cycle.  The resulting path or cycle contains the named second
edge. -/
theorem exists_directed_odd_path_or_cycle_of_incident_pair
    (start : W) (first second : H.edgeSet)
    (hfirstSecond : first ≠ second)
    (hfirstIncident : start ∈ first.1)
    (hsecondIncident : start ∈ second.1)
    (hstartDegree : H.degree start = 2) :
    (∃ finish : W, finish ≠ start ∧ Odd (H.degree finish) ∧
      ∃ path : H.Walk start finish,
        path.IsPath ∧ first.1 ∉ path.edges ∧ second.1 ∈ path.edges) ∨
    ∃ cycle : H.Walk start start,
      cycle.IsCycle ∧ first.1 ∈ cycle.edges ∧
        second.1 ∈ cycle.edges := by
  classical
  let deletedGraph : SimpleGraph W := H.deleteEdges {first.1}
  have hdeletedStartAddOne : deletedGraph.degree start + 1 =
      H.degree start := by
    exact degree_deleteEdges_singleton_add_one_of_mem
      first hfirstIncident
  have hdeletedStartDegree : deletedGraph.degree start = 1 := by
    omega
  have hdeletedStartOdd : Odd (deletedGraph.degree start) := by
    simp [hdeletedStartDegree]
  rcases exists_distinct_reachable_odd_of_odd
      (H := deletedGraph) start hdeletedStartOdd with
    ⟨finish, hfinishNe, hfinishOdd, hfinishReachable⟩
  by_cases hfinishFirst : finish ∈ first.1
  · right
    let other := Sym2.Mem.other' hfirstIncident
    have hfinishOther : finish = other := by
      have hfinishCases : finish = start ∨ finish = other := by
        have hmem : Sym2.Mem finish first.1 :=
          Sym2.mem_iff_mem.mpr hfinishFirst
        rw [← Sym2.other_spec' hfirstIncident] at hmem
        exact Sym2.mem_iff'.mp hmem
      exact hfinishCases.resolve_left hfinishNe
    have hfirstAdjacent : H.Adj start other := by
      rw [← SimpleGraph.mem_edgeSet, Sym2.other_spec' hfirstIncident]
      exact first.2
    have hclosureReachable :
        (H.deleteEdges {s(start, other)}).Reachable start other := by
      rw [Sym2.other_spec' hfirstIncident]
      simpa only [deletedGraph, hfinishOther] using hfinishReachable
    rcases
        SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
          ⟨hfirstAdjacent, hclosureReachable⟩ with
      ⟨root, unrootedCycle, hunrootedCycle, hfirstCycle⟩
    have hstartSupport : start ∈ unrootedCycle.support :=
      unrootedCycle.fst_mem_support_of_mem_edges hfirstCycle
    let cycle : H.Walk start start :=
      unrootedCycle.rotate start hstartSupport
    have hcycle : cycle.IsCycle :=
      hunrootedCycle.rotate hstartSupport
    refine ⟨cycle, hcycle, ?_, ?_⟩
    · exact edge_mem_rooted_isCycle_of_degree_eq_two
        hcycle hstartDegree first hfirstIncident
    · exact edge_mem_rooted_isCycle_of_degree_eq_two
        hcycle hstartDegree second hsecondIncident
  · left
    have hfinishDegree : deletedGraph.degree finish =
        H.degree finish := by
      exact degree_deleteEdges_singleton_eq_of_not_mem
        first hfinishFirst
    have hfinishAmbientOdd : Odd (H.degree finish) := by
      simpa [hfinishDegree] using hfinishOdd
    rcases hfinishReachable.exists_isPath with
      ⟨deletedPath, hdeletedPath⟩
    let path : H.Walk start finish :=
      deletedPath.mapLe (SimpleGraph.deleteEdges_le {first.1})
    have hpath : path.IsPath :=
      hdeletedPath.mapLe (SimpleGraph.deleteEdges_le {first.1})
    have hfirstNotPath : first.1 ∉ path.edges := by
      change first.1 ∉
        (deletedPath.mapLe
          (SimpleGraph.deleteEdges_le {first.1})).edges
      rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
      intro hfirstPath
      have hfirstDeleted :=
        deletedPath.edges_subset_edgeSet hfirstPath
      rw [SimpleGraph.edgeSet_deleteEdges] at hfirstDeleted
      exact hfirstDeleted.2 (by simp)
    have hsecondValueNe : second.1 ≠ first.1 := by
      intro hvalue
      exact hfirstSecond (Subtype.ext hvalue.symm)
    let secondDeleted : deletedGraph.edgeSet :=
      ⟨second.1, by
        rw [SimpleGraph.edgeSet_deleteEdges]
        exact ⟨second.2, by simpa only [Set.mem_singleton_iff]⟩⟩
    have hsecondDeletedIncident : start ∈ secondDeleted.1 :=
      hsecondIncident
    have hsecondDeletedPath : secondDeleted.1 ∈ deletedPath.edges :=
      edge_mem_rooted_isPath_of_degree_eq_one
        hdeletedPath hfinishNe hdeletedStartDegree
          secondDeleted hsecondDeletedIncident
    have hsecondPath : second.1 ∈ path.edges := by
      change second.1 ∈
        (deletedPath.mapLe
          (SimpleGraph.deleteEdges_le {first.1})).edges
      rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
      exact hsecondDeletedPath
    exact ⟨finish, hfinishNe, hfinishAmbientOdd,
      path, hpath, hfirstNotPath, hsecondPath⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

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
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

namespace FirstHitSingletonCompanionTransferPath

variable {firstHit : FirstHitSingletonCompanionTransferPath
  (collar := collar) (sourceEscape := sourceEscape)}

namespace TransverseCompanionChange

variable {change : firstHit.TransverseCompanionChange}

namespace ComplementarySupportCorner

/-- Following the complementary support component from a transverse turn
either reaches a distinct named collar terminal or closes into a simple
scalar-support cycle rooted at the turn. -/
theorem exists_distinct_terminal_reachable_or_supportCycle
    (corner : change.ComplementarySupportCorner) :
    let supportGraph := collar.coordinateDiscrepancySupportGraph
      sourceEscape (!firstHit.transfer.coordinate)
    let junction := SimpleGraph.lineGraphCommonVertex
      corner.incoming_transverse_adj
    (∃ finish : collar.commonCoreVertex,
        finish ∈ collar.commonPortVertexFinset ∧
        finish ≠ junction ∧
        supportGraph.Reachable junction finish) ∨
      ∃ supportCycle : supportGraph.Walk junction junction,
        supportCycle.IsCycle ∧
        corner.incomingSupportEdge.1 ∈ supportCycle.edges ∧
        (transverseSupportEdge change).1 ∈ supportCycle.edges := by
  classical
  let scalarChain : collar.commonCore.edgeSet → F2 :=
    fun edge => crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)
  let supportGraph : SimpleGraph collar.commonCoreVertex :=
    scalarSupportGraph scalarChain
  let junction := SimpleGraph.lineGraphCommonVertex
    corner.incoming_transverse_adj
  change (∃ finish : collar.commonCoreVertex,
      finish ∈ collar.commonPortVertexFinset ∧
      finish ≠ junction ∧
      supportGraph.Reachable junction finish) ∨
    ∃ supportCycle : supportGraph.Walk junction junction,
      supportCycle.IsCycle ∧
      corner.incomingSupportEdge.1 ∈ supportCycle.edges ∧
      (transverseSupportEdge change).1 ∈ supportCycle.edges
  have hjunctionDegree : supportGraph.degree junction = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree]
    have hcornerDegree := corner.supportJunction_degree_eq_two
    change (incidentEdgeFinset supportGraph junction).card = 2 at hcornerDegree
    exact hcornerDegree
  have hdegree : ∀ vertex : collar.commonCoreVertex,
      supportGraph.degree vertex ≤ 2 := by
    intro vertex
    rw [← incidentEdgeFinset_card_eq_degree]
    exact taitDiscrepancySupport_incidentCard_le_two
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate) vertex
      (collar.commonCore_incidentEdgeFinset_card_le_three vertex)
  have hoddTerminal : ∀ vertex : collar.commonCoreVertex,
      Odd (supportGraph.degree vertex) →
        vertex ∈ collar.commonPortVertexFinset := by
    intro vertex hodd
    have hscalarBoundary :
        scalarVertexKirchhoffSum collar.commonCore scalarChain vertex ≠ 0 := by
      exact (scalarSupportGraph_degree_odd_iff scalarChain vertex).1 hodd
    by_contra hterminal
    apply hscalarBoundary
    rw [scalarVertexKirchhoffSum_crossFaceCoordinate,
      collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
        sourceEscape vertex hterminal]
    cases (!firstHit.transfer.coordinate) <;> rfl
  rcases
      exists_reachable_odd_or_cycle_of_degree_eq_two_of_degree_le_two
        (H := supportGraph) junction hjunctionDegree hdegree with
    hterminal | hcycle
  · left
    rcases hterminal with ⟨finish, hfinishNe, hfinishOdd, hreachable⟩
    exact ⟨finish, hoddTerminal finish hfinishOdd,
      hfinishNe, hreachable⟩
  · right
    rcases hcycle with ⟨supportCycle, hsupportCycle⟩
    refine ⟨supportCycle, hsupportCycle, ?_, ?_⟩
    · apply edge_mem_rooted_isCycle_of_degree_eq_two
        hsupportCycle hjunctionDegree corner.incomingSupportEdge
      exact SimpleGraph.lineGraphCommonVertex_mem_left
        corner.incoming_transverse_adj
    · apply edge_mem_rooted_isCycle_of_degree_eq_two
        hsupportCycle hjunctionDegree (transverseSupportEdge change)
      exact SimpleGraph.lineGraphCommonVertex_mem_right
        corner.incoming_transverse_adj

/-- Deleting the incoming support edge orients the component classification:
the terminal path avoids that edge and necessarily leaves the junction along
the transverse edge; otherwise both edges lie on one rooted support cycle. -/
theorem exists_directed_terminalPath_or_supportCycle
    (corner : change.ComplementarySupportCorner) :
    let supportGraph := collar.coordinateDiscrepancySupportGraph
      sourceEscape (!firstHit.transfer.coordinate)
    let junction := SimpleGraph.lineGraphCommonVertex
      corner.incoming_transverse_adj
    (∃ finish : collar.commonCoreVertex,
        finish ∈ collar.commonPortVertexFinset ∧
        finish ≠ junction ∧
        ∃ path : supportGraph.Walk junction finish,
          path.IsPath ∧
          corner.incomingSupportEdge.1 ∉ path.edges ∧
          (transverseSupportEdge change).1 ∈ path.edges) ∨
      ∃ supportCycle : supportGraph.Walk junction junction,
        supportCycle.IsCycle ∧
        corner.incomingSupportEdge.1 ∈ supportCycle.edges ∧
        (transverseSupportEdge change).1 ∈ supportCycle.edges := by
  classical
  let scalarChain : collar.commonCore.edgeSet → F2 :=
    fun edge => crossFaceCoordinate (!firstHit.transfer.coordinate)
      (collar.commonDiscrepancy sourceEscape edge)
  let supportGraph : SimpleGraph collar.commonCoreVertex :=
    scalarSupportGraph scalarChain
  let junction := SimpleGraph.lineGraphCommonVertex
    corner.incoming_transverse_adj
  change (∃ finish : collar.commonCoreVertex,
      finish ∈ collar.commonPortVertexFinset ∧
      finish ≠ junction ∧
      ∃ path : supportGraph.Walk junction finish,
        path.IsPath ∧
        corner.incomingSupportEdge.1 ∉ path.edges ∧
        (transverseSupportEdge change).1 ∈ path.edges) ∨
    ∃ supportCycle : supportGraph.Walk junction junction,
      supportCycle.IsCycle ∧
      corner.incomingSupportEdge.1 ∈ supportCycle.edges ∧
      (transverseSupportEdge change).1 ∈ supportCycle.edges
  have hjunctionDegree : supportGraph.degree junction = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree]
    have hcornerDegree := corner.supportJunction_degree_eq_two
    change (incidentEdgeFinset supportGraph junction).card = 2 at hcornerDegree
    exact hcornerDegree
  have hincomingIncident : junction ∈ corner.incomingSupportEdge.1 :=
    SimpleGraph.lineGraphCommonVertex_mem_left
      corner.incoming_transverse_adj
  have htransverseIncident : junction ∈
      (transverseSupportEdge change).1 :=
    SimpleGraph.lineGraphCommonVertex_mem_right
      corner.incoming_transverse_adj
  have hoddTerminal : ∀ vertex : collar.commonCoreVertex,
      Odd (supportGraph.degree vertex) →
        vertex ∈ collar.commonPortVertexFinset := by
    intro vertex hodd
    have hscalarBoundary :
        scalarVertexKirchhoffSum collar.commonCore scalarChain vertex ≠ 0 := by
      exact (scalarSupportGraph_degree_odd_iff scalarChain vertex).1 hodd
    by_contra hterminal
    apply hscalarBoundary
    rw [scalarVertexKirchhoffSum_crossFaceCoordinate,
      collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
        sourceEscape vertex hterminal]
    cases (!firstHit.transfer.coordinate) <;> rfl
  rcases exists_directed_odd_path_or_cycle_of_incident_pair
      (H := supportGraph) junction corner.incomingSupportEdge
        (transverseSupportEdge change)
        corner.incoming_transverse_adj.ne
        hincomingIncident htransverseIncident hjunctionDegree with
    hterminal | hcycle
  · left
    rcases hterminal with
      ⟨finish, hfinishNe, hfinishOdd, path,
        hpath, hincomingAvoided, htransversePath⟩
    exact ⟨finish, hoddTerminal finish hfinishOdd,
      hfinishNe, path, hpath, hincomingAvoided, htransversePath⟩
  · exact Or.inr hcycle

/-- The directed terminal branch may be truncated at its first later named
port without losing the transverse launch.  Thus its internal vertices avoid
every source and target port. -/
theorem exists_firstTerminalPath_or_supportCycle
    (corner : change.ComplementarySupportCorner) :
    let supportGraph := collar.coordinateDiscrepancySupportGraph
      sourceEscape (!firstHit.transfer.coordinate)
    let junction := SimpleGraph.lineGraphCommonVertex
      corner.incoming_transverse_adj
    (∃ finish : collar.commonCoreVertex,
        finish ∈ collar.commonPortVertexFinset ∧
        finish ≠ junction ∧
        ∃ path : supportGraph.Walk junction finish,
          path.IsPath ∧ 0 < path.length ∧
          (∀ position : Nat, 0 < position → position < path.length →
            path.getVert position ∉ collar.commonPortVertexFinset) ∧
          corner.incomingSupportEdge.1 ∉ path.edges ∧
          (transverseSupportEdge change).1 ∈ path.edges) ∨
      ∃ supportCycle : supportGraph.Walk junction junction,
        supportCycle.IsCycle ∧
        corner.incomingSupportEdge.1 ∈ supportCycle.edges ∧
        (transverseSupportEdge change).1 ∈ supportCycle.edges := by
  classical
  let supportGraph := collar.coordinateDiscrepancySupportGraph
    sourceEscape (!firstHit.transfer.coordinate)
  let junction := SimpleGraph.lineGraphCommonVertex
    corner.incoming_transverse_adj
  change (∃ finish : collar.commonCoreVertex,
      finish ∈ collar.commonPortVertexFinset ∧
      finish ≠ junction ∧
      ∃ path : supportGraph.Walk junction finish,
        path.IsPath ∧ 0 < path.length ∧
        (∀ position : Nat, 0 < position → position < path.length →
          path.getVert position ∉ collar.commonPortVertexFinset) ∧
        corner.incomingSupportEdge.1 ∉ path.edges ∧
        (transverseSupportEdge change).1 ∈ path.edges) ∨
    ∃ supportCycle : supportGraph.Walk junction junction,
      supportCycle.IsCycle ∧
      corner.incomingSupportEdge.1 ∈ supportCycle.edges ∧
      (transverseSupportEdge change).1 ∈ supportCycle.edges
  rcases corner.exists_directed_terminalPath_or_supportCycle with
    hterminal | hcycle
  · rcases hterminal with
      ⟨finish, hfinishTerminal, hfinishNe, path,
        hpath, hincomingAvoided, _htransversePath⟩
    rcases exists_firstTerminalPrefix collar.commonPortVertexFinset
        path hfinishTerminal hfinishNe hpath with
      ⟨firstTerminal, initialPath, hfirstTerminal, hfirstNe,
        hinitialPath, hinitialPositive, hinternal, hinitialSubwalk⟩
    have hincomingInitial : corner.incomingSupportEdge.1 ∉
        initialPath.edges := by
      intro hincoming
      exact hincomingAvoided (hinitialSubwalk.edges_subset hincoming)
    have hjunctionDegree : supportGraph.degree junction = 2 := by
      rw [← incidentEdgeFinset_card_eq_degree]
      have hcornerDegree := corner.supportJunction_degree_eq_two
      change (incidentEdgeFinset supportGraph junction).card = 2 at hcornerDegree
      exact hcornerDegree
    have htransverseInitial : (transverseSupportEdge change).1 ∈
        initialPath.edges := by
      apply second_mem_edges_of_isPath_of_degree_eq_two_of_first_not_mem
        hinitialPath hfirstNe corner.incomingSupportEdge
          (transverseSupportEdge change)
          corner.incoming_transverse_adj.ne
      · exact SimpleGraph.lineGraphCommonVertex_mem_left
          corner.incoming_transverse_adj
      · exact SimpleGraph.lineGraphCommonVertex_mem_right
          corner.incoming_transverse_adj
      · exact hjunctionDegree
      · exact hincomingInitial
    left
    exact ⟨firstTerminal, hfirstTerminal, hfirstNe,
      initialPath, hinitialPath, hinitialPositive, hinternal,
      hincomingInitial, htransverseInitial⟩
  · exact Or.inr hcycle

end ComplementarySupportCorner

end TransverseCompanionChange

end FirstHitSingletonCompanionTransferPath

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
