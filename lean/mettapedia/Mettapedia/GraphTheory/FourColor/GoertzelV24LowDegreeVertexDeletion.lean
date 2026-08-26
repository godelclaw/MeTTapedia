import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Deleting leaves preserves preconnectedness

If a finite simple graph is connected, deleting any collection of vertices
whose ambient degrees are at most one leaves a preconnected induced graph.
The result deliberately says `Preconnected`: deleting every vertex of a
one-edge graph leaves an empty graph, which has no inhabitant but still has
the required pairwise reachability property.

The proof is elementary and does not classify the graph.  A simple path
between two retained vertices cannot use a deleted vertex internally, because
an internal path vertex has two distinct neighbours.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24LowDegreeVertexDeletion

open SimpleGraph

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
  {graph : SimpleGraph Vertex} [DecidableRel graph.Adj]

/-- Deleting any finite set of degree-at-most-one vertices from a connected
finite graph leaves a preconnected induced graph. -/
theorem preconnected_induce_compl_of_degree_le_one
    (hconnected : graph.Connected) (removed : Finset Vertex)
    (hdegree : ∀ vertex ∈ removed, graph.degree vertex ≤ 1) :
    (graph.induce (↑removed : Set Vertex)ᶜ).Preconnected := by
  classical
  intro start finish
  obtain ⟨path, hpath⟩ := hconnected.exists_isPath start.1 finish.1
  have hsupport :
      ∀ vertex ∈ path.support, vertex ∈ (↑removed : Set Vertex)ᶜ := by
    intro vertex hvertexSupport
    rw [Set.mem_compl_iff, Finset.mem_coe]
    intro hvertexRemoved
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvertexSupport with
      ⟨index, hindexVertex, hindexBound⟩
    have hindexNotStart : index ≠ 0 := by
      intro hindex
      subst index
      have hvertexEq : vertex = start.1 := by
        simpa using hindexVertex.symm
      exact start.2 (hvertexEq ▸ hvertexRemoved)
    have hindexNotFinish : index ≠ path.length := by
      intro hindex
      have hvertexEq : vertex = finish.1 := by
        calc
          vertex = path.getVert index := hindexVertex.symm
          _ = finish.1 := by simp [hindex]
      exact finish.2 (hvertexEq ▸ hvertexRemoved)
    have hindexLt : index < path.length := by omega
    let previous : Vertex := path.getVert (index - 1)
    let next : Vertex := path.getVert (index + 1)
    have hpreviousAdj : graph.Adj vertex previous := by
      have hpreviousIndex : index - 1 < path.length := by omega
      have hadj := path.adj_getVert_succ hpreviousIndex
      have hsub : index - 1 + 1 = index :=
        Nat.sub_add_cancel (Nat.pos_of_ne_zero hindexNotStart)
      simpa [previous, hindexVertex, hsub] using hadj.symm
    have hnextAdj : graph.Adj vertex next := by
      have hadj := path.adj_getVert_succ hindexLt
      simpa [next, hindexVertex] using hadj
    have hpreviousNeNext : previous ≠ next := by
      intro heq
      have hindices : index - 1 = index + 1 :=
        hpath.getVert_injOn
          (by rw [Set.mem_setOf_eq]; omega)
          (by rw [Set.mem_setOf_eq]; omega)
          (by simpa [previous, next] using heq)
      omega
    let neighbors : Finset Vertex := {previous, next}
    have hneighborsSubset : neighbors ⊆ graph.neighborFinset vertex := by
      intro candidate hcandidate
      simp [neighbors] at hcandidate
      rcases hcandidate with rfl | rfl
      · simpa using hpreviousAdj
      · simpa using hnextAdj
    have hdegreeAtLeastTwo : 2 ≤ graph.degree vertex := by
      rw [← graph.card_neighborFinset_eq_degree]
      calc
        2 = neighbors.card := by simp [neighbors, hpreviousNeNext]
        _ ≤ (graph.neighborFinset vertex).card :=
          Finset.card_le_card hneighborsSubset
    exact (Nat.not_succ_le_self 1)
      (hdegreeAtLeastTwo.trans (hdegree vertex hvertexRemoved))
  exact ⟨path.induce (↑removed : Set Vertex)ᶜ hsupport⟩

/-- Deleting connected blocks which each reach an ambient endpoint preserves
preconnectedness in a connected maximum-degree-two graph.

This strictly extends deletion of individual leaves.  A removed block may run
several vertices inward from an endpoint; what is forbidden is an interior
block with retained vertices on both sides.  The proof detects such a block on
a simple path between two retained vertices.  A path inside the removed block
from its low-degree witness to the first intersection would give three
distinct neighbours there (or two at the witness), contradicting the degree
bounds. -/
theorem preconnected_induce_compl_of_components_meet_degree_le_one
    (hconnected : graph.Connected) (removed : Finset Vertex)
    (hdegree : ∀ vertex, graph.degree vertex ≤ 2)
    (hmeets : ∀ component :
      (graph.induce (↑removed : Set Vertex)).ConnectedComponent,
      ∃ vertex : {vertex // vertex ∈ removed},
        vertex ∈ component.supp ∧ graph.degree vertex.1 ≤ 1) :
    (graph.induce (↑removed : Set Vertex)ᶜ).Preconnected := by
  classical
  intro start finish
  obtain ⟨path, hpath⟩ := hconnected.exists_isPath start.1 finish.1
  have hsupport :
      ∀ vertex ∈ path.support, vertex ∈ (↑removed : Set Vertex)ᶜ := by
    intro vertex hvertexSupport
    rw [Set.mem_compl_iff, Finset.mem_coe]
    intro hvertexRemoved
    let removedGraph := graph.induce (↑removed : Set Vertex)
    let removedVertex : {vertex // vertex ∈ removed} :=
      ⟨vertex, hvertexRemoved⟩
    let component := removedGraph.connectedComponentMk removedVertex
    rcases hmeets component with ⟨endpoint, hendpointComponent, hendpointDegree⟩
    have hendpointRemoved : endpoint.1 ∈ removed := endpoint.2
    by_cases hendpointPath : endpoint.1 ∈ path.support
    · rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hendpointPath
          with ⟨index, hindexEndpoint, hindexBound⟩
      have hindexNotStart : index ≠ 0 := by
        intro hindex
        have hendpointEq : endpoint.1 = start.1 := by
          calc
            endpoint.1 = path.getVert index := hindexEndpoint.symm
            _ = start.1 := by simp [hindex]
        exact start.2 (hendpointEq ▸ hendpointRemoved)
      have hindexNotFinish : index ≠ path.length := by
        intro hindex
        have hendpointEq : endpoint.1 = finish.1 := by
          calc
            endpoint.1 = path.getVert index := hindexEndpoint.symm
            _ = finish.1 := by simp [hindex]
        exact finish.2 (hendpointEq ▸ hendpointRemoved)
      have hindexLt : index < path.length := by omega
      let previous : Vertex := path.getVert (index - 1)
      let next : Vertex := path.getVert (index + 1)
      have hpreviousAdj : graph.Adj endpoint.1 previous := by
        have hpreviousIndex : index - 1 < path.length := by omega
        have hadj := path.adj_getVert_succ hpreviousIndex
        have hsub : index - 1 + 1 = index :=
          Nat.sub_add_cancel (Nat.pos_of_ne_zero hindexNotStart)
        simpa [previous, hindexEndpoint, hsub] using hadj.symm
      have hnextAdj : graph.Adj endpoint.1 next := by
        have hadj := path.adj_getVert_succ hindexLt
        simpa [next, hindexEndpoint] using hadj
      have hpreviousNeNext : previous ≠ next := by
        intro heq
        have hindices : index - 1 = index + 1 :=
          hpath.getVert_injOn
            (by rw [Set.mem_setOf_eq]; omega)
            (by rw [Set.mem_setOf_eq]; omega)
            (by simpa [previous, next] using heq)
        omega
      let neighbors : Finset Vertex := {previous, next}
      have hneighborsSubset : neighbors ⊆ graph.neighborFinset endpoint.1 := by
        intro candidate hcandidate
        simp [neighbors] at hcandidate
        rcases hcandidate with rfl | rfl
        · simpa using hpreviousAdj
        · simpa using hnextAdj
      have hdegreeAtLeastTwo : 2 ≤ graph.degree endpoint.1 := by
        rw [← graph.card_neighborFinset_eq_degree]
        calc
          2 = neighbors.card := by simp [neighbors, hpreviousNeNext]
          _ ≤ (graph.neighborFinset endpoint.1).card :=
            Finset.card_le_card hneighborsSubset
      omega
    · have hcomponentEq :
          removedGraph.connectedComponentMk endpoint = component :=
        (component.mem_supp_iff endpoint).1 hendpointComponent
      have hremovedReachable : removedGraph.Reachable endpoint removedVertex :=
        SimpleGraph.ConnectedComponent.exact hcomponentEq
      let inclusion : removedGraph →g graph :=
        { toFun := fun point => point.1
          map_rel' := by
            intro left right hadj
            exact hadj }
      have hroute : ∃ route : graph.Walk endpoint.1 vertex,
          ∀ point ∈ route.support, point ∈ removed := by
        apply hremovedReachable.elim
        intro removedRoute
        let route := removedRoute.map inclusion
        refine ⟨route, ?_⟩
        intro point hpoint
        rw [SimpleGraph.Walk.support_map] at hpoint
        rcases List.mem_map.mp hpoint with ⟨source, _hsource, rfl⟩
        exact source.2
      rcases hroute with ⟨route, hrouteRemoved⟩
      let pathSupport : Finset Vertex := path.support.toFinset
      have hintersection :
          {candidate ∈ pathSupport | candidate ∈ route.support}.Nonempty := by
        refine ⟨vertex, by
          simp [pathSupport, hvertexSupport, route.end_mem_support]⟩
      obtain ⟨firstHit, hfirstHitPath, hfirstHitRoute, hfirstHit⟩ :=
        route.exists_mem_support_forall_mem_support_imp_eq
          pathSupport hintersection
      have hfirstHitSupport : firstHit ∈ path.support := by
        simpa [pathSupport] using hfirstHitPath
      have hfirstHitRemoved : firstHit ∈ removed :=
        hrouteRemoved firstHit hfirstHitRoute
      let routeToHit : graph.Walk endpoint.1 firstHit :=
        route.takeUntil firstHit hfirstHitRoute
      have hrouteToHitNotNil : ¬ routeToHit.Nil := by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        by_contra hlength
        have hendpointFirstHit : endpoint.1 ≠ firstHit := by
          intro heq
          exact hendpointPath (heq ▸ hfirstHitSupport)
        exact hendpointFirstHit
          (routeToHit.eq_of_length_eq_zero (by omega))
      let predecessor : Vertex := routeToHit.penultimate
      have hpredecessorAdj : graph.Adj predecessor firstHit :=
        routeToHit.adj_penultimate hrouteToHitNotNil
      have hpredecessorRoute : predecessor ∈ routeToHit.support :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
          ⟨routeToHit.length - 1, rfl, Nat.sub_le _ _⟩
      have hpredecessorNotPath : predecessor ∉ path.support := by
        intro hpredecessorPath
        have hpredecessorEq : predecessor = firstHit :=
          hfirstHit predecessor (by simpa [pathSupport] using hpredecessorPath)
            hpredecessorRoute
        exact graph.irrefl (hpredecessorEq ▸ hpredecessorAdj)
      rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hfirstHitSupport
          with ⟨index, hfirstHitIndex, hindexBound⟩
      have hindexNotStart : index ≠ 0 := by
        intro hindex
        have hfirstHitStart : firstHit = start.1 := by
          calc
            firstHit = path.getVert index := hfirstHitIndex.symm
            _ = start.1 := by simp [hindex]
        exact start.2 (hfirstHitStart ▸ hfirstHitRemoved)
      have hindexNotFinish : index ≠ path.length := by
        intro hindex
        have hfirstHitFinish : firstHit = finish.1 := by
          calc
            firstHit = path.getVert index := hfirstHitIndex.symm
            _ = finish.1 := by simp [hindex]
        exact finish.2 (hfirstHitFinish ▸ hfirstHitRemoved)
      have hindexLt : index < path.length := by omega
      let previous : Vertex := path.getVert (index - 1)
      let next : Vertex := path.getVert (index + 1)
      have hpreviousAdj : graph.Adj firstHit previous := by
        have hpreviousIndex : index - 1 < path.length := by omega
        have hadj := path.adj_getVert_succ hpreviousIndex
        have hsub : index - 1 + 1 = index :=
          Nat.sub_add_cancel (Nat.pos_of_ne_zero hindexNotStart)
        simpa [previous, hfirstHitIndex, hsub] using hadj.symm
      have hnextAdj : graph.Adj firstHit next := by
        have hadj := path.adj_getVert_succ hindexLt
        simpa [next, hfirstHitIndex] using hadj
      have hpreviousSupport : previous ∈ path.support :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
          ⟨index - 1, by simp [previous], by omega⟩
      have hnextSupport : next ∈ path.support :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
          ⟨index + 1, by simp [next], by omega⟩
      have hpredecessorNePrevious : predecessor ≠ previous := by
        intro heq
        exact hpredecessorNotPath (heq ▸ hpreviousSupport)
      have hpredecessorNeNext : predecessor ≠ next := by
        intro heq
        exact hpredecessorNotPath (heq ▸ hnextSupport)
      have hpreviousNeNext : previous ≠ next := by
        intro heq
        have hindices : index - 1 = index + 1 :=
          hpath.getVert_injOn
            (by rw [Set.mem_setOf_eq]; omega)
            (by rw [Set.mem_setOf_eq]; omega)
            (by simpa [previous, next] using heq)
        omega
      let neighbors : Finset Vertex := {predecessor, previous, next}
      have hneighborsSubset : neighbors ⊆ graph.neighborFinset firstHit := by
        intro candidate hcandidate
        simp [neighbors] at hcandidate
        rcases hcandidate with rfl | rfl | rfl
        · simpa using hpredecessorAdj.symm
        · simpa using hpreviousAdj
        · simpa using hnextAdj
      have hdegreeAtLeastThree : 3 ≤ graph.degree firstHit := by
        rw [← graph.card_neighborFinset_eq_degree]
        calc
          3 = neighbors.card := by
            simp [neighbors, hpredecessorNePrevious, hpredecessorNeNext,
              hpreviousNeNext]
          _ ≤ (graph.neighborFinset firstHit).card :=
            Finset.card_le_card hneighborsSubset
      exact (Nat.not_succ_le_self 2)
        (hdegreeAtLeastThree.trans (hdegree firstHit))
  exact ⟨path.induce (↑removed : Set Vertex)ᶜ hsupport⟩

omit [Fintype Vertex] [DecidableRel graph.Adj] in
/-- A path in an induced subgraph whose endpoints lie in one ambient
connected component lifts to the corresponding induced graph on that
component.  This is the subtype bookkeeping needed when a finite receipt
first proves a path globally and a componentwise deletion theorem consumes it
locally. -/
theorem induce_reachable_lift_connectedComponent
    (component : graph.ConnectedComponent) (kept : Set Vertex)
    (start finish : {vertex // vertex ∈ kept})
    (hstart : start.1 ∈ component.supp)
    (hfinish : finish.1 ∈ component.supp)
    (hreachable : (graph.induce kept).Reachable start finish) :
    (component.toSimpleGraph.induce
      {vertex : component | vertex.1 ∈ kept}).Reachable
        ⟨⟨start.1, hstart⟩, start.2⟩ ⟨⟨finish.1, hfinish⟩, finish.2⟩ := by
  classical
  rcases hreachable with ⟨walk⟩
  have hsupport : ∀ vertex ∈ walk.support,
      vertex.1 ∈ component.supp := by
    intro vertex hvertex
    let routeToVertex := walk.takeUntil vertex hvertex
    have hreachAmbient : graph.Reachable start.1 vertex.1 :=
      ⟨routeToVertex.map (SimpleGraph.Embedding.induce kept).toHom⟩
    have hcomponentStart :
        graph.connectedComponentMk start.1 = component :=
      (component.mem_supp_iff start.1).1 hstart
    have hcomponentVertex :
        graph.connectedComponentMk vertex.1 = component :=
      (SimpleGraph.ConnectedComponent.sound hreachAmbient).symm.trans
        hcomponentStart
    exact (component.mem_supp_iff vertex.1).2 hcomponentVertex
  let componentWalk := walk.induce
    {vertex : {vertex // vertex ∈ kept} |
      vertex.1 ∈ component.supp} hsupport
  let reorder :
      ((graph.induce kept).induce
          {vertex : {vertex // vertex ∈ kept} |
            vertex.1 ∈ component.supp}) →g
        (component.toSimpleGraph.induce
          {vertex : component | vertex.1 ∈ kept}) :=
    { toFun := fun vertex =>
        ⟨⟨vertex.1.1, vertex.2⟩, vertex.1.2⟩
      map_rel' := by
        intro left right hadj
        exact hadj }
  exact ⟨componentWalk.map reorder⟩

end GoertzelV24LowDegreeVertexDeletion

end Mettapedia.GraphTheory.FourColor
